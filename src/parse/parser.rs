use std::cell::RefCell;
use std::rc::Rc;
use log::Level;
use crate::ast::*;
use crate::log::{Log, LogBuilder, LogHandler};
use crate::parse::error::ParseError;
use crate::parse::{FilePos, ItemDef, ScopeTree, SourceFile, Span};
use crate::parse::token::{Token, TokenStream, TokenType};

macro_rules! attempt {
    ($parser:expr, $expected:expr) => {
        match $parser.check(&[$expected]) {
            true => {
                $parser.bump();
                true
            }
            false => false,
        }
    };
}

macro_rules! expect {
    ($parser:expr, $expected:expr) => {
        match $parser.check(&[$expected]) {
            true => {
                let tok = $parser.curr_tok.clone();
                $parser.bump();
                Ok(tok)
            },
            false => {
                let err = $parser.expectation_err(&[$expected], None).emit();
                Err(err)
            }
        }
    };
    ($parser:expr, $expected:expr, $str:expr) => {
        match $parser.check(&[$expected]) {
            true => {
                let tok = $parser.curr_tok.clone();
                $parser.bump();
                Ok(tok)
            },
            false => {
                let err = $parser.expectation_err(&[$expected], Some($str)).emit();
                Err(err)
            }
        }
    };
}

macro_rules! expect_warn {
    ($parser:expr, $expected:expr) => {
        match $parser.check(&[$expected]) {
            true => { $parser.bump(); }
            false => {
                $parser.expectation_err(&[$expected], None)
                    .with_level(::log::Level::Warn)
                    .print();
            }
        }
    };
    ($parser:expr, $expected:expr, $str:expr) => {
        match $parser.check(&[$expected]) {
            true => { $parser.bump(); }
            false => {
                $parser.expectation_err(&[$expected], Some($str))
                    .with_level(::log::Level::Warn)
                    .print();
            }
        }
    };
}

pub struct Parser {
    source: SourceFile,
    tokens: TokenStream,
    prev_tok: Token,
    curr_tok: Token,
    next_tok: Token,
    scope_tree: Rc<RefCell<ScopeTree>>,

    error_count: RefCell<usize>,
    warn_count: RefCell<usize>,
    last_log: RefCell<Option<Log>>,
}

impl LogHandler for Parser {
    fn on_emit(&self, log: &mut Log) -> bool {
        if let Some(last_log) = self.last_log.borrow().as_ref() {
            let matches =
                log.level == last_log.level &&
                log.span == last_log.span &&
                log.msg.to_string() == last_log.msg.to_string();

            if matches {
                return false;
            }
        };

        *self.last_log.borrow_mut() = Some(log.clone());

        match log.level {
            Level::Error => *self.error_count.borrow_mut() += 1,
            Level::Warn => *self.warn_count.borrow_mut() += 1,
            _ => {}
        }
        true
    }
}

impl Parser {
    pub fn new(tokens: TokenStream, scope_tree: Rc<RefCell<ScopeTree>>) -> Self {
        let mut parser = Self {
            source: tokens.source.clone(),
            tokens,
            prev_tok: Token::invalid(Span::initial()),
            curr_tok: Token::invalid(Span::initial()),
            next_tok: Token::invalid(Span::initial()),
            scope_tree,

            error_count: RefCell::new(0),
            warn_count: RefCell::new(0),
            last_log: RefCell::new(None),
        };

        parser.bump();
        parser.bump();

        parser
    }

    pub fn parse_module(&mut self) -> Module {
        let name = self.source.get_filename().unwrap();
        let path = self.scope_tree.borrow().get_path();
        let def = self.push_define_module(name.to_string(), path, self.source.clone()).unwrap();

        let items = {
            let mut items = Vec::new();
            while !self.is_eof() {
                if let Some(item) = self.try_parse_stmt() {
                    items.push(item)
                }
            }
            items
        };

        self.pop_scope();
        Module { def, items }
    }

    fn try_parse_stmt(&mut self) -> Option<Rc<Stmt>> {
        match self.parse_stmt() {
            Ok(item) => Some(item),
            Err(e) => {
                e.print();
                self.skip_to_next_stmt();
                None
            }
        }
    }

    fn parse_stmt(&mut self) -> Result<Rc<Stmt>, Log> {
        match &self.curr_tok.ty {
            TokenType::Var => {
                self.bump();
                let decl = self.parse_var_decl()?;
                Ok(Rc::new(Stmt::VarDecl(decl)))
            }
            TokenType::Func => {
                let decl = self.parse_func_decl()?;
                Ok(Rc::new(Stmt::FuncDecl(decl)))
            }
            TokenType::If => {
                let stmt = self.parse_branch()?;
                Ok(Rc::new(Stmt::Branch(stmt)))
            }
            TokenType::For => {
                let stmt = self.parse_for_loop()?;
                Ok(Rc::new(Stmt::ForLoop(stmt)))
            }
            TokenType::While => {
                let stmt = self.parse_while_loop()?;
                Ok(Rc::new(Stmt::WhileLoop(stmt)))
            }
            TokenType::Loop => {
                let stmt = self.parse_loop()?;
                Ok(Rc::new(Stmt::Loop(stmt)))
            }
            TokenType::Continue => {
                let stmt = self.parse_continue()?;
                Ok(Rc::new(Stmt::Continue(stmt)))
            }
            TokenType::Break => {
                let stmt = self.parse_break()?;
                Ok(Rc::new(Stmt::Break(stmt)))
            }
            TokenType::Return => {
                let stmt = self.parse_return()?;
                Ok(Rc::new(Stmt::Return(stmt)))
            }
            TokenType::LBrace => {
                let block = self.parse_block()?;
                Ok(Rc::new(Stmt::Block(block)))
            }
            TokenType::Semicolon => {
                crate::log::error(ParseError::DanglingSemi)
                    .with_span(&self.curr_tok.span, &self.source)
                    .handled(self)
                    .into_result()
            }
            _ => {
                let expr = self.parse_expr()?;
                expect_warn!(self, TokenType::Semicolon);
                Ok(Rc::new(Stmt::Expr(expr)))
            }
        }
    }

    fn parse_var_decl(&mut self) -> Result<VarDecl, Log> {
        let start = self.curr_pos();

        let name = self.parse_ident()?;

        expect!(self, TokenType::Colon)?;
        let ty = self.parse_type()?;

        expect!(self, TokenType::Assign)?;
        let value = self.parse_expr()?;

        expect_warn!(self, TokenType::Semicolon);

        let def = self.define_var(name, ty);
        let decl = VarDecl{ def, value, span: self.span_from(start) };
        Ok(decl)
    }

    fn parse_branch(&mut self) -> Result<Branch, Log> {
        let start = self.curr_pos();

        expect!(self, TokenType::If)?;
        let cond = self.parse_expr()?;

        let true_block = self.parse_block()?;

        let false_block = if attempt!(self, TokenType::Else) {
            if self.check(&[TokenType::If]) {
                let start = self.curr_pos();
                let id = self.push_define_block(&self.curr_tok.span).unwrap();

                let sub_branch = Rc::new(Stmt::Branch(self.parse_branch()?));

                self.pop_scope();
                let block = Block { id, items: vec![sub_branch], span: self.span_from(start) };
                Some(block)
            } else {
                Some(self.parse_block()?)
            }
        } else { None };

        let branch = Branch { cond, true_block, false_block, span: self.span_from(start) };
        Ok(branch)
    }

    fn parse_for_loop(&mut self) -> Result<ForLoop, Log> {
        let start = self.curr_pos();

        let start_tok = expect!(self, TokenType::For)?;
        let id = self.push_define_block(&start_tok.span).unwrap();

        let init = self.parse_stmt()?;
        let cond = self.parse_expr()?;
        let update = self.parse_expr()?;
        let block = self.parse_block()?;

        self.pop_scope();
        let stmt = ForLoop { id, init, cond, update, block, span: self.span_from(start) };
        Ok(stmt)
    }

    fn parse_while_loop(&mut self) -> Result<WhileLoop, Log> {
        let start = self.curr_pos();

        let start_tok = expect!(self, TokenType::While)?;
        let id = self.push_define_block(&start_tok.span).unwrap();

        let cond = self.parse_expr()?;
        let block = self.parse_block()?;

        self.pop_scope();
        let stmt = WhileLoop { id, cond, block, span: self.span_from(start) };
        Ok(stmt)
    }

    fn parse_loop(&mut self) -> Result<Loop, Log> {
        let start = self.curr_pos();

        let start_tok = expect!(self, TokenType::Loop)?;
        let id = self.push_define_block(&start_tok.span).unwrap();
        
        let block = self.parse_block()?;

        self.pop_scope();
        let stmt = Loop { id, block, span: self.span_from(start) };
        Ok(stmt)
    }

    fn parse_continue(&mut self) -> Result<Continue, Log> {
        let start = self.curr_pos();

        expect!(self, TokenType::Continue)?;
        expect_warn!(self, TokenType::Semicolon);

        let stmt = Continue { span: self.span_from(start) };
        Ok(stmt)
    }

    fn parse_break(&mut self) -> Result<Break, Log> {
        let start = self.curr_pos();

        expect!(self, TokenType::Break)?;
        expect_warn!(self, TokenType::Semicolon);

        let stmt = Break { span: self.span_from(start) };
        Ok(stmt)
    }

    fn parse_return(&mut self) -> Result<Return, Log> {
        let start = self.curr_pos();

        expect!(self, TokenType::Return)?;

        let value = if !attempt!(self, TokenType::Semicolon) {
            let value = self.parse_expr()?;
            expect_warn!(self, TokenType::Semicolon);
            Some(value)
        } else {
            None
        };

        let ret = Return { value, span: self.span_from(start) };
        Ok(ret)
    }

    fn parse_func_decl(&mut self) -> Result<FuncDecl, Log> {
        let start = self.curr_pos();

        expect!(self, TokenType::Func)?;
        let name = self.parse_ident()?;

        expect!(self, TokenType::LParen)?;
        let (params, span) = self.parse_comma_seperated(Self::parse_param, TokenType::RParen)?;
        let params = Params { items: params, span };
        expect!(self, TokenType::RParen)?;

        let ret = if attempt!(self, TokenType::Colon) {
            self.parse_type()?
        } else {
            Type::Void
        };

        let def = self.push_define_func(name, ret, params).unwrap();

        for param in def.params.iter() {
            self.define_var(param.def.id.clone(), param.def.ty);
        }

        let block = self.parse_block()?;

        self.pop_scope();
        let decl = FuncDecl{ def, block, span: self.span_from(start) };
        Ok(decl)
    }

    fn parse_block(&mut self) -> Result<Block, Log> {
        let start = self.curr_pos();

        let lbrace = expect!(self, TokenType::LBrace)?;
        let id = self.push_define_block(&lbrace.span).unwrap();

        let items = {
            let mut items = Vec::new();
            while !self.check(&[TokenType::RBrace, TokenType::Eof]) {
                if let Some(item) = self.try_parse_stmt() {
                    items.push(item)
                }
            }
            items
        };

        self.pop_scope();
        expect!(self, TokenType::RBrace)?;

        let block = Block { id, items, span: self.span_from(start) };
        Ok(block)
    }

    fn parse_expr(&mut self) -> Result<Rc<Expr>, Log> {
        self.parse_expr_inner(1)
    }

    fn parse_expr_inner(&mut self, prec: u32) -> Result<Rc<Expr>, Log> {
        let start = self.curr_pos();

        // Parse the LHS expression
        let mut lhs = self.parse_expr_atom(prec)?;

        // Keep parsing as long as binary operations continue,
        // or operator precedence requires us to stop.
        while self.curr_tok.is_binary_op() {
            // Get info on current operator
            let opinfo = get_binary_op_info(&self.curr_tok.ty);
            if opinfo.precedence < prec {
                break;
            }
            self.bump();

            // Parse RHS expression
            let prec = if opinfo.associativity == Associativity::Left {
                opinfo.precedence + 1
            } else {
                opinfo.precedence
            };
            let rhs = self.parse_expr_inner(prec)?;

            // Validate that assigment is only done on variables
            // Also checked during validation stage, but it's nice to error quicker if possible
            if opinfo.token_type.is_assign() {
                if !matches!(lhs.as_ref(), Expr::VarAccess(_)) {
                    return crate::log::error(ParseError::InvalidAssignExpression)
                        .with_span(&self.span_from(start.clone()), &self.source)
                        .handled(self)
                        .into_result();
                }
            }

            // Save this as the new LHS expression
            let span = self.span_from(start.clone());
            let op = BinaryOp{ op: opinfo.token_type.clone(), lhs, rhs, span };
            lhs = Rc::new(Expr::BinaryOp(op));
        }

        Ok(lhs)
    }

    fn parse_expr_atom(&mut self, prec: u32) -> Result<Rc<Expr>, Log> {
        let start = self.curr_pos();

        // Handle unary NOT or MINUS operations
        if self.curr_tok.is_unary_op() {
            let opinfo = get_unary_op_info(&self.curr_tok.ty);
            if opinfo.precedence >= prec {
                self.bump();

                // Reenter expr parsing
                let prec = if opinfo.associativity == Associativity::Left {
                    opinfo.precedence + 1
                } else {
                    opinfo.precedence
                };
                let val = self.parse_expr_inner(prec)?;

                // Return unary op expr
                let span = self.span_from(start);
                let op = UnaryOp { op: opinfo.token_type.clone(), val, span };
                return Ok(Rc::new(Expr::UnaryOp(op)));
            }
        }

        match &self.curr_tok.ty {
            // Variable access or function call
            TokenType::Id(_) => {
                let path = self.parse_path()?;

                // Handle function call
                if attempt!(self, TokenType::LParen) {
                    let (args, span) = self.parse_comma_seperated(Self::parse_arg, TokenType::RParen)?;
                    let args = Args { items: args, span };
                    expect!(self, TokenType::RParen)?;

                    let func_call = FuncCall { symbol: path.into(), args, span: self.span_from(start) };
                    return Ok(Rc::new(Expr::FuncCall(func_call)))
                }

                // Check if variable is defined
                if !self.has_defined_id(&path) {
                    crate::log::error(ParseError::UndefinedVariable(path.clone()))
                        .with_span(&path.get_span(), &self.source)
                        .handled(self)
                        .print();
                }

                Ok(Rc::new(Expr::VarAccess(path.into())))
            }
            TokenType::NumberVal(val) => {
                let val = val.clone();
                self.bump();
                Ok(Rc::new(Expr::Number(val, self.curr_tok.span.clone())))
            }
            TokenType::BoolVal(val) => {
                let val = val.clone();
                self.bump();
                Ok(Rc::new(Expr::Bool(val, self.curr_tok.span.clone())))
            }
            _ => {
                // we've lost the plot. could be anything
                let err = self.expectation_err(&[], Some("an expression")).emit();
                Err(err)
            }
        }
    }

    fn parse_path(&mut self) -> Result<Path, Log> {
        let mut path = Path::new(vec![]);

        let ident = self.parse_ident()?;
        path.push(ident);

        while self.check(&[TokenType::Scope]) {
            self.bump();

            let ident = self.parse_ident()?;
            path.push(ident);
        }

        Ok(path)
    }

    fn parse_param(&mut self) -> Result<Param, Log> {
        let start = self.curr_pos();

        let name = self.parse_ident()?;

        expect!(self, TokenType::Colon)?;
        let ty = self.parse_type()?;

        let def = VarDef::new(name, ty);
        let param = Param { def, span: self.span_from(start) };
        Ok(param)
    }

    fn parse_arg(&mut self) -> Result<Arg, Log> {
        let expr = self.parse_expr()?;
        let arg = Arg { span: expr.get_span(), expr };
        Ok(arg)
    }

    fn parse_ident(&mut self) -> Result<Ident, Log> {
        match &self.curr_tok.ty {
            TokenType::Id(name) => {
                let id = Ident { name: name.clone(), span: self.curr_tok.span.clone() };
                self.bump();
                Ok(id)
            }
            _ => {
                let err = self.expectation_err(&[], Some("an identifier")).emit();
                Err(err)
            }
        }
    }

    fn parse_type(&mut self) -> Result<Type, Log> {
        match &self.curr_tok.ty {
            TokenType::LParen => {
                self.bump();
                if attempt!(self, TokenType::RParen) {
                    Ok(Type::Void)
                }
                else {
                    let ty = self.parse_type()?;
                    expect!(self, TokenType::RParen)?;
                    Ok(ty)
                }
            },
            TokenType::Number => {
                self.bump();
                Ok(Type::Number)
            },
            TokenType::Bool => {
                self.bump();
                Ok(Type::Bool)
            },
            _ => {
                // we've lost the plot. could be anything
                let err = self.expectation_err(&[], Some("a type")).emit();
                Err(err)
            }
        }
    }

    fn parse_comma_seperated<T, F>(&mut self, parse_single: F, delim: TokenType) -> Result<(Vec<T>, Span), Log>
        where
            F: Fn(&mut Self) -> Result<T, Log>
    {
        let start = self.curr_pos();

        let delims = [delim];
        let mut items = vec![];

        if !self.check(&delims) {
            let param = parse_single(self)?;
            items.push(param);

            while self.check(&[TokenType::Comma]) {
                self.bump();

                if self.check(&delims) {
                    // TODO: warn about trailing comma
                    break;
                }

                let param = parse_single(self)?;
                items.push(param);
            }
        }

        Ok((items, self.span_from(start)))
    }

    #[inline]
    fn bump(&mut self) {
        if let Some(next) = self.tokens.next().cloned() {
            std::mem::swap(&mut self.prev_tok, &mut self.curr_tok);
            std::mem::swap(&mut self.curr_tok, &mut self.next_tok);
            self.next_tok = next;
        }
    }

    #[inline]
    fn skip_to_next_stmt(&mut self) {
        while !matches!(self.curr_tok.ty, TokenType::Var | TokenType::Func |
            TokenType::If | TokenType::For | TokenType::While | TokenType::Loop |
            TokenType::Continue | TokenType::Break | TokenType::Return | TokenType::Eof)
        {
            self.bump();
        }
    }

    #[inline]
    fn check(&self, expected: &[TokenType]) -> bool {
        expected.contains(&self.curr_tok.ty)
    }

    fn expectation_err(&mut self, expected: &[TokenType], expected_str: Option<&str>) -> LogBuilder {
        if expected == [TokenType::Semicolon] {
            crate::log::error(ParseError::MissingSemi)
                .with_span(&self.prev_tok.span.next_char(), &self.source)
                .handled(self)
        }
        else if self.curr_tok.ty == TokenType::Eof {
            crate::log::error(ParseError::UnexpectedEof)
                .with_span(&self.curr_tok.span, &self.source)
                .handled(self)
        }
        else {
            let tok = self.curr_tok.ty.clone();

            let expected = expected_str.map(str::to_string).unwrap_or_else(||
                if expected.is_empty() {
                    String::new()
                } else if expected.len() == 1 {
                    format!("{}", expected.first().unwrap())
                } else {
                    let expected_as_str = expected.into_iter()
                        .map(|x| x.to_string())
                        .collect::<Vec<_>>();
                    format!("one of {}", expected_as_str.join(", "))
                });

            crate::log::error(ParseError::UnexpectedToken { tok, expected })
                .with_span(&self.curr_tok.span, &self.source)
                .handled(self)
        }
    }

    #[inline]
    fn is_eof(&self) -> bool {
        self.curr_tok.is_eof()
    }

    #[inline]
    fn curr_pos(&self) -> FilePos {
        self.curr_tok.span.start.clone()
    }

    #[inline]
    fn span_from(&self, pos: FilePos) -> Span {
        let len = self.curr_tok.span.start.idx - pos.idx;
        Span::new(pos, len)
    }

    #[inline]
    fn push_into_scope(&self, name: &str) -> Result<(), Log> {
        self.scope_tree.borrow_mut()
            .push_into(name)
            .map_err(|e| e.into())
    }

    #[inline]
    fn pop_scope(&self) {
        self.scope_tree.borrow_mut().pop();
    }

    #[inline]
    fn push_define_package(&mut self, name: String) -> Result<PackageDef, Log> {
        let def = self.define_package(name)?;
        self.push_into_scope(&def.name)?;
        Ok(def)
    }

    #[inline]
    fn push_define_module(&mut self, name: String, path: Path, source: SourceFile) -> Result<ModuleDef, Log> {
        let def = self.define_module(name, path, source)?;
        self.push_into_scope(&def.name)?;
        Ok(def)
    }

    #[inline]
    fn push_define_func(&mut self, id: Ident, ret: Type, params: Params) -> Result<FuncDef, Log> {
        let def = self.define_func(id, ret, params)?;
        self.push_into_scope(&def.id.name)?;
        Ok(def)
    }

    #[inline]
    fn push_define_block(&self, span: &Span) -> Result<Ident, Log> {
        let id = self.define_block(span);
        self.push_into_scope(&id.name)?;
        Ok(id)
    }

    fn define_package(&mut self, name: String) -> Result<PackageDef, Log> {
        let def = PackageDef::new(name);
        let replaced = self.scope_tree.borrow_mut().define_package(def.clone());
        assert!(replaced.is_none(), "package shouldn't cause redefinitions!");
        Ok(def)
    }

    fn define_module(&mut self, name: String, path: Path, source: SourceFile) -> Result<ModuleDef, Log> {
        let def = ModuleDef::new(name.clone(), path, source);
        let replaced = self.scope_tree.borrow_mut().define_module(def.clone());

        if let Some(replaced) = replaced {
            match replaced {
                ItemDef::Package(def) => {
                    panic!("package '{}' redefined by module '{}'", def.name, name);
                },
                ItemDef::Module(def) => {
                    return crate::log::error(ParseError::PathNameCollision(Ident::new_initial(def.name)))
                        .with_file(&self.source)
                        .handled(self)
                        .into_result();
                }
                ItemDef::Func(def) => {
                    return crate::log::error(ParseError::PathNameCollision(def.id))
                        .with_file(&self.source)
                        .into_result();
                }
                ItemDef::Var(def) => {
                    panic!("variable '{}' redefined by module '{}'", def.id.name, name);
                }
                ItemDef::Block(def) => {
                    panic!("block '{}' redefined by module '{}'", def.name, name);
                }
            }
        }
        Ok(def)
    }

    fn define_func(&mut self, id: Ident, ret: Type, params: Params) -> Result<FuncDef, Log> {
        let def = FuncDef::new(id.clone(), ret, params, &self.scope_tree.borrow());
        let replaced = self.scope_tree.borrow_mut().define_func(def.clone());

        if let Some(replaced) = replaced {
            match replaced {
                ItemDef::Package(def) => {
                    panic!("package '{}' redefined by function '{}'", def.name, id.name);
                },
                ItemDef::Module(def) => {
                    panic!("module '{}' redefined by function '{}'", def.name, id.name);
                }
                ItemDef::Func(def) => {
                    return crate::log::error(ParseError::PathNameCollision(def.id))
                        .with_span(&id.span, &self.source)
                        .handled(self)
                        .into_result();
                }
                ItemDef::Var(def) => {
                    panic!("variable '{}' redefined by function '{}'", def.id.name, id.name);
                }
                ItemDef::Block(def) => {
                    panic!("block '{}' redefined by function '{}'", def.name, id.name);
                }
            }
        }
        Ok(def)
    }

    fn define_block(&self, span: &Span) -> Ident {
        let id = Ident::new_unnamed(span);
        let replaced = self.scope_tree.borrow_mut().define_block(id.clone());
        assert!(replaced.is_none(), "blocks shouldn't cause redefinitions!");
        id
    }

    #[inline]
    fn define_var(&self, id: Ident, ty: Type) -> VarDef {
        let def = VarDef::new(id, ty);
        self.scope_tree.borrow_mut().define_var(def.clone());
        def
    }

    #[inline]
    fn has_defined_id(&self, path: &Path) -> bool {
        self.scope_tree.borrow_mut().contains(path)
    }

    #[inline]
    pub fn has_errors(&self) -> bool { self.error_count() != 0 }
    #[inline]
    pub fn error_count(&self) -> usize { *self.error_count.borrow() }

    #[inline]
    pub fn has_warnings(&self) -> bool { self.warning_count() != 0 }
    #[inline]
    pub fn warning_count(&self) -> usize { *self.warn_count.borrow() }
}

fn get_unary_op_info(ty: &TokenType) -> OpInfo {
    match ty {
        TokenType::Not =>
            OpInfo { token_type: TokenType::Not, precedence: 12, associativity: Associativity::Right },

        TokenType::Plus =>
            OpInfo { token_type: TokenType::Plus, precedence: 12, associativity: Associativity::Right },
        TokenType::Minus =>
            OpInfo { token_type: TokenType::Minus, precedence: 12, associativity: Associativity::Right },

        _ => panic!("operator info not defined for token type {ty}"),
    }
}

fn get_binary_op_info(ty: &TokenType) -> OpInfo {
    match ty {
        TokenType::Dot =>
            OpInfo { token_type: TokenType::Dot, precedence: 13, associativity: Associativity::Left },

        TokenType::Star =>
            OpInfo { token_type: TokenType::Star, precedence: 10, associativity: Associativity::Left },
        TokenType::Slash =>
            OpInfo { token_type: TokenType::Slash, precedence: 10, associativity: Associativity::Left },
        TokenType::Percent =>
            OpInfo { token_type: TokenType::Percent, precedence: 10, associativity: Associativity::Left },
        TokenType::Plus =>
            OpInfo { token_type: TokenType::Plus, precedence: 9, associativity: Associativity::Left },
        TokenType::Minus =>
            OpInfo { token_type: TokenType::Minus, precedence: 9, associativity: Associativity::Left },

        TokenType::Lesser =>
            OpInfo { token_type: TokenType::Lesser, precedence: 8, associativity: Associativity::Left },
        TokenType::LesserEq =>
            OpInfo { token_type: TokenType::LesserEq, precedence: 8, associativity: Associativity::Left },
        TokenType::Greater =>
            OpInfo { token_type: TokenType::Greater, precedence: 8, associativity: Associativity::Left },
        TokenType::GreaterEq =>
            OpInfo { token_type: TokenType::GreaterEq, precedence: 8, associativity: Associativity::Left },

        TokenType::Eq =>
            OpInfo { token_type: TokenType::Eq, precedence: 7, associativity: Associativity::Left },
        TokenType::Neq =>
            OpInfo { token_type: TokenType::Neq, precedence: 7, associativity: Associativity::Left },

        TokenType::LogicAnd =>
            OpInfo { token_type: TokenType::LogicAnd, precedence: 3, associativity: Associativity::Left },
        TokenType::LogicOr =>
            OpInfo { token_type: TokenType::LogicOr, precedence: 2, associativity: Associativity::Left },

        TokenType::Assign =>
            OpInfo { token_type: TokenType::Assign, precedence: 1, associativity: Associativity::Right },
        TokenType::AndAssign =>
            OpInfo { token_type: TokenType::AndAssign, precedence: 1, associativity: Associativity::Right },
        TokenType::OrAssign =>
            OpInfo { token_type: TokenType::OrAssign, precedence: 1, associativity: Associativity::Right },
        TokenType::AddAssign =>
            OpInfo { token_type: TokenType::AddAssign, precedence: 1, associativity: Associativity::Right },
        TokenType::SubAssign =>
            OpInfo { token_type: TokenType::SubAssign, precedence: 1, associativity: Associativity::Right },
        TokenType::MulAssign =>
            OpInfo { token_type: TokenType::MulAssign, precedence: 1, associativity: Associativity::Right },
        TokenType::DivAssign =>
            OpInfo { token_type: TokenType::DivAssign, precedence: 1, associativity: Associativity::Right },
        TokenType::ModAssign =>
            OpInfo { token_type: TokenType::ModAssign, precedence: 1, associativity: Associativity::Right },

        _ => panic!("operator info not defined for token type {ty}"),
    }
}

#[derive(Debug, Clone)]
struct OpInfo {
    pub token_type: TokenType,
    pub precedence: u32,
    pub associativity: Associativity,
}

#[derive(Debug, Clone, Eq, PartialEq)]
enum Associativity { Left, Right }
