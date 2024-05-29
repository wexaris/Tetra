use display_tree::{AsTree, DisplayTree, Style};
use display_tree::to_display_tree_ref::ToDisplayTreeRef;
use crate::ast::*;

impl std::fmt::Display for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Ident ({})", self.name)
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl DisplayTree for Module {
    fn fmt(&self, f: &mut std::fmt::Formatter, style: Style) -> std::fmt::Result {
        let name = format!("{} ({})", type_name_only::<Self>(), self.def.name);
        write_inline(name, f, style)?;
        write_tree_refs(&self.items, f, style)
    }
}

impl DisplayTree for Stmt {
    fn fmt(&self, f: &mut std::fmt::Formatter, style: Style) -> std::fmt::Result {
        match self {
            Stmt::Block(block) => DisplayTree::fmt(block, f, style),
            Stmt::VarDecl(decl) => DisplayTree::fmt(decl, f, style),
            Stmt::Branch(stmt) => DisplayTree::fmt(stmt, f, style),
            Stmt::ForLoop(stmt) => DisplayTree::fmt(stmt, f, style),
            Stmt::WhileLoop(stmt) => DisplayTree::fmt(stmt, f, style),
            Stmt::Loop(stmt) => DisplayTree::fmt(stmt, f, style),
            Stmt::Continue(stmt) => DisplayTree::fmt(stmt, f, style),
            Stmt::Break(stmt) => DisplayTree::fmt(stmt, f, style),
            Stmt::Return(stmt) => DisplayTree::fmt(stmt, f, style),
            Stmt::FuncDecl(decl) => DisplayTree::fmt(decl, f, style),
            Stmt::Expr(expr) => DisplayTree::fmt(expr.as_ref(), f, style),
        }
    }
}

impl DisplayTree for VarDecl {
    fn fmt(&self, f: &mut std::fmt::Formatter, style: Style) -> std::fmt::Result {
        write_inline(format!("VarDecl ({}: {})", self.def.id.name, self.def.ty), f, style)?;

        let name = format!("{}", AsTree::with_style(self.value.to_display_tree(), style));
        write_branch(name, f, style, true)
    }
}

impl DisplayTree for Branch {
    fn fmt(&self, f: &mut std::fmt::Formatter, style: Style) -> std::fmt::Result {
        write_inline(type_name_only::<Self>(), f, style)?;

        let cond = format!("{}", AsTree::with_style(self.cond.to_display_tree(), style));
        write_branch(cond, f, style, false)?;

        let name = format!("True {}", AsTree::with_style(self.true_block.to_display_tree(), style));
        write_branch(name, f, style, self.false_block.is_none())?;

        if let Some(false_block) = &self.false_block {
            let name = format!("False {}", AsTree::with_style(false_block.to_display_tree(), style));
            write_branch(name, f, style, true)?;
        }
        Ok(())
    }
}

impl DisplayTree for Return {
    fn fmt(&self, f: &mut std::fmt::Formatter, style: Style) -> std::fmt::Result {
        write_inline("Return", f, style)?;
        if let Some(val) = &self.value {
            let val = format!("{}", AsTree::with_style(val.to_display_tree(), style));
            write_branch(&val, f, style, true)?;
        }
        Ok(())
    }
}

impl DisplayTree for FuncDecl {
    fn fmt(&self, f: &mut std::fmt::Formatter, style: Style) -> std::fmt::Result {
        write_inline(format!("FuncDecl ({}: {})", self.def.id.name, self.def.ret), f, style)?;

        let params = format!("{}", AsTree::with_style(self.def.params.to_display_tree(), style));
        write_branch(params, f, style, false)?;

        let name = format!("{}", AsTree::with_style(self.block.to_display_tree(), style));
        write_branch(name, f, style, true)
    }
}

impl DisplayTree for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter, style: Style) -> std::fmt::Result {
        match self {
            Expr::VarAccess(sym) => {
                let name = format!("VarAccess ({})", sym.path);
                write_inline(name, f, style)
            }
            Expr::UnaryOp(op) => DisplayTree::fmt(op, f, style),
            Expr::BinaryOp(op) => DisplayTree::fmt(op, f, style),
            Expr::FuncCall(call) => DisplayTree::fmt(call, f, style),
            Expr::Number(val, _) => {
                write_inline(format!("Number ({val})"), f, style)
            }
            Expr::Bool(val, _) => {
                write_inline(format!("Bool ({val})"), f, style)
            }
        }
    }
}

impl DisplayTree for FuncCall {
    fn fmt(&self, f: &mut std::fmt::Formatter, style: Style) -> std::fmt::Result {
        write_inline(format!("FuncCall ({})", self.symbol.path), f, style)?;
        write_trees(&self.args.items, f, style)
    }
}

impl DisplayTree for Params {
    fn fmt(&self, f: &mut std::fmt::Formatter, style: Style) -> std::fmt::Result {
        write_inline(type_name_only::<Self>(), f, style)?;
        write_trees(&self.items, f, style)
    }
}

impl DisplayTree for Param {
    fn fmt(&self, f: &mut std::fmt::Formatter, style: Style) -> std::fmt::Result {
        write_inline(format!("Param ({}: {})", self.def.id.name, self.def.ty), f, style)
    }
}

impl DisplayTree for Args {
    fn fmt(&self, f: &mut std::fmt::Formatter, style: Style) -> std::fmt::Result {
        write_inline(type_name_only::<Self>(), f, style)?;
        write_trees(&self.items, f, style)
    }
}

impl DisplayTree for Arg {
    fn fmt(&self, f: &mut std::fmt::Formatter, style: Style) -> std::fmt::Result {
        DisplayTree::fmt(self.expr.as_ref(), f, style)
    }
}

impl DisplayTree for Block {
    fn fmt(&self, f: &mut std::fmt::Formatter, style: Style) -> std::fmt::Result {
        write_inline(format!("Block ({})", self.id.name), f, style)?;
        write_tree_refs(&self.items, f, style)
    }
}

#[inline]
fn write_tree_refs<T: DisplayTree>(items: &[Box<T>], f: &mut std::fmt::Formatter, style: Style) -> std::fmt::Result {
    for (idx, x) in items.iter().enumerate() {
        let item = format!("{}", AsTree::with_style(x.to_display_tree(), style));
        let is_last = idx == items.len() - 1;
        write_branch(item, f, style, is_last)?;
    }
    Ok(())
}

#[inline]
fn write_trees<T: DisplayTree>(items: &[T], f: &mut std::fmt::Formatter, style: Style) -> std::fmt::Result {
    for (idx, x) in items.iter().enumerate() {
        let item = format!("{}", AsTree::with_style(x.to_display_tree(), style));
        let is_last = idx == items.len() - 1;
        write_branch(item, f, style, is_last)?;
    }
    Ok(())
}

#[inline]
fn write_inline<S: AsRef<str>>(item_str: S, f: &mut std::fmt::Formatter, style: Style) -> std::fmt::Result {
    writeln!(f, "{}", style.leaf_style.apply(item_str.as_ref()))
}

#[inline]
fn write_leaf<S: AsRef<str>>(item_str: S, f: &mut std::fmt::Formatter, style: Style, last: bool) -> std::fmt::Result {
    let item = style.leaf_style.apply(item_str.as_ref());
    write_branch(item, f, style, last)
}

fn write_branch<S: AsRef<str>>(item_str: S, f: &mut std::fmt::Formatter, style: Style, last: bool) -> std::fmt::Result {
    let branch = fmt_indent(item_str, style, true, last);
    writeln!(f, "{}", branch)
}

fn fmt_indent<S: AsRef<str>>(item_str: S, style: Style, branch_self: bool, last: bool) -> String {
    let mut ret = String::new();

    let mut lines = item_str.as_ref().lines();
    if !last {
        if branch_self {
            ret += &format!("{}{}", style.branch_style.apply(
                &format!("{}{} ", style.char_set.connector,
                    std::iter::repeat(style.char_set.horizontal)
                        .take(style.indentation as usize)
                        .collect::<String>())),
                    lines.next().unwrap_or_default());
        }
        else {
            ret += &format!("\n{}{}", style.branch_style.apply(
                &format!("{}{} ", style.char_set.vertical,
                    std::iter::repeat(' ')
                        .take(style.indentation as usize)
                        .collect::<String>())),
                    lines.next().unwrap_or_default());
        }
        for line in lines {
            ret += &format!("\n{}{}", style.branch_style.apply(
                &format!("{}{} ", style.char_set.vertical,
                    std::iter::repeat(' ')
                        .take(style.indentation as usize)
                        .collect::<String>())),
                    line);
        };
    }
    else {
        if branch_self {
            ret += &format!("{}{}", style.branch_style.apply(
                &format!("{}{} ", style.char_set.end_connector,
                    std::iter::repeat(style.char_set.horizontal)
                        .take(style.indentation as usize)
                        .collect::<String>())),
                    lines.next().unwrap_or_default());
        }
        else {
            ret += &format!("{}{}", style.branch_style.apply(
                &format!(" {} ",
                    std::iter::repeat(' ')
                        .take(style.indentation as usize)
                        .collect::<String>())),
                    lines.next().unwrap_or_default());
        }
        for line in lines {
            ret += &format!("\n{}{}", style.branch_style.apply(
                &format!(" {} ",
                    std::iter::repeat(' ')
                        .take(style.indentation as usize)
                        .collect::<String>())),
                    line);
        };
    }
    ret
}

#[inline]
fn type_name_only<T>() -> &'static str {
    std::any::type_name::<T>().split("::").last().unwrap_or_default()
}
