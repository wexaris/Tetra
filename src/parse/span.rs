use std::fmt::Formatter;
use std::io::BufRead;
use std::path::PathBuf;

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub struct SourceFile {
    pub file: PathBuf,
}

impl SourceFile {
    pub fn get_filename(&self) -> Option<&str> {
        if let Some(file_stem) = self.file.file_stem() {
            if let Some(name) = file_stem.to_str() {
                return Some(name);
            }
        }
        None
    }
}

impl From<PathBuf> for SourceFile {
    fn from(p: PathBuf) -> Self { Self { file: p } }
}

impl std::ops::Deref for SourceFile {
    type Target = PathBuf;
    fn deref(&self) -> &Self::Target { &self.file }
}
impl std::fmt::Display for SourceFile {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.file.display())
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub struct FileSpan {
    pub file: SourceFile,
    pub span: Span,
}

impl FileSpan {
    pub fn new(file: SourceFile, span: Span) -> Self { Self { file, span } }

    pub fn read_line(&self) -> std::io::Result<String> {
        let file = std::fs::File::open(self.file.as_path())?;
        let file = std::io::BufReader::new(file);

        if let Some(line) = file.lines().skip(self.span.start.line - 1).next() {
            return Ok(line?);
        }

        Ok(String::new())
    }
}

impl std::fmt::Display for FileSpan {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.file.display(), self.span)
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub struct Span {
    pub start: FilePos,
    pub len: usize,
}

impl Span {
    pub fn new(start: FilePos, len: usize) -> Self {
        Self { start, len, }
    }

    pub fn initial() -> Self { Span::new(FilePos::initial(), 1) }

    pub fn next_pos(&self) -> FilePos {
        FilePos::new(self.start.idx + self.len, self.start.line, self.start.col + self.len)
    }

    pub fn next_char(&self) -> Span {
        Self::new(self.next_pos(), 1)
    }

    pub fn with_file(&self, file: &SourceFile) -> FileSpan {
        FileSpan { file: file.clone(), span: self.clone() }
    }
}

impl std::fmt::Display for Span {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.start)
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct FilePos {
    pub idx: usize,
    pub line: usize,
    pub col: usize,
}

impl FilePos {
    pub fn new(idx: usize, line: usize, col: usize) -> Self {
        Self { idx, line, col, }
    }

    pub fn initial() -> Self { FilePos::new(0, 1, 1) }
}

impl std::fmt::Display for FilePos {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}
