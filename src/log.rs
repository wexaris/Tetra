use std::fmt::{Debug, Display, Formatter};
use std::io::Write;
use std::rc::Rc;
use env_logger::fmt::style::{AnsiColor, Style};
use log::{Level, LevelFilter};
use crate::parse::{SourceFile, Span};

pub fn init() {
    let mut builder = env_logger::builder();
    builder.filter_level(LevelFilter::Info);
    builder.format(|fmt, record| {
        let level = {
            let level = record.level();
            match level {
                Level::Error => {}
                Level::Warn => {}
                Level::Info => {}
                Level::Debug => {}
                Level::Trace => {}
            }
            let style = fmt.default_level_style(level);
            let level_str = level.as_str().to_lowercase();
            format!("{style}{level_str}{style:#}")
        };
        let msg = {
            let style = Style::new().bold();
            let args = record.args();
            format!("{style}{args}{style:#}")
        };
        writeln!(fmt, "{level}: {msg}\n")
    });
    builder.init();
}

pub fn error<'a, M: LogMsg + 'static>(msg: M) -> LogBuilder<'a> {
    LogBuilder {
        log: Log {
            level: Level::Error,
            msg: Rc::new(msg),
            ..Default::default()
        },
        handler: None,
    }
}

pub fn warn<'a, M: LogMsg + 'static>(msg: M) -> LogBuilder<'a> {
    LogBuilder {
        log: Log {
            level: Level::Warn,
            msg: Rc::new(msg),
            ..Default::default()
        },
        handler: None,
    }
}

pub struct LogBuilder<'a> {
    log: Log,
    handler: Option<&'a dyn LogHandler>,
}

impl<'a> LogBuilder<'a> {
    pub fn with_level(mut self, level: Level) -> Self {
        self.log.level = level;
        Self { log: self.log, handler: self.handler }
    }

    pub fn with_span(mut self, span: &Span, source: &SourceFile) -> Self {
        self.log.span = Some(span.clone());
        self.log.file = Some(source.clone());
        Self { log: self.log, handler: self.handler }
    }

    pub fn with_file(mut self, source: &SourceFile) -> Self {
        self.log.file = Some(source.clone());
        Self { log: self.log, handler: self.handler }
    }

    pub fn handled(self, handler: &'a dyn LogHandler) -> Self {
        Self { log: self.log, handler: Some(handler) }
    }

    #[inline]
    pub fn print(self) { self.emit().print(); }

    #[inline]
    pub fn into_result<T>(self) -> Result<T, Log> { Err(self.emit()) }

    pub fn emit(mut self) -> Log {
        if !self.log.canceled {
            if let Some(handler) = self.handler {
                self.log.canceled |= !handler.on_emit(&mut self.log);
            }
        }
        self.log
    }
}

pub trait LogHandler {
    fn on_emit(&self, _log: &mut Log) -> bool { true }
}

pub trait LogMsg: Display + Debug {}
impl<T: Display + Debug> LogMsg for T {}

#[derive(Clone)]
pub struct Log {
    pub canceled: bool,
    pub level: Level,
    pub msg: Rc<dyn LogMsg>,
    pub span: Option<Span>,
    pub file: Option<SourceFile>,
}

impl Default for Log {
    fn default() -> Self {
        Self {
            canceled: false,
            level: Level::Info,
            msg: Rc::new(""),
            span: None,
            file: None,
        }
    }
}

impl Log {
    #[inline]
    pub fn print(self) {
        if !self.canceled {
            log::log!(self.level, "{self}");
        }
    }

    #[inline]
    pub fn is_error(&self) -> bool { self.level == Level::Error }
    #[inline]
    pub fn is_warn(&self) -> bool { self.level == Level::Warn }
    #[inline]
    pub fn is_info(&self) -> bool { self.level == Level::Info }
    #[inline]
    pub fn is_trace(&self) -> bool { self.level == Level::Trace }
    #[inline]
    pub fn is_debug(&self) -> bool { self.level == Level::Debug }
}

impl Debug for Log {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let span = self.span.as_ref()
            .map(|span| format!("{span}: "))
            .unwrap_or_default();
        write!(f, "[{}] {span}{}", &self.level, &self.msg)
    }
}

impl Display for Log {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let msg = &self.msg;

        let span_fmt = if let Some(file) = &self.file {
            let blue = Style::new()
                .fg_color(Some(AnsiColor::BrightBlue.into()))
                .bold();

            if let Some(span) = &self.span {
                let line_num = span.start.line.to_string();

                // padding for line number
                let line_pad = std::iter::repeat(' ')
                    .take(line_num.len())
                    .collect::<String>();

                // format markers (^^^) for issue span
                let line = if let Ok(line_full) = span.with_file(file).read_line() {
                    let line = line_full.trim_start();

                    let col_pad = std::iter::repeat(' ')
                        .take(span.start.col - (line_full.len() - line.len()))
                        .collect::<String>();

                    let marker = {
                        let style = Style::new()
                            .fg_color(Some(AnsiColor::Yellow.into()))
                            .bold();
                        let marker = std::iter::repeat('^')
                            .take(span.len)
                            .collect::<String>();
                        format!("{style}{marker}{style:#}")
                    };

                    let line = line.trim(); // trim both ends

                    format!("\n{blue} {line_pad} |\n {line_num} |{blue:#} {line}{blue}\n {line_pad} |{blue:#}{col_pad}{marker}")
                } else {
                    String::new()
                };
                format!("\n{line_pad} {blue}-->{blue:#} {}:{span}{line}", file.display())
            } else {
                format!("\n   {blue}-->{blue:#} {}", file.display())
            }
        } else {
            String::new()
        };

        write!(f, "{msg}{span_fmt}")
    }
}
