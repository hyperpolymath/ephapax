// SPDX-License-Identifier: EUPL-1.2
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Error reporting for the Ephapax parser
//!
//! Uses ariadne for rich, colorful error messages.

use ariadne::{Cache, Color, Label, Report as AriadneReport, ReportKind, Source};
use ephapax_syntax::Span;
use std::fmt;
use thiserror::Error;

/// Parser error types
#[derive(Error, Debug, Clone)]
pub enum ParseError {
    #[error("Lexer error: {0}")]
    Lexer(String),

    #[error("Syntax error: {message}")]
    Syntax { message: String, span: Span },

    #[error("Unexpected end of file")]
    UnexpectedEof { span: Span },

    #[error("Expected {expected}, found {found}")]
    Expected {
        expected: String,
        found: String,
        span: Span,
    },
}

impl ParseError {
    pub fn span(&self) -> Span {
        match self {
            ParseError::Lexer(_) => Span::dummy(),
            ParseError::Syntax { span, .. } => *span,
            ParseError::UnexpectedEof { span } => *span,
            ParseError::Expected { span, .. } => *span,
        }
    }
}

/// A rendered error report
pub struct Report {
    source_name: String,
    source: String,
    errors: Vec<ParseError>,
}

impl Report {
    pub fn new(source_name: impl Into<String>, source: impl Into<String>, errors: Vec<ParseError>) -> Self {
        Self {
            source_name: source_name.into(),
            source: source.into(),
            errors,
        }
    }

    /// Print the report to stderr
    pub fn eprint(&self) {
        let mut cache = SingleFileCache::new(&self.source_name, &self.source);

        for error in &self.errors {
            let report = self.build_report(error);
            report.eprint(&mut cache).ok();
        }
    }

    /// Render the report to a string
    pub fn to_string_colored(&self) -> String {
        let mut output = Vec::new();
        let mut cache = SingleFileCache::new(&self.source_name, &self.source);

        for error in &self.errors {
            let report = self.build_report(error);
            report.write(&mut cache, &mut output).ok();
        }

        String::from_utf8(output).unwrap_or_default()
    }

    fn build_report(&self, error: &ParseError) -> AriadneReport<'_, (String, std::ops::Range<usize>)> {
        let span = error.span();
        let range = span.start..span.end;
        let location = (self.source_name.clone(), range.clone());

        match error {
            ParseError::Lexer(msg) => AriadneReport::build(ReportKind::Error, self.source_name.clone(), range.start)
                .with_message("Lexer error")
                .with_label(
                    Label::new(location)
                        .with_message(msg)
                        .with_color(Color::Red),
                )
                .finish(),

            ParseError::Syntax { message, .. } => {
                AriadneReport::build(ReportKind::Error, self.source_name.clone(), range.start)
                    .with_message("Syntax error")
                    .with_label(
                        Label::new(location)
                            .with_message(message)
                            .with_color(Color::Red),
                    )
                    .finish()
            }

            ParseError::UnexpectedEof { .. } => {
                AriadneReport::build(ReportKind::Error, self.source_name.clone(), range.start)
                    .with_message("Unexpected end of file")
                    .with_label(
                        Label::new(location)
                            .with_message("expected more input here")
                            .with_color(Color::Red),
                    )
                    .finish()
            }

            ParseError::Expected { expected, found, .. } => {
                AriadneReport::build(ReportKind::Error, self.source_name.clone(), range.start)
                    .with_message(format!("Expected {}", expected))
                    .with_label(
                        Label::new(location)
                            .with_message(format!("found {} instead", found))
                            .with_color(Color::Red),
                    )
                    .finish()
            }
        }
    }

    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    pub fn error_count(&self) -> usize {
        self.errors.len()
    }
}

impl fmt::Display for Report {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_string_colored())
    }
}

/// Simple cache for a single file
struct SingleFileCache {
    name: String,
    source: Source<String>,
}

impl SingleFileCache {
    fn new(name: &str, source: &str) -> Self {
        Self {
            name: name.to_string(),
            source: Source::from(source.to_string()),
        }
    }
}

impl Cache<String> for SingleFileCache {
    type Storage = String;

    fn fetch(
        &mut self,
        id: &String,
    ) -> Result<&Source<Self::Storage>, Box<dyn std::fmt::Debug + '_>> {
        if id == &self.name {
            Ok(&self.source)
        } else {
            Err(Box::new(format!("Unknown file: {}", id)))
        }
    }

    fn display<'a>(&self, id: &'a String) -> Option<Box<dyn std::fmt::Display + 'a>> {
        Some(Box::new(id.clone()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_report_creation() {
        let errors = vec![ParseError::Syntax {
            message: "test error".to_string(),
            span: Span::new(0, 5),
        }];

        let report = Report::new("test.epx", "hello", errors);
        assert!(report.has_errors());
        assert_eq!(report.error_count(), 1);
    }
}
