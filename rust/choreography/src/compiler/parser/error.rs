//! Error types for choreography parsing.
//!
//! This module provides structured error types with span information
//! for helpful error messages during parsing.

use thiserror::Error;

/// Span information for error reporting
#[derive(Debug, Clone)]
pub struct ErrorSpan {
    pub line: usize,
    pub column: usize,
    pub line_end: usize,
    pub column_end: usize,
    pub snippet: String,
}

impl ErrorSpan {
    /// Create an `ErrorSpan` from a Pest span
    pub fn from_pest_span(span: pest::Span, input: &str) -> Self {
        let (line, column) = span.start_pos().line_col();
        let (line_end, column_end) = span.end_pos().line_col();

        // Extract the line containing the error
        let snippet = input.lines().nth(line - 1).unwrap_or("").to_string();

        Self {
            line,
            column,
            line_end,
            column_end,
            snippet,
        }
    }

    /// Create an `ErrorSpan` from a line/column pair.
    pub fn from_line_col(line: usize, column: usize, input: &str) -> Self {
        let snippet = input
            .lines()
            .nth(line.saturating_sub(1))
            .unwrap_or("")
            .to_string();
        Self {
            line,
            column,
            line_end: line,
            column_end: column + 1,
            snippet,
        }
    }

    /// Format the error with context
    #[must_use]
    pub fn format_error(&self, message: &str) -> String {
        let line_num_width = self.line.to_string().len().max(3);
        let mut output = String::new();

        // Error message
        output.push_str(&format!("\n{message}\n"));

        // Location
        output.push_str(&format!(
            "  {} {}:{}:{}\n",
            "-->", "input", self.line, self.column
        ));

        // Empty line
        output.push_str(&format!("{:width$} |\n", " ", width = line_num_width));

        // Source line with line number
        output.push_str(&format!(
            "{:>width$} | {}\n",
            self.line,
            self.snippet,
            width = line_num_width
        ));

        // Underline indicator
        let spaces = " ".repeat(line_num_width + 3 + self.column - 1);
        let underline_len = if self.line == self.line_end {
            (self.column_end - self.column).max(1)
        } else {
            self.snippet.len() - self.column + 1
        };
        let underline = "^".repeat(underline_len);
        output.push_str(&format!("{spaces}{underline}\n"));

        output
    }
}

use super::Rule;

/// Parse errors that can occur during choreography parsing
#[derive(Error, Debug)]
pub enum ParseError {
    #[error("{}", format_pest_error(.0))]
    Pest(#[from] Box<pest::error::Error<Rule>>),

    #[error("{}", .span.format_error(&format!("Layout error: {}", .message)))]
    Layout { span: ErrorSpan, message: String },

    #[error("{}", .span.format_error(&format!("Syntax error: {}", .message)))]
    Syntax { span: ErrorSpan, message: String },

    #[error("{}", .span.format_error(&format!("Undefined role '{}'", .role)))]
    UndefinedRole { role: String, span: ErrorSpan },

    #[error("{}", .span.format_error(&format!("Duplicate role declaration '{}'", .role)))]
    DuplicateRole { role: String, span: ErrorSpan },

    #[error("Empty choreography: no statements found")]
    EmptyChoreography,

    #[error("{}", .span.format_error(&format!("Invalid message format: {}", .message)))]
    InvalidMessage { message: String, span: ErrorSpan },

    #[error("{}", .span.format_error(&format!("Invalid condition: {}", .message)))]
    InvalidCondition { message: String, span: ErrorSpan },

    #[error("{}", .span.format_error(&format!("Undefined protocol '{}'", .protocol)))]
    UndefinedProtocol { protocol: String, span: ErrorSpan },

    #[error("{}", .span.format_error(&format!("Duplicate protocol definition '{}'", .protocol)))]
    DuplicateProtocol { protocol: String, span: ErrorSpan },

    #[error("Grammar composition failed: {0}")]
    GrammarComposition(#[from] crate::compiler::grammar::GrammarCompositionError),
}

/// Format Pest errors nicely
fn format_pest_error(err: &pest::error::Error<Rule>) -> String {
    format!("\nParse error:\n{err}")
}
