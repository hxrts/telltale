//! Diagnostic Framework for Choreographic Compilation
//!
//! This module provides a comprehensive error and warning system for the
//! choreography compiler, including:
//!
//! - Error codes for programmatic handling
//! - Detailed error messages with source locations
//! - Suggestions for common mistakes
//! - Severity levels for errors and warnings
//!
//! # Error Code Format
//!
//! Error codes follow the format `CXXX` where:
//! - `C` is the category (R=Role, M=Message, S=Syntax, P=Protocol)
//! - `XXX` is a numeric identifier
//!
//! # Example
//!
//! ```ignore
//! error[R001]: Undefined role 'Bob'
//!   --> protocol.chor:5:3
//!    |
//!  5 | Alice -> Bob: Request;
//!    |          ^^^ Role 'Bob' is not declared
//!    |
//!  = help: Add 'Bob' to the roles declaration, or check for typos
//!  = note: Available roles: Alice, Server
//! ```

use std::collections::HashSet;
use std::fmt;

/// Error codes for choreography compilation.
///
/// These codes help users quickly identify error types and find solutions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DiagnosticCode {
    // Role errors (R001-R099)
    /// Role referenced but not declared
    UndefinedRole,
    /// Role declared multiple times
    DuplicateRole,
    /// Invalid role index (out of bounds)
    RoleIndexOutOfBounds,
    /// Invalid role parameter
    InvalidRoleParam,
    /// Self-communication (role sends to itself)
    SelfCommunication,

    // Message errors (M001-M099)
    /// Message type not defined
    UndefinedMessage,
    /// Duplicate message type
    DuplicateMessage,
    /// Message payload type mismatch
    MessageTypeMismatch,
    /// Invalid message format
    InvalidMessageFormat,

    // Syntax errors (S001-S099)
    /// General syntax error
    SyntaxError,
    /// Missing required element
    MissingElement,
    /// Unexpected token
    UnexpectedToken,
    /// Invalid identifier
    InvalidIdentifier,

    // Protocol errors (P001-P099)
    /// Empty protocol
    EmptyProtocol,
    /// Unreachable code
    UnreachableCode,
    /// Infinite loop without termination
    InfiniteLoop,
    /// Choice without branches
    EmptyChoice,
    /// Duplicate branch label
    DuplicateBranch,

    // Annotation errors (A001-A099)
    /// Invalid annotation key
    InvalidAnnotationKey,
    /// Invalid annotation value
    InvalidAnnotationValue,
    /// Conflicting annotations
    ConflictingAnnotations,

    // Choice propagation errors (C001-C099)
    /// Role cannot determine which branch was selected
    ChoicePropagationError,
    /// Choice has no distinguishing messages
    IndistinguishableChoiceBranches,
}

impl DiagnosticCode {
    /// Get the numeric code string (e.g., "R001").
    #[must_use]
    pub fn code(&self) -> &'static str {
        match self {
            // Role errors
            Self::UndefinedRole => "R001",
            Self::DuplicateRole => "R002",
            Self::RoleIndexOutOfBounds => "R003",
            Self::InvalidRoleParam => "R004",
            Self::SelfCommunication => "R005",

            // Message errors
            Self::UndefinedMessage => "M001",
            Self::DuplicateMessage => "M002",
            Self::MessageTypeMismatch => "M003",
            Self::InvalidMessageFormat => "M004",

            // Syntax errors
            Self::SyntaxError => "S001",
            Self::MissingElement => "S002",
            Self::UnexpectedToken => "S003",
            Self::InvalidIdentifier => "S004",

            // Protocol errors
            Self::EmptyProtocol => "P001",
            Self::UnreachableCode => "P002",
            Self::InfiniteLoop => "P003",
            Self::EmptyChoice => "P004",
            Self::DuplicateBranch => "P005",

            // Annotation errors
            Self::InvalidAnnotationKey => "A001",
            Self::InvalidAnnotationValue => "A002",
            Self::ConflictingAnnotations => "A003",

            // Choice propagation errors
            Self::ChoicePropagationError => "C001",
            Self::IndistinguishableChoiceBranches => "C002",
        }
    }

    /// Get a documentation URL for this error code.
    #[must_use]
    pub fn doc_url(&self) -> String {
        format!(
            "https://telltale.dev/errors/{}",
            self.code().to_lowercase()
        )
    }
}

impl fmt::Display for DiagnosticCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.code())
    }
}

/// Severity levels for diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Severity {
    /// Informational note
    Note,
    /// Warning (code will compile but may have issues)
    Warning,
    /// Error (compilation will fail)
    Error,
}

impl fmt::Display for Severity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Note => write!(f, "note"),
            Self::Warning => write!(f, "warning"),
            Self::Error => write!(f, "error"),
        }
    }
}

/// A location in source code.
#[derive(Debug, Clone)]
pub struct SourceLocation {
    /// Line number (1-indexed)
    pub line: usize,
    /// Column number (1-indexed)
    pub column: usize,
    /// End line (for multi-line spans)
    pub end_line: usize,
    /// End column
    pub end_column: usize,
    /// The source line content
    pub source_line: String,
    /// Optional file name
    pub file: Option<String>,
}

impl SourceLocation {
    /// Create a new source location.
    pub fn new(line: usize, column: usize, source_line: impl Into<String>) -> Self {
        Self {
            line,
            column,
            end_line: line,
            end_column: column + 1,
            source_line: source_line.into(),
            file: None,
        }
    }

    /// Create with an end position.
    pub fn with_end(mut self, end_line: usize, end_column: usize) -> Self {
        self.end_line = end_line;
        self.end_column = end_column;
        self
    }

    /// Create with a file name.
    pub fn with_file(mut self, file: impl Into<String>) -> Self {
        self.file = Some(file.into());
        self
    }
}

/// A diagnostic message (error, warning, or note).
#[derive(Debug, Clone)]
pub struct Diagnostic {
    /// The error code
    pub code: DiagnosticCode,
    /// Severity level
    pub severity: Severity,
    /// Main error message
    pub message: String,
    /// Source location
    pub location: Option<SourceLocation>,
    /// Suggested fixes
    pub suggestions: Vec<String>,
    /// Additional notes
    pub notes: Vec<String>,
    /// Related information
    pub related: Vec<RelatedInfo>,
}

/// Related information for a diagnostic.
#[derive(Debug, Clone)]
pub struct RelatedInfo {
    /// Related location
    pub location: SourceLocation,
    /// Message
    pub message: String,
}

impl Diagnostic {
    /// Create a new diagnostic.
    pub fn new(code: DiagnosticCode, severity: Severity, message: impl Into<String>) -> Self {
        Self {
            code,
            severity,
            message: message.into(),
            location: None,
            suggestions: Vec::new(),
            notes: Vec::new(),
            related: Vec::new(),
        }
    }

    /// Create an error diagnostic.
    pub fn error(code: DiagnosticCode, message: impl Into<String>) -> Self {
        Self::new(code, Severity::Error, message)
    }

    /// Create a warning diagnostic.
    pub fn warning(code: DiagnosticCode, message: impl Into<String>) -> Self {
        Self::new(code, Severity::Warning, message)
    }

    /// Add a source location.
    pub fn with_location(mut self, location: SourceLocation) -> Self {
        self.location = Some(location);
        self
    }

    /// Add a suggestion.
    pub fn with_suggestion(mut self, suggestion: impl Into<String>) -> Self {
        self.suggestions.push(suggestion.into());
        self
    }

    /// Add a note.
    pub fn with_note(mut self, note: impl Into<String>) -> Self {
        self.notes.push(note.into());
        self
    }

    /// Add related information.
    pub fn with_related(mut self, location: SourceLocation, message: impl Into<String>) -> Self {
        self.related.push(RelatedInfo {
            location,
            message: message.into(),
        });
        self
    }

    /// Format the diagnostic for display.
    #[must_use]
    pub fn format(&self) -> String {
        let mut output = String::new();

        // Header: error[R001]: message
        output.push_str(&format!(
            "{}[{}]: {}\n",
            self.severity, self.code, self.message
        ));

        // Location
        if let Some(loc) = &self.location {
            let file = loc.file.as_deref().unwrap_or("input");
            output.push_str(&format!("  --> {}:{}:{}\n", file, loc.line, loc.column));

            // Source line with indicator
            let line_num_width = loc.line.to_string().len().max(3);
            output.push_str(&format!("{:width$} |\n", " ", width = line_num_width));
            output.push_str(&format!(
                "{:>width$} | {}\n",
                loc.line,
                loc.source_line,
                width = line_num_width
            ));

            // Underline
            let spaces = " ".repeat(line_num_width + 3 + loc.column - 1);
            let underline_len = if loc.line == loc.end_line {
                (loc.end_column - loc.column).max(1)
            } else {
                loc.source_line.len().saturating_sub(loc.column) + 1
            };
            let underline = "^".repeat(underline_len);
            output.push_str(&format!("{spaces}{underline}\n"));
        }

        // Suggestions
        for suggestion in &self.suggestions {
            output.push_str(&format!("  = help: {suggestion}\n"));
        }

        // Notes
        for note in &self.notes {
            output.push_str(&format!("  = note: {note}\n"));
        }

        // Related info
        for related in &self.related {
            let file = related.location.file.as_deref().unwrap_or("input");
            output.push_str(&format!(
                "  --> {}:{}:{}: {}\n",
                file, related.location.line, related.location.column, related.message
            ));
        }

        output
    }
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.format())
    }
}

/// Collector for diagnostics during compilation.
#[derive(Debug, Default)]
pub struct DiagnosticCollector {
    diagnostics: Vec<Diagnostic>,
}

impl DiagnosticCollector {
    /// Create a new collector.
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a diagnostic.
    pub fn add(&mut self, diagnostic: Diagnostic) {
        self.diagnostics.push(diagnostic);
    }

    /// Add an error.
    pub fn error(&mut self, code: DiagnosticCode, message: impl Into<String>) {
        self.add(Diagnostic::error(code, message));
    }

    /// Add a warning.
    pub fn warning(&mut self, code: DiagnosticCode, message: impl Into<String>) {
        self.add(Diagnostic::warning(code, message));
    }

    /// Check if there are any errors.
    #[must_use]
    pub fn has_errors(&self) -> bool {
        self.diagnostics
            .iter()
            .any(|d| d.severity == Severity::Error)
    }

    /// Get the number of errors.
    #[must_use]
    pub fn error_count(&self) -> usize {
        self.diagnostics
            .iter()
            .filter(|d| d.severity == Severity::Error)
            .count()
    }

    /// Get the number of warnings.
    #[must_use]
    pub fn warning_count(&self) -> usize {
        self.diagnostics
            .iter()
            .filter(|d| d.severity == Severity::Warning)
            .count()
    }

    /// Get all diagnostics.
    #[must_use]
    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }

    /// Take all diagnostics.
    pub fn take_diagnostics(&mut self) -> Vec<Diagnostic> {
        std::mem::take(&mut self.diagnostics)
    }

    /// Format all diagnostics.
    #[must_use]
    pub fn format_all(&self) -> String {
        let mut output = String::new();
        for diagnostic in &self.diagnostics {
            output.push_str(&diagnostic.format());
            output.push('\n');
        }

        // Summary
        let errors = self.error_count();
        let warnings = self.warning_count();
        if errors > 0 || warnings > 0 {
            output.push_str(&format!(
                "{}: {} error{}, {} warning{}\n",
                if errors > 0 { "aborting" } else { "finished" },
                errors,
                if errors == 1 { "" } else { "s" },
                warnings,
                if warnings == 1 { "" } else { "s" }
            ));
        }

        output
    }
}

// ============================================================================
// Validation Helpers
// ============================================================================

/// Validate that all roles in a protocol are declared.
pub fn validate_roles(
    referenced_roles: &[(&str, Option<SourceLocation>)],
    declared_roles: &HashSet<String>,
    collector: &mut DiagnosticCollector,
) {
    for (role, location) in referenced_roles {
        if !declared_roles.contains(*role) {
            let available: Vec<_> = declared_roles.iter().cloned().collect();
            let mut diagnostic = Diagnostic::error(
                DiagnosticCode::UndefinedRole,
                format!("Undefined role '{role}'"),
            );

            if let Some(loc) = location {
                diagnostic = diagnostic.with_location(loc.clone());
            }

            // Find similar roles for suggestions
            let similar = find_similar_strings(role, &available);
            if !similar.is_empty() {
                diagnostic = diagnostic.with_suggestion(format!("Did you mean '{}'?", similar[0]));
            }

            diagnostic = diagnostic
                .with_suggestion(format!("Add '{role}' to the roles declaration"))
                .with_note(format!("Available roles: {}", available.join(", ")));

            collector.add(diagnostic);
        }
    }
}

/// Check for self-communication (role sending to itself).
pub fn check_self_communication(
    from: &str,
    to: &str,
    location: Option<SourceLocation>,
    collector: &mut DiagnosticCollector,
) {
    if from == to {
        let mut diagnostic = Diagnostic::warning(
            DiagnosticCode::SelfCommunication,
            format!("Role '{from}' sends message to itself"),
        );

        if let Some(loc) = location {
            diagnostic = diagnostic.with_location(loc);
        }

        diagnostic = diagnostic
            .with_note("Self-communication is usually a protocol design error")
            .with_suggestion("Consider splitting into separate roles if this is intentional");

        collector.add(diagnostic);
    }
}

/// Find strings similar to the target (for typo suggestions).
fn find_similar_strings(target: &str, candidates: &[String]) -> Vec<String> {
    let target_lower = target.to_lowercase();
    let mut similar: Vec<_> = candidates
        .iter()
        .filter_map(|s| {
            let distance = levenshtein_distance(&target_lower, &s.to_lowercase());
            if distance <= 2 {
                Some((s.clone(), distance))
            } else {
                None
            }
        })
        .collect();

    similar.sort_by_key(|(_, d)| *d);
    similar.into_iter().map(|(s, _)| s).collect()
}

/// Simple Levenshtein distance implementation.
#[allow(clippy::needless_range_loop)]
fn levenshtein_distance(s1: &str, s2: &str) -> usize {
    let s1_chars: Vec<char> = s1.chars().collect();
    let s2_chars: Vec<char> = s2.chars().collect();
    let m = s1_chars.len();
    let n = s2_chars.len();

    if m == 0 {
        return n;
    }
    if n == 0 {
        return m;
    }

    let mut dp = vec![vec![0usize; n + 1]; m + 1];

    for i in 0..=m {
        dp[i][0] = i;
    }
    for j in 0..=n {
        dp[0][j] = j;
    }

    for i in 1..=m {
        for j in 1..=n {
            let cost = if s1_chars[i - 1] == s2_chars[j - 1] {
                0
            } else {
                1
            };
            dp[i][j] = (dp[i - 1][j] + 1)
                .min(dp[i][j - 1] + 1)
                .min(dp[i - 1][j - 1] + cost);
        }
    }

    dp[m][n]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_diagnostic_code_display() {
        assert_eq!(DiagnosticCode::UndefinedRole.code(), "R001");
        assert_eq!(DiagnosticCode::DuplicateMessage.code(), "M002");
        assert_eq!(DiagnosticCode::SyntaxError.code(), "S001");
    }

    #[test]
    fn test_diagnostic_format() {
        let diagnostic = Diagnostic::error(DiagnosticCode::UndefinedRole, "Undefined role 'Bob'")
            .with_location(SourceLocation::new(5, 10, "Alice -> Bob: Request;").with_end(5, 13))
            .with_suggestion("Add 'Bob' to the roles declaration")
            .with_note("Available roles: Alice, Server");

        let formatted = diagnostic.format();
        assert!(formatted.contains("error[R001]"));
        assert!(formatted.contains("Undefined role 'Bob'"));
        assert!(formatted.contains("help:"));
        assert!(formatted.contains("note:"));
    }

    #[test]
    fn test_levenshtein_distance() {
        assert_eq!(levenshtein_distance("hello", "hello"), 0);
        assert_eq!(levenshtein_distance("hello", "helo"), 1);
        assert_eq!(levenshtein_distance("hello", "world"), 4);
        assert_eq!(levenshtein_distance("", "abc"), 3);
    }

    #[test]
    fn test_find_similar_strings() {
        let candidates = vec![
            "Alice".to_string(),
            "Bob".to_string(),
            "Charlie".to_string(),
        ];
        let similar = find_similar_strings("Alic", &candidates);
        assert_eq!(similar, vec!["Alice"]);
    }

    #[test]
    fn test_collector() {
        let mut collector = DiagnosticCollector::new();
        collector.error(DiagnosticCode::UndefinedRole, "Test error");
        collector.warning(DiagnosticCode::SelfCommunication, "Test warning");

        assert!(collector.has_errors());
        assert_eq!(collector.error_count(), 1);
        assert_eq!(collector.warning_count(), 1);
    }
}
