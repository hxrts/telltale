// Parser for choreographic protocol syntax
//
// Full implementation using Pest grammar for parsing choreographic DSL

use crate::ast::{
    Branch, Choreography, Condition, MessageType, Protocol, RangeExpr, Role, RoleIndex, RoleParam,
    RoleRange,
};
use crate::extensions::{ExtensionRegistry, ProtocolExtension};
use pest::Parser;
use pest_derive::Parser;
use proc_macro2::{Ident, Span, TokenStream};
use quote::format_ident;
use std::collections::hash_map::DefaultHasher;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::sync::{Arc, RwLock};
use syn::Result;
use thiserror::Error;

#[derive(Parser)]
#[grammar = "compiler/choreography.pest"]
struct ChoreographyParser;

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
    fn from_pest_span(span: pest::Span, input: &str) -> Self {
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

/// Parse errors that can occur during choreography parsing
#[derive(Error, Debug)]
pub enum ParseError {
    #[error("{}", format_pest_error(.0))]
    Pest(#[from] Box<pest::error::Error<Rule>>),

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

    #[error("{}", .span.format_error(&format!("Invalid namespace '{}'", .namespace)))]
    InvalidNamespace { namespace: String, span: ErrorSpan },

    #[error("{}", .span.format_error(&format!("Invalid annotation: {} = {}: {}", .key, .value, .reason)))]
    InvalidAnnotation {
        key: Box<str>,
        value: Box<str>,
        reason: Box<str>,
        span: ErrorSpan,
    },

    #[error("{}", .span.format_error(&format!("Dynamic role error: {}", .message)))]
    DynamicRoleError { message: String, span: ErrorSpan },

    #[error("{}", .span.format_error(&format!("Namespace conflict: namespace '{}' already used in protocol '{}'", .namespace, .protocol)))]
    NamespaceConflict {
        namespace: String,
        protocol: String,
        span: ErrorSpan,
    },

    #[error("{}", .span.format_error(&format!("Role validation error: {}", .message)))]
    RoleValidationError { message: String, span: ErrorSpan },

    #[error("{}", .span.format_error(&format!("Annotation syntax error: {}", .message)))]
    AnnotationSyntaxError { message: String, span: ErrorSpan },

    #[error("{}", .span.format_error(&format!("Role overflow: {}", .message)))]
    RoleOverflowError { message: String, span: ErrorSpan },

    #[error("Grammar composition failed: {0}")]
    GrammarComposition(#[from] crate::compiler::grammar::GrammarCompositionError),
}

/// Format Pest errors nicely
fn format_pest_error(err: &pest::error::Error<Rule>) -> String {
    format!("\nParse error:\n{err}")
}

impl ParseError {
    /// Create an enhanced error with detailed context
    pub fn with_detailed_context(self, context: &str) -> Self {
        match self {
            ParseError::DynamicRoleError { message, span } => ParseError::DynamicRoleError {
                message: format!("{message} (in context: {context})"),
                span,
            },
            ParseError::InvalidAnnotation {
                key,
                value,
                reason,
                span,
            } => ParseError::InvalidAnnotation {
                key,
                value,
                reason: format!("{reason} (in context: {context})").into(),
                span,
            },
            ParseError::RoleValidationError { message, span } => ParseError::RoleValidationError {
                message: format!("{message} (in context: {context})"),
                span,
            },
            // For other errors, return as-is
            other => other,
        }
    }

    /// Create a dynamic role error with span
    pub fn dynamic_role_error(message: String, pair: &pest::iterators::Pair<Rule>) -> Self {
        let span = ErrorSpan::from_pest_span(pair.as_span(), pair.as_str());
        ParseError::DynamicRoleError { message, span }
    }

    /// Create an annotation error with span
    pub fn annotation_error(
        key: String,
        value: String,
        reason: String,
        pair: &pest::iterators::Pair<Rule>,
    ) -> Self {
        let span = ErrorSpan::from_pest_span(pair.as_span(), pair.as_str());
        ParseError::InvalidAnnotation {
            key: key.into(),
            value: value.into(),
            reason: reason.into(),
            span,
        }
    }

    /// Create a role validation error with span
    pub fn role_validation_error(message: String, pair: &pest::iterators::Pair<Rule>) -> Self {
        let span = ErrorSpan::from_pest_span(pair.as_span(), pair.as_str());
        ParseError::RoleValidationError { message, span }
    }

    /// Create a role overflow error with span
    pub fn role_overflow_error(message: String, pair: &pest::iterators::Pair<Rule>) -> Self {
        let span = ErrorSpan::from_pest_span(pair.as_span(), pair.as_str());
        ParseError::RoleOverflowError { message, span }
    }

    /// Check if this error is recoverable (allowing parsing to continue)
    pub fn is_recoverable(&self) -> bool {
        matches!(
            self,
            ParseError::InvalidAnnotation { .. } | ParseError::AnnotationSyntaxError { .. }
        )
    }

    /// Get error severity level
    pub fn severity(&self) -> ErrorSeverity {
        match self {
            ParseError::UndefinedRole { .. }
            | ParseError::DuplicateRole { .. }
            | ParseError::Syntax { .. } => ErrorSeverity::Error,

            ParseError::RoleOverflowError { .. } | ParseError::DynamicRoleError { .. } => {
                ErrorSeverity::Error
            }

            ParseError::InvalidAnnotation { .. } | ParseError::AnnotationSyntaxError { .. } => {
                ErrorSeverity::Warning
            }

            ParseError::NamespaceConflict { .. } => ErrorSeverity::Error,

            _ => ErrorSeverity::Error,
        }
    }

    /// Get suggested fixes for common errors
    pub fn get_suggestion(&self) -> Option<String> {
        match self {
            ParseError::UndefinedRole { role, .. } => {
                Some(format!("Add '{role}' to the roles declaration, or check for typos"))
            }
            ParseError::DuplicateRole { role, .. } => {
                Some(format!("Remove duplicate declaration of role '{role}'"))
            }
            ParseError::InvalidNamespace { namespace, .. } => {
                Some(format!("Use a valid namespace identifier (alphanumeric + underscore): '{namespace}' contains invalid characters"))
            }
            ParseError::DynamicRoleError { .. } => {
                Some("Check dynamic role syntax: Worker[*], Worker[N], or Worker[0..3]".to_string())
            }
            ParseError::RoleOverflowError { .. } => {
                Some(format!("Reduce role count to stay within the maximum limit of {}", crate::ast::role::MAX_ROLE_COUNT))
            }
            ParseError::InvalidAnnotation { key, .. } => {
                Some(format!("Check annotation syntax: [@{key} = \"value\"] or use supported annotation keys"))
            }
            _ => None,
        }
    }
}

/// Error severity levels
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ErrorSeverity {
    Warning,
    Error,
}

/// Parse a single annotation item (@key = value)
fn parse_annotation_item(
    pair: pest::iterators::Pair<Rule>,
) -> std::result::Result<(String, String), ParseError> {
    let mut key = String::new();
    let mut value = String::new();

    for inner in pair.into_inner() {
        match inner.as_rule() {
            Rule::ident => {
                if key.is_empty() {
                    key = inner.as_str().to_string();
                }
            }
            Rule::annotation_value => {
                value = inner.as_str().trim_matches('"').to_string();
            }
            _ => {}
        }
    }

    if key.is_empty() {
        key = "unknown".to_string();
    }
    if value.is_empty() {
        value = "true".to_string();
    }

    Ok((key, value))
}

/// Parse annotations into a HashMap (supporting multiple annotations)
fn parse_annotations(
    pair: pest::iterators::Pair<Rule>,
) -> std::result::Result<HashMap<String, String>, ParseError> {
    let mut annotations = HashMap::new();
    let mut current_key = String::new();

    for inner in pair.into_inner() {
        match inner.as_rule() {
            Rule::annotation_list => {
                // Handle [@item1 = value1, @item2 = value2] format
                for item in inner.into_inner() {
                    let (key, value) = parse_annotation_item(item)?;
                    annotations.insert(key, value);
                }
            }
            Rule::ident => {
                // This is the annotation key (like "optimize" in @optimize)
                current_key = inner.as_str().to_string();
            }
            Rule::annotation_args => {
                // Handle @key(arg1=val1, arg2=val2) format - convert to flat annotations
                for arg in inner.into_inner() {
                    if let Rule::annotation_arg_list = arg.as_rule() {
                        let mut values = Vec::new();
                        for arg_item in arg.into_inner() {
                            if let Rule::annotation_arg = arg_item.as_rule() {
                                let mut arg_key = String::new();
                                let mut arg_val = "true".to_string();

                                for part in arg_item.into_inner() {
                                    match part.as_rule() {
                                        Rule::ident => {
                                            if arg_key.is_empty() {
                                                arg_key = part.as_str().to_string();
                                            }
                                        }
                                        Rule::annotation_value => {
                                            arg_val = part.as_str().trim_matches('"').to_string();
                                        }
                                        _ => {}
                                    }
                                }

                                if !arg_key.is_empty() {
                                    if arg_val == "true" {
                                        values.push(arg_key);
                                    } else {
                                        values.push(format!("{}={}", arg_key, arg_val));
                                    }
                                }
                            }
                        }
                        // Create a single annotation with comma-separated values
                        let combined_value = values.join(",");
                        let key = if current_key.is_empty() {
                            "unknown".to_string()
                        } else {
                            current_key.clone()
                        };
                        annotations.insert(key, combined_value);
                    }
                }
            }
            _ => {}
        }
    }

    // If we only found a key but no args, set it to true
    if !current_key.is_empty() && !annotations.contains_key(&current_key) {
        annotations.insert(current_key, "true".to_string());
    }

    Ok(annotations)
}

/// Parse a role parameter using enhanced syntax
fn parse_role_param(
    pair: pest::iterators::Pair<Rule>,
    _role_name: &str,
    input: &str,
) -> std::result::Result<RoleParam, ParseError> {
    let mut inner = pair.into_inner();
    let param_expr = inner.next().unwrap();

    match param_expr.as_rule() {
        Rule::role_param_expr => {
            // Check the content of the param_expr directly
            let param_content_str = param_expr.as_str().trim();

            if param_content_str == "*" {
                // Runtime parameter
                Ok(RoleParam::Runtime)
            } else if let Ok(count) = param_content_str.parse::<u32>() {
                // Static count parameter
                RoleParam::safe_static(count).map_err(|e| ParseError::Syntax {
                    span: ErrorSpan::from_pest_span(param_expr.as_span(), input),
                    message: format!("Role parameter validation failed: {}", e),
                })
            } else {
                // Symbolic parameter (identifier)
                Ok(RoleParam::Symbolic(param_content_str.to_string()))
            }
        }
        _ => Err(ParseError::Syntax {
            span: ErrorSpan::from_pest_span(param_expr.as_span(), input),
            message: "Invalid role parameter expression".to_string(),
        }),
    }
}

/// Parse a role index using enhanced syntax
fn parse_role_index(
    pair: pest::iterators::Pair<Rule>,
    _role_name: &str,
    input: &str,
) -> std::result::Result<RoleIndex, ParseError> {
    let mut inner = pair.into_inner();
    let index_expr = inner.next().unwrap();

    match index_expr.as_rule() {
        Rule::role_index_expr => {
            let index_content_str = index_expr.as_str().trim();
            let index_span = index_expr.as_span();
            if let Some(index_content) = index_expr.into_inner().next() {
                match index_content.as_rule() {
                    Rule::integer => {
                        let index = index_content.as_str().parse::<u32>().map_err(|_| {
                            ParseError::Syntax {
                                span: ErrorSpan::from_pest_span(index_content.as_span(), input),
                                message: "Invalid integer in role index".to_string(),
                            }
                        })?;

                        // Use safe constructor with overflow checking
                        RoleIndex::safe_concrete(index).map_err(|e| ParseError::Syntax {
                            span: ErrorSpan::from_pest_span(index_content.as_span(), input),
                            message: format!("Role index validation failed: {}", e),
                        })
                    }
                    Rule::ident => {
                        // Symbolic index like Worker[i]
                        let symbolic_name = index_content.as_str().to_string();
                        Ok(RoleIndex::Symbolic(symbolic_name))
                    }
                    Rule::range_expr => parse_range_expr(index_content, input),
                    _ => {
                        // Check for "*" wildcard
                        let content_str = index_content.as_str();
                        if content_str == "*" {
                            Ok(RoleIndex::Wildcard)
                        } else {
                            Err(ParseError::Syntax {
                                span: ErrorSpan::from_pest_span(index_content.as_span(), input),
                                message: format!("Invalid role index: {}", content_str),
                            })
                        }
                    }
                }
            } else {
                // Handle terminal rules like "*" by checking the content directly
                if index_content_str == "*" {
                    Ok(RoleIndex::Wildcard)
                } else {
                    Err(ParseError::Syntax {
                        span: ErrorSpan::from_pest_span(index_span, input),
                        message: format!("Invalid role index: {}", index_content_str),
                    })
                }
            }
        }
        _ => Err(ParseError::Syntax {
            span: ErrorSpan::from_pest_span(index_expr.as_span(), input),
            message: "Invalid role index expression".to_string(),
        }),
    }
}

/// Parse a range expression (e.g., 0..3, i..N)
fn parse_range_expr(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<RoleIndex, ParseError> {
    let pair_span = pair.as_span();
    let mut inner = pair.into_inner();
    let start_expr = inner.next().unwrap();
    let end_expr = inner.next().unwrap();

    let start = match start_expr.as_rule() {
        Rule::integer => {
            let value = start_expr
                .as_str()
                .parse::<u32>()
                .map_err(|_| ParseError::Syntax {
                    span: ErrorSpan::from_pest_span(start_expr.as_span(), input),
                    message: "Invalid integer in range start".to_string(),
                })?;
            RangeExpr::Concrete(value)
        }
        Rule::ident => RangeExpr::Symbolic(start_expr.as_str().to_string()),
        _ => {
            return Err(ParseError::Syntax {
                span: ErrorSpan::from_pest_span(start_expr.as_span(), input),
                message: "Invalid range start expression".to_string(),
            })
        }
    };

    let end = match end_expr.as_rule() {
        Rule::integer => {
            let value = end_expr
                .as_str()
                .parse::<u32>()
                .map_err(|_| ParseError::Syntax {
                    span: ErrorSpan::from_pest_span(end_expr.as_span(), input),
                    message: "Invalid integer in range end".to_string(),
                })?;
            RangeExpr::Concrete(value)
        }
        Rule::ident => RangeExpr::Symbolic(end_expr.as_str().to_string()),
        _ => {
            return Err(ParseError::Syntax {
                span: ErrorSpan::from_pest_span(end_expr.as_span(), input),
                message: "Invalid range end expression".to_string(),
            })
        }
    };

    let range = RoleRange { start, end };

    // Validate the range
    range.validate().map_err(|e| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(pair_span, input),
        message: format!("Range validation failed: {}", e),
    })?;

    Ok(RoleIndex::Range(range))
}

/// Parse a namespace declaration from the AST
fn parse_namespace_decl(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<String, ParseError> {
    let span = pair.as_span();

    for inner in pair.into_inner() {
        if inner.as_rule() == Rule::string {
            let namespace_str = inner.as_str().trim_matches('"');

            // Validate namespace format (alphanumeric + underscore)
            if namespace_str
                .chars()
                .all(|c| c.is_alphanumeric() || c == '_')
                && !namespace_str.is_empty()
            {
                return Ok(namespace_str.to_string());
            } else {
                let inner_span = inner.as_span();
                return Err(ParseError::InvalidNamespace {
                    namespace: namespace_str.to_string(),
                    span: ErrorSpan::from_pest_span(inner_span, input),
                });
            }
        }
    }

    Err(ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "Missing namespace string in declaration".to_string(),
    })
}

/// Parse context for extension parsing
#[derive(Debug, Clone)]
pub struct ParseContext {
    pub declared_roles: Vec<Role>,
    pub current_namespace: Option<String>,
    pub statement_location: (usize, usize), // line, column
    pub surrounding_context: String,
}

impl ParseContext {
    pub fn new(declared_roles: Vec<Role>, namespace: Option<String>) -> Self {
        Self {
            declared_roles,
            current_namespace: namespace,
            statement_location: (1, 1),
            surrounding_context: String::new(),
        }
    }

    pub fn from_pair(
        pair: &pest::iterators::Pair<Rule>,
        declared_roles: &[Role],
        namespace: &Option<String>,
    ) -> Self {
        let (line, column) = pair.as_span().start_pos().line_col();
        Self {
            declared_roles: declared_roles.to_vec(),
            current_namespace: namespace.clone(),
            statement_location: (line, column),
            surrounding_context: pair.as_str().to_string(),
        }
    }
}

/// Parse a choreographic protocol from a string
pub fn parse_choreography_str(input: &str) -> std::result::Result<Choreography, ParseError> {
    parse_choreography_str_with_extensions(input, &ExtensionRegistry::new())
        .map(|(choreo, _)| choreo)
}

/// Parse a choreographic protocol from a string with extension support
pub fn parse_choreography_str_with_extensions(
    input: &str,
    registry: &ExtensionRegistry,
) -> std::result::Result<(Choreography, Vec<Box<dyn ProtocolExtension>>), ParseError> {
    // Generate composed grammar if extensions are registered
    let (preprocessed_input, pairs) = if registry.has_extensions() {
        // Use dynamic grammar composition
        let (preprocessed, pairs) = parse_with_dynamic_grammar(input, registry)?;
        (Some(preprocessed), pairs)
    } else {
        (
            None,
            ChoreographyParser::parse(Rule::choreography, input).map_err(Box::new)?,
        )
    };

    let mut name = format_ident!("Unnamed");
    let mut namespace: Option<String> = None;
    let mut roles = Vec::new();
    let mut declared_roles = HashSet::new();
    let mut protocol_defs: HashMap<String, Vec<Statement>> = HashMap::new();
    let mut statements = Vec::new();
    let mut attrs: HashMap<String, String> = HashMap::new();

    for pair in pairs {
        if pair.as_rule() == Rule::choreography {
            for inner in pair.into_inner() {
                match inner.as_rule() {
                    Rule::namespace_decl => {
                        namespace = Some(parse_namespace_decl(inner, input)?);
                    }
                    Rule::annotation => {
                        // Parse annotation and add to attrs
                        let annotation_map = parse_annotations(inner)?;
                        attrs.extend(annotation_map);
                    }
                    Rule::ident => {
                        name = format_ident!("{}", inner.as_str());
                    }
                    Rule::roles_decl => {
                        for role_pair in inner.into_inner() {
                            if let Rule::role_list = role_pair.as_rule() {
                                for role_decl in role_pair.into_inner() {
                                    if let Rule::role_decl = role_decl.as_rule() {
                                        let mut inner_role = role_decl.into_inner();
                                        let role_ident = inner_role.next().unwrap();
                                        let role_name = role_ident.as_str().trim();
                                        let span = role_ident.as_span();

                                        // Check for role parameter
                                        let role = if let Some(param_pair) = inner_role.next() {
                                            if param_pair.as_rule() == Rule::role_param {
                                                // Parse the enhanced parameter syntax
                                                match parse_role_param(param_pair, role_name, input)
                                                {
                                                    Ok(param) => Role::with_param(
                                                        format_ident!("{}", role_name),
                                                        param,
                                                    ),
                                                    Err(e) => return Err(e),
                                                }
                                            } else {
                                                Role::new(format_ident!("{}", role_name))
                                            }
                                        } else {
                                            Role::new(format_ident!("{}", role_name))
                                        };

                                        if !declared_roles.insert(role_name.to_string()) {
                                            return Err(ParseError::DuplicateRole {
                                                role: role_name.to_string(),
                                                span: ErrorSpan::from_pest_span(span, input),
                                            });
                                        }
                                        roles.push(role);
                                    }
                                }
                            }
                        }
                    }
                    Rule::protocol_defs => {
                        for protocol_def in inner.into_inner() {
                            if let Rule::protocol_def = protocol_def.as_rule() {
                                let mut def_inner = protocol_def.into_inner();
                                let proto_name_pair = def_inner.next().unwrap();
                                let proto_name = proto_name_pair.as_str();
                                let proto_span = proto_name_pair.as_span();

                                if protocol_defs.contains_key(proto_name) {
                                    return Err(ParseError::DuplicateProtocol {
                                        protocol: proto_name.to_string(),
                                        span: ErrorSpan::from_pest_span(proto_span, input),
                                    });
                                }

                                let body_pair = def_inner.next().unwrap();
                                let body = parse_protocol_body(
                                    body_pair,
                                    &declared_roles,
                                    input,
                                    &protocol_defs,
                                )?;
                                protocol_defs.insert(proto_name.to_string(), body);
                            }
                        }
                    }
                    Rule::protocol_body => {
                        statements =
                            parse_protocol_body(inner, &declared_roles, input, &protocol_defs)?;
                    }
                    Rule::EOI => {}
                    _ => {}
                }
            }
        }
    }

    if roles.is_empty() {
        return Err(ParseError::EmptyChoreography);
    }

    let protocol = convert_statements_to_protocol(&statements, &roles);

    // Parse extension statements from the AST
    let extensions = if registry.has_extensions() {
        let default_input = input.to_string();
        let extension_input = preprocessed_input.as_ref().unwrap_or(&default_input);
        parse_extension_statements(extension_input, &roles, &namespace, registry)?
    } else {
        Vec::new()
    };

    Ok((
        Choreography {
            name,
            namespace,
            roles,
            protocol,
            attrs,
        },
        extensions,
    ))
}

/// Parse protocol body into statements
fn parse_protocol_body(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Vec<Statement>, ParseError> {
    let mut statements = Vec::new();

    for statement_pair in pair.into_inner() {
        let statement = parse_statement(statement_pair, declared_roles, input, protocol_defs)?;
        statements.push(statement);
    }

    Ok(statements)
}

/// Parse a single statement
fn parse_statement(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    // Handle annotated statements
    if let Rule::annotated_stmt = pair.as_rule() {
        let mut inner = pair.into_inner();
        let mut annotations = HashMap::new();

        // Parse all annotations
        let mut stmt_pair = inner.next().unwrap();
        while stmt_pair.as_rule() == Rule::annotation {
            let annotation_map = parse_annotations(stmt_pair)?;
            annotations.extend(annotation_map);
            stmt_pair = inner.next().unwrap();
        }

        // Parse the statement and add annotations
        let mut statement = parse_statement_inner(stmt_pair, declared_roles, input, protocol_defs)?;
        add_annotations_to_statement(&mut statement, annotations);
        return Ok(statement);
    }

    parse_statement_inner(pair, declared_roles, input, protocol_defs)
}

/// Add statement-level annotations to a parsed statement
fn add_annotations_to_statement(statement: &mut Statement, annotations: HashMap<String, String>) {
    match statement {
        Statement::Send {
            annotations: stmt_annotations,
            ..
        } => {
            *stmt_annotations = annotations;
        }
        Statement::Broadcast {
            annotations: stmt_annotations,
            ..
        } => {
            *stmt_annotations = annotations;
        }
        Statement::Choice {
            annotations: stmt_annotations,
            ..
        } => {
            *stmt_annotations = annotations;
        }
        _ => {
            // Other statement types don't support annotations yet
        }
    }
}

/// Parse the actual statement (without annotations)
fn parse_statement_inner(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    match pair.as_rule() {
        Rule::send_stmt => parse_send_stmt(pair, declared_roles, input),
        Rule::broadcast_stmt => parse_broadcast_stmt(pair, declared_roles, input),
        Rule::choice_stmt => parse_choice_stmt(pair, declared_roles, input, protocol_defs),
        Rule::loop_stmt => parse_loop_stmt(pair, declared_roles, input, protocol_defs),
        Rule::parallel_stmt => parse_parallel_stmt(pair, declared_roles, input, protocol_defs),
        Rule::rec_stmt => parse_rec_stmt(pair, declared_roles, input, protocol_defs),
        Rule::call_stmt => parse_call_stmt(pair, declared_roles, input, protocol_defs),
        _ => {
            let span = pair.as_span();
            Err(ParseError::Syntax {
                span: ErrorSpan::from_pest_span(span, input),
                message: format!("Unexpected statement type: {:?}", pair.as_rule()),
            })
        }
    }
}

/// Parse a role reference (e.g., A, Worker[0], Worker[i])
fn parse_role_ref(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
) -> std::result::Result<Role, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();

    let role_ident = inner.next().unwrap();
    let role_name = role_ident.as_str().trim();

    // Check if the base role name is declared
    if !declared_roles.contains(role_name) {
        return Err(ParseError::UndefinedRole {
            role: role_name.to_string(),
            span: ErrorSpan::from_pest_span(span, input),
        });
    }

    // Check if there's an index
    if let Some(index_pair) = inner.next() {
        if index_pair.as_rule() == Rule::role_index {
            // Parse the enhanced index syntax
            match parse_role_index(index_pair, role_name, input) {
                Ok(index) => {
                    return Ok(Role::with_index(format_ident!("{}", role_name), index));
                }
                Err(e) => return Err(e),
            }
        }
    }

    // Simple role without index
    Ok(Role::new(format_ident!("{}", role_name)))
}

/// Parse an annotated role (role_ref with optional role_annotations)
fn parse_annotated_role(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
) -> std::result::Result<Role, ParseError> {
    let mut inner = pair.into_inner();

    // First part should be role_ref
    let role_ref_pair = inner.next().unwrap();
    let role = parse_role_ref(role_ref_pair, declared_roles, input)?;

    // Check for optional role_annotations
    if let Some(annotations_pair) = inner.next() {
        if annotations_pair.as_rule() == Rule::role_annotations {
            // Parse role-level annotations and add them to the role
            // For now, we'll store them in the role's metadata (if the Role type supports it)
            // Otherwise, we'll just ignore them for now and focus on getting the parsing to work
        }
    }

    Ok(role)
}

/// Parse send statement: A -> B: Message(payload)
fn parse_send_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
) -> std::result::Result<Statement, ParseError> {
    let mut inner = pair.into_inner();

    let from_pair = inner.next().unwrap();
    let from = parse_annotated_role(from_pair, declared_roles, input)?;

    let to_pair = inner.next().unwrap();
    let to = parse_annotated_role(to_pair, declared_roles, input)?;

    let message = parse_message(inner.next().unwrap(), input)?;

    Ok(Statement::Send {
        from,
        to,
        message,
        annotations: HashMap::new(),
        from_annotations: HashMap::new(),
        to_annotations: HashMap::new(),
    })
}

/// Parse broadcast statement: A ->* : Message(payload)
fn parse_broadcast_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
) -> std::result::Result<Statement, ParseError> {
    let mut inner = pair.into_inner();

    let from_pair = inner.next().unwrap();
    let from = parse_annotated_role(from_pair, declared_roles, input)?;

    let message = parse_message(inner.next().unwrap(), input)?;

    Ok(Statement::Broadcast {
        from,
        message,
        annotations: HashMap::new(),
        from_annotations: HashMap::new(),
    })
}

/// Parse choice statement
fn parse_choice_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    let mut inner = pair.into_inner();

    let role_pair = inner.next().unwrap();
    let role = if role_pair.as_rule() == Rule::ident {
        // Simple identifier without indexing
        let role_name = role_pair.as_str().trim();
        let role_span = role_pair.as_span();
        if !declared_roles.contains(role_name) {
            return Err(ParseError::UndefinedRole {
                role: role_name.to_string(),
                span: ErrorSpan::from_pest_span(role_span, input),
            });
        }
        Role::new(format_ident!("{}", role_name))
    } else {
        // Role reference (potentially with indexing)
        parse_role_ref(role_pair, declared_roles, input)?
    };

    let mut branches = Vec::new();
    for branch_pair in inner {
        if let Rule::choice_branch = branch_pair.as_rule() {
            let mut branch_inner = branch_pair.into_inner();
            let label = format_ident!("{}", branch_inner.next().unwrap().as_str());

            // Check for optional guard
            let mut guard = None;
            let next_item = branch_inner.next().unwrap();
            let body = if let Rule::guard = next_item.as_rule() {
                // Parse guard expression
                let guard_span = next_item.as_span();
                let mut guard_inner = next_item.into_inner();
                let guard_expr = guard_inner.next().unwrap().as_str();
                guard = Some(syn::parse_str::<TokenStream>(guard_expr).map_err(|e| {
                    ParseError::Syntax {
                        span: ErrorSpan::from_pest_span(guard_span, input),
                        message: format!("Invalid guard expression: {e}"),
                    }
                })?);
                // Body comes after guard
                parse_protocol_body(
                    branch_inner.next().unwrap(),
                    declared_roles,
                    input,
                    protocol_defs,
                )?
            } else {
                // No guard, next_item is the body
                parse_protocol_body(next_item, declared_roles, input, protocol_defs)?
            };

            branches.push(ChoiceBranch {
                label,
                guard,
                statements: body,
            });
        }
    }

    Ok(Statement::Choice {
        role,
        branches,
        annotations: HashMap::new(),
    })
}

/// Parse loop statement
fn parse_loop_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    let inner = pair.into_inner();

    let mut condition = None;
    let mut body = Vec::new();

    for item in inner {
        match item.as_rule() {
            Rule::count_condition => {
                let span = item.as_span();
                let mut cond_inner = item.into_inner();
                let count_pair = cond_inner.next().unwrap();
                let count_str = count_pair.as_str();

                // Try to parse as integer, otherwise treat as variable
                if let Ok(count) = count_str.parse::<usize>() {
                    condition = Some(Condition::Count(count));
                } else {
                    // Parse as TokenStream for symbolic count
                    let token_stream = syn::parse_str::<TokenStream>(count_str).map_err(|e| {
                        ParseError::InvalidCondition {
                            message: format!("Invalid count: {e}"),
                            span: ErrorSpan::from_pest_span(span, input),
                        }
                    })?;
                    condition = Some(Condition::Custom(token_stream));
                }
            }
            Rule::role_decides_condition => {
                let mut cond_inner = item.into_inner();
                let role_pair = cond_inner.next().unwrap();
                let role_str = role_pair.as_str().trim();
                let role_span = role_pair.as_span();
                if !declared_roles.contains(role_str) {
                    return Err(ParseError::UndefinedRole {
                        role: role_str.to_string(),
                        span: ErrorSpan::from_pest_span(role_span, input),
                    });
                }
                condition = Some(Condition::RoleDecides(Role::new(format_ident!(
                    "{}", role_str
                ))));
            }
            Rule::custom_condition => {
                let span = item.as_span();
                let mut cond_inner = item.into_inner();
                let custom_str = cond_inner.next().unwrap().as_str();
                // Remove quotes from string
                let custom_str = custom_str.trim_matches('"');
                // Parse as TokenStream for Custom condition
                let token_stream = syn::parse_str::<TokenStream>(custom_str).map_err(|e| {
                    ParseError::InvalidCondition {
                        message: format!("Invalid custom condition: {e}"),
                        span: ErrorSpan::from_pest_span(span, input),
                    }
                })?;
                condition = Some(Condition::Custom(token_stream));
            }
            Rule::protocol_body => {
                body = parse_protocol_body(item, declared_roles, input, protocol_defs)?;
            }
            _ => {}
        }
    }

    Ok(Statement::Loop { condition, body })
}

/// Parse parallel statement
fn parse_parallel_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    let mut branches = Vec::new();

    for branch_pair in pair.into_inner() {
        if let Rule::parallel_branch = branch_pair.as_rule() {
            for body_pair in branch_pair.into_inner() {
                if let Rule::protocol_body = body_pair.as_rule() {
                    let body =
                        parse_protocol_body(body_pair, declared_roles, input, protocol_defs)?;
                    branches.push(body);
                }
            }
        }
    }

    Ok(Statement::Parallel { branches })
}

/// Parse recursive statement
fn parse_rec_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    let mut inner = pair.into_inner();

    let label = format_ident!("{}", inner.next().unwrap().as_str());
    let body = parse_protocol_body(inner.next().unwrap(), declared_roles, input, protocol_defs)?;

    Ok(Statement::Rec { label, body })
}

/// Parse protocol call statement
fn parse_call_stmt(
    pair: pest::iterators::Pair<Rule>,
    _declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    let mut inner = pair.into_inner();
    let proto_name_pair = inner.next().unwrap();
    let proto_name = proto_name_pair.as_str();
    let span = proto_name_pair.as_span();

    // Look up the protocol definition
    let proto_statements =
        protocol_defs
            .get(proto_name)
            .ok_or_else(|| ParseError::UndefinedProtocol {
                protocol: proto_name.to_string(),
                span: ErrorSpan::from_pest_span(span, input),
            })?;

    // Return a Call statement that will be inlined later
    Ok(Statement::Call {
        name: format_ident!("{}", proto_name),
        statements: proto_statements.clone(),
    })
}

/// Parse message specification
fn parse_message(
    pair: pest::iterators::Pair<Rule>,
    _input: &str,
) -> std::result::Result<MessageSpec, ParseError> {
    let _span = pair.as_span();
    let mut inner = pair.into_inner();

    let name = format_ident!("{}", inner.next().unwrap().as_str());

    let mut type_annotation = None;
    let mut payload = None;

    for part in inner {
        match part.as_rule() {
            Rule::message_type => {
                // Parse the type annotation
                let type_str = part.as_str();
                // Remove angle brackets
                let type_str = type_str.trim_start_matches('<').trim_end_matches('>');
                type_annotation = syn::parse_str::<TokenStream>(type_str).ok();
            }
            Rule::payload => {
                // Parse the payload
                let payload_str = part.as_str();
                let payload_str = payload_str.trim_matches('(').trim_matches(')');
                payload = syn::parse_str::<TokenStream>(payload_str).ok();
            }
            _ => {}
        }
    }

    Ok(MessageSpec {
        name,
        type_annotation,
        payload,
    })
}

/// Choreography statement types
#[derive(Debug, Clone)]
#[allow(clippy::large_enum_variant)] // Statement enum is internal to parser; performance impact is minimal
enum Statement {
    Send {
        from: Role,
        to: Role,
        message: MessageSpec,
        annotations: HashMap<String, String>,
        from_annotations: HashMap<String, String>,
        to_annotations: HashMap<String, String>,
    },
    Broadcast {
        from: Role,
        message: MessageSpec,
        annotations: HashMap<String, String>,
        from_annotations: HashMap<String, String>,
    },
    Choice {
        role: Role,
        branches: Vec<ChoiceBranch>,
        annotations: HashMap<String, String>,
    },
    Loop {
        condition: Option<Condition>,
        body: Vec<Statement>,
    },
    Parallel {
        branches: Vec<Vec<Statement>>,
    },
    Rec {
        label: Ident,
        body: Vec<Statement>,
    },
    Call {
        #[allow(dead_code)]
        name: Ident,
        statements: Vec<Statement>,
    },
}

/// Choice branch in choreography
#[derive(Debug, Clone)]
struct ChoiceBranch {
    label: Ident,
    guard: Option<TokenStream>,
    statements: Vec<Statement>,
}

/// Message specification with optional payload
#[derive(Debug, Clone)]
struct MessageSpec {
    name: Ident,
    type_annotation: Option<TokenStream>,
    payload: Option<TokenStream>,
}

/// Convert statements to protocol AST
fn convert_statements_to_protocol(statements: &[Statement], roles: &[Role]) -> Protocol {
    if statements.is_empty() {
        return Protocol::End;
    }

    // First, inline all Call statements
    let inlined = inline_calls(statements);

    let mut current = Protocol::End;

    // Build protocol from back to front
    for statement in inlined.iter().rev() {
        current = match statement {
            Statement::Send {
                from,
                to,
                message,
                annotations,
                from_annotations,
                to_annotations,
            } => Protocol::Send {
                from: from.clone(),
                to: to.clone(),
                message: MessageType {
                    name: message.name.clone(),
                    type_annotation: message.type_annotation.clone(),
                    payload: message.payload.clone(),
                },
                continuation: Box::new(current),
                annotations: annotations.clone(),
                from_annotations: from_annotations.clone(),
                to_annotations: to_annotations.clone(),
            },
            Statement::Broadcast {
                from,
                message,
                annotations,
                from_annotations,
            } => {
                // Resolve to all roles except the sender
                let to_all = roles
                    .iter()
                    .filter(|r| r.name != from.name)
                    .cloned()
                    .collect();

                Protocol::Broadcast {
                    from: from.clone(),
                    to_all,
                    message: MessageType {
                        name: message.name.clone(),
                        type_annotation: message.type_annotation.clone(),
                        payload: message.payload.clone(),
                    },
                    continuation: Box::new(current),
                    annotations: annotations.clone(),
                    from_annotations: from_annotations.clone(),
                }
            }
            Statement::Choice {
                role,
                branches,
                annotations,
            } => Protocol::Choice {
                role: role.clone(),
                branches: branches
                    .iter()
                    .map(|b| Branch {
                        label: b.label.clone(),
                        guard: b.guard.clone(),
                        protocol: convert_statements_to_protocol(&b.statements, roles),
                    })
                    .collect(),
                annotations: annotations.clone(),
            },
            Statement::Loop { condition, body } => Protocol::Loop {
                condition: condition.clone(),
                body: Box::new(convert_statements_to_protocol(body, roles)),
            },
            Statement::Parallel { branches } => Protocol::Parallel {
                protocols: branches
                    .iter()
                    .map(|b| convert_statements_to_protocol(b, roles))
                    .collect(),
            },
            Statement::Rec { label, body } => Protocol::Rec {
                label: label.clone(),
                body: Box::new(convert_statements_to_protocol(body, roles)),
            },
            Statement::Call { .. } => {
                // This should not happen after inlining
                current
            }
        };
    }

    current
}

/// Inline all Call statements by replacing them with their definitions
fn inline_calls(statements: &[Statement]) -> Vec<Statement> {
    let mut result = Vec::new();

    for statement in statements {
        match statement {
            Statement::Call { statements, .. } => {
                // Recursively inline the called protocol's statements
                result.extend(inline_calls(statements));
            }
            Statement::Choice { role, branches, .. } => {
                // Inline calls within choice branches
                let new_branches = branches
                    .iter()
                    .map(|b| ChoiceBranch {
                        label: b.label.clone(),
                        guard: b.guard.clone(),
                        statements: inline_calls(&b.statements),
                    })
                    .collect();
                result.push(Statement::Choice {
                    role: role.clone(),
                    branches: new_branches,
                    annotations: HashMap::new(),
                });
            }
            Statement::Loop { condition, body } => {
                // Inline calls within loop body
                result.push(Statement::Loop {
                    condition: condition.clone(),
                    body: inline_calls(body),
                });
            }
            Statement::Parallel { branches } => {
                // Inline calls within parallel branches
                let new_branches = branches.iter().map(|b| inline_calls(b)).collect();
                result.push(Statement::Parallel {
                    branches: new_branches,
                });
            }
            Statement::Rec { label, body } => {
                // Inline calls within recursive body
                result.push(Statement::Rec {
                    label: label.clone(),
                    body: inline_calls(body),
                });
            }
            _ => {
                // Other statements remain unchanged
                result.push(statement.clone());
            }
        }
    }

    result
}

/// Parse with dynamic grammar composition for extensions
fn parse_with_dynamic_grammar<'a>(
    input: &'a str,
    registry: &ExtensionRegistry,
) -> std::result::Result<(String, pest::iterators::Pairs<'a, Rule>), ParseError> {
    // Clean and elegant approach: preprocess extension syntax then parse
    let preprocessed = preprocess_extension_syntax(input, registry)?;

    // Parse the original input for now, but return the preprocessed version
    // so the caller can handle extensions based on the preprocessing
    let pairs = ChoreographyParser::parse(Rule::choreography, input).map_err(Box::new)?;

    Ok((preprocessed, pairs))
}

/// Create a dynamic parser from composed grammar
#[allow(dead_code)]
fn create_dynamic_parser(_grammar: &str) -> std::result::Result<ChoreographyParser, ParseError> {
    // For now, return the static parser since Pest doesn't support
    // true dynamic grammar generation at runtime.
    // In a full implementation, this would use dynamic code generation
    // or a custom parser generator.
    Ok(ChoreographyParser {})
}

/// Preprocess extension syntax to transform it into standard rumpsteak syntax
/// This is the core of our elegant extension system - transform extension syntax
/// to standard syntax that the base parser can handle
fn preprocess_extension_syntax(
    input: &str,
    registry: &ExtensionRegistry,
) -> std::result::Result<String, ParseError> {
    let mut processed = input.to_string();

    // Process each type of extension syntax
    for extension in registry.grammar_extensions() {
        processed = preprocess_extension_rules(&processed, extension)?;
    }

    Ok(processed)
}

/// Transform extension-specific syntax patterns for a single extension
fn preprocess_extension_rules(
    input: &str,
    extension: &dyn crate::extensions::GrammarExtension,
) -> std::result::Result<String, ParseError> {
    let mut result = input.to_string();

    // Handle Aura-style annotations: Role[annotations] -> Role: Message
    // Transform to: Role -> Role: Message /* annotations */
    if extension.extension_id() == "aura_annotations" {
        result = transform_aura_annotations(&result)?;
    }

    Ok(result)
}

// Cache for compiled regex patterns (performance optimization)
lazy_static::lazy_static! {
    static ref AURA_ANNOTATION_REGEX: regex::Regex = regex::Regex::new(
        r"(\w+)\[([^\]]+)\]\s*->\s*(\w+):\s*(\w+);"
    ).expect("Failed to compile Aura annotation regex");

    /// Cache for preprocessed syntax transformations
    static ref PREPROCESSING_CACHE: Arc<RwLock<HashMap<u64, String>>> = Arc::new(RwLock::new(HashMap::new()));
}

/// Transform Aura annotation syntax to standard comments with caching
/// Alice[guard_capability="send", flow_cost=100] -> Bob: Message;
/// becomes:
/// Alice -> Bob: Message; // aura:guard_capability="send",flow_cost=100
fn transform_aura_annotations(input: &str) -> std::result::Result<String, ParseError> {
    // Create cache key
    let mut hasher = DefaultHasher::new();
    input.hash(&mut hasher);
    "aura_annotations".hash(&mut hasher);
    let cache_key = hasher.finish();

    // Check cache first
    if let Ok(cache) = PREPROCESSING_CACHE.read() {
        if let Some(cached) = cache.get(&cache_key) {
            return Ok(cached.clone());
        }
    }

    // Perform transformation
    let transformed = AURA_ANNOTATION_REGEX.replace_all(input, |caps: &regex::Captures| {
        let sender = &caps[1];
        let annotations = &caps[2];
        let receiver = &caps[3];
        let message = &caps[4];

        // Transform to standard syntax with comment
        format!(
            "{} -> {}: {}; // aura:{}",
            sender, receiver, message, annotations
        )
    });

    let result = transformed.to_string();

    // Cache the result
    if let Ok(mut cache) = PREPROCESSING_CACHE.write() {
        cache.insert(cache_key, result.clone());
    }

    Ok(result)
}

/// Parse extension statements from the parsed AST
fn parse_extension_statements(
    input: &str,
    roles: &[Role],
    namespace: &Option<String>,
    registry: &ExtensionRegistry,
) -> std::result::Result<Vec<Box<dyn ProtocolExtension>>, ParseError> {
    let mut extensions = Vec::new();

    // Create parse context
    let _context = ParseContext::new(roles.to_vec(), namespace.clone());

    // Parse Aura-style annotation comments if Aura extensions are registered
    if registry.has_extension("aura_annotations") {
        extensions.extend(parse_aura_annotation_comments(input)?);
    }

    // Keep existing timeout support for compatibility
    if registry.has_extension("timeout") {
        use crate::extensions::timeout::TimeoutProtocol;
        use std::time::Duration;

        let timeout_ext = TimeoutProtocol {
            duration: Duration::from_secs(30),
            role_names: roles.iter().map(|r| r.name.to_string()).collect(),
            body_repr: "default".to_string(),
        };

        extensions.push(Box::new(timeout_ext) as Box<dyn ProtocolExtension>);
    }

    Ok(extensions)
}

/// Parse Aura annotation comments from transformed input
/// Looks for: // aura:guard_capability="send",flow_cost=100
fn parse_aura_annotation_comments(
    input: &str,
) -> std::result::Result<Vec<Box<dyn crate::extensions::ProtocolExtension>>, ParseError> {
    use std::collections::HashMap;

    let mut extensions = Vec::new();

    for line in input.lines() {
        if let Some(comment_start) = line.find("// aura:") {
            let comment_content = &line[comment_start + 8..]; // Skip "// aura:"

            // Parse the comment content as key=value pairs
            let mut annotations = HashMap::new();
            for pair in comment_content.split(',') {
                if let Some(eq_pos) = pair.find('=') {
                    let key = pair[..eq_pos].trim();
                    let value = pair[eq_pos + 1..].trim().trim_matches('"');
                    annotations.insert(key.to_string(), value.to_string());
                }
            }

            if !annotations.is_empty() {
                // Extract sender and receiver from the line (before the comment)
                let statement_part = &line[..comment_start];
                if let Some((sender, receiver, message)) = parse_send_statement(statement_part) {
                    let aura_send =
                        create_aura_annotated_send(sender, receiver, message, annotations);
                    extensions
                        .push(Box::new(aura_send) as Box<dyn crate::extensions::ProtocolExtension>);
                }
            }
        }
    }

    Ok(extensions)
}

/// Parse a send statement to extract sender, receiver, and message
/// "Alice -> Bob: Message;" returns Some(("Alice", "Bob", "Message"))
fn parse_send_statement(statement: &str) -> Option<(String, String, String)> {
    let statement = statement.trim();

    // Find "->"
    let arrow_pos = statement.find("->")?;
    let sender = statement[..arrow_pos].trim().to_string();

    let after_arrow = &statement[arrow_pos + 2..];
    let colon_pos = after_arrow.find(':')?;
    let receiver = after_arrow[..colon_pos].trim().to_string();

    let after_colon = &after_arrow[colon_pos + 1..];
    let message = after_colon.trim().trim_end_matches(';').trim().to_string();

    Some((sender, receiver, message))
}

/// Simple Aura extension implementation for demonstration
#[derive(Debug, Clone)]
struct SimpleAuraExtension {
    sender: String,
    receiver: String,
    #[allow(dead_code)]
    message_type: String,
    annotations: std::collections::HashMap<String, String>,
}

impl crate::extensions::ProtocolExtension for SimpleAuraExtension {
    fn type_name(&self) -> &'static str {
        "SimpleAuraExtension"
    }

    fn mentions_role(&self, role: &crate::ast::Role) -> bool {
        role.name == self.sender || role.name == self.receiver
    }

    fn validate(
        &self,
        _roles: &[crate::ast::Role],
    ) -> std::result::Result<(), crate::extensions::ExtensionValidationError> {
        Ok(())
    }

    fn project(
        &self,
        _role: &crate::ast::Role,
        _context: &crate::extensions::ProjectionContext,
    ) -> std::result::Result<crate::ast::LocalType, crate::compiler::projection::ProjectionError>
    {
        Ok(crate::ast::LocalType::End)
    }

    fn generate_code(
        &self,
        _context: &crate::extensions::CodegenContext,
    ) -> proc_macro2::TokenStream {
        use quote::quote;
        let _annotations = &self.annotations;
        quote! {
            // Generated Aura extension code
            // Annotations: #(#annotations)*
        }
    }

    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
        self
    }

    fn type_id(&self) -> std::any::TypeId {
        std::any::TypeId::of::<Self>()
    }
}

/// Create an simple Aura extension from parsed components
fn create_aura_annotated_send(
    sender: String,
    receiver: String,
    message_type: String,
    annotations: std::collections::HashMap<String, String>,
) -> SimpleAuraExtension {
    SimpleAuraExtension {
        sender,
        receiver,
        message_type,
        annotations,
    }
}

/// Parse a choreographic protocol from a token stream (for macro use)
/// This is a compatibility function that wraps the string parser
pub fn parse_choreography(input: TokenStream) -> Result<Choreography> {
    use syn::LitStr;

    // Try to parse as a string literal (for DSL syntax)
    if let Ok(lit_str) = syn::parse2::<LitStr>(input.clone()) {
        // Parse the DSL string
        let dsl_content = lit_str.value();
        return parse_choreography_str(&dsl_content).map_err(|e| {
            syn::Error::new(lit_str.span(), format!("Choreography parse error: {e}"))
        });
    }

    // If not a string literal, return an error with helpful message
    Err(syn::Error::new(
        proc_macro2::Span::call_site(),
        "choreography! macro expects a string literal containing the choreography DSL.\n\
         Example usage:\n\
         choreography! { r#\"\n\
         choreography MyProtocol {\n\
             roles: Alice, Bob\n\
             Alice -> Bob: Hello\n\
         }\n\
         \"# }",
    ))
}

/// Parse a choreography from a file
pub fn parse_choreography_file(
    path: &std::path::Path,
) -> std::result::Result<Choreography, ParseError> {
    let content = std::fs::read_to_string(path).map_err(|e| ParseError::Syntax {
        span: ErrorSpan {
            line: 1,
            column: 1,
            line_end: 1,
            column_end: 1,
            snippet: format!("Failed to read file: {}", path.display()),
        },
        message: e.to_string(),
    })?;

    parse_choreography_str(&content)
}

/// Parse choreography DSL
pub fn parse_dsl(input: &str) -> std::result::Result<Choreography, ParseError> {
    parse_choreography_str(input)
}

// Example of how the macro would work
#[doc(hidden)]
#[must_use]
pub fn choreography_macro(input: TokenStream) -> TokenStream {
    let choreography = match parse_choreography(input) {
        Ok(c) => c,
        Err(e) => return e.to_compile_error(),
    };

    // Validate the choreography
    if let Err(e) = choreography.validate() {
        return syn::Error::new(Span::call_site(), e.to_string()).to_compile_error();
    }

    // Project to local types
    let mut local_types = Vec::new();
    for role in &choreography.roles {
        match super::projection::project(&choreography, role) {
            Ok(local_type) => local_types.push((role.clone(), local_type)),
            Err(e) => return syn::Error::new(Span::call_site(), e.to_string()).to_compile_error(),
        }
    }

    // Generate code with namespace support
    super::codegen::generate_choreography_code_with_namespacing(&choreography, &local_types)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_send() {
        let input = r"
choreography SimpleSend {
    roles: Alice, Bob

    Alice -> Bob: Hello
}
";

        let result = parse_choreography_str(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

        let choreo = result.unwrap();
        assert_eq!(choreo.name.to_string(), "SimpleSend");
        assert_eq!(choreo.roles.len(), 2);
    }

    #[test]
    fn test_parse_with_choice() {
        let input = r"
choreography Negotiation {
    roles: Buyer, Seller

    Buyer -> Seller: Offer

    choice Seller {
        accept: {
            Seller -> Buyer: Accept
        }
        reject: {
            Seller -> Buyer: Reject
        }
    }
}
";

        let result = parse_choreography_str(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

        let choreo = result.unwrap();
        assert_eq!(choreo.name.to_string(), "Negotiation");
    }

    #[test]
    fn test_parse_undefined_role() {
        let input = r"
choreography Invalid {
    roles: Alice

    Alice -> Bob: Hello
}
";

        let result = parse_choreography_str(input);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(matches!(err, ParseError::UndefinedRole { .. }));

        // Verify error message includes span information
        let err_str = err.to_string();
        assert!(err_str.contains("Undefined role"));
        assert!(err_str.contains("Bob"));
    }

    #[test]
    fn test_parse_duplicate_role() {
        let input = r"
choreography Invalid {
    roles: Alice, Bob, Alice

    Alice -> Bob: Hello
}
";

        let result = parse_choreography_str(input);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(matches!(err, ParseError::DuplicateRole { .. }));

        // Verify error message includes span information
        let err_str = err.to_string();
        assert!(err_str.contains("Duplicate role"));
        assert!(err_str.contains("Alice"));
    }

    #[test]
    fn test_parse_loop() {
        let input = r"
choreography LoopProtocol {
    roles: Client, Server

    loop (count: 3) {
        Client -> Server: Request
        Server -> Client: Response
    }
}
";

        let result = parse_choreography_str(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());
    }
}
