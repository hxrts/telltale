// Parser for choreographic protocol syntax
//
// Full implementation using Pest grammar for parsing choreographic DSL

use crate::ast::{
    Branch, Choreography, Condition, MessageType, Protocol, RangeExpr, Role, RoleIndex, RoleParam,
    RoleRange,
};
use crate::compiler::layout::preprocess_layout;
use crate::extensions::{ExtensionRegistry, ProtocolExtension};
use pest::Parser;
use pest_derive::Parser;
use proc_macro2::{Ident, Span, TokenStream};
use quote::format_ident;
use std::collections::{HashMap, HashSet};
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

    /// Create an `ErrorSpan` from a line/column pair.
    fn from_line_col(line: usize, column: usize, input: &str) -> Self {
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

/// Parse a role parameter using enhanced syntax
fn parse_role_param(
    pair: pest::iterators::Pair<Rule>,
    _role_name: &str,
    input: &str,
) -> std::result::Result<RoleParam, ParseError> {
    let mut inner = pair.into_inner();
    let param_expr = inner
        .next()
        .expect("grammar: role_param must contain role_param_expr");

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
    let index_expr = inner
        .next()
        .expect("grammar: role_index must contain role_index_expr");

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
    let start_expr = inner
        .next()
        .expect("grammar: range_expr must have start expression");
    let end_expr = inner
        .next()
        .expect("grammar: range_expr must have end expression");

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
fn parse_module_decl(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<String, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    if let Some(ident) = inner.next() {
        if ident.as_rule() == Rule::ident {
            return Ok(ident.as_str().to_string());
        }
    }
    Err(ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "Invalid module declaration".to_string(),
    })
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
    let dedented = strip_common_indent(input);
    let layout = preprocess_layout(&dedented).map_err(|e| ParseError::Layout {
        span: ErrorSpan::from_line_col(e.line, e.column, &dedented),
        message: e.message,
    })?;

    let preprocessed = preprocess_extension_syntax(&layout, registry)?;

    let pairs = ChoreographyParser::parse(Rule::choreography, &preprocessed).map_err(Box::new)?;

    let mut name = format_ident!("Unnamed");
    let mut namespace: Option<String> = None;
    let mut roles: Vec<Role> = Vec::new();
    let mut declared_roles: HashSet<String> = HashSet::new();
    let mut protocol_defs: HashMap<String, Vec<Statement>> = HashMap::new();
    let mut statements: Vec<Statement> = Vec::new();

    for pair in pairs {
        if pair.as_rule() == Rule::choreography {
            for inner in pair.into_inner() {
                match inner.as_rule() {
                    Rule::module_decl => {
                        namespace = Some(parse_module_decl(inner, &preprocessed)?);
                    }
                    Rule::import_decl => {
                        // Imports are parsed for completeness but ignored for now.
                    }
                    Rule::protocol_decl => {
                        let mut proto_inner = inner.into_inner();
                        let name_pair = proto_inner
                            .next()
                            .expect("grammar: protocol_decl must have name");
                        name = format_ident!("{}", name_pair.as_str());

                        let mut header_roles: Option<Vec<Role>> = None;
                        let mut body_pair: Option<pest::iterators::Pair<Rule>> = None;
                        let mut where_pair: Option<pest::iterators::Pair<Rule>> = None;

                        for item in proto_inner {
                            match item.as_rule() {
                                Rule::header_roles => {
                                    header_roles =
                                        Some(parse_roles_from_pair(item, &preprocessed)?);
                                }
                                Rule::protocol_body => {
                                    body_pair = Some(item);
                                }
                                Rule::where_block => {
                                    where_pair = Some(item);
                                }
                                _ => {}
                            }
                        }

                        let allow_roles_decl = header_roles.is_none();
                        let body_pair = body_pair.expect("grammar: protocol_decl must have body");
                        let body_span = body_pair.as_span();
                        let ParsedBody {
                            roles: body_roles,
                            statements: body_statements,
                        } = parse_protocol_body(
                            body_pair,
                            &declared_roles,
                            &preprocessed,
                            &protocol_defs,
                            allow_roles_decl,
                        )?;

                        if header_roles.is_some() && body_roles.is_some() {
                            return Err(ParseError::Syntax {
                                span: ErrorSpan::from_pest_span(body_span, &preprocessed),
                                message: "roles cannot be declared both in the header and body"
                                    .to_string(),
                            });
                        }

                        if let Some(r) = header_roles {
                            roles = r;
                            declared_roles = roles.iter().map(|r| r.name.to_string()).collect();
                        } else if let Some(r) = body_roles {
                            roles = r;
                            declared_roles = roles.iter().map(|r| r.name.to_string()).collect();
                        }

                        if let Some(where_block) = where_pair {
                            for local in where_block.into_inner().flat_map(|p| p.into_inner()) {
                                if local.as_rule() == Rule::local_protocol_decl {
                                    parse_local_protocol_decl(
                                        local,
                                        &declared_roles,
                                        &preprocessed,
                                        &mut protocol_defs,
                                    )?;
                                }
                            }
                        }

                        statements = inline_calls(&body_statements, &protocol_defs, &preprocessed)?;
                    }
                    _ => {}
                }
            }
        }
    }

    if roles.is_empty() {
        return Err(ParseError::EmptyChoreography);
    }

    let protocol = convert_statements_to_protocol(&statements, &roles);

    Ok((
        Choreography {
            name,
            namespace,
            roles,
            protocol,
            attrs: HashMap::new(),
        },
        Vec::new(),
    ))
}

/// Parse protocol body into statements
struct ParsedBody {
    roles: Option<Vec<Role>>,
    statements: Vec<Statement>,
}

fn parse_roles_from_pair(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<Vec<Role>, ParseError> {
    let mut roles = Vec::new();
    let mut declared = HashSet::new();

    let mut role_list_pairs: Vec<pest::iterators::Pair<Rule>> = Vec::new();
    match pair.as_rule() {
        Rule::roles_decl | Rule::header_roles => {
            for inner in pair.into_inner() {
                if inner.as_rule() == Rule::role_list {
                    role_list_pairs.push(inner);
                }
            }
        }
        Rule::role_list => role_list_pairs.push(pair),
        _ => {}
    }

    for role_list in role_list_pairs {
        for role_decl in role_list.into_inner() {
            if let Rule::role_decl = role_decl.as_rule() {
                let mut inner_role = role_decl.into_inner();
                let role_ident = inner_role
                    .next()
                    .expect("grammar: role_decl must have identifier");
                let role_name = role_ident.as_str().trim();
                let span = role_ident.as_span();

                let role = if let Some(param_pair) = inner_role.next() {
                    if param_pair.as_rule() == Rule::role_param {
                        match parse_role_param(param_pair, role_name, input) {
                            Ok(param) => Role::with_param(format_ident!("{}", role_name), param),
                            Err(e) => return Err(e),
                        }
                    } else {
                        Role::new(format_ident!("{}", role_name))
                    }
                } else {
                    Role::new(format_ident!("{}", role_name))
                };

                if !declared.insert(role_name.to_string()) {
                    return Err(ParseError::DuplicateRole {
                        role: role_name.to_string(),
                        span: ErrorSpan::from_pest_span(span, input),
                    });
                }

                roles.push(role);
            }
        }
    }

    Ok(roles)
}

fn parse_protocol_body(
    pair: pest::iterators::Pair<Rule>,
    declared_roles_base: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
    allow_roles_decl: bool,
) -> std::result::Result<ParsedBody, ParseError> {
    let mut roles: Option<Vec<Role>> = None;
    let mut statements = Vec::new();
    let mut declared_roles = declared_roles_base.clone();

    let mut inner_pairs: Vec<pest::iterators::Pair<Rule>> = Vec::new();
    match pair.as_rule() {
        Rule::protocol_body => {
            if let Some(inner) = pair.into_inner().next() {
                inner_pairs = inner.into_inner().collect();
            }
        }
        Rule::block_protocol | Rule::block => {
            inner_pairs = pair.into_inner().collect();
        }
        _ => {
            inner_pairs = pair.into_inner().collect();
        }
    }

    for item in inner_pairs {
        match item.as_rule() {
            Rule::roles_decl => {
                if !allow_roles_decl {
                    return Err(ParseError::Syntax {
                        span: ErrorSpan::from_pest_span(item.as_span(), input),
                        message: "roles declaration is not allowed here".to_string(),
                    });
                }
                if roles.is_some() {
                    return Err(ParseError::Syntax {
                        span: ErrorSpan::from_pest_span(item.as_span(), input),
                        message: "duplicate roles declaration".to_string(),
                    });
                }
                let parsed_roles = parse_roles_from_pair(item, input)?;
                declared_roles = parsed_roles.iter().map(|r| r.name.to_string()).collect();
                roles = Some(parsed_roles);
            }
            _ => {
                let statement = parse_statement(item, &declared_roles, input, protocol_defs)?;
                statements.push(statement);
            }
        }
    }

    let statements = normalize_branches_to_parallel(statements, input)?;
    Ok(ParsedBody { roles, statements })
}

fn parse_block(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Vec<Statement>, ParseError> {
    let span = pair.as_span();
    let ParsedBody { roles, statements } =
        parse_protocol_body(pair, declared_roles, input, protocol_defs, false)?;
    if roles.is_some() {
        return Err(ParseError::Syntax {
            span: ErrorSpan::from_pest_span(span, input),
            message: "roles declaration is not allowed in this block".to_string(),
        });
    }
    Ok(statements)
}

fn parse_local_protocol_decl(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &mut HashMap<String, Vec<Statement>>,
) -> std::result::Result<(), ParseError> {
    let mut inner = pair.into_inner();
    let name_pair = inner
        .next()
        .expect("grammar: local_protocol_decl must have name");
    let proto_name = name_pair.as_str().to_string();
    let span = name_pair.as_span();

    if protocol_defs.contains_key(&proto_name) {
        return Err(ParseError::DuplicateProtocol {
            protocol: proto_name,
            span: ErrorSpan::from_pest_span(span, input),
        });
    }

    let mut body_pair: Option<pest::iterators::Pair<Rule>> = None;
    for item in inner {
        match item.as_rule() {
            Rule::header_roles => {
                return Err(ParseError::Syntax {
                    span: ErrorSpan::from_pest_span(item.as_span(), input),
                    message: "local protocols cannot declare roles".to_string(),
                });
            }
            Rule::protocol_body => body_pair = Some(item),
            _ => {}
        }
    }

    let ParsedBody { roles, statements } = parse_protocol_body(
        body_pair.expect("grammar: local_protocol_decl must have body"),
        declared_roles,
        input,
        protocol_defs,
        false,
    )?;

    if roles.is_some() {
        return Err(ParseError::Syntax {
            span: ErrorSpan::from_pest_span(span, input),
            message: "local protocols cannot declare roles".to_string(),
        });
    }

    protocol_defs.insert(proto_name, statements);
    Ok(())
}

fn normalize_branches_to_parallel(
    statements: Vec<Statement>,
    input: &str,
) -> std::result::Result<Vec<Statement>, ParseError> {
    let mut result = Vec::new();
    let mut i = 0usize;

    while i < statements.len() {
        match &statements[i] {
            Statement::Branch { .. } => {
                let mut branches = Vec::new();
                let mut span = None;
                while i < statements.len() {
                    if let Statement::Branch { body, span: s } = &statements[i] {
                        if span.is_none() {
                            span = Some(s.clone());
                        }
                        branches.push(body.clone());
                        i += 1;
                    } else {
                        break;
                    }
                }

                if branches.len() < 2 {
                    let err_span = span.unwrap_or_else(|| ErrorSpan::from_line_col(1, 1, input));
                    return Err(ParseError::Syntax {
                        span: err_span,
                        message: "parallel requires at least two adjacent branch blocks"
                            .to_string(),
                    });
                }

                result.push(Statement::Parallel { branches });
            }
            _ => {
                result.push(statements[i].clone());
                i += 1;
            }
        }
    }

    Ok(result)
}

/// Parse a single statement
fn parse_statement(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    parse_statement_inner(pair, declared_roles, input, protocol_defs)
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
        Rule::branch_stmt => parse_branch_stmt(pair, declared_roles, input, protocol_defs),
        Rule::rec_stmt => parse_rec_stmt(pair, declared_roles, input, protocol_defs),
        Rule::continue_stmt => parse_continue_stmt(pair),
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

    let role_ident = inner
        .next()
        .expect("grammar: role_ref must have identifier");
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

/// Parse send statement: A -> B: Message(payload)
fn parse_send_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
) -> std::result::Result<Statement, ParseError> {
    let mut inner = pair.into_inner();

    let from_pair = inner
        .next()
        .expect("grammar: send_stmt must have sender role");
    let from = parse_role_ref(from_pair, declared_roles, input)?;

    let to_pair = inner
        .next()
        .expect("grammar: send_stmt must have receiver role");
    let to = parse_role_ref(to_pair, declared_roles, input)?;

    let message = parse_message(
        inner.next().expect("grammar: send_stmt must have message"),
        input,
    )?;

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

    let from_pair = inner
        .next()
        .expect("grammar: broadcast_stmt must have sender role");
    let from = parse_role_ref(from_pair, declared_roles, input)?;

    let message = parse_message(
        inner
            .next()
            .expect("grammar: broadcast_stmt must have message"),
        input,
    )?;

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
    let span = pair.as_span();
    let mut role: Option<Role> = None;
    let mut branches = Vec::new();

    let mut parse_branch = |item: pest::iterators::Pair<Rule>| -> Result<(), ParseError> {
        let mut branch_inner = item.into_inner();
        let label = format_ident!(
            "{}",
            branch_inner
                .next()
                .expect("grammar: choice_branch must have label")
                .as_str()
        );

        // Check for optional guard
        let mut guard = None;
        let next_item = branch_inner
            .next()
            .expect("grammar: choice_branch must have body or guard");
        let body = if let Rule::guard = next_item.as_rule() {
            let guard_span = next_item.as_span();
            let guard_expr = next_item
                .into_inner()
                .next()
                .expect("grammar: guard must have expression")
                .as_str();
            guard = Some(syn::parse_str::<TokenStream>(guard_expr).map_err(|e| {
                ParseError::Syntax {
                    span: ErrorSpan::from_pest_span(guard_span, input),
                    message: format!("Invalid guard expression: {e}"),
                }
            })?);
            parse_block(
                branch_inner
                    .next()
                    .expect("grammar: choice_branch with guard must have body"),
                declared_roles,
                input,
                protocol_defs,
            )?
        } else {
            parse_block(next_item, declared_roles, input, protocol_defs)?
        };

        branches.push(ChoiceBranch {
            label,
            guard,
            statements: body,
        });
        Ok(())
    };

    for item in pair.into_inner() {
        match item.as_rule() {
            Rule::choice_head => {
                for head_item in item.into_inner() {
                    if head_item.as_rule() == Rule::role_ref {
                        role = Some(parse_role_ref(head_item, declared_roles, input)?);
                    }
                }
            }
            Rule::choice_block => {
                for branch_item in item.into_inner() {
                    match branch_item.as_rule() {
                        Rule::choice_branch => {
                            parse_branch(branch_item)?;
                        }
                        Rule::block_choice => {
                            for nested in branch_item.into_inner() {
                                if nested.as_rule() == Rule::choice_branch {
                                    parse_branch(nested)?;
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
            Rule::role_ref => {
                role = Some(parse_role_ref(item, declared_roles, input)?);
            }
            Rule::choice_branch => {
                parse_branch(item)?;
            }
            _ => {}
        }
    }

    let role = role.ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "choice is missing a deciding role".to_string(),
    })?;

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
    let mut condition = None;
    let mut body = Vec::new();

    for item in pair.into_inner() {
        match item.as_rule() {
            Rule::loop_spec => {
                for spec in item.into_inner() {
                    match spec.as_rule() {
                        Rule::loop_decide => {
                            let span = spec.as_span();
                            let role_pair = spec
                                .into_inner()
                                .find(|p| p.as_rule() == Rule::role_ref)
                                .ok_or_else(|| ParseError::Syntax {
                                    span: ErrorSpan::from_pest_span(span, input),
                                    message: "loop decide by is missing a role".to_string(),
                                })?;
                            let role = parse_role_ref(role_pair, declared_roles, input)?;
                            condition = Some(Condition::RoleDecides(role));
                        }
                        Rule::loop_repeat => {
                            let span = spec.as_span();
                            let count_pair = spec
                                .into_inner()
                                .next()
                                .expect("grammar: loop_repeat must have value");
                            let count_str = count_pair.as_str();
                            if let Ok(count) = count_str.parse::<usize>() {
                                condition = Some(Condition::Count(count));
                            } else {
                                let token_stream = syn::parse_str::<TokenStream>(count_str)
                                    .map_err(|e| ParseError::InvalidCondition {
                                        message: format!("Invalid repeat value: {e}"),
                                        span: ErrorSpan::from_pest_span(span, input),
                                    })?;
                                condition = Some(Condition::Custom(token_stream));
                            }
                        }
                        Rule::loop_while => {
                            let span = spec.as_span();
                            let cond_pair = spec
                                .into_inner()
                                .next()
                                .expect("grammar: loop while must have string");
                            let cond_str = cond_pair.as_str();
                            let token_stream =
                                syn::parse_str::<TokenStream>(cond_str).map_err(|e| {
                                    ParseError::InvalidCondition {
                                        message: format!("Invalid loop condition: {e}"),
                                        span: ErrorSpan::from_pest_span(span, input),
                                    }
                                })?;
                            condition = Some(Condition::Custom(token_stream));
                        }
                        Rule::loop_forever => {
                            condition = None;
                        }
                        _ => {}
                    }
                }
            }
            Rule::loop_decide | Rule::loop_repeat | Rule::loop_while | Rule::loop_forever => {
                // Fall back for grammars that expose loop spec directly.
                let spec = item;
                match spec.as_rule() {
                    Rule::loop_decide => {
                        let span = spec.as_span();
                        let role_pair = spec
                            .into_inner()
                            .find(|p| p.as_rule() == Rule::role_ref)
                            .ok_or_else(|| ParseError::Syntax {
                            span: ErrorSpan::from_pest_span(span, input),
                            message: "loop decide by is missing a role".to_string(),
                        })?;
                        let role = parse_role_ref(role_pair, declared_roles, input)?;
                        condition = Some(Condition::RoleDecides(role));
                    }
                    Rule::loop_repeat => {
                        let span = spec.as_span();
                        let count_pair = spec
                            .into_inner()
                            .next()
                            .expect("grammar: loop_repeat must have value");
                        let count_str = count_pair.as_str();
                        if let Ok(count) = count_str.parse::<usize>() {
                            condition = Some(Condition::Count(count));
                        } else {
                            let token_stream =
                                syn::parse_str::<TokenStream>(count_str).map_err(|e| {
                                    ParseError::InvalidCondition {
                                        message: format!("Invalid repeat value: {e}"),
                                        span: ErrorSpan::from_pest_span(span, input),
                                    }
                                })?;
                            condition = Some(Condition::Custom(token_stream));
                        }
                    }
                    Rule::loop_while => {
                        let span = spec.as_span();
                        let cond_pair = spec
                            .into_inner()
                            .next()
                            .expect("grammar: loop while must have string");
                        let cond_str = cond_pair.as_str();
                        let token_stream =
                            syn::parse_str::<TokenStream>(cond_str).map_err(|e| {
                                ParseError::InvalidCondition {
                                    message: format!("Invalid loop condition: {e}"),
                                    span: ErrorSpan::from_pest_span(span, input),
                                }
                            })?;
                        condition = Some(Condition::Custom(token_stream));
                    }
                    Rule::loop_forever => {
                        condition = None;
                    }
                    _ => {}
                }
            }
            Rule::block => {
                body = parse_block(item, declared_roles, input, protocol_defs)?;
            }
            _ => {}
        }
    }

    Ok(Statement::Loop { condition, body })
}

/// Parse branch statement
fn parse_branch_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    let span = ErrorSpan::from_pest_span(pair.as_span(), input);
    let mut body = Vec::new();
    for item in pair.into_inner() {
        if item.as_rule() == Rule::block {
            body = parse_block(item, declared_roles, input, protocol_defs)?;
        }
    }
    Ok(Statement::Branch { body, span })
}

/// Parse recursive statement
fn parse_rec_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    let mut inner = pair.into_inner();

    let label = format_ident!(
        "{}",
        inner
            .next()
            .expect("grammar: rec_stmt must have label")
            .as_str()
    );
    let body = parse_block(
        inner.next().expect("grammar: rec_stmt must have body"),
        declared_roles,
        input,
        protocol_defs,
    )?;

    Ok(Statement::Rec { label, body })
}

/// Parse protocol call statement
fn parse_call_stmt(
    pair: pest::iterators::Pair<Rule>,
    _declared_roles: &HashSet<String>,
    _input: &str,
    _protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    let mut inner = pair.into_inner();
    let proto_name_pair = inner
        .next()
        .expect("grammar: call_stmt must have protocol name");
    let proto_name = proto_name_pair.as_str();

    Ok(Statement::Call {
        name: format_ident!("{}", proto_name),
    })
}

/// Parse continue statement (recursive back-reference)
fn parse_continue_stmt(
    pair: pest::iterators::Pair<Rule>,
) -> std::result::Result<Statement, ParseError> {
    let mut inner = pair.into_inner();
    let label_pair = inner
        .next()
        .expect("grammar: continue_stmt must have label");
    let label = label_pair.as_str();

    Ok(Statement::Continue {
        label: format_ident!("{}", label),
    })
}

/// Parse message specification
fn parse_message(
    pair: pest::iterators::Pair<Rule>,
    _input: &str,
) -> std::result::Result<MessageSpec, ParseError> {
    let _span = pair.as_span();
    let mut inner = pair.into_inner();

    let name = format_ident!(
        "{}",
        inner
            .next()
            .expect("grammar: message must have name")
            .as_str()
    );

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
    Branch {
        body: Vec<Statement>,
        span: ErrorSpan,
    },
    Parallel {
        branches: Vec<Vec<Statement>>,
    },
    Rec {
        label: Ident,
        body: Vec<Statement>,
    },
    /// Recursive back-reference (continue to a rec label)
    Continue {
        label: Ident,
    },
    Call {
        #[allow(dead_code)]
        name: Ident,
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

    let mut current = Protocol::End;

    // Build protocol from back to front
    for statement in statements.iter().rev() {
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
            Statement::Branch { .. } => {
                // Branch blocks should be normalized into Parallel before conversion.
                current
            }
            Statement::Rec { label, body } => Protocol::Rec {
                label: label.clone(),
                body: Box::new(convert_statements_to_protocol(body, roles)),
            },
            Statement::Continue { label } => Protocol::Var(label.clone()),
            Statement::Call { .. } => current,
        };
    }

    current
}

/// Inline all Call statements by replacing them with their definitions
fn inline_calls(
    statements: &[Statement],
    protocol_defs: &HashMap<String, Vec<Statement>>,
    input: &str,
) -> std::result::Result<Vec<Statement>, ParseError> {
    let mut result = Vec::new();

    for statement in statements {
        match statement {
            Statement::Call { name } => {
                let key = name.to_string();
                let called =
                    protocol_defs
                        .get(&key)
                        .ok_or_else(|| ParseError::UndefinedProtocol {
                            protocol: key.clone(),
                            span: ErrorSpan::from_line_col(1, 1, input),
                        })?;
                result.extend(inline_calls(called, protocol_defs, input)?);
            }
            Statement::Choice { role, branches, .. } => {
                // Inline calls within choice branches
                let mut new_branches = Vec::new();
                for b in branches {
                    new_branches.push(ChoiceBranch {
                        label: b.label.clone(),
                        guard: b.guard.clone(),
                        statements: inline_calls(&b.statements, protocol_defs, input)?,
                    });
                }
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
                    body: inline_calls(body, protocol_defs, input)?,
                });
            }
            Statement::Parallel { branches } => {
                // Inline calls within parallel branches
                let mut new_branches = Vec::new();
                for b in branches {
                    new_branches.push(inline_calls(b, protocol_defs, input)?);
                }
                result.push(Statement::Parallel {
                    branches: new_branches,
                });
            }
            Statement::Branch { body, span } => {
                result.push(Statement::Branch {
                    body: inline_calls(body, protocol_defs, input)?,
                    span: span.clone(),
                });
            }
            Statement::Rec { label, body } => {
                // Inline calls within recursive body
                result.push(Statement::Rec {
                    label: label.clone(),
                    body: inline_calls(body, protocol_defs, input)?,
                });
            }
            _ => {
                // Other statements remain unchanged
                result.push(statement.clone());
            }
        }
    }

    Ok(result)
}

/// Preprocess extension syntax to transform it into standard DSL syntax.
///
/// The new DSL drops annotation/extension surface syntax for now, so this is a
/// no-op placeholder that keeps the API stable.
fn preprocess_extension_syntax(
    input: &str,
    _registry: &ExtensionRegistry,
) -> std::result::Result<String, ParseError> {
    Ok(input.to_string())
}

fn strip_common_indent(input: &str) -> String {
    let lines: Vec<&str> = input.lines().collect();
    let mut min_indent: Option<usize> = None;

    for line in &lines {
        if line.trim().is_empty() {
            continue;
        }
        let indent = line.chars().take_while(|c| *c == ' ').count();
        min_indent = Some(match min_indent {
            Some(current) => current.min(indent),
            None => indent,
        });
    }

    let min_indent = min_indent.unwrap_or(0);
    if min_indent == 0 {
        return input.to_string();
    }

    let mut out = String::new();
    for (idx, line) in lines.iter().enumerate() {
        let stripped = line.get(min_indent..).unwrap_or(line);
        out.push_str(stripped);
        if idx + 1 < lines.len() {
            out.push('\n');
        }
    }

    if input.ends_with('\n') {
        out.push('\n');
    }

    out
}

/// Parse a choreographic protocol from a token stream (for macro use)
/// This is a compatibility function that wraps the string parser
pub fn parse_choreography(input: TokenStream) -> syn::Result<Choreography> {
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
         protocol MyProtocol =\n\
           roles Alice, Bob\n\
           Alice -> Bob : Hello\n\
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
    use crate::ast::Protocol;

    #[test]
    fn test_parse_simple_send() {
        let input = r#"
protocol SimpleSend =
  roles Alice, Bob
  Alice -> Bob : Hello
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

        let choreo = result.unwrap();
        assert_eq!(choreo.name.to_string(), "SimpleSend");
        assert_eq!(choreo.roles.len(), 2);
    }

    #[test]
    fn test_parse_with_choice() {
        let input = r#"
protocol Negotiation =
  roles Buyer, Seller
  Buyer -> Seller : Offer
  case choose Seller of
    accept ->
      Seller -> Buyer : Accept
    reject ->
      Seller -> Buyer : Reject
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

        let choreo = result.unwrap();
        assert_eq!(choreo.name.to_string(), "Negotiation");
    }

    #[test]
    fn test_parse_choice_alias() {
        let input = r#"
protocol AliasChoice =
  roles A, B
  choice at A
    ok ->
      A -> B : Ack
    fail ->
      A -> B : Nack
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse alias choice: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_parse_undefined_role() {
        let input = r#"
protocol Invalid =
  roles Alice
  Alice -> Bob : Hello
"#;

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
        let input = r#"
protocol DuplicateRole =
  roles Alice, Bob, Alice
  Alice -> Bob : Hello
"#;

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
    fn test_parse_loop_repeat() {
        let input = r#"
protocol LoopProtocol =
  roles Client, Server
  loop repeat 3
    Client -> Server : Request
    Server -> Client : Response
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());
    }

    #[test]
    fn test_parse_loop_decide() {
        let input = r#"
protocol DecideLoop =
  roles Client, Server
  loop decide by Client
    Client -> Server : Ping
    Server -> Client : Pong
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse decide loop: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_parse_parallel_branches() {
        let input = r#"
protocol Parallel =
  roles A, B, C, D
  branch
    A -> B : Msg1
  branch
    C -> D : Msg2
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse parallel: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match choreo.protocol {
            Protocol::Parallel { protocols } => {
                assert_eq!(protocols.len(), 2);
            }
            _ => panic!("Expected top-level parallel protocol"),
        }
    }

    #[test]
    fn test_single_branch_is_error() {
        let input = r#"
protocol SingleBranch =
  roles A, B
  branch
    A -> B : Msg
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_err());
        let err = result.unwrap_err();
        let err_str = err.to_string();
        assert!(err_str.contains("parallel requires at least two adjacent branch blocks"));
    }
}
