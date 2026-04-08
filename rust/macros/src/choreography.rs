//! Telltale protocol definition macro implementation.
//!
//! Parsing is delegated to the shared Telltale frontend. This proc-macro now
//! only recovers source text and proc-macro diagnostics; the protocol-module
//! lowering/codegen path itself is shared with string-fed compilation in
//! `telltale-language`.

use proc_macro::{Delimiter, TokenStream as MacroTokenStream, TokenTree as MacroTokenTree};
use proc_macro2::{Span, TokenStream};
use syn::{Error, LitStr, Result};
use telltale_language::Choreography;

struct ParsedMacroChoreography {
    choreography: Choreography,
    source: String,
}

/// Main entry point for the tell! macro.
///
/// This macro is intentionally outside the current formal-verification claim.
/// It is treated as a public frontend convenience surface whose generated
/// output is checked by compiler-pipeline, Lean-correspondence, and macro-UI
/// gates rather than by a mechanized macro-expansion proof.
pub fn tell(input: MacroTokenStream) -> Result<TokenStream> {
    let parsed = parse_macro_choreography(input)?;
    parsed
        .choreography
        .validate()
        .map_err(|err| Error::new(Span::call_site(), err.to_string()))?;

    telltale_language::generate_protocol_module(&parsed.choreography, &parsed.source)
}

fn parse_macro_choreography(input: MacroTokenStream) -> Result<ParsedMacroChoreography> {
    if let Ok(lit_str) = syn::parse::<LitStr>(input.clone()) {
        return Err(Error::new(
            lit_str.span(),
            "string-literal tell input was removed; use the canonical indentation-based token DSL directly",
        ));
    }

    let source = macro_source_text(input)
        .map(normalize_macro_indentation)
        .ok_or_else(|| {
            Error::new(
                Span::call_site(),
                "failed to recover original choreography source from macro input",
            )
        })?;

    let choreography = telltale_language::parse_choreography_str(&source).map_err(|err| {
        Error::new(
            Span::call_site(),
            format!(
                "Choreography parse error: {err}\n\
                 Macro token input is parsed from original source text.\n\
                 Use the canonical indentation-based DSL surface in token form."
            ),
        )
    })?;

    Ok(ParsedMacroChoreography {
        choreography,
        source,
    })
}

fn normalize_macro_indentation(source: String) -> String {
    const TOP_LEVEL_HEADERS: &[&str] = &[
        "module ",
        "import ",
        "protocol ",
        "proof_bundle ",
        "profile ",
        "agreement_profile ",
        "role_set ",
        "topology ",
        "type ",
        "effect ",
        "fragment ",
        "operation ",
        "guest runtime ",
    ];

    let mut normalized = String::new();
    for line in source.lines() {
        let trimmed = line.trim_start();
        if TOP_LEVEL_HEADERS
            .iter()
            .any(|prefix| trimmed.starts_with(prefix))
        {
            normalized.push_str(trimmed);
        } else {
            normalized.push_str(line);
        }
        normalized.push('\n');
    }

    if !source.ends_with('\n') {
        normalized.pop();
    }

    normalized
}

fn macro_source_text(input: MacroTokenStream) -> Option<String> {
    #[derive(Clone, Copy)]
    struct Location {
        line: usize,
        column: usize,
    }

    #[allow(clippy::incompatible_msrv)]
    fn location_of(span: proc_macro::Span) -> (Location, Location) {
        let start = span.start();
        let end = span.end();
        (
            Location {
                line: start.line(),
                column: start.column(),
            },
            Location {
                line: end.line(),
                column: end.column(),
            },
        )
    }

    fn append_gap(out: &mut String, previous_end: Location, next_start: Location) {
        if next_start.line > previous_end.line {
            for _ in previous_end.line..next_start.line {
                out.push('\n');
            }
            for _ in 0..next_start.column {
                out.push(' ');
            }
        } else if next_start.column > previous_end.column {
            for _ in previous_end.column..next_start.column {
                out.push(' ');
            }
        }
    }

    fn append_stream(
        out: &mut String,
        previous_end: &mut Option<Location>,
        stream: MacroTokenStream,
    ) -> Option<()> {
        for token in stream {
            match token {
                MacroTokenTree::Group(group) => {
                    let (open_start, _) = location_of(group.span_open());
                    let (_, close_end) = location_of(group.span_close());
                    if let Some(prev) = previous_end.as_ref() {
                        append_gap(out, *prev, open_start);
                    }
                    out.push_str(&group.to_string());
                    *previous_end = Some(close_end);
                }
                MacroTokenTree::Ident(ident) => {
                    let (start, end) = location_of(ident.span());
                    if let Some(prev) = previous_end.as_ref() {
                        append_gap(out, *prev, start);
                    }
                    out.push_str(&ident.to_string());
                    *previous_end = Some(end);
                }
                MacroTokenTree::Punct(punct) => {
                    let (start, end) = location_of(punct.span());
                    if let Some(prev) = previous_end.as_ref() {
                        append_gap(out, *prev, start);
                    }
                    out.push(punct.as_char());
                    *previous_end = Some(end);
                }
                MacroTokenTree::Literal(literal) => {
                    let (start, end) = location_of(literal.span());
                    if let Some(prev) = previous_end.as_ref() {
                        append_gap(out, *prev, start);
                    }
                    out.push_str(&literal.to_string());
                    *previous_end = Some(end);
                }
            }
        }
        Some(())
    }

    fn strip_group_source(source: &str, delimiter: Delimiter) -> String {
        let trimmed = source.trim();
        match delimiter {
            Delimiter::Parenthesis | Delimiter::Brace | Delimiter::Bracket
                if trimmed.len() >= 2 =>
            {
                trimmed[1..trimmed.len() - 1].to_string()
            }
            _ => trimmed.to_string(),
        }
    }

    let mut tokens = input.clone().into_iter();
    if let Some(MacroTokenTree::Group(group)) = tokens.next() {
        let single_group = tokens.next().is_none();
        if single_group {
            if let Some(source) = group.span().source_text() {
                return Some(strip_group_source(&source, group.delimiter()));
            }
        }
        if single_group && group.delimiter() == Delimiter::Brace {
            return macro_source_text(group.stream());
        }
    }

    let mut out = String::new();
    let mut previous_end = None;
    append_stream(&mut out, &mut previous_end, input)?;
    Some(out)
}
