#![allow(clippy::expect_used)]

//! Validate source-document DSL snippets against the real parser.

use std::fs;
use std::path::{Path, PathBuf};

use telltale_runtime::compiler::parser::parse_choreography_str;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FenceKind {
    Tell,
    Rust,
}

#[derive(Debug, Clone)]
struct Fence {
    kind: FenceKind,
    start_line: usize,
    content: String,
}

#[derive(Debug, Clone, Copy)]
enum SnippetKind {
    TellFence,
    TellMacro,
    ParserString,
}

#[derive(Debug, Clone)]
struct Snippet {
    kind: SnippetKind,
    start_line: usize,
    content: String,
}

#[test]
fn source_doc_dsl_snippets_parse() {
    let docs_dir = workspace_root().join("docs");
    let mut failures = Vec::new();

    for path in markdown_files(&docs_dir) {
        let content = fs::read_to_string(&path).expect("read markdown source");
        let fences = extract_fences(&content);
        let mut snippets = Vec::new();

        for fence in fences {
            match fence.kind {
                FenceKind::Tell => snippets.push(Snippet {
                    kind: SnippetKind::TellFence,
                    start_line: fence.start_line,
                    content: fence.content,
                }),
                FenceKind::Rust => {
                    snippets.extend(extract_tell_macros(&fence));
                    snippets.extend(extract_parser_strings(&fence));
                }
            }
        }

        for snippet in snippets {
            if let Err(err) = parse_source_snippet(&snippet) {
                failures.push(format!(
                    "{}:{}: {:?} failed to parse: {}\n{}",
                    path.display(),
                    snippet.start_line,
                    snippet.kind,
                    err,
                    snippet.content
                ));
            }
        }
    }

    if !failures.is_empty() {
        panic!(
            "source-doc DSL snippet validation failed:\n\n{}",
            failures.join("\n\n")
        );
    }
}

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("runtime crate parent")
        .parent()
        .expect("workspace root")
        .to_path_buf()
}

fn markdown_files(docs_dir: &Path) -> Vec<PathBuf> {
    let mut files = fs::read_dir(docs_dir)
        .expect("list docs dir")
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.extension().and_then(|ext| ext.to_str()) == Some("md"))
        .collect::<Vec<_>>();
    files.sort();
    files
}

fn extract_fences(markdown: &str) -> Vec<Fence> {
    let mut fences = Vec::new();
    let mut current_kind = None;
    let mut current_start = 0usize;
    let mut current_lines = Vec::new();

    for (index, line) in markdown.lines().enumerate() {
        let line_no = index + 1;
        if current_kind.is_none() {
            let trimmed = line.trim();
            if trimmed == "```tell" {
                current_kind = Some(FenceKind::Tell);
                current_start = line_no + 1;
                current_lines.clear();
            } else if trimmed == "```rust" {
                current_kind = Some(FenceKind::Rust);
                current_start = line_no + 1;
                current_lines.clear();
            }
            continue;
        }

        if line.trim() == "```" {
            fences.push(Fence {
                kind: current_kind.expect("open fence"),
                start_line: current_start,
                content: strip_common_indent(&current_lines.join("\n")),
            });
            current_kind = None;
            current_lines.clear();
            continue;
        }

        current_lines.push(line.to_string());
    }

    fences
}

fn extract_tell_macros(fence: &Fence) -> Vec<Snippet> {
    let source = fence.content.as_str();
    let mut snippets = Vec::new();
    let mut offset = 0usize;

    while let Some(idx) = source[offset..].find("tell!") {
        let macro_start = offset + idx;
        let after_bang = macro_start + "tell!".len();
        let brace_rel = source[after_bang..].find('{');
        let Some(brace_rel) = brace_rel else {
            break;
        };
        let open_brace = after_bang + brace_rel;
        let Some(close_brace) = match_brace(source, open_brace) else {
            break;
        };
        let body = source[open_brace + 1..close_brace].to_string();
        snippets.push(Snippet {
            kind: SnippetKind::TellMacro,
            start_line: fence.start_line + line_offset(source, macro_start),
            content: strip_common_indent(&body),
        });
        offset = close_brace + 1;
    }

    snippets
}

fn extract_parser_strings(fence: &Fence) -> Vec<Snippet> {
    let source = fence.content.as_str();
    if !source.contains("parse_choreography_str") {
        return Vec::new();
    }

    let mut snippets = Vec::new();
    let bytes = source.as_bytes();
    let mut index = 0usize;

    while index < bytes.len() {
        if bytes[index] != b'r' {
            index += 1;
            continue;
        }

        let mut hash_count = 0usize;
        let mut probe = index + 1;
        while probe < bytes.len() && bytes[probe] == b'#' {
            hash_count += 1;
            probe += 1;
        }
        if probe >= bytes.len() || bytes[probe] != b'"' {
            index += 1;
            continue;
        }

        let content_start = probe + 1;
        let mut end = content_start;
        let mut found = None;
        while end < bytes.len() {
            if bytes[end] == b'"'
                && bytes
                    .get(end + 1..end + 1 + hash_count)
                    .map(|suffix| suffix.iter().all(|b| *b == b'#'))
                    .unwrap_or(false)
            {
                found = Some(end);
                break;
            }
            end += 1;
        }
        let Some(content_end) = found else {
            break;
        };

        let candidate = &source[content_start..content_end];
        if looks_like_dsl(candidate) {
            snippets.push(Snippet {
                kind: SnippetKind::ParserString,
                start_line: fence.start_line + line_offset(source, index),
                content: strip_common_indent(candidate.trim()),
            });
        }

        index = content_end + 1 + hash_count;
    }

    snippets
}

fn match_brace(source: &str, open_brace: usize) -> Option<usize> {
    let bytes = source.as_bytes();
    let mut depth = 0usize;
    let mut index = open_brace;
    let mut in_string = false;
    let mut escaped = false;

    while index < bytes.len() {
        let byte = bytes[index];
        if in_string {
            if escaped {
                escaped = false;
            } else if byte == b'\\' {
                escaped = true;
            } else if byte == b'"' {
                in_string = false;
            }
            index += 1;
            continue;
        }

        match byte {
            b'"' => in_string = true,
            b'{' => depth += 1,
            b'}' => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return Some(index);
                }
            }
            _ => {}
        }

        index += 1;
    }

    None
}

fn line_offset(source: &str, offset: usize) -> usize {
    source[..offset].bytes().filter(|b| *b == b'\n').count()
}

fn looks_like_dsl(candidate: &str) -> bool {
    let trimmed = candidate.trim_start();
    [
        "protocol ",
        "module ",
        "effect ",
        "profile ",
        "agreement_profile ",
        "proof_bundle ",
        "role_set ",
        "cluster ",
        "ring ",
        "mesh ",
    ]
    .iter()
    .any(|prefix| trimmed.starts_with(prefix))
}

fn parse_source_snippet(
    snippet: &Snippet,
) -> Result<(), telltale_runtime::compiler::parser::ParseError> {
    match snippet.kind {
        SnippetKind::TellFence => parse_tell_fence(&snippet.content),
        SnippetKind::TellMacro | SnippetKind::ParserString => {
            parse_choreography_str(&snippet.content).map(|_| ())
        }
    }
}

fn parse_tell_fence(content: &str) -> Result<(), telltale_runtime::compiler::parser::ParseError> {
    let original = parse_choreography_str(content);
    if original.is_ok() {
        return Ok(());
    }

    if looks_like_top_level_decl(content) {
        if declares_protocol(content) {
            return original.map(|_| ());
        }
        let with_dummy_protocol =
            format!("{content}\n\nprotocol DocSnippet =\n  roles A, B\n  A -> B : Ping\n");
        return parse_choreography_str(&with_dummy_protocol).map(|_| ());
    }

    let wrapped = wrap_protocol_fragment(content);
    parse_choreography_str(&wrapped).map(|_| ())
}

fn looks_like_top_level_decl(content: &str) -> bool {
    let trimmed = content.trim_start();
    [
        "module ",
        "effect ",
        "type ",
        "profile ",
        "agreement_profile ",
        "proof_bundle ",
        "role_set ",
        "cluster ",
        "ring ",
        "mesh ",
        "fragment ",
        "operation ",
        "guest runtime ",
    ]
    .iter()
    .any(|prefix| trimmed.starts_with(prefix))
}

fn declares_protocol(content: &str) -> bool {
    content
        .lines()
        .any(|line| line.trim_start().starts_with("protocol "))
}

fn wrap_protocol_fragment(content: &str) -> String {
    let roles = inferred_roles(content);
    let indented = content
        .lines()
        .map(|line| {
            if line.is_empty() {
                String::new()
            } else {
                format!("  {line}")
            }
        })
        .collect::<Vec<_>>()
        .join("\n");

    let mut wrapped = format!(
        "protocol DocSnippet =\n  roles {}\n{}\n",
        roles.join(", "),
        indented
    );

    let where_block = dummy_where_block_for_calls(content);
    if !where_block.is_empty() {
        wrapped.push_str(&where_block);
    }

    wrapped
}

fn inferred_roles(content: &str) -> Vec<String> {
    let mut roles = Vec::new();
    let mut current = String::new();

    for ch in content.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            current.push(ch);
            continue;
        }
        maybe_push_role(&mut roles, &mut current);
    }
    maybe_push_role(&mut roles, &mut current);

    for required in ["A", "B"] {
        if !roles.iter().any(|existing| existing == required) {
            roles.push(required.to_string());
        }
    }

    roles
}

fn maybe_push_role(roles: &mut Vec<String>, token: &mut String) {
    if token.is_empty() {
        return;
    }
    let candidate = std::mem::take(token);
    if candidate
        .chars()
        .next()
        .map(|ch| ch.is_ascii_uppercase())
        .unwrap_or(false)
        && !roles.iter().any(|existing| existing == &candidate)
    {
        roles.push(candidate);
    }
}

fn strip_common_indent(input: &str) -> String {
    let lines = input.lines().collect::<Vec<_>>();
    let min_indent = lines
        .iter()
        .filter(|line| !line.trim().is_empty())
        .map(|line| {
            line.chars()
                .take_while(|ch| *ch == ' ' || *ch == '\t')
                .count()
        })
        .min()
        .unwrap_or(0);

    lines
        .iter()
        .map(|line| {
            if line.trim().is_empty() {
                String::new()
            } else {
                line.chars().skip(min_indent).collect::<String>()
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn dummy_where_block_for_calls(content: &str) -> String {
    let mut names = Vec::new();
    let tokens = content.split_whitespace().collect::<Vec<_>>();
    for window in tokens.windows(2) {
        if window[0] == "call" {
            let candidate = window[1]
                .trim_matches(|ch: char| !ch.is_ascii_alphanumeric() && ch != '_')
                .to_string();
            if !candidate.is_empty() && !names.iter().any(|existing| existing == &candidate) {
                names.push(candidate);
            }
        }
    }

    if names.is_empty() {
        return String::new();
    }

    let locals = names
        .into_iter()
        .map(|name| format!("  protocol {name} =\n    A -> B : Ping\n"))
        .collect::<Vec<_>>()
        .join("");

    format!("where\n{locals}")
}
