// Layout preprocessing for the new indentation-sensitive DSL.
//
// Converts indentation into explicit braces while preserving line count to
// keep error reporting reasonably aligned.

use std::fmt;

#[derive(Debug, Clone)]
pub struct LayoutError {
    pub line: usize,
    pub column: usize,
    pub message: String,
}

impl LayoutError {
    fn new(line: usize, column: usize, message: impl Into<String>) -> Self {
        Self {
            line,
            column,
            message: message.into(),
        }
    }
}

impl fmt::Display for LayoutError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}: {}", self.line, self.column, self.message)
    }
}

#[derive(Default, Debug, Clone)]
struct ScanState {
    in_block_comment: bool,
    in_string: bool,
    escape: bool,
}

#[derive(Debug, Clone)]
struct LineScan {
    has_code: bool,
    depth_delta: i32,
    end_state: ScanState,
}

fn advance_if_in_block_comment(chars: &[char], st: &mut ScanState, idx: usize) -> Option<usize> {
    if !st.in_block_comment {
        return None;
    }
    if chars[idx] == '-' && chars.get(idx + 1).copied() == Some('}') {
        st.in_block_comment = false;
        return Some(idx + 2);
    }
    Some(idx + 1)
}

fn advance_if_in_string(chars: &[char], st: &mut ScanState, idx: usize) -> Option<usize> {
    if !st.in_string {
        return None;
    }
    if st.escape {
        st.escape = false;
        return Some(idx + 1);
    }
    match chars[idx] {
        '\\' => {
            st.escape = true;
            Some(idx + 1)
        }
        '"' => {
            st.in_string = false;
            Some(idx + 1)
        }
        _ => Some(idx + 1),
    }
}

fn update_code_and_depth(ch: char, has_code: &mut bool, depth_delta: &mut i32) {
    if !ch.is_whitespace() {
        *has_code = true;
    }
    match ch {
        '{' | '(' | '[' => *depth_delta += 1,
        '}' | ')' | ']' => *depth_delta -= 1,
        _ => {}
    }
}

fn scan_line(line: &str, state: &ScanState) -> LineScan {
    let mut st = state.clone();
    let mut has_code = false;
    let mut depth_delta = 0i32;
    let chars: Vec<char> = line.chars().collect();
    let mut i = 0usize;

    while i < chars.len() {
        if let Some(next_idx) = advance_if_in_block_comment(&chars, &mut st, i) {
            i = next_idx;
            continue;
        }
        if let Some(next_idx) = advance_if_in_string(&chars, &mut st, i) {
            i = next_idx;
            continue;
        }

        let ch = chars[i];
        let next = chars.get(i + 1).copied();
        if ch == '-' && next == Some('-') {
            break;
        }
        if ch == '{' && next == Some('-') {
            st.in_block_comment = true;
            i += 2;
            continue;
        }
        if ch == '"' {
            st.in_string = true;
            i += 1;
            continue;
        }

        update_code_and_depth(ch, &mut has_code, &mut depth_delta);
        i += 1;
    }

    LineScan {
        has_code,
        depth_delta,
        end_state: st,
    }
}

fn is_layout_continuation(line: &str) -> bool {
    let trimmed = line.trim_start();
    trimmed.starts_with("->") || trimmed.starts_with('{')
}

fn leading_indent(line: &str, line_no: usize) -> Result<usize, LayoutError> {
    let mut indent = 0usize;
    for (idx, ch) in line.chars().enumerate() {
        match ch {
            ' ' => indent += 1,
            '\t' => {
                return Err(LayoutError::new(
                    line_no,
                    idx + 1,
                    "Tabs are not allowed for indentation",
                ))
            }
            _ => break,
        }
    }
    Ok(indent)
}

fn adjust_indent_stack(
    indent_stack: &mut Vec<usize>,
    current: usize,
    line_no: usize,
    column: usize,
) -> Result<String, LayoutError> {
    let mut prefix = String::new();
    let last = *indent_stack.last().unwrap_or(&0);
    if current > last {
        indent_stack.push(current);
        prefix.push_str("{ ");
        return Ok(prefix);
    }
    if current < last {
        while current < *indent_stack.last().unwrap_or(&0) {
            indent_stack.pop();
            prefix.push_str("} ");
        }
        if current != *indent_stack.last().unwrap_or(&0) {
            return Err(LayoutError::new(
                line_no,
                column,
                "Inconsistent indentation",
            ));
        }
    }
    Ok(prefix)
}

fn close_remaining_layout_blocks(out_lines: &mut Vec<String>, open_blocks: usize) {
    if open_blocks == 0 {
        return;
    }
    let mut tail = String::new();
    for _ in 0..open_blocks {
        tail.push_str("} ");
    }
    if let Some(last) = out_lines.last_mut() {
        last.push_str(&tail);
    } else {
        out_lines.push(tail);
    }
}

/// Convert indentation into braces for parsing.
///
/// Notes:
/// - Inserts `{` before the first statement of an indented block.
/// - Inserts `}` before statements that dedent.
/// - Does not alter line count.
/// - Ignores indentation while inside explicit `{}` or `()` blocks.
pub fn preprocess_layout(input: &str) -> Result<String, LayoutError> {
    let mut out_lines: Vec<String> = Vec::new();
    let mut indent_stack: Vec<usize> = vec![0];
    let mut explicit_depth: i32 = 0;
    let mut scan_state = ScanState::default();

    for (line_idx, line) in input.lines().enumerate() {
        let line_no = line_idx + 1;
        let indent = leading_indent(line, line_no)?;

        let scan = scan_line(line, &scan_state);
        scan_state = scan.end_state.clone();

        let layout_enabled = explicit_depth == 0;
        let mut prefix = String::new();

        if layout_enabled && scan.has_code && !is_layout_continuation(line) {
            prefix.push_str(&adjust_indent_stack(
                &mut indent_stack,
                indent,
                line_no,
                indent + 1,
            )?);
        }

        let mut out_line = String::new();
        out_line.push_str(&prefix);
        out_line.push_str(line);
        out_lines.push(out_line);

        explicit_depth += scan.depth_delta;
        if explicit_depth < 0 {
            return Err(LayoutError::new(
                line_no,
                indent + 1,
                "Unmatched closing delimiter",
            ));
        }
    }

    close_remaining_layout_blocks(&mut out_lines, indent_stack.len().saturating_sub(1));

    Ok(out_lines.join("\n"))
}

#[cfg(test)]
mod tests {
    use super::preprocess_layout;

    #[test]
    fn layout_inserts_braces_for_simple_block() {
        let input = "protocol PingPong =\n  roles Alice, Bob\n  Alice -> Bob : Ping\n  Bob -> Alice : Pong\n";
        let out = preprocess_layout(input).unwrap();
        let normalized = out.split_whitespace().collect::<Vec<_>>().join(" ");
        assert!(normalized.contains("{ roles"));
        assert!(normalized.contains("Pong}"));
    }

    #[test]
    fn layout_handles_choice_and_branch_blocks() {
        let input = "protocol Test =\n  roles A, B\n  choice at A\n    | Buy ->\n        A -> B : Msg\n    | Cancel -> {}\n";
        let out = preprocess_layout(input).unwrap();
        let normalized = out.split_whitespace().collect::<Vec<_>>().join(" ");
        assert!(normalized.contains("choice at A"));
        assert!(normalized.contains("{ | Buy ->"));
        assert!(normalized.contains("{ A -> B"));
        assert!(normalized.contains("} | Cancel -> {}"));
    }

    #[test]
    fn layout_ignores_explicit_braces_blocks() {
        let input = "protocol Test =\n  roles A, B\n  par {\n    | A -> B : Msg\n    | B -> A : Ack\n  }\n";
        let out = preprocess_layout(input).unwrap();
        // Should still insert outer protocol block, but not double-open inside explicit braces.
        let normalized = out.split_whitespace().collect::<Vec<_>>().join(" ");
        assert!(normalized.contains("{ roles"));
        assert!(normalized.contains("par {"));
    }

    #[test]
    fn layout_allows_empty_blocks_only_with_braces() {
        let input = "protocol Test =\n  roles A, B\n  choice at A\n    | Cancel -> {}\n";
        let out = preprocess_layout(input).unwrap();
        let normalized = out.split_whitespace().collect::<Vec<_>>().join(" ");
        assert!(normalized.contains("Cancel -> {}"));
    }

    #[test]
    fn layout_does_not_insert_braces_inside_multiline_sender_records() {
        let input = "protocol Test =\n  roles A, B\n  A {\n    priority = high,\n  }\n    -> B : Msg\n";
        let out = preprocess_layout(input).unwrap();
        assert!(!out.contains("{     priority = high,"));
        assert!(out.contains("A {"));
        assert!(out.contains("}\n    -> B : Msg"));
    }

    #[test]
    fn layout_treats_arrow_line_as_continuation() {
        let input = "protocol Test =\n  roles A, B\n  A { priority = high }\n    -> B : Msg\n";
        let out = preprocess_layout(input).unwrap();
        assert!(!out.contains("{     -> B : Msg"));
        assert!(out.contains("-> B : Msg"));
    }
}
