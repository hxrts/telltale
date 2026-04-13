use std::fs;
use std::path::Path;

use anyhow::{bail, Result};

pub fn run(repo_root: &Path) -> Result<()> {
    let docs_dir = repo_root.join("docs");
    let mut errors: Vec<String> = Vec::new();

    let mut entries: Vec<_> = walkdir::WalkDir::new(&docs_dir)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| {
            e.file_type().is_file()
                && e.path().extension().and_then(|s| s.to_str()) == Some("md")
                && !e
                    .path()
                    .to_str()
                    .map(|s| s.contains("/book/"))
                    .unwrap_or(false)
                && e.path().file_name().and_then(|s| s.to_str()) != Some("SUMMARY.md")
        })
        .collect();
    entries.sort_by(|a, b| a.path().cmp(b.path()));

    if entries.is_empty() {
        bail!("docs-prose-quality: no docs found");
    }

    for entry in &entries {
        let path = entry.path();
        let rel = path.strip_prefix(repo_root).unwrap_or(path);
        let text = fs::read_to_string(path)?;

        let mut in_code = false;
        let mut pending_explainer = false;
        let mut prose_words: usize = 0;
        let mut code_words: usize = 0;

        for (line_no, line) in text.lines().enumerate() {
            let trimmed = line.trim();

            if trimmed.starts_with("```") {
                if !in_code {
                    in_code = true;
                } else {
                    in_code = false;
                    pending_explainer = true;
                }
                continue;
            }

            if in_code {
                code_words += trimmed.split_whitespace().count();
                continue;
            }

            if trimmed.is_empty() || trimmed.starts_with('#') || trimmed.starts_with('|') {
                continue;
            }

            let words = trimmed.split_whitespace().count();

            if pending_explainer && words > 0 {
                pending_explainer = false;
            }

            // Em dash check
            if trimmed.contains("—") {
                errors.push(format!(
                    "{}:{}: em dash found (use prose rephrasing instead)",
                    rel.display(),
                    line_no + 1
                ));
            }

            // Semicolon check
            if trimmed.contains(';') && !trimmed.starts_with("```") {
                errors.push(format!(
                    "{}:{}: semicolon found (split into two sentences)",
                    rel.display(),
                    line_no + 1
                ));
            }

            prose_words += words;
        }

        if pending_explainer {
            errors.push(format!(
                "{}: code block at end of file missing trailing prose explanation",
                rel.display()
            ));
        }

        // Prose must exceed code word count for non-trivial files
        if code_words > 20 && prose_words < code_words {
            errors.push(format!(
                "{}: prose word count ({prose_words}) is less than code word count ({code_words}); add more explanatory prose",
                rel.display()
            ));
        }
    }

    if !errors.is_empty() {
        for err in &errors {
            eprintln!("{err}");
        }
        bail!("docs-prose-quality: {} violation(s)", errors.len());
    }

    println!("docs-prose-quality: ok");
    Ok(())
}
