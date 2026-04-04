//! Compile-fail tests for authority validation fixtures.
use std::fs;
use std::path::{Path, PathBuf};

use telltale_runtime::compiler::parser::parse_choreography_file;

fn authority_fail_fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("ui")
        .join("authority_fail")
}

fn compile_fixture(path: &Path) -> Result<(), String> {
    let choreography = parse_choreography_file(path).map_err(|err| err.to_string())?;
    choreography.validate().map_err(|err| err.to_string())
}

fn fixture_stem(path: &Path) -> String {
    path.file_stem()
        .and_then(|stem| stem.to_str())
        .expect("fixture stem should be valid UTF-8")
        .to_string()
}

#[test]
fn authority_surface_compile_fail_fixtures() {
    let fixture_dir = authority_fail_fixture_dir();
    let mut sources: Vec<PathBuf> = fs::read_dir(&fixture_dir)
        .expect("read authority fail fixtures")
        .map(|entry| entry.expect("fixture entry").path())
        .filter(|path| path.extension().and_then(|ext| ext.to_str()) == Some("tell"))
        .collect();
    sources.sort();

    assert!(
        !sources.is_empty(),
        "expected at least one authority compile-fail fixture in {}",
        fixture_dir.display()
    );

    for source in sources {
        let case_name = fixture_stem(&source);
        let expected_path = source.with_extension("stderr");
        let expected = fs::read_to_string(&expected_path).unwrap_or_else(|err| {
            panic!(
                "read expected stderr for fixture {}: {err}",
                expected_path.display()
            )
        });

        let actual = match compile_fixture(&source) {
            Ok(()) => panic!("fixture {case_name} compiled successfully but was expected to fail"),
            Err(err) => err,
        };

        for needle in expected
            .lines()
            .map(str::trim)
            .filter(|line| !line.is_empty())
        {
            assert!(
                actual.contains(needle),
                "fixture {case_name} failed with unexpected error.\nexpected snippet: {needle}\nactual error: {actual}"
            );
        }
    }
}
