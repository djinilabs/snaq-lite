//! Integration test: run the CLI with --stream and a temp file; assert output.
//! All tests use a timeout when running the CLI subprocess (see common module).

mod common;

use std::fs;

#[test]
fn cli_stream_from_file_prints_vector() {
    let tmp = std::env::temp_dir().join(format!("snaq_lite_cli_stream_test_{}", std::process::id()));
    common::write_and_sync(&tmp, "1\n2\n3\n".as_bytes());
    let path = tmp.to_string_lossy();

    let (ok, stdout, stderr) = common::run_cli(&["--stream", &format!("x={path}"), "$x * 2"]);

    let _ = fs::remove_file(&tmp);

    assert!(ok, "stderr: {stderr}");
    assert!(
        stdout == "[2, 4, 6]" || stdout.contains("2") && stdout.contains("4") && stdout.contains("6"),
        "stdout: {stdout:?}"
    );
}

#[test]
fn cli_stream_from_csv_prints_mapped_column() {
    let tmp = std::env::temp_dir().join(format!("snaq_lite_cli_csv_test_{}.csv", std::process::id()));
    let csv = "x,y\n1,2\n3,4\n";
    common::write_and_sync(&tmp, csv.as_bytes());
    let path = tmp.to_string_lossy();

    let (ok, stdout, stderr) = common::run_cli(&[
        "--stream",
        &format!("d={path}"),
        "$d.map(fn r => (r.x))",
    ]);

    let _ = fs::remove_file(&tmp);

    assert!(ok, "stderr: {stderr}");
    // CSV yields rows as maps; .map(fn r => (r.x)) extracts column x -> [1, 3]
    assert_eq!(stdout, "[1, 3]", "stdout: {stdout:?}");
}

#[test]
fn cli_stream_variance_infer_succeeds() {
    let tmp = std::env::temp_dir().join(format!(
        "snaq_lite_variance_infer_test_{}.txt",
        std::process::id()
    ));
    common::write_and_sync(&tmp, "10.5\n10.50\n".as_bytes());
    let path = tmp.to_string_lossy();

    let (ok, stdout, stderr) = common::run_cli(&[
        "--stream-variance",
        "infer",
        "--stream",
        &format!("x={path}"),
        "$x",
    ]);

    let _ = fs::remove_file(&tmp);

    assert!(ok, "stderr: {stderr}");
    assert!(stdout.contains("10.5"), "stdout should contain 10.5: {stdout:?}");
}

#[test]
fn cli_stream_duplicate_name_errors() {
    let tmp = std::env::temp_dir().join(format!("snaq_lite_dup_test_{}", std::process::id()));
    common::write_and_sync(&tmp, "1\n".as_bytes());
    let path = tmp.to_string_lossy();

    let (ok, _stdout, stderr) = common::run_cli(&[
        "--stream",
        &format!("x={path}"),
        "--stream",
        &format!("x={path}"),
        "$x",
    ]);

    let _ = fs::remove_file(&tmp);

    assert!(!ok, "duplicate name should fail");
    assert!(
        stderr.contains("duplicate stream name"),
        "stderr should mention duplicate stream name: {stderr:?}"
    );
}
