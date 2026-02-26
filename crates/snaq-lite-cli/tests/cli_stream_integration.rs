//! Integration test: run the CLI with --stream and a temp file; assert output.

use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::Command;

fn cli_bin() -> PathBuf {
    if let Ok(path) = env::var("CARGO_BIN_EXE_snaq_lite") {
        return PathBuf::from(path);
    }
    let mut exe = env::current_exe().expect("current_exe");
    exe.pop();
    exe.pop();
    exe.push(format!("snaq-lite{}", std::env::consts::EXE_SUFFIX));
    exe
}

#[test]
fn cli_stream_from_file_prints_vector() {
    let tmp = env::temp_dir().join(format!("snaq_lite_cli_stream_test_{}", std::process::id()));
    fs::write(&tmp, "1\n2\n3\n").expect("write temp file");
    let path = tmp.to_string_lossy();

    let out = Command::new(cli_bin())
        .args(["--stream", &format!("x={path}"), "$x * 2"])
        .output()
        .expect("run CLI");

    let _ = fs::remove_file(&tmp);

    assert!(out.status.success(), "stderr: {}", String::from_utf8_lossy(&out.stderr));
    let stdout = String::from_utf8_lossy(&out.stdout).trim().to_string();
    assert!(
        stdout == "[2, 4, 6]" || stdout.contains("2") && stdout.contains("4") && stdout.contains("6"),
        "stdout: {stdout:?}"
    );
}

#[test]
#[ignore = "subprocess can hang in some environments; tabular path verified by feed_tabular_csv_to_sender_yields_map_elements"]
fn cli_stream_from_csv_prints_mapped_column() {
    let tmp = env::temp_dir().join(format!("snaq_lite_cli_csv_test_{}.csv", std::process::id()));
    let csv = "x,y\n1,2\n3,4\n";
    fs::write(&tmp, csv).expect("write temp CSV");
    let path = tmp.to_string_lossy();

    let out = Command::new(cli_bin())
        .args([
            "--stream",
            &format!("d={path}"),
            "$d.map(fn r => (r.x))",
        ])
        .output()
        .expect("run CLI");

    let _ = fs::remove_file(&tmp);

    assert!(out.status.success(), "stderr: {}", String::from_utf8_lossy(&out.stderr));
    let stdout = String::from_utf8_lossy(&out.stdout).trim().to_string();
    // CSV yields rows as maps; .map(fn r => (r.x)) extracts column x -> [1, 3]
    assert_eq!(stdout, "[1, 3]", "stdout: {stdout:?}");
}

#[test]
fn cli_stream_variance_infer_succeeds() {
    let tmp = env::temp_dir().join(format!(
        "snaq_lite_variance_infer_test_{}.txt",
        std::process::id()
    ));
    fs::write(&tmp, "10.5\n10.50\n").expect("write temp file");
    let path = tmp.to_string_lossy();

    let out = Command::new(cli_bin())
        .args([
            "--stream-variance",
            "infer",
            "--stream",
            &format!("x={path}"),
            "$x",
        ])
        .output()
        .expect("run CLI");

    let _ = fs::remove_file(&tmp);

    assert!(out.status.success(), "stderr: {}", String::from_utf8_lossy(&out.stderr));
    let stdout = String::from_utf8_lossy(&out.stdout).trim().to_string();
    assert!(stdout.contains("10.5"), "stdout should contain 10.5: {stdout:?}");
}

#[test]
fn cli_stream_duplicate_name_errors() {
    let tmp = env::temp_dir().join(format!("snaq_lite_dup_test_{}", std::process::id()));
    fs::write(&tmp, "1\n").expect("write temp file");
    let path = tmp.to_string_lossy();

    let out = Command::new(cli_bin())
        .args([
            "--stream",
            &format!("x={path}"),
            "--stream",
            &format!("x={path}"),
            "$x",
        ])
        .output()
        .expect("run CLI");

    let _ = fs::remove_file(&tmp);

    assert!(!out.status.success(), "duplicate name should fail");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("duplicate stream name"),
        "stderr should mention duplicate stream name: {stderr:?}"
    );
}
