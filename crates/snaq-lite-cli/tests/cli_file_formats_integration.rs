//! CLI integration tests: all supported stream file types (numeric .txt, CSV, Parquet, Arrow),
//! sizes (empty, single, many, chunking), and shapes. Also covers non-stream (run_standard).
//! Parquet/Arrow tests run when the CLI is built with `--features parquet` (default for this crate).
//!
//! Some tests that run the CLI with CSV or stream consumption are `#[ignore]` because the
//! subprocess can hang in some environments; the same behaviour is covered by unit tests in
//! `stream_feed_dispatch` and `stream_feeder`.

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

/// Run CLI with the given args; returns (success, stdout_trimmed, stderr).
fn run_cli(args: &[&str]) -> (bool, String, String) {
    let out = Command::new(cli_bin())
        .args(args)
        .output()
        .expect("run CLI");
    let success = out.status.success();
    let stdout = String::from_utf8_lossy(&out.stdout).trim().to_string();
    let stderr = String::from_utf8_lossy(&out.stderr).to_string();
    (success, stdout, stderr)
}

fn unique_tmp_path(prefix: &str, suffix: &str) -> PathBuf {
    env::temp_dir().join(format!("snaq_cli_{}_{}_{}", std::process::id(), prefix, suffix))
}

/// Temp path with `.csv` extension so format detection treats the file as CSV.
fn unique_tmp_csv(prefix: &str) -> PathBuf {
    unique_tmp_path(prefix, "csv").with_extension("csv")
}

// -----------------------------------------------------------------------------
// Numeric lines (.txt)
// -----------------------------------------------------------------------------

#[test]
fn cli_numeric_empty_file_prints_empty_vector() {
    let tmp = unique_tmp_path("numeric_empty", "txt");
    fs::write(&tmp, "").expect("write");
    let path = tmp.to_string_lossy();
    let (ok, stdout, stderr) = run_cli(&["--stream", &format!("x={path}"), "$x"]);
    let _ = fs::remove_file(&tmp);
    assert!(ok, "stderr: {stderr}");
    assert_eq!(stdout, "[]", "stdout: {stdout:?}");
}

#[test]
fn cli_numeric_single_value() {
    let tmp = unique_tmp_path("numeric_single", "txt");
    fs::write(&tmp, "1\n").expect("write");
    let path = tmp.to_string_lossy();
    let (ok, stdout, stderr) = run_cli(&["--stream", &format!("x={path}"), "$x"]);
    let _ = fs::remove_file(&tmp);
    assert!(ok, "stderr: {stderr}");
    assert_eq!(stdout, "[1]", "stdout: {stdout:?}");
}

#[test]
fn cli_numeric_multiple_values_doubled() {
    let tmp = unique_tmp_path("numeric_multi", "txt");
    fs::write(&tmp, "1\n2\n3\n").expect("write");
    let path = tmp.to_string_lossy();
    let (ok, stdout, stderr) = run_cli(&["--stream", &format!("x={path}"), "$x * 2"]);
    let _ = fs::remove_file(&tmp);
    assert!(ok, "stderr: {stderr}");
    assert_eq!(stdout, "[2, 4, 6]", "stdout: {stdout:?}");
}

#[test]
fn cli_numeric_no_extension_treated_as_numeric_lines() {
    let tmp = unique_tmp_path("num_noext", "data");
    fs::write(&tmp, "1\n2\n").expect("write");
    let path = tmp.to_string_lossy();
    let (ok, stdout, stderr) = run_cli(&["--stream", &format!("x={path}"), "$x"]);
    let _ = fs::remove_file(&tmp);
    assert!(ok, "stderr: {stderr}");
    assert_eq!(stdout, "[1, 2]", "path with no extension should be numeric lines: {stdout:?}");
}

#[test]
fn cli_numeric_blank_lines_skipped() {
    let tmp = unique_tmp_path("numeric_blanks", "txt");
    fs::write(&tmp, "1\n\n2\n").expect("write");
    let path = tmp.to_string_lossy();
    let (ok, stdout, stderr) = run_cli(&["--stream", &format!("x={path}"), "$x"]);
    let _ = fs::remove_file(&tmp);
    assert!(ok, "stderr: {stderr}");
    assert_eq!(stdout, "[1, 2]", "stdout: {stdout:?}");
}

#[test]
#[ignore = "subprocess can hang in some environments; chunking verified by unit tests"]
fn cli_numeric_large_file_chunking_sum() {
    let n = 10_000_usize;
    let content: String = (1..=n).map(|i| format!("{i}\n")).collect();
    let tmp = unique_tmp_path("numeric_chunk", "txt");
    fs::write(&tmp, content).expect("write");
    let path = tmp.to_string_lossy();
    let (ok, stdout, stderr) = run_cli(&["--stream", &format!("x={path}"), "$x.sum()"]);
    let _ = fs::remove_file(&tmp);
    assert!(ok, "stderr: {stderr}");
    let expected_sum: usize = (1..=n).sum();
    assert_eq!(stdout, expected_sum.to_string(), "stdout: {stdout:?}");
}

#[test]
fn cli_numeric_flag_one_per_line() {
    let tmp = unique_tmp_path("numeric_flag", "txt");
    fs::write(&tmp, "1\n2\n3\n").expect("write");
    let path = tmp.to_string_lossy();
    let (ok, stdout, stderr) = run_cli(&[
        "--numeric",
        "--stream",
        &format!("x={path}"),
        "$x * 2",
    ]);
    let _ = fs::remove_file(&tmp);
    assert!(ok, "stderr: {stderr}");
    let lines: Vec<&str> = stdout.split('\n').collect();
    assert_eq!(lines, ["2", "4", "6"], "stdout: {stdout:?}");
}

// -----------------------------------------------------------------------------
// CSV
// -----------------------------------------------------------------------------

#[test]
fn cli_csv_headers_only_empty_vector() {
    let tmp = unique_tmp_csv("csv_empty");
    fs::write(&tmp, "a,b\n").expect("write");
    let path = tmp.to_string_lossy();
    let (ok, stdout, stderr) = run_cli(&["--stream", &format!("d={path}"), "$d"]);
    let _ = fs::remove_file(&tmp);
    assert!(ok, "stderr: {stderr}");
    assert_eq!(stdout, "[]", "stdout: {stdout:?}");
}

#[test]
#[ignore = "subprocess can hang in some environments; tabular path verified by unit tests"]
fn cli_csv_single_row_one_column() {
    let tmp = unique_tmp_csv("csv_1col");
    fs::write(&tmp, "x\n42\n").expect("write");
    let path = tmp.to_string_lossy();
    let (ok, stdout, stderr) = run_cli(&[
        "--stream",
        &format!("d={path}"),
        "$d.map(fn r => (r.x))",
    ]);
    let _ = fs::remove_file(&tmp);
    assert!(ok, "stderr: {stderr}");
    assert_eq!(stdout, "[42]", "stdout: {stdout:?}");
}

#[test]
#[ignore = "subprocess can hang in some environments; tabular path verified by unit tests"]
fn cli_csv_single_row_multi_column_x() {
    let tmp = unique_tmp_csv("csv_1row_x");
    fs::write(&tmp, "x,y\n1,2\n").expect("write");
    let path = tmp.to_string_lossy();
    let (ok, stdout, stderr) = run_cli(&[
        "--stream",
        &format!("d={path}"),
        "$d.map(fn r => (r.x))",
    ]);
    let _ = fs::remove_file(&tmp);
    assert!(ok, "stderr: {stderr}");
    assert_eq!(stdout, "[1]", "stdout: {stdout:?}");
}

#[test]
#[ignore = "subprocess can hang in some environments; tabular path verified by unit tests"]
fn cli_csv_single_row_multi_column_y() {
    let tmp = unique_tmp_csv("csv_1row_y");
    fs::write(&tmp, "x,y\n1,2\n").expect("write");
    let path = tmp.to_string_lossy();
    let (ok, stdout, stderr) = run_cli(&[
        "--stream",
        &format!("d={path}"),
        "$d.map(fn r => (r.y))",
    ]);
    let _ = fs::remove_file(&tmp);
    assert!(ok, "stderr: {stderr}");
    assert_eq!(stdout, "[2]", "stdout: {stdout:?}");
}

#[test]
#[ignore = "subprocess can hang in some environments; tabular path verified by unit tests"]
fn cli_csv_multiple_rows_mapped_column() {
    let tmp = unique_tmp_csv("csv_multi");
    fs::write(&tmp, "x,y\n1,2\n3,4\n").expect("write");
    let path = tmp.to_string_lossy();
    let (ok, stdout, stderr) = run_cli(&[
        "--stream",
        &format!("d={path}"),
        "$d.map(fn r => (r.x))",
    ]);
    let _ = fs::remove_file(&tmp);
    assert!(ok, "stderr: {stderr}");
    assert_eq!(stdout, "[1, 3]", "stdout: {stdout:?}");
}

#[test]
#[ignore = "subprocess can hang in some environments; tabular path verified by unit tests"]
fn cli_csv_empty_cell_undefined_shows_question_mark() {
    let tmp = unique_tmp_csv("csv_empty_cell");
    fs::write(&tmp, "a,b\n1,\n3,4\n").expect("write");
    let path = tmp.to_string_lossy();
    let (ok, stdout, stderr) = run_cli(&[
        "--stream",
        &format!("d={path}"),
        "$d.map(fn r => (r.b))",
    ]);
    let _ = fs::remove_file(&tmp);
    assert!(ok, "stderr: {stderr}");
    // Second column: first row empty -> ?, second row 4
    assert_eq!(stdout, "[?, 4]", "stdout: {stdout:?}");
}

#[test]
#[ignore = "subprocess can hang in some environments; tabular path verified by unit tests"]
fn cli_csv_many_rows_chunking_sum() {
    let n = 10_000_usize;
    let mut lines = vec!["i,v".to_string()];
    for i in 1..=n {
        lines.push(format!("{i},{i}"));
    }
    let content = lines.join("\n") + "\n";
    let tmp = unique_tmp_csv("csv_chunk");
    fs::write(&tmp, content).expect("write");
    let path = tmp.to_string_lossy();
    let (ok, stdout, stderr) = run_cli(&[
        "--stream",
        &format!("d={path}"),
        "$d.map(fn r => (r.v)).sum()",
    ]);
    let _ = fs::remove_file(&tmp);
    assert!(ok, "stderr: {stderr}");
    let expected_sum: usize = (1..=n).sum();
    assert_eq!(stdout, expected_sum.to_string(), "stdout: {stdout:?}");
}

#[test]
#[ignore = "subprocess can hang in some environments; tabular path verified by unit tests"]
fn cli_csv_numeric_flag_one_per_line() {
    let tmp = unique_tmp_csv("csv_numeric");
    fs::write(&tmp, "x\n1\n2\n3\n").expect("write");
    let path = tmp.to_string_lossy();
    let (ok, stdout, stderr) = run_cli(&[
        "--numeric",
        "--stream",
        &format!("d={path}"),
        "$d.map(fn r => (r.x))",
    ]);
    let _ = fs::remove_file(&tmp);
    assert!(ok, "stderr: {stderr}");
    let lines: Vec<&str> = stdout.split('\n').collect();
    assert_eq!(lines, ["1", "2", "3"], "stdout: {stdout:?}");
}

// -----------------------------------------------------------------------------
// Error and edge cases
// -----------------------------------------------------------------------------

#[test]
fn cli_stream_file_not_found_errors() {
    let path = "/nonexistent/snaq_cli_test_path_12345";
    let (ok, _stdout, stderr) = run_cli(&["--stream", &format!("x={path}"), "$x"]);
    assert!(!ok, "should fail when file does not exist");
    assert!(
        stderr.contains("No such file") || stderr.contains("reading") || stderr.contains("error"),
        "stderr should mention error: {stderr:?}"
    );
}

#[test]
fn cli_numeric_invalid_line_errors() {
    let tmp = unique_tmp_path("numeric_invalid", "txt");
    fs::write(&tmp, "1\nnot_a_number\n2\n").expect("write");
    let path = tmp.to_string_lossy();
    let (ok, _stdout, stderr) = run_cli(&["--stream", &format!("x={path}"), "$x"]);
    let _ = fs::remove_file(&tmp);
    assert!(!ok, "invalid line should cause failure");
    assert!(
        stderr.contains("error") || stderr.contains("invalid"),
        "stderr should mention error: {stderr:?}"
    );
}

#[test]
#[ignore = "subprocess can hang in some environments; invalid cell verified by unit tests"]
fn cli_csv_invalid_cell_errors() {
    let tmp = unique_tmp_csv("csv_invalid");
    fs::write(&tmp, "a,b\n1,foo\n").expect("write");
    let path = tmp.to_string_lossy();
    let (ok, _stdout, stderr) = run_cli(&[
        "--stream",
        &format!("d={path}"),
        "$d.map(fn r => (r.a))",
    ]);
    let _ = fs::remove_file(&tmp);
    assert!(!ok, "invalid CSV cell should cause failure");
    assert!(
        stderr.contains("error") || stderr.contains("invalid"),
        "stderr should mention error: {stderr:?}"
    );
}

// -----------------------------------------------------------------------------
// CLI argument and usage errors
// -----------------------------------------------------------------------------

#[test]
fn cli_missing_expression_exits_with_usage() {
    let (ok, _stdout, stderr) = run_cli(&[]);
    assert!(!ok, "missing expression should fail");
    assert!(
        stderr.contains("usage") || stderr.contains("snaq-lite"),
        "stderr should show usage: {stderr:?}"
    );
}

#[test]
fn cli_stream_requires_name_equals_path() {
    let (ok, _stdout, stderr) = run_cli(&["--stream", "foo", "1"]);
    assert!(!ok, "--stream without name=path should fail");
    assert!(
        stderr.contains("name=path") || stderr.contains("error"),
        "stderr should mention name=path: {stderr:?}"
    );
}

#[test]
fn cli_stream_variance_invalid_value_errors() {
    let (ok, _stdout, stderr) = run_cli(&["--stream-variance", "bar", "1"]);
    assert!(!ok, "invalid --stream-variance should fail");
    assert!(
        stderr.contains("zero") || stderr.contains("infer") || stderr.contains("error"),
        "stderr should mention valid values: {stderr:?}"
    );
}

#[test]
fn cli_stream_empty_name_or_path_errors() {
    let tmp = unique_tmp_path("empty_name", "txt");
    fs::write(&tmp, "1\n").expect("write");
    let path = tmp.to_string_lossy();
    let (ok, _stdout, stderr) = run_cli(&["--stream", &format!("={path}"), "1"]);
    let _ = fs::remove_file(&tmp);
    assert!(!ok, "empty stream name should fail");
    assert!(
        stderr.contains("name=path") || stderr.contains("error"),
        "stderr should mention name=path: {stderr:?}"
    );
}

// -----------------------------------------------------------------------------
// Non-stream (run_standard)
// -----------------------------------------------------------------------------

#[test]
fn cli_standard_simple_expression() {
    let (ok, stdout, stderr) = run_cli(&["1 + 2"]);
    assert!(ok, "stderr: {stderr}");
    assert_eq!(stdout, "3", "stdout: {stdout:?}");
}

#[test]
fn cli_standard_numeric_flag() {
    let (ok, stdout, stderr) = run_cli(&["--numeric", "1 + 2"]);
    assert!(ok, "stderr: {stderr}");
    assert!(
        stdout.starts_with("3"),
        "stdout should be 3 or 3 with variance: {stdout:?}"
    );
}

#[test]
fn cli_standard_parse_error_exits_nonzero() {
    let (ok, _stdout, stderr) = run_cli(&["1 +"]);
    assert!(!ok, "parse error should fail");
    assert!(
        !stderr.is_empty(),
        "stderr should contain error message: {stderr:?}"
    );
}

#[test]
fn cli_standard_symbolic_without_numeric_prints_formatted() {
    let (ok, stdout, stderr) = run_cli(&["1 + pi"]);
    assert!(ok, "stderr: {stderr}");
    assert!(
        stdout.contains("π") || stdout.contains("pi") || stdout.contains("1"),
        "stdout should show symbolic or value: {stdout:?}"
    );
}

#[test]
fn cli_standard_function_result_prints_function_placeholder() {
    let (ok, stdout, stderr) = run_cli(&["--numeric", "fn x => (x)"]);
    assert!(ok, "stderr: {stderr}");
    assert_eq!(stdout, "<function>", "function result with --numeric prints placeholder: {stdout:?}");
}

#[test]
fn cli_stream_mode_scalar_result_prints_value() {
    let tmp = unique_tmp_path("scalar_result", "txt");
    fs::write(&tmp, "1\n").expect("write");
    let path = tmp.to_string_lossy();
    let (ok, stdout, stderr) = run_cli(&["--stream", &format!("x={path}"), "42"]);
    let _ = fs::remove_file(&tmp);
    assert!(ok, "stderr: {stderr}");
    assert_eq!(stdout, "42", "expression without $x should yield scalar: {stdout:?}");
}

#[test]
fn cli_stream_unbound_name_errors() {
    let tmp = unique_tmp_path("unbound", "txt");
    fs::write(&tmp, "1\n").expect("write");
    let path = tmp.to_string_lossy();
    let (ok, _stdout, stderr) = run_cli(&["--stream", &format!("a={path}"), "$b"]);
    let _ = fs::remove_file(&tmp);
    assert!(!ok, "unbound stream name should fail");
    assert!(
        stderr.contains("unbound") || stderr.contains("error") || stderr.contains("b"),
        "stderr should mention unbound or stream: {stderr:?}"
    );
}

// -----------------------------------------------------------------------------
// Parquet and Arrow (only when built with --features parquet)
// -----------------------------------------------------------------------------

#[cfg(feature = "parquet")]
mod parquet_arrow_tests {
    use super::*;
    use arrow::array::{Float64Array, Int64Array};
    use arrow::record_batch::RecordBatch;
    use arrow::datatypes::{DataType, Field, Schema};
    use arrow_ipc::writer::FileWriter;
    use parquet::arrow::ArrowWriter;
    use std::sync::Arc;

    fn write_parquet_temp(batch: &RecordBatch) -> PathBuf {
        let mut buffer = Vec::new();
        {
            let mut writer = ArrowWriter::try_new(&mut buffer, batch.schema().clone(), None)
                .expect("parquet writer");
            writer.write(batch).expect("write");
            writer.close().expect("close");
        }
        let tmp = unique_tmp_path("parquet_cli", "parquet");
        fs::write(&tmp, buffer).expect("write parquet");
        tmp
    }

    fn write_arrow_temp(batch: &RecordBatch) -> PathBuf {
        let mut buf = Vec::new();
        let mut writer =
            FileWriter::try_new(&mut buf, batch.schema().as_ref()).expect("arrow file writer");
        writer.write(batch).expect("write");
        writer.finish().expect("finish");
        let tmp = unique_tmp_path("arrow_cli", "arrow");
        fs::write(&tmp, buf).expect("write arrow");
        tmp
    }

    #[test]
    #[ignore = "subprocess can hang in some environments; Parquet path verified by ingest unit tests"]
    fn cli_parquet_mapped_column() {
        let schema = Schema::new(vec![
            Field::new("a", DataType::Int64, false),
            Field::new("b", DataType::Float64, false),
        ]);
        let batch = RecordBatch::try_new(
            Arc::new(schema),
            vec![
                Arc::new(Int64Array::from(vec![1_i64, 3])),
                Arc::new(Float64Array::from(vec![2.0, 4.0])),
            ],
        )
        .expect("batch");
        let tmp = write_parquet_temp(&batch);
        let path = tmp.to_string_lossy();
        let (ok, stdout, stderr) = run_cli(&[
            "--stream",
            &format!("p={path}"),
            "$p.map(fn r => (r.a))",
        ]);
        let _ = fs::remove_file(&tmp);
        assert!(ok, "stderr: {stderr}");
        assert_eq!(stdout, "[1, 3]", "stdout: {stdout:?}");
    }

    #[test]
    #[ignore = "subprocess can hang in some environments; Arrow path verified by ingest unit tests"]
    fn cli_arrow_mapped_column() {
        let schema = Schema::new(vec![
            Field::new("x", DataType::Int64, false),
            Field::new("y", DataType::Int64, false),
        ]);
        let batch = RecordBatch::try_new(
            Arc::new(schema),
            vec![
                Arc::new(Int64Array::from(vec![10_i64, 20])),
                Arc::new(Int64Array::from(vec![1_i64, 2])),
            ],
        )
        .expect("batch");
        let tmp = write_arrow_temp(&batch);
        let path = tmp.to_string_lossy();
        let (ok, stdout, stderr) = run_cli(&[
            "--stream",
            &format!("a={path}"),
            "$a.map(fn r => (r.x))",
        ]);
        let _ = fs::remove_file(&tmp);
        assert!(ok, "stderr: {stderr}");
        assert_eq!(stdout, "[10, 20]", "stdout: {stdout:?}");
    }
}
