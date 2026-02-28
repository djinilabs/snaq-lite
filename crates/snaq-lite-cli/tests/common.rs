//! Shared helpers for CLI integration tests: binary path and timeout-based runner.
//! All tests use a time-bounded run so the suite never hangs locally or in CI.

use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};

const DEFAULT_TIMEOUT_SECS: u64 = 30;

/// Write contents to path and sync to disk so a child process sees the full file.
pub fn write_and_sync(path: impl AsRef<Path>, contents: &[u8]) {
    let path = path.as_ref();
    std::fs::write(path, contents).expect("write temp file");
    let f = std::fs::File::open(path).expect("open for sync");
    f.sync_all().expect("sync temp file");
}

/// Path to the built CLI binary (set by cargo for integration tests, or derived from current exe).
pub fn cli_bin() -> PathBuf {
    if let Ok(path) = std::env::var("CARGO_BIN_EXE_snaq_lite") {
        return PathBuf::from(path);
    }
    let mut exe = std::env::current_exe().expect("current_exe");
    exe.pop();
    exe.pop();
    exe.push(format!("snaq-lite{}", std::env::consts::EXE_SUFFIX));
    exe
}

/// Run CLI with the given args and timeout. Returns (success, stdout_trimmed, stderr).
/// If the subprocess does not exit before the deadline, it is killed and this panics.
pub fn run_cli_with_timeout(args: &[&str], timeout: Duration) -> (bool, String, String) {
    let mut child = Command::new(cli_bin())
        .args(args)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn CLI");

    let mut stdout = child.stdout.take().expect("stdout piped");
    let mut stderr = child.stderr.take().expect("stderr piped");

    let (tx_out, rx_out) = mpsc::channel();
    let (tx_err, rx_err) = mpsc::channel();

    let h_stdout = thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = stdout.read_to_end(&mut buf);
        let _ = tx_out.send(buf);
    });
    let h_stderr = thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = stderr.read_to_end(&mut buf);
        let _ = tx_err.send(buf);
    });

    let deadline = Instant::now() + timeout;
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                let _ = h_stdout.join();
                let _ = h_stderr.join();
                let out_buf = rx_out.recv().unwrap_or_default();
                let err_buf = rx_err.recv().unwrap_or_default();
                let stdout_s = String::from_utf8_lossy(&out_buf).trim().to_string();
                let stderr_s = String::from_utf8_lossy(&err_buf).to_string();
                return (status.success(), stdout_s, stderr_s);
            }
            Ok(None) => {
                if Instant::now() >= deadline {
                    let _ = child.kill();
                    let _ = child.wait();
                    let _ = h_stdout.join();
                    let _ = h_stderr.join();
                    let out_buf = rx_out.recv().unwrap_or_default();
                    let err_buf = rx_err.recv().unwrap_or_default();
                    let stderr_s = String::from_utf8_lossy(&err_buf);
                    let stdout_s = String::from_utf8_lossy(&out_buf);
                    panic!(
                        "CLI subprocess did not exit within {}s (args: {:?})\nstderr:\n{}\nstdout:\n{}",
                        timeout.as_secs(),
                        args,
                        stderr_s,
                        stdout_s
                    );
                }
                thread::sleep(Duration::from_millis(100));
            }
            Err(e) => {
                let _ = child.kill();
                let _ = child.wait();
                let _ = h_stdout.join();
                let _ = h_stderr.join();
                panic!("CLI try_wait failed: {e}");
            }
        }
    }
}

/// Run CLI with the given args; uses default timeout (env SNAQ_CLI_TEST_TIMEOUT_SECS or 30s).
/// Returns (success, stdout_trimmed, stderr).
pub fn run_cli(args: &[&str]) -> (bool, String, String) {
    let secs = std::env::var("SNAQ_CLI_TEST_TIMEOUT_SECS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(DEFAULT_TIMEOUT_SECS);
    run_cli_with_timeout(args, Duration::from_secs(secs))
}
