mod stream_feeder;
mod stream_feed_dispatch;

use std::io::Write;
use std::path::PathBuf;

/// Format a numeric value for CLI output: ±∞ as Unicode ∞, -∞.
fn format_value(v: f64) -> String {
    if v == f64::INFINITY {
        "∞".to_string()
    } else if v == f64::NEG_INFINITY {
        "-∞".to_string()
    } else {
        format!("{v}")
    }
}

/// Print a single quantity for CLI numeric output (value ± variance, unit).
fn print_numeric_quantity(result: &snaq_lite_lang::Quantity) {
    let value_str = format_value(result.value());
    let variance = result.variance();
    if variance > 0.0 {
        let std_dev = variance.sqrt();
        let dev_str = if std_dev > 0.0 && !(1e-6..1e10).contains(&std_dev) {
            format!("{std_dev:.4e}")
        } else {
            format!("{std_dev}")
        };
        if result.unit().is_scalar() {
            println!("{value_str} (± {dev_str})");
        } else {
            println!("{value_str} (± {dev_str}) {}", result.unit());
        }
    } else if result.unit().is_scalar() {
        println!("{value_str}");
    } else {
        println!("{value_str} {}", result.unit());
    }
}

/// Parse CLI args into streams (name, path), numeric flag, stream variance mode, and expression.
/// Returns (streams, numeric, stream_variance, expression). Expression is empty if missing.
fn parse_args(
    args: &[String],
) -> (
    Vec<(String, String)>,
    bool,
    snaq_lite_lang::StreamVarianceMode,
    String,
) {
    let mut streams: Vec<(String, String)> = Vec::new();
    let mut numeric = false;
    let mut stream_variance = snaq_lite_lang::StreamVarianceMode::Zero;
    let mut expression = String::new();
    let mut i = 0;

    while i < args.len() {
        match args[i].as_str() {
            "-n" | "--numeric" => {
                numeric = true;
                i += 1;
            }
            "-s" | "--stream" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("error: --stream requires name=path");
                    std::process::exit(1);
                }
                let s = &args[i];
                if let Some((name, path)) = s.split_once('=') {
                    let name = name.trim();
                    let path = path.trim();
                    if name.is_empty() || path.is_empty() {
                        eprintln!("error: --stream expects name=path (non-empty name and path)");
                        std::process::exit(1);
                    }
                    streams.push((name.to_string(), path.to_string()));
                } else {
                    eprintln!("error: --stream expects name=path, got {s:?}");
                    std::process::exit(1);
                }
                i += 1;
            }
            "--stream-variance" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("error: --stream-variance requires zero or infer");
                    std::process::exit(1);
                }
                match args[i].as_str().trim().to_lowercase().as_str() {
                    "zero" => stream_variance = snaq_lite_lang::StreamVarianceMode::Zero,
                    "infer" => {
                        stream_variance = snaq_lite_lang::StreamVarianceMode::InferFromDecimalPlaces
                    }
                    other => {
                        eprintln!("error: --stream-variance must be zero or infer, got {other:?}");
                        std::process::exit(1);
                    }
                }
                i += 1;
            }
            _ => {
                expression = args[i..].join(" ").trim().to_string();
                break;
            }
        }
    }

    (streams, numeric, stream_variance, expression)
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (streams, numeric, stream_variance, expression) = parse_args(&args);

    if expression.is_empty() {
        eprintln!("usage: snaq-lite [--numeric] [--stream-variance zero|infer] [--stream name=path ...] <expression>");
        eprintln!("  e.g. snaq-lite \"1 + 2 * 3\"");
        eprintln!("  e.g. snaq-lite --numeric \"1 + pi\"");
        eprintln!("  e.g. snaq-lite --stream data=numbers.txt '$data * 2'");
        eprintln!("  e.g. snaq-lite --stream-variance infer --stream d=data.csv '$d.map(fn r => (r.x))'");
        std::process::exit(1);
    }

    if streams.is_empty() {
        run_standard(&expression, numeric);
        return;
    }

    run_stream_mode(&expression, numeric, &streams, stream_variance);
}

/// Current behavior when no --stream is used.
fn run_standard(expression: &str, numeric: bool) {
    if numeric {
        match snaq_lite_lang::run(expression) {
            Ok(snaq_lite_lang::Value::Function(_)) => println!("<function>"),
            Ok(snaq_lite_lang::Value::Vector(_)) | Ok(snaq_lite_lang::Value::Undefined) => {
                if let Ok(formatted) = snaq_lite_lang::run_format(expression) {
                    println!("{formatted}");
                } else {
                    eprintln!("error: failed to format result");
                    std::process::exit(1);
                }
            }
            Ok(v) => {
                let sym_reg = snaq_lite_lang::SymbolRegistry::default_registry();
                match v.to_quantity(&sym_reg) {
                    Ok(result) => print_numeric_quantity(&result),
                    Err(_) => {
                        if let Ok(formatted) = snaq_lite_lang::run_format(expression) {
                            println!("{formatted}");
                        } else {
                            eprintln!("error: failed to format result");
                            std::process::exit(1);
                        }
                    }
                }
            }
            Err(e) => {
                let msg = snaq_lite_lang::format_run_error_with_source(&e, Some(expression));
                eprintln!("error: {msg}");
                let _ = std::io::stderr().flush();
                std::process::exit(1);
            }
        }
    } else {
        match snaq_lite_lang::run_format(expression) {
            Ok(formatted) => println!("{formatted}"),
            Err(e) => {
                let msg = snaq_lite_lang::format_run_error_with_source(&e, Some(expression));
                eprintln!("error: {msg}");
                let _ = std::io::stderr().flush();
                std::process::exit(1);
            }
        }
    }
}

/// Run with stream inputs: create channels, run_with_stream_inputs, feed files, consume output.
fn run_stream_mode(
    expression: &str,
    numeric: bool,
    streams: &[(String, String)],
    variance_mode: snaq_lite_lang::StreamVarianceMode,
) {
    use futures::stream::StreamExt;

    let registry = snaq_lite_lang::default_si_registry();
    let mut stream_input_map = std::collections::HashMap::new();
    let mut feeders: Vec<(PathBuf, futures::channel::mpsc::UnboundedSender<snaq_lite_lang::Chunk>)> =
        Vec::new();

    for (name, path) in streams {
        if stream_input_map.contains_key(name) {
            eprintln!("error: duplicate stream name: {name}");
            std::process::exit(1);
        }
        let (id, sender) = snaq_lite_lang::create_stream_input();
        stream_input_map.insert(name.clone(), id);
        feeders.push((PathBuf::from(path), sender));
    }

    // Spawn feeders before run_with_stream_inputs so that when value() calls
    // collect_vector_stream (e.g. for $d.map(...)), data is already being sent.
    let n = feeders.len();
    let (ready_tx, ready_rx) = std::sync::mpsc::channel();
    let mut join_handles = Vec::with_capacity(n);
    for (path, sender) in feeders {
        let mode = variance_mode;
        let ready_tx = ready_tx.clone();
        let handle = std::thread::spawn(move || {
            let on_ready = Some(Box::new(move || {
                let _ = ready_tx.send(());
            }) as Box<dyn FnOnce() + Send>);
            if let Err(e) = stream_feed_dispatch::feed_stream_file_to_sender(
                &path,
                sender,
                mode,
                on_ready,
            ) {
                eprintln!("error: reading {}: {}", path.display(), e);
                std::process::exit(1);
            }
        });
        join_handles.push(handle);
    }

    for _ in 0..n {
        let _ = ready_rx.recv();
    }

    let (value, db) = match snaq_lite_lang::run_with_stream_inputs(
        expression,
        &registry,
        stream_input_map,
    ) {
        Ok(x) => x,
        Err(e) => {
            let _ = join_handles.into_iter().map(std::thread::JoinHandle::join);
            let msg = snaq_lite_lang::format_run_error_with_source(&e, Some(expression));
            eprintln!("error: {msg}");
            let _ = std::io::stderr().flush();
            std::process::exit(1);
        }
    };

    for h in join_handles {
        if h.join().is_err() {
            eprintln!("error: stream feeder thread panicked");
            std::process::exit(1);
        }
    }

    match &value {
        snaq_lite_lang::Value::Vector(v) => {
            let results: Vec<_> = if let Some(evaluated) = v.inner.clone().take_evaluated_results()
            {
                evaluated
            } else {
                let stream = snaq_lite_lang::vector_into_stream(&db, v.inner.clone());
                futures::executor::block_on(async move { stream.collect().await })
            };

            let mut parts = Vec::with_capacity(results.len());
            for r in results {
                match r {
                    Ok(Some(val)) => {
                        let s = match &val {
                            snaq_lite_lang::Value::Undefined => "?".to_string(),
                            _ => match snaq_lite_lang::format_value_for_display(&db, &val) {
                                Ok(ss) => ss,
                                Err(e) => {
                                    eprintln!("error: {e}");
                                    std::process::exit(1);
                                }
                            },
                        };
                        parts.push(s);
                    }
                    Ok(None) => parts.push("?".to_string()),
                    Err(e) => {
                        eprintln!("error: {e}");
                        std::process::exit(1);
                    }
                }
            }

            if numeric {
                for part in &parts {
                    if part == "?" {
                        println!("?");
                    } else {
                        println!("{part}");
                    }
                }
            } else {
                println!("[{}]", parts.join(", "));
            }
        }
        _ => {
            if numeric {
                let sym_reg = snaq_lite_lang::SymbolRegistry::default_registry();
                if let Ok(result) = value.to_quantity(&sym_reg) {
                    print_numeric_quantity(&result);
                } else {
                    match snaq_lite_lang::format_value_for_display(&db, &value) {
                        Ok(formatted) => println!("{formatted}"),
                        Err(e) => {
                            eprintln!("error: {e}");
                            std::process::exit(1);
                        }
                    }
                }
            } else {
                match snaq_lite_lang::format_value_for_display(&db, &value) {
                    Ok(formatted) => println!("{formatted}"),
                    Err(e) => {
                        eprintln!("error: {e}");
                        std::process::exit(1);
                    }
                }
            }
        }
    }
}
