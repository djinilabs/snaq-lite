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

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (numeric, expression) = if args.len() >= 2
        && (args[0] == "--numeric" || args[0] == "-n")
    {
        (true, args[1..].join(" ").trim().to_string())
    } else if args.len() == 1 && (args[0] == "--numeric" || args[0] == "-n") {
        (true, String::new())
    } else {
        (false, args.join(" ").trim().to_string())
    };

    if expression.is_empty() {
        eprintln!("usage: snaq-lite [--numeric] <expression>");
        eprintln!("  e.g. snaq-lite \"1 + 2 * 3\"");
        eprintln!("  e.g. snaq-lite --numeric \"1 + pi\"");
        std::process::exit(1);
    }

    if numeric {
        match snaq_lite_lang::run_numeric(&expression) {
            Ok(result) => {
                let value = result.value();
                let value_str = format_value(value);
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
            Err(e) => {
                eprintln!("error: {e}");
                std::process::exit(1);
            }
        }
    } else {
        match snaq_lite_lang::run_format(&expression) {
            Ok(formatted) => println!("{formatted}"),
            Err(e) => {
                eprintln!("error: {e}");
                std::process::exit(1);
            }
        }
    }
}
