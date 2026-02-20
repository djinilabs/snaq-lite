fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let expression = args.join(" ").trim().to_string();

    if expression.is_empty() {
        eprintln!("usage: snaq-lite <expression>");
        eprintln!("  e.g. snaq-lite \"1 + 2 * 3\"");
        std::process::exit(1);
    }

    match snaq_lite_lang::run(&expression) {
        Ok(result) => println!("{result}"),
        Err(e) => {
            eprintln!("error: {e}");
            std::process::exit(1);
        }
    }
}
