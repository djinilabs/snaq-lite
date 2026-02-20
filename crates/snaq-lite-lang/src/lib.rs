/// Placeholder entry point for the arithmetic language.
pub fn run(_input: &str) -> Result<(), ()> {
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn placeholder() {
        assert!(run("").is_ok());
    }
}
