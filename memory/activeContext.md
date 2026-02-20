# Active context

## Just completed
- **Review and improve:** Grammar `Num` rule made fallible (=>?) so integer overflow returns a parse error instead of panicking. Added `extern { type Error = String }`, test `parse_integer_overflow_is_error`, test for i64::MAX and 0 in `parse_lit`, and doc on `run()` for i64 range.

## Next steps
- None specified.
