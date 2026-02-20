#!/usr/bin/env bash
# Complexity report: run Clippy so functions over the cognitive complexity
# threshold (see root clippy.toml) are reported. Exits non-zero if any are found.
set -e
cd "$(dirname "$0")/.."
exec cargo clippy --workspace "$@"
