filter_bin := "scripts/filter/target/release/filter"

default:
    @just --list

build:
    lake build metalean

build-filter:
    cargo build --release --manifest-path scripts/filter/Cargo.toml

fast file:
    .lake/build/bin/metalean fast {{ file }}

slow file:
    .lake/build/bin/metalean slow {{ file }}

trace file:
    .lake/build/bin/metalean fast --verbose {{ file }}

filter input output:
    {{ filter_bin }} {{ input }} {{ output }}
