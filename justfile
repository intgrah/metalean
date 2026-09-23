filter_bin := "scripts/filter/target/release/filter"

default:
    @just --list

build:
    lake build metalean

build-filter:
    cargo build --release --manifest-path scripts/filter/Cargo.toml

fast file: build
    .lake/build/bin/metalean fast {{file}}

slow file: build
    .lake/build/bin/metalean slow {{file}}

trace file: build
    .lake/build/bin/metalean fast --verbose {{file}}

filter input output: build-filter
    {{filter_bin}} {{input}} {{output}}
