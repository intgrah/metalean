filter_bin := "scripts/filter/target/release/filter"

default:
    @just --list

build:
    lake build metalean metalean-fast

build-filter:
    cargo build --release --manifest-path scripts/filter/Cargo.toml

fast file: build
    .lake/build/bin/metalean-fast {{file}}

slow file: build
    .lake/build/bin/metalean {{file}}

trace file: build
    METALEAN_TRACE=1 .lake/build/bin/metalean-fast {{file}}

filter input output: build-filter
    {{filter_bin}} {{input}} {{output}}
