#!/bin/bash

# unit tests only
CARGO_INCREMENTAL=0 RUSTFLAGS='-Cinstrument-coverage' LLVM_PROFILE_FILE='cargo-test-%p-%m.profraw' cargo test --release

~/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/x86_64-unknown-linux-gnu/bin/llvm-profdata merge -sparse cargo-test*.profraw -o test_coverage.profdata

~/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/x86_64-unknown-linux-gnu/bin/llvm-cov report \
    --use-color --ignore-filename-regex='/.cargo/registry' \
    --instr-profile=test_coverage.profdata \
    --object /home/michi/rust_target/release/deps/fastfibonacci-5d45d27f73ca81bd \
    --object /home/michi/rust_target/release/deps/fastfibonacci-cc98cbb91a3631bf

~/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/x86_64-unknown-linux-gnu/bin/llvm-cov show \
    --use-color --ignore-filename-regex='/.cargo/registry' \
    --instr-profile=test_coverage.profdata \
    --object /home/michi/rust_target/release/deps/fastfibonacci-5d45d27f73ca81bd \
    --object /home/michi/rust_target/release/deps/fastfibonacci-cc98cbb91a3631bf \
    --show-instantiations --show-line-counts-or-regions \
    --Xdemangler=rustfilt | less -R


grcov . --binary-path /home/michi/rust_target/release/deps/ -s . -t html --branch --ignore-not-existing --ignore '../*' --ignore "/*" -o /tmp/coverage/html 