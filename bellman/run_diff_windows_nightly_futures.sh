#!/bin/sh

RUSTFLAGS="-C target-cpu=native -C target_feature=+bmi2,+adx,+sse4.1" cargo +nightly test --release --features "asm" -- --ignored --nocapture future_based_test_large_data_different_windows
