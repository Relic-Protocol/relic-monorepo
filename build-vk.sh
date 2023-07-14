#!/bin/bash
set -e

(cd proof_generator && cargo build -r)

mkdir output
cd output

../proof_generator/target/release/proof_generator gen-inner 16 ../setup_2^23.key vk-inner
../proof_generator/target/release/proof_generator gen-middle 2 vk-inner ../setup_2^23.key vk-middle-2

for layer in `seq 2 16`; do
    prev=$(($layer - 1))
    prev_vk=vk-middle-$((1 << $prev))
    middle_prefix=middle-$((1 << $layer))
    echo $prev_vk $middle_prefix
    ../proof_generator/target/release/proof_generator gen-middle-middle 2 $prev_vk ../setup_2^23.key vk-$middle_prefix
done

for layer in `seq 9 16`; do
    middle_prefix=middle-$((1 << $layer))
    outer_prefix=outer-$((1 << $layer))

    echo $outer_prefix
    ../proof_generator/target/release/proof_generator gen-outer 1 vk-$middle_prefix ../setup_2^23.key vk-$outer_prefix
done

sha256sum vk-* > expected-sha256.sum
