#!/bin/bash
set -e

(cd proof_generator && cargo build -r)

mkdir output
cd output

../proof_generator/target/release/proof_generator setup-inner 16 inner-1-setup
../proof_generator/target/release/proof_generator gen-inner inner-1-setup ../setup_2^23.key inner-1-vk

../proof_generator/target/release/proof_generator setup-middle 1 inner-1-vk middle-1-setup
../proof_generator/target/release/proof_generator gen-middle 1 inner-1-vk middle-1-setup ../setup_2^23.key middle-1-vk

for layer in `seq 1 16`; do
    prev=$(($layer - 1))
    prev_vk=middle-$((1 << $prev))-vk
    middle_prefix=middle-$((1 << $layer))
    outer_prefix=outer-$((1 << $layer))
    echo $prev_vk $middle_prefix $outer_prefix
    ../proof_generator/target/release/proof_generator setup-middle-middle 2 $prev_vk $middle_prefix-setup
    ../proof_generator/target/release/proof_generator gen-middle-middle 2 $prev_vk $middle_prefix-setup ../setup_2^23.key $middle_prefix-vk

    ../proof_generator/target/release/proof_generator setup-outer 1 $middle_prefix-vk $outer_prefix-setup
    ../proof_generator/target/release/proof_generator gen-outer 1 $middle_prefix-vk $outer_prefix-setup ../setup_2^23.key $outer_prefix-vk
done
