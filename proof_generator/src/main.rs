use proof_generator::circuit::inner::*;
use proof_generator::circuit::recursive::*;
use proof_generator::circuit::param::*;

use clap::{Parser, Subcommand};

use franklin_crypto::bellman::bn256::Bn256;
use franklin_crypto::bellman::kate_commitment::*;
use franklin_crypto::bellman::plonk::better_better_cs::proof::Proof;
use franklin_crypto::bellman::plonk::better_better_cs::setup::{
    Setup, VerificationKey
};
use franklin_crypto::bellman::worker::Worker;
use franklin_crypto::bellman::plonk::better_better_cs::cs::PlonkCsWidth4WithNextStepParams;
use franklin_crypto::plonk::circuit::Width4WithCustomGates;

use std::fs::File;
use std::io::{BufReader, BufWriter, Error, Write};
use std::path::Path;

#[derive(Parser)]
#[clap(author, version, about, long_about = None)]
struct Cli {
    #[clap(subcommand)]
    command: Option<Commands>,
}

#[derive(Subcommand)]
enum Commands {
    GenInner {
        num_headers: usize,
        crs_path: String,
        output_path: String,
    },
    GenMiddle {
        num_proofs: usize,
        inner_vk_path: String,
        crs_path: String,
        output_path: String,
    },
    GenMiddleMiddle {
        num_proofs: usize,
        inner_vk_path: String,
        crs_path: String,
        output_path: String,
    },
    GenOuter {
        num_proofs: usize,
        inner_vk_path: String,
        crs_path: String,
        output_path: String,
    },
}

fn get_universal_setup_monomial_form(
    path: &Path
) -> Result<Crs<DefaultEngine, CrsForMonomialForm>, Error> {
    let setup_file = File::open(path)?;
    let mut buf_reader = BufReader::with_capacity(1 << 29, setup_file);
    Crs::<DefaultEngine, CrsForMonomialForm>::read(&mut buf_reader)
}

type InnerCircuit<'a> = EthereumBlockHeaderCircuit<DefaultEngine>;
type InnerCircuitParams = PlonkCsWidth4WithNextStepParams;
type MiddleCircuit<'a> = RecursiveAggregationCircuitBn256<'a, InnerCircuit<'a>, InnerCircuitParams>;
type MiddleCircuitParams = Width4WithCustomGates;
type MiddleMiddleCircuit<'a> = RecursiveAggregationCircuitBn256<'a, MiddleCircuit<'a>, MiddleCircuitParams>;
type MiddleMiddleCircuitParams = Width4WithCustomGates;
type OuterCircuit<'a> = RecursiveAggregationCircuitBn256<'a, MiddleMiddleCircuit<'a>, MiddleMiddleCircuitParams>;

type Inputs = ProofInputs<Bn256>;

fn main() {
    let cli = Cli::parse();

    println!("Hello, world!");

    let worker = Worker::new();

    match &cli.command {
        Some(Commands::GenInner { num_headers, crs_path, output_path }) => {
            let out_path = Path::new(output_path);
            assert!(!out_path.exists(), "output path exists");
            let out_file = File::create(&out_path).expect("unable to create output file");
            let stream = BufWriter::with_capacity(1 << 20, out_file);

            let setup = create_inner_circuit_setup(&worker, *num_headers).expect("Generate setup failed");
            let crs = get_universal_setup_monomial_form(Path::new(crs_path)).expect("Universal setup no found");
            let vk = create_inner_circuit_vk(&worker, setup, &crs).expect("Generate vk failed");
            vk.write(stream).expect("Failed to save verification key");
        }
        Some(Commands::GenMiddle { num_proofs, inner_vk_path, crs_path, output_path }) => {
            let out_path = Path::new(output_path);
            assert!(!out_path.exists(), "output path exists");
            let out_file = File::create(&out_path).expect("unable to create output file");
            let stream = BufWriter::with_capacity(1 << 20, out_file);

            let inner_vk = VerificationKey::<DefaultEngine, InnerCircuit>::read(File::open(&inner_vk_path).expect("unable to open inner vk")).expect("unable to read innver vk");
            let setup = create_recursive_circuit_setup::<InnerCircuit, InnerCircuitParams>(
                *num_proofs,
                Inputs::NUM_VARIABLES_INNER,
                &inner_vk,
                &worker,
                false, // is_inner_recursive
                true, // is_outer_recursive
            ).expect("Generation failed");
            let vk = create_recursive_circuit_vk(
                *num_proofs,
                Inputs::NUM_VARIABLES_INNER,
                &inner_vk,
                setup,
                &get_universal_setup_monomial_form(Path::new(crs_path)).expect("Universal setup no found"),
                &worker,
            ).expect("Generation failed");
            vk.write(stream).expect("Failed to save verification key");
        }
        Some(Commands::GenMiddleMiddle { num_proofs, inner_vk_path, crs_path, output_path }) => {
            let out_path = Path::new(output_path);
            assert!(!out_path.exists(), "output path exists");
            let out_file = File::create(&out_path).expect("unable to create output file");
            let stream = BufWriter::with_capacity(1 << 20, out_file);

            let inner_vk = VerificationKey::<DefaultEngine, MiddleCircuit>::read(File::open(&inner_vk_path).expect("unable to open inner vk")).expect("unable to read innver vk");
            let setup = create_recursive_circuit_setup::<MiddleCircuit, MiddleCircuitParams>(
                *num_proofs,
                Inputs::NUM_VARIABLES_RECURSIVE,
                &inner_vk,
                &worker,
                true, // is_inner_recursive
                true, // is_outer_recursive
            ).expect("Generation failed");
            let vk = create_recursive_circuit_vk(
                *num_proofs,
                Inputs::NUM_VARIABLES_RECURSIVE,
                &inner_vk,
                setup,
                &get_universal_setup_monomial_form(Path::new(crs_path)).expect("Universal setup no found"),
                &worker,
            ).expect("Generation failed");
            vk.write(stream).expect("Failed to save verification key");
        }
        Some(Commands::GenOuter { num_proofs, inner_vk_path, crs_path, output_path }) => {
            let out_path = Path::new(output_path);
            assert!(!out_path.exists(), "output path exists");
            let out_file = File::create(&out_path).expect("unable to create output file");
            let stream = BufWriter::with_capacity(1 << 20, out_file);

            let inner_vk = VerificationKey::<DefaultEngine, MiddleMiddleCircuit>::read(File::open(&inner_vk_path).expect("unable to open inner vk")).expect("unable to read innver vk");
            let setup = create_recursive_circuit_setup::<MiddleMiddleCircuit, MiddleMiddleCircuitParams>(
                *num_proofs,
                Inputs::NUM_VARIABLES_RECURSIVE,
                &inner_vk,
                &worker,
                true, // is_inner_recursive
                false, // is_outer_recursive
            ).expect("Generation failed");
            let vk = create_recursive_circuit_vk(
                *num_proofs,
                Inputs::NUM_VARIABLES_RECURSIVE,
                &inner_vk,
                setup,
                &get_universal_setup_monomial_form(Path::new(crs_path)).expect("Universal setup no found"),
                &worker,
            ).expect("Generation failed");
            vk.write(stream).expect("Failed to save verification key");
        }
        None => {}
    }
}
