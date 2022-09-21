use franklin_crypto::bellman::pairing::Engine;
use franklin_crypto::bellman::pairing::bn256::Bn256;
use franklin_crypto::bellman::pairing::ff::ScalarEngine;
use franklin_crypto::bellman::plonk::commitments::transcript::Prng;
use franklin_crypto::bellman::plonk::commitments::transcript::keccak_transcript::RollingKeccakTranscript;
use franklin_crypto::plonk::circuit::bigint::RnsParameters;
use franklin_crypto::rescue::bn256::Bn256RescueParams;
use franklin_crypto::rescue::rescue_transcript::RescueTranscriptForRNS;
use once_cell::sync::Lazy;

pub type DefaultEngine = Bn256;
pub type InnerTranscript<'a, E> = RescueTranscriptForRNS<'a, E>;
pub type OuterTranscript<E> = RollingKeccakTranscript<<E as ScalarEngine>::Fr>;

pub static RNS_PARAMETERS: Lazy<RnsParameters::<DefaultEngine, <DefaultEngine as Engine>::Fq>> = Lazy::new(|| {
    let mut rns_params = RnsParameters::<DefaultEngine, <DefaultEngine as Engine>::Fq>::new_for_field(68, 110, 4);
    // FIXME
    rns_params.set_prefer_single_limb_allocation(true);
    rns_params
});

pub static INNER_RESCUE_PARAMETERS: Lazy<Bn256RescueParams> = Lazy::new(|| {
    let rescue_params = Bn256RescueParams::new_checked_2_into_1();
    rescue_params
});

pub fn inner_transcript_params<'a>() -> Option< <InnerTranscript<'a, DefaultEngine> as Prng<<DefaultEngine as ScalarEngine>::Fr> >:: InitializationParameters> {
    Some((&*INNER_RESCUE_PARAMETERS, &*RNS_PARAMETERS))
}

pub fn outer_transcript_params() -> Option< <OuterTranscript<DefaultEngine> as Prng<<DefaultEngine as ScalarEngine>::Fr> >:: InitializationParameters> {
    None
}
