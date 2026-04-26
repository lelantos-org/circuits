pragma circom 2.2.3;

include "../../node_modules/circomlib/circuits/bitify.circom";
include "../../node_modules/circomlib/circuits/pedersen.circom";

// HashToAssetGen: derive a Baby-Jubjub Edwards point V^t = Pedersen(asset_id_bits)
// for a given asset_id field element.
//
// Soundness: the output (gen_x, gen_y) is a deterministic function of asset_id
// witnessed inside the circuit, so a prover cannot pair an asset_id with a
// generator chosen freely. Combined with PerAssetPointBalance this enforces
// per-asset value conservation.
//
// Implementation: 254-bit decomposition via Num2Bits_strict (rejects field
// aliases above the modulus), fed into circomlib Pedersen which selects from
// 10 fixed independent generators in 200-bit segments. asset_id ≤ 2^254 so we
// use a single Pedersen segment (consumes only BASE[0]).
//
// Constraint cost ≈ 254 (bits) + ~3.5k (Pedersen 254-bit) ≈ 3.8k per call.
template HashToAssetGen() {
    signal input asset_id;
    signal output gen[2];

    component bits = Num2Bits_strict();
    bits.in <== asset_id;

    component p = Pedersen(254);
    for (var i = 0; i < 254; i++) {
        p.in[i] <== bits.out[i];
    }

    gen[0] <== p.out[0];
    gen[1] <== p.out[1];
}
