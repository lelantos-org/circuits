pragma circom 2.2.3;

include "../../node_modules/circomlib/circuits/bitify.circom";
include "../../node_modules/circomlib/circuits/pedersen.circom";
include "tags.circom";

// HashToAssetGen: derive a Baby-Jubjub Edwards point V^t = Pedersen(asset_id_bits)
// for a given asset_id field element.
//
// Soundness: the output (gen_x, gen_y) is a deterministic function of asset_id
// witnessed inside the circuit, so a prover cannot pair an asset_id with a
// generator chosen freely. Combined with PerAssetPointBalance this enforces
// per-asset value conservation.
//
// Implementation: 64-bit decomposition via Num2Bits(64), prepended with a
// TAG_ASSET byte → 72-bit (9-byte) Pedersen input. The SDK mirror passes
// `[TAG_ASSET, ...assetId_LE_8]` to circomlibjs `pedersen.hash(buf)` for
// byte-for-byte parity.
//
// A 264-bit zero-padded input would yield the identical point (zero bits
// contribute the identity in additive Pedersen) but spans 2 Pedersen segments
// instead of 1.
//
// Side-effect: Num2Bits(64) enforces asset_id < 2^64 in-circuit on every
// private in_asset / out_asset; contract enforces the same bound on
// public_asset_id.
//
// Bit layout (LSB-first per Pedersen window):
//   bits[ 0.. 7] = TAG_ASSET (8 bits, LSB-first)
//   bits[ 8..71] = asset_id  (64 bits, LSB-first)
//
// 72 bits → 1 Pedersen segment (BASE[0]); the H base used by ValueCommit is
// BASE[2], outside the image of HashToAssetGen.
//
// Constraint cost ≈ 64 (bits) + ~2.0k (Pedersen 72-bit) ≈ 2.1k per call
template HashToAssetGen() {
    signal input asset_id;
    signal output gen[2];

    component bits = Num2Bits(64);
    bits.in <== asset_id;

    var TAG = TAG_ASSET();

    component p = Pedersen(72);
    for (var i = 0; i < 8; i++) {
        p.in[i] <== (TAG >> i) & 1;
    }
    for (var i = 0; i < 64; i++) {
        p.in[8 + i] <== bits.out[i];
    }

    gen[0] <== p.out[0];
    gen[1] <== p.out[1];
}
