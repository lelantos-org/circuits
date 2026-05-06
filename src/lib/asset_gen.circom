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
// TAG_ASSET byte and zero-padded to 264 bits (33 bytes) so the circomlibjs
// `pedersen.hash(buf)` mirror in the SDK can pass
// `[TAG_ASSET, ...assetId_LE_32]` byte-for-byte. Bits 64..255 of the SDK
// 32-byte buffer are zero in practice (registry keys < 2^64), so this
// matches byte-for-byte for any asset_id < 2^64.
//
// Soundness bonus: Num2Bits(64) also enforces asset_id < 2^64 in-circuit on
// every private in_asset / out_asset (previously enforced only on
// public_asset_id by the contract).
//
// Bit layout (LSB-first per Pedersen window):
//   bits[  0.. 7] = TAG_ASSET (8 bits, LSB-first)
//   bits[  8.. 71] = asset_id (64 bits, LSB-first)
//   bits[ 72..263] = 0 (zero padding to byte boundary)
//
// 264 bits → 2 Pedersen segments (BASE[0], BASE[1]); the H base used by
// ValueCommit is BASE[2], outside the image of HashToAssetGen.
//
// Constraint cost ≈ 64 (bits) + ~3.9k (Pedersen 264-bit) ≈ 4.0k per call
template HashToAssetGen() {
    signal input asset_id;
    signal output gen[2];

    component bits = Num2Bits(64);
    bits.in <== asset_id;

    var TAG = TAG_ASSET();

    component p = Pedersen(264);
    for (var i = 0; i < 8; i++) {
        p.in[i] <== (TAG >> i) & 1;
    }
    for (var i = 0; i < 64; i++) {
        p.in[8 + i] <== bits.out[i];
    }
    for (var i = 72; i < 264; i++) {
        p.in[i] <== 0;
    }

    gen[0] <== p.out[0];
    gen[1] <== p.out[1];
}
