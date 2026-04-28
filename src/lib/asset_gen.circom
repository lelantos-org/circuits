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
// Implementation: 254-bit decomposition via Num2Bits_strict (rejects field
// aliases above the modulus), prepended with a TAG_ASSET byte and zero-padded
// to 264 bits (33 bytes) so the circomlibjs `pedersen.hash(buf)` mirror in
// the SDK can pass `[TAG_ASSET, ...assetId_LE_32]` byte-for-byte.
//
// Bit layout (LSB-first per Pedersen window):
//   bits[  0.. 7] = TAG_ASSET (8 bits, LSB-first)
//   bits[  8..261] = asset_id (254 bits, LSB-first; high 2 bits of byte 31
//                              forced to 0 by Num2Bits_strict + asset_id < 2^254)
//   bits[262..263] = 0 (padding to byte boundary)
//
// 264 bits → 2 Pedersen segments (BASE[0], BASE[1]); the H base used by
// ValueCommit is BASE[2], outside the image of HashToAssetGen.
//
// Constraint cost ≈ 254 (bits) + ~3.9k (Pedersen 264-bit) ≈ 4.2k per call.
template HashToAssetGen() {
    signal input asset_id;
    signal output gen[2];

    component bits = Num2Bits_strict();
    bits.in <== asset_id;

    var TAG = TAG_ASSET();

    component p = Pedersen(264);
    for (var i = 0; i < 8; i++) {
        p.in[i] <== (TAG >> i) & 1;
    }
    for (var i = 0; i < 254; i++) {
        p.in[8 + i] <== bits.out[i];
    }
    p.in[262] <== 0;
    p.in[263] <== 0;

    gen[0] <== p.out[0];
    gen[1] <== p.out[1];
}
