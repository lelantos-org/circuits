pragma circom 2.2.3;

include "../../node_modules/circomlib/circuits/bitify.circom";
include "../../node_modules/circomlib/circuits/pedersen.circom";
include "tags.circom";

// HashToAssetGen: V^t = Pedersen(TAG_ASSET || asset_id_LE_64) on Baby-Jubjub.
// Derived in-circuit so prover cannot pair asset_id with a chosen generator;
// underpins per-asset balance via PerAssetPointBalance.
//
// Layout (LSB-first): bits[0..7] = TAG_ASSET, bits[8..71] = asset_id.
// 72 bits = 1 Pedersen segment (BASE[0]); ValueCommit's H uses BASE[2],
// outside this image. Num2Bits(64) enforces asset_id < 2^64.
// SDK parity: circomlibjs pedersen.hash([TAG_ASSET, ...assetId_LE_8]).
// Cost ≈ 2.1k constraints.
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
