pragma circom 2.2.3;

include "../../node_modules/circomlib/circuits/bitify.circom";
include "../../node_modules/circomlib/circuits/pedersen.circom";
include "tags.circom";

// V^t = Pedersen(TAG_ASSET || asset_id_LE_64) on Baby-Jubjub.
// Bits LSB-first: [0..7]=TAG_ASSET, [8..71]=asset_id. Uses BASE[0]; H uses
// BASE[2] (disjoint images). Matches circomlibjs pedersen.hash([TAG_ASSET, ...assetId_LE_8]).
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
