pragma circom 2.2.3;

include "lib/spent.circom";
include "lib/output.circom";
include "lib/balance.circom";
include "lib/value_commit.circom";
include "lib/poly_eval.circom";
include "lib/clue.circom";

// MASP Pool: N_IN-input × N_OUT-output transact circuit (v1, multi-asset).
//
// Template params:
//   DEPTH  — Merkle tree depth (quaternary). Capacity = 4^DEPTH.
//   N_IN   — number of spent-note slots. Empty slots = dummies.
//   N_OUT  — number of output-note slots. Padding outputs are real value=0
//            notes addressed to self (no on-chain dummy sentinel).
//
//
// Multi-asset model (Sapling / Namada-faithful):
//   - Each note carries a private asset_id. Circuit derives a Baby-Jubjub
//     generator V^t = HashToAssetGen(asset_id) per note.
//   - Public bucket also derives V^pub = HashToAssetGen(public_asset_id)
//     in-circuit; no externally witnessed point.
//   - Per-note value commitment cv = value · V^t + rcv · H (Sapling).
//   - Balance check via Edwards point equality:
//        Σ in_cv + public_in · V^pub + Σ out_rH
//          == Σ out_cv + public_out · V^pub + Σ in_rH
//   - Distinct assets live in distinct V^t subgroups, so cross-asset balance
//     leakage is impossible without breaking the discrete log of Pedersen.
//
// Public-input compression (SnarkCompression):
//   The verifier sees only two public signals:
//     - z : Fiat-Shamir challenge supplied by the caller (contract).
//     - y : circuit-computed PolyEval evaluation, y = Σ_{k=0..19} c_k·z^k.
//   The 20 logical "public" signals below (formerly the verifier's PI vector)
//   are demoted to private witnesses; PolyEval binds all 20 to (z, y) so any
//   contract-side tamper changes y for almost every z (Schwartz–Zippel).
//
//   Coefficient slot layout (MUST match contracts/src/MASP.sol::_flatten):
//     [ 0] merkle_root
//     [ 1] nullifier[0]
//     [ 2] nullifier[1]
//     [ 3] out_cm[0]
//     [ 4] out_cm[1]
//     [ 5] public_asset_id
//     [ 6] public_in
//     [ 7] public_out
//     [ 8] in_cv[0][0]
//     [ 9] in_cv[0][1]
//     [10] in_cv[1][0]
//     [11] in_cv[1][1]
//     [12] out_cv[0][0]
//     [13] out_cv[0][1]
//     [14] out_cv[1][0]
//     [15] out_cv[1][1]
//     [16] recipient_address
//     [17] chain_id
//     [18] payer_address
//     [19] relayer_address
//   Re-ordering this list is a soundness change for the contract.
//
// Per-slot logic is delegated to `SpentNote` (lib/spent.circom) and
// `OutputNote` (lib/output.circom). This file is a wiring layer only.
//
// Properties NOT enforced in-circuit — contract MUST check before verifying:
//   - chain_id == block.chainid
//   - public_in, public_out  < 2^64
//   - public_asset_id < 2^64 (or whatever registry key range applies)
//   - recipient_address typed as address (< 2^160)
//   - nullifier[i] always inserted (no sentinel); revert on already-spent
//   - out_cm[j] always inserted into cm tree (no sentinel)
//
// Properties now also enforced in-circuit (defense-in-depth on contract):
//   - in_asset[i], out_asset[j] < 2^64 (via Num2Bits(64) inside HashToAssetGen)

template Transact(DEPTH, N_IN, N_OUT, GAMMA) {
    // ===== PUBLIC (verifier-visible) =====
    signal input  z;   // Fiat-Shamir challenge (contract-supplied).
    signal output y;   // PolyEval(20)(coeffs, z); binds the 20 logical PIs.

    // ===== LOGICAL PIs — now private witnesses, bound via PolyEval below =====
    signal input merkle_root;
    signal input nullifier[N_IN];
    signal input out_cm[N_OUT];
    signal input public_asset_id;
    signal input public_in;
    signal input public_out;
    signal input in_cv[N_IN][2];
    signal input out_cv[N_OUT][2];
    signal input recipient_address;
    signal input chain_id;
    signal input payer_address;
    signal input relayer_address;

    // ===== PRIVATE: spent notes =====
    signal input in_asset[N_IN];
    signal input in_value[N_IN];
    signal input in_pk[N_IN];
    signal input in_rho[N_IN];
    signal input in_rcm[N_IN];
    signal input in_nsk[N_IN];
    signal input in_rcv[N_IN];
    signal input in_path_elements[N_IN][DEPTH][3];
    signal input in_path_indices[N_IN][DEPTH];
    signal input in_is_dummy[N_IN];

    // ===== PRIVATE: output notes =====
    signal input out_asset[N_OUT];
    signal input out_value[N_OUT];
    signal input out_pk[N_OUT];
    signal input out_rho[N_OUT];
    signal input out_rcm[N_OUT];
    signal input out_rcv[N_OUT];

    // ===== PRIVATE: FMD clue witnesses (per output) =====
    // `out_r`  : FMD blinding scalar, fresh per output (≤ 254 bits).
    // `out_fk` : recipient flag-key array (γ Baby-Jubjub points).
    // Sender MUST set every slot to a real (r, fk) — pad/dummy outputs
    // also produce a clue; cheapest is sender's own fk + random r so
    // the resulting clue lands on sender's own subscription harmlessly.
    signal input out_r[N_OUT];
    signal input out_fk[N_OUT][GAMMA][2];

    // ===== LOGICAL PIs (private witnesses, bound via PolyEval): clue =====
    // 14-bit packed clueBits per output; first GAMMA bits constrained
    // honest, rest unconstrained but contract masks upper-2 bits zero.
    signal input out_clue_bits[N_OUT];
    // Legendre-symbol witness pair per (output, γ-slot). Computed by
    // `fmdLegendreWitness` in sdk/src/crypto/sqrt.ts. See HashToBit gadget
    // in circuits/src/lib/hash_to_bit.circom for the constraint shape.
    signal input out_legendre_bit[N_OUT][GAMMA];
    signal input out_legendre_y[N_OUT][GAMMA];
    // Output-only signals exposed by ClueCheck so PolyEval can pin them.
    signal out_clue_Rx[N_OUT];
    signal out_clue_Ry[N_OUT];

    // -------------------------------------------------------------------------
    // Spent-note slots
    // -------------------------------------------------------------------------
    component spent[N_IN];
    component in_dz = DummyZeroValue(N_IN);

    for (var i = 0; i < N_IN; i++) {
        spent[i] = SpentNote(DEPTH);
        spent[i].asset_id <== in_asset[i];
        spent[i].value    <== in_value[i];
        spent[i].pk       <== in_pk[i];
        spent[i].rho      <== in_rho[i];
        spent[i].rcm      <== in_rcm[i];
        spent[i].nsk      <== in_nsk[i];
        spent[i].rcv      <== in_rcv[i];
        spent[i].is_dummy <== in_is_dummy[i];
        for (var d = 0; d < DEPTH; d++) {
            spent[i].path_elements[d][0] <== in_path_elements[i][d][0];
            spent[i].path_elements[d][1] <== in_path_elements[i][d][1];
            spent[i].path_elements[d][2] <== in_path_elements[i][d][2];
            spent[i].path_indices[d]     <== in_path_indices[i][d];
        }
        spent[i].root      <== merkle_root;
        spent[i].nullifier <== nullifier[i];
        spent[i].cv[0]     <== in_cv[i][0];
        spent[i].cv[1]     <== in_cv[i][1];

        // Dummy ⇒ value == 0 so dummy slots add the additive identity to balance.
        in_dz.dummy[i] <== in_is_dummy[i];
        in_dz.value[i] <== in_value[i];
    }

    // -------------------------------------------------------------------------
    // Output-note slots
    // -------------------------------------------------------------------------
    component out_note[N_OUT];
    component clue[N_OUT];

    for (var j = 0; j < N_OUT; j++) {
        out_note[j] = OutputNote();
        out_note[j].asset_id <== out_asset[j];
        out_note[j].value    <== out_value[j];
        out_note[j].pk       <== out_pk[j];
        out_note[j].rho      <== out_rho[j];
        out_note[j].rcm      <== out_rcm[j];
        out_note[j].rcv      <== out_rcv[j];
        out_note[j].cm       <== out_cm[j];
        out_note[j].cv[0]    <== out_cv[j][0];
        out_note[j].cv[1]    <== out_cv[j][1];

        // FMD clue: prove R = r·G_8 and clue_bits[i] = 1 - legendre_bit(Poseidon(...)).
        // Output Rx, Ry exposed for PolyEval binding.
        clue[j] = ClueCheck(GAMMA);
        clue[j].r <== out_r[j];
        for (var gi = 0; gi < GAMMA; gi++) {
            clue[j].fk[gi][0] <== out_fk[j][gi][0];
            clue[j].fk[gi][1] <== out_fk[j][gi][1];
            clue[j].legendre_bit[gi] <== out_legendre_bit[j][gi];
            clue[j].legendre_y[gi]   <== out_legendre_y[j][gi];
        }
        clue[j].clue_bits <== out_clue_bits[j];
        out_clue_Rx[j] <== clue[j].Rx;
        out_clue_Ry[j] <== clue[j].Ry;
    }

    // -------------------------------------------------------------------------
    // Public-bucket scalar mults
    //
    // V^pub = HashToAssetGen(public_asset_id) — derived in-circuit. Output is
    // a canonical Pedersen image (on Baby-Jubjub, prime-order subgroup), so
    // no SafePoint validation is needed: identity / 2-torsion are not in the
    // image of the Pedersen hash for any 64-bit asset_id.
    //
    // ValueScalarMul consumes pre-decomposed bits, so an explicit
    // RangeCheck64 is wired here for public_in / public_out — belt-and-
    // suspenders to the on-chain `< 2^64` check.
    // -------------------------------------------------------------------------
    component pub_gen = HashToAssetGen();
    pub_gen.asset_id <== public_asset_id;

    component pub_in_rng = RangeCheck64();
    pub_in_rng.v <== public_in;

    component pub_in_mul = ValueScalarMul();
    for (var i = 0; i < 64; i++) {
        pub_in_mul.bits[i] <== pub_in_rng.bits[i];
    }
    pub_in_mul.gen[0] <== pub_gen.gen[0];
    pub_in_mul.gen[1] <== pub_gen.gen[1];

    component pub_out_rng = RangeCheck64();
    pub_out_rng.v <== public_out;

    component pub_out_mul = ValueScalarMul();
    for (var i = 0; i < 64; i++) {
        pub_out_mul.bits[i] <== pub_out_rng.bits[i];
    }
    pub_out_mul.gen[0] <== pub_gen.gen[0];
    pub_out_mul.gen[1] <== pub_gen.gen[1];

    // -------------------------------------------------------------------------
    // Per-asset point balance
    //
    // Substituting cv = value·V + rcv·H and rearranging so rcv·H cancels:
    //   Σ in_cv + public_in·V^pub + Σ out_rH  ==  Σ out_cv + public_out·V^pub + Σ in_rH
    // Equivalent to per-asset value conservation:
    //   Σ value_in·V_in + public_in·V^pub  ==  Σ value_out·V_out + public_out·V^pub
    // Distinct assets live in distinct subgroups (independent V^t points),
    // so cross-asset cancellation is infeasible.
    // -------------------------------------------------------------------------
    component bal = PerAssetPointBalance(N_IN, N_OUT);
    for (var i = 0; i < N_IN; i++) {
        bal.in_cv[i][0] <== in_cv[i][0];
        bal.in_cv[i][1] <== in_cv[i][1];
        bal.in_rH[i][0] <== spent[i].rH[0];
        bal.in_rH[i][1] <== spent[i].rH[1];
    }
    for (var j = 0; j < N_OUT; j++) {
        bal.out_cv[j][0] <== out_cv[j][0];
        bal.out_cv[j][1] <== out_cv[j][1];
        bal.out_rH[j][0] <== out_note[j].rH[0];
        bal.out_rH[j][1] <== out_note[j].rH[1];
    }
    bal.pub_in_pt[0]  <== pub_in_mul.out[0];
    bal.pub_in_pt[1]  <== pub_in_mul.out[1];
    bal.pub_out_pt[0] <== pub_out_mul.out[0];
    bal.pub_out_pt[1] <== pub_out_mul.out[1];

    // -------------------------------------------------------------------------
    // SnarkCompression: bind the 20 logical PIs to (z, y) via Horner eval.
    //
    // Coefficient ordering MUST match contracts/src/MASP.sol::_flatten().
    // -------------------------------------------------------------------------
    // 20 base PIs + 3 per output (clue Rx, Ry, bits).
    var PI_BASE = 20;
    var PI_PER_OUT = 3;
    component pe = PolyEval(PI_BASE + PI_PER_OUT * N_OUT);
    pe.coeffs[ 0] <== merkle_root;
    pe.coeffs[ 1] <== nullifier[0];
    pe.coeffs[ 2] <== nullifier[1];
    pe.coeffs[ 3] <== out_cm[0];
    pe.coeffs[ 4] <== out_cm[1];
    pe.coeffs[ 5] <== public_asset_id;
    pe.coeffs[ 6] <== public_in;
    pe.coeffs[ 7] <== public_out;
    pe.coeffs[ 8] <== in_cv[0][0];
    pe.coeffs[ 9] <== in_cv[0][1];
    pe.coeffs[10] <== in_cv[1][0];
    pe.coeffs[11] <== in_cv[1][1];
    pe.coeffs[12] <== out_cv[0][0];
    pe.coeffs[13] <== out_cv[0][1];
    pe.coeffs[14] <== out_cv[1][0];
    pe.coeffs[15] <== out_cv[1][1];
    pe.coeffs[16] <== recipient_address;
    pe.coeffs[17] <== chain_id;
    pe.coeffs[18] <== payer_address;
    pe.coeffs[19] <== relayer_address;
    for (var j = 0; j < N_OUT; j++) {
        pe.coeffs[PI_BASE + PI_PER_OUT * j + 0] <== out_clue_Rx[j];
        pe.coeffs[PI_BASE + PI_PER_OUT * j + 1] <== out_clue_Ry[j];
        pe.coeffs[PI_BASE + PI_PER_OUT * j + 2] <== out_clue_bits[j];
    }
    pe.z <== z;
    y    <== pe.y;
}

// Public signals layout (verifier IC0..IC2):
//   IC0 = constant term, IC1 binds z, IC2 binds y.
// y is a `signal output` of Transact and therefore implicitly public.
component main {
    public [ z ]
// Quaternary tree: depth 10 → 4^10 = 1,048,576 leaves (binary-equivalent depth 20).
// GAMMA = 5 matches FMD_DEFAULT_GAMMA in sdk/src/fmd.ts. Bumping requires
// new trusted setup + regenerated Verifier.sol.
} = Transact(10, 2, 2, 5);
