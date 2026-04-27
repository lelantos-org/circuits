// Emit proof_deposit.json fixture for contracts/test/MASP.t.sol.
//
// Generates a Groth16 proof for the deposit case:
//   - 2 dummy inputs, 1 real output (publicIn=100), 1 padding output
//   - asset_id=1 (must be present in asset_registry.json)
//   - recipient = 0x000…beef, chainId = 31337
//
// SnarkCompression: the verifier sees only (z, y) where
//   z = keccak256(abi.encode(uint256[20] flatten)) mod BN254_R   // Fiat-Shamir
//   y = Σ flatten[k] · z^k mod BN254_R                           // Horner
// We compute z off-chain identically to how the contract MUST derive it.
//
// Re-run after any circuit / zkey / asset-registry change.

import { writeFileSync, mkdirSync } from "fs";
import { dirname, resolve } from "path";
import { ethers } from "ethers";
// snarkjs has no published TS types
// @ts-ignore
import { groth16 } from "snarkjs";

import {
    Poseidon,
    Jubjub,
    MerkleTree,
    derivePk,
    toCircomInput,
    dummyInputAt,
    type Note,
    type Field,
} from "../test/helpers";

const DEPTH = 10;
const ASSET = 1n;            // must match asset_registry id
const PUBLIC_IN = 100n;
const PUBLIC_OUT = 0n;
const RECIPIENT = 0xbeefn;   // matches old fixture
const CHAIN_ID = 31337n;
const ALICE_NSK = 11n;

// BN254 scalar field (Groth16 curve).
const BN254_R = 21888242871839275222246405745257275088548364400416034343698204186575808495617n;

const WASM = resolve(__dirname, "..", "..", "build", "2x2_js", "2x2.wasm");
const ZKEY = resolve(__dirname, "..", "..", "build", "2x2_final.zkey");

// Slot order MUST match contracts/src/MASP.sol::_flatten() byte-for-byte.
function flatten(input: Record<string, any>): bigint[] {
    return [
        BigInt(input.merkle_root),
        BigInt(input.nullifier[0]),
        BigInt(input.nullifier[1]),
        BigInt(input.out_cm[0]),
        BigInt(input.out_cm[1]),
        BigInt(input.public_asset_id),
        BigInt(input.pub_asset_gen_x),
        BigInt(input.pub_asset_gen_y),
        BigInt(input.public_in),
        BigInt(input.public_out),
        BigInt(input.in_cv[0][0]),
        BigInt(input.in_cv[0][1]),
        BigInt(input.in_cv[1][0]),
        BigInt(input.in_cv[1][1]),
        BigInt(input.out_cv[0][0]),
        BigInt(input.out_cv[0][1]),
        BigInt(input.out_cv[1][0]),
        BigInt(input.out_cv[1][1]),
        BigInt(input.recipient_address),
        BigInt(input.chain_id),
    ];
}

function fiatShamirZ(coeffs: bigint[]): bigint {
    // Solidity equivalent:
    //   uint256(keccak256(abi.encode(uint256[20] coeffs))) % BN254_R
    const types = new Array(coeffs.length).fill("uint256");
    const packed = ethers.utils.defaultAbiCoder.encode(types, coeffs.map(c => c.toString()));
    const digest = BigInt(ethers.utils.keccak256(packed));
    return digest % BN254_R;
}

function hornerEval(coeffs: bigint[], z: bigint): bigint {
    // y = c[0] + c[1]·z + c[2]·z² + … (low-to-high), mod r.
    let acc = 0n;
    for (let i = coeffs.length - 1; i >= 0; i--) {
        acc = (acc * z + coeffs[i]) % BN254_R;
    }
    return acc;
}

async function main() {
    const P = await Poseidon.build();
    const J = await Jubjub.build();

    // Empty tree → root used as merkle_root in the fixture (must match
    // contracts' empty-root constant; tests assertEq() against currentRoot()).
    const tree = new MerkleTree(P, DEPTH);
    const root = tree.root();

    const dA = dummyInputAt(P, DEPTH, 0n);
    const dB = dummyInputAt(P, DEPTH, 1n);

    const aliceP: Field = derivePk(P, ALICE_NSK);
    const realOut: Note = { asset: ASSET, value: PUBLIC_IN, pk: aliceP, rho: 9n,  rcm: 10n, rcv: 11n };
    const padOut:  Note = { asset: ASSET, value: 0n,        pk: aliceP, rho: 12n, rcm: 13n, rcv: 14n };

    const pubGen = J.hashToAssetGen(ASSET);

    // First build with z=0 to compute the canonical flatten + derive z; then
    // re-pack input with the real z. (Circuit constraint y === Σ c_k·z^k means
    // any z is sound; we pick the FS-derived z so the contract can reproduce.)
    const baseInput = toCircomInput(P, J, {
        publicAssetId: ASSET,
        publicAssetGen: pubGen,
        publicIn: PUBLIC_IN,
        publicOut: PUBLIC_OUT,
        inputs: [dA, dB],
        outputs: [realOut, padOut],
        merkleRoot: root,
        recipientAddress: RECIPIENT,
        chainId: CHAIN_ID,
        z: 0n,
    });

    const coeffs = flatten(baseInput);
    const z = fiatShamirZ(coeffs);
    const yExpected = hornerEval(coeffs, z);

    const input = { ...baseInput, z: z.toString() };

    console.log("==> proving (snarkjs.groth16.fullProve)");
    const { proof, publicSignals } = await groth16.fullProve(input, WASM, ZKEY);

    // snarkjs publicSignals order: outputs first (y), then declared public
    // inputs (z). Sanity-check both against our off-circuit computation.
    if (publicSignals.length !== 2) throw new Error(`expected 2 publicSignals, got ${publicSignals.length}`);
    const yProver = BigInt(publicSignals[0]);
    const zProver = BigInt(publicSignals[1]);
    if (zProver !== z)         throw new Error(`z mismatch: prover=${zProver} expected=${z}`);
    if (yProver !== yExpected) throw new Error(`y mismatch: prover=${yProver} expected=${yExpected}`);

    const fixture = {
        chainId: CHAIN_ID.toString(),
        assetId: ASSET.toString(),
        assetGen: { x: pubGen[0].toString(), y: pubGen[1].toString() },
        publicIn: PUBLIC_IN.toString(),
        publicOut: PUBLIC_OUT.toString(),
        recipient: "0x" + RECIPIENT.toString(16).padStart(40, "0"),
        merkleRoot: root.toString(),
        z: z.toString(),
        y: yExpected.toString(),
        // 20-slot flatten in MASP._flatten order — contract recomputes z & y from this.
        coeffs: coeffs.map(c => c.toString()),
        proof: {
            a: [proof.pi_a[0], proof.pi_a[1]],
            b: [
                [proof.pi_b[0][0], proof.pi_b[0][1]],
                [proof.pi_b[1][0], proof.pi_b[1][1]],
            ],
            c: [proof.pi_c[0], proof.pi_c[1]],
        },
        // Raw snarkjs order (output before input): [y, z].
        publicSignals,
    };

    const outEnv = process.env.PROOF_DEPOSIT_OUT;
    if (!outEnv) {
        throw new Error("PROOF_DEPOSIT_OUT env var required (path to proof_deposit.json)");
    }
    const out = resolve(outEnv);
    mkdirSync(dirname(out), { recursive: true });
    writeFileSync(out, JSON.stringify(fixture, null, 2) + "\n");
    console.log(`wrote -> ${out}`);
}

main()
    .then(() => process.exit(0))   // snarkjs/ffjavascript leave bn128 workers alive — force exit.
    .catch(e => { console.error(e); process.exit(1); });
