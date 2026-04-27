// Build bench/public/input.json — canonical witness for the 2x2 deposit case.
// Same logic as src/scripts/gen_proof_deposit.ts up to FS-derived z, but
// stops before snarkjs proving (browser does that part).

import { writeFileSync, mkdirSync } from "fs";
import { dirname, resolve } from "path";
import { ethers } from "ethers";

import {
    Poseidon,
    Jubjub,
    MerkleTree,
    derivePk,
    toCircomInput,
    dummyInputAt,
    type Note,
    type Field,
} from "../src/test/helpers";

const DEPTH = 10;
const ASSET = 1n;
const PUBLIC_IN = 100n;
const PUBLIC_OUT = 0n;
const RECIPIENT = 0xbeefn;
const CHAIN_ID = 31337n;
const ALICE_NSK = 11n;

const BN254_R = 21888242871839275222246405745257275088548364400416034343698204186575808495617n;

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
    const types = new Array(coeffs.length).fill("uint256");
    const packed = ethers.utils.defaultAbiCoder.encode(types, coeffs.map(c => c.toString()));
    const digest = BigInt(ethers.utils.keccak256(packed));
    return digest % BN254_R;
}

async function main() {
    const P = await Poseidon.build();
    const J = await Jubjub.build();

    const tree = new MerkleTree(P, DEPTH);
    const root = tree.root();

    const dA = dummyInputAt(P, DEPTH, 0n);
    const dB = dummyInputAt(P, DEPTH, 1n);

    const aliceP: Field = derivePk(P, ALICE_NSK);
    const realOut: Note = { asset: ASSET, value: PUBLIC_IN, pk: aliceP, rho: 9n,  rcm: 10n, rcv: 11n };
    const padOut:  Note = { asset: ASSET, value: 0n,        pk: aliceP, rho: 12n, rcm: 13n, rcv: 14n };

    const pubGen = J.hashToAssetGen(ASSET);

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
    const input = { ...baseInput, z: z.toString() };

    const out = resolve(__dirname, "public", "input.json");
    mkdirSync(dirname(out), { recursive: true });
    writeFileSync(out, JSON.stringify(input, null, 2) + "\n");
    console.log(`wrote -> ${out}`);
}

main().catch(e => { console.error(e); process.exit(1); });
