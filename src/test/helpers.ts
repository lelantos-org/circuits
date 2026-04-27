// Helpers for building MASP test inputs that match circuits/2x2.circom.
//
// Cryptographic primitives (Poseidon, Jubjub, derive, commit, nullifier,
// MerkleTree, H_BASE, hashToAssetGen, valueCommit) live in
// `@lelantos/sdk` (../../../sdk/src/crypto). This file imports them so
// circuit witnesses are byte-identical to the wallet's view of the same
// objects. Do NOT re-implement them here — that would silently divert
// the SDK and circuit and is exactly the bug we are preventing.

import {
    Poseidon,
    Jubjub,
    H_BASE,
    deriveIvk,
    derivePk,
    derivePkFromIvk,
    buildNoteCommitment,
    buildNullifier,
    MerkleTree,
    type Field,
    type Point,
} from "../../../sdk/src/crypto/index";

export { Poseidon, Jubjub, H_BASE, deriveIvk, derivePk, derivePkFromIvk, MerkleTree };
export type { Field, Point };

// Legacy names — circuit tests historically used `commit` / `nullifier`.
// Keep them as aliases over the SDK so existing tests stay green without
// touching their imports.
export function commit(P: Poseidon, n: Note): Field {
    return buildNoteCommitment(P, n);
}
export function nullifier(P: Poseidon, nsk: Field, rho: Field): Field {
    return buildNullifier(P, nsk, rho);
}

export interface Note {
    asset: Field;
    value: Field;
    pk: Field;
    rho: Field;
    rcm: Field;
    rcv: Field;
}

export interface SpentNote extends Note {
    nsk: Field;
    cm: Field;
    nf: Field;
    leafIndex: number;
    pathElements: Field[][];
    pathIndices: number[];
    isDummy: boolean;
}

export interface BuildOpts {
    publicAssetId: Field;
    publicAssetGen?: Point;
    publicIn: Field;
    publicOut: Field;
    inputs: SpentNote[];
    outputs: Note[];
    merkleRoot: Field;
    recipientAddress?: Field;
    chainId?: Field;
    // SnarkCompression Fiat-Shamir challenge. Tests default to 1n; in prod
    // the contract derives this from a transcript over the 20 logical PIs.
    z?: Field;
}

export function toCircomInput(P: Poseidon, J: Jubjub, opts: BuildOpts): Record<string, string | string[] | string[][] | string[][][]> {
    const { inputs, outputs, publicAssetId, publicIn, publicOut, merkleRoot } = opts;
    const N_IN = 2;
    const N_OUT = 2;
    if (inputs.length !== N_IN) throw new Error("need 2 inputs");
    if (outputs.length !== N_OUT) throw new Error("need 2 outputs");

    const recipientAddress = opts.recipientAddress ?? 0n;
    const chainId = opts.chainId ?? 0n;
    const pubGen = opts.publicAssetGen ?? J.hashToAssetGen(publicAssetId);

    const out_cm = outputs.map(o => commit(P, o));

    const in_cv: Point[] = inputs.map(i => J.valueCommit(i.value, J.hashToAssetGen(i.asset), i.rcv));
    const out_cv: Point[] = outputs.map(o => J.valueCommit(o.value, J.hashToAssetGen(o.asset), o.rcv));

    const z = opts.z ?? 1n;

    return {
        z: z.toString(),
        merkle_root: merkleRoot.toString(),
        nullifier: inputs.map(i => i.nf.toString()),
        out_cm: out_cm.map(c => c.toString()),
        public_asset_id: publicAssetId.toString(),
        pub_asset_gen_x: pubGen[0].toString(),
        pub_asset_gen_y: pubGen[1].toString(),
        public_in: publicIn.toString(),
        public_out: publicOut.toString(),
        in_cv: in_cv.map(p => [p[0].toString(), p[1].toString()]),
        out_cv: out_cv.map(p => [p[0].toString(), p[1].toString()]),
        recipient_address: recipientAddress.toString(),
        chain_id: chainId.toString(),

        in_asset: inputs.map(i => i.asset.toString()),
        in_value: inputs.map(i => i.value.toString()),
        in_pk: inputs.map(i => i.pk.toString()),
        in_rho: inputs.map(i => i.rho.toString()),
        in_rcm: inputs.map(i => i.rcm.toString()),
        in_nsk: inputs.map(i => i.nsk.toString()),
        in_rcv: inputs.map(i => i.rcv.toString()),
        in_path_elements: inputs.map(i => i.pathElements.map(level => level.map(e => e.toString()))),
        in_path_indices: inputs.map(i => i.pathIndices.map(b => b.toString())),
        in_is_dummy: inputs.map(i => i.isDummy ? "1" : "0"),

        out_asset: outputs.map(o => o.asset.toString()),
        out_value: outputs.map(o => o.value.toString()),
        out_pk: outputs.map(o => o.pk.toString()),
        out_rho: outputs.map(o => o.rho.toString()),
        out_rcm: outputs.map(o => o.rcm.toString()),
        out_rcv: outputs.map(o => o.rcv.toString()),
    };
}

export function dummyOutput(asset: Field = 1n): Note {
    return { asset, value: 0n, pk: 0n, rho: 0n, rcm: 0n, rcv: 0n };
}

// Dummy spent slot. is_dummy=1 bypasses Merkle membership and pk check inside
// the circuit. nf is computed normally as Poseidon(TAG_NF, 0, rho); pick a
// fresh `rho` to keep nf distinct from prior dummies and any real spend.
export function dummyInputAt(P: Poseidon, depth: number, rho: Field = 0n): SpentNote {
    const nsk = 0n;
    const nf = buildNullifier(P, nsk, rho);
    const pathElements: Field[][] = [];
    for (let i = 0; i < depth; i++) pathElements.push([0n, 0n, 0n]);
    return {
        asset: 0n, value: 0n, pk: 0n, rho, rcm: 0n, rcv: 0n, nsk,
        cm: 0n,
        nf,
        leafIndex: 0,
        pathElements,
        pathIndices: new Array(depth).fill(0),
        isDummy: true,
    };
}
