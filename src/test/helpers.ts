// Helpers for building MASP test inputs that match circuits/2x2.circom.
// Mirrors the in-circuit tag scheme:
//   ivk = Poseidon(4, nsk)
//   pk  = Poseidon(3, ivk)
//   cm  = Poseidon(asset*2^64 + value, pk, rho, rcm)   // arity 4 = domain tag
//   nf  = Poseidon(2, nsk, rho)
//   merkle node = Poseidon(5, c0, c1, c2, c3)   // quaternary, TAG_MERKLE = 5
// Multi-asset (Sapling-style) value commitments:
//   gen = HashToAssetGen(asset_id) = Pedersen(asset_id_bits) on Baby-Jubjub
//   cv  = value · gen + rcv · H
// where H is Baby-Jubjub Pedersen BASE[2] (independent of HashToAssetGen
// which consumes BASE[0] + BASE[1] for a 254-bit input).

// @ts-ignore — circomlibjs ships without TS types
import { buildPoseidon, buildBabyjub, buildPedersenHash } from "circomlibjs";

export type Field = bigint;
export type Point = [Field, Field];

export interface Note {
    asset: Field;
    value: Field;
    pk: Field;
    rho: Field;
    rcm: Field;
    rcv: Field;          // Sapling-style value-commitment blinding scalar
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

export class Poseidon {
    private p: any;
    constructor(p: any) { this.p = p; }
    static async build() { return new Poseidon(await buildPoseidon()); }
    hash(xs: Field[]): Field { return BigInt(this.p.F.toObject(this.p(xs))); }
}

// Fixed independent generator H — must match value_commit.circom H_BASE.
export const H_BASE: Point = [
    5802099305472655231388284418920769829666717045250560929368476121199858275951n,
    5980429700218124965372158798884772646841287887664001482443826541541529227896n,
];

// Wraps circomlibjs babyjub + pedersenHash so the rest of the suite works in
// (bigint, bigint) Edwards coordinates instead of the toObject/fromObject dance.
export class Jubjub {
    private babyjub: any;
    private pedersen: any;

    private constructor(b: any, p: any) { this.babyjub = b; this.pedersen = p; }

    static async build(): Promise<Jubjub> {
        const babyjub = await buildBabyjub();
        const pedersen = await buildPedersenHash();
        return new Jubjub(babyjub, pedersen);
    }

    private toFE(x: Field): any { return this.babyjub.F.e(x); }
    private fromFE(fe: any): Field { return BigInt(this.babyjub.F.toObject(fe)); }

    private toPair(p: any): Point { return [this.fromFE(p[0]), this.fromFE(p[1])]; }
    private fromPair(p: Point): any { return [this.toFE(p[0]), this.toFE(p[1])]; }

    addPoint(a: Point, b: Point): Point {
        return this.toPair(this.babyjub.addPoint(this.fromPair(a), this.fromPair(b)));
    }

    mulPointEscalar(p: Point, e: Field): Point {
        // babyjub.mulPointEscalar accepts negative or zero scalars; for our use
        // value/rcv/public are always non-negative.
        return this.toPair(this.babyjub.mulPointEscalar(this.fromPair(p), e));
    }

    // 32-byte little-endian encoding of `x` (must be < 2^256).
    private toLeBytes(x: Field): Uint8Array {
        const out = new Uint8Array(32);
        let v = x;
        for (let i = 0; i < 32; i++) { out[i] = Number(v & 0xffn); v >>= 8n; }
        return out;
    }

    // Match the in-circuit HashToAssetGen exactly: Num2Bits_strict(asset_id)
    // (254 bits LSB-first) → circomlib Pedersen(254). circomlib Pedersen
    // pads the final segment with zero bits, so a 32-byte LE buffer with
    // bits 254..255 = 0 (asset_id < 2^254) reproduces the identical bit
    // stream that the circuit consumes.
    hashToAssetGen(assetId: Field): Point {
        if (assetId >= 1n << 254n) {
            throw new Error("asset_id must be < 2^254 for HashToAssetGen parity");
        }
        const buf = this.toLeBytes(assetId);
        const packed = this.pedersen.hash(buf);
        const unpacked = this.babyjub.unpackPoint(packed);
        return this.toPair(unpacked);
    }

    // cv = value · gen + rcv · H
    valueCommit(value: Field, gen: Point, rcv: Field): Point {
        const vt = this.mulPointEscalar(gen, value);
        const rH = this.mulPointEscalar(H_BASE, rcv);
        return this.addPoint(vt, rH);
    }
}

export function deriveIvk(P: Poseidon, nsk: Field): Field {
    return P.hash([4n, nsk]);
}

export function derivePk(P: Poseidon, nsk: Field): Field {
    return derivePkFromIvk(P, deriveIvk(P, nsk));
}

export function derivePkFromIvk(P: Poseidon, ivk: Field): Field {
    return P.hash([3n, ivk]);
}

export function commit(P: Poseidon, n: Note): Field {
    const packedAv = n.asset * (1n << 64n) + n.value;
    return P.hash([packedAv, n.pk, n.rho, n.rcm]);
}

export function nullifier(P: Poseidon, nsk: Field, rho: Field): Field {
    return P.hash([2n, nsk, rho]);
}

// Quaternary sparse Merkle tree.
const TAG_MERKLE: Field = 5n;
const ARITY = 4;

export class MerkleTree {
    depth: number;
    P: Poseidon;
    leaves: Field[] = [];
    zeros: Field[] = [];

    constructor(P: Poseidon, depth: number) {
        this.P = P;
        this.depth = depth;
        let z: Field = 0n;
        for (let i = 0; i < depth; i++) {
            this.zeros.push(z);
            z = P.hash([TAG_MERKLE, z, z, z, z]);
        }
        this.zeros.push(z);
    }

    insert(leaf: Field): number {
        const idx = this.leaves.length;
        this.leaves.push(leaf);
        return idx;
    }

    private nodeAt(level: number, index: number): Field {
        if (level === 0) {
            return this.leaves[index] ?? 0n;
        }
        const subtreeSize = ARITY ** level;
        const start = index * subtreeSize;
        if (start >= this.leaves.length) return this.zeros[level];
        const c0 = this.nodeAt(level - 1, index * ARITY + 0);
        const c1 = this.nodeAt(level - 1, index * ARITY + 1);
        const c2 = this.nodeAt(level - 1, index * ARITY + 2);
        const c3 = this.nodeAt(level - 1, index * ARITY + 3);
        return this.P.hash([TAG_MERKLE, c0, c1, c2, c3]);
    }

    root(): Field { return this.nodeAt(this.depth, 0); }

    proof(leafIndex: number): { pathElements: Field[][]; pathIndices: number[] } {
        const pathElements: Field[][] = [];
        const pathIndices: number[] = [];
        let idx = leafIndex;
        for (let level = 0; level < this.depth; level++) {
            const selfPos = idx % ARITY;
            const parentIdx = Math.floor(idx / ARITY);
            const siblings: Field[] = [];
            for (let k = 0; k < ARITY; k++) {
                if (k === selfPos) continue;
                siblings.push(this.nodeAt(level, parentIdx * ARITY + k));
            }
            pathElements.push(siblings);
            pathIndices.push(selfPos);
            idx = parentIdx;
        }
        return { pathElements, pathIndices };
    }
}

export interface BuildOpts {
    publicAssetId: Field;
    publicAssetGen?: Point;       // defaults to J.hashToAssetGen(publicAssetId)
    publicIn: Field;
    publicOut: Field;
    inputs: SpentNote[];          // length 2
    outputs: Note[];              // length 2 — all real (use value=0 for padding)
    merkleRoot: Field;
    recipientAddress?: Field;
    chainId?: Field;
}

// Build the full circom witness object. cv values are computed off-circuit
// from (value, asset, rcv) and emitted as the public `in_cv` / `out_cv`.
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

    return {
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

// Padding output: real value=0 note, real Poseidon cm. Asset MUST be non-zero
// (circuit rejects asset_id == 0 unconditionally — ghost-note defense). The cm
// is inserted into the on-chain tree and is indistinguishable from any other
// output. `asset` defaults to 1; pass any registered asset_id to taste.
export function dummyOutput(asset: Field = 1n): Note {
    return { asset, value: 0n, pk: 0n, rho: 0n, rcm: 0n, rcv: 0n };
}

// Dummy spent slot. is_dummy=1 bypasses Merkle membership and pk check inside
// the circuit (private flag — invisible on chain). The public nullifier is
// computed normally as Poseidon(TAG_NF, nsk, rho) from prover-chosen private
// (nsk, rho); pick fresh `rho` to keep nf distinct from prior dummies and from
// any real spend. There is NO on-chain sentinel — the contract inserts every
// nullifier exactly like a real spend.
export function dummyInputAt(P: Poseidon, depth: number, rho: Field = 0n): SpentNote {
    const nsk = 0n;
    const TAG_NF = 2n;
    const nf = P.hash([TAG_NF, nsk, rho]);
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
