// Baby-Jubjub, backed by circomlibjs.
//
// Field-element conversion is confined to this module. circomlibjs represents
// field elements as Uint8Array(32) in Montgomery form, which is structurally
// indistinguishable from the little-endian byte arrays used elsewhere in this
// directory: passing one where the other is expected produces a wrong point
// rather than a type error. Conversion goes through `F.e()` and `F.toObject()`,
// and the public API accepts and returns only `bigint` and `[bigint, bigint]`.
//
// Scalars are not reduced, matching the circuit: `MulH` is Num2Bits(253) +
// EscalarMulFix and `ValueScalarMul` is EscalarMulAny(64) over raw bits.
// Reduction would diverge for points outside the prime-order subgroup. The
// bit widths those Num2Bits calls enforce are asserted instead.

import { buildBabyjub, buildPedersenHash } from "circomlibjs";
import { BABYJUB_SUBGROUP_ORDER, POW_2_64, type Field, type Point } from "./field.js";
import { toLeBytes } from "./bytes.js";
import { TAG_ASSET } from "./tags.js";

/**
 * Fixed independent generator for value-commitment blinding:
 *   cv = value·gen + rcv·H
 * Must equal H_BASE_X() / H_BASE_Y() in src/lib/value_commit.circom.
 */
export const H_BASE: Point = [
    5802099305472655231388284418920769829666717045250560929368476121199858275951n,
    5980429700218124965372158798884772646841287887664001482443826541541529227896n,
];

/** Width of the `rcv` scalar, mirroring `RCV_BITS()` in src/lib/value_commit.circom. */
const MAX_BLINDER_BITS = 252n;

function assertBigint(x: unknown, what: string): asserts x is bigint {
    if (typeof x !== "bigint") {
        throw new TypeError(`Jubjub: ${what} must be a bigint, got ${typeof x}`);
    }
}

function assertPoint(p: Point, what: string): void {
    if (!Array.isArray(p) || p.length !== 2) {
        throw new TypeError(`Jubjub: ${what} must be [bigint, bigint]`);
    }
    assertBigint(p[0], `${what}.x`);
    assertBigint(p[1], `${what}.y`);
}

export class Jubjub {
    private constructor(
        private readonly bj: any,
        private readonly pedersen: any,
        private readonly _base8: Point,
    ) {}

    static async build(): Promise<Jubjub> {
        const [bj, pedersen] = await Promise.all([buildBabyjub(), buildPedersenHash()]);
        const base8: Point = [bj.F.toObject(bj.Base8[0]), bj.F.toObject(bj.Base8[1])];
        return new Jubjub(bj, pedersen, base8);
    }

    get base8(): Point {
        return this._base8;
    }

    /** Prime-order subgroup order. */
    get order(): Field {
        return BABYJUB_SUBGROUP_ORDER;
    }

    // ===== boundary: bigint <-> Montgomery =====

    private toInternal(p: Point): [Uint8Array, Uint8Array] {
        return [this.bj.F.e(p[0]), this.bj.F.e(p[1])];
    }

    private fromInternal(p: [Uint8Array, Uint8Array]): Point {
        return [this.bj.F.toObject(p[0]), this.bj.F.toObject(p[1])];
    }

    // ===== group operations =====

    addPoint(a: Point, b: Point): Point {
        assertPoint(a, "addPoint a");
        assertPoint(b, "addPoint b");
        return this.fromInternal(this.bj.addPoint(this.toInternal(a), this.toInternal(b)));
    }

    mulPointEscalar(p: Point, scalar: Field): Point {
        assertPoint(p, "mulPointEscalar p");
        assertBigint(scalar, "mulPointEscalar scalar");
        return this.fromInternal(this.bj.mulPointEscalar(this.toInternal(p), scalar));
    }

    inSubgroup(p: Point): boolean {
        assertPoint(p, "inSubgroup p");
        return this.bj.inSubgroup(this.toInternal(p));
    }

    packPoint(p: Point): Uint8Array {
        assertPoint(p, "packPoint p");
        return new Uint8Array(this.bj.packPoint(this.toInternal(p)));
    }

    unpackPoint(buf: Uint8Array): Point | null {
        const out = this.bj.unpackPoint(buf);
        return out ? this.fromInternal(out) : null;
    }

    // ===== circuit gadget mirrors =====

    /**
     * Per-asset generator V^t = Pedersen(TAG_ASSET || asset_id_LE_64).
     * Mirrors HashToAssetGen in src/lib/asset_gen.circom, whose header states
     * the equivalence to circomlibjs `pedersen.hash([TAG_ASSET, ...assetId_LE_8])`.
     *
     * The buffer is exactly 9 bytes and circomlibjs reads bits LSB-first
     * within each byte, which is what lines up with the circom's
     * `(TAG >> i) & 1` followed by `Num2Bits(64).out[i]`.
     */
    hashToAssetGen(assetId: Field): Point {
        assertBigint(assetId, "hashToAssetGen assetId");
        if (assetId >= POW_2_64) {
            throw new Error("asset_id must be < 2^64 for HashToAssetGen parity");
        }
        const buf = new Uint8Array(9);
        buf[0] = Number(TAG_ASSET);
        buf.set(toLeBytes(assetId, 8), 1);
        const pt = this.bj.unpackPoint(this.pedersen.hash(buf));
        if (!pt) throw new Error("hashToAssetGen: pedersen output did not unpack");
        return this.fromInternal(pt);
    }

    /**
     * cv = value·gen + rcv·H.
     *
     * Bounds mirror the circuit: `value` goes through EscalarMulAny(64) and
     * `rcv` through Num2Bits(253), so anything wider would be a witness the
     * circuit cannot represent.
     */
    valueCommit(value: Field, assetGen: Point, rcv: Field): Point {
        assertBigint(value, "valueCommit value");
        assertBigint(rcv, "valueCommit rcv");
        if (value >= POW_2_64) throw new Error("valueCommit: value must be < 2^64");
        if (rcv >= 1n << MAX_BLINDER_BITS) throw new Error("valueCommit: rcv must be < 2^252");
        return this.addPoint(
            this.mulPointEscalar(assetGen, value),
            this.mulPointEscalar(H_BASE, rcv),
        );
    }
}
