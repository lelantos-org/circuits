// Baby-Jubjub, backed by circomlibjs.
//
// Field-element conversion is confined to this module. circomlibjs represents
// field elements as Uint8Array(32) in Montgomery form, which is structurally
// indistinguishable from the little-endian byte arrays used elsewhere in this
// directory: passing one where the other is expected produces a wrong point
// rather than a type error. Conversion goes through `F.e()` and `F.toObject()`,
// and the public API accepts and returns only `bigint` and `[bigint, bigint]`.
//
// No circuit uses the curve. It remains for the FMD clue reference (./fmd.ts),
// which is computed off-circuit and bound through the Fiat-Shamir challenge.

import { buildBabyjub } from "circomlibjs";
import { BABYJUB_SUBGROUP_ORDER, type Field, type Point } from "./field.js";

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
        private readonly _base8: Point,
    ) {}

    static async build(): Promise<Jubjub> {
        const bj = await buildBabyjub();
        const base8: Point = [bj.F.toObject(bj.Base8[0]), bj.F.toObject(bj.Base8[1])];
        return new Jubjub(bj, base8);
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
}
