// Field <-> byte conversion and bit packing. FMD clue bits are LSB-first within
// each byte on the wire.

import type { Field } from "./field.js";

export const FIELD_BYTES = 32;

export function toLeBytes(x: Field, len = FIELD_BYTES): Uint8Array {
    const out = new Uint8Array(len);
    let v = x;
    for (let i = 0; i < len; i++) {
        out[i] = Number(v & 0xffn);
        v >>= 8n;
    }
    if (v !== 0n) throw new Error(`field exceeds ${len} bytes`);
    return out;
}

/** Big-endian, for the `uint256[]` ABI encoding in `fiatShamirZ`. */
export function toBeBytes32(x: Field): Uint8Array {
    const out = new Uint8Array(32);
    let v = x;
    for (let i = 31; i >= 0; i--) {
        out[i] = Number(v & 0xffn);
        v >>= 8n;
    }
    if (v !== 0n) throw new Error("field exceeds 32 bytes");
    return out;
}

/** Bit `i` of a packed byte array, LSB-first within each byte. */
export function bitAt(packed: Uint8Array, i: number): number {
    return (packed[i >> 3] >> (i & 7)) & 1;
}

/** Packs LSB-first within each byte. */
export function packBits(bits: number[] | Uint8Array): Uint8Array {
    const out = new Uint8Array(Math.ceil(bits.length / 8));
    for (let i = 0; i < bits.length; i++) {
        if (bits[i]) out[i >> 3] |= 1 << (i & 7);
    }
    return out;
}

export function unpackBits(packed: Uint8Array, count: number): number[] {
    const out: number[] = new Array(count);
    for (let i = 0; i < count; i++) out[i] = bitAt(packed, i);
    return out;
}
