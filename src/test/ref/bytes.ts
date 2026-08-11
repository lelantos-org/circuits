// Field <-> byte conversion and bit packing.
//
// Bit order is significant: the Pedersen asset-generator input is LSB-first
// within each byte (src/lib/asset_gen.circom), as are the FMD clue bits on the
// wire. `toBeBytes32` is big-endian for ABI encoding only.

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

export function fromLeBytes(b: Uint8Array): Field {
    let v = 0n;
    for (let i = b.length - 1; i >= 0; i--) v = (v << 8n) | BigInt(b[i]);
    return v;
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

/** Read bit `i` (LSB-first) from a packed byte array. Returns 0 or 1. */
export function bitAt(packed: Uint8Array, i: number): number {
    return (packed[i >> 3] >> (i & 7)) & 1;
}

/** Pack `bits` (each 0 or 1) LSB-first into `ceil(bits.length / 8)` bytes. */
export function packBits(bits: number[] | Uint8Array): Uint8Array {
    const out = new Uint8Array(Math.ceil(bits.length / 8));
    for (let i = 0; i < bits.length; i++) {
        if (bits[i]) out[i >> 3] |= 1 << (i & 7);
    }
    return out;
}

/** Unpack the first `count` bits (LSB-first) from a packed byte array. */
export function unpackBits(packed: Uint8Array, count: number): number[] {
    const out: number[] = new Array(count);
    for (let i = 0; i < count; i++) out[i] = bitAt(packed, i);
    return out;
}
