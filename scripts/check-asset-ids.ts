// Asset-id separation gate for the deposit path.
//
// `tree_update_batch.circom` pins a deposit leaf with a single Pedersen
// equality:
//
//     cv_dep[k] == leaf_public_in[k] · V^leaf_asset[k] + rcv[k] · H
//
// That is the only thing tying a deposit leaf to an (asset, value) pair: `cms[k]`
// is depositor-chosen and carries no transact proof. The equality is binding
// only if `value · V^asset` determines `(asset, value)`, which does not hold in
// general, because `HashToAssetGen` is circomlib `Pedersen` over a 72-bit
// message, which fits one segment and so reduces to
//
//     V^a = m(a) · BASE0
//
// for a publicly computable integer m(a) of about 2^85 (`src/README.md` §5).
// Two ids therefore collide whenever
//
//     v · m(a) == v' · m(a')
//
// has a solution with both values inside the circuit's 64-bit range. Values and
// multipliers are far below the subgroup order, so this is an integer equation,
// not a modular one, and the minimal solution is
//
//     v = |m(a')| / g,   v' = |m(a)| / g,   g = gcd(|m(a)|, |m(a')|)
//
// with every other solution a multiple of it. A pair is safe exactly when that
// minimal solution already overflows 2^64. Signs matter: `v · m(a)` and
// `v' · m(a')` agree in sign for positive values, so opposite-signed multipliers
// never collide.
//
// A colliding pair lets a depositor pay `v` units of the cheap asset while
// committing `cm` to `(a', v')`, then spend the leaf later as the expensive
// one: `SpentNote` recomputes the same `cv_dep` and sees a well-formed note.
// Both ids must be registered for this to be reachable, which is what this gate
// checks. `AssetRegistry.addAsset` takes an arbitrary caller-chosen `uint64`,
// so nothing else constrains the id space.
//
// Run over every id the deployment intends to register, BEFORE registering it.
// Small sequential ids are separated by a wide margin; the risk lies in
// hash-like or otherwise unstructured ids.
//
// Usage:
//   check-asset-ids.ts <id>...            ids as decimal or 0x-hex
//   check-asset-ids.ts --file <path>      newline/comma-separated ids
//   check-asset-ids.ts --self-test        check the gate against a known pair

import { readFileSync } from "node:fs";
import { pathToFileURL } from "node:url";

import { Jubjub, TAG_ASSET, BABYJUB_SUBGROUP_ORDER, POW_2_64, type Point } from "../test/helpers.js";

/** Signed 4-bit windows, the encoding circomlib's `Window4` applies per window. */
const WINDOW_BITS = 4;
const WINDOW_STRIDE = 1n << 5n; // each window advances the base by 2^5 in the multiplier
const MESSAGE_BITS = 72; // 8 tag bits + 64 asset bits
const WINDOWS = MESSAGE_BITS / WINDOW_BITS;

/**
 * The integer `m` with `V^a == m · BASE0`.
 *
 * circomlib's `Segment` accumulates `Window4` outputs, each contributing
 * `(1 + b0 + 2·b1 + 4·b2) · (b3 ? -1 : +1)` against a base advanced by 2^5 per
 * window. `verifyModel` below checks this against the compiled gadget, so a
 * circomlib change surfaces here instead of weakening the bound unnoticed.
 */
export function assetMultiplier(assetId: bigint): bigint {
    const bits: number[] = [];
    for (let i = 0n; i < 8n; i++) bits.push(Number((TAG_ASSET >> i) & 1n));
    for (let i = 0n; i < 64n; i++) bits.push(Number((assetId >> i) & 1n));

    let m = 0n;
    let stride = 1n;
    for (let w = 0; w < WINDOWS; w++) {
        const b = bits.slice(WINDOW_BITS * w, WINDOW_BITS * w + WINDOW_BITS);
        const magnitude = BigInt(1 + b[0] + 2 * b[1] + 4 * b[2]);
        m += (b[3] ? -magnitude : magnitude) * stride;
        stride *= WINDOW_STRIDE;
    }
    return m;
}

function gcd(a: bigint, b: bigint): bigint {
    let [x, y] = [a < 0n ? -a : a, b < 0n ? -b : b];
    while (y) [x, y] = [y, x % y];
    return x;
}

function modInverse(a: bigint, n: bigint): bigint {
    let [old_r, r] = [((a % n) + n) % n, n];
    let [old_s, s] = [1n, 0n];
    while (r !== 0n) {
        const q = old_r / r;
        [old_r, r] = [r, old_r - q * r];
        [old_s, s] = [s, old_s - q * s];
    }
    if (old_r !== 1n) throw new Error("modInverse: not invertible");
    return ((old_s % n) + n) % n;
}

/**
 * Assert `assetMultiplier` agrees with the compiled gadget on every id in play.
 *
 * BASE0 is recovered from `V^0`, whose multiplier the model also supplies, so
 * the check is a round trip through circomlibjs rather than a restated constant.
 */
function verifyModel(J: Jubjub, ids: bigint[]): void {
    const ell = BABYJUB_SUBGROUP_ORDER;
    const mod = (x: bigint) => ((x % ell) + ell) % ell;
    const base0 = J.mulPointEscalar(J.hashToAssetGen(0n), modInverse(assetMultiplier(0n), ell));

    const same = (p: Point, q: Point) => p[0] === q[0] && p[1] === q[1];
    for (const id of ids) {
        const modelled = J.mulPointEscalar(base0, mod(assetMultiplier(id)));
        if (!same(modelled, J.hashToAssetGen(id))) {
            throw new Error(
                `assetMultiplier disagrees with HashToAssetGen at id ${id}. ` +
                `The Pedersen encoding this gate assumes has changed; the bound below is void.`,
            );
        }
    }
}

export interface PairVerdict {
    a: bigint;
    b: bigint;
    /** Minimal colliding values, or null when the multipliers differ in sign. */
    values: { va: bigint; vb: bigint } | null;
    /** True when both minimal values fit the circuit's 64-bit range. */
    colliding: boolean;
}

/** Smallest `(v_a, v_b)` with `v_a · m(a) == v_b · m(b)`, and whether both fit. */
export function classifyPair(a: bigint, b: bigint): PairVerdict {
    const ma = assetMultiplier(a);
    const mb = assetMultiplier(b);
    if (ma === 0n || mb === 0n || (ma > 0n) !== (mb > 0n)) {
        return { a, b, values: null, colliding: false };
    }
    const [absA, absB] = [ma < 0n ? -ma : ma, mb < 0n ? -mb : mb];
    const g = gcd(absA, absB);
    const va = absB / g;
    const vb = absA / g;
    return { a, b, values: { va, vb }, colliding: va < POW_2_64 && vb < POW_2_64 };
}

function parseId(raw: string): bigint {
    const t = raw.trim();
    const v = t.startsWith("0x") || t.startsWith("0X") ? BigInt(t) : BigInt(t);
    if (v < 0n || v >= POW_2_64) throw new Error(`asset id out of uint64 range: ${t}`);
    return v;
}

async function main(argv: string[]): Promise<number> {
    const selfTest = argv.includes("--self-test");
    const fileFlag = argv.indexOf("--file");

    let ids: bigint[];
    if (selfTest) {
        // A pair with a shared divisor between the two multipliers. Both ids are
        // valid uint64 and both minimal values are under 2^64, so the gate must
        // flag it.
        ids = [0x067f8028c470047cn, 0x067f8028c472818bn];
    } else if (fileFlag !== -1) {
        const raw = readFileSync(argv[fileFlag + 1], "utf8");
        ids = raw.split(/[\s,]+/).filter(Boolean).map(parseId);
    } else {
        const rest = argv.filter(a => !a.startsWith("--"));
        if (rest.length < 2) {
            console.error("usage: check-asset-ids.ts <id>... | --file <path> | --self-test");
            return 2;
        }
        ids = rest.map(parseId);
    }

    const unique = [...new Set(ids)];
    if (unique.length < 2) {
        console.log("fewer than two distinct ids — nothing to compare");
        return 0;
    }

    const J = await Jubjub.build();
    verifyModel(J, unique);
    console.log(`model verified against HashToAssetGen for ${unique.length} ids\n`);

    const bad: PairVerdict[] = [];
    let closest = { ratio: Infinity, v: null as PairVerdict | null };

    for (let i = 0; i < unique.length; i++) {
        for (let j = i + 1; j < unique.length; j++) {
            const v = classifyPair(unique[i], unique[j]);
            if (v.colliding) bad.push(v);
            if (v.values) {
                // How far the minimal solution sits below the 64-bit ceiling.
                const worst = v.values.va > v.values.vb ? v.values.va : v.values.vb;
                const ratio = Number(POW_2_64) / Number(worst);
                if (ratio < closest.ratio) closest = { ratio, v };
            }
        }
    }

    for (const v of bad) {
        console.error(
            `COLLIDING  ${v.a} (0x${v.a.toString(16)})  and  ${v.b} (0x${v.b.toString(16)})\n` +
            `           ${v.values!.va} units of the first commit to the same point as\n` +
            `           ${v.values!.vb} units of the second. A deposit of one can be spent\n` +
            `           as the other; do not register both.`,
        );
    }

    if (closest.v) {
        const worst = closest.v.values!.va > closest.v.values!.vb
            ? closest.v.values!.va
            : closest.v.values!.vb;
        console.log(
            `tightest pair: ${closest.v.a} / ${closest.v.b} — smallest colliding value ` +
            `${worst}, ${(Math.log2(Number(worst)) - 64).toFixed(1)} bits above the 2^64 ceiling`,
        );
    }

    if (selfTest) {
        const ok = bad.length === 1;
        console.log(ok
            ? "\nself-test ok: the known colliding pair is flagged"
            : `\nSELF-TEST FAILED: expected exactly 1 colliding pair, got ${bad.length}`);
        return ok ? 0 : 1;
    }

    console.log(bad.length ? "\nasset id check FAILED" : "\nasset id check ok");
    return bad.length ? 1 : 0;
}

// Only when run as a command: `test/check_asset_ids.test.ts` imports
// `assetMultiplier` and `classifyPair` from here, and an unguarded call would
// run the CLI, exiting the process during test collection.
if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
    process.exit(await main(process.argv.slice(2)));
}
