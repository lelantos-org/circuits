// Decides whether two R1CS files are the same constraint system up to a
// renaming of intermediate signals and a reordering of constraints. A mutant
// isomorphic to the original proves the same statement, so no test can reject
// it.
//
// The constant, the outputs and the inputs are the circuit's interface and
// stay themselves; only intermediates may be renamed. Interface signals are
// identified by label, not by index: circom gives no wire to an input no
// constraint reads, so the same input can sit at different indices in the two
// files.
//
// Method: colour refinement proposes the renaming, and an exact comparison of
// the renamed constraints confirms it. A `true` is therefore a proof. A `false`
// means no renaming was found; the search does not undo a wrong choice among
// interchangeable signals, and does not try rescaling a constraint or a signal.
//
// Runs as a script, so the search stays off the campaign's event loop:
//
//   node test/mutation/isomorphic.ts <a.r1cs> <b.r1cs>     prints {"isomorphic": bool, "reason": string}

import { pathToFileURL } from "url";

// r1csfile ships without TS types
// @ts-ignore
import { readR1cs } from "r1csfile";
// @ts-ignore
import { F1Field } from "ffjavascript";

/** One linear combination: parallel arrays of signal index and interned coefficient. */
interface Lc {
    vars: Int32Array;
    coefs: Int32Array;
}

interface System {
    nVars: number;
    /**
     * Labels up to this one are the interface. circom numbers labels as the
     * constant, the outputs, the public inputs, the private inputs, then
     * everything else, in that order whatever the declaration order.
     */
    lastInterfaceLabel: number;
    /** Wire index -> label. */
    label: number[];
    constraints: [Lc, Lc, Lc][];
}

/** Coefficients interned across both systems, so equal ids mean equal field elements. */
type Interner = Map<string, number>;

async function load(file: string, coefIds: Interner): Promise<System> {
    const r1cs = await readR1cs(file, {
        loadConstraints: true,
        loadMap: true,
        getFieldFromPrime: (p: bigint) => new F1Field(p),
    });
    const lc = (raw: Record<string, bigint>): Lc => {
        const keys = Object.keys(raw);
        const vars = new Int32Array(keys.length);
        const coefs = new Int32Array(keys.length);
        keys.forEach((key, i) => {
            const coef = raw[key].toString();
            let id = coefIds.get(coef);
            if (id === undefined) coefIds.set(coef, (id = coefIds.size + 1));
            vars[i] = Number(key);
            coefs[i] = id;
        });
        return { vars, coefs };
    };
    return {
        nVars: r1cs.nVars,
        lastInterfaceLabel: r1cs.nOutputs + r1cs.nPubInputs + r1cs.nPrvInputs,
        label: (r1cs.map as (number | bigint)[]).map(Number),
        constraints: (r1cs.constraints as Record<string, bigint>[][]).map(([a, b, c]) => [lc(a), lc(b), lc(c)]),
    };
}

// ===== colour refinement =====

// A colour is a pair of 32-bit hashes under independent seeds, compared as one
// 53-bit number. A collision can only merge two classes, which makes the
// proposed renaming fail the exact comparison; it cannot produce a false proof.

function mix(h: number, x: number): number {
    h = Math.imul(h ^ x, 0x9e3779b1);
    h ^= h >>> 15;
    h = Math.imul(h, 0x85ebca6b);
    return (h ^ (h >>> 13)) | 0;
}

class Colouring {
    readonly c1: Int32Array;
    readonly c2: Int32Array;

    constructor(readonly sys: System) {
        this.c1 = new Int32Array(sys.nVars);
        this.c2 = new Int32Array(sys.nVars);
        for (let v = 0; v < sys.nVars; v++) {
            if (sys.label[v] <= sys.lastInterfaceLabel) this.pin(v, sys.label[v] + 1);
        }
    }

    /** Give `v` a colour no refinement produces for another signal by chance. */
    pin(v: number, tag: number): void {
        this.c1[v] = mix(0x1234567, tag);
        this.c2[v] = mix(0x7654321, tag);
    }

    key(v: number): number {
        return (this.c1[v] >>> 0) * 0x200000 + (this.c2[v] >>> 11);
    }

    /** Sum of term hashes: independent of the order terms are stored in. */
    private side(lc: Lc, c: Int32Array, seed: number): number {
        let h = 0;
        for (let i = 0; i < lc.vars.length; i++) h = (h + mix(mix(seed, lc.coefs[i]), c[lc.vars[i]])) | 0;
        return h;
    }

    /** Add a constraint's hash, as seen from one of its sides, to each signal on that side. */
    private spread(acc: Int32Array, lc: Lc, seen: number): void {
        for (let i = 0; i < lc.vars.length; i++) {
            acc[lc.vars[i]] = (acc[lc.vars[i]] + mix(seen, lc.coefs[i])) | 0;
        }
    }

    /** One round: every signal's colour absorbs the constraints it occurs in. */
    private round(c: Int32Array, seed: number): void {
        const acc = new Int32Array(this.sys.nVars);
        for (const [A, B, C] of this.sys.constraints) {
            const a = this.side(A, c, seed);
            const b = this.side(B, c, seed);
            const cc = this.side(C, c, seed);
            // A·B is commutative, so the two factors are an unordered pair.
            const whole = mix(mix(mix(seed, Math.min(a, b)), Math.max(a, b)), cc);
            this.spread(acc, A, mix(mix(whole, 1), a));
            this.spread(acc, B, mix(mix(whole, 1), b));
            this.spread(acc, C, mix(mix(whole, 2), cc));
        }
        for (let v = 0; v < this.sys.nVars; v++) c[v] = mix(c[v], acc[v]);
    }

    refineOnce(): void {
        this.round(this.c1, 0x3c6ef372);
        this.round(this.c2, 0x510e527f);
    }

    classCount(): number {
        const seen = new Set<number>();
        for (let v = 0; v < this.sys.nVars; v++) seen.add(this.key(v));
        return seen.size;
    }

    /** `colour -> signals`, each list ascending. */
    classes(): Map<number, number[]> {
        const out = new Map<number, number[]>();
        for (let v = 0; v < this.sys.nVars; v++) {
            const k = this.key(v);
            const list = out.get(k);
            if (list === undefined) out.set(k, [v]);
            else list.push(v);
        }
        return out;
    }
}

const MAX_ROUNDS = 20_000;
/** Interchangeable-signal classes resolved one at a time before giving up. */
const MAX_CHOICES = 256;

/** Refine both colourings in step until neither partition splits further. */
function stabilize(a: Colouring, b: Colouring): boolean {
    let count = a.classCount();
    for (let round = 0; round < MAX_ROUNDS; round++) {
        a.refineOnce();
        b.refineOnce();
        const next = a.classCount();
        // Refinement only splits classes, so an unchanged count is a fixed point.
        if (next === count) return true;
        count = next;
    }
    return false;
}

function sameClassSizes(a: Map<number, number[]>, b: Map<number, number[]>): boolean {
    if (a.size !== b.size) return false;
    for (const [key, list] of a) {
        if (b.get(key)?.length !== list.length) return false;
    }
    return true;
}

// ===== exact comparison =====

/** `sys`'s constraints as sorted strings, with signal `v` written as `rename[v]`. */
function canonical(sys: System, rename: Int32Array): string[] {
    const side = (lc: Lc) => {
        const terms: string[] = [];
        for (let i = 0; i < lc.vars.length; i++) terms.push(`${rename[lc.vars[i]]}:${lc.coefs[i]}`);
        return terms.sort().join(",");
    };
    return sys.constraints
        .map(([A, B, C]) => {
            const [a, b] = [side(A), side(B)].sort();
            return `${a}|${b}|${side(C)}`;
        })
        .sort();
}

export interface Verdict {
    isomorphic: boolean;
    reason: string;
}

export async function isomorphic(fileA: string, fileB: string): Promise<Verdict> {
    const coefIds: Interner = new Map();
    const [A, B] = [await load(fileA, coefIds), await load(fileB, coefIds)];
    const no = (reason: string): Verdict => ({ isomorphic: false, reason });

    if (A.nVars !== B.nVars) return no("different signal counts");
    const wired = (s: System) => s.label.filter(l => l <= s.lastInterfaceLabel).join();
    if (A.lastInterfaceLabel !== B.lastInterfaceLabel || wired(A) !== wired(B)) {
        return no("different interface signals are wired");
    }
    if (A.constraints.length !== B.constraints.length) return no("different constraint counts");

    const [ca, cb] = [new Colouring(A), new Colouring(B)];
    let choices = 0;
    for (;;) {
        if (!stabilize(ca, cb)) return no("colour refinement did not settle");
        const [classesA, classesB] = [ca.classes(), cb.classes()];
        if (!sameClassSizes(classesA, classesB)) return no("the constraint graphs differ");

        // Signals refinement cannot tell apart. Pair one from each side and
        // refine again; the pairing then propagates to whatever depends on it.
        let open: number | undefined;
        for (const [key, list] of classesA) {
            if (list.length > 1 && (open === undefined || key < open)) open = key;
        }
        if (open === undefined) {
            const rename = new Int32Array(B.nVars);
            for (const [key, [v]] of classesB) rename[v] = classesA.get(key)![0];
            const identity = Int32Array.from({ length: A.nVars }, (_, v) => v);
            const [left, right] = [canonical(A, identity), canonical(B, rename)];
            const equal = left.every((c, i) => c === right[i]);
            return equal
                ? { isomorphic: true, reason: `renaming verified over ${left.length} constraints, ${choices} choice(s)` }
                : no("the proposed renaming does not map the constraints onto each other");
        }
        if (++choices > MAX_CHOICES) return no("too many interchangeable signals to resolve");
        // Above every interface tag, which is a label plus one.
        const tag = A.lastInterfaceLabel + 1 + choices;
        ca.pin(classesA.get(open)![0], tag);
        cb.pin(classesB.get(open)![0], tag);
    }
}

if (process.argv[1] !== undefined && import.meta.url === pathToFileURL(process.argv[1]).href) {
    isomorphic(process.argv[2], process.argv[3]).then(
        verdict => {
            console.log(JSON.stringify(verdict));
            process.exit(0);
        },
        err => {
            console.error(err instanceof Error ? err.message : err);
            process.exit(1);
        },
    );
}
