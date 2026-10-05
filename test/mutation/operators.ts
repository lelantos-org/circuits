// Mutation operators over circom source: each rewrites one statement into a
// defect of a known class. `scripts/mutate.ts` compiles every result and runs
// the suites against it; a mutant no suite rejects is a constraint nothing
// tests.
//
// Operators work on single-line statements with comments already stripped,
// which is how `src/` is written. They are textual: a mutant that does not
// compile is discarded by the runner, so an operator may over-generate.

/** One replaced line. `text` is code only; the runner re-attaches the comment. */
export interface Edit {
    /** 1-based. */
    line: number;
    text: string;
}

export interface Operator {
    name: string;
    /** The defect the operator plants. */
    bugClass: string;
    /**
     * The mutant computes the same witness and fails the same asserts as the
     * original, so a suite that only runs the witness calculator cannot reject
     * it. Only a check that reads the R1CS or the source can.
     */
    calculatorPreserving?: boolean;
    /**
     * Every mutant of the statement at `code[i]`, each as the edits that
     * produce it. `code` is the whole file, one comment-stripped entry per line.
     */
    mutate(code: readonly string[], i: number): Edit[][];
}

// ===== statement shapes =====

const ASSERT = /^(\s*)(.+?)\s*===\s*(.+?);\s*$/;
const ASSIGN = /^(\s*)(.+?)\s*<==\s*(.+?);\s*$/;
const FOR = /^(\s*for\s*\(\s*var\s+\w+\s*=\s*)(.+?)(\s*;\s*\w+\s*<\s*)(.+?)(\s*;.*)$/;
/** `= Template(args);`, the instantiation of a component. */
const INSTANCE = /=\s*[A-Z]\w*\(([^()]*)\)\s*;/;
const RETURN_INT = /^(.*\breturn\s+)(\d+)(\s*;.*)$/;

/** The top-level `component main`, whose arguments are the shipped shape. */
function isMain(code: readonly string[], i: number): boolean {
    return /\bcomponent\s+main\b/.test(code[i]) || /^\s*}\s*=/.test(code[i]);
}

function single(line: number, texts: string[]): Edit[][] {
    return texts.map(text => [{ line, text }]);
}

/**
 * Where an expression-level operator may rewrite. For `x <== e` only `e`: a
 * rewritten left side is a double assignment, which does not compile. For
 * `a === b` the whole statement.
 */
function expressionRegion(code: string): { head: string; body: string } | null {
    const assign = code.indexOf("<==");
    if (assign >= 0) return { head: code.slice(0, assign + 3), body: code.slice(assign + 3) };
    if (code.includes("===")) return { head: "", body: code };
    return null;
}

/** `body` with the `n`-th match of `pattern` replaced, one result per match. */
function eachMatch(
    body: string,
    pattern: RegExp,
    replace: (m: RegExpExecArray) => string | null,
): string[] {
    const out: string[] = [];
    const re = new RegExp(pattern.source, "g");
    for (let m = re.exec(body); m !== null; m = re.exec(body)) {
        const next = replace(m);
        if (next !== null) out.push(body.slice(0, m.index) + next + body.slice(m.index + m[0].length));
    }
    return out;
}

// ===== operators =====

/** `a === b;` deleted. */
const dropAssert: Operator = {
    name: "drop-assert",
    bugClass: "missing constraint",
    mutate(code, i) {
        const m = ASSERT.exec(code[i]);
        if (m === null || code[i].includes("<==")) return [];
        return single(i + 1, [m[1]]);
    },
};

/** `x <== e;` becomes `x <-- e;`: the witness is unchanged, the constraint is gone. */
const unconstrain: Operator = {
    name: "unconstrain",
    bugClass: "assigned but not constrained",
    calculatorPreserving: true,
    mutate(code, i) {
        return single(i + 1, eachMatch(code[i], /<==/, () => "<--"));
    },
};

/** `x <== e;` becomes `x <== 0;` and `x <== 1;`: a wire tied to a constant. */
const constRhs: Operator = {
    name: "const-rhs",
    bugClass: "signal tied to a constant",
    mutate(code, i) {
        const m = ASSIGN.exec(code[i]);
        if (m === null) return [];
        return single(
            i + 1,
            ["0", "1"].filter(c => m[3] !== c).map(c => `${m[1]}${m[2]} <== ${c};`),
        );
    },
};

/** One array index moved: a literal `n` to `n + 1`, anything else to `0`. */
const swapIndex: Operator = {
    name: "swap-index",
    bugClass: "wrong slot",
    mutate(code, i) {
        const region = expressionRegion(code[i]);
        if (region === null) return [];
        const bodies = eachMatch(region.body, /\[([^\[\]]+)\]/, m => {
            const inner = m[1].trim();
            return /^\d+$/.test(inner) ? `[${Number(inner) + 1}]` : `[0]`;
        });
        return single(i + 1, bodies.map(b => region.head + b));
    },
};

/** A loop that skips its last or its first iteration. */
const loopBound: Operator = {
    name: "loop-bound",
    bugClass: "off-by-one loop",
    mutate(code, i) {
        const m = FOR.exec(code[i]);
        if (m === null) return [];
        return single(i + 1, [
            `${m[1]}${m[2]}${m[3]}${m[4]} - 1${m[5]}`,
            `${m[1]}${m[2]} + 1${m[3]}${m[4]}${m[5]}`,
        ]);
    },
};

/** `(1 - s)` becomes `(s)`: a gate that opens on the opposite selector. */
const flipGate: Operator = {
    name: "flip-gate",
    bugClass: "inverted selector",
    mutate(code, i) {
        const region = expressionRegion(code[i]);
        if (region === null) return [];
        const bodies = eachMatch(region.body, /\(1 - ([^()]+)\)/, m => `(${m[1]})`);
        return single(i + 1, bodies.map(b => region.head + b));
    },
};

/** One `+` or `-` flipped, outside array indices. */
const arithFlip: Operator = {
    name: "arith-flip",
    bugClass: "wrong arithmetic",
    mutate(code, i) {
        const region = expressionRegion(code[i]);
        if (region === null) return [];
        // Depth of `[` at each offset, so an index expression is left to
        // `swap-index`.
        const depth: number[] = [];
        let d = 0;
        for (const ch of region.body) {
            if (ch === "[") d++;
            depth.push(d);
            if (ch === "]") d--;
        }
        const bodies = eachMatch(region.body, / ([+-]) /, m =>
            depth[m.index] > 0 ? null : m[1] === "+" ? " - " : " + ",
        );
        return single(i + 1, bodies.map(b => region.head + b));
    },
};

/**
 * An integer literal incremented: a template argument (`Num2Bits(64)` to
 * `Num2Bits(65)`) or a function's return value (a tag, the packing shift).
 */
const constTweak: Operator = {
    name: "const-tweak",
    bugClass: "wrong constant",
    mutate(code, i) {
        if (isMain(code, i)) return [];
        const line = code[i];
        const ret = RETURN_INT.exec(line);
        if (ret !== null) return single(i + 1, [`${ret[1]}${BigInt(ret[2]) + 1n}${ret[3]}`]);

        const inst = INSTANCE.exec(line);
        if (inst === null) return [];
        const open = line.indexOf("(", inst.index);
        const args = eachMatch(inst[1], /\b\d+\b/, m => String(BigInt(m[0]) + 1n));
        return single(i + 1, args.map(a => line.slice(0, open + 1) + a + line.slice(open + 1 + inst[1].length)));
    },
};

/** Two adjacent `x <== e;` wires with their right sides exchanged. */
const crossWire: Operator = {
    name: "cross-wire",
    bugClass: "transposed wires",
    mutate(code, i) {
        if (i + 1 >= code.length) return [];
        const a = ASSIGN.exec(code[i]);
        const b = ASSIGN.exec(code[i + 1]);
        if (a === null || b === null || a[3] === b[3]) return [];
        return [[
            { line: i + 1, text: `${a[1]}${a[2]} <== ${b[3]};` },
            { line: i + 2, text: `${b[1]}${b[2]} <== ${a[3]};` },
        ]];
    },
};

export const OPERATORS: readonly Operator[] = [
    dropAssert,
    unconstrain,
    constRhs,
    swapIndex,
    loopBound,
    flipGate,
    arithFlip,
    constTweak,
    crossWire,
];

// ===== comment stripping =====

/**
 * Split a source file into per-line code and trailing comment. A line inside a
 * block comment has empty code, so no operator matches it.
 */
export function splitComments(source: string): { code: string[]; comment: string[] } {
    const code: string[] = [];
    const comment: string[] = [];
    let inBlock = false;
    for (const line of source.split("\n")) {
        if (inBlock) {
            const end = line.indexOf("*/");
            if (end >= 0) inBlock = false;
            code.push("");
            comment.push(line);
            continue;
        }
        const block = line.indexOf("/*");
        const slash = line.indexOf("//");
        if (block >= 0 && (slash < 0 || block < slash)) {
            inBlock = !line.includes("*/", block + 2);
            code.push(line.slice(0, block));
            comment.push(line.slice(block));
            continue;
        }
        if (slash >= 0) {
            code.push(line.slice(0, slash));
            comment.push(line.slice(slash));
        } else {
            code.push(line);
            comment.push("");
        }
    }
    return { code, comment };
}

/** Whether mutants of operator `name` leave the witness calculator unchanged. */
export function calculatorPreserving(name: string): boolean {
    return OPERATORS.some(op => op.name === name && op.calculatorPreserving === true);
}
