// Runs the suites against one mutant of `src/`.
//
// A worker is a private copy of `src/`, `test/` and the justfile under
// `build/.mutation/`, with everything else symlinked. The copied suites resolve the package root
// from their own location, so they compile the worker's `src/` and write under
// the worker's `build/`. Workers therefore run concurrently and the checkout is
// never modified.

import { spawn } from "child_process";
import * as crypto from "crypto";
import * as fs from "fs";
import * as path from "path";

import { ROOT } from "../lib/files";
import { apply, type Mutant, type Root } from "./mutants";
import type { Tamper } from "./probe";

export const WORK = path.join(ROOT, "build", ".mutation");

/** Read through a symlink. */
const LINKED = ["node_modules", "lean", "vectors", "scripts", "budget.json", "package.json", "tsconfig.json"];

/** Copied. The justfile is among them because its recipes resolve paths from its own directory. */
const COPIED = ["src", "test", "justfile"];

// ===== stages =====

/**
 * The gates a mutant is run against, each a separate process:
 *
 *   unit   the spec suites: honest witnesses, tamper rows, gadget tests
 *   fuzz   the fast-check properties
 *   sweep  the R1CS second-witness search
 *   lint   `just lint`: circomspect and the ban on `<--`
 *   lean   the citation and coverage checks tying `lean/` to the source text
 *
 * `lint` and `lean` read source text and never run the circuit; see `DYNAMIC`.
 */
export const STAGES = ["unit", "fuzz", "sweep", "lint", "lean"] as const;
export type Stage = (typeof STAGES)[number];

/**
 * Stages that execute the mutant. A mutant only the others reject is caught by
 * CI, but nothing tests the behaviour it changes.
 */
export const DYNAMIC: readonly Stage[] = ["unit", "fuzz", "sweep"];

export interface StageResult {
    stage: Stage;
    killed: boolean;
    /** The first failing test, or what stopped the process. */
    test?: string;
    /** The spec file that test is in, relative to the package root. */
    spec?: string;
    message?: string;
    ms: number;
    /** On a passing run: the time each spec file's tests took. */
    specMs?: Record<string, number>;
}

interface SpecRule {
    match: RegExp;
    /** `null`: never run against a mutant. */
    stage: Stage | null;
    /** Run only for mutants of files this circuit includes. */
    root?: Root;
}

// First match wins. Paths are relative to `test/`.
const SPEC_RULES: SpecRule[] = [
    // Read committed artifacts or test the tooling; none compiles `src/`.
    { match: /^(tooling|formal|mutation)\//, stage: null },
    { match: /^fuzz\/underconstrained_batch\./, stage: "sweep", root: "tree_update_batch" },
    { match: /^fuzz\/underconstrained\./, stage: "sweep", root: "4x6" },
    { match: /^fuzz\/frontier_binding\./, stage: "fuzz", root: "tree_update_batch" },
    { match: /^fuzz\/transact/, stage: "fuzz", root: "4x6" },
    { match: /^fuzz\//, stage: "fuzz" },
    { match: /^batch\//, stage: "unit", root: "tree_update_batch" },
    { match: /^gadgets\/batch_append\./, stage: "unit", root: "tree_update_batch" },
    { match: /^transact\//, stage: "unit", root: "4x6" },
    { match: /./, stage: "unit" },
];

function specFiles(dir: string, prefix = ""): string[] {
    return fs.readdirSync(dir, { withFileTypes: true }).flatMap(entry => {
        const rel = prefix + entry.name;
        if (entry.isDirectory()) return specFiles(path.join(dir, entry.name), rel + "/");
        return entry.name.endsWith(".test.ts") ? [rel] : [];
    });
}

/** The spec files `stage` runs for a mutant reaching `roots`, relative to the package root. */
export function specsFor(stage: Stage, roots: readonly Root[]): string[] {
    return specFiles(path.join(ROOT, "test"))
        .sort()
        .filter(rel => {
            const rule = SPEC_RULES.find(r => r.match.test(rel))!;
            return rule.stage === stage && (rule.root === undefined || roots.includes(rule.root));
        })
        .map(rel => `test/${rel}`);
}

// ===== processes =====

interface Exit {
    code: number | null;
    timedOut: boolean;
    output: string;
}

function run(cmd: string, args: string[], cwd: string, env: NodeJS.ProcessEnv, timeoutMs: number): Promise<Exit> {
    return new Promise(resolve => {
        const child = spawn(cmd, args, { cwd, env, stdio: ["ignore", "pipe", "pipe"] });
        const chunks: Buffer[] = [];
        child.stdout.on("data", c => chunks.push(c));
        child.stderr.on("data", c => chunks.push(c));
        let timedOut = false;
        const timer = setTimeout(() => {
            timedOut = true;
            child.kill("SIGKILL");
        }, timeoutMs);
        child.on("close", code => {
            clearTimeout(timer);
            resolve({ code, timedOut, output: Buffer.concat(chunks).toString("utf8") });
        });
    });
}

/** The last non-empty lines of a process's output, for a failure with no test to name. */
function tail(output: string, lines = 3): string {
    return output.split("\n").map(l => l.trim()).filter(l => l !== "").slice(-lines).join(" | ");
}

// ===== workers =====

export interface Worker {
    root: string;
}

/** A fresh worker. Anything a previous run left at the same index is removed. */
export function createWorker(index: number): Worker {
    const root = path.join(WORK, `w${index}`);
    fs.rmSync(root, { recursive: true, force: true });
    fs.mkdirSync(path.join(root, "build"), { recursive: true });
    for (const name of COPIED) {
        fs.cpSync(path.join(ROOT, name), path.join(root, name), { recursive: true });
    }
    for (const name of LINKED) {
        fs.symlinkSync(path.join(ROOT, name), path.join(root, name));
    }
    return { root };
}

/** Write `mutant` into the worker's `src/`; the returned function restores it. */
export function plant(worker: Worker, mutant: Mutant): () => void {
    const file = path.join(worker.root, "src", mutant.file);
    const original = fs.readFileSync(path.join(ROOT, "src", mutant.file), "utf8");
    fs.writeFileSync(file, apply(original, mutant));
    return () => fs.writeFileSync(file, original);
}

// ===== compile check =====

const COMPILE_TIMEOUT = 120_000;

function r1csPath(worker: Worker, root: Root): string {
    return path.join(worker.root, "build", ".precheck", root, `${root}.r1cs`);
}

/** The unmutated R1CS of `root`, kept for `provenEquivalent`. */
function pristineR1cs(root: Root): string {
    return path.join(WORK, `pristine-${root}.r1cs`);
}

/** Compile one shipped circuit from `worker` and return the digest of its R1CS. */
async function r1csDigest(worker: Worker, root: Root): Promise<{ digest?: string; error?: string }> {
    const out = path.dirname(r1csPath(worker, root));
    fs.rmSync(out, { recursive: true, force: true });
    fs.mkdirSync(out, { recursive: true });
    const exit = await run(
        "circom",
        [path.join(worker.root, "src", `${root}.circom`), "--r1cs", "-o", out, "-l", path.join(ROOT, "node_modules")],
        worker.root,
        process.env,
        COMPILE_TIMEOUT,
    );
    if (exit.code !== 0) return { error: exit.timedOut ? "compile timed out" : tail(exit.output, 2) };
    const bytes = fs.readFileSync(r1csPath(worker, root));
    return { digest: crypto.createHash("sha256").update(bytes).digest("hex") };
}

/** The R1CS digest of each shipped circuit, compiled from an unmutated worker. */
export async function pristineDigests(worker: Worker, roots: readonly Root[]): Promise<Map<Root, string>> {
    const digests = new Map<Root, string>();
    for (const root of roots) {
        const { digest, error } = await r1csDigest(worker, root);
        if (digest === undefined) throw new Error(`the unmutated ${root}.circom does not compile: ${error}`);
        digests.set(root, digest);
        fs.copyFileSync(r1csPath(worker, root), pristineR1cs(root));
    }
    return digests;
}

export type Viability =
    | { kind: "viable" }
    /** Does not compile. */
    | { kind: "stillborn"; detail: string }
    /** Compiles to the same R1CS: the same statement is proved. */
    | { kind: "equivalent" };

/** Classify the mutant currently planted in `worker`. */
export async function viability(
    worker: Worker,
    mutant: Mutant,
    pristine: ReadonlyMap<Root, string>,
): Promise<Viability> {
    let changed = false;
    for (const root of mutant.roots) {
        const { digest, error } = await r1csDigest(worker, root);
        if (digest === undefined) return { kind: "stillborn", detail: error ?? "" };
        if (digest !== pristine.get(root)) changed = true;
    }
    return changed ? { kind: "viable" } : { kind: "equivalent" };
}

/**
 * Whether the mutant planted in `worker` is the original constraint system
 * with its intermediate signals renamed; see `isomorphic.ts`. Returns the proof
 * summary, or `null` when no renaming was found.
 */
export async function provenEquivalent(
    worker: Worker,
    mutant: Mutant,
    pristine: ReadonlyMap<Root, string>,
): Promise<string | null> {
    const reasons: string[] = [];
    for (const root of mutant.roots) {
        const { digest } = await r1csDigest(worker, root);
        if (digest === undefined) return null;
        if (digest === pristine.get(root)) continue;
        const exit = await run(
            process.execPath,
            [path.join(ROOT, "test", "mutation", "isomorphic.ts"), pristineR1cs(root), r1csPath(worker, root)],
            ROOT,
            { ...process.env, NODE_OPTIONS: "--import tsx/esm" },
            COMPILE_TIMEOUT * 5,
        );
        if (exit.code !== 0) return null;
        const verdict = JSON.parse(exit.output.trim().split("\n").pop()!) as { isomorphic: boolean; reason: string };
        if (!verdict.isomorphic) return null;
        reasons.push(`${root}: ${verdict.reason}`);
    }
    return reasons.join("; ");
}

// ===== running a stage =====

const STAGE_TIMEOUT: Record<Stage, number> = {
    unit: 900_000,
    fuzz: 900_000,
    sweep: 1_800_000,
    lint: 120_000,
    lean: 120_000,
};

interface MochaReport {
    stats: { tests: number; failures: number };
    tests: { file?: string; duration?: number }[];
    failures: { fullTitle: string; file?: string; err: { message?: string } }[];
}

async function runSpecs(worker: Worker, stage: Stage, specs: string[], seed: number): Promise<StageResult> {
    const started = Date.now();
    const done = (r: Omit<StageResult, "stage" | "ms">): StageResult => ({ stage, ms: Date.now() - started, ...r });
    if (specs.length === 0) return done({ killed: false });

    const report = path.join(worker.root, "build", `.mocha-${stage}.json`);
    fs.rmSync(report, { force: true });
    const env = { ...process.env, NODE_OPTIONS: "--import tsx/esm", FUZZ: "light", FUZZ_SEED: String(seed) };
    delete (env as NodeJS.ProcessEnv).FUZZ_PATH;
    const exit = await run(
        process.execPath,
        [
            path.join(ROOT, "node_modules", "mocha", "bin", "mocha.js"),
            "--reporter", "json", "--reporter-option", `output=${report}`,
            "--timeout", String(STAGE_TIMEOUT[stage]), "--exit", "--bail",
            ...specs,
        ],
        worker.root,
        env,
        STAGE_TIMEOUT[stage],
    );

    if (exit.timedOut) return done({ killed: true, test: "(timeout)" });
    if (!fs.existsSync(report)) {
        // No report: mocha died before or while loading the specs.
        return done({ killed: true, test: "(no report)", message: tail(exit.output) });
    }
    const parsed = JSON.parse(fs.readFileSync(report, "utf8")) as MochaReport;
    if (parsed.failures.length === 0) {
        if (parsed.stats.tests === 0) {
            return done({ killed: true, test: "(no tests ran)", message: tail(exit.output) });
        }
        const specMs: Record<string, number> = {};
        for (const t of parsed.tests) {
            if (t.file === undefined) continue;
            const spec = path.relative(worker.root, t.file);
            specMs[spec] = (specMs[spec] ?? 0) + (t.duration ?? 0);
        }
        return done({ killed: false, specMs });
    }
    const first = parsed.failures[0];
    return done({
        killed: true,
        test: first.fullTitle,
        spec: first.file === undefined ? undefined : path.relative(worker.root, first.file),
        message: (first.err.message ?? "").split("\n")[0].slice(0, 240),
    });
}

async function runLean(worker: Worker): Promise<StageResult> {
    const started = Date.now();
    for (const script of ["check-citations.py", "check-coverage.py"]) {
        // The path is passed through the worker's `lean` symlink: the scripts
        // locate the repository from their own unresolved path.
        const exit = await run(
            "python3",
            [path.join(worker.root, "lean", "scripts", script)],
            worker.root,
            process.env,
            STAGE_TIMEOUT.lean,
        );
        if (exit.code !== 0) {
            return { stage: "lean", killed: true, test: script, message: tail(exit.output, 2), ms: Date.now() - started };
        }
    }
    return { stage: "lean", killed: false, ms: Date.now() - started };
}

async function runLint(worker: Worker): Promise<StageResult> {
    const started = Date.now();
    const exit = await run("just", ["lint"], worker.root, process.env, STAGE_TIMEOUT.lint);
    const ms = Date.now() - started;
    if (exit.code === 0) return { stage: "lint", killed: false, ms };
    return { stage: "lint", killed: true, test: "just lint", message: tail(exit.output, 2), ms };
}

/**
 * Run one stage against whatever is planted in `worker`. `order` arranges a
 * dynamic stage's spec files; the stage stops at its first failing test.
 */
export function runStage(
    worker: Worker,
    stage: Stage,
    roots: readonly Root[],
    seed: number,
    order: (specs: string[]) => string[] = specs => specs,
): Promise<StageResult> {
    if (stage === "lean") return runLean(worker);
    if (stage === "lint") return runLint(worker);
    return runSpecs(worker, stage, order(specsFor(stage, roots)), seed);
}

/** Whether `cmd` is on PATH. */
export async function available(cmd: string): Promise<boolean> {
    const exit = await run("sh", ["-c", `command -v ${cmd}`], ROOT, process.env, 10_000);
    return exit.code === 0;
}

// ===== input search =====

const PROBE_TIMEOUT = 1_800_000;

function runProbe(worker: Worker, args: string[]): Promise<Exit> {
    return run(
        process.execPath,
        [path.join(worker.root, "test", "mutation", "probe.ts"), ...args],
        worker.root,
        { ...process.env, NODE_OPTIONS: "--import tsx/esm" },
        PROBE_TIMEOUT,
    );
}

function corpusFile(root: Root): string {
    return path.join(WORK, `corpus-${root}.json`);
}

/**
 * Build the rejected-input corpus of one shipped circuit; see `probe.ts`.
 * `worker` must hold the unmutated tree.
 */
export async function buildCorpus(worker: Worker, root: Root): Promise<number> {
    const exit = await runProbe(worker, ["corpus", root, corpusFile(root)]);
    if (exit.code !== 0) throw new Error(`probe corpus for ${root} failed: ${tail(exit.output)}`);
    return (JSON.parse(fs.readFileSync(corpusFile(root), "utf8")) as Tamper[]).length;
}

export interface ProbeResult {
    /** Rejected inputs replayed. */
    tried: number;
    /** The ones the mutant accepts, each tagged with its circuit. */
    accepted: (Tamper & { root: Root })[];
    /** Set when the search itself failed. */
    error?: string;
}

/** Replay each corpus against the mutant planted in `worker`. */
export async function probe(worker: Worker, mutant: Mutant): Promise<ProbeResult> {
    const result: ProbeResult = { tried: 0, accepted: [] };
    for (const root of mutant.roots) {
        const out = path.join(worker.root, "build", `.probe-${root}.json`);
        fs.rmSync(out, { force: true });
        const exit = await runProbe(worker, ["replay", root, corpusFile(root), out]);
        if (exit.code !== 0 || !fs.existsSync(out)) {
            result.error = exit.timedOut ? "timed out" : tail(exit.output);
            continue;
        }
        const parsed = JSON.parse(fs.readFileSync(out, "utf8")) as { tried: number; accepted: Tamper[] };
        result.tried += parsed.tried;
        result.accepted.push(...parsed.accepted.map(t => ({ ...t, root })));
    }
    return result;
}

// ===== pool =====

/**
 * Map `items` over the workers, one item per worker at a time. Results keep the
 * order of `items`.
 */
export async function pool<T, R>(
    workers: readonly Worker[],
    items: readonly T[],
    task: (item: T, worker: Worker, index: number) => Promise<R>,
): Promise<R[]> {
    const results = new Array<R>(items.length);
    let next = 0;
    await Promise.all(
        workers.map(async worker => {
            while (next < items.length) {
                const index = next++;
                results[index] = await task(items[index], worker, index);
            }
        }),
    );
    return results;
}
