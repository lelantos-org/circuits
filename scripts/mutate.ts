// Mutation fuzzer for `src/`: plants one defect at a time and checks that a
// gate rejects it.
//
//   node scripts/mutate.ts [options]         (or: just mutate [options])
//
//   --all              every mutant, instead of a sample
//   --only <id,...>    these mutants; ids are printed by every run and by --list
//   --file <text>      mutants of files whose path contains <text>
//   --op <name,...>    mutants of these operators
//   --stages <a,b>     gates to run: unit, fuzz, sweep, lint, lean (default: all)
//   --jobs <n>         concurrent workers
//   --matrix           run every gate on every mutant, to see which gates overlap
//   --resume           reuse outcomes already recorded for the current tree
//   --baseline         run the unmutated tree through the gates even if the
//                      history says it passed; for a machine that may have changed
//   --no-probe         skip the input search on mutants no test rejects
//   --list             print the selected mutants, in the order a run takes them
//   --update           rewrite test/mutation/survivors.json from this run
//
// Env: FUZZ=light|medium|heavy sets the sample size (8 / 40 / 160). FUZZ_SEED
// orders mutants the history ranks equally and seeds the fuzz suites.
//
// A mutant is `killed` when a suite that runs it fails, `static` when only lint
// or the lean citation checks reject it, and `survived` when nothing does. One
// that compiles to the original constraint system, byte for byte or up to a
// renaming of signals, is `equivalent` and discarded.
//
// By default a mutant stops at its first kill, and gates that cannot reject it
// are not run: see `gatesFor`. Earlier runs steer this one through
// build/.mutation/history.json: the test that rejected a mutant before runs
// first, and a sample is drawn from weak and untested mutants before repeats.
//
// For each `static` or `survived` mutant the run then searches for an input
// the shipped circuit rejects and the mutant accepts (test/mutation/probe.ts):
// the tamper row that would have killed it.
//
// Exits 1 when a mutant survives that test/mutation/survivors.json does not
// accept, or when an accepted entry no longer survives.

import * as fs from "fs";
import * as os from "os";
import * as path from "path";

import { ROOT } from "../test/lib/files";
import {
    DYNAMIC,
    STAGES,
    WORK,
    available,
    buildCorpus,
    createWorker,
    plant,
    pool,
    pristineDigests,
    probe,
    provenEquivalent,
    runStage,
    viability,
    type ProbeResult,
    type Stage,
    type StageResult,
    type Worker,
} from "../test/mutation/campaign";
import {
    TESTED,
    Tier,
    fingerprint,
    orderSpecs,
    orderStages,
    prioritized,
    readHistory,
    tierOf,
    writeHistory,
    type History,
    type Status,
} from "../test/mutation/history";
import {
    ROOTS,
    enumerate,
    keyOf,
    readAccepted,
    writeAccepted,
    type Accepted,
    type Mutant,
    type Root,
} from "../test/mutation/mutants";
import { calculatorPreserving } from "../test/mutation/operators";

const ACCEPTED = path.join(ROOT, "test", "mutation", "survivors.json");
const REPORT = path.join(WORK, "report.json");
const HISTORY = path.join(WORK, "history.json");
const SAMPLE: Record<string, number> = { light: 8, medium: 40, heavy: 160 };
const STATIC: readonly Stage[] = STAGES.filter(s => !DYNAMIC.includes(s));

// ===== arguments =====

interface Options {
    all: boolean;
    only: string[];
    file?: string;
    ops: string[];
    stages: Stage[];
    jobs: number;
    matrix: boolean;
    resume: boolean;
    baseline: boolean;
    probe: boolean;
    list: boolean;
    update: boolean;
    tier: string;
    seed: number;
}

function parseArgs(argv: string[]): Options {
    const tier = (process.env.FUZZ || "medium").toLowerCase();
    if (!(tier in SAMPLE)) throw new Error(`FUZZ must be light, medium or heavy, got "${tier}"`);
    const seed = process.env.FUZZ_SEED ? Number(process.env.FUZZ_SEED) : Date.now();
    if (!Number.isFinite(seed)) throw new Error(`FUZZ_SEED must be a number, got "${process.env.FUZZ_SEED}"`);

    const opts: Options = {
        all: false,
        only: [],
        ops: [],
        stages: [...STAGES],
        jobs: Math.max(1, Math.min(8, Math.floor(os.availableParallelism() / 2))),
        matrix: false,
        resume: false,
        baseline: false,
        probe: true,
        list: false,
        update: false,
        tier,
        seed,
    };
    const list = (v: string) => v.split(",").map(s => s.trim()).filter(s => s !== "");
    for (let i = 0; i < argv.length; i++) {
        const arg = argv[i];
        const value = () => {
            if (i + 1 >= argv.length) throw new Error(`${arg} needs a value`);
            return argv[++i];
        };
        switch (arg) {
            case "--all": opts.all = true; break;
            case "--matrix": opts.matrix = true; break;
            case "--resume": opts.resume = true; break;
            case "--baseline": opts.baseline = true; break;
            case "--no-probe": opts.probe = false; break;
            case "--list": opts.list = true; break;
            case "--update": opts.update = true; break;
            case "--only": opts.only.push(...list(value())); break;
            case "--file": opts.file = value(); break;
            case "--op": opts.ops.push(...list(value())); break;
            case "--jobs": opts.jobs = Math.max(1, parseInt(value(), 10)); break;
            case "--stages": {
                const stages = list(value());
                const unknown = stages.filter(s => !(STAGES as readonly string[]).includes(s));
                if (unknown.length > 0) throw new Error(`unknown stage(s): ${unknown.join(", ")}`);
                opts.stages = STAGES.filter(s => stages.includes(s));
                break;
            }
            default: throw new Error(`unknown argument: ${arg}`);
        }
    }
    return opts;
}

// ===== outcome =====

interface Outcome {
    mutant: Mutant;
    status: Status;
    /** Why a stillborn mutant does not compile, or how an equivalent one was proved so. */
    detail?: string;
    stages: StageResult[];
    /** The input search, on a mutant no test rejects. */
    probe?: ProbeResult;
    /** Taken from the history instead of run. */
    resumed?: boolean;
}

function killers(o: Outcome): Stage[] {
    return o.stages.filter(s => s.killed).map(s => s.stage);
}

function describe(o: Outcome): string {
    const m = o.mutant;
    const lines = [m.id, `  - ${m.source}`, `  + ${m.mutated}`];
    if (o.probe !== undefined) {
        const { tried, accepted, error } = o.probe;
        if (error !== undefined) lines.push(`  input search failed: ${error}`);
        for (const t of accepted.slice(0, 3)) {
            lines.push(`  missing test: ${t.root} "${t.base}" with ${t.path} = ${t.value} is rejected today, accepted by the mutant`);
        }
        if (accepted.length > 3) lines.push(`  (${accepted.length - 3} more in the report)`);
        if (accepted.length === 0 && error === undefined) {
            lines.push(`  no single-field tamper separates it (${tried} rejected inputs replayed)`);
        }
    }
    return lines.join("\n      ");
}

// ===== gates =====

/**
 * The dynamic gates able to reject `mutant`. `unit` and `fuzz` execute only the
 * witness calculator, which a calculator-preserving operator leaves as it was;
 * the second-witness search reads the R1CS.
 */
function gatesFor(mutant: Mutant, opts: Options): Stage[] {
    const able = calculatorPreserving(mutant.op) ? ["sweep"] : DYNAMIC;
    return opts.stages.filter(s => able.includes(s));
}

/** Everything `run` needs beside the mutant and its worker. */
interface Campaign {
    opts: Options;
    history: History;
    pristine: ReadonlyMap<Root, string>;
}

/** Run the gates against one viable mutant. */
async function run(worker: Worker, mutant: Mutant, { opts, history, pristine }: Campaign): Promise<Outcome> {
    const restore = plant(worker, mutant);
    try {
        const stages: StageResult[] = [];
        for (const stage of opts.stages.filter(s => STATIC.includes(s))) {
            stages.push(await runStage(worker, stage, mutant.roots, opts.seed));
        }
        const flagged = stages.some(s => s.killed);
        const preserving = calculatorPreserving(mutant.op);

        // Lint rejects every `<--`. Whether the second-witness search also finds
        // the freed signal is a question about the search, asked with --matrix.
        if (flagged && preserving && !opts.matrix) return { mutant, status: "static", stages };

        const dynamic = gatesFor(mutant, opts);
        let killed = false;
        let compared = preserving;
        for (const stage of opts.matrix ? dynamic : orderStages(dynamic, mutant, history)) {
            const result = await runStage(worker, stage, mutant.roots, opts.seed, specs => orderSpecs(specs, mutant, history));
            stages.push(result);
            killed ||= result.killed;
            if (killed && !opts.matrix) break;
            // Once a gate has passed, before paying for the slower ones: is this
            // the original system with its signals renamed?
            if (!killed && !compared) {
                compared = true;
                const proof = await provenEquivalent(worker, mutant, pristine);
                if (proof !== null) return { mutant, status: "equivalent", detail: `isomorphic R1CS (${proof})`, stages };
            }
        }
        return { mutant, status: killed ? "killed" : flagged ? "static" : "survived", stages };
    } finally {
        restore();
    }
}

function remember(history: History, current: string, o: Outcome, opts: Options): void {
    const first = o.stages.find(s => s.killed && DYNAMIC.includes(s.stage));
    const { mutant, resumed: _, ...outcome } = o;
    history.mutants[keyOf(mutant)] = {
        fingerprint: current,
        file: mutant.file,
        op: mutant.op,
        status: o.status,
        stage: first?.stage,
        spec: first?.spec,
        stages: opts.stages,
        matrix: opts.matrix,
        outcome,
    };
    writeHistory(HISTORY, history);
}

/** The outcome recorded for `mutant` under the current tree and the same gates, if any. */
function recall(history: History, current: string, mutant: Mutant, opts: Options): Outcome | null {
    const past = history.mutants[keyOf(mutant)];
    if (past === undefined || past.fingerprint !== current) return null;
    if (past.stages.join() !== opts.stages.join() || (opts.matrix && !past.matrix)) return null;
    return { ...(past.outcome as Omit<Outcome, "mutant">), mutant, resumed: true };
}

// ===== report =====

function pad(s: string | number, n: number): string {
    return String(s).padStart(n);
}

function summarize(outcomes: Outcome[], opts: Options): void {
    const count = (xs: Outcome[], s: Status) => xs.filter(o => o.status === s).length;

    console.log("\n  operator       tested  killed  static  survived  killed %");
    const ops = [...new Set(outcomes.map(o => o.mutant.op))].sort();
    for (const op of [...ops, "TOTAL"]) {
        const rows = outcomes.filter(o => (op === "TOTAL" || o.mutant.op === op) && TESTED.includes(o.status));
        if (rows.length === 0) continue;
        const killed = count(rows, "killed");
        console.log(
            `  ${op.padEnd(13)} ${pad(rows.length, 7)} ${pad(killed, 7)} ${pad(count(rows, "static"), 7)} ` +
                `${pad(count(rows, "survived"), 9)} ${pad(((100 * killed) / rows.length).toFixed(1), 8)}%`,
        );
    }
    const equivalent = outcomes.filter(o => o.status === "equivalent");
    const proved = equivalent.filter(o => o.detail !== undefined);
    console.log(
        `\n  discarded: ${count(outcomes, "stillborn")} did not compile, ` +
            `${equivalent.length - proved.length} compiled to the same R1CS, ` +
            `${proved.length} to the same R1CS with signals renamed`,
    );
    for (const o of proved) console.log(`    ${o.mutant.id}  ${o.mutant.source}  =>  ${o.mutant.mutated}`);

    const tested = outcomes.filter(o => TESTED.includes(o.status));
    if (opts.matrix) {
        console.log("\n  gate    kills   only this gate");
        for (const stage of opts.stages) {
            const kills = tested.filter(o => killers(o).includes(stage));
            console.log(`  ${stage.padEnd(6)} ${pad(kills.length, 6)} ${pad(kills.filter(o => killers(o).length === 1).length, 8)}`);
        }
    } else {
        // Without --matrix a mutant stops at its first kill, so these are first kills.
        const first = new Map<Stage, number>();
        for (const o of tested) {
            const stage = o.stages.find(s => s.killed && DYNAMIC.includes(s.stage))?.stage;
            if (stage !== undefined) first.set(stage, (first.get(stage) ?? 0) + 1);
        }
        console.log(`\n  first kill by gate: ${DYNAMIC.map(s => `${s} ${first.get(s) ?? 0}`).join(", ")}`);
    }

    const cpu = outcomes.filter(o => !o.resumed).flatMap(o => o.stages).reduce((sum, s) => sum + s.ms, 0);
    console.log(`  gate time: ${Math.round(cpu / 1000)}s across workers`);
}

// ===== main =====

/** Claim `build/.mutation/`: a second run would delete the first one's workers. */
function lock(): void {
    fs.mkdirSync(WORK, { recursive: true });
    const file = path.join(WORK, "lock");
    if (fs.existsSync(file)) {
        const pid = Number(fs.readFileSync(file, "utf8"));
        let alive = false;
        try {
            process.kill(pid, 0);
            alive = true;
        } catch {
            // No such process: the lock is left over from a run that was killed.
        }
        if (alive) throw new Error(`another mutation run (pid ${pid}) is using ${path.relative(ROOT, WORK)}`);
    }
    fs.writeFileSync(file, String(process.pid));
    process.on("exit", () => fs.rmSync(file, { force: true }));
    // Workers of a run that was killed, or that used more jobs than this one.
    for (const name of fs.readdirSync(WORK)) {
        if (/^w\d+$/.test(name)) fs.rmSync(path.join(WORK, name), { recursive: true, force: true });
    }
}

async function main(): Promise<number> {
    const opts = parseArgs(process.argv.slice(2));
    const all = enumerate(path.join(ROOT, "src"));

    let selected = all;
    if (opts.only.length > 0) {
        const missing = opts.only.filter(id => !all.some(m => m.id === id));
        if (missing.length > 0) throw new Error(`no such mutant: ${missing.join(", ")} (see --list)`);
        selected = all.filter(m => opts.only.includes(m.id));
    }
    if (opts.file !== undefined) selected = selected.filter(m => m.file.includes(opts.file!));
    if (opts.ops.length > 0) selected = selected.filter(m => opts.ops.includes(m.op));

    const history = readHistory(HISTORY);
    const current = fingerprint();

    // A named or exhaustive run takes the mutants in source order; a sample is
    // drawn towards what the history marks as weak or untested.
    const exhaustive = opts.all || opts.only.length > 0;
    const candidates = exhaustive ? selected : prioritized(selected, history, current, opts.seed);
    const target = exhaustive ? Infinity : SAMPLE[opts.tier];

    if (opts.list) {
        for (const m of candidates) {
            console.log(`${m.id}\t${Tier[tierOf(m, history, current)].toLowerCase()}\t${m.source}  =>  ${m.mutated}`);
        }
        console.error(`${candidates.length} mutant(s)`);
        return 0;
    }

    const covered = all.filter(m => tierOf(m, history, current) === Tier.Current).length;
    console.error(
        `[mutate] ${selected.length} candidate(s), ` +
            (exhaustive ? "all of them" : `sampling ${target} (FUZZ=${opts.tier} FUZZ_SEED=${opts.seed})`) +
            `, ${opts.jobs} worker(s), gates: ${opts.stages.join(", ")}${opts.matrix ? " (every gate on every mutant)" : ""}`,
    );
    console.error(`[mutate] ${covered} of ${all.length} mutants already run against this tree`);

    // A gate whose tool is absent is skipped; the verdict below then stays open.
    // Under CI that would pass a run that checked nothing, so it is an error.
    const needs: Partial<Record<Stage, string[]>> = { lint: ["just", "circomspect"], lean: ["python3"] };
    for (const stage of [...opts.stages]) {
        const absent = [];
        for (const cmd of needs[stage] ?? []) if (!(await available(cmd))) absent.push(cmd);
        if (absent.length === 0) continue;
        if (process.env.CI) throw new Error(`the ${stage} gate needs ${absent.join(", ")}, which CI must install`);
        console.error(`[mutate] skipping the ${stage} gate: ${absent.join(", ")} not found`);
        opts.stages = opts.stages.filter(s => s !== stage);
    }

    lock();
    const workers = Array.from({ length: opts.jobs }, (_, i) => createWorker(i));
    const pristine = await pristineDigests(workers[0], ROOTS);

    // The unmutated tree must pass every gate, or every mutant would be "killed".
    const green = history.green;
    const passed = green !== undefined && green.fingerprint === current && opts.stages.every(s => green.stages.includes(s));
    if (passed && !opts.baseline) {
        console.error("[mutate] unmutated tree already passed these gates");
    } else {
        const baseline = await pool(workers, opts.stages, (stage, w) => runStage(w, stage, ROOTS, opts.seed));
        const red = baseline.filter(r => r.killed);
        if (red.length > 0) {
            for (const r of red) console.error(`  ${r.stage}: ${r.test}\n    ${r.message ?? ""}`);
            throw new Error("the unmutated circuits fail a gate; fix that before mutating");
        }
        for (const r of baseline) Object.assign(history.specMs, r.specMs ?? {});
        history.green = { fingerprint: current, stages: opts.stages };
        writeHistory(HISTORY, history);
        console.error(`[mutate] unmutated tree passes (${baseline.map(r => `${r.stage} ${Math.round(r.ms / 1000)}s`).join(", ")})`);
    }

    const outcomes: Outcome[] = [];
    const pending: Mutant[] = [];
    for (const mutant of candidates) {
        const past = opts.resume ? recall(history, current, mutant, opts) : null;
        if (past === null) pending.push(mutant);
        else outcomes.push(past);
    }
    if (opts.resume) console.error(`[mutate] resumed ${outcomes.length} outcome(s) from the history`);

    // Classified in candidate order, a batch at a time, so the sample a seed
    // selects does not depend on which worker finishes first.
    const viable: Mutant[] = [];
    let discarded = 0;
    for (let at = 0; at < pending.length && viable.length < target; at += workers.length) {
        const batch = pending.slice(at, at + workers.length);
        const kinds = await pool(workers, batch, async (mutant, worker) => {
            const restore = plant(worker, mutant);
            try {
                return await viability(worker, mutant, pristine);
            } finally {
                restore();
            }
        });
        batch.forEach((mutant, i) => {
            const kind = kinds[i];
            if (kind.kind === "viable") {
                if (viable.length < target) viable.push(mutant);
                return;
            }
            const outcome: Outcome = {
                mutant,
                status: kind.kind,
                detail: kind.kind === "stillborn" ? kind.detail : undefined,
                stages: [],
            };
            outcomes.push(outcome);
            remember(history, current, outcome, opts);
            discarded++;
        });
    }
    const drawn = (tier: Tier) => viable.filter(m => tierOf(m, history, current) === tier).length;
    console.error(
        `[mutate] ${viable.length} mutant(s) to test (${drawn(Tier.Weak)} weak before, ${drawn(Tier.New)} new, ` +
            `${drawn(Tier.Old) + drawn(Tier.Current)} repeat), ${discarded} discarded`,
    );

    const campaign: Campaign = { opts, history, pristine };
    let finished = 0;
    const tested = await pool(workers, viable, async (mutant, worker) => {
        const outcome = await run(worker, mutant, campaign);
        remember(history, current, outcome, opts);
        finished++;
        const by = killers(outcome).join(",") || "-";
        console.error(
            `[${pad(finished, 4)}/${viable.length}] ${outcome.status.padEnd(10)} ${by.padEnd(16)} ` +
                `${mutant.id}  ${mutant.source}  =>  ${mutant.mutated}`,
        );
        return outcome;
    });
    outcomes.push(...tested);

    // Every worker is back to the unmutated tree here, which the corpus needs.
    const unkilled = tested.filter(o =>
        // The witness calculator of a calculator-preserving mutant is the original one.
        (o.status === "survived" || o.status === "static") && !calculatorPreserving(o.mutant.op));
    if (opts.probe && unkilled.length > 0) {
        const roots = ROOTS.filter(r => unkilled.some(o => o.mutant.roots.includes(r)));
        const sizes = await pool(workers, roots, (root, w) => buildCorpus(w, root));
        console.error(
            `[mutate] input search over ${unkilled.length} mutant(s); rejected inputs: ` +
                roots.map((r, i) => `${r} ${sizes[i]}`).join(", "),
        );
        await pool(workers, unkilled, async (outcome, worker) => {
            const restore = plant(worker, outcome.mutant);
            try {
                outcome.probe = await probe(worker, outcome.mutant);
            } finally {
                restore();
            }
            remember(history, current, outcome, opts);
        });
    }

    fs.writeFileSync(REPORT, JSON.stringify({ seed: opts.seed, tier: opts.tier, stages: opts.stages, outcomes }, null, 2));
    // Each worker holds a compiled copy of every circuit the suites build.
    for (const w of workers) fs.rmSync(w.root, { recursive: true, force: true });
    summarize(outcomes, opts);

    // ===== verdict =====

    const accepted = readAccepted(ACCEPTED);
    const acceptedKeys = new Map(accepted.map(a => [keyOf(a), a]));
    const survivors = outcomes.filter(o => o.status === "survived");
    const allKeys = new Set(all.map(keyOf));
    const testedKeys = new Map(outcomes.map(o => [keyOf(o.mutant), o]));

    // A survivor is only a finding if every gate had the chance to reject it.
    const complete = STAGES.every(s => opts.stages.includes(s));
    const unexpected = survivors.filter(o => !acceptedKeys.has(keyOf(o.mutant)));
    const stale = accepted.filter(a => {
        const key = keyOf(a);
        if (!allKeys.has(key)) return true;
        const outcome = testedKeys.get(key);
        return complete && outcome !== undefined && outcome.status !== "survived";
    });
    const unexplained = accepted.filter(a => a.reason.trim() === "" && !stale.includes(a));

    if (opts.update) {
        if (!complete) throw new Error(`--update needs every gate: ${STAGES.join(", ")}`);
        const kept = accepted.filter(a => !stale.includes(a));
        const added: Accepted[] = unexpected.map(({ mutant: m }) => ({
            file: m.file, op: m.op, variant: m.variant, source: m.source, nth: m.nth, reason: "",
        }));
        writeAccepted(ACCEPTED, [...kept, ...added]);
        console.log(`\n  wrote ${path.relative(ROOT, ACCEPTED)}: ${added.length} added, ${stale.length} removed.`);
        if (added.length > 0) console.log("  Each new entry needs a `reason` before the gate passes.");
        return 0;
    }

    const statics = outcomes.filter(o => o.status === "static" && !calculatorPreserving(o.mutant.op));
    if (statics.length > 0) {
        console.log(`\n  rejected by static gates only (${statics.length}): no test runs into the defect`);
        for (const o of statics) console.log(`    [${killers(o).join(",")}] ${describe(o)}`);
    }
    const expected = outcomes.filter(o => o.status === "static" && calculatorPreserving(o.mutant.op)).length;
    if (expected > 0) {
        console.log(`\n  ${expected} mutant(s) that free a signal were rejected by lint` +
            (opts.matrix ? " and missed by the second-witness search" : "; --matrix asks the second-witness search too"));
    }
    if (survivors.length > 0) {
        console.log(`\n  survivors (${survivors.length}):`);
        for (const o of survivors) {
            const known = acceptedKeys.get(keyOf(o.mutant));
            console.log(`    ${describe(o)}`);
            if (known) console.log(`      accepted: ${known.reason}`);
        }
    }
    for (const a of stale) {
        const now = testedKeys.get(keyOf(a))?.status;
        console.log(`\n  STALE accepted survivor (${now ?? "no such mutant"}): ${a.file}  ${a.op}:${a.variant}  ${a.source}`);
    }
    for (const a of unexplained) {
        console.log(`\n  accepted survivor has no reason: ${a.file}  ${a.op}:${a.variant}  ${a.source}`);
    }

    console.log(`\n  report: ${path.relative(ROOT, REPORT)}`);
    // A sample also depends on the history, so a seed alone does not replay it.
    if (unexpected.length > 0) {
        console.log(`  re-run the survivors: just mutate --only ${unexpected.map(o => o.mutant.id).join(",")}`);
    }

    if (!complete) {
        console.log("\n  not every gate ran; survivors are not checked against the accepted list");
        return stale.length > 0 || unexplained.length > 0 ? 1 : 0;
    }
    if (unexpected.length > 0) {
        console.log(
            `\n  FAIL: ${unexpected.length} mutant(s) no gate rejects. Add a test that does, or accept ` +
                `with a reason: just mutate --update --only <ids>`,
        );
    }
    return unexpected.length > 0 || stale.length > 0 || unexplained.length > 0 ? 1 : 0;
}

main().then(
    code => process.exit(code),
    err => {
        console.error(err instanceof Error ? err.message : err);
        process.exit(2);
    },
);
