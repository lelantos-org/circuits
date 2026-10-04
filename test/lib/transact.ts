// Transact-circuit witness builders shared by the spec and fuzz suites.

import {
    Poseidon,
    Jubjub,
    MerkleTree,
    derivePk,
    commit,
    nullifier,
    buildRho,
    toCircomInput,
    deterministicClueGen,
    circuitSignals,
    dummyInputAt,
    dummyOutput,
    fiatShamirZ,
    flatten,
    coeffs,
    hornerEval,
    transactDigest,
    type TransactWitnessBundle,
    type ClueInputs,
    type Field,
    type Note,
    type SpentNote,
} from "../helpers";
import { ALICE_NSK, N_IN, N_OUT } from "./constants";
import type { CircuitInput, CircuitTester } from "./circuit";

// Default asset id, for tests that do not depend on which asset is in use.
export const DEFAULT_ASSET: Field = 7n;

// Stand-in for `auxDigest(aux)`. The tests build clue witnesses but no
// encrypted-note payload, and the circuit constrains this slot only through
// PolyEval. Non-zero, so a test that drops the field fails rather than matching
// a default.
export const TEST_AUX_DIGEST: Field = 0xa17d19e57n;

// Stand-in for a swap's intent hash in the published vectors. A full-width word
// (top bits set, still below r), so a consumer that masks the slot to an address
// or drops it fails.
export const TEST_INTENT_HASH: Field = 0x2f00000000000000000000000000000000000000000000000000000000c0ffeen;

/**
 * The diversifier `TxBuilder.note` derives `pk` under: a function of the note's
 * `rho`, so `TxBuilder.insert` recovers it. 128-bit and non-zero; distinct for
 * distinct `rho` below 2^127.
 */
export function diversifierOf(rho: Field): Field {
    return (1n << 127n) | (rho & ((1n << 127n) - 1n));
}

export interface TxBuildArgs {
    inputs: SpentNote[];
    outputs: Note[];
    merkleRoot: Field;
    /**
     * Defaults to the only value the circuit accepts for `publicOut`: 0n for a
     * transfer (`publicOut == 0`), DEFAULT_ASSET for a withdrawal. Pass it
     * explicitly to withdraw another asset or to build a rejected witness.
     */
    publicAssetId?: Field;
    /** Defaults to 0n, the shielded-to-shielded case. */
    publicOut?: bigint;
    outputClues?: ClueInputs[];
    outputAuxDigest?: Field;
    /**
     * Overrides the Fiat-Shamir derivation. For tests that need a chosen
     * challenge; leave unset so `build` derives it from the coefficients.
     */
    z?: Field;
}

export class TxBuilder {
    private readonly clues: ReturnType<typeof deterministicClueGen>;
    constructor(public readonly P: Poseidon, public readonly J: Jubjub, public readonly depth: number) {
        this.clues = deterministicClueGen(P, J);
    }

    note(value: bigint, ownerNsk: Field, rho: Field, asset: Field = DEFAULT_ASSET): Note {
        return {
            asset,
            value,
            pk: derivePk(this.P, ownerNsk, diversifierOf(rho)),
            rho,
            rcm: rho + 1n,
        };
    }

    // Insert a note into `tree`, returning a SpentNote with an empty proof;
    // `finalize` populates path and indices once the root is frozen. The leaf
    // is the note commitment itself. `d` defaults to the diversifier `note`
    // derives `pk` under.
    insert(tree: MerkleTree, n: Note, nsk: Field, d: Field = diversifierOf(n.rho)): SpentNote {
        const cm = commit(this.P, n);
        const idx = tree.insert(cm);
        return {
            ...n, nsk, d, cm,
            nf: nullifier(this.P, nsk, n.rho, cm),
            leafIndex: idx,
            pathElements: [], pathIndices: [], isDummy: false,
        };
    }

    finalize(tree: MerkleTree, sn: SpentNote): SpentNote {
        const { pathElements, pathIndices } = tree.proof(sn.leafIndex);
        return { ...sn, pathElements, pathIndices };
    }

    // Build the JSON object the circuit consumes.
    //
    // Output rho is forced to the derivation the circuit enforces,
    // rho = Poseidon(TAG_RHO, nullifier[0], out_index), overriding any note.rho
    // the caller supplied.
    build(args: TxBuildArgs): TransactWitnessBundle {
        const nf0 = args.inputs[0].nf;
        // `Transact` takes N_IN inputs and N_OUT outputs. Unused slots take
        // dummy inputs (`is_dummy = 1`, bypassing the Merkle and asset
        // checks) and value-0 output notes, which are real leaves.
        const inputs = padInputs(this.P, this.depth, args.inputs);
        const padded = padOutputs(this.P, args.outputs);
        const outputs = padded.map((o, j) => ({ ...o, rho: buildRho(this.P, nf0, j) }));
        const outputClues = args.outputClues
            ? padClues(args.outputClues, outputs.length, this.clues)
            : outputs.map(() => this.clues.next());
        const outputAuxDigest = args.outputAuxDigest ?? TEST_AUX_DIGEST;
        const publicOut = args.publicOut ?? 0n;
        const input = toCircomInput(this.P, {
            ...args,
            inputs,
            // The circuit requires asset 0 when nothing is withdrawn.
            publicAssetId: args.publicAssetId ?? (publicOut === 0n ? 0n : DEFAULT_ASSET),
            publicOut,
            outputs,
            outputClues,
            outputAuxDigest,
        });
        // Derive the challenge from the coefficients, as the contract does. At
        // `toCircomInput`'s default z = 1, PolyEval collapses to a plain sum
        // and y is permutation-invariant.
        if (args.z !== undefined) input.z = args.z.toString();
        else rebindFiatShamir(input);
        return input;
    }

    newTree(): MerkleTree {
        return new MerkleTree(this.P, this.depth);
    }

    /**
     * Spend `scenario`'s inputs against its root into `outputs`; `extra` carries
     * the public buckets, clues or a chosen challenge.
     */
    spend(
        scenario: Pick<Scenario, "root" | "inputs">,
        outputs: Note[],
        extra: Omit<TxBuildArgs, "inputs" | "outputs" | "merkleRoot"> = {},
    ): TransactWitnessBundle {
        return this.build({ ...extra, inputs: scenario.inputs, outputs, merkleRoot: scenario.root });
    }

    // ===== scenario factories =====

    /**
     * Insert `notes` into a fresh tree, freeze the root, then take the proofs: a
     * path taken before the last insert authenticates against a stale root.
     * `nsk` is one owner for every note, or one per note.
     */
    plant(notes: Note[], nsk: Field | readonly Field[]): Scenario {
        const owners = typeof nsk === "bigint" ? notes.map(() => nsk) : nsk;
        if (owners.length !== notes.length) {
            throw new Error(`plant: ${notes.length} notes but ${owners.length} owners`);
        }
        const tree = this.newTree();
        const inserted = notes.map((n, i) => this.insert(tree, n, owners[i]));
        const root = tree.root();
        return { tree, root, inputs: inserted.map(s => this.finalize(tree, s)) };
    }

    /** Two real inputs from one owner. */
    twoRealInputs(values: [bigint, bigint], nsk: Field, asset: Field = DEFAULT_ASSET): Scenario {
        return this.nRealInputs(values, nsk, asset, [1n, 2n]);
    }

    /** One real input plus a dummy: the withdraw / single-spend shape. */
    oneRealOneDummy(value: bigint, nsk: Field, asset: Field = DEFAULT_ASSET): Scenario {
        const scenario = this.plant([this.note(value, nsk, 1n, asset)], nsk);
        scenario.inputs.push(dummyInputAt(this.P, this.depth, 99n));
        return scenario;
    }

    /**
     * A two-in-two-out transfer: both inputs owned by `payer`, `o1` to `payee`
     * and `o2` back to `payer`, nothing public. Returns the parts so a negative
     * case can tamper a note before `spend`.
     */
    transferParts(
        split: Split,
        payer: Field,
        payee: Field,
        rhos: readonly [Field, Field, Field, Field] = [1n, 2n, 100n, 200n],
    ): { scenario: Scenario; outputs: Note[] } {
        const [rhoA, rhoB, rhoOA, rhoOB] = rhos;
        return {
            scenario: this.plant([this.note(split.v1, payer, rhoA), this.note(split.v2, payer, rhoB)], payer),
            outputs: [this.note(split.o1, payee, rhoOA), this.note(split.o2, payer, rhoOB)],
        };
    }

    transfer(
        split: Split,
        payer: Field,
        payee: Field,
        rhos?: readonly [Field, Field, Field, Field],
    ): TransactWitnessBundle {
        const { scenario, outputs } = this.transferParts(split, payer, payee, rhos);
        return this.spend(scenario, outputs);
    }

    /** Two dummy inputs against an empty tree: the deposit / all-dummy shape. */
    allDummyInputs(): Scenario {
        const tree = this.newTree();
        return {
            tree,
            root: tree.root(),
            inputs: [dummyInputAt(this.P, this.depth, 0n), dummyInputAt(this.P, this.depth, 1n)],
        };
    }

    /**
     * A balanced witness with two real inputs and two real outputs, one owner,
     * one asset, nothing public: the honest base the tamper tests mutate.
     */
    balanced(nsk: Field = ALICE_NSK): TransactWitnessBundle {
        return this.spend(
            this.twoRealInputs([100n, 50n], nsk),
            [this.note(75n, nsk, 9n), this.note(75n, nsk, 11n)],
        );
    }

    /**
     * `N_IN` real inputs and `N_OUT` real outputs, balanced: every slot holds a
     * real note. The base for the per-slot tamper expansion.
     *
     * The other factories fill at most two input and two output slots. A dummy
     * input bypasses the Merkle check and a padding output is value-0,
     * so a constraint mis-indexed for slot >= 2 is satisfied by every witness
     * they produce.
     *
     * Values are distinct per slot so a witness that confuses two slots does
     * not balance by coincidence, and the rho seeds are spaced so a `+1` tamper
     * on one slot's field cannot land on another slot's value.
     */
    fullShape(nsk: Field = ALICE_NSK): TransactWitnessBundle {
        assertFullShapeValues();
        const outputs = FULL_SHAPE_OUT_VALUES.map((v, j) =>
            this.note(v, nsk, 1_000_000n + BigInt(j) * 1_000n),
        );
        return this.spend(this.nRealInputs(FULL_SHAPE_IN_VALUES, nsk), outputs);
    }

    /**
     * `fullShape`, but every slot declares one of four distinct assets.
     *
     * `PerAssetValueBalance` sweeps N_CAND = N_IN + N_OUT + 1 = 11 candidate
     * assets. Under a single-asset witness the sweep collapses onto one row, so
     * a candidate that is never evaluated, or one evaluated against the wrong
     * slot, balances anyway. Here two of the four assets are split across
     * outputs, so each candidate carries a different sum.
     *
     * `publicAssetId` is left at its default, 0 for a transfer, which no note
     * declares: the public candidate row is then `0 == 0`, the orphan case.
     */
    fullShapeMultiAsset(nsk: Field = ALICE_NSK): TransactWitnessBundle {
        assertMultiAssetConserves();
        const inputs = MULTI_ASSET_IN.map(([asset, value], i) =>
            this.note(value, nsk, BigInt(i + 1) * 1_000n, asset),
        );
        const outputs = MULTI_ASSET_OUT.map(([asset, value], j) =>
            this.note(value, nsk, 1_000_000n + BigInt(j) * 1_000n, asset),
        );
        return this.spend(this.plant(inputs, nsk), outputs);
    }

    /**
     * `values.length` real inputs from one owner against a single frozen root.
     *
     * Generalises `twoRealInputs`; rho seeds default to multiples of 1000 so
     * that no `+1` tamper on one input's field collides with another's.
     */
    nRealInputs(
        values: bigint[],
        nsk: Field,
        asset: Field = DEFAULT_ASSET,
        rhos: readonly Field[] = values.map((_, i) => BigInt(i + 1) * 1_000n),
    ): Scenario {
        return this.plant(values.map((v, i) => this.note(v, nsk, rhos[i], asset)), nsk);
    }
}

/** A balanced two-in-two-out value split: `v1 + v2 == o1 + o2`. */
export interface Split {
    v1: bigint;
    v2: bigint;
    o1: bigint;
    o2: bigint;
}

/** Input and output values for `fullShape`: equal totals, distinct per slot. */
const FULL_SHAPE_IN_VALUES = [100n, 50n, 30n, 20n];
const FULL_SHAPE_OUT_VALUES = [60n, 50n, 40n, 30n, 15n, 5n];

/**
 * `(asset, value)` per input slot for `fullShapeMultiAsset`.
 *
 * Every value is non-zero: a zero-valued slot contributes nothing to its
 * candidate row, so relabelling its asset would still balance and a tamper
 * test on it would pass vacuously.
 */
export const MULTI_ASSET_IN: readonly (readonly [Field, bigint])[] = [
    [101n, 100n],
    [102n, 50n],
    [103n, 30n],
    [104n, 20n],
];

/** The outputs conserving the table above, splitting assets 101 and 104. */
export const MULTI_ASSET_OUT: readonly (readonly [Field, bigint])[] = [
    [101n, 60n],
    [101n, 40n],
    [102n, 50n],
    [103n, 30n],
    [104n, 15n],
    [104n, 5n],
];

/**
 * Check the two tables above for per-asset conservation, non-zero values and
 * lengths matching the shape: on an unbalanced base every rejection test would
 * pass vacuously.
 */
function assertMultiAssetConserves(): void {
    if (MULTI_ASSET_IN.length !== N_IN || MULTI_ASSET_OUT.length !== N_OUT) {
        throw new Error(
            `fullShapeMultiAsset: tables are ${MULTI_ASSET_IN.length}x${MULTI_ASSET_OUT.length} ` +
                `but the shape is ${N_IN}x${N_OUT}. Extend MULTI_ASSET_IN / MULTI_ASSET_OUT, ` +
                "keeping every asset conserved and every value non-zero.",
        );
    }
    const totals = new Map<bigint, bigint>();
    for (const [asset, value] of MULTI_ASSET_IN) {
        if (value === 0n) throw new Error(`fullShapeMultiAsset: input asset ${asset} has value 0`);
        totals.set(asset, (totals.get(asset) ?? 0n) + value);
    }
    for (const [asset, value] of MULTI_ASSET_OUT) {
        if (value === 0n) throw new Error(`fullShapeMultiAsset: output asset ${asset} has value 0`);
        totals.set(asset, (totals.get(asset) ?? 0n) - value);
    }
    for (const [asset, net] of totals) {
        if (net !== 0n) {
            throw new Error(`fullShapeMultiAsset: asset ${asset} is not conserved (net ${net})`);
        }
    }
}

/**
 * Throw if the `fullShape` value tables, which are literals, do not match
 * `N_IN` x `N_OUT` or do not balance.
 */
function assertFullShapeValues(): void {
    const sum = (xs: bigint[]) => xs.reduce((a, b) => a + b, 0n);
    if (FULL_SHAPE_IN_VALUES.length !== N_IN || FULL_SHAPE_OUT_VALUES.length !== N_OUT) {
        throw new Error(
            `fullShape: value tables are ${FULL_SHAPE_IN_VALUES.length}x` +
                `${FULL_SHAPE_OUT_VALUES.length} but the shape is ${N_IN}x${N_OUT}. ` +
                "Extend FULL_SHAPE_IN_VALUES / FULL_SHAPE_OUT_VALUES to match, keeping the sums equal.",
        );
    }
    if (sum(FULL_SHAPE_IN_VALUES) !== sum(FULL_SHAPE_OUT_VALUES)) {
        throw new Error("fullShape: input and output values must sum to the same total");
    }
}

/**
 * Re-derive the calldata digest and the Fiat-Shamir challenge `z` from the
 * witness in its current state: what an honest prover submits for it.
 *
 * Call after mutating a PolyEval-bound field when the test needs the calldata
 * to describe the witness. A tamper test expecting a constraint to fire does
 * not: neither word carries a constraint of its own, and a stale one only
 * moves the `y` the circuit outputs.
 *
 * The digest is refreshed first because it is a word of the challenge
 * preimage. The circuit takes no digest input and outputs its own.
 */
export function rebindFiatShamir(input: TransactWitnessBundle): TransactWitnessBundle {
    input.digest = transactDigest(input).toString();
    return bindFiatShamir(input, calldataView(input));
}

/**
 * Snapshot a bundle's logical public inputs: the calldata view. The clone is
 * deep, so the caller can mutate one view without affecting the other.
 */
export function calldataView(w: TransactWitnessBundle): TransactWitnessBundle {
    return structuredClone(w);
}

/**
 * Bind `z` to a calldata view that may differ from the witness `w`, and return
 * `w`. `calldataPublic` computes the other two public signals the contract
 * hands the verifier.
 *
 * In deployment `MASP` hashes its calldata into `z`, compares its own `y`, and
 * passes the calldata digest word to the verifier; the prover then picks any
 * witness satisfying the R1CS at that `z`. `z` is a circuit input known before
 * the witness is chosen; the digest public signal is what commits the
 * witness's coefficients before it (src/README.md § 2a).
 *
 * The view's `digest` is used as it stands. A divergence case that rewrites a
 * coefficient chooses whether to leave the digest stale or recompute it;
 * neither may verify.
 *
 * Use this to test whether the prover can diverge from the contract's
 * calldata, and `rebindFiatShamir` to test whether a specific constraint fires.
 */
export function bindFiatShamir(
    w: TransactWitnessBundle,
    calldata: TransactWitnessBundle,
): TransactWitnessBundle {
    w.z = fiatShamirZ(flatten(calldata)).toString();
    return w;
}

/**
 * The `y` the contract computes for a calldata view at challenge `z`, which
 * defaults to the view's own.
 */
export function calldataY(calldata: TransactWitnessBundle, z: Field = BigInt(calldata.z)): Field {
    return hornerEval(coeffs(calldata), z);
}

/**
 * The public signals the contract hands the verifier beside `z`, for a calldata
 * view at the bound challenge: its own `y`, and its digest word as given.
 */
export function calldataPublic(
    calldata: TransactWitnessBundle,
    z: Field = BigInt(calldata.z),
): { y: Field; digest: Field } {
    return { y: calldataY(calldata, z), digest: BigInt(calldata.digest) };
}

/**
 * Top up `inputs` to `N_IN` with dummies, distinct by `rho` so their nullifiers
 * differ.
 *
 * Pairwise distinctness is a consumer obligation, not a circuit constraint:
 * `Transact` places no relation between nullifier slots, and `src/4x6.circom`
 * assigns the pairwise check to the consumer (`MASP.sol`).
 */
function padInputs(P: Poseidon, depth: number, inputs: SpentNote[]): SpentNote[] {
    if (inputs.length > N_IN) {
        throw new Error(`padInputs: ${inputs.length} inputs exceeds N_IN = ${N_IN}`);
    }
    const out = [...inputs];
    // Offset well clear of the rho values the scenario factories hand out.
    for (let k = out.length; k < N_IN; k++) out.push(dummyInputAt(P, depth, 1000n + BigInt(k)));
    return out;
}

/**
 * Top up `outputs` to `N_OUT` with value-0 notes. Each padding note's `rcm` is
 * seeded by the slot it lands in; see `dummyOutput`.
 */
function padOutputs(P: Poseidon, outputs: Note[]): Note[] {
    if (outputs.length > N_OUT) {
        throw new Error(`padOutputs: ${outputs.length} outputs exceeds N_OUT = ${N_OUT}`);
    }
    const out = [...outputs];
    while (out.length < N_OUT) out.push(dummyOutput(P, out.length));
    return out;
}

/** Top up a caller-supplied clue list to match the padded output count. */
function padClues(
    clues: ClueInputs[],
    count: number,
    gen: ReturnType<typeof deterministicClueGen>,
): ClueInputs[] {
    const out = [...clues];
    while (out.length < count) out.push(gen.next());
    return out;
}

/** A frozen tree plus the finalized inputs spent from it. */
export interface Scenario {
    tree: MerkleTree;
    root: Field;
    inputs: SpentNote[];
}

/**
 * Wrap a tester so it drops the challenge-only fields before the witness
 * calculator sees them.
 *
 * A `TransactWitnessBundle` carries the circuit's signals plus `digest`,
 * `recipient_address`, `chain_id`, `payer_address`, `relayer_address`,
 * `intent_hash`, the clue triples and `out_aux_digest`. Those are logical public
 * inputs but not input signals of this circuit: the circuit outputs its own
 * digest, and the rest reach the proof through the Fiat-Shamir challenge, not
 * through `PolyEval`. The wasm calculator rejects an unknown key, and
 * `expectWitnessFails` classifies that as a test bug rather than a constraint
 * firing.
 *
 * `circuitSignals` is an explicit pick: a signal added to the circuit but
 * missing there fails with "Not all inputs have been set" rather than being
 * defaulted.
 */
export function projectingTester(c: CircuitTester): CircuitTester {
    return {
        calculateWitness: (input: CircuitInput, sanityCheck?: boolean) =>
            c.calculateWitness(
                circuitSignals(input as unknown as TransactWitnessBundle) as unknown as CircuitInput,
                sanityCheck,
            ),
        checkConstraints: w => c.checkConstraints(w),
        assertOut: (w, e) => c.assertOut(w, e),
    };
}

/** Re-exported so suites import their transact vocabulary from one module. */
import { buildJubjub } from "./harness";
export { dummyInputAt, dummyOutput };

export async function buildTxBuilder(depth: number): Promise<TxBuilder> {
    const [P, J] = await Promise.all([Poseidon.build(), buildJubjub()]);
    return new TxBuilder(P, J, depth);
}
