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
    buildLeaf,
    circuitSignals,
    dummyInputAt,
    dummyOutput,
    fiatShamirZ,
    flatten,
    coeffs,
    hornerEval,
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

export interface TxBuildArgs {
    inputs: SpentNote[];
    outputs: Note[];
    merkleRoot: Field;
    /** Defaults to DEFAULT_ASSET. Pass 0n explicitly for the all-dummy zero tx. */
    publicAssetId?: Field;
    /** Both default to 0n, the shielded-to-shielded case. */
    publicIn?: bigint;
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
            pk: derivePk(this.P, ownerNsk),
            rho,
            rcm: rho + 1n,
            rcv: rho + 2n,
            rcvDep: rho + 3n,
        };
    }

    // Insert a note into `tree`, returning a SpentNote with an empty proof;
    // `finalize` populates path and indices once the root is frozen. Leaf
    // format: Poseidon(TAG_LEAF, cm, cv_dep_x, cv_dep_y), the deposit anchor
    // pinning (asset, value) to the leaf.
    insert(tree: MerkleTree, n: Note, nsk: Field): SpentNote {
        const cm = commit(this.P, n);
        const assetGen = this.J.hashToAssetGen(n.asset);
        const cvDep = this.J.valueCommit(n.value, assetGen, n.rcvDep);
        const idx = tree.insert(buildLeaf(this.P, cm, cvDep));
        return {
            ...n, nsk, cm,
            nf: nullifier(this.P, nsk, n.rho, cm),
            leafIndex: idx,
            pathElements: [], pathIndices: [], isDummy: false,
        };
    }

    finalize(tree: MerkleTree, sn: SpentNote): SpentNote {
        const { pathElements, pathIndices } = tree.proof(sn.leafIndex);
        return { ...sn, pathElements, pathIndices };
    }

    // Build the JSON object the circuit consumes. The public asset generator is
    // derived in-circuit from publicAssetId.
    //
    // Output rho is forced to the derivation the circuit enforces,
    // rho = Poseidon(TAG_RHO, nullifier[0], out_index), overriding any note.rho
    // the caller supplied. Matches the SDK bundle builders.
    build(args: TxBuildArgs): TransactWitnessBundle {
        const nf0 = args.inputs[0].nf;
        // `Transact` takes exactly N_IN inputs and N_OUT outputs; a short
        // witness fails witness calculation. Unused slots take dummy inputs
        // (`is_dummy = 1`, bypassing the pk, Merkle and asset checks) and
        // value-0 output notes, which are real leaves and hash as such.
        const inputs = padInputs(this.P, this.depth, args.inputs);
        const padded = padOutputs(this.P, args.outputs);
        const outputs = padded.map((o, j) => ({ ...o, rho: buildRho(this.P, nf0, j) }));
        const outputClues = args.outputClues
            ? padClues(args.outputClues, outputs.length, this.clues)
            : outputs.map(() => this.clues.next());
        const outputAuxDigest = args.outputAuxDigest ?? TEST_AUX_DIGEST;
        const input = toCircomInput(this.P, this.J, {
            ...args,
            inputs,
            publicAssetId: args.publicAssetId ?? DEFAULT_ASSET,
            publicIn: args.publicIn ?? 0n,
            publicOut: args.publicOut ?? 0n,
            outputs,
            outputClues,
            outputAuxDigest,
        });
        // Derive the challenge from the coefficients, as the contract does.
        // `toCircomInput` defaults z to 1, at which PolyEval collapses to a
        // plain sum and y is permutation-invariant, so a TransactCompressN that
        // transposed two slots would still satisfy the suite. An explicit
        // `args.z` takes precedence.
        if (args.z !== undefined) input.z = args.z.toString();
        else rebindFiatShamir(input);
        return input;
    }

    newTree(): MerkleTree {
        return new MerkleTree(this.P, this.depth);
    }

    /**
     * Spend `scenario`'s inputs against its root into `outputs`.
     *
     * `build` with the scenario unpacked; `extra` carries the public buckets,
     * clues or a chosen challenge.
     */
    spend(
        scenario: Pick<Scenario, "root" | "inputs">,
        outputs: Note[],
        extra: Omit<TxBuildArgs, "inputs" | "outputs" | "merkleRoot"> = {},
    ): TransactWitnessBundle {
        return this.build({ ...extra, inputs: scenario.inputs, outputs, merkleRoot: scenario.root });
    }

    // ===== scenario factories =====
    //
    // Each builds a tree, freezes its root, then finalizes the proofs; the root
    // must be frozen before proofs are taken.

    /**
     * Insert `notes` into a fresh tree, freeze the root, then take the proofs.
     *
     * Order matters: `finalize` reads an authentication path, and a path taken
     * before the last insert authenticates against a stale root. `nsk` is one
     * owner for every note, or one per note.
     *
     * The base of every factory below; call it directly for pre-shaped notes (a
     * second asset, a blinder at its ceiling, mixed owners).
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
     * The two-in-two-out transfer the fuzz suites draw: both inputs owned by
     * `payer`, `o1` to `payee` and `o2` back to `payer`, nothing public.
     *
     * Returns the parts rather than the bundle, so a negative case can tamper a
     * note before `spend`; `transfer` builds it directly.
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

    /** `transferParts`, built. */
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
     * A balanced witness with two real inputs and two real outputs: 100 + 50 in,
     * 75 + 75 out, one owner, one asset, nothing public.
     *
     * The base for the tamper tests, which mutate a single field and expect
     * rejection, so it is honest in every respect but the field under test.
     */
    balanced(nsk: Field = ALICE_NSK): TransactWitnessBundle {
        return this.spend(
            this.twoRealInputs([100n, 50n], nsk),
            [this.note(75n, nsk, 9n), this.note(75n, nsk, 11n)],
        );
    }

    /**
     * `N_IN` real inputs and `N_OUT` real outputs, balanced: every slot the
     * shape declares holds a real note.
     *
     * `balanced()` and the scenario factories above fill at most two input and
     * two output slots, leaving the rest to `padInputs` / `padOutputs`. A dummy
     * input bypasses the key and Merkle checks and a padding output is
     * value-0, so a constraint that is mis-indexed for slot >= 2 — a loop bound
     * one short, a high slot left unconstrained — is satisfied by every witness
     * those factories produce. `src/4x6.circom` makes the same point about the
     * consumer's checks: they "must range over the whole shape".
     *
     * This is the base for the per-slot tamper expansion, which needs every
     * slot to carry the same constraints as slot 0 for the expectations to be
     * uniform across `i` and `j`.
     *
     * Values are distinct per slot so a witness that confuses two slots does
     * not balance by coincidence, and the rho seeds are spaced well apart so a
     * `+1` tamper on one slot's field cannot land on another slot's value.
     */
    fullShape(nsk: Field = ALICE_NSK): TransactWitnessBundle {
        assertFullShapeValues();
        const outputs = FULL_SHAPE_OUT_VALUES.map((v, j) =>
            this.note(v, nsk, 1_000_000n + BigInt(j) * 1_000n),
        );
        return this.spend(this.nRealInputs(FULL_SHAPE_IN_VALUES, nsk), outputs);
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

/**
 * Input and output values for `fullShape`, summing to the same total so the
 * witness balances.
 *
 * Distinct per slot, so a witness that reads one slot's value into another
 * changes that note's commitment rather than passing unnoticed.
 */
const FULL_SHAPE_IN_VALUES = [100n, 50n, 30n, 20n];
const FULL_SHAPE_OUT_VALUES = [60n, 50n, 40n, 30n, 15n, 5n];

/**
 * The two tables above are listed explicitly rather than generated, so a change
 * to `N_IN` or `N_OUT` leaves them the wrong length and `fullShape` would no
 * longer fill every slot. This check throws in that case.
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
 * Re-derive the Fiat-Shamir challenge `z` from the witness in its current state.
 *
 * Mirrors `lib/batch.ts :: rebindFiatShamir`. Call after mutating a
 * PolyEval-bound field when the test needs the challenge to describe the
 * witness it is evaluating; a tamper test expecting a constraint to fire does
 * not, since `z` carries no constraint of its own and a stale one only moves
 * the `y` the circuit outputs.
 */
export function rebindFiatShamir(input: TransactWitnessBundle): TransactWitnessBundle {
    return bindFiatShamir(input, calldataView(input));
}

/**
 * Snapshot a bundle's logical public inputs — the calldata view.
 *
 * A structural clone rather than a field-by-field copy, because unlike the batch
 * every field `flatten`/`coeffs` read is already a logical public input; there
 * is no private state in the bundle to exclude. The clone is deep, so the
 * caller can mutate one view without affecting the other.
 */
export function calldataView(w: TransactWitnessBundle): TransactWitnessBundle {
    return structuredClone(w);
}

/**
 * Bind `z` to a calldata view that may differ from the witness `w`, and return
 * `w`. `calldataY` computes the `y` the contract compares against.
 *
 * `rebindFiatShamir` combines two roles that are separate in deployment:
 * deriving the challenge and choosing the witness. `MASP` hashes its calldata
 * into `z` and compares its own `y`; the prover then picks any witness
 * satisfying the R1CS at that `z`. `z` is a circuit input known before the
 * witness is chosen, so Schwartz-Zippel does not apply and a word is bound only
 * if a constraint pins it (src/README.md § 2a).
 *
 * Mirrors `lib/batch.ts :: bindFiatShamir`. Use this to test whether the prover
 * can diverge from the contract's calldata, and `rebindFiatShamir` to test
 * whether a specific constraint fires.
 */
export function bindFiatShamir(
    w: TransactWitnessBundle,
    calldata: TransactWitnessBundle,
): TransactWitnessBundle {
    w.z = fiatShamirZ(flatten(calldata)).toString();
    return w;
}

/**
 * The `y` the contract computes for a calldata view at the bound challenge.
 *
 * `z` defaults to the view's own; pass one explicitly to evaluate a calldata
 * view at a challenge bound from elsewhere.
 */
export function calldataY(calldata: TransactWitnessBundle, z: Field = BigInt(calldata.z)): Field {
    return hornerEval(coeffs(calldata), z);
}

/**
 * Top up `inputs` to `N_IN` with dummies, distinct by `rho` so their nullifiers
 * differ.
 *
 * Pairwise distinctness is a consumer obligation, not a circuit constraint:
 * `Transact` places no relation between nullifier slots, and `src/4x6.circom`
 * assigns the pairwise check to the consumer (`MASP.sol`). Dummies are kept
 * distinct here so a witness matches what the SDK emits.
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
 * Top up `outputs` to `N_OUT` with value-0 notes.
 *
 * Each padding note is seeded by the slot it lands in, so no two share a
 * blinder and none commits to the identity point; see `dummyOutput`.
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
 * `TxBuilder.build` emits a `TransactWitnessBundle`: the circuit's signals plus
 * `recipient_address`, `chain_id`, `payer_address`, `relayer_address`,
 * `intent_hash`, the clue triples and `out_aux_digest`. Those are logical public
 * inputs but not signals of this circuit; they reach the proof through the
 * Fiat-Shamir challenge, not through `PolyEval`.
 *
 * The wasm calculator rejects an unknown key ("Signal recipient_address not
 * found"), and `expectWitnessFails` classifies that as a test bug rather than a
 * constraint firing, since a rejection test that accepts it would pass
 * vacuously. Every suite that feeds a bundle to a tester must therefore
 * project first; applying the projection at the `loadCircuit` call covers all
 * call sites.
 *
 * `circuitSignals` is an explicit pick, so this drops exactly the binding fields:
 * a signal added to the circuit but missing there fails with "Not all inputs
 * have been set" rather than being defaulted.
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
