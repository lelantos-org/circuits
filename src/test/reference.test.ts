// Unit tests for `ref/`, the reference implementation the published vectors are
// generated from.
//
// These cover the parts of `ref/` that no circuit test can reach. Anything a
// circuit consumes is checked transitively — a wrong Poseidon or asset generator
// makes commitments disagree with circom and fails a constraint. The values
// below have no such backstop:
//
//   - `z` is an unconstrained circuit input, so an incorrect ABI encoding
//     produces a witness the circuit accepts and a challenge the contract
//     recomputes differently.
//   - The FMD clue signals carry no in-circuit constraints at all.
//   - `rootFromPath` and `cacheKeyStride` have no circuit counterpart.

import { expect } from "chai";

import { TIMEOUT_FAST } from "./lib/constants";
import { readFileSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";

import { keccak_256 } from "@noble/hashes/sha3";

import {
    Poseidon,
    Jubjub,
    MerkleTree,
    rootFromPath,
    cacheKeyStride,
    legendreSymbol,
    modSqrt,
    fmdGenDetectionKey,
    fmdTest,
    encodeClue,
    decodeClue,
    deterministicClueGen,
    abiEncodeCoeffs,
    fiatShamirZ,
    hornerEval,
    BN254_FR,
    FMD_LEGENDRE_QNR,
    FMD_DEFAULT_GAMMA,
} from "./helpers";

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), "../..");

describe("reference / merkle path recomputation", function () {
    this.timeout(TIMEOUT_FAST);

    let P: Poseidon;
    before(async () => {
        P = await Poseidon.build();
    });

    // `rootFromPath` is a second implementation of the same quaternary node
    // hashing as `MerkleTree`. Its value is that the two are independent, which
    // only holds if something checks they agree.
    for (const depth of [2, 10]) {
        it(`rootFromPath reproduces MerkleTree.root() at every leaf (depth ${depth})`, () => {
            const tree = new MerkleTree(P, depth);
            const n = depth === 2 ? 16 : 21;
            for (let i = 0; i < n; i++) tree.insert(BigInt(1000 + i));

            const root = tree.root();
            for (let i = 0; i < n; i++) {
                const { pathElements, pathIndices } = tree.proof(i);
                expect(
                    rootFromPath(P, tree.leaves[i], pathElements, pathIndices),
                    `leaf ${i} of ${n} at depth ${depth}`,
                ).to.equal(root);
            }
        });
    }

    it("rootFromPath rejects a perturbed sibling", () => {
        const tree = new MerkleTree(P, 10);
        for (let i = 0; i < 5; i++) tree.insert(BigInt(500 + i));
        const { pathElements, pathIndices } = tree.proof(0);
        pathElements[0][0] += 1n;
        expect(rootFromPath(P, tree.leaves[0], pathElements, pathIndices)).to.not.equal(tree.root());
    });

    // The node cache is keyed by `level * stride + index`. If the stride does not
    // exceed the widest level's index range, a level-1 key collides with a
    // level-2 key and the tree returns a wrong root.
    it("cacheKeyStride keeps (level, index) keys injective for every supported depth", () => {
        for (let depth = 1; depth <= 25; depth++) {
            const stride = cacheKeyStride(depth);
            for (let level = 1; level <= depth; level++) {
                // Largest index reachable at this level.
                const maxIndex = 4 ** (depth - level) - 1;
                expect(
                    maxIndex,
                    `depth ${depth}, level ${level}: index range overruns the stride`,
                ).to.be.lessThan(stride);
            }
            expect(depth * stride + 1, `depth ${depth} exceeds MAX_SAFE_INTEGER`).to.be.lessThan(
                Number.MAX_SAFE_INTEGER,
            );
        }
    });

    // `fillConstant` seeds the node cache instead of hashing every internal
    // node, so it is only sound while it agrees with a naive fill of the same
    // leaves — including the frontier, which reads the seeded siblings.
    it("fillConstant agrees with a naive constant fill (root and frontier)", () => {
        const C = 0xdeadn;
        for (const depth of [1, 2, 3]) {
            const capacity = 4 ** depth;
            for (let n = 0; n <= capacity; n++) {
                const naive = new MerkleTree(P, depth);
                for (let i = 0; i < n; i++) naive.insert(C);

                const fast = new MerkleTree(P, depth);
                fast.fillConstant(n, C);

                const where = `depth ${depth}, n ${n}`;
                expect(fast.root(), `root at ${where}`).to.equal(naive.root());
                expect(fast.frontier(), `frontier at ${where}`).to.deep.equal(naive.frontier());

                // The prefill is only ever a base for further inserts, so the
                // post-insert state has to agree too.
                if (n < capacity) {
                    naive.insert(7n);
                    fast.insert(7n);
                    expect(fast.root(), `root after insert at ${where}`).to.equal(naive.root());
                    expect(fast.frontier(), `frontier after insert at ${where}`)
                        .to.deep.equal(naive.frontier());
                }
            }
        }
    });

    // Depth 10 is the production shape and the one the frontier fuzz suite
    // prefills near capacity; a naive fill there is ~350k hashes, so this
    // checks the boundary values rather than every n.
    it("fillConstant agrees with a naive fill at depth 10 boundary counts", () => {
        const C = 0xdeadn;
        for (const n of [0, 1, 3, 4, 5, 15, 16, 17, 63, 64, 21, 1023, 1024, 4097]) {
            const naive = new MerkleTree(P, 10);
            for (let i = 0; i < n; i++) naive.insert(C);
            const fast = new MerkleTree(P, 10);
            fast.fillConstant(n, C);
            expect(fast.root(), `root at n ${n}`).to.equal(naive.root());
            expect(fast.frontier(), `frontier at n ${n}`).to.deep.equal(naive.frontier());
        }
    });

    it("fillConstant rejects a count outside 0..4^depth", () => {
        const tree = new MerkleTree(P, 3);
        expect(() => tree.fillConstant(-1, 1n)).to.throw(RangeError);
        expect(() => tree.fillConstant(65, 1n)).to.throw(RangeError);
        expect(() => tree.fillConstant(1.5, 1n)).to.throw(RangeError);
    });

    it("cacheKeyStride grows past the depth-10 value", () => {
        // A stride fixed at 2^18 is exact at depth 10 and one short at depth 11,
        // where the largest level-1 index is 4^10 - 1.
        expect(cacheKeyStride(10)).to.equal(2 ** 18);
        expect(cacheKeyStride(11)).to.be.greaterThan(4 ** 10 - 1);
    });
});

describe("reference / quadratic residues", () => {
    it("FMD_LEGENDRE_QNR is a non-residue in BN254 Fr", () => {
        // The FMD bit gadget needs a public non-residue; if this were a square
        // the bit derivation would not be balanced.
        expect(legendreSymbol(FMD_LEGENDRE_QNR, BN254_FR)).to.equal(-1);
    });

    it("legendreSymbol classifies squares and non-squares", () => {
        for (const x of [1n, 2n, 3n, 7n, 123456789n, 1n << 200n]) {
            const sq = (x * x) % BN254_FR;
            expect(legendreSymbol(sq, BN254_FR), `square of ${x}`).to.equal(1);
            expect(
                legendreSymbol((sq * FMD_LEGENDRE_QNR) % BN254_FR, BN254_FR),
                `QNR times square of ${x}`,
            ).to.equal(-1);
        }
        expect(legendreSymbol(0n, BN254_FR)).to.equal(0);
    });

    it("modSqrt inverts squaring", () => {
        for (const x of [1n, 2n, 3n, 7n, 123456789n, 1n << 200n]) {
            const sq = (x * x) % BN254_FR;
            const root = modSqrt(sq, BN254_FR);
            expect(root, `no root for the square of ${x}`).to.not.equal(null);
            expect((root! * root!) % BN254_FR).to.equal(sq);
        }
        expect(modSqrt(0n, BN254_FR)).to.equal(0n);
        expect(modSqrt(FMD_LEGENDRE_QNR, BN254_FR), "a non-residue has no root").to.equal(null);
    });
});

describe("reference / fuzzy message detection", function () {
    this.timeout(TIMEOUT_FAST);

    let P: Poseidon;
    let J: Jubjub;
    before(async () => {
        [P, J] = await Promise.all([Poseidon.build(), Jubjub.build()]);
    });

    // The clue signals have no in-circuit constraints, so the scheme's own
    // correctness is not covered anywhere else.
    it("a detection key detects every clue flagged for its flag key", () => {
        const gen = deterministicClueGen(P, J);
        for (let i = 0; i < 32; i++) {
            expect(fmdTest(J, P, gen.dk, gen.next().clue), `clue ${i}`).to.equal(true);
        }
    });

    it("flipping any clue bit breaks detection", () => {
        const gen = deterministicClueGen(P, J);
        const clue = gen.next().clue;
        for (let i = 0; i < FMD_DEFAULT_GAMMA; i++) {
            const bits = Uint8Array.from(clue.bits);
            bits[i >> 3] ^= 1 << (i & 7);
            expect(fmdTest(J, P, gen.dk, { ...clue, bits }), `bit ${i} flipped`).to.equal(false);
        }
    });

    it("an unrelated detection key matches at the false-positive rate, not universally", () => {
        const gen = deterministicClueGen(P, J);
        const other = fmdGenDetectionKey(() => 99991n, FMD_DEFAULT_GAMMA);

        const N = 128;
        let matched = 0;
        for (let i = 0; i < N; i++) {
            if (fmdTest(J, P, other, gen.next().clue)) matched++;
        }
        // Expected N / 2^gamma = 4. The bound is loose because the security
        // property is that detection is rate-limited, not that it never fires.
        expect(matched, `${matched}/${N} matched an unrelated detection key`).to.be.lessThan(N / 8);
    });

    it("a detection key of the wrong gamma is rejected", () => {
        const gen = deterministicClueGen(P, J);
        const short = fmdGenDetectionKey(() => 7n, FMD_DEFAULT_GAMMA - 1);
        expect(fmdTest(J, P, short, gen.next().clue)).to.equal(false);
    });

    it("encodeClue and decodeClue round-trip", () => {
        const gen = deterministicClueGen(P, J);
        for (let i = 0; i < 4; i++) {
            const clue = gen.next().clue;
            const back = decodeClue(encodeClue(clue));
            expect(back.gamma).to.equal(clue.gamma);
            expect(Buffer.from(back.R).toString("hex")).to.equal(
                Buffer.from(clue.R).toString("hex"),
            );
            expect(Buffer.from(back.bits).toString("hex")).to.equal(
                Buffer.from(clue.bits).toString("hex"),
            );
        }
    });
});

describe("reference / snark compression", () => {
    const CASES: bigint[][] = [
        [1n],
        [1n, 2n, 3n],
        Array.from({ length: 31 }, (_, i) => BigInt(i + 1) * 1000003n),
        Array.from({ length: 100 }, (_, i) => BigInt(i) ** 3n + 7n),
    ];

    // `abi.encode(uint256[])` is
    //   32-byte offset (0x20) || 32-byte length || N x 32-byte big-endian.
    // The circuit places no constraint on `z`, so an error here is invisible to
    // witness generation and surfaces only when the contract recomputes `z`.
    it("abiEncodeCoeffs matches the abi.encode(uint256[]) layout", () => {
        for (const coeffs of CASES) {
            const enc = abiEncodeCoeffs(coeffs);
            expect(enc.length, "total length").to.equal(64 + coeffs.length * 32);

            const word = (i: number) => {
                let v = 0n;
                for (const b of enc.subarray(i * 32, i * 32 + 32)) v = (v << 8n) | BigInt(b);
                return v;
            };
            expect(word(0), "head must be the 0x20 offset word").to.equal(0x20n);
            expect(word(1), "length word").to.equal(BigInt(coeffs.length));
            coeffs.forEach((c, i) => {
                expect(word(2 + i), `element ${i} must be big-endian`).to.equal(c);
            });
        }
    });

    it("fiatShamirZ is keccak256 over that preimage, reduced mod r", () => {
        for (const coeffs of CASES) {
            let v = 0n;
            for (const b of keccak_256(abiEncodeCoeffs(coeffs))) v = (v << 8n) | BigInt(b);
            expect(fiatShamirZ(coeffs)).to.equal(v % BN254_FR);
        }
    });

    // Regression pin. Independently reproducible with
    //   cast keccak $(cast abi-encode 'f(uint256[])' '[1,2,3]')
    // reduced mod the BN254 scalar field.
    it("fiatShamirZ([1,2,3]) is unchanged", () => {
        expect(fiatShamirZ([1n, 2n, 3n]).toString()).to.equal(
            "949944173773553631396417664205921158114683290423144883256233788818757206298",
        );
    });

    // The vectors record `abiEncodedCoeffs` so the contract side can localise a
    // mismatch to the encoding; recomputing it here checks the published value.
    //
    // Driven from index.json, so a shape change (a new circuit, or a different
    // MAX_L) is covered without editing this file.
    const INDEX = JSON.parse(readFileSync(resolve(ROOT, "vectors/index.json"), "utf8"));
    const VECTOR_FILES: string[] = Object.keys(INDEX.files);

    it("index.json lists every published vector file", () => {
        expect(VECTOR_FILES.length, "no vector files listed").to.be.greaterThan(0);
    });

    for (const file of VECTOR_FILES) {
        it(`vectors/${file} is internally consistent`, () => {
            const v = JSON.parse(readFileSync(resolve(ROOT, "vectors", file), "utf8"));
            for (const vec of v.vectors) {
                const coeffs = vec.compression.coeffs.map(BigInt);
                const where = `${file} :: ${vec.name}`;

                expect(coeffs.length, `${where}: coefficient count`).to.equal(v.circuit.coeffCount);
                expect(
                    "0x" + Buffer.from(abiEncodeCoeffs(coeffs)).toString("hex"),
                    `${where}: recorded ABI preimage`,
                ).to.equal(vec.compression.abiEncodedCoeffs);
                expect(fiatShamirZ(coeffs).toString(), `${where}: z`).to.equal(vec.compression.z);
                expect(
                    hornerEval(coeffs, BigInt(vec.compression.z)).toString(),
                    `${where}: y`,
                ).to.equal(vec.compression.y);
                // Recorded separately by the generator: what the compiled circuit emitted.
                expect(vec.circuitOutput.y, `${where}: circuit y`).to.equal(vec.compression.y);
            }
        });
    }
});
