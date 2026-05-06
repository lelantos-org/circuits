import { expect } from "chai";

import {
    BABYJUB_SUBGROUP_ORDER,
    BN254_FR,
    fmdLegendreWitness,
    Jubjub,
    Poseidon,
} from "@lelantos-org/sdk/crypto";
import { TAG_FMD_BIT } from "@lelantos-org/sdk";
import { fixturePath, loadCircuit } from "./lib/circuit";
import { expectWitnessFails } from "./lib/expect";

const WRAPPER = fixturePath("test_clue.circom");
const GAMMA = 5;

interface ClueWitness {
    r: bigint;
    fk: [bigint, bigint][];
    clue_bits: bigint;
    legendre_bit: number[];
    legendre_y: bigint[];
    Rx: bigint;
    Ry: bigint;
}

function mod(a: bigint, p: bigint): bigint {
    const r = a % p;
    return r < 0n ? r + p : r;
}

// Build an honest ClueCheck witness off-circuit, matching `sharedBit` in
// sdk/src/fmd.ts byte-for-byte: c_bits[i] === 1 - legendre_bit_i.
function buildHonestWitness(
    J: Jubjub,
    P: Poseidon,
    r: bigint,
    dkScalars: bigint[],
): ClueWitness {
    const rMod = mod(r, BABYJUB_SUBGROUP_ORDER);
    const R = J.mulPointEscalar(J.base8, rMod);
    const fk = dkScalars.map((x) => J.mulPointEscalar(J.base8, x)) as [bigint, bigint][];

    const legendre_bit: number[] = [];
    const legendre_y: bigint[] = [];
    let cBitsPacked = 0n;
    for (let i = 0; i < GAMMA; i++) {
        const S = J.mulPointEscalar(fk[i], rMod);
        const h = P.hash([TAG_FMD_BIT, R[0], R[1], BigInt(i), S[0], S[1]]);
        const w = fmdLegendreWitness(h);
        legendre_bit.push(w.bit);
        legendre_y.push(w.y);
        const c = 1 - w.bit; // sender flips
        if (c) cBitsPacked |= 1n << BigInt(i);
    }

    return {
        r: rMod,
        fk,
        clue_bits: cBitsPacked,
        legendre_bit,
        legendre_y,
        Rx: R[0],
        Ry: R[1],
    };
}

function toInput(w: ClueWitness): any {
    return {
        r: w.r.toString(),
        fk: w.fk.map(([x, y]) => [x.toString(), y.toString()]),
        clue_bits: w.clue_bits.toString(),
        legendre_bit: w.legendre_bit.map((b) => b.toString()),
        legendre_y: w.legendre_y.map((y) => y.toString()),
    };
}

describe("ClueCheck (FMD2 in-circuit bit derivation)", function () {
    this.timeout(300000);

    let circuit: any;
    let J: Jubjub;
    let P: Poseidon;

    before(async () => {
        J = await Jubjub.build();
        P = await Poseidon.build();
        circuit = await loadCircuit(WRAPPER);
    });

    it("accepts honest witness; Rx/Ry match r·G_8", async () => {
        const r = 0xdeadbeefcafebaben % BABYJUB_SUBGROUP_ORDER;
        const dk = [11n, 22n, 33n, 44n, 55n];
        const w = buildHonestWitness(J, P, r, dk);
        const wt = await circuit.calculateWitness(toInput(w), true);
        await circuit.assertOut(wt, { Rx: w.Rx.toString(), Ry: w.Ry.toString() });
    });

    it("works across multiple seeds (γ=5 independence)", async () => {
        for (const seed of [1n, 2n, 7n, 12345n]) {
            const r = mod(seed * 0x9e3779b97f4a7c15n + 1n, BABYJUB_SUBGROUP_ORDER);
            const dk = Array.from({ length: GAMMA }, (_, i) =>
                mod(seed + BigInt(i + 1) * 101n, BABYJUB_SUBGROUP_ORDER),
            );
            const w = buildHonestWitness(J, P, r, dk);
            await circuit.calculateWitness(toInput(w), true);
        }
    });

    it("flipping one clue_bit breaks only that index (independence)", async () => {
        const r = 1234567n % BABYJUB_SUBGROUP_ORDER;
        const dk = [3n, 5n, 7n, 9n, 11n];
        const w = buildHonestWitness(J, P, r, dk);
        for (let i = 0; i < GAMMA; i++) {
            const tampered = { ...w, clue_bits: w.clue_bits ^ (1n << BigInt(i)) };
            await expectWitnessFails(circuit, toInput(tampered));
        }
    });

    it("rejects tampered legendre_bit", async () => {
        const r = 999n;
        const dk = [2n, 4n, 6n, 8n, 10n];
        const w = buildHonestWitness(J, P, r, dk);
        const tampered = {
            ...w,
            legendre_bit: w.legendre_bit.map((b, i) => (i === 0 ? 1 - b : b)),
        };
        await expectWitnessFails(circuit, toInput(tampered));
    });

    it("rejects wrong legendre_y witness", async () => {
        const r = 4242n;
        const dk = [1n, 2n, 3n, 4n, 5n];
        const w = buildHonestWitness(J, P, r, dk);
        const tampered = {
            ...w,
            legendre_y: w.legendre_y.map((y, i) => (i === 0 ? mod(y + 1n, BN254_FR) : y)),
        };
        await expectWitnessFails(circuit, toInput(tampered));
    });

    it("rejects tampered fk point (changes shared secret ⇒ wrong bits)", async () => {
        const r = 7777n;
        const dk = [10n, 20n, 30n, 40n, 50n];
        const w = buildHonestWitness(J, P, r, dk);
        // Replace fk[2] with a different valid subgroup point (dk=99·G_8).
        const newFk = J.mulPointEscalar(J.base8, 99n);
        const tampered = {
            ...w,
            fk: w.fk.map((p, i) => (i === 2 ? (newFk as [bigint, bigint]) : p)),
        };
        await expectWitnessFails(circuit, toInput(tampered));
    });

    it("rejects r ≥ BN254 scalar prime (Num2Bits_strict guard)", async () => {
        // r = p (BN254 scalar field) violates strict range check.
        const w = buildHonestWitness(J, P, 1n, [1n, 1n, 1n, 1n, 1n]);
        const tampered = { ...w, r: BN254_FR };
        await expectWitnessFails(circuit, toInput(tampered));
    });

    it("rejects when sender omits flip (clue_bits === legendre_bit)", async () => {
        const r = 555n;
        const dk = [13n, 17n, 19n, 23n, 29n];
        const w = buildHonestWitness(J, P, r, dk);
        // Pack legendre_bit (no XOR with 1) into clue_bits — what a buggy
        // sender that forgot the FMD2 flip would do.
        let unflipped = 0n;
        for (let i = 0; i < GAMMA; i++) {
            if (w.legendre_bit[i]) unflipped |= 1n << BigInt(i);
        }
        if (unflipped === w.clue_bits) return; // all bits 0 — skip rare case
        await expectWitnessFails(circuit, toInput({ ...w, clue_bits: unflipped }));
    });
});
