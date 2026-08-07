// Plain-JSON input shapers shared by spec + fuzz tests.

import type { Field, Point } from "../helpers";

export function merkleInputJson(leaf: Field, pathElements: Field[][], pathIndices: number[]) {
    return {
        leaf: leaf.toString(),
        path_elements: pathElements.map(lvl => lvl.map(s => s.toString())),
        path_indices: pathIndices.map(p => p.toString()),
    };
}

export interface TreeUpdateArgs {
    oldRoot: Field;
    newRoot: Field;
    cm0: Field;
    cm1: Field;
    startIndex: number;
    frontier: Field[][];
    z: Field;
}

export function treeUpdateInputJson(a: TreeUpdateArgs) {
    return {
        z: a.z.toString(),
        old_root: a.oldRoot.toString(),
        new_root: a.newRoot.toString(),
        cm0: a.cm0.toString(),
        cm1: a.cm1.toString(),
        start_index: a.startIndex.toString(),
        frontier_in: a.frontier.map(lvl => lvl.map(s => s.toString())),
    };
}

export interface TreeUpdateBatchArgs {
    oldRoot: Field;
    newRoot: Field;
    startIndex: number | bigint;
    actualCount: number | bigint;
    cms: Field[];
    cvDep: Point[];
    pairAsset: Field[];
    pairPublicIn: Field[];
    isDeposit: (number | bigint)[];
    rcvTotal: Field[];
    rcvDepPad: Field[];
    frontier: Field[][];
    z: Field;
}

export function treeUpdateBatchInputJson(a: TreeUpdateBatchArgs) {
    return {
        z: a.z.toString(),
        old_root: a.oldRoot.toString(),
        new_root: a.newRoot.toString(),
        start_index: a.startIndex.toString(),
        actual_count: a.actualCount.toString(),
        cms: a.cms.map(c => c.toString()),
        cv_dep: a.cvDep.map(p => [p[0].toString(), p[1].toString()]),
        pair_asset: a.pairAsset.map(p => p.toString()),
        pair_public_in: a.pairPublicIn.map(p => p.toString()),
        is_deposit: a.isDeposit.map(d => d.toString()),
        rcv_total: a.rcvTotal.map(r => r.toString()),
        rcv_dep_pad: a.rcvDepPad.map(r => r.toString()),
        frontier_in: a.frontier.map(lvl => lvl.map(s => s.toString())),
    };
}

// Coefficient layout MUST match TreeUpdateBatch circuit:
//   [old_root, new_root, start_index, actual_count,
//    cms[0..2*MAX_N-1],
//    cv_dep[0..2*MAX_N-1] flattened (x0,y0,x1,y1,...),
//    pair_asset[0..MAX_N-1],
//    pair_public_in[0..MAX_N-1],
//    is_deposit[0..MAX_N-1]]
// Total = 4 + 9*MAX_N coefficients.
export function flattenTreeUpdateBatch(a: {
    oldRoot: Field;
    newRoot: Field;
    startIndex: number | bigint;
    actualCount: number | bigint;
    cms: Field[];
    cvDep: Point[];
    pairAsset: Field[];
    pairPublicIn: Field[];
    isDeposit: (number | bigint)[];
}): Field[] {
    const out: Field[] = [
        a.oldRoot,
        a.newRoot,
        BigInt(a.startIndex),
        BigInt(a.actualCount),
        ...a.cms,
    ];
    for (const p of a.cvDep) {
        out.push(p[0]);
        out.push(p[1]);
    }
    for (const v of a.pairAsset) out.push(v);
    for (const v of a.pairPublicIn) out.push(v);
    for (const v of a.isDeposit) out.push(BigInt(v));
    return out;
}
