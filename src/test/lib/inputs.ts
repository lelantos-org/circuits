// Plain-JSON input shapers shared by spec + fuzz tests.

import type { Field } from "../helpers";

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
        frontier_in: a.frontier.map(lvl => lvl.map(s => s.toString())),
    };
}

// Coefficient layout MUST match TreeUpdateBatch circuit:
//   [old_root, new_root, start_index, actual_count, cms[0..2*MAX_N-1]]
export function flattenTreeUpdateBatch(a: {
    oldRoot: Field; newRoot: Field;
    startIndex: number | bigint; actualCount: number | bigint;
    cms: Field[];
}): Field[] {
    return [
        a.oldRoot,
        a.newRoot,
        BigInt(a.startIndex),
        BigInt(a.actualCount),
        ...a.cms,
    ];
}
