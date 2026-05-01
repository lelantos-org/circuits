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
