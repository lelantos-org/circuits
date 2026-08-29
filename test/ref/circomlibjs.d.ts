// circomlibjs ships no type declarations.
//
// These are intentionally untyped. Field elements are Uint8Array in Montgomery
// form and are structurally indistinguishable from plain little-endian byte
// arrays, so a richer signature here would imply a static guarantee that does
// not exist. `ref/jubjub.ts` is the sole consumer and validates at runtime.

declare module "circomlibjs" {
    export function buildBabyjub(): Promise<any>;
    export function buildPedersenHash(): Promise<any>;
    export function buildPoseidon(): Promise<any>;
    export function buildPoseidonOpt(): Promise<any>;
    export function buildPoseidonReference(): Promise<any>;
    export function buildEddsa(): Promise<any>;
    export function buildMimc7(): Promise<any>;
    export function buildMimcSponge(): Promise<any>;
    export function buildSMT(): Promise<any>;
    export function newMemEmptyTrie(): Promise<any>;
}
