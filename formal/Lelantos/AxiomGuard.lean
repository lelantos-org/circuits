import Lelantos

/-!
# Environment-wide axiom guard

`Lelantos.Assumptions` prints the axiom dependencies of the headline theorems, and
`scripts/check-axioms.sh` diffs that output against `expected-axioms.txt`. That guard is
only as good as the list of theorems someone remembered to add to it: a new result proved
from a new axiom is invisible to it.

This module closes that gap by checking **every** declaration in the `Lelantos` namespace
against an allow-list, at build time. Adding an axiom — or admitting a proof, which surfaces
as `sorryAx` — fails `lake build` rather than merely failing to appear in a diff.

The allow-list is the trusted base. This file decides what is permitted;
`Lelantos.Assumptions` documents why each entry is on the list. Keep the two in sync.
-/

open Lean

namespace Lelantos.AxiomGuard

/-- Lean's own axioms. Not assumptions about the circuit. -/
private def leanAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- Arithmetic facts that Mathlib cannot decide at these bit widths, discharged externally
by `scripts/check-prime.py`. -/
private def arithmeticAxioms : List Name :=
  [``Lelantos.p_prime, ``Lelantos.ell_prime]

/-- Curve and gadget semantics: the Baby Jubjub group law, the scalar-multiplication
gadgets, the two Pedersen bases, and the known discrete log of the asset generators. -/
private def curveAxioms : List Name :=
  [``Lelantos.coords_injective, ``Lelantos.babyAdd, ``Lelantos.babyAdd_spec,
   ``Lelantos.escalarMul, ``Lelantos.escalarMul_spec, ``Lelantos.H, ``Lelantos.BASE0,
   ``Lelantos.assetMul, ``Lelantos.assetMul_arith]

/-- The complete trusted base. Note what is *absent*: there is no hash axiom, and
`Lelantos.poseidon_not_injective` is the reason one cannot be added. -/
def allowed : List Name := leanAxioms ++ arithmeticAxioms ++ curveAxioms

/-- Every declaration this development introduces, excluding compiler-generated ones. -/
private def ownDeclarations (env : Environment) : Array Name :=
  env.constants.fold (init := #[]) fun acc name _ =>
    if (`Lelantos).isPrefixOf name && !name.isInternal then acc.push name else acc

run_cmd do
  let env ← Elab.Command.liftCoreM getEnv
  let mut violations : Array (Name × Name) := #[]
  for decl in ownDeclarations env do
    let axioms ← Elab.Command.liftCoreM (collectAxioms decl)
    for ax in axioms do
      unless allowed.contains ax do
        violations := violations.push (decl, ax)
  unless violations.isEmpty do
    let rendered := violations.map fun (d, a) => s!"  {d} depends on {a}"
    throwError "\n\
      Axiom guard failed. These declarations depend on axioms outside the trusted base:\n\
      {String.intercalate "\n" rendered.toList}\n\n\
      `sorryAx` means a proof was admitted. Any other name means an axiom was added: remove\n\
      it, or — if it is intended — add it to `Lelantos.AxiomGuard.allowed` and document it\n\
      in `Lelantos.Assumptions`, in the same commit."

end Lelantos.AxiomGuard
