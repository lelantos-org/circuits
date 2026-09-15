import Lelantos

/-!
# Environment-wide axiom guard

`Lelantos.Meta.Assumptions` prints the axiom dependencies of the headline theorems, and
`lean/scripts/check-axioms.sh` diffs that output against `expected/axioms.txt`; that check
covers only the theorems listed there.

This module checks every declaration in the `Lelantos` namespace against an allow-list at
build time. Adding an axiom, or admitting a proof (which surfaces as `sorryAx`), fails
`lake build`.

The allow-list is the trusted base. This file defines what is permitted;
`Lelantos.Meta.Assumptions` documents each entry. Keep the two in sync.
-/

open Lean

namespace Lelantos.Meta.AxiomGuard

/-- Lean's own axioms. Not assumptions about the circuit. -/
private def leanAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- Arithmetic facts that Mathlib cannot decide at these bit widths, discharged externally
by `lean/scripts/check-prime.py`. -/
private def arithmeticAxioms : List Name :=
  [``Lelantos.p_prime, ``Lelantos.ell_prime]

/-- Curve and gadget semantics: the Baby Jubjub group law, the scalar-multiplication
gadgets, the two Pedersen bases, and the known discrete log of the asset generators.

`coords_injective` is permitted but reaches no headline theorem: its only consumer lifts the
point equation into the group, which has no consumers. See `Lelantos.Model.Jubjub`. -/
private def curveAxioms : List Name :=
  [``Lelantos.coords_injective, ``Lelantos.babyAdd, ``Lelantos.babyAdd_spec,
   ``Lelantos.escalarMul, ``Lelantos.escalarMul_spec, ``Lelantos.H, ``Lelantos.BASE0,
   ``Lelantos.assetMul, ``Lelantos.assetMul_arith]

/-- The complete trusted base. It contains no hash axiom; `Lelantos.poseidon_not_injective`
shows that an injectivity axiom would be inconsistent. -/
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
      it, or — if it is intended — add it to `Lelantos.Meta.AxiomGuard.allowed` and document it\n\
      in `Lelantos.Meta.Assumptions`, in the same commit."

end Lelantos.Meta.AxiomGuard
