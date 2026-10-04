import Lelantos

/-!
# Environment-wide axiom guard

Checks every declaration in the `Lelantos` namespace against an allow-list at build time:
adding an axiom, or admitting a proof (which surfaces as `sorryAx`), fails `lake build`.
`lean/scripts/check-axioms.sh` covers only the theorems `Lelantos.Meta.Assumptions` lists.

The allow-list is the trusted base; `Lelantos.Meta.Assumptions` documents each entry. Keep
the two in sync.
-/

open Lean

namespace Lelantos.Meta.AxiomGuard

/-- Lean's own axioms. Not assumptions about the circuit. -/
private def leanAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- The one arithmetic fact Mathlib cannot decide at this bit width, discharged externally
by `lean/scripts/check-prime.py`. -/
private def arithmeticAxioms : List Name :=
  [``Lelantos.p_prime]

/-- The complete trusted base. It contains no hash axiom: `Lelantos.poseidon_not_injective`
shows that an injectivity axiom would be inconsistent. -/
def allowed : List Name := leanAxioms ++ arithmeticAxioms

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
