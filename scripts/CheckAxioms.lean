import ShearerTriangleFreeInd
import Lean.Util.CollectAxioms

/-!
Check the transitive axiom dependencies of both main theorems.
Run with `lake env lean scripts/CheckAxioms.lean` after `lake build`.
-/

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let theorems : Array Name := #[
    `SimpleGraph.triangle_free_independence_bound,
    `SimpleGraph.triangle_free_independence_count_bound]
  for theoremName in theorems do
    unless (← getEnv).contains theoremName do
      throwError m!"Main theorem not found: {theoremName}"
    let axioms ← collectAxioms theoremName
    let unexpected := axioms.filter fun axiomName ↦ !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{theoremName} depends on unexpected axioms: {unexpected.toList}"
    logInfo m!"{theoremName} depends only on standard axioms: {axioms.toList}"
