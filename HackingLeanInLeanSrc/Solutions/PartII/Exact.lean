import Lean.Meta.Basic
import Lean.Elab

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Tactic

syntax (name := exact_anyhow) "exact_anyhow" (ppSpace colGt term:max)* : tactic

@[tactic exact_anyhow]
def evalExactAnyhow : Tactic := fun stx =>
  match stx with
  | `(tactic| exact_anyhow $e $_*) =>
    closeMainGoalUsing (checkUnassigned := false)
      fun type => do
        let mvarCounterSaved := (← getMCtx).mvarCounter
        let r ← elabTermEnsuringType e type
        logUnassignedAndAbort (← filterOldMVars (← getMVars r) mvarCounterSaved)
        return r
  | _ => throwUnsupportedSyntax

example {A B C : Type} (f : A -> B -> C) (x : A) (y : B) : C := by
  apply f
  exact_anyhow x 42
    somehow
      anyhow rfl are we proving
  exact_anyhow y x x x x y
