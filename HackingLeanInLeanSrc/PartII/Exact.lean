import Lean.Meta.Basic
import Lean.Elab

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Tactic

syntax (name := exact') "exact' " term : tactic

@[tactic exact']
def evalExact' : Tactic := fun stx =>
  match stx with
  | `(tactic| exact' $e:term) =>
    closeMainGoalUsing (checkUnassigned := false)
      fun type => do
        let mvarCounterSaved := (← getMCtx).mvarCounter
        let r ← elabTermEnsuringType e type
        logUnassignedAndAbort (← filterOldMVars (← getMVars r) mvarCounterSaved)
        return r
  | _ => throwUnsupportedSyntax

example {A B C : Type} (f : A -> B -> C) (x : A) (y : B) : C := by
  apply f
  exact' x
  exact' y

-- If we have two parsers `xs` and `ys`,
-- the parser `xs ys` will first run parsing `xs`, then run parsing `ys`.
-- The parser `(xs ys)*` will run parsing `xs ys` zero or more times,
-- as long as parse succeed.

-- The parser `ppSpace` will parse spaces and line breaks,
-- the parser `colGt` requires that the next token starts a strictly
-- greater column than the current position,
-- the parser `term:max` suggests maximum precedence used in term parsers.

-- Please write a tactic to make the following example work.

-- HINT: in pattern matching arm, you need to consider the case
-- that `exact_anyhow` takes one and more arguments, which syntax
-- is similar to the one for parse many `p*`

-- example {A B C : Type} (f : A -> B -> C) (x : A) (y : B) : C := by
--   apply f
--   exact_anyhow x 42
--     somehow
--       anyhow rfl are we proving
--   exact_anyhow y x x x x y
