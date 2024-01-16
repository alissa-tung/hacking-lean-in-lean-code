import Mathlib.Topology.MetricSpace.Basic

open Std.ExtendedBinder
open Topology

syntax "lim " extBinder " → " term ", " term " ≡ " term:50 : term
macro_rules
  | `(lim $x:ident → $x0, $f ≡ $y) => `(Filter.Tendsto (fun $x ↦ $f) (𝓝 $x0) (𝓝 $y))

lemma foo [MetricSpace α] [MetricSpace β] {f : α → β} {a b} :
    lim x → a, f x ≡ b ↔ ∀ ε > 0, ∃ δ > 0, ∀ {x : α}, dist x a < δ → dist (f x) b < ε :=
  Metric.tendsto_nhds_nhds

#check foo

open Lean PrettyPrinter.Delaborator SubExpr in
@[delab app.Filter.Tendsto] def delabLim : Delab := do
  let #[_, _, f, l₁, l₂] := (← getExpr).getAppArgs | failure
  guard <| f.isLambda
  guard <| l₁.isAppOfArity' ``nhds 3 -- (1) same as (3)
  guard <| l₂.isAppOfArity' ``nhds 3 -- (2) same as (4)
  let (i, body) ← withNaryArg 2 <| withBindingBodyUnusedName fun i => do
    return (i, ← delab)
  let x0 ← withNaryArg 3 do
    let e ← getExpr
    guard <| e.isAppOfArity' ``nhds 3 -- (3) same as (1)
    withNaryArg 2 delab
  let y ← withNaryArg 4 do
    let e ← getExpr
    guard <| e.isAppOfArity' ``nhds 3 -- (4) same as (2)
    withNaryArg 2 delab
  `(lim $(.mk i):ident → $x0, $body ≡ $y)

#check foo
