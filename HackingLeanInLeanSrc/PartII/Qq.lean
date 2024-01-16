import Qq


import Lean
open Lean Lean.Meta Lean.Elab

open Qq
set_option trace.compiler.ir.result true in

-- Note: `betterApp` actually has two additional parameters
-- `{u v : Lean.Level}` auto-generated due to option
-- `autoBoundImplicitLocal`.

def betterApp {α : Q(Sort $u)} {β : Q($α → Sort $v)}
    (f : Q((a : $α) → $β a)) (a : Q($α)) : Q($β $a) :=
  q($f $a)

#eval betterApp q(Nat.succ) q(Nat.zero)

#check betterApp (β := q(fun n : Nat => Fin (n+1))) q(fun a => ⟨a, Nat.lt_succ_self _⟩) q(42)

#check Expr.const

#check PUnit


#check Syntax
#check Expr


#eval q(PUnit.{1})

#check Lean.Expr.lam `x (Lean.Expr.const `Nat []) (Lean.Expr.const `Nat.zero []) (Lean.BinderInfo.default)
#eval q(fun (x : Nat) => Nat.zero)
