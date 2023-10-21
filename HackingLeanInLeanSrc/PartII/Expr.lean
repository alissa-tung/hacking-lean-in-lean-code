import Lean

open Lean Meta

-- 1 + 2
def one : Expr :=
  Expr.app (Expr.app (Expr.const `Nat.add []) (mkNatLit 1)) (mkNatLit 2)

elab "one" : term => return one
#check one  -- Nat.add 1 2 : Nat
#reduce one -- 3

-- 1 + 2
def two : Expr :=
  Lean.mkAppN (Expr.const `Nat.add []) #[mkNatLit 1, mkNatLit 2]

elab "two" : term => return two
#check two  -- Nat.add 1 2 : Nat
#reduce two -- 3

-- f 0 1 2
def Example.Expr.f : Nat -> Nat -> Nat -> Nat :=
  fun x y z => x + y + z

def two' : Expr :=
  Lean.mkAppN
    (Expr.const ``Example.Expr.f [])
    #[mkNatLit 0, mkNatLit 1, mkNatLit 2]

elab "two'" : term => return two'
#check two'  -- Nat.add 1 2 : Nat
#reduce two' -- 3

-- fun x => 1 + x
def three : Expr :=
  Expr.lam `x (Expr.const `Nat [])
  (Lean.mkAppN (Expr.const `Nat.add []) #[Lean.mkNatLit 1, Expr.bvar 0])
  BinderInfo.default

elab "three" : term => return three
#check three    -- fun x => Nat.add 1 x : Nat → Nat
#reduce three 6 -- 7

-- fun a, fun b, fun c, (b * a) + c
def four : Expr :=
  Expr.lam `a (Expr.const `Nat [])
  (
    Expr.lam `b (Expr.const `Nat [])
    (
      Expr.lam `c (Expr.const `Nat [])
      (
        Lean.mkAppN
        (Expr.const `Nat.add [])
        #[
          (Lean.mkAppN (Expr.const `Nat.mul []) #[Expr.bvar 1, Expr.bvar 2]),
          (Expr.bvar 0)
        ]
      )
      BinderInfo.default
    )
    BinderInfo.default
  )
  BinderInfo.default

elab "four" : term => return four
#check four -- fun a b c => Nat.add (Nat.mul b a) c : Nat → Nat → Nat → Nat
#reduce four 666 1 2 -- 668

def eight : Expr :=
  Expr.forallE `notUsed
  (Expr.const `Nat []) (Expr.const `String [])
  BinderInfo.default

elab "eight" : term => return eight
#check eight  -- Nat → String : Type
#reduce eight -- Nat → String

-- let x : Nat := 2; Nat.succ x
def exampleLet := Expr.letE `x (.const `Nat []) (.lit (.natVal 2)) (.app (.const `Nat.succ []) (.bvar 0)) true

elab "exampleLet" : term => return exampleLet
#check exampleLet
#reduce exampleLet
