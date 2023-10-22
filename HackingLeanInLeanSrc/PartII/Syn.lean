import Lean

open Lean Elab Command Term Meta

-- XOR, denoted \oplus
infixl:60 " ⊕ " => fun l r => (!l && r) || (l && !r)

#eval true ⊕ true -- false
#eval true ⊕ false -- true
#eval false ⊕ true -- true
#eval false ⊕ false -- false

-- with `notation`, "left XOR"
-- notation:10 l:10 " LXOR " r:11 => (!l && r)

syntax (name := lxor) term " LXOR " term : term

-- @[macro lxor]
-- def lxorImpl : Macro := fun stx =>
--   match stx with
--   | `($l:term LXOR $r:term) => `(!$l:term && $r:term)
--   | _ => Macro.throwUnsupported

macro_rules
  | `($l:term LXOR $r:term) => `(!$l:term && $r:term)

macro_rules
  | `($l:term LXOR $r:term) => `(!$l:term || $r:term)

macro l:term:10 " LXOR' " r:term:11 : term => `(!$l:term && $r:term)

#eval true LXOR true -- false
#eval true LXOR false -- false
#eval false LXOR true -- true
#eval false LXOR false -- false

#eval  true LXOR true LXOR false
#eval (true LXOR true) LXOR false
#eval true LXOR (true LXOR false)
#eval true ⊕ false LXOR false -- false
#eval (true ⊕ false) LXOR false -- false
#eval true ⊕ (false LXOR false) -- true

notation:65 lhs:65 " ~ " rhs:60 => (lhs - rhs)

#eval 5 ~ 3 ~ 3 -- 5
#eval (5 ~ 3) ~ 3 -- 0
#eval 5 ~ (3 ~ 3) -- 5

-- false true : term

declare_syntax_cat boolean_expr
syntax "⊥" : boolean_expr -- ⊥ for false
syntax "⊤" : boolean_expr -- ⊤ for true
syntax:40 boolean_expr " OR " boolean_expr : boolean_expr
syntax:50 boolean_expr " AND " boolean_expr : boolean_expr

open Lean

def isAdd11 : Syntax → Bool
  | `(term| Nat.add 1 1) => true
  | `(boolean_expr| ⊥) => true
  -- | `(tactic| exact $x) => _
  | _ => false

#eval isAdd11 (Syntax.mkApp (mkIdent `Nat.add) #[Syntax.mkNumLit "1", Syntax.mkNumLit "1"]) -- true
#eval isAdd11 (Syntax.mkApp (mkIdent `Nat.add) #[mkIdent `foo, Syntax.mkNumLit "1"]) -- false
-- #eval isAdd11 (mkIdent `(boolean_expr| ⊥))

def isAdd : Syntax → Option (Syntax × Syntax)
  | `(Nat.add $x $y) => some (x, y)
  | _ => none

#eval isAdd (Syntax.mkApp (mkIdent `Nat.add) #[Syntax.mkNumLit "1", Syntax.mkNumLit "1"]) -- some ...
#eval isAdd (Syntax.mkApp (mkIdent `Nat.add) #[mkIdent `foo, Syntax.mkNumLit "1"]) -- some ...
#eval isAdd (Syntax.mkApp (mkIdent `Nat.add) #[mkIdent `foo]) -- none

-- Now we are also explicitly marking the function to operate on term syntax
def isLitAdd : TSyntax `term → Option Nat
  | `(Nat.add $x:num $y:num) => some (x.getNat + y.getNat)
  | _ => none

#eval isLitAdd (Syntax.mkApp (mkIdent `Nat.add) #[Syntax.mkNumLit "1", Syntax.mkNumLit "1"]) -- some 2
#eval isLitAdd (Syntax.mkApp (mkIdent `Nat.add) #[mkIdent `foo, Syntax.mkNumLit "1"]) -- none

declare_syntax_cat arith

syntax num : arith
syntax arith "-" arith : arith
syntax arith "+" arith : arith
syntax "(" arith ")" : arith

partial def denoteArith : TSyntax `arith → Nat
  | `(arith| $x:num) => x.getNat
  | `(arith| $x:arith + $y:arith) => denoteArith x + denoteArith y
  | `(arith| $x:arith - $y:arith) => denoteArith x - denoteArith y
  | `(arith| ($x:arith)) => denoteArith x
  | _ => 0

-- You can ignore Elab.TermElabM, what is important for us is that it allows
-- us to use the ``(arith| (12 + 3) - 4)` notation to construct `Syntax`
-- instead of only being able to match on it like this.
def test : Elab.TermElabM Nat := do
  let stx ← `(arith| (12 + 3) - 4)
  pure (denoteArith stx)

#eval test -- 11

syntax (name := p0) "good morning" : term
syntax (name := p1) "hello" : command
syntax (name := p2) "yellow" : tactic

-- Note: when the following are highlighted in red, however that's just because we haven't implemented the semantics ("elaboration function") yet - the syntax parsing stage works.

open Lean Elab Meta Term Command Tactic

@[command_elab p1]
def p1Impl : CommandElab := fun _ => return

@[term_elab p0]
def p0Impl : TermElab := fun _ _ => return mkNatLit 0

-- @[tactic p2]
-- def p2Impl : Tactic := fun _ => return

macro_rules
  | `(tactic| yellow) => `(tactic| rfl)

#eval good morning -- works
-- good morning -- error: `expected command`

hello -- works
-- #eval hello -- error: `expected term`

example : 2 + 2 = 4 := by
  yellow -- works
-- yellow -- error: `expected command`
-- #eval yellow -- error: `unknown identifier 'yellow'`

-- syntax (name := lxor) term " LXOR " term : term

-- @[macro lxor]
-- def lxorImpl : Macro := fun stx =>
--   match stx with
--   | `($l:term LXOR $r:term) => `(!$l:term && $r:term)
--   | _ => Macro.throwUnsupported

syntax (name := cmd_output) "#cmd_output" : command

#check Macro

@[command_elab cmd_output]
def cmdOutputImpl : CommandElab := fun stx =>
  match stx with
  | `(command| #cmd_output) => do
      logInfo "first elab cmd"
  | _ => throwUnsupportedSyntax

#cmd_output

elab "cmd_output" x:term : command => do
  logInfo f!"{x}"

cmd_output 42

#check (1 + 1)

#check 42

-- elab "#check" x:term : command => do
--   match x with
--   | `(term| $x:num) => logInfo "test"
--   | _ => throwUnsupportedSyntax

elab "#check" "mycheck" : command => do
  logInfo "Got ya!"

@[command_elab Lean.Parser.Command.check]
def mySpecialCheck : CommandElab := fun stx => do
  if let some str := stx[1].isStrLit? then
    logInfo s!"Specially elaborated string literal!: {str} : String"
  else
    throwUnsupportedSyntax

#check unfold

#check "test"

-- example : Nat := by
--   unfold
