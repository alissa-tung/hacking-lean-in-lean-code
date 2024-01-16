import Lean

open Lean PrettyPrinter Delaborator SubExpr

def foo : Nat → Nat := fun x => 42

@[delab app.foo]
def delabFoo : Delab := do
  `(1)

#check foo -- 1 : Nat → Nat
#check foo 13

def myid {α : Type} (x : α) := x

@[app_unexpander myid]
def unexpMyId : Unexpander
  -- hygiene disabled so we can actually return `id` without macro scopes etc.
  | `(myid $arg) => set_option hygiene false in `(sdsdwdsds $arg)
  | `(myid) => pure $ mkIdent `id
  | _ => throw ()

notation "const " x => fun x => x

#check myid
#check myid 1

declare_syntax_cat lang
syntax num   : lang
syntax ident : lang
syntax "let " ident " := " lang " in " lang: lang
syntax "[Lang| " lang "]" : term

inductive LangExpr
  | numConst : Nat → LangExpr
  | ident    : String → LangExpr
  | letE     : String → LangExpr → LangExpr → LangExpr

macro_rules
  | `([Lang| $x:num ]) => `(LangExpr.numConst $x)
  | `([Lang| $x:ident]) => `(LangExpr.ident $(Lean.quote (toString x.getId)))
  | `([Lang| let $x:ident := $v:lang in $b:lang]) => `(LangExpr.letE $(Lean.quote (toString x.getId)) [Lang| $v] [Lang| $b])

instance : Coe NumLit (TSyntax `lang) where
  coe s := ⟨s.raw⟩

instance : Coe Ident (TSyntax `lang) where
  coe s := ⟨s.raw⟩

-- LangExpr.letE "foo" (LangExpr.numConst 12)
--   (LangExpr.letE "bar" (LangExpr.ident "foo") (LangExpr.ident "foo")) : LangExpr
#check [Lang|
  let foo := 12 in
  let bar := foo in
  foo
]

@[app_unexpander LangExpr.numConst]
def unexpandNumConst : Unexpander
  | `(LangExpr.numConst $x:num) => `([Lang| $x])
  | _ => throw ()

@[app_unexpander LangExpr.ident]
def unexpandIdent : Unexpander
  | `(LangExpr.ident $x:str) =>
    let str := x.getString
    let name := mkIdent $ Name.mkSimple str
    `([Lang| $name])
  | _ => throw ()

@[app_unexpander LangExpr.letE]
def unexpandLet : Unexpander
  | `(LangExpr.letE $x:str [Lang| $v:lang] [Lang| $b:lang]) =>
    let str := x.getString
    let name := mkIdent $ Name.mkSimple str
    `([Lang| let $name := $v in $b])
  | _ => throw ()

-- [Lang| let foo := 12 in foo] : LangExpr
#check [Lang|
  let foo := 12 in foo
]

-- [Lang| let foo := 12 in let bar := foo in foo] : LangExpr
#check [Lang|
  let foo := 12 in
  let bar := foo in
  foo
]
