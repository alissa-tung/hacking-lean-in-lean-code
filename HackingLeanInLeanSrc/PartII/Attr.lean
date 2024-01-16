-- https://github.com/leanprover/lean4/tree/master/tests/pkg/user_attr/UserAttr

import Lean
open Lean

syntax (name := foo) "foo " ident : attr

initialize fooRef : IO.Ref (Array (Name × Name)) ← IO.mkRef #[]

def fooAttr : AttributeImpl where
  name := `foo
  descr := "foo"
  add
  | declName, stx, attrKind => do
    fooRef.modify fun foos => foos.push (declName, stx.isNameLit?.get!)

#eval show CoreM Unit from do
  match registerAttributeOfDecl (← getEnv) (← getOptions) ``fooAttr with
  | Except.ok env => setEnv env
  | Except.error e => throwError e

initialize blaAttr : TagAttribute ← registerTagAttribute `bla "simple user defined attribute"

/-- My own new simp attribute. -/
register_simp_attr my_simp

syntax (name := fooo) "foo" num "important"? : attr

initialize foooAttr : ParametricAttribute (Nat × Bool) ←
  registerParametricAttribute {
    name := `fooo
    descr := "parametric attribute containing a priority and flag"
    getParam := fun _ stx =>
      match stx with
      | `(attr| foo $prio:num $[important%$imp]?) =>
        return (prio.getNat, imp.isSome)
      | _  => throwError "unexpected foo attribute"
    afterSet := fun declName _ => do
      IO.println s!"set attribute [foo] at {declName}"
  }


-- register_simp_attr my_simp

