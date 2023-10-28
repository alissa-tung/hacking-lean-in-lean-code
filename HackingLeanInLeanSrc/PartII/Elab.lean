import Lean

import Std.Tactic.ShowTerm

open Lean Elab Command Term Meta

syntax (name := output_cmd) "#output_cmd" : command

@[command_elab output_cmd]
def outputCmdImpl : CommandElab := fun _ =>
  logInfo "suppose"

#output_cmd

elab "#mycommand2" : command =>
  logInfo "Hello World"

#mycommand2

#check TermElab

#check Tactic.TacticM

elab "custom_sorry_1" : tactic =>
  Lean.Elab.Tactic.withMainContext do
  -- do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalDecl ← goal.getDecl
    let goalType := goalDecl.type
    dbg_trace s!"goal type: {goalType}"
    -- logInfo "x"
    -- logInfo s!"{goalDecl}"
    Lean.Elab.admitGoal goal

example : 1 = 2 := by
  show_term custom_sorry_1

-- example : Nat := by exact
