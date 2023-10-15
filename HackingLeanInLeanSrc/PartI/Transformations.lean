import Mathlib.Logic.Equiv.Defs

import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.Basic

def id' {A : Type _} (x : A) : A := x

def id'' : {A : Type _} -> (x : A) -> A := fun x => x

def id''' {A : Type _} (x : A) : A := by
  exact x

def id'''' : {A : Type _} -> (x : A) -> A := by
  intro _ x
  exact x

def with_default (x : Int) (y : Int := 42) : Int := x + y

#eval with_default 0
#eval with_default 1 2

#check Equiv

instance subring_is_module
  {S : Type _} [Ring S]
  {R : Subring S} : Module R S where
  add_smul := by
    intro r s x
    apply add_smul
  zero_smul := by
    intro x
    rw [zero_smul]

instance subring_is_module'
  {S : Type _} [Ring S]
  {R : Subring S} : Module R S :=
  { add_smul := by
    intro r s x
    apply add_smul
  , zero_smul := by
    intro x
    rw [zero_smul]
  }

instance subring_is_module''
  {S : Type _} [Ring S]
  {R : Subring S} : Module R S := by
  constructor
  sorry
  sorry
  -- { add_smul := by
  --   intro r s x
  --   apply add_smul
  -- , zero_smul := by
  --   intro x
  --   rw [zero_smul]
  -- }
