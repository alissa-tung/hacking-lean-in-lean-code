import Mathlib.Tactic

#check (· ∘ ·)
#check funext

-- {A B} {f g : A -> B}
-- ∀ (x : A) → f x = g x
-- f = g

structure Isomorphism (A B : Type*) where
  -- intro ::
  toFun  : A -> B
  invFun : B -> A
  inv_comp_to : (x : A) -> invFun (toFun  x) = x -- invFun ∘ toFun = id
  to_comp_inv : (y : B) -> toFun  (invFun y) = y

infix:0 " ≃I " =>
  fun lhs rhs =>
    Isomorphism lhs rhs

namespace Isomorphism

variable {A B C : Type*}

def someNat : Isomorphism A A -> ℕ := fun _ => 42

#check Isomorphism A B
#check A ≃I B

-- def refl : A ≃I A where -- instance
--     toFun  := id
--     invFun := id
--     inv_comp_to := fun _ => rfl
--     to_comp_inv := fun _ => rfl

-- where
-- := { k := v }

-- def refl : A ≃I A :=
--   ⟨ id
--   , id
--   , fun _ => rfl
--   , fun _ => rfl
--   ⟩

example : (4 : Nat) + 4 = 8 := by
  show 8 = 8
  rfl

#check Isomorphism.mk

def refl : A ≃I A := by
  -- (fun lhs rhs => Isomorphism lhs rhs) A A
  show Isomorphism A A
  constructor -- apply Isomorphism.mk
  repeat pick_goal 3; exact id
  -- pick_goal 3; exact id
  repeat intro _; dsimp
  -- intro _; dsimp


-- def sym : Isomorphism A B -> Isomorphism B A := fun xs => {
--   toFun  := xs.invFun
--   invFun := xs.toFun
--   inv_comp_to := xs.to_comp_inv
--   to_comp_inv := xs.inv_comp_to
-- }

def sym : (A ≃I B) -> (B ≃I A) := fun xs => {
  toFun  := xs.2
  invFun := xs.1
  inv_comp_to := xs.4
  to_comp_inv := xs.3
}

def trans : Isomorphism A B -> Isomorphism B C -> Isomorphism A C := fun xs ys => {
  toFun  := ys.toFun  ∘ xs.toFun
  invFun := xs.invFun ∘ ys.invFun
  inv_comp_to := by
    intro _
    dsimp
    rw [ys.inv_comp_to, xs.inv_comp_to]
  to_comp_inv := by
    intro _
    dsimp
    rw [xs.to_comp_inv, ys.to_comp_inv]
}

end Isomorphism

#check Isomorphism.someNat

def natIso : Isomorphism ℕ ℕ := Isomorphism.refl

#eval Isomorphism.someNat natIso
#eval natIso.someNat

-- Conjunction is product

-- A ∧ B
-- x : A
-- y : B
-- ⟨x, y⟩ : A ∧ B

#check Prod
-- structure Prod (α : Type u) (β : Type v) where
  -- fst : α
  -- snd : β

inductive Prod' (A B : Type*) where
  | prod' : A
         -> B
    -----------------
         -> Prod' A B

example {A B : Type*} : Isomorphism (Prod A B) (Prod' A B) := by
  -- constructor
  -- repeat
  --   pick_goal 3
  --   rintro ⟨x, y⟩
  --   exact  ⟨x, y⟩
  -- repeat intro _; simp
  constructor
  repeat
    pick_goal 3
    rintro ⟨x, y⟩
    exact  ⟨x, y⟩
  repeat intro _; dsimp

def proj_l {A B : Type*} : A × B → A :=
  fun ⟨x, _⟩ =>
    x

def proj_r {A B : Type*} : A × B → B :=
  fun ⟨_, y⟩ =>
    y

-- A × B → A
-- A × B → B
-- A + B <- A
-- A + B <- B

-- A -> A + B
-- B -> A + B

example {A B : Type*} : A × B → A := by
  rintro ⟨x, _⟩
  assumption

inductive Coprod (A B : Type*) where -- Sum
  | inl : A -> Coprod A B
  | inr : B -> Coprod A B

variable {A B C D : Type*}

-- f : ℝ × ℝ → R
-- f(x,y)
-- f : ℝ → ℝ → ℝ
-- f x y

def currying : (A -> B -> C) ≃I (A × B -> C) where
  toFun  := fun f ⟨x, y⟩ => f  x  y
  invFun := fun f  x  y  => f ⟨x, y⟩
  inv_comp_to := fun _ => rfl
  to_comp_inv := fun _ => rfl

#check (0 : Fin 1)
#check (2 : Fin 4)

-- #check (0 : Fin 2)
-- #check (1 : Fin 2)
-- #check (2 : Fin 2)
-- #check (3 : Fin 2)

def count_or : Coprod (Fin 2) (Fin 3) -> ℕ -- Coprod 2 3 => 5
  | .inl 0 => 1
  | .inl 1 => 2
  | .inr 0 => 3
  | .inr 1 => 4
  | .inr 2 => 5

def count_and : Fin 2 × Fin 3 -> ℕ -- Prod 2 3 => 6
  | ⟨0, 0⟩ => 1
  | ⟨0, 1⟩ => 2
  | ⟨0, 2⟩ => 3
  | ⟨1, 0⟩ => 4
  | ⟨1, 1⟩ => 5
  | ⟨1, 2⟩ => 6

inductive TopI where
  | truth : TopI

inductive BotI where

def bot_elim {A : Type*} : BotI -> A := by
  intro x
  rcases x

-- ⊥ ∧ A = ⊥
example {A : Type*} : (BotI × A) ≃I BotI := by
  show Isomorphism (BotI × A) BotI
  constructor
  pick_goal 3
  · rintro ⟨x, _⟩; exact x
  pick_goal 3
  · intro x
    apply bot_elim
    assumption
  · rintro ⟨x, y⟩
    dsimp
    rcases x
  intro y
  dsimp
  rcases y

#check Not

def NotI (A : Type*) := A → BotI



-- example {A : Type*} : Coprod TopI A ≃I TopI := by
--   show Isomorphism (Coprod TopI A) TopI
--   constructor
--   pick_goal 3
--   · rintro (l | r)
--     · assumption
--     exact .truth
--   pick_goal 3
--   · intro x
--     exact .inl x
--   · rintro (l | r)
--     dsimp
--     simp





-- (A ⊎ B → C) ≃ ((A → C) × (B → C))

example : Isomorphism (Coprod A B → C) ((A → C) × (B → C)) := by
  constructor
  pick_goal 3
  · intro f
    constructor
    · intro x
      exact f $ .inl x
    intro y
    exact f $ .inr y
  pick_goal 3
  · rintro ⟨f, g⟩
    intro xs
    rcases xs with l | r
    · exact f l
    exact g r
  · intro f
    -- dsimp
    apply funext
    dsimp
    intro x
    rcases x with l | r
    · dsimp
    dsimp
  intro g
  dsimp







-- (A → B × C) ≃ (A → B) × (A → C)
-- (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)



-- ¬¬-intro

def neg_neg_intro {A : Type*} : A -> NotI (NotI A) := by
  unfold NotI
  intro x f
  apply f
  exact x

-- ¬¬¬-elim

-- ¬¬¬-elim ¬¬¬x  =  λ x → ¬¬¬x (¬¬-intro x)

def neg_neg_neg_elim {A : Type*} : NotI (NotI (NotI A)) -> NotI A :=
  fun not_not_not_x =>
    fun x => not_not_not_x (neg_neg_intro x)

-- ¬¬¬ A → ¬ A
-- ¬¬ A → A
-- ¬¬ True  = True
-- ¬¬ False = False
def neg_neg_neg_elim' {A : Type*} : NotI (NotI (NotI A)) -> NotI A := by
  intro not_not_not_x
  let not_not_not_x' : (NotI (NotI A)) -> BotI := not_not_not_x
  unfold NotI
  exact fun x =>
    let x' := neg_neg_intro x
    not_not_not_x' x'
