import Mathlib.Init.Logic

inductive ℕ where
  | zero : ℕ
  | succ : ℕ -> ℕ

def add : ℕ -> ℕ -> ℕ
  | .zero  , n => n
  | .succ m, n => .succ $ add m n

def add_identity (n : ℕ) : n = add n .zero :=
  match n with
  | .zero   => rfl
  | .succ n => congr_arg ℕ.succ $ add_identity n

def add_succ (m n : ℕ) : .succ (add m n) = add m (.succ n) :=
  match m with
  | .zero   => rfl
  | .succ m => congr_arg ℕ.succ $ add_succ m n

def add_comm (m n : ℕ) : add m n = add n m :=
  match m with
  | .zero   => add_identity n
  | .succ m => Eq.trans
      (congr_arg ℕ.succ $ add_comm m n)
      (add_succ n m)

variable {A B : Type}

@[simp] def length : List A -> ℕ :=
  fun xs =>
    match xs with
    | []      => .zero
    | _ :: xs => .succ $ length xs

@[simp] def append : List A -> List A -> List A :=
  fun xs ys =>
    match xs with
    | []      => ys
    | x :: xs => x :: append xs ys

def append_length (xs ys : List A) : add (length xs) (length ys) = length (append xs ys) :=
  match xs with
  | []      => rfl
  | _ :: xs => congr_arg ℕ.succ $ append_length xs ys

def reverse : List A -> List A :=
  sorry

example : reverse [0, 1, 2, 3, 4, 5] = [5, 4, 3, 2, 1, 0] := by
  sorry -- rfl

-- Exercise: define reverse, and
--           prove that the reverse of one list appended to another
--           is the reverse of the second appended to the reverse
--           of the first.

-- Exercise: prove reverse is an involution

@[simp] def foldl : (B -> A -> B) -> B -> List A -> B :=
  fun f acc xs =>
    match xs with
    | []      => acc
    | x :: xs => foldl f (f acc x) xs

@[simp] def foldr : (A -> B -> B) -> B -> List A -> B :=
  fun f acc xs =>
    match xs with
    | []      => acc
    | x :: xs => f x (foldr f acc xs)

def sum : List Int -> Int :=
  foldr (· + ·) 0

example : sum [0, 1, 2, 3, 4] = 10 := rfl

def filter (f : A -> Bool) : List A -> List A
  | []      => []
  | x :: xs => if f x
      then x :: filter f xs
      else      filter f xs

example : filter (· ≠ 0) [0, 1, 2, 0, 3, 4, 0, 0, 5, 6] = [1, 2, 3, 4, 5, 6] :=
  rfl

-- Exercise: define filter in terms of folds

def foldr_cons_nil (xs : List A) : foldr List.cons [] xs = xs :=
  match xs with
  | []      => rfl
  | x :: xs => by simp; exact foldr_cons_nil xs

def pure' : A -> List A := (· :: [])

def map : (A -> B) -> (List A -> List B) :=
  fun f xs =>
    match xs with
    | [] => []
    | x :: xs => f x :: map f xs

def join : List (List A) -> List A :=
  foldl (fun acc xs => append acc xs) []

example : join [[0], [1, 2, 3, 4], [5, 6, 7]] = [0, 1, 2, 3, 4, 5, 6, 7] := by
  rfl

--- `pure`, `map`, `join` <-> comprehension

-- [42]
#eval (pure' 42 : List Int)

-- [ x          | x <- [0, 1, 2, 3, 4, 5] ]
-- [ fun x => x | x <- [0, 1, 2, 3, 4, 5] ]
#eval map (fun x => x) [0, 1, 2, 3, 4, 5]

-- [ x               | x <- [0, 1, 2, 3, 4, 5] ]
-- [ fun x => ⟨x, x⟩ | x <- [0, 1, 2, 3, 4, 5] ]
#eval map (fun x => (⟨x, x⟩ : Int × Int)) [0, 1, 2, 3, 4, 5]

-- [ ⟨x, y⟩            | x <- [0, 1, 2, 3, 4, 5], y <- [0, 1, 2, 3, 4, 5] ]
-- [ fun x y => ⟨x, y⟩ | x <- [0, 1, 2, 3, 4, 5], y <- [0, 1, 2, 3, 4, 5] ]
-- [ fun x => fun y => ⟨x, y⟩ | x <- [0, 1, 2, 3, 4, 5], y <- [0, 1, 2, 3, 4, 5] ]
-- join [ fun x => [ fun y => ⟨x, y⟩ | y <- [0, 1, 2, 3, 4, 5] ] | x <- [0, 1, 2, 3, 4, 5] ]
#eval join $ map (fun x => (map ((fun y => ⟨x, y⟩) : Int -> Int × Int) [0, 1, 2, 3, 4, 5])) [0, 1, 2, 3, 4, 5]

-- [ x | x <- [0, 1, 2, 3] | x != 2 ]
-- Exercise: how can we translate the above
-- HINT: [ c | p ] = if p then [c] else []

--- `map`, `join` <-> `bind`
-- bind xs k = join (map k xs)
-- join xss  = bind xss id

-- https://leanprover-community.github.io/archive/stream/270676-lean4/topic/Option.20do.20notation.20regression.3F.html
instance : Monad List where
  pure := pure'
  bind := fun xs k => join (map k xs)

-- [ ⟨x, y⟩ | x <- [0, 1, 2, 3, 4, 5], y <- [0, 1, 2, 3, 4, 5] ]
example : List (Int × Int) := do
  let x <- [0, 1, 2, 3, 4, 5]
  let y <- [0, 1, 2, 3, 4, 5]
  pure ⟨x, y⟩

-- alias `· >>= ·` `bind`
example : List (Int × Int) :=
  [0, 1, 2, 3, 4, 5] >>= fun x =>
    [0, 1, 2, 3, 4, 5] >>= fun y =>
      pure ⟨x, y⟩

example : List (Int × Int) :=
  bind [0, 1, 2, 3, 4, 5] (fun x =>
    bind [0, 1, 2, 3, 4, 5] (fun y =>
      pure ⟨x, y⟩))

-- we can also use `$`
example : List (Int × Int) :=
  bind [0, 1, 2, 3, 4, 5] fun x =>
    bind [0, 1, 2, 3, 4, 5] fun y =>
      pure ⟨x, y⟩

def head: List A -> Option A :=
  fun xs =>
    match xs with
    | []     => .none
    | x :: _ => .some x

def last: List A -> Option A :=
  fun xs =>
    match xs with
    | []      => .none
    | [x]     => .some x
    | _ :: xs => last xs

def cons_head_last: List A -> List A -> Option (List A) :=
  fun xs ys =>
    let x := head xs
    let y := last ys
    match x with
    | .none   => .none
    | .some x => match y with
                 | .none   => .none
                 | .some y => .some [x, y]

def pair_head_last: List A -> Option (A × A) :=
  fun xs =>
    let x := head xs
    let y := last xs
    match x with
    | .none   => .none
    | .some x => match y with
                 | .none   => .none
                 | .some y => .some (x, y)

inductive Result (err_t : Type _) (ok_t : Type _) where
  | ok  : ok_t  -> Result err_t ok_t
  | err : err_t -> Result err_t ok_t
  deriving Repr

def cons_head_last_and_why: List A -> List A -> Result String (List A) :=
  fun xs ys =>
    let x := head xs
    let y := last ys
    match x with
    | .none   => .err "head failed"
    | .some x => match y with
                 | .none   => .err "last failed"
                 | .some y => .ok [x, y]

#eval cons_head_last_and_why [] [1]
#eval cons_head_last_and_why [1] []
