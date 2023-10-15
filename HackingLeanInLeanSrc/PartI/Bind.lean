import HackingLeanInLeanSrc.PartI.BasicFp

#check cons_head_last
#check pair_head_last

example : List A -> List A -> Option (List A) :=
  fun xs ys =>
    let x := head xs
    let y := last ys
    match x with
    | .none   => .none
    | .some x => match y with
                 | .none   => .none
                 | .some y => .some [x, y]

example : List A -> List A -> Option (List A) :=
  fun xs ys =>
    bind (head xs) fun x =>
      bind (last ys) fun y =>
        .some [x, y]

example : List A -> List A -> Option (List A) :=
  fun xs ys =>
    head xs >>= fun x =>
      last ys >>= fun y =>
        .some [x, y]

example : List A -> List A -> Option (List A) :=
  fun xs ys => do
    let x <- head xs
    let y <- last ys
    pure [x, y]

example : List A -> List A -> Option (List A) :=
  fun xs ys => do
    let x <- head xs
    let y <- last ys
    return [x, y]

#check Except

instance {err : Type _} : Functor (Result err) where
  map f xs := sorry
