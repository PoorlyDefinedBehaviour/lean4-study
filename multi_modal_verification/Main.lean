-- https://proofsandintuitions.net/2026/01/21/multi-modal-verification-velvet/

def append(xs ys : List Int) : List Int :=
  match xs with
  | [] => ys
  | x :: xs => x :: append xs ys

theorem append_assoc (xs ys zs : List Int) :
  append (append xs ys) zs = append xs (append ys zs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [append, ih]
