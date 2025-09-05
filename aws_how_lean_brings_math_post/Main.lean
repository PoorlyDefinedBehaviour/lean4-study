-- https://www.amazon.science/blog/how-the-lean-language-brings-math-to-coding-and-coding-to-math

def append (xs ys : List a) : List a :=
  match xs with
    | [] => ys
    | x :: xs => x :: append xs ys

infixr:67 " ;; " => List.cons

theorem append_length (xs ys : List a) :
  (append xs ys).length = xs.length + ys.length := by
  induction xs with
    | nil => simp [append]
    | cons x xs ih => simp [append, ih]; omega
