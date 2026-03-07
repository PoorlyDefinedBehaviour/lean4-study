def length (xs : List a): Nat :=
  match xs with
  | [] => 0
  | _ :: xs' => Nat.succ (length xs')

def length1: List a -> Nat
  | [] => 0
  | _ :: xs' => Nat.succ (length1 xs')

def length2 {a: Type} (xs: List a) : Nat :=
  match xs with
  | [] => 0
  | _ :: xs' => Nat.succ (length2 xs')

def fromOption (default: a): Option a -> a
  | none => default
  | some v => v

#eval fromOption 2 (none)

#eval (some 2).getD 1
#eval none.getD 1

def unzip: List (a × b) -> List a × List b
  | [] => ([], [])
  | (x, y) :: rest =>
    let (xs, ys) := unzip rest
    (x :: xs, y :: ys)

def id2 (v : a): a := v
