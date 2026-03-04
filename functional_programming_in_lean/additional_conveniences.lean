

def length {α : Type} (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: ys => Nat.succ (length ys)

def length2 (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: ys => Nat.succ (length2 ys)

def length3 : List α → Nat
  | [] => 0
  | _ :: ys => Nat.succ (length3 ys)

def drop : Nat → List α → List α
  | Nat.zero, xs => xs
  | _, [] => []
  | Nat.succ n, _ :: xs => drop n xs

def fromOption (default : α) : Option α → α
  | none => default
  | some x => x

#eval (some "salmonberry").getD ""
#eval none.getD ""

def unzip : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
      (x :: (unzip xys).fst, y :: (unzip xys).snd)

def unzip2 : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped : List α × List β := unzip2 xys
    (x :: unzipped.fst, y :: unzipped.snd)

def unzip3 : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let (xs, ys) : List α × List β := unzip3 xys
    (x :: xs ,y :: ys)

def reverse (xs : List α) : List α :=
  let rec helper : List α → List α → List α
    | [], soFar => soFar
    | y :: ys, soFar => helper ys (y :: soFar)
  helper xs []

def unzip4 : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let (xs, ys) := unzip4 xys
    (x :: xs, y :: ys)

#check 14
#check (14 : Int)

def id' (x : α) : α := x

def sameLength (xs : List α) (ys : List β) : Bool :=
  match xs, ys with
  | [], [] => true
  | _ :: xs', y :: ys' => sameLength xs' ys'
  | _, _ => false

def even : Nat → Bool
  | 0 => true
  | n + 1 => not (even n)

def halve : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => halve n + 1

#check fun x => x + 1
#check fun (x : Int) => x + 1
#check fun {α : Type} (x : α) => x

def Nat.double (x : Nat) : Nat := x + x

#eval (4 : Nat).double
#eval Nat.double 4

namespace NewNamespace
def triple (x : Nat) : Nat := 3 * x
def quadruple (x : Nat) : Nat := 2 * x + 2 * x
end NewNamespace

def timesTwelve (x : Nat) :=
  open NewNamespace in
  quadruple (triple x)
