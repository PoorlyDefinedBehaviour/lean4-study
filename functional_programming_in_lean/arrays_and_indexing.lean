def northernTrees : Array String := #["sloe", "birch", "elm", "oak"]

#eval Array.size northernTrees
#eval northernTrees.size
#eval northernTrees[2]

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

def idahoSpiders : NonEmptyList String := {
  head := "Banded Garden Spider",
  tail := [
    "Long-legged Sac Spider",
    "Wolf Spider",
    "Hobo Spider",
    "Cat-faced Spider"
  ]
}

def NonEmptyList.get? : NonEmptyList α → Nat → Option α
  | xs, 0 => some xs.head
  | {head := _, tail := []}, Nat.succ _ => none
  | {head := _, tail := h :: t}, Nat.succ n => get? {head := h, tail := t} n

def NonEmptyList.get2? : NonEmptyList α → Nat → Option α
  | xs, 0 => some xs.head
  | xs, Nat.succ n => xs.tail[n]?

abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i ≤ xs.tail.length

theorem atLeastThreeSpiders : idahoSpiders.inBounds 2 := by decide

theorem notSixSpiders : ¬idahoSpiders.inBounds 5 := by decide

def NonEmptyList.get (xs : NonEmptyList α) (i : Nat) (ok : xs.inBounds i) : α :=
  match i with
  | 0 => xs.head
  | Nat.succ n => xs.tail[n]

-- class GetElem
--   (coll : Type)
--   (idx : Type)
--   (item : outParam Type)
--   (inBounds : outParam (coll → idx → Prop)) where
--   getElem : (c : coll) → (i : idx) → InBounds c i → item

instance : GetElem (NonEmptyList α) Nat α NonEmptyList.inBounds where
  getElem := NonEmptyList.get

#eval idahoSpiders.head
#eval idahoSpiders[9]

instance : GetElem (List α) Pos α (fun list n => list.length > n.toNat) where
  getElem (xs : List α) (i : Pos) ok := xs[i.toNat]

structure PPoint (α : Type) where
  x : α
  y : α

instance : GetElem (PPoint α) Bool α (fun _ _ => True) where
  getElem (p : PPoint α) (i : Bool) _ :=
    if not i then p.x else p.y

def point : PPoint Nat :=  {x := 1, y  := 2}

#eval point[true]
#eval point[false]

#check 2 < 4

#eval Functor.map (· + 5) [1, 2, 3]

#eval Functor.map toString (some (List.cons 5 List.nil))

#eval Functor.map List.reverse [[1,2,3], [4,5,6]]

#eval (· + 5) <$> [1,2,3]

#eval toString <$> (some (List.cons 5 List.nil))

#eval List.reverse <$> [[1,2,3], [4,5,6]]
