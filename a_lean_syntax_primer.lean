-- https://overreacted.io/a-lean-syntax-primer/

def name := "Alice"
def age := 42

def temperature := -140
def roomTemperature : Int := 25
def roomTemperature2 := (25 : Int)
def birthYear := 2025 - age

#eval birthYear

def main := IO.println birthYear

#eval main

theorem my_theorem : age + birthYear = 2025 := by
  unfold age
  unfold birthYear
  unfold age
  decide

theorem my_theorem2 : age + birthYear = 2025 := by
  simp [age, birthYear]

open IO
def main2 := println birthYear
#eval main2

open IO in
def main3 := println birthYear
#eval main3

def main4 := IO.println (2025 - age)
#eval main4

def main5 :=
  let birthYear := 2025 - age
  IO.println birthYear
#eval main5

def name2 :=
  let namesInPassport := ["Alice", "Babbage", "McDuck"]
  namesInPassport[0]

def age2 :=
  let twenty := 20
  let one := 1
  twenty + twenty + one + one

def main6 :=
  let birthYear := 2025 - age2
  IO.println birthYear
#eval main6

def birthYear2 currentYear := currentYear - age
#eval IO.println (birthYear2 2025)

def birthYear3 (currentYear : Int) (age : Nat) := currentYear - age

theorem my_theorem3 (currentYear : Int) (age : Nat) : age + birthYear3 currentYear age = currentYear := by
  unfold birthYear3
  omega

theorem my_theorem4 : ∀ currentYear age, age + birthYear3 currentYear age = currentYear := by
  intro currentYear age
  unfold birthYear3
  omega

def append (xs ys : List α) : List α := Id.run do
  let mut out := ys
  for x in xs.reverse do
    out := x :: out
  return out

theorem append_abcd : append ["a", "b"] ["c", "d"] = ["a", "b", "c", "d"] := by
  simp [append]

theorem append_length (xs ys : List α) : (append xs ys).length = xs.length + ys.length := by
  simp [append]

def count_up_and_down n :=
  let up := List.range (n)
  let down := (List.range (n + 1)).reverse
  append up down

theorem count_up_down_length n : (count_up_and_down n).length = n * 2 + 1 := by
  simp only [count_up_and_down, append_length, List.length_range, List.length_reverse]
  omega

def main7 := do
  IO.println "Enter a number: "
  let stdin ← IO.getStdin
  let input ← stdin.getLine
  let n := input.trim.toNat!
  let sequence := count_up_and_down n
  IO.println sequence
