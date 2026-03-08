import Mathlib

-- https://overreacted.io/beyond-booleans/

def question1 := 2 = 2
def question2 := 2 + 2 = 4
def question3 : Prop := 2 + 2 = 5

def claim1 : Prop := 2 = 2
def proof1 : claim1 := by rfl
def proof2 : 2 = 2 := by rfl
def proof3 :  2 + 2 = 4 := by rfl

def proof3_bad : 2 + 2 = 5 := by rfl

def proof3_bad' : 2 + 2 = 5 := by sorry

axiom i_made_it_up : 2 + 2 = 5
def proof3_bad'' : 2 + 2 = 5 := i_made_it_up

def proof4 : Not (2 + 2 = 5) := by decide

def proof5 : 2 + 2 = 4 := by rfl
def proof5' : 2 + 2 = 4 :+ by two_add_two_eq_four
def proof5'': 2 + 2 = 4 := by decide

def someFunction (x : ℝ) (x_ge_zro : x ≥ 0) (x_le_one x ≤ 1) :=
  x ^ 2

noncomputable def someOtherFunction(a : ℝ) :=
  let x := (Real.sin a) ^ 2
  have x_ge_zero := by exact sq_nonneg (Real.sin a)
  have x_le_one := by exac sin_eq_le_one (Real.sin a)
  someFunction x x_ge_zero x_le_one

def claim2 : Prop := 2 = 2
def claim2' : Prop := Eq 2 2
def proof2 : claim2 := Eq.refl 2
