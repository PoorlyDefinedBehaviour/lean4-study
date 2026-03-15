import Mathlib.Tactic

example (x y : Int) : (x + y)^2 = x^2 + 2*x*y + y^2 := by ring

example (x y : Int) (h1 : x < y) (h2 : y < x) : False := by linarith

example (h : ∃ n : Nat, n > 0 ∧ n < 10) : True := by
  rcases h with ⟨n, hn_pos, hn_lt⟩
  trivial

example (a b : ℤ) : (a - b) * (a + b) = a^2 - b^2 := by ring

example (x : Int) : (x + 1)^2 = x^2 + 2*x + 1 := by ring
