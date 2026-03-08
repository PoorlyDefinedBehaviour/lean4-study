-- https://overreacted.io/the-math-is-haunted/

theorem two_eq_two : 2 = 2 := by
  rfl

theorem two_eq_two_again : 2 = 2 := by
  exact two_eq_two

axiom math_is_haunted : 2 = 3

theorem two_eq_three : 2 = 3 := by
  exact math_is_haunted

theorem two_add_two_eq_six : 2 + 2 = 6 := by
  rewrite [math_is_haunted]
  rfl

theorem two_eq_two1 : 2 = 2 := by
  rfl

theorem two_add_two_eq_four : 2 + 2 = 4 := by
  rfl
