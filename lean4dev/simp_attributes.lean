def double (n : Nat) : Nat := n + n

@[simp]
theorem double_zero : double 0 = 0 := rfl

-- @[simp]
-- theorem double_succ (n : Nat) : double (n + 1) = double n + 2 := by
--   simp [double]
--   ring

example : double 0 = 0 := by simp
-- example : double 1 = 2 := by simp

structure Vec3 where
  x : Float
  y : Float
  z : Float

def Vec3.zero : Vec3 := ⟨0, 0, 0⟩

def Vec3.add (v w : Vec3) : Vec3 :=
  ⟨v.x + w.x, v.y + w.y, v.z + w.z⟩

-- @[simp]
-- theorem Vec3.add_zero (v : Vec3) : v.add Vec3.zero = v := by
--   simp [Vec3.add, Vec3.zero]
--   -- complete...
