import Std.Tactic.BVDecide

#reduce (λx ↦ x + 1)

#reduce (λ x ↦ 1 + x)

#check λx ↦ [x]

#check λx ↦ x + x

#check_failure "one" + 1
#check "one" + 1

#synth HAdd Int Int Int

#print "hello world"

def swap (x y : BitVec 32) : BitVec 32 × BitVec 32 := (y, x)

def swap' (x y : BitVec 32) : BitVec 32 × BitVec 32 :=
  let x := x ^^^ y
  let y := x ^^^ y
  let x := x ^^^ y
  (x, y)

theorem swap_eq_swap' : swap = swap' := by
  funext x y
  simp only [swap, swap', Prod.mk.injEq]
  bv_decide

#print axioms swap_eq_swap'

def intersperse (x : α) : List α → List α
  | y :: z :: zs => y :: x :: intersperse x (z :: zs)
  | xs => xs

#print equations intersperse

#where
