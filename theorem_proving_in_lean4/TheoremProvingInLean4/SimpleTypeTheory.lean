-- Define some constants

def m : Nat := 1
def n : Nat := 0
def b1 : Bool := true
def b2 : Bool := false

-- Check their types

#check m -- Nat
#check n -- Nat
#check n + 0 -- Nat
#check m * (n + 0) -- Nat
#check b1 -- Bool
#check b1 && b2 -- Bool
#check true -- Bool

-- Evaluate

#eval 5 * 4 -- 20
#eval m + 2 -- 3
#eval b1 && b2 -- false

#check Nat → Nat -- Type
#check Nat × Nat -- Type
#check Nat → Nat → Nat -- Type
-- Same as above.
#check Nat → (Nat → Nat) -- Type
