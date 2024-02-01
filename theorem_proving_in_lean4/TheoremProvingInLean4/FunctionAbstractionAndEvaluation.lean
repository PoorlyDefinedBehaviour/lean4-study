#check fun (x : Nat) => x + 5 -- Nat → Nat
-- λ is the same as fun
#check λ (x : Nat) => x + 5 -- Nat → Nat

-- The type of x is inferred.
#check fun x : Nat => x + 5 -- Nat → Nat
-- The type of x is inferred.
#check λ x : Nat => x + 5 -- Nat → Nat

#eval (λ x : Nat => x + 5) 10 -- 15

#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2

def f (n : Nat) : String := toString n

#eval f 5 -- "5"

def g (s : String) : Bool := s.length > 0
