#check And
#check Or
#check Not
-- #check Implies

variable (p r q : Prop)

#check And p q
#check Or (And p q) r

-- #check Proof

-- axiom add_commut (p q : Prop) : Proof (Implies (And p q) (And q p))

-- #check add_commut p q

-- axiom modus_ponens (p q : Prop) :
--   Proof (Implies p q) → Proof p → Proof q

        -- qaw

set_option linter.unusedVariables false

section a
variable {p q : Prop}

theorem t1 : p → q → p := fun hp : p => fun hq : q => show p from hp
#print t1

theorem t2 (hp : p) (hq : q) : p := hp
#print t2
end a

section and
variable (p q : Prop)

example (hp : p) (hq : q) : p ∧ q := And.intro hp hq
example (h : p ∧ q) : p := And.left h
example (h : p ∧ q) : q := And.right h

example (h : p ∧ q) : q ∧ p :=
  And.intro (And.right h) (And.left h)

variable (hp : p) (hq : q)
#check (⟨hp, hq⟩ : p ∧ q)
end and

variable (xs : List Nat)

#check List.length xs
#check xs.length

example (h : p ∧ q) : q ∧ p :=
  ⟨h.right, h.left⟩

example (h : p ∧ q) : q ∧ p ∧ q :=
  ⟨h.right, ⟨h.left, h.right⟩⟩

example (h : p ∧ q) : q ∧ p ∧ q :=
  ⟨h.right, h.left, h.right⟩

example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq

variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p =>
      show q ∨ p from Or.intro_right q hp)
    (fun hq : q =>
      show q ∨ p from Or.intro_left p hq)

example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun (hp : p) => show False from hnq (hpq hp)

example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)

