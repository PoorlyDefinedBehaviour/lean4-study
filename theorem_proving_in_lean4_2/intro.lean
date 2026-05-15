theorem and_commutative (p q : Prop) : p ∧ q → q ∧ p :=
  λ⟨p, q⟩ ↦ ⟨q, p⟩
