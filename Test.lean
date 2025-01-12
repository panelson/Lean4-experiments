import Mathlib.Logic.Basic

variable {S : Type*}

variable [Mul S]

variable (e₁ e₂ : S)

/- Theorem 7: A binary system S = (S,*) can have at most one identity element -/

theorem mul_one_identity : (∀ x : S, x * e₁ = x) ∧ (∀ x : S, e₂ * x = x) → e₁ = e₂ := by
  intro h
  have h1 := h.left e₂
  have h2 := h.right e₁
  rw [<-h1, h2]

variable (e : S)

/- Theorem 8: If a group G = (G,*) has an identity element
  then every element has a unique inverse then it is unique -/

theorem unique_inverse : (∀ x : S, x * e = x ∧ e * x = x)
  ∧ a * b = e ∧ c * b = e → b = c := by
