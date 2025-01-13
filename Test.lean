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

variable [Group G]

/- Theorem 8: In a group G = (G,*) every element has a unique inverse. -/

theorem unique_inverse :
  (∀ x : S, x * 1 = x ∧ 1 * x = x) ∧ a * b = 1 ∧ c * b = 1 → b = c := by
