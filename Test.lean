import Mathlib.Logic.Basic
import Mathlib.Algebra.Group.Defs

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

theorem unique_inverse : ∀ a b c : G, b * a = 1 ∧ a * c = 1 → b = c := by
  intro a b c h
  calc
    b = b * 1 := by rw [mul_one]
    _ = b * (a * c) := by rw [h.2]
    _ = (b * a) * c := by rw [mul_assoc]
    _ = 1 * c := by rw [h.1]
    _ = c := by rw [one_mul]
