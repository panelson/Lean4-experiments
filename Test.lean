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

/- Theorem 8: In a group G = (G,*) every element has a unique inverse.

In fact, we prove that if b is a left inverse and c is a right inverse of a,
then b = c. -/

theorem unique_inverse : ∀ a b c : G, b * a = 1 ∧ a * c = 1 → b = c := by
  intro a b c h
  calc
    b = b * 1 := by rw [mul_one]
    _ = b * (a * c) := by rw [h.2]
    _ = (b * a) * c := by rw [mul_assoc]
    _ = 1 * c := by rw [h.1]
    _ = c := by rw [one_mul]

/- Theorem 9: (i) x⁻¹⁻¹ = x -/

theorem inverse_inverse : ∀ x : G, x⁻¹⁻¹ = x := by
  intro x
  calc
    x⁻¹⁻¹ = x⁻¹⁻¹ * 1 := by rw [mul_one]
    _ = x⁻¹⁻¹ * (x⁻¹ * x) := by rw [inv_mul_cancel]
    _ = (x⁻¹⁻¹ * x⁻¹) * x := by rw [mul_assoc]
    _ = 1 * x := by rw [inv_mul_cancel]
    _ = x := by rw [one_mul]

/- Theorem 9: (ii) (x * y)⁻¹ = y⁻¹ * x⁻¹ -/

theorem mul_inverse : ∀ x y : G, (x * y)⁻¹ = y⁻¹ * x⁻¹ := by
  intro x y
  calc
    (x * y)⁻¹ = (x * y)⁻¹ * 1 := by rw [mul_one]
    _ = (x * y)⁻¹ * (x * x⁻¹) := by rw [mul_inv_cancel]
    _ = (x * y)⁻¹ * ((x * 1) * x⁻¹) := by rw [mul_one]
    _ = (x * y)⁻¹ * ((x * (y * y⁻¹)) * x⁻¹) := by rw [mul_inv_cancel]
    _ = (x * y)⁻¹ * ((x * y) * (y⁻¹ * x⁻¹)) := by rw [mul_assoc, mul_assoc, mul_assoc]
    _ = ((x * y)⁻¹ * (x * y)) * (y⁻¹ * x⁻¹) := by rw [←mul_assoc]
    _ = 1 * (y⁻¹ * x⁻¹) := by rw [inv_mul_cancel]
    _ = y⁻¹ * x⁻¹ := by rw [one_mul]

/- Theorem 10: S is an associative binary system with right identity such that each element has a right inverse. It then follows that G is a group -/

--Show that if a * b = e => b * a = e. a * b = e, a * a ^-1 = e, a

theorem right_id_and_inverse_imply_group : (h1 : ∀ x y : S, x * y = 1 = x * x⁻¹) (h2 : h1 → ) : Group S := by
  sorry

def Function.comp f g
