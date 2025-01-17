import Mathlib.Order.BooleanAlgebra
import Mathlib.Order.Lattice
import Mathlib.Algebra.Group.Defs

/- Extends Boolean algebra (A, ⊔, ᶜ, ⊥) where A is a non-empty set of elements, ⊔ is the binary operation join,
ᶜ is the unary operation complement, and ⊥ is the bottom element of A.

A relation algebra in addition has a binary operation ; , a unary operation ⁻¹, and a constant 1.
They are abstract versions of the concrete operations composition, converse and identity relation -/

/- What distinguishes the converse in a relation algebra from the complement of a boolean algebra?
The converse is a binary operation that swaps the elements, whereas the complement is a unary operation that negates the elements.
But do they not result in essentially the same thing?

No, they behave differently. E.g., (x ⊔ y)⁻¹ = x⁻¹ ⊔ y⁻¹ but (x ⊔ y)ᶜ = xᶜ ⊓ yᶜ.
-/

variable {A : Type u} [BooleanAlgebra A] (x y : A)

theorem meet_eq_bot_iff_le_compl : x ⊓ y = ⊥ ↔ x ≤ yᶜ := by
  constructor
  . intro h
    calc
      x = x ⊓ y ⊔ x ⊓ yᶜ := by simp
      _ = ⊥ ⊔ x ⊓ yᶜ := by rw [h]
      _ = x ⊓ yᶜ := by rw [bot_sup_eq]
      _ ≤ yᶜ := by simp
  . intro h
    have h' : x ⊓ y ≤ ⊥ := by
      calc
        x ⊓ y ≤ yᶜ ⊓ y := inf_le_inf_right y h
        _ = ⊥ := by simp
    exact bot_unique h'

class Comp (A : Type u) where
  comp : A → A → A

infixl:90 " ; "  => Comp.comp

class RelationAlgebra (A : Type u) extends BooleanAlgebra A, Comp A, One A, Inv A where

  assoc : ∀ x y z : A, (x ; y) ; z = x ; (y ; z)
  rdist : ∀ x y z : A, (x ⊔ y) ; z = x ; z ⊔ y ; z
  comp_one  : ∀ x : A, x ; 1 = x
  conv_conv : ∀ x : A, x⁻¹⁻¹ = x
  conv_dist : ∀ x y : A, (x ⊔ y)⁻¹ = x⁻¹ ⊔ y⁻¹
  conv_comp : ∀ x y : A, (x ; y)⁻¹ = y⁻¹ ; x⁻¹
  schroeder : ∀ x y : A, x⁻¹ ; (x ; y)ᶜ ≤ yᶜ

open RelationAlgebra

variable {A : Type u} [RelationAlgebra A]

lemma ldist (x y z : A) : x ; (y ⊔ z) = x ; y ⊔ x ; z := by
  calc
    x ; (y ⊔ z) = (x ; (y ⊔ z))⁻¹⁻¹ := by rw [conv_conv]
    _ = ((y ⊔ z)⁻¹ ; x⁻¹)⁻¹ := by rw [conv_comp]
    _ = ((y⁻¹ ⊔ z⁻¹) ; x⁻¹)⁻¹ := by rw [conv_dist]
    _ = (y⁻¹ ; x⁻¹ ⊔ z⁻¹ ; x⁻¹)⁻¹ := by rw [rdist]
    _ = ((x ; y)⁻¹ ⊔ (x ; z)⁻¹)⁻¹ := by rw [←conv_comp, ←conv_comp]
    _ = (x ; y) ⊔ (x ; z) := by rw [←conv_dist, conv_conv]

lemma comp_le_comp_right (z : A) {x y : A} (h : x ≤ y) : x ; z ≤ y ; z := by
  calc
    x ; z ≤ x ; z ⊔ y ; z := by simp
    _ = (x ⊔ y) ; z := by rw [←rdist]
    _ = y ; z := by simp [h]

--theorem inf_le_inf_right (a : α) {b c : α} (h : b ≤ c) : b ⊓ a ≤ c ⊓ a :=

lemma comp_le_comp_left (z : A) {x y : A} (h : x ≤ y) : z ; x ≤ z ; y := by
  calc
    z ; x ≤ z ; x ⊔ z ; y := by simp
    _ = z ; (x ⊔ y) := by rw [←ldist]
    _ = z ; y := by simp [h]

lemma peirce_law (x y z : A) : x ; y ⊓ z = ⊥ ↔ x⁻¹ ; z ⊓ y = ⊥ := by
  constructor
  intro h
  have : x ; y ≤ zᶜ := by rw [meet_eq_bot_iff_le_compl] at h; exact h
  have : z ≤ (x ; y)ᶜ := by
    rw [←compl_le_compl_iff_le, compl_compl] at this; exact this
  have : x⁻¹ ; z ≤ x⁻¹ ; (x ; y)ᶜ := comp_le_comp_left x⁻¹ this
  have : x⁻¹ ; z ⊓ y ≤ ⊥ := by
    calc
      x⁻¹ ; z ⊓ y ≤ x⁻¹ ; (x ; y)ᶜ ⊓ y := inf_le_inf_right y this
      _ ≤ yᶜ ⊓ y := inf_le_inf_right y (schroeder x y)
      _ = ⊥ := by simp
  exact bot_unique this
  . intro h
    have : x⁻¹ ; z ≤ yᶜ := by rw [meet_eq_bot_iff_le_compl] at h; exact h
    have : y ≤ (x⁻¹ ; z)ᶜ := by
      rw [←compl_le_compl_iff_le, compl_compl] at this; exact this
    have : x⁻¹⁻¹ ; y ≤ x⁻¹⁻¹ ; (x⁻¹ ; z)ᶜ := comp_le_comp_left x⁻¹⁻¹ this
    have : x⁻¹⁻¹ ; y ⊓ z ≤ ⊥ := by
      calc
        x⁻¹⁻¹ ; y ⊓ z ≤ x⁻¹⁻¹ ; (x⁻¹ ; z)ᶜ ⊓ z := inf_le_inf_right z this
        _ ≤ zᶜ ⊓ z := inf_le_inf_right z (schroeder x⁻¹ z)
        _ = ⊥ := by simp
    have : x ; y ⊓ z ≤ ⊥ := by rw [conv_conv] at this; exact this
    exact bot_unique this

-- I think the Schröder equivalence is a consequence of the relation algebra axioms and not a separate axiom in itself.
/- Schröder equivalence: ∀ x,y ∈ A, x;(x⁻¹;yᶜ)ᶜ ≤ y -/

/- converses a ∈ A ⇒ a⁻¹ ∈ A where a⁻¹ = {(c,b) | (b,c) ∈ a} -/
