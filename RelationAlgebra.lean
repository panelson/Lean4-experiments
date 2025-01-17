import Mathlib.Order.BooleanAlgebra
import Mathlib.Algebra.Group.Defs


/- Extends Boolean algebra (A, ⊔, ᶜ, ⊥) where A is a non-empty set of elements, ⊔ is the binary operation join,
ᶜ is the unary operation complement, and ⊥ is the bottom element of A.

A relation algebra in addition has a binary operation ; , a unary operation ⁻¹, and a constant 1.
They are abstracted from the concrete operations of composition, converse and identity relation -/

/- What distinguishes the converse in a relation algebra from the complement of a boolean algebra?
The converse is a binary operation that swaps the elements, whereas the complement is a unary operation that negates the elements.
But do they not result in essentially the same thing?

No, they behave differently. E.g.,
-/

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

lemma peirce_law {A : Type u} [RelationAlgebra A] (x y z : A) : x ; y ⊓ z = ⊥ ↔ x⁻¹ ; z ⊓ y = ⊥ := by
  constructor
  intro h
  have h : x ; y ⊓ z = ⊥ ↔ x ; y ≤ zᶜ := by
    rw [←le_iff_eq_bot]
    exact h
  have h' : x⁻¹ ; z ⊓ y = ⊥ ↔ x⁻¹ ; z ≤ yᶜ := by
    rw [←le_iff_eq_bot]
  sorry



-- I think the schroder equivalence is a consequence of the relation algebra axioms and not a separate axiom in itself.
  /- Schrod equiv x;(xᶜ;y⁻¹)⁻¹  <= y ∀ x,y ∈ A -/


  /- converses a ∈ A ⇒ a⁻¹ ∈ A where a⁻¹={(c,b | (b,c) ∈ A} -/
  --conv : {x : A}{y : A} (f : fun x y => y x )
  --one_comp : ∀ x : A, 1 ; x = x
