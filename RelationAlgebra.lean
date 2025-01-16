import Mathlib.Order.BooleanAlgebra
import Mathlib.Algebra.Group.Defs


/- Extends the boolean algebra: where A is  a non-empty set of elements generated from binary relations , ∪ is the binary operation join, ᶜ is the unary operation complement, and ⊥ is the smallest set in A (empty-set) (A, ∪, ᶜ , ⊥). Relation Algebra adds: the binary operations ;, the binary operation ⁻¹, and the Identity relation.  -/

--What distinguishes the converse in a relation algebra from the complement of a boolean algebra? The converse is a binary operation that swaps the elements, whereas the complement is a unary operation that negates the elements. But do they not result in essentially the same thing?

class Comp (A : Type u) where
  comp : A → A → A

infixl:90 " ; "  => Comp.comp

class RelationAlgebra (A : Type u) extends BooleanAlgebra A, Comp A, One A, Inv A where

  assoc : ∀ x y z : A, x ; (y ; z) = (x ; y) ; z
  distr : ∀ x y z : A, (x ⊔ y) ; z = x ; z ⊔ y ; z
  comp_one : ∀ x : A, x ; 1 = x
  inv_inv  : ∀ x : A, x⁻¹⁻¹ = x
  inv_dist : ∀ x y : A, (x ⊔ y)⁻¹ = x⁻¹ ⊔ y⁻¹
  inv_comp : ∀ x y : A, (x ; y)⁻¹ = y⁻¹ ; x⁻¹
  schroeder : ∀ x y : A, x⁻¹ ; (x ; y)ᶜ ≤ yᶜ

lemma peirce_law {A : Type u} [RelationAlgebra A] (x y z : A) : (x ; y) ⊓ z = ⊥ ↔ (x⁻¹ ; z) ⊓ y = ⊥ := by
  sorry



-- I think the schroder equivalence is a consequence of the relation algebra axioms and not a separate axiom in itself.
  /- Schrod equiv x;(xᶜ;y⁻¹)⁻¹  <= y ∀ x,y ∈ A -/


  /- converses a ∈ A ⇒ a⁻¹ ∈ A where a⁻¹={(c,b | (b,c) ∈ A} -/
  --conv : {x : A}{y : A} (f : fun x y => y x )
  --one_comp : ∀ x : A, 1 ; x = x
