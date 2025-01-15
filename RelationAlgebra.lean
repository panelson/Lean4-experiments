import Mathlib.order.BooleanAlgebra


/- Extends the boolean algebra: where A is  a non-empty set of elements generated from binary relations , ∪ is the binary operation join, ᶜ is the unary operation complement, and ⊥ is the smallest set in A (empty-set) (A, ∪, ᶜ , ⊥). Relation Algebra adds: the binary operations ;, the binary operation ⁻¹, and the Identity relation.  -/

--What distinguishes the converse in a relation algebra from the complement of a boolean algebra? The converse is a binary operation that swaps the elements, whereas the complement is a unary operation that negates the elements. But do they not result in essentially the same thing?



class RelationAlgebra (A : Type u) extends BooleanAlgebra A where

  /- Composition R;S = {(b,d) | ∃d(bRc and cSd))} -/
  comp : {B : A}{C : A}{D : A}(R : fun B => C)(S : fun C => D)
  -- => fun b c => ∃d(f b d and g d c)

  /- converses a ∈ A ⇒ a⁻¹ ∈ A where a⁻¹={(c,b | (b,c) ∈ A} -/
  conv : {x : A}{y : A} (f : fun x y => y x )

  /- Identity relation I = {(a,a) | a ∈ A} -/
  id : {x : A} (f : fun x => x x)

-- I think the schroder equivalence is a consequence of the relation algebra axioms and not a separate axiom in itself.
  /- Schrod equiv x;(xᶜ;y⁻¹)⁻¹  <= y ∀ x,y ∈ A -/
