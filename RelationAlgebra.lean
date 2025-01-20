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

lemma meet_eq_bot_iff_le_compl : x ⊓ y = ⊥ ↔ x ≤ yᶜ := by
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

lemma bot_compl_eq_top : (⊥ : A)ᶜ = ⊤ := by simp

lemma top_compl_eq_bot : (⊤ : A)ᶜ = ⊥ := by simp

lemma compl_eq : xᶜ = yᶜ ↔ x = y := by
  constructor
  intro h
  rw [←compl_compl x, h, compl_compl]
  intro h
  rw [h]

lemma join_eq_top_iff_compl_le : x ⊔ y = ⊤ ↔ xᶜ ≤ y := by
  calc
    x ⊔ y = ⊤ ↔ (x ⊔ y)ᶜ = ⊤ᶜ  := by rw [compl_eq]
    _ ↔ xᶜ ⊓ yᶜ = ⊥ := by simp
    _ ↔ xᶜ ≤ y := by rw [meet_eq_bot_iff_le_compl, compl_compl]

class Comp (A : Type u) where
  comp : A → A → A

infixl:90 " ; "  => Comp.comp

/-- An (abstract) relation algebra, as defined by Tarski [1942], is a
Boolean algebra with three additional operation ; ⁻¹ 1 that satisfy
the following additional equational axioms -/
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

/- these simp lemmas are not needed so far
@[simp] lemma rdist' (x y z : A) : (x ⊔ y) ; z = x ; z ⊔ y ; z := rdist x y z
@[simp] lemma conv_conv' (x : A) : x⁻¹⁻¹ = x := conv_conv x
@[simp] lemma conv_dist' (x y : A) : (x ⊔ y)⁻¹ = x⁻¹ ⊔ y⁻¹ := conv_dist x y
@[simp] lemma conv_comp' (x y : A) : (x ; y)⁻¹ = y⁻¹ ; x⁻¹ := conv_comp x y
@[simp] lemma comp_one' (x : A) : x ; 1 = x := comp_one x
-/

lemma top_conv : (⊤ : A)⁻¹ = ⊤ := by
  have : (⊤ : A)⁻¹ = (⊤ ⊔ ⊤⁻¹)⁻¹ := by simp
  have : (⊤ : A)⁻¹ = ⊤⁻¹ ⊔ ⊤ := by rw [conv_dist, conv_conv] at this; exact this
  have : (⊤ : A) ≤ ⊤⁻¹ := by rw [left_eq_sup] at this; exact this
  exact top_unique this

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

lemma comp_le_comp_left (z : A) {x y : A} (h : x ≤ y) : z ; x ≤ z ; y := by
  calc
    z ; x ≤ z ; x ⊔ z ; y := by simp
    _ = z ; (x ⊔ y) := by rw [←ldist]
    _ = z ; y := by simp [h]

lemma conv_le_conv {x y : A} (h : x ≤ y) : x⁻¹ ≤ y⁻¹ := by
  calc
    x⁻¹ ≤ x⁻¹ ⊔ y⁻¹ := by simp
    _ = (x ⊔ y)⁻¹ := by rw [←conv_dist]
    _ = y⁻¹ := by simp [h]

lemma conv_compl_le_compl_conv (x : A) : x⁻¹ᶜ ≤ xᶜ⁻¹ := by
  have : x ⊔ xᶜ = ⊤ := by simp
  have : (x ⊔ xᶜ)⁻¹ = ⊤⁻¹ := by simp
  have : x⁻¹ ⊔ xᶜ⁻¹ = ⊤ := by rw [conv_dist, top_conv] at this; exact this
  rw[join_eq_top_iff_compl_le] at this; exact this

lemma conv_compl_eq_compl_conv (x : A) : xᶜ⁻¹ = x⁻¹ᶜ := by
  have : x⁻¹⁻¹ᶜ ≤ x⁻¹ᶜ⁻¹ := conv_compl_le_compl_conv x⁻¹
  have : xᶜ ≤ x⁻¹ᶜ⁻¹ := by rw [conv_conv] at this; exact this
  have : xᶜ⁻¹ ≤ x⁻¹ᶜ⁻¹⁻¹ := conv_le_conv this
  rw [conv_conv] at this; exact le_antisymm this (conv_compl_le_compl_conv x)

lemma one_conv_eq_one : (1 : A)⁻¹ = 1 := by
  calc
    (1 : A)⁻¹ = 1⁻¹ ; 1 := by rw [comp_one]
    _ = (1⁻¹ ; 1)⁻¹⁻¹ := by rw [conv_conv]
    _ = (1⁻¹ ; 1⁻¹⁻¹)⁻¹ := by rw [conv_comp]
    _ = (1⁻¹ ; 1)⁻¹ := by rw [conv_conv]
    _ = 1 := by rw [comp_one, conv_conv]

lemma one_comp (x : A) : 1 ; x = x := by
  calc
    1 ; x = (1 ; x)⁻¹⁻¹ := by rw [conv_conv]
    _ = (x⁻¹ ; 1⁻¹)⁻¹ := by rw [conv_comp]
    _ = (x⁻¹ ; 1)⁻¹ := by rw [one_conv_eq_one]
    _ = x⁻¹⁻¹ := by rw [comp_one]
    _ = x := by rw [conv_conv]

lemma schroeder' (x y : A) : (x ; y)ᶜ ; y⁻¹  ≤ xᶜ := by
  calc
    (x ; y)ᶜ ; y⁻¹ = ((x ; y)ᶜ ; y⁻¹)⁻¹⁻¹ := by rw [conv_conv]
    _ = (y⁻¹⁻¹ ; (x ; y)ᶜ⁻¹)⁻¹ := by rw [conv_comp]
    _ = (y⁻¹⁻¹ ; (x ; y)⁻¹ᶜ)⁻¹ := by rw [←conv_compl_eq_compl_conv]
    _ = (y⁻¹⁻¹ ; (y⁻¹ ; x⁻¹)ᶜ)⁻¹ := by rw [←conv_comp]
    _ ≤ x⁻¹ᶜ⁻¹ := conv_le_conv (schroeder y⁻¹ x⁻¹)
    _ = xᶜ := by rw [←conv_compl_eq_compl_conv,conv_conv]

lemma peirce_law1 (x y z : A) : x ; y ⊓ z = ⊥ ↔ x⁻¹ ; z ⊓ y = ⊥ := by
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
  intro h
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

/- Try to prove this law in a way that is similar to pierce_law1 using schroeder' -/
lemma peirce_law2 (x y z : A) : x ; y ⊓ z = ⊥ ↔ z ; y⁻¹ ⊓ x = ⊥ := by
  constructor
  intro h
  have : x ; y ≤ zᶜ := by rw [meet_eq_bot_iff_le_compl] at h; exact h
  have : z ≤ (x ; y)ᶜ := by
    rw [←compl_le_compl_iff_le, compl_compl] at this; exact this
  have : z ; y⁻¹ ≤ (x ; y)ᶜ ; y⁻¹ := comp_le_comp_right y⁻¹ this
  have : z ; y⁻¹ ⊓ x ≤ ⊥ := by
    calc
      z ; y⁻¹ ⊓ x ≤ (x ; y)ᶜ ; y⁻¹ ⊓ x := inf_le_inf_right x this
      _ ≤ xᶜ ⊓ x := inf_le_inf_right x (schroeder' x y)
      _ = ⊥ := by simp
  exact bot_unique this
  . intro h
    have : z ; y⁻¹ ≤ xᶜ := by rw [meet_eq_bot_iff_le_compl] at h; exact h
    have : x ≤ (z ; y⁻¹)ᶜ := by
      rw [←compl_le_compl_iff_le, compl_compl] at this; exact this
    have : x ; y⁻¹⁻¹ ≤ (z ; y⁻¹)ᶜ ; y⁻¹⁻¹ := comp_le_comp_right y⁻¹⁻¹ this
    have : x ; y⁻¹⁻¹ ⊓ z ≤ ⊥ := by
      calc
        x ; y⁻¹⁻¹ ⊓ z ≤ (z ; y⁻¹)ᶜ ; y⁻¹⁻¹ ⊓ z := inf_le_inf_right z this
        _ ≤ zᶜ ⊓ z := inf_le_inf_right z (schroeder' z y⁻¹)
        _ = ⊥ := by simp
    have : x ; y ⊓ z ≤ ⊥ := by rw [conv_conv] at this; exact this
    exact bot_unique this



-- I think the Schröder equivalence is a consequence of the relation algebra axioms and not a separate axiom in itself.
/- Schröder equivalence: ∀ x,y ∈ A, x;(x⁻¹;yᶜ)ᶜ ≤ y -/

/- converses a ∈ A ⇒ a⁻¹ ∈ A where a⁻¹ = {(c,b) | (b,c) ∈ a} -/
