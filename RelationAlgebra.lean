import Mathlib.Order.BooleanAlgebra
import Mathlib.Order.Lattice
import Mathlib.Algebra.Group.Defs
--import Mathlib.Logic.Basic

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
  · intro h
    calc
      x = x ⊓ y ⊔ x ⊓ yᶜ := by simp
      _ = ⊥ ⊔ x ⊓ yᶜ := by rw [h]
      _ = x ⊓ yᶜ := by rw [bot_sup_eq]
      _ ≤ yᶜ := by simp
  · intro h
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

class NonassociativeRA (A : Type u) extends BooleanAlgebra A, Comp A, One A, Inv A where
  comp_one  : ∀ x : A, x ; 1 = x
  one_comp  : ∀ x : A, 1 ; x = x
  peirce_law1 (x y z : A) : x ; y ⊓ z = ⊥ ↔ x⁻¹ ; z ⊓ y = ⊥
  peirce_law2 (x y z : A) : x ; y ⊓ z = ⊥ ↔ z ; y⁻¹ ⊓ x = ⊥

class WeaklyassociativeRA (A : Type u) extends NonassociativeRA A where
  assoc : ∀ x : A, (1 ⊓ x ; ⊤) ; ⊤ = (1 ⊓ x) ; ⊤

class SemiassociativeRA (A : Type u) extends NonassociativeRA A where
  assoc : ∀ x : A, (x ; ⊤) ; ⊤ = x ; ⊤

class RMRelationAlgebra (A : Type u) extends NonassociativeRA A where
  assoc : ∀ x y z : A, (x ; y) ; z = x ; (y ; z)

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
  · intro h
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
  · intro h
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
  · intro h
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
  · intro h
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

/- Full relation algebras Re(X) = (P(X²), ∪, ∩, \, ∅, X², ;, ⁻¹, id) as instance of
the class RelationAlgebra

P(X²) is the power set of X², ∪ is the union of sets, ∩ is the intersection of sets, \ is the set difference,

Set (X x X)
-/

variable (X : Type u) (R : Set (X × X))

instance : RelationAlgebra (Set (X × X)) where
  comp R S := { (x, y) | ∃ z, (x, z) ∈ R ∧ (z, y) ∈ S }
  one := { (x, y) | x = y }
  inv R := { (y, x) | (x, y) ∈ R }
  bot := ∅
  top := Set.univ
  sup R S := R ∪ S
  inf R S := R ∩ S
  compl R := Set.univ \ R
  le_refl := by sorry
  assoc x y z := by sorry
  rdist x y z := by sorry

--instance : Comp A where
-- comp := λ x y => x ; y

--#check

class Ternary (S : Type u) where
  ternary : S → S → S → Prop

notation "R "  => Ternary.ternary

class Unary (S : Type u) where
  unary : S → Prop

prefix:90 "I "  => Unary.unary

class AtomStructure (S : Type u) extends Ternary S, Inv S, Unary S where
  peirce1 : ∀ x y z : S, R x y z ↔ R x⁻¹ z y
  peirce2 : ∀ x y z : S, R x y z ↔ R z y⁻¹ x
  id : ∃ x : S, I x
  identity1 : ∀ x y u : S, I u ∧ R x u y → x = y
  identity2 : ∀ x y : S, ∃ u : S, x = y → I u ∧ R x u y
  assoc : ∀ u x y z w : S, R x y u ∧ R u z w → ∃ v : S, R y z v ∧ R x v w

open AtomStructure

variable {S : Type u} [AtomStructure S]

lemma conv_conv (x : S) : x⁻¹⁻¹ = x := by
  have h : ∃ e : S, I e ∧ R x e x := by rw [←identity]
  cases h with
  | intro e h' => rw [peirce1] at h'; rw [peirce1] at h'; exact (identity x⁻¹⁻¹ x).mpr ⟨e, h'⟩

/- define atom structure with atoms e, a, b and relations
  R e e e, R e a a, R e b b,
  R a e a, R a a b, R a b e,
  R b e b, R b a e, R b b a -/

/- The group Z_3 as atom structure -/
inductive Z₃ : Type u | e : Z₃ | a : Z₃ | b : Z₃
open Z₃
def Z₃.ternary : Z₃ → Z₃ → Z₃ → Prop := fun
| e, e, e => True | e, a, a => True | e, b, b => True
| a, e, a => True | a, a, b => True | a, b, e => True
| b, e, b => True | b, a, e => True | b, b, a => True
| _, _, _ => False
def Z₃.inv : Z₃ → Z₃ := fun | e => e | a => b | b => a
def Z₃.unary : Z₃ → Prop := fun | e => True | _ => False

open Classical -- needed for the next example
example : False → e = a := by trivial
example : ∃ x : Z₃, x = e → a = a := by (exists e <;> intro; trivial)

set_option diagnostics true
example : ∃ x : Z₃, unary x := by exists e
example : True → e = e := by intro h; exact rfl
example : Z₃.ternary e e e := trivial


instance : AtomStructure (Z₃) where
  ternary x y z := Z₃.ternary x y z
  unary x := Z₃.unary x
  inv x := Z₃.inv x
  id := by exists e
  peirce1 x y z := by cases x <;> cases y <;> cases z <;> rfl
  peirce2 x y z := by cases x <;> cases y <;> cases z <;> rfl
  identity1 x y u := by cases x <;> cases y <;> cases u <;> aesop
  identity2 x y := by cases x <;> cases y <;> (exists e <;> intro; trivial)
  assoc u x y z w := by cases u <;> cases x <;> cases y <;> cases z <;> cases w <;> rfl

lemma peirce3 (x y z : S) : R x y z ↔ R y⁻¹ x⁻¹ z⁻¹ := by
  rw [peirce1, peirce2, peirce1]


lemma assocr (u x y z w : S) : R y z v ∧ R x v w → ∃ u : S, R x y u ∧ R u z w := by
  rw [peirce1, peirce2]
  intro h
  have h : R y z⁻¹ v ∧ R x⁻¹ v⁻¹ w := by sorry



  -- this proof will use lemma peirce3


-- I think the Schröder equivalence is a consequence of the relation algebra axioms and not a separate axiom in itself.
/- Schröder equivalence: ∀ x,y ∈ A, x;(x⁻¹;yᶜ)ᶜ ≤ y -/

/- converses a ∈ A ⇒ a⁻¹ ∈ A where a⁻¹ = {(c,b) | (b,c) ∈ a} -/
