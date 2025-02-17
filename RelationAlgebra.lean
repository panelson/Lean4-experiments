import Mathlib.Order.BooleanAlgebra
import Mathlib.Order.Lattice
import Mathlib.Algebra.Group.Defs
--import Mathlib.Logic.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

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


def isJtrue (t u v w x y z : A) : Prop :=
  t ≤ u;v ⊓ w;x  ∧  u⁻¹;w ⊓ v;x⁻¹ ≤ y;z → t ≤ (u;y ⊓ w;z⁻¹);(y⁻¹;v ⊓ x;z)

def isLtrue (u v w x y z : A) : Prop :=
  x;y ⊓ z;w ⊓ u;v ≤ x;((x⁻¹;z ⊓ y;w⁻¹);(z⁻¹;u ⊓ w;v⁻¹) ⊓ x⁻¹;u ⊓ y;v⁻¹);v

def isMtrue (t u v w x y z : A) : Prop := sorry
  --t ⊓ (u ⊓ v;w);(x ⊓ y;z) ≤ x ; ((x⁻¹ ; z ⊓ y ; w⁻¹) ; (z⁻¹ ; u ⊓ w ; v⁻¹) ⊓ x⁻¹ ; u ⊓ y ; v⁻¹) ; v



-- Note on Aesop: Simp Lemmas are used by aesop when recursively simplifying what the goal or hypothesis --> they call these normalisation rules and are customizsable. Aesop is essentially recursively making use of the best possible normalisation rule and making obvious deductions


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

variable (X : Type u) --(R : Set (X × X))

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
  le_trans := by sorry
  le_antisymm := by sorry
  le_sup_left := by sorry
  le_sup_right := by sorry
  sup_le := by sorry
  le_inf := by sorry
  inf_le_left := by sorry
  inf_le_right := by sorry
  le_sup_inf := by sorry
  inf_compl_le_bot := by sorry
  top_le_sup_compl := by sorry
  bot_le := by sorry
  le_top := by sorry
  assoc x y z := by sorry
  rdist x y z := by sorry
  comp_one x := by sorry
  conv_conv x := by sorry
  conv_dist x y := by sorry
  conv_comp x y := by sorry
  schroeder x y := by sorry

--instance : Comp A where
-- comp := λ x y => x ; y

#check Finset X
#check Fintype X

class Ternary (S : Type) where
  ternary : S → S → S → Prop

notation "R "  => Ternary.ternary

class Unary (S : Type) where
  unary : S → Prop

prefix:90 "I "  => Unary.unary

class AtomStructure (S : Type) extends Ternary S, Inv S, Unary S where
  peirce1 : ∀ x y z : S, R x y z ↔ R x⁻¹ z y
  peirce2 : ∀ x y z : S, R x y z ↔ R z y⁻¹ x
  id : ∃ x : S, I x
  identity1 : ∀ x y u : S, I u ∧ R x u y → x = y
  identity2 : ∀ x y : S, ∃ u : S, x = y → I u ∧ R x u y
  assoc : ∀ u x y z w : S, R x y u ∧ R u z w → ∃ v : S, R y z v ∧ R x v w

open AtomStructure

variable {S : Type} [AtomStructure S]

lemma conv_conv1 (x : S) : x⁻¹⁻¹ = x := by
  have h : ∃ e : S, x = x → I e ∧ R x e x := identity2 x x
  cases' h with e em
  have h' : I e ∧ R x e x := em rfl
  have h'' : I e := h'.1
  have h''' : R x e x := h'.2
  have h1 : R x⁻¹ x e := by rw [peirce1] at h'''; exact h'''
  have h2 : R x⁻¹⁻¹ e x := by rw [peirce1] at h1; exact h1
  have h3 : I e ∧ R x⁻¹⁻¹ e x → x⁻¹⁻¹ = x := identity1 x⁻¹⁻¹ x e
  exact h3 ⟨h'', h2⟩

/- define atom structure with atoms e, a, b and relations
  R e e e, R e a a, R e b b,
  R a e a, R a a b, R a b e,
  R b e b, R b a e, R b b a -/

#check (0 : Fin 3)

/- The group Z_3 as atom structure -/
inductive Z₃ : Type | e : Z₃ | a : Z₃ | b : Z₃
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
  id := by cases e <;> exact ⟨e, trivial⟩
  peirce1 x y z := by cases x <;> cases y <;> cases z <;> rfl
  peirce2 x y z := by cases x <;> cases y <;> cases z <;> rfl
  identity1 x y u := by sorry --cases x <;> cases y <;> cases u <;> ((intro; rfl) <|> (intro h; exact False.elim h.1))
  identity2 x y := by cases x <;> cases y <;> (exists e <;> intro; trivial)
  assoc u x y z w := by sorry --cases u <;> cases x <;> cases y <;> cases z <;> cases w <;> use aesop

  --aesop struggles with existential quantifiers because it has troubles providing witness (concrete examaples) for the cases.

  -- can implement the cases with tactic, the "with" keyword is used to provide the witness for the existential quantifier

--#eval R a e a

example : I a ∧ R a a e → e = a := by
  intro h
  have k : I a := by exact h.1
  have : False := by simp at k; exact k
  exact False.elim this
/-
example : I a = False := by
  have : I a := by exact trivial
  have : False := by simp at this; exact this
  exact False.elim this
-/
example : I e ∧ R a a e → e = e := by intro; rfl

lemma peirce3 (x y z : S) : R x y z ↔ R y⁻¹ x⁻¹ z⁻¹ := by
  rw [peirce1, peirce2, peirce1]

--assoc : ∀ u x y z w : S, R  x  y   u   ∧ R u   z   w → ∃ v : S, R y z v ∧ R x v w
--                         R z⁻¹ y⁻¹ v⁻¹ ∧ R v⁻¹ x⁻¹ w⁻¹




lemma assocr (u x y z w : S) : R y z v ∧ R x v w → ∃ u : S, R x y u ∧ R u z w := by
  rintro ⟨hyzv, hxvw⟩ --Destructure the conjunction hypothesis
  have hxvw' : R v⁻¹ x⁻¹ w⁻¹ := (peirce3 x v w).mp hxvw
  have hyzv' : R z⁻¹ y⁻¹ v⁻¹ := (peirce3 y z v).mp hyzv
  have hand : R z⁻¹ y⁻¹ v⁻¹ ∧ R v⁻¹ x⁻¹ w⁻¹ := ⟨hyzv', hxvw'⟩
  have h : ∃ t : S, R y⁻¹ x⁻¹ t ∧ R z⁻¹ t w⁻¹ := (AtomStructure.assoc v⁻¹ z⁻¹ y⁻¹ x⁻¹ w⁻¹) hand
  cases' h with c mh
  have h1 : R x⁻¹⁻¹ y⁻¹⁻¹ c⁻¹ := (peirce3 _ _ _).mp mh.1
  have h2 : R c⁻¹ z⁻¹⁻¹ w⁻¹⁻¹ := (peirce3 _ _ _).mp mh.2
  have h3 : R x y c⁻¹ := by rw [conv_conv1, conv_conv1] at h1; exact h1
  have h4 : R c⁻¹ z w := by rw [conv_conv1, conv_conv1] at h2; exact h2
  use c⁻¹



/-
  have hxvw'' : R y⁻¹ x⁻¹ m := hxvw'
  have hyzv'' : R z⁻¹ t w⁻¹ := by exact hyzv'
  have u := t
  have u := m
  have hxvw''' : R x y u := (peirce3 y⁻¹ x⁻¹ m).mpr hxvw''
  have hyzv''' : R u z w := (peirce3 z⁻¹ t w⁻¹).mpr hyzv''

  exact ⟨u, hxvw''', hyzv'''⟩
-/
  -- show m = t
  --apply peirce laws to hxvw'' and hyzv''
  --substitute u

/-
The ternary operator describes whether the relation between the three relations holds or not.

If given these mappings:
((y: b->c ∧ z: c->d ) ( v: b->d ))
((x: a->b ∧ v: b->d ) ( w: a->d ))

We can deduce these mappings:

We already know x and y are true, so we can deduce u is true
((x: a->b ∧ y: b->c ) ( u: a->c ))

Now that we have u, we can complete the picture and show how u is related to z and w
((u: a->c ∧ z: c->d ) ( w: a->d ))

NOTE: there are no mappings that take "d" as an input, which I think may point to the fact of this proof being right associative.

x: a->b y: b->c z: c->d

QUESTION: How do I want to define the inverses of each mapping? ANSWER: By switching the input and output, for ex: v inverse is u.

It follows then that I should be able to use peirce laws to manipulate these equalities and show that there exists a U which gives way to two other true ternary relations.
  --> It makes sense for inverses to not be composable

-/
