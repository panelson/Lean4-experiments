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


instance Prop.instBooleanAlgebra1 : BooleanAlgebra Prop where
  __ := Prop.instHeytingAlgebra
  __ := GeneralizedHeytingAlgebra.toDistribLattice
  compl := Not
  himp_eq _ _ := propext imp_iff_or_not
  inf_compl_le_bot _ H := H.2 H.1
  top_le_sup_compl p _ := Classical.em p

instance instBooleanAlgebra : BooleanAlgebra (Set (X × X)) :=
  { (inferInstance : BooleanAlgebra ((X × X) → Prop)) with
    sup := (· ∪ ·),
    inf := (· ∩ ·),
    bot := ∅,
    compl := (·ᶜ),
    top := Set.univ,
    sdiff := (· \ ·) }

#print Multiset

#print inferInstance

instance fullRA : RelationAlgebra (Set (X × X)) where
  bot := ∅
  top := Set.univ
  sup := (· ∪ ·)
  inf := (· ∩ ·)
  le := (· ≤ ·)
  lt := fun s t => s ⊆ t ∧ ¬t ⊆ s
  sdiff := (· \ ·)
  compl := (·ᶜ)
  comp R S := { (x, y) | ∃ z, (x, z) ∈ R ∧ (z, y) ∈ S }
  one := { (x, y) | x = y }
  inv R := { (y, x) | (x, y) ∈ R }
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

variable {G : Type u} [Group G]

instance : RelationAlgebra (Set G) where
  comp X Y := { z | ∃ x ∈ X, ∃ y ∈ Y, z = x * y }
  one := { 1 }
  inv X := { x⁻¹ | x ∈ X }
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

--Want comp :
S → S → Finset S
--Or
#check S → S → Set S

structure AtomStruct (S : Type) extends Ternary S, Inv S, Unary S where
  peirce1 : ∀ x y z : S, R x y z ↔ R x⁻¹ z y
  peirce2 : ∀ x y z : S, R x y z ↔ R z y⁻¹ x
  id : ∃ x : S, I x
  identity1 : ∀ x y u : S, I u ∧ R x u y → x = y
  identity2 : ∀ x y : S, ∃ u : S, x = y → I u ∧ R x u y
  assoc : ∀ u x y z w : S, R x y u ∧ R u z w → ∃ v : S, R y z v ∧ R x v w
/-
structure AtomStruct

[[0,1,2],
   [1,2,0],
   [2,0,1]]-/

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

/--Roger Maddux's list of integral 4-atom relation algebras given by cycles-/

def RA37 := [[[]],
[ [1],          [2,2,2],          [1,2,2], [2,1,2]],
[ [2], [1,1,1], [2,2,2],          [1,2,2], [2,1,2]],
[ [3],                   [2,2,3], [1,2,2], [2,1,2]],
[ [4], [1,1,1],          [2,2,3], [1,2,2], [2,1,2]],
[ [5],          [2,2,2], [2,2,3], [1,2,2], [2,1,2]],
[ [6], [1,1,1], [2,2,2], [2,2,3], [1,2,2], [2,1,2]],
[ [7],          [2,2,2],                            [2,1,1]],
[ [8], [1,1,1], [2,2,2],                            [2,1,1]],
[ [9],                   [2,2,3],                   [2,1,1]],
[[10], [1,1,1],          [2,2,3],                   [2,1,1]],
[[11],          [2,2,2], [2,2,3],                   [2,1,1]],
[[12], [1,1,1], [2,2,2], [2,2,3],                   [2,1,1]],
[[13], [1,1,1], [2,2,2],          [1,2,2],          [2,1,1]],
[[14],          [2,2,2],          [1,2,2], [2,1,2], [2,1,1]],
[[15], [1,1,1], [2,2,2],          [1,2,2], [2,1,2], [2,1,1]],
[[16],          [2,2,2], [2,2,3], [1,2,2], [2,1,2], [2,1,1]],
[[17], [1,1,1], [2,2,2], [2,2,3], [1,2,2], [2,1,2], [2,1,1]],
[[18],                                                       [2,2,1]],
[[19],          [2,2,2], [2,2,3],                            [2,2,1]],
[[20], [1,1,1],                   [1,2,2], [2,1,2],          [2,2,1]],
[[21], [1,1,1], [2,2,2],          [1,2,2], [2,1,2],          [2,2,1]],
[[22], [1,1,1], [2,2,2], [2,2,3], [1,2,2], [2,1,2],          [2,2,1]],
[[23],          [2,2,2],                            [2,1,1], [2,2,1]],
[[24], [1,1,1], [2,2,2],                            [2,1,1], [2,2,1]],
[[25],          [2,2,2], [2,2,3],                   [2,1,1], [2,2,1]],
[[26], [1,1,1], [2,2,2], [2,2,3],                   [2,1,1], [2,2,1]],
[[27],          [2,2,2],          [1,2,2],          [2,1,1], [2,2,1]],
[[28], [1,1,1], [2,2,2],          [1,2,2],          [2,1,1], [2,2,1]],
[[29],          [2,2,2], [2,2,3], [1,2,2],          [2,1,1], [2,2,1]],
[[30], [1,1,1], [2,2,2], [2,2,3], [1,2,2],          [2,1,1], [2,2,1]],
[[31], [1,1,1],                   [1,2,2], [2,1,2], [2,1,1], [2,2,1]],
[[32],          [2,2,2],          [1,2,2], [2,1,2], [2,1,1], [2,2,1]],
[[33], [1,1,1], [2,2,2],          [1,2,2], [2,1,2], [2,1,1], [2,2,1]],
[[34],                   [2,2,3], [1,2,2], [2,1,2], [2,1,1], [2,2,1]],
[[35], [1,1,1],          [2,2,3], [1,2,2], [2,1,2], [2,1,1], [2,2,1]],
[[36],          [2,2,2], [2,2,3], [1,2,2], [2,1,2], [2,1,1], [2,2,1]],
[[37], [1,1,1], [2,2,2], [2,2,3], [1,2,2], [2,1,2], [2,1,1], [2,2,1]]
]

#eval RA37[2]
--     [1,1,1], [2,2,2], [3,3,3], [1,2,2], [2,1,1], [1,3,3], [3,1,1], [2,3,3], [3,2,2], [1,2,3]],
def RA65 := [
[ [1],                            [1,2,2],          [1,3,3],          [2,3,3]],
[ [2], [1,1,1],                   [1,2,2],          [1,3,3],          [2,3,3]],
[ [3],          [2,2,2],          [1,2,2],          [1,3,3],          [2,3,3]],
[ [4], [1,1,1], [2,2,2],          [1,2,2],          [1,3,3],          [2,3,3]],
[ [5],                   [3,3,3], [1,2,2],          [1,3,3],          [2,3,3]],
[ [6], [1,1,1],          [3,3,3], [1,2,2],          [1,3,3],          [2,3,3]],
[ [7],          [2,2,2], [3,3,3], [1,2,2],          [1,3,3],          [2,3,3]],
[ [8], [1,1,1], [2,2,2], [3,3,3], [1,2,2],          [1,3,3],          [2,3,3]],
[ [9],                            [1,2,2], [2,1,1], [1,3,3],          [2,3,3]],
[[10], [1,1,1],                   [1,2,2], [2,1,1], [1,3,3],          [2,3,3]],
[[11], [1,1,1], [2,2,2],          [1,2,2], [2,1,1], [1,3,3],          [2,3,3]],
[[12],                   [3,3,3], [1,2,2], [2,1,1], [1,3,3],          [2,3,3]],
[[13], [1,1,1],          [3,3,3], [1,2,2], [2,1,1], [1,3,3],          [2,3,3]],
[[14], [1,1,1], [2,2,2], [3,3,3], [1,2,2], [2,1,1], [1,3,3],          [2,3,3]],
[[15],                                     [2,1,1], [1,3,3], [3,1,1], [2,3,3]],
[[16], [1,1,1],                            [2,1,1], [1,3,3], [3,1,1], [2,3,3]],
[[17],          [2,2,2],                   [2,1,1], [1,3,3], [3,1,1], [2,3,3]],
[[18], [1,1,1], [2,2,2],                   [2,1,1], [1,3,3], [3,1,1], [2,3,3]],
[[19], [1,1,1],          [3,3,3],          [2,1,1], [1,3,3], [3,1,1], [2,3,3]],
[[20], [1,1,1], [2,2,2], [3,3,3],          [2,1,1], [1,3,3], [3,1,1], [2,3,3]],
[[21],                            [1,2,2], [2,1,1], [1,3,3], [3,1,1], [2,3,3], [3,2,2]],
[[22], [1,1,1],                   [1,2,2], [2,1,1], [1,3,3], [3,1,1], [2,3,3], [3,2,2]],
[[23], [1,1,1], [2,2,2],          [1,2,2], [2,1,1], [1,3,3], [3,1,1], [2,3,3], [3,2,2]],
[[24], [1,1,1], [2,2,2], [3,3,3], [1,2,2], [2,1,1], [1,3,3], [3,1,1], [2,3,3], [3,2,2]],
[[25],                                                                                  [1,2,3]],
[[26], [1,1,1],                   [1,2,2],                                              [1,2,3]],
[[27], [1,1,1], [2,2,2],          [1,2,2], [2,1,1],                                     [1,2,3]],
[[28], [1,1,1],                   [1,2,2],          [1,3,3],                            [1,2,3]],
[[29], [1,1,1], [2,2,2], [3,3,3],          [2,1,1],          [3,1,1],                   [1,2,3]],
[[30], [1,1,1],          [3,3,3], [1,2,2], [2,1,1],          [3,1,1],                   [1,2,3]],
[[31], [1,1,1], [2,2,2], [3,3,3], [1,2,2], [2,1,1],          [3,1,1],                   [1,2,3]],
[[32], [1,1,1],                   [1,2,2], [2,1,1], [1,3,3], [3,1,1],                   [1,2,3]],
[[33], [1,1,1], [2,2,2],          [1,2,2], [2,1,1], [1,3,3], [3,1,1],                   [1,2,3]],
[[34], [1,1,1], [2,2,2], [3,3,3], [1,2,2], [2,1,1], [1,3,3], [3,1,1],                   [1,2,3]],
[[35], [1,1,1], [2,2,2],          [1,2,2],          [1,3,3],          [2,3,3],          [1,2,3]],
[[36], [1,1,1], [2,2,2], [3,3,3], [1,2,2],          [1,3,3],          [2,3,3],          [1,2,3]],
[[37], [1,1,1], [2,2,2],          [1,2,2], [2,1,1], [1,3,3],          [2,3,3],          [1,2,3]],
[[38], [1,1,1], [2,2,2], [3,3,3], [1,2,2], [2,1,1], [1,3,3],          [2,3,3],          [1,2,3]],
[[39],                            [1,2,2],                   [3,1,1], [2,3,3],          [1,2,3]],
[[40], [1,1,1],                   [1,2,2],                   [3,1,1], [2,3,3],          [1,2,3]],
[[41], [1,1,1], [2,2,2],          [1,2,2],                   [3,1,1], [2,3,3],          [1,2,3]],
[[42], [1,1,1], [2,2,2], [3,3,3], [1,2,2],                   [3,1,1], [2,3,3],          [1,2,3]],
[[43],                            [1,2,2], [2,1,1],          [3,1,1], [2,3,3],          [1,2,3]],
[[44], [1,1,1],                   [1,2,2], [2,1,1],          [3,1,1], [2,3,3],          [1,2,3]],
[[45],          [2,2,2],          [1,2,2], [2,1,1],          [3,1,1], [2,3,3],          [1,2,3]],
[[46], [1,1,1], [2,2,2],          [1,2,2], [2,1,1],          [3,1,1], [2,3,3],          [1,2,3]],
[[47],                   [3,3,3], [1,2,2], [2,1,1],          [3,1,1], [2,3,3],          [1,2,3]],
[[48], [1,1,1],          [3,3,3], [1,2,2], [2,1,1],          [3,1,1], [2,3,3],          [1,2,3]],
[[49],          [2,2,2], [3,3,3], [1,2,2], [2,1,1],          [3,1,1], [2,3,3],          [1,2,3]],
[[50], [1,1,1], [2,2,2], [3,3,3], [1,2,2], [2,1,1],          [3,1,1], [2,3,3],          [1,2,3]],
[[51],          [2,2,2],                   [2,1,1], [1,3,3], [3,1,1], [2,3,3],          [1,2,3]],
[[52], [1,1,1], [2,2,2],                   [2,1,1], [1,3,3], [3,1,1], [2,3,3],          [1,2,3]],
[[53], [1,1,1], [2,2,2], [3,3,3],          [2,1,1], [1,3,3], [3,1,1], [2,3,3],          [1,2,3]],
[[54],                            [1,2,2], [2,1,1], [1,3,3], [3,1,1], [2,3,3],          [1,2,3]],
[[55], [1,1,1],                   [1,2,2], [2,1,1], [1,3,3], [3,1,1], [2,3,3],          [1,2,3]],
[[56],          [2,2,2],          [1,2,2], [2,1,1], [1,3,3], [3,1,1], [2,3,3],          [1,2,3]],
[[57], [1,1,1], [2,2,2],          [1,2,2], [2,1,1], [1,3,3], [3,1,1], [2,3,3],          [1,2,3]],
[[58],                   [3,3,3], [1,2,2], [2,1,1], [1,3,3], [3,1,1], [2,3,3],          [1,2,3]],
[[59], [1,1,1],          [3,3,3], [1,2,2], [2,1,1], [1,3,3], [3,1,1], [2,3,3],          [1,2,3]],
[[60],          [2,2,2], [3,3,3], [1,2,2], [2,1,1], [1,3,3], [3,1,1], [2,3,3],          [1,2,3]],
[[61], [1,1,1], [2,2,2], [3,3,3], [1,2,2], [2,1,1], [1,3,3], [3,1,1], [2,3,3],          [1,2,3]],
[[62],                            [1,2,2], [2,1,1], [1,3,3], [3,1,1], [2,3,3], [3,2,2], [1,2,3]],
[[63], [1,1,1],                   [1,2,2], [2,1,1], [1,3,3], [3,1,1], [2,3,3], [3,2,2], [1,2,3]],
[[64], [1,1,1], [2,2,2],          [1,2,2], [2,1,1], [1,3,3], [3,1,1], [2,3,3], [3,2,2], [1,2,3]],
[[65], [1,1,1], [2,2,2], [3,3,3], [1,2,2], [2,1,1], [1,3,3], [3,1,1], [2,3,3], [3,2,2], [1,2,3]]
]
#check RA37
#check RA65
#eval RA65

-- RAbook1to5.py, Python file, 2025-03-06 by Peter Jipsen
-- based on Roger Maddux's GAP file ra1to3013.2-6-19
--
-- Finite integral relation algebras with up to 5 atoms in the format of
-- Roger Maddux's list of RAs in his Relation Algebra book (Elsevier, 2006)
-- a,c,c,d are self-converse, R is the converse of r, S is the converse of s
-- Identity cycles and other redundant cycles are not included.
-- In total there are 1+2+3+7+37+65+83+1316+3013 := 4537 RAs in this file.

def ra5 := [[
-- 1_1
[""]
],
[
-- 1_2
[""],
-- 2_2
["aaa"]
],
[
-- 1_3
["rrr"],
-- 2_3
["rrR"],
-- 3_3
["rrr","rrR"]
],
[
-- 1_7
["abb"],
-- 2_7
["aaa","abb"],
-- 3_7
["bbb","abb"],
-- 4_7
["aaa","bbb","abb"],
-- 5_7
["abb","baa"],
-- 6_7
["aaa","abb","baa"],
-- 7_7
["aaa","bbb","abb","baa"]
],
[
-- 1_37
["rrr","arr","rar"],
-- 2_37
["aaa","rrr","arr","rar"],
-- 3_37
["rrR","arr","rar"],
-- 4_37
["aaa","rrR","arr","rar"],
-- 5_37
["rrr","rrR","arr","rar"],
-- 6_37
["aaa","rrr","rrR","arr","rar"],
-- 7_37
["rrr","raa"],
-- 8_37
["aaa","rrr","raa"],
-- 9_37
["rrR","raa"],
-- 10_37
["aaa","rrR","raa"],
-- 11_37
["rrr","rrR","raa"],
-- 12_37
["aaa","rrr","rrR","raa"],
-- 13_37
["aaa","rrr","arr","raa"],
-- 14_37
["rrr","arr","rar","raa"],
-- 15_37
["aaa","rrr","arr","rar","raa"],
-- 16_37
["rrr","rrR","arr","rar","raa"],
-- 17_37
["aaa","rrr","rrR","arr","rar","raa"],
-- 18_37
["rra"],
-- 19_37
["rrr","rrR","rra"],
-- 20_37
["aaa","arr","rar","rra"],
-- 21_37
["aaa","rrr","arr","rar","rra"],
-- 22_37
["aaa","rrr","rrR","arr","rar","rra"],
-- 23_37
["rrr","raa","rra"],
-- 24_37
["aaa","rrr","raa","rra"],
-- 25_37
["rrr","rrR","raa","rra"],
-- 26_37
["aaa","rrr","rrR","raa","rra"],
-- 27_37
["rrr","arr","raa","rra"],
-- 28_37
["aaa","rrr","arr","raa","rra"],
-- 29_37
["rrr","rrR","arr","raa","rra"],
-- 30_37
["aaa","rrr","rrR","arr","raa","rra"],
-- 31_37
["aaa","arr","rar","raa","rra"],
-- 32_37
["rrr","arr","rar","raa","rra"],
-- 33_37
["aaa","rrr","arr","rar","raa","rra"],
-- 34_37
["rrR","arr","rar","raa","rra"],
-- 35_37
["aaa","rrR","arr","rar","raa","rra"],
-- 36_37
["rrr","rrR","arr","rar","raa","rra"],
-- 37_37
["aaa","rrr","rrR","arr","rar","raa","rra"]
],
[
-- 1_65
["abb","acc","bcc"],
-- 2_65
["aaa","abb","acc","bcc"],
-- 3_65
["bbb","abb","acc","bcc"],
-- 4_65
["aaa","bbb","abb","acc","bcc"],
-- 5_65
["ccc","abb","acc","bcc"],
-- 6_65
["aaa","ccc","abb","acc","bcc"],
-- 7_65
["bbb","ccc","abb","acc","bcc"],
-- 8_65
["aaa","bbb","ccc","abb","acc","bcc"],
-- 9_65
["abb","baa","acc","bcc"],
-- 10_65
["aaa","abb","baa","acc","bcc"],
-- 11_65
["aaa","bbb","abb","baa","acc","bcc"],
-- 12_65
["ccc","abb","baa","acc","bcc"],
-- 13_65
["aaa","ccc","abb","baa","acc","bcc"],
-- 14_65
["aaa","bbb","ccc","abb","baa","acc","bcc"],
-- 15_65
["baa","acc","caa","bcc"],
-- 16_65
["aaa","baa","acc","caa","bcc"],
-- 17_65
["bbb","baa","acc","caa","bcc"],
-- 18_65
["aaa","bbb","baa","acc","caa","bcc"],
-- 19_65
["aaa","ccc","baa","acc","caa","bcc"],
-- 20_65
["aaa","bbb","ccc","baa","acc","caa","bcc"],
-- 21_65
["abb","baa","acc","caa","bcc","cbb"],
-- 22_65
["aaa","abb","baa","acc","caa","bcc","cbb"],
-- 23_65
["aaa","bbb","abb","baa","acc","caa","bcc","cbb"],
-- 24_65
["aaa","bbb","ccc","abb","baa","acc","caa","bcc","cbb"],
-- 25_65
["abc"],
-- 26_65
["aaa","abb","abc"],
-- 27_65
["aaa","bbb","abb","baa","abc"],
-- 28_65
["aaa","abb","acc","abc"],
-- 29_65
["aaa","bbb","ccc","baa","caa","abc"],
-- 30_65
["aaa","ccc","abb","baa","caa","abc"],
-- 31_65
["aaa","bbb","ccc","abb","baa","caa","abc"],
-- 32_65
["aaa","abb","baa","acc","caa","abc"],
-- 33_65
["aaa","bbb","abb","baa","acc","caa","abc"],
-- 34_65
["aaa","bbb","ccc","abb","baa","acc","caa","abc"],
-- 35_65
["aaa","bbb","abb","acc","bcc","abc"],
-- 36_65
["aaa","bbb","ccc","abb","acc","bcc","abc"],
-- 37_65
["aaa","bbb","abb","baa","acc","bcc","abc"],
-- 38_65
["aaa","bbb","ccc","abb","baa","acc","bcc","abc"],
-- 39_65
["abb","caa","bcc","abc"],
-- 40_65
["aaa","abb","caa","bcc","abc"],
-- 41_65
["aaa","bbb","abb","caa","bcc","abc"],
-- 42_65
["aaa","bbb","ccc","abb","caa","bcc","abc"],
-- 43_65
["abb","baa","caa","bcc","abc"],
-- 44_65
["aaa","abb","baa","caa","bcc","abc"],
-- 45_65
["bbb","abb","baa","caa","bcc","abc"],
-- 46_65
["aaa","bbb","abb","baa","caa","bcc","abc"],
-- 47_65
["ccc","abb","baa","caa","bcc","abc"],
-- 48_65
["aaa","ccc","abb","baa","caa","bcc","abc"],
-- 49_65
["bbb","ccc","abb","baa","caa","bcc","abc"],
-- 50_65
["aaa","bbb","ccc","abb","baa","caa","bcc","abc"],
-- 51_65
["bbb","baa","acc","caa","bcc","abc"],
-- 52_65
["aaa","bbb","baa","acc","caa","bcc","abc"],
-- 53_65
["aaa","bbb","ccc","baa","acc","caa","bcc","abc"],
-- 54_65
["abb","baa","acc","caa","bcc","abc"],
-- 55_65
["aaa","abb","baa","acc","caa","bcc","abc"],
-- 56_65
["bbb","abb","baa","acc","caa","bcc","abc"],
-- 57_65
["aaa","bbb","abb","baa","acc","caa","bcc","abc"],
-- 58_65
["ccc","abb","baa","acc","caa","bcc","abc"],
-- 59_65
["aaa","ccc","abb","baa","acc","caa","bcc","abc"],
-- 60_65
["bbb","ccc","abb","baa","acc","caa","bcc","abc"],
-- 61_65
["aaa","bbb","ccc","abb","baa","acc","caa","bcc","abc"],
-- 62_65
["abb","baa","acc","caa","bcc","cbb","abc"],
-- 63_65
["aaa","abb","baa","acc","caa","bcc","cbb","abc"],
-- 64_65
["aaa","bbb","abb","baa","acc","caa","bcc","cbb","abc"],
-- 65_65
["aaa","bbb","ccc","abb","baa","acc","caa","bcc","cbb","abc"]
],
[
-- 1_83
["rrS","ssr"],
-- 2_83
["rrr","sss","srr","rsr"],
-- 3_83
["sss","rrR","srr","rsr"],
-- 4_83
["rrr","sss","rrR","srr","rsr"],
-- 5_83
["rrr","ssS","srr","rsr"],
-- 6_83
["rrr","sss","ssS","srr","rsr"],
-- 7_83
["rrR","ssS","srr","rsr"],
-- 8_83
["rrr","rrR","ssS","srr","rsr"],
-- 9_83
["sss","rrR","ssS","srr","rsr"],
-- 10_83
["rrr","sss","rrR","ssS","srr","rsr"],
-- 11_83
["sss","rrs","srr","rsr"],
-- 12_83
["rrr","sss","rrs","srr","rsr"],
-- 13_83
["rrr","sss","rrR","rrs","srr","rsr"],
-- 14_83
["sss","rrs","rrS","srr","rsr"],
-- 15_83
["rrr","sss","rrs","rrS","srr","rsr"],
-- 16_83
["rrr","sss","rrR","rrs","rrS","srr","rsr"],
-- 17_83
["sss","ssS","rrs","rrS","srr","rsr"],
-- 18_83
["rrr","sss","ssS","rrs","rrS","srr","rsr"],
-- 19_83
["rrr","sss","rrR","ssS","rrs","rrS","srr","rsr"],
-- 20_83
["sss","rrR","rrS","ssr","srr","rsr"],
-- 21_83
["sss","rrs","rrS","ssr","ssR","srr","rsr"],
-- 22_83
["rrr","sss","rrs","rrS","ssr","ssR","srr","rsr"],
-- 23_83
["sss","rrR","rrs","rrS","ssr","ssR","srr","rsr"],
-- 24_83
["rrr","sss","rrR","rrs","rrS","ssr","ssR","srr","rsr"],
-- 25_83
["sss","ssS","rrs","rrS","ssr","ssR","srr","rsr"],
-- 26_83
["rrr","sss","ssS","rrs","rrS","ssr","ssR","srr","rsr"],
-- 27_83
["sss","rrR","ssS","rrs","rrS","ssr","ssR","srr","rsr"],
-- 28_83
["rrr","sss","rrR","ssS","rrs","rrS","ssr","ssR","srr","rsr"],
-- 29_83
["rrr","sss","srr","rsr","rss"],
-- 30_83
["rrr","sss","rrR","srr","rsr","rss"],
-- 31_83
["rrr","sss","rrs","srr","rsr","rss"],
-- 32_83
["rrr","sss","rrR","rrs","srr","rsr","rss"],
-- 33_83
["rrr","sss","rrs","rrS","srr","rsr","rss"],
-- 34_83
["rrr","sss","rrR","rrs","rrS","srr","rsr","rss"],
-- 35_83
["sss","rrs","rrS","ssr","ssR","srr","rsr","rss"],
-- 36_83
["rrr","sss","rrs","rrS","ssr","ssR","srr","rsr","rss"],
-- 37_83
["sss","rrR","rrs","rrS","ssr","ssR","srr","rsr","rss"],
-- 38_83
["rrr","sss","rrR","rrs","rrS","ssr","ssR","srr","rsr","rss"],
-- 39_83
["sss","ssS","rrs","rrS","ssr","ssR","srr","rsr","rss"],
-- 40_83
["rrr","sss","ssS","rrs","rrS","ssr","ssR","srr","rsr","rss"],
-- 41_83
["sss","rrR","ssS","rrs","rrS","ssr","ssR","srr","rsr","rss"],
-- 42_83
["rrr","sss","rrR","ssS","rrs","rrS","ssr","ssR","srr","rsr","rss"],
-- 43_83
["rrr","sss","srr","rsr","rss","srs"],
-- 44_83
["rrr","sss","rrR","srr","rsr","rss","srs"],
-- 45_83
["rrr","sss","rrR","ssS","srr","rsr","rss","srs"],
-- 46_83
["rrr","sss","rrs","srr","rsr","rss","srs"],
-- 47_83
["sss","rrR","rrs","srr","rsr","rss","srs"],
-- 48_83
["rrr","sss","rrR","rrs","srr","rsr","rss","srs"],
-- 49_83
["sss","rrs","rrS","srr","rsr","rss","srs"],
-- 50_83
["rrr","sss","rrs","rrS","srr","rsr","rss","srs"],
-- 51_83
["sss","rrR","rrs","rrS","srr","rsr","rss","srs"],
-- 52_83
["rrr","sss","rrR","rrs","rrS","srr","rsr","rss","srs"],
-- 53_83
["sss","ssS","rrs","rrS","srr","rsr","rss","srs"],
-- 54_83
["rrr","sss","ssS","rrs","rrS","srr","rsr","rss","srs"],
-- 55_83
["sss","rrR","ssS","rrs","rrS","srr","rsr","rss","srs"],
-- 56_83
["rrr","sss","rrR","ssS","rrs","rrS","srr","rsr","rss","srs"],
-- 57_83
["rrr","rrs","ssr","srr","rsr","rss","srs"],
-- 58_83
["rrr","sss","rrs","ssr","srr","rsr","rss","srs"],
-- 59_83
["rrr","sss","rrS","ssr","srr","rsr","rss","srs"],
-- 60_83
["rrr","sss","rrR","rrS","ssr","srr","rsr","rss","srs"],
-- 61_83
["rrR","ssS","rrS","ssr","srr","rsr","rss","srs"],
-- 62_83
["rrr","rrR","ssS","rrS","ssr","srr","rsr","rss","srs"],
-- 63_83
["rrr","sss","rrR","ssS","rrS","ssr","srr","rsr","rss","srs"],
-- 64_83
["sss","rrs","rrS","ssr","srr","rsr","rss","srs"],
-- 65_83
["rrr","sss","rrs","rrS","ssr","srr","rsr","rss","srs"],
-- 66_83
["rrr","rrR","rrs","rrS","ssr","srr","rsr","rss","srs"],
-- 67_83
["sss","rrR","rrs","rrS","ssr","srr","rsr","rss","srs"],
-- 68_83
["rrr","sss","rrR","rrs","rrS","ssr","srr","rsr","rss","srs"],
-- 69_83
["rrr","ssS","rrs","rrS","ssr","srr","rsr","rss","srs"],
-- 70_83
["sss","ssS","rrs","rrS","ssr","srr","rsr","rss","srs"],
-- 71_83
["rrr","sss","ssS","rrs","rrS","ssr","srr","rsr","rss","srs"],
-- 72_83
["rrR","ssS","rrs","rrS","ssr","srr","rsr","rss","srs"],
-- 73_83
["rrr","rrR","ssS","rrs","rrS","ssr","srr","rsr","rss","srs"],
-- 74_83
["sss","rrR","ssS","rrs","rrS","ssr","srr","rsr","rss","srs"],
-- 75_83
["rrr","sss","rrR","ssS","rrs","rrS","ssr","srr","rsr","rss","srs"],
-- 76_83
["rrr","rrs","rrS","ssr","ssR","srr","rsr","rss","srs"],
-- 77_83
["rrr","sss","rrs","rrS","ssr","ssR","srr","rsr","rss","srs"],
-- 78_83
["rrr","rrR","rrs","rrS","ssr","ssR","srr","rsr","rss","srs"],
-- 79_83
["sss","rrR","rrs","rrS","ssr","ssR","srr","rsr","rss","srs"],
-- 80_83
["rrr","sss","rrR","rrs","rrS","ssr","ssR","srr","rsr","rss","srs"],
-- 81_83
["rrR","ssS","rrs","rrS","ssr","ssR","srr","rsr","rss","srs"],
-- 82_83
["rrr","rrR","ssS","rrs","rrS","ssr","ssR","srr","rsr","rss","srs"],
-- 83_83
["rrr","sss","rrR","ssS","rrs","rrS","ssr","ssR","srr","rsr","rss","srs"]
],
[
-- 1_1316
["rrr","abb","arr","rar","brr","rbr"],
-- 2_1316
["aaa","rrr","abb","arr","rar","brr","rbr"],
-- 3_1316
["bbb","rrr","abb","arr","rar","brr","rbr"],
-- 4_1316
["aaa","bbb","rrr","abb","arr","rar","brr","rbr"],
-- 5_1316
["rrR","abb","arr","rar","brr","rbr"],
-- 6_1316
["aaa","rrR","abb","arr","rar","brr","rbr"],
-- 7_1316
["bbb","rrR","abb","arr","rar","brr","rbr"],
-- 8_1316
["aaa","bbb","rrR","abb","arr","rar","brr","rbr"],
-- 9_1316
["rrr","rrR","abb","arr","rar","brr","rbr"],
-- 10_1316
["aaa","rrr","rrR","abb","arr","rar","brr","rbr"],
-- 11_1316
["bbb","rrr","rrR","abb","arr","rar","brr","rbr"],
-- 12_1316
["aaa","bbb","rrr","rrR","abb","arr","rar","brr","rbr"],
-- 13_1316
["rrr","abb","baa","arr","rar","brr","rbr"],
-- 14_1316
["aaa","rrr","abb","baa","arr","rar","brr","rbr"],
-- 15_1316
["aaa","bbb","rrr","abb","baa","arr","rar","brr","rbr"],
-- 16_1316
["rrR","abb","baa","arr","rar","brr","rbr"],
-- 17_1316
["aaa","rrR","abb","baa","arr","rar","brr","rbr"],
-- 18_1316
["aaa","bbb","rrR","abb","baa","arr","rar","brr","rbr"],
-- 19_1316
["rrr","rrR","abb","baa","arr","rar","brr","rbr"],
-- 20_1316
["aaa","rrr","rrR","abb","baa","arr","rar","brr","rbr"],
-- 21_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","rar","brr","rbr"],
-- 22_1316
["rrr","baa","brr","rbr","raa"],
-- 23_1316
["aaa","rrr","baa","brr","rbr","raa"],
-- 24_1316
["bbb","rrr","baa","brr","rbr","raa"],
-- 25_1316
["aaa","bbb","rrr","baa","brr","rbr","raa"],
-- 26_1316
["rrR","baa","brr","rbr","raa"],
-- 27_1316
["aaa","rrR","baa","brr","rbr","raa"],
-- 28_1316
["bbb","rrR","baa","brr","rbr","raa"],
-- 29_1316
["aaa","bbb","rrR","baa","brr","rbr","raa"],
-- 30_1316
["rrr","rrR","baa","brr","rbr","raa"],
-- 31_1316
["aaa","rrr","rrR","baa","brr","rbr","raa"],
-- 32_1316
["bbb","rrr","rrR","baa","brr","rbr","raa"],
-- 33_1316
["aaa","bbb","rrr","rrR","baa","brr","rbr","raa"],
-- 34_1316
["aaa","rrr","baa","arr","brr","rbr","raa"],
-- 35_1316
["aaa","bbb","rrr","baa","arr","brr","rbr","raa"],
-- 36_1316
["rrr","baa","arr","rar","brr","rbr","raa"],
-- 37_1316
["aaa","rrr","baa","arr","rar","brr","rbr","raa"],
-- 38_1316
["bbb","rrr","baa","arr","rar","brr","rbr","raa"],
-- 39_1316
["aaa","bbb","rrr","baa","arr","rar","brr","rbr","raa"],
-- 40_1316
["rrr","rrR","baa","arr","rar","brr","rbr","raa"],
-- 41_1316
["aaa","rrr","rrR","baa","arr","rar","brr","rbr","raa"],
-- 42_1316
["bbb","rrr","rrR","baa","arr","rar","brr","rbr","raa"],
-- 43_1316
["aaa","bbb","rrr","rrR","baa","arr","rar","brr","rbr","raa"],
-- 44_1316
["rrr","abb","raa","rbb"],
-- 45_1316
["aaa","rrr","abb","raa","rbb"],
-- 46_1316
["bbb","rrr","abb","raa","rbb"],
-- 47_1316
["aaa","bbb","rrr","abb","raa","rbb"],
-- 48_1316
["rrR","abb","raa","rbb"],
-- 49_1316
["aaa","rrR","abb","raa","rbb"],
-- 50_1316
["bbb","rrR","abb","raa","rbb"],
-- 51_1316
["aaa","bbb","rrR","abb","raa","rbb"],
-- 52_1316
["rrr","rrR","abb","raa","rbb"],
-- 53_1316
["aaa","rrr","rrR","abb","raa","rbb"],
-- 54_1316
["bbb","rrr","rrR","abb","raa","rbb"],
-- 55_1316
["aaa","bbb","rrr","rrR","abb","raa","rbb"],
-- 56_1316
["rrr","abb","baa","raa","rbb"],
-- 57_1316
["aaa","rrr","abb","baa","raa","rbb"],
-- 58_1316
["aaa","bbb","rrr","abb","baa","raa","rbb"],
-- 59_1316
["rrR","abb","baa","raa","rbb"],
-- 60_1316
["aaa","rrR","abb","baa","raa","rbb"],
-- 61_1316
["aaa","bbb","rrR","abb","baa","raa","rbb"],
-- 62_1316
["rrr","rrR","abb","baa","raa","rbb"],
-- 63_1316
["aaa","rrr","rrR","abb","baa","raa","rbb"],
-- 64_1316
["aaa","bbb","rrr","rrR","abb","baa","raa","rbb"],
-- 65_1316
["aaa","rrr","abb","arr","raa","rbb"],
-- 66_1316
["aaa","bbb","rrr","abb","arr","raa","rbb"],
-- 67_1316
["rrr","abb","arr","rar","raa","rbb"],
-- 68_1316
["aaa","rrr","abb","arr","rar","raa","rbb"],
-- 69_1316
["bbb","rrr","abb","arr","rar","raa","rbb"],
-- 70_1316
["aaa","bbb","rrr","abb","arr","rar","raa","rbb"],
-- 71_1316
["rrr","rrR","abb","arr","rar","raa","rbb"],
-- 72_1316
["aaa","rrr","rrR","abb","arr","rar","raa","rbb"],
-- 73_1316
["bbb","rrr","rrR","abb","arr","rar","raa","rbb"],
-- 74_1316
["aaa","bbb","rrr","rrR","abb","arr","rar","raa","rbb"],
-- 75_1316
["aaa","bbb","rrr","abb","baa","arr","brr","raa","rbb"],
-- 76_1316
["rrr","abb","baa","arr","rar","brr","rbr","raa","rbb"],
-- 77_1316
["aaa","rrr","abb","baa","arr","rar","brr","rbr","raa","rbb"],
-- 78_1316
["aaa","bbb","rrr","abb","baa","arr","rar","brr","rbr","raa","rbb"],
-- 79_1316
["rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb"],
-- 80_1316
["aaa","rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb"],
-- 81_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb"],
-- 82_1316
["baa","brr","rbr","rra"],
-- 83_1316
["bbb","baa","brr","rbr","rra"],
-- 84_1316
["rrr","rrR","baa","brr","rbr","rra"],
-- 85_1316
["bbb","rrr","rrR","baa","brr","rbr","rra"],
-- 86_1316
["aaa","baa","arr","rar","brr","rbr","rra"],
-- 87_1316
["aaa","bbb","baa","arr","rar","brr","rbr","rra"],
-- 88_1316
["aaa","rrr","baa","arr","rar","brr","rbr","rra"],
-- 89_1316
["aaa","bbb","rrr","baa","arr","rar","brr","rbr","rra"],
-- 90_1316
["aaa","rrr","rrR","baa","arr","rar","brr","rbr","rra"],
-- 91_1316
["aaa","bbb","rrr","rrR","baa","arr","rar","brr","rbr","rra"],
-- 92_1316
["rrr","baa","brr","rbr","raa","rra"],
-- 93_1316
["aaa","rrr","baa","brr","rbr","raa","rra"],
-- 94_1316
["bbb","rrr","baa","brr","rbr","raa","rra"],
-- 95_1316
["aaa","bbb","rrr","baa","brr","rbr","raa","rra"],
-- 96_1316
["rrr","rrR","baa","brr","rbr","raa","rra"],
-- 97_1316
["aaa","rrr","rrR","baa","brr","rbr","raa","rra"],
-- 98_1316
["bbb","rrr","rrR","baa","brr","rbr","raa","rra"],
-- 99_1316
["aaa","bbb","rrr","rrR","baa","brr","rbr","raa","rra"],
-- 100_1316
["rrr","baa","arr","brr","rbr","raa","rra"],
-- 101_1316
["aaa","rrr","baa","arr","brr","rbr","raa","rra"],
-- 102_1316
["bbb","rrr","baa","arr","brr","rbr","raa","rra"],
-- 103_1316
["aaa","bbb","rrr","baa","arr","brr","rbr","raa","rra"],
-- 104_1316
["rrr","rrR","baa","arr","brr","rbr","raa","rra"],
-- 105_1316
["aaa","rrr","rrR","baa","arr","brr","rbr","raa","rra"],
-- 106_1316
["bbb","rrr","rrR","baa","arr","brr","rbr","raa","rra"],
-- 107_1316
["aaa","bbb","rrr","rrR","baa","arr","brr","rbr","raa","rra"],
-- 108_1316
["aaa","baa","arr","rar","brr","rbr","raa","rra"],
-- 109_1316
["aaa","bbb","baa","arr","rar","brr","rbr","raa","rra"],
-- 110_1316
["rrr","baa","arr","rar","brr","rbr","raa","rra"],
-- 111_1316
["aaa","rrr","baa","arr","rar","brr","rbr","raa","rra"],
-- 112_1316
["bbb","rrr","baa","arr","rar","brr","rbr","raa","rra"],
-- 113_1316
["aaa","bbb","rrr","baa","arr","rar","brr","rbr","raa","rra"],
-- 114_1316
["rrR","baa","arr","rar","brr","rbr","raa","rra"],
-- 115_1316
["aaa","rrR","baa","arr","rar","brr","rbr","raa","rra"],
-- 116_1316
["bbb","rrR","baa","arr","rar","brr","rbr","raa","rra"],
-- 117_1316
["aaa","bbb","rrR","baa","arr","rar","brr","rbr","raa","rra"],
-- 118_1316
["rrr","rrR","baa","arr","rar","brr","rbr","raa","rra"],
-- 119_1316
["aaa","rrr","rrR","baa","arr","rar","brr","rbr","raa","rra"],
-- 120_1316
["bbb","rrr","rrR","baa","arr","rar","brr","rbr","raa","rra"],
-- 121_1316
["aaa","bbb","rrr","rrR","baa","arr","rar","brr","rbr","raa","rra"],
-- 122_1316
["abb","rbb","rra"],
-- 123_1316
["bbb","abb","rbb","rra"],
-- 124_1316
["rrr","rrR","abb","rbb","rra"],
-- 125_1316
["bbb","rrr","rrR","abb","rbb","rra"],
-- 126_1316
["aaa","abb","arr","rar","rbb","rra"],
-- 127_1316
["aaa","bbb","abb","arr","rar","rbb","rra"],
-- 128_1316
["aaa","rrr","abb","arr","rar","rbb","rra"],
-- 129_1316
["aaa","bbb","rrr","abb","arr","rar","rbb","rra"],
-- 130_1316
["aaa","rrr","rrR","abb","arr","rar","rbb","rra"],
-- 131_1316
["aaa","bbb","rrr","rrR","abb","arr","rar","rbb","rra"],
-- 132_1316
["rrr","abb","raa","rbb","rra"],
-- 133_1316
["aaa","rrr","abb","raa","rbb","rra"],
-- 134_1316
["bbb","rrr","abb","raa","rbb","rra"],
-- 135_1316
["aaa","bbb","rrr","abb","raa","rbb","rra"],
-- 136_1316
["rrr","rrR","abb","raa","rbb","rra"],
-- 137_1316
["aaa","rrr","rrR","abb","raa","rbb","rra"],
-- 138_1316
["bbb","rrr","rrR","abb","raa","rbb","rra"],
-- 139_1316
["aaa","bbb","rrr","rrR","abb","raa","rbb","rra"],
-- 140_1316
["rrr","abb","arr","raa","rbb","rra"],
-- 141_1316
["aaa","rrr","abb","arr","raa","rbb","rra"],
-- 142_1316
["bbb","rrr","abb","arr","raa","rbb","rra"],
-- 143_1316
["aaa","bbb","rrr","abb","arr","raa","rbb","rra"],
-- 144_1316
["rrr","rrR","abb","arr","raa","rbb","rra"],
-- 145_1316
["aaa","rrr","rrR","abb","arr","raa","rbb","rra"],
-- 146_1316
["bbb","rrr","rrR","abb","arr","raa","rbb","rra"],
-- 147_1316
["aaa","bbb","rrr","rrR","abb","arr","raa","rbb","rra"],
-- 148_1316
["aaa","abb","arr","rar","raa","rbb","rra"],
-- 149_1316
["aaa","bbb","abb","arr","rar","raa","rbb","rra"],
-- 150_1316
["rrr","abb","arr","rar","raa","rbb","rra"],
-- 151_1316
["aaa","rrr","abb","arr","rar","raa","rbb","rra"],
-- 152_1316
["bbb","rrr","abb","arr","rar","raa","rbb","rra"],
-- 153_1316
["aaa","bbb","rrr","abb","arr","rar","raa","rbb","rra"],
-- 154_1316
["rrR","abb","arr","rar","raa","rbb","rra"],
-- 155_1316
["aaa","rrR","abb","arr","rar","raa","rbb","rra"],
-- 156_1316
["bbb","rrR","abb","arr","rar","raa","rbb","rra"],
-- 157_1316
["aaa","bbb","rrR","abb","arr","rar","raa","rbb","rra"],
-- 158_1316
["rrr","rrR","abb","arr","rar","raa","rbb","rra"],
-- 159_1316
["aaa","rrr","rrR","abb","arr","rar","raa","rbb","rra"],
-- 160_1316
["bbb","rrr","rrR","abb","arr","rar","raa","rbb","rra"],
-- 161_1316
["aaa","bbb","rrr","rrR","abb","arr","rar","raa","rbb","rra"],
-- 162_1316
["rrr","abb","baa","arr","rar","brr","rbr","raa","rbb","rra"],
-- 163_1316
["aaa","rrr","abb","baa","arr","rar","brr","rbr","raa","rbb","rra"],
-- 164_1316
["bbb","rrr","abb","baa","arr","rar","brr","rbr","raa","rbb","rra"],
-- 165_1316
["aaa","bbb","rrr","abb","baa","arr","rar","brr","rbr","raa","rbb","rra"],
-- 166_1316
["rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra"],
-- 167_1316
["aaa","rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra"],
-- 168_1316
["bbb","rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra"],
-- 169_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra"],
-- 170_1316
["baa","arr","rar","rra","rrb"],
-- 171_1316
["aaa","baa","arr","rar","rra","rrb"],
-- 172_1316
["rrr","rrR","baa","arr","rar","rra","rrb"],
-- 173_1316
["aaa","rrr","rrR","baa","arr","rar","rra","rrb"],
-- 174_1316
["aaa","abb","arr","rar","brr","rbr","rra","rrb"],
-- 175_1316
["aaa","bbb","abb","arr","rar","brr","rbr","rra","rrb"],
-- 176_1316
["aaa","rrr","abb","arr","rar","brr","rbr","rra","rrb"],
-- 177_1316
["aaa","bbb","rrr","abb","arr","rar","brr","rbr","rra","rrb"],
-- 178_1316
["aaa","rrr","rrR","abb","arr","rar","brr","rbr","rra","rrb"],
-- 179_1316
["aaa","bbb","rrr","rrR","abb","arr","rar","brr","rbr","rra","rrb"],
-- 180_1316
["abb","baa","arr","rar","brr","rbr","rra","rrb"],
-- 181_1316
["aaa","abb","baa","arr","rar","brr","rbr","rra","rrb"],
-- 182_1316
["aaa","bbb","abb","baa","arr","rar","brr","rbr","rra","rrb"],
-- 183_1316
["rrr","abb","baa","arr","rar","brr","rbr","rra","rrb"],
-- 184_1316
["aaa","rrr","abb","baa","arr","rar","brr","rbr","rra","rrb"],
-- 185_1316
["aaa","bbb","rrr","abb","baa","arr","rar","brr","rbr","rra","rrb"],
-- 186_1316
["rrr","rrR","abb","baa","arr","rar","brr","rbr","rra","rrb"],
-- 187_1316
["aaa","rrr","rrR","abb","baa","arr","rar","brr","rbr","rra","rrb"],
-- 188_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","rar","brr","rbr","rra","rrb"],
-- 189_1316
["baa","arr","rar","raa","rra","rrb"],
-- 190_1316
["aaa","baa","arr","rar","raa","rra","rrb"],
-- 191_1316
["rrr","rrR","baa","arr","rar","raa","rra","rrb"],
-- 192_1316
["aaa","rrr","rrR","baa","arr","rar","raa","rra","rrb"],
-- 193_1316
["bbb","baa","arr","rar","brr","rbr","raa","rra","rrb"],
-- 194_1316
["aaa","bbb","baa","arr","rar","brr","rbr","raa","rra","rrb"],
-- 195_1316
["bbb","rrr","baa","arr","rar","brr","rbr","raa","rra","rrb"],
-- 196_1316
["aaa","bbb","rrr","baa","arr","rar","brr","rbr","raa","rra","rrb"],
-- 197_1316
["bbb","rrr","rrR","baa","arr","rar","brr","rbr","raa","rra","rrb"],
-- 198_1316
["aaa","bbb","rrr","rrR","baa","arr","rar","brr","rbr","raa","rra","rrb"],
-- 199_1316
["rrr","abb","baa","arr","rar","raa","rbb","rra","rrb"],
-- 200_1316
["aaa","rrr","abb","baa","arr","rar","raa","rbb","rra","rrb"],
-- 201_1316
["bbb","rrr","abb","baa","arr","rar","raa","rbb","rra","rrb"],
-- 202_1316
["aaa","bbb","rrr","abb","baa","arr","rar","raa","rbb","rra","rrb"],
-- 203_1316
["rrr","rrR","abb","baa","arr","rar","raa","rbb","rra","rrb"],
-- 204_1316
["aaa","rrr","rrR","abb","baa","arr","rar","raa","rbb","rra","rrb"],
-- 205_1316
["bbb","rrr","rrR","abb","baa","arr","rar","raa","rbb","rra","rrb"],
-- 206_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","rar","raa","rbb","rra","rrb"],
-- 207_1316
["rrr","abb","baa","arr","rar","brr","raa","rbb","rra","rrb"],
-- 208_1316
["aaa","rrr","abb","baa","arr","rar","brr","raa","rbb","rra","rrb"],
-- 209_1316
["bbb","rrr","abb","baa","arr","rar","brr","raa","rbb","rra","rrb"],
-- 210_1316
["aaa","bbb","rrr","abb","baa","arr","rar","brr","raa","rbb","rra","rrb"],
-- 211_1316
["rrr","rrR","abb","baa","arr","rar","brr","raa","rbb","rra","rrb"],
-- 212_1316
["aaa","rrr","rrR","abb","baa","arr","rar","brr","raa","rbb","rra","rrb"],
-- 213_1316
["bbb","rrr","rrR","abb","baa","arr","rar","brr","raa","rbb","rra","rrb"],
-- 214_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","rar","brr","raa","rbb","rra","rrb"],
-- 215_1316
["abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb"],
-- 216_1316
["aaa","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb"],
-- 217_1316
["aaa","bbb","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb"],
-- 218_1316
["rrr","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb"],
-- 219_1316
["aaa","rrr","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb"],
-- 220_1316
["aaa","bbb","rrr","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb"],
-- 221_1316
["rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb"],
-- 222_1316
["aaa","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb"],
-- 223_1316
["aaa","bbb","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb"],
-- 224_1316
["rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb"],
-- 225_1316
["aaa","rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb"],
-- 226_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb"],
-- 227_1316
["rrr","raa","rbb","abr"],
-- 228_1316
["aaa","bbb","rrr","abb","baa","raa","rbb","abr"],
-- 229_1316
["aaa","bbb","rrr","baa","arr","brr","raa","rbb","abr"],
-- 230_1316
["aaa","rrr","abb","baa","arr","brr","raa","rbb","abr"],
-- 231_1316
["aaa","bbb","rrr","abb","baa","arr","brr","raa","rbb","abr"],
-- 232_1316
["aaa","bbb","rrr","arr","rbr","raa","rbb","abr"],
-- 233_1316
["aaa","bbb","rrr","abb","baa","arr","rbr","raa","rbb","abr"],
-- 234_1316
["bbb","rrr","abb","arr","rar","rbr","raa","rbb","abr"],
-- 235_1316
["aaa","bbb","rrr","abb","arr","rar","rbr","raa","rbb","abr"],
-- 236_1316
["bbb","rrr","abb","baa","arr","rar","rbr","raa","rbb","abr"],
-- 237_1316
["aaa","bbb","rrr","abb","baa","arr","rar","rbr","raa","rbb","abr"],
-- 238_1316
["rrr","abb","baa","arr","rar","brr","rbr","raa","rbb","abr"],
-- 239_1316
["aaa","rrr","abb","baa","arr","rar","brr","rbr","raa","rbb","abr"],
-- 240_1316
["aaa","bbb","rrr","abb","baa","arr","rar","brr","rbr","raa","rbb","abr"],
-- 241_1316
["aaa","rrr","rrR","abb","rar","brr","raa","rbb","rra","abr"],
-- 242_1316
["aaa","bbb","rrr","rrR","abb","rar","brr","raa","rbb","rra","abr"],
-- 243_1316
["rrr","rrR","abb","baa","rar","brr","raa","rbb","rra","abr"],
-- 244_1316
["aaa","rrr","rrR","abb","baa","rar","brr","raa","rbb","rra","abr"],
-- 245_1316
["bbb","rrr","rrR","abb","baa","rar","brr","raa","rbb","rra","abr"],
-- 246_1316
["aaa","bbb","rrr","rrR","abb","baa","rar","brr","raa","rbb","rra","abr"],
-- 247_1316
["aaa","rrr","rrR","abb","arr","rar","brr","raa","rbb","rra","abr"],
-- 248_1316
["aaa","bbb","rrr","rrR","abb","arr","rar","brr","raa","rbb","rra","abr"],
-- 249_1316
["rrr","rrR","abb","baa","arr","rar","brr","raa","rbb","rra","abr"],
-- 250_1316
["aaa","rrr","rrR","abb","baa","arr","rar","brr","raa","rbb","rra","abr"],
-- 251_1316
["bbb","rrr","rrR","abb","baa","arr","rar","brr","raa","rbb","rra","abr"],
-- 252_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","rar","brr","raa","rbb","rra","abr"],
-- 253_1316
["rrr","rrR","abb","baa","brr","rbr","raa","rbb","rra","abr"],
-- 254_1316
["aaa","rrr","rrR","abb","baa","brr","rbr","raa","rbb","rra","abr"],
-- 255_1316
["bbb","rrr","rrR","abb","baa","brr","rbr","raa","rbb","rra","abr"],
-- 256_1316
["aaa","bbb","rrr","rrR","abb","baa","brr","rbr","raa","rbb","rra","abr"],
-- 257_1316
["rrr","rrR","abb","baa","arr","brr","rbr","raa","rbb","rra","abr"],
-- 258_1316
["aaa","rrr","rrR","abb","baa","arr","brr","rbr","raa","rbb","rra","abr"],
-- 259_1316
["bbb","rrr","rrR","abb","baa","arr","brr","rbr","raa","rbb","rra","abr"],
-- 260_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","brr","rbr","raa","rbb","rra","abr"],
-- 261_1316
["rrr","rrR","abb","rar","brr","rbr","raa","rbb","rra","abr"],
-- 262_1316
["aaa","rrr","rrR","abb","rar","brr","rbr","raa","rbb","rra","abr"],
-- 263_1316
["bbb","rrr","rrR","abb","rar","brr","rbr","raa","rbb","rra","abr"],
-- 264_1316
["aaa","bbb","rrr","rrR","abb","rar","brr","rbr","raa","rbb","rra","abr"],
-- 265_1316
["rrr","rrR","abb","baa","rar","brr","rbr","raa","rbb","rra","abr"],
-- 266_1316
["aaa","rrr","rrR","abb","baa","rar","brr","rbr","raa","rbb","rra","abr"],
-- 267_1316
["bbb","rrr","rrR","abb","baa","rar","brr","rbr","raa","rbb","rra","abr"],
-- 268_1316
["aaa","bbb","rrr","rrR","abb","baa","rar","brr","rbr","raa","rbb","rra","abr"],
-- 269_1316
["rrr","rrR","abb","arr","rar","brr","rbr","raa","rbb","rra","abr"],
-- 270_1316
["aaa","rrr","rrR","abb","arr","rar","brr","rbr","raa","rbb","rra","abr"],
-- 271_1316
["bbb","rrr","rrR","abb","arr","rar","brr","rbr","raa","rbb","rra","abr"],
-- 272_1316
["aaa","bbb","rrr","rrR","abb","arr","rar","brr","rbr","raa","rbb","rra","abr"],
-- 273_1316
["rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","abr"],
-- 274_1316
["aaa","rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","abr"],
-- 275_1316
["bbb","rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","abr"],
-- 276_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","abr"],
-- 277_1316
["rrr","abb","rar","raa","rbb","rra","rrb","abr"],
-- 278_1316
["aaa","rrr","abb","rar","raa","rbb","rra","rrb","abr"],
-- 279_1316
["bbb","rrr","abb","rar","raa","rbb","rra","rrb","abr"],
-- 280_1316
["aaa","bbb","rrr","abb","rar","raa","rbb","rra","rrb","abr"],
-- 281_1316
["rrr","rrR","abb","rar","raa","rbb","rra","rrb","abr"],
-- 282_1316
["aaa","rrr","rrR","abb","rar","raa","rbb","rra","rrb","abr"],
-- 283_1316
["bbb","rrr","rrR","abb","rar","raa","rbb","rra","rrb","abr"],
-- 284_1316
["aaa","bbb","rrr","rrR","abb","rar","raa","rbb","rra","rrb","abr"],
-- 285_1316
["rrr","abb","baa","rar","raa","rbb","rra","rrb","abr"],
-- 286_1316
["aaa","rrr","abb","baa","rar","raa","rbb","rra","rrb","abr"],
-- 287_1316
["bbb","rrr","abb","baa","rar","raa","rbb","rra","rrb","abr"],
-- 288_1316
["aaa","bbb","rrr","abb","baa","rar","raa","rbb","rra","rrb","abr"],
-- 289_1316
["rrr","rrR","abb","baa","rar","raa","rbb","rra","rrb","abr"],
-- 290_1316
["aaa","rrr","rrR","abb","baa","rar","raa","rbb","rra","rrb","abr"],
-- 291_1316
["bbb","rrr","rrR","abb","baa","rar","raa","rbb","rra","rrb","abr"],
-- 292_1316
["aaa","bbb","rrr","rrR","abb","baa","rar","raa","rbb","rra","rrb","abr"],
-- 293_1316
["rrr","abb","arr","rar","raa","rbb","rra","rrb","abr"],
-- 294_1316
["aaa","rrr","abb","arr","rar","raa","rbb","rra","rrb","abr"],
-- 295_1316
["bbb","rrr","abb","arr","rar","raa","rbb","rra","rrb","abr"],
-- 296_1316
["aaa","bbb","rrr","abb","arr","rar","raa","rbb","rra","rrb","abr"],
-- 297_1316
["rrr","rrR","abb","arr","rar","raa","rbb","rra","rrb","abr"],
-- 298_1316
["aaa","rrr","rrR","abb","arr","rar","raa","rbb","rra","rrb","abr"],
-- 299_1316
["bbb","rrr","rrR","abb","arr","rar","raa","rbb","rra","rrb","abr"],
-- 300_1316
["aaa","bbb","rrr","rrR","abb","arr","rar","raa","rbb","rra","rrb","abr"],
-- 301_1316
["rrr","abb","baa","arr","rar","raa","rbb","rra","rrb","abr"],
-- 302_1316
["aaa","rrr","abb","baa","arr","rar","raa","rbb","rra","rrb","abr"],
-- 303_1316
["bbb","rrr","abb","baa","arr","rar","raa","rbb","rra","rrb","abr"],
-- 304_1316
["aaa","bbb","rrr","abb","baa","arr","rar","raa","rbb","rra","rrb","abr"],
-- 305_1316
["rrr","rrR","abb","baa","arr","rar","raa","rbb","rra","rrb","abr"],
-- 306_1316
["aaa","rrr","rrR","abb","baa","arr","rar","raa","rbb","rra","rrb","abr"],
-- 307_1316
["bbb","rrr","rrR","abb","baa","arr","rar","raa","rbb","rra","rrb","abr"],
-- 308_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","rar","raa","rbb","rra","rrb","abr"],
-- 309_1316
["rrr","baa","arr","brr","raa","rbb","rra","rrb","abr"],
-- 310_1316
["aaa","rrr","baa","arr","brr","raa","rbb","rra","rrb","abr"],
-- 311_1316
["bbb","rrr","baa","arr","brr","raa","rbb","rra","rrb","abr"],
-- 312_1316
["aaa","bbb","rrr","baa","arr","brr","raa","rbb","rra","rrb","abr"],
-- 313_1316
["rrr","rrR","baa","arr","brr","raa","rbb","rra","rrb","abr"],
-- 314_1316
["aaa","rrr","rrR","baa","arr","brr","raa","rbb","rra","rrb","abr"],
-- 315_1316
["bbb","rrr","rrR","baa","arr","brr","raa","rbb","rra","rrb","abr"],
-- 316_1316
["aaa","bbb","rrr","rrR","baa","arr","brr","raa","rbb","rra","rrb","abr"],
-- 317_1316
["rrr","abb","baa","arr","brr","raa","rbb","rra","rrb","abr"],
-- 318_1316
["aaa","rrr","abb","baa","arr","brr","raa","rbb","rra","rrb","abr"],
-- 319_1316
["bbb","rrr","abb","baa","arr","brr","raa","rbb","rra","rrb","abr"],
-- 320_1316
["aaa","bbb","rrr","abb","baa","arr","brr","raa","rbb","rra","rrb","abr"],
-- 321_1316
["rrr","rrR","abb","baa","arr","brr","raa","rbb","rra","rrb","abr"],
-- 322_1316
["aaa","rrr","rrR","abb","baa","arr","brr","raa","rbb","rra","rrb","abr"],
-- 323_1316
["bbb","rrr","rrR","abb","baa","arr","brr","raa","rbb","rra","rrb","abr"],
-- 324_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","brr","raa","rbb","rra","rrb","abr"],
-- 325_1316
["rrr","abb","rar","brr","raa","rbb","rra","rrb","abr"],
-- 326_1316
["aaa","rrr","abb","rar","brr","raa","rbb","rra","rrb","abr"],
-- 327_1316
["bbb","rrr","abb","rar","brr","raa","rbb","rra","rrb","abr"],
-- 328_1316
["aaa","bbb","rrr","abb","rar","brr","raa","rbb","rra","rrb","abr"],
-- 329_1316
["rrr","rrR","abb","rar","brr","raa","rbb","rra","rrb","abr"],
-- 330_1316
["aaa","rrr","rrR","abb","rar","brr","raa","rbb","rra","rrb","abr"],
-- 331_1316
["bbb","rrr","rrR","abb","rar","brr","raa","rbb","rra","rrb","abr"],
-- 332_1316
["aaa","bbb","rrr","rrR","abb","rar","brr","raa","rbb","rra","rrb","abr"],
-- 333_1316
["rrr","abb","baa","rar","brr","raa","rbb","rra","rrb","abr"],
-- 334_1316
["aaa","rrr","abb","baa","rar","brr","raa","rbb","rra","rrb","abr"],
-- 335_1316
["aaa","bbb","rrr","abb","baa","rar","brr","raa","rbb","rra","rrb","abr"],
-- 336_1316
["rrr","rrR","abb","baa","rar","brr","raa","rbb","rra","rrb","abr"],
-- 337_1316
["aaa","rrr","rrR","abb","baa","rar","brr","raa","rbb","rra","rrb","abr"],
-- 338_1316
["aaa","bbb","rrr","rrR","abb","baa","rar","brr","raa","rbb","rra","rrb","abr"],
-- 339_1316
["rrr","abb","arr","rar","brr","raa","rbb","rra","rrb","abr"],
-- 340_1316
["aaa","rrr","abb","arr","rar","brr","raa","rbb","rra","rrb","abr"],
-- 341_1316
["bbb","rrr","abb","arr","rar","brr","raa","rbb","rra","rrb","abr"],
-- 342_1316
["aaa","bbb","rrr","abb","arr","rar","brr","raa","rbb","rra","rrb","abr"],
-- 343_1316
["rrr","rrR","abb","arr","rar","brr","raa","rbb","rra","rrb","abr"],
-- 344_1316
["aaa","rrr","rrR","abb","arr","rar","brr","raa","rbb","rra","rrb","abr"],
-- 345_1316
["bbb","rrr","rrR","abb","arr","rar","brr","raa","rbb","rra","rrb","abr"],
-- 346_1316
["aaa","bbb","rrr","rrR","abb","arr","rar","brr","raa","rbb","rra","rrb","abr"],
-- 347_1316
["rrr","baa","arr","rar","brr","raa","rbb","rra","rrb","abr"],
-- 348_1316
["aaa","rrr","baa","arr","rar","brr","raa","rbb","rra","rrb","abr"],
-- 349_1316
["bbb","rrr","baa","arr","rar","brr","raa","rbb","rra","rrb","abr"],
-- 350_1316
["aaa","bbb","rrr","baa","arr","rar","brr","raa","rbb","rra","rrb","abr"],
-- 351_1316
["rrr","rrR","baa","arr","rar","brr","raa","rbb","rra","rrb","abr"],
-- 352_1316
["aaa","rrr","rrR","baa","arr","rar","brr","raa","rbb","rra","rrb","abr"],
-- 353_1316
["bbb","rrr","rrR","baa","arr","rar","brr","raa","rbb","rra","rrb","abr"],
-- 354_1316
["aaa","bbb","rrr","rrR","baa","arr","rar","brr","raa","rbb","rra","rrb","abr"],
-- 355_1316
["rrr","abb","baa","arr","rar","brr","raa","rbb","rra","rrb","abr"],
-- 356_1316
["aaa","rrr","abb","baa","arr","rar","brr","raa","rbb","rra","rrb","abr"],
-- 357_1316
["bbb","rrr","abb","baa","arr","rar","brr","raa","rbb","rra","rrb","abr"],
-- 358_1316
["aaa","bbb","rrr","abb","baa","arr","rar","brr","raa","rbb","rra","rrb","abr"],
-- 359_1316
["rrr","rrR","abb","baa","arr","rar","brr","raa","rbb","rra","rrb","abr"],
-- 360_1316
["aaa","rrr","rrR","abb","baa","arr","rar","brr","raa","rbb","rra","rrb","abr"],
-- 361_1316
["bbb","rrr","rrR","abb","baa","arr","rar","brr","raa","rbb","rra","rrb","abr"],
-- 362_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","rar","brr","raa","rbb","rra","rrb","abr"],
-- 363_1316
["rrr","abb","arr","rar","rbr","raa","rbb","rra","rrb","abr"],
-- 364_1316
["aaa","rrr","abb","arr","rar","rbr","raa","rbb","rra","rrb","abr"],
-- 365_1316
["bbb","rrr","abb","arr","rar","rbr","raa","rbb","rra","rrb","abr"],
-- 366_1316
["aaa","bbb","rrr","abb","arr","rar","rbr","raa","rbb","rra","rrb","abr"],
-- 367_1316
["rrr","rrR","abb","arr","rar","rbr","raa","rbb","rra","rrb","abr"],
-- 368_1316
["aaa","rrr","rrR","abb","arr","rar","rbr","raa","rbb","rra","rrb","abr"],
-- 369_1316
["bbb","rrr","rrR","abb","arr","rar","rbr","raa","rbb","rra","rrb","abr"],
-- 370_1316
["aaa","bbb","rrr","rrR","abb","arr","rar","rbr","raa","rbb","rra","rrb","abr"],
-- 371_1316
["rrr","abb","baa","arr","rar","rbr","raa","rbb","rra","rrb","abr"],
-- 372_1316
["aaa","rrr","abb","baa","arr","rar","rbr","raa","rbb","rra","rrb","abr"],
-- 373_1316
["bbb","rrr","abb","baa","arr","rar","rbr","raa","rbb","rra","rrb","abr"],
-- 374_1316
["aaa","bbb","rrr","abb","baa","arr","rar","rbr","raa","rbb","rra","rrb","abr"],
-- 375_1316
["rrr","rrR","abb","baa","arr","rar","rbr","raa","rbb","rra","rrb","abr"],
-- 376_1316
["aaa","rrr","rrR","abb","baa","arr","rar","rbr","raa","rbb","rra","rrb","abr"],
-- 377_1316
["bbb","rrr","rrR","abb","baa","arr","rar","rbr","raa","rbb","rra","rrb","abr"],
-- 378_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","rar","rbr","raa","rbb","rra","rrb","abr"],
-- 379_1316
["rrr","rrR","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr"],
-- 380_1316
["aaa","rrr","rrR","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr"],
-- 381_1316
["aaa","bbb","rrr","rrR","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr"],
-- 382_1316
["aaa","abb","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr"],
-- 383_1316
["aaa","bbb","abb","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr"],
-- 384_1316
["rrr","abb","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr"],
-- 385_1316
["aaa","rrr","abb","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr"],
-- 386_1316
["bbb","rrr","abb","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr"],
-- 387_1316
["aaa","bbb","rrr","abb","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr"],
-- 388_1316
["rrR","abb","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr"],
-- 389_1316
["aaa","rrR","abb","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr"],
-- 390_1316
["bbb","rrR","abb","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr"],
-- 391_1316
["aaa","bbb","rrR","abb","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr"],
-- 392_1316
["rrr","rrR","abb","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr"],
-- 393_1316
["aaa","rrr","rrR","abb","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr"],
-- 394_1316
["bbb","rrr","rrR","abb","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr"],
-- 395_1316
["aaa","bbb","rrr","rrR","abb","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr"],
-- 396_1316
["abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr"],
-- 397_1316
["aaa","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr"],
-- 398_1316
["aaa","bbb","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr"],
-- 399_1316
["rrr","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr"],
-- 400_1316
["aaa","rrr","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr"],
-- 401_1316
["aaa","bbb","rrr","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr"],
-- 402_1316
["rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr"],
-- 403_1316
["aaa","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr"],
-- 404_1316
["aaa","bbb","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr"],
-- 405_1316
["rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr"],
-- 406_1316
["aaa","rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr"],
-- 407_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr"],
-- 408_1316
["rrr","raa","rbb","abr","bar"],
-- 409_1316
["rrr","rrR","raa","rbb","abr","bar"],
-- 410_1316
["aaa","rrr","abb","raa","rbb","abr","bar"],
-- 411_1316
["aaa","bbb","rrr","abb","raa","rbb","abr","bar"],
-- 412_1316
["aaa","rrr","rrR","abb","raa","rbb","abr","bar"],
-- 413_1316
["aaa","bbb","rrr","rrR","abb","raa","rbb","abr","bar"],
-- 414_1316
["rrr","abb","baa","raa","rbb","abr","bar"],
-- 415_1316
["aaa","rrr","abb","baa","raa","rbb","abr","bar"],
-- 416_1316
["aaa","bbb","rrr","abb","baa","raa","rbb","abr","bar"],
-- 417_1316
["rrr","rrR","abb","baa","raa","rbb","abr","bar"],
-- 418_1316
["aaa","rrr","rrR","abb","baa","raa","rbb","abr","bar"],
-- 419_1316
["aaa","bbb","rrr","rrR","abb","baa","raa","rbb","abr","bar"],
-- 420_1316
["aaa","rrr","abb","arr","brr","raa","rbb","abr","bar"],
-- 421_1316
["aaa","bbb","rrr","abb","arr","brr","raa","rbb","abr","bar"],
-- 422_1316
["rrr","abb","baa","arr","brr","raa","rbb","abr","bar"],
-- 423_1316
["aaa","rrr","abb","baa","arr","brr","raa","rbb","abr","bar"],
-- 424_1316
["aaa","bbb","rrr","abb","baa","arr","brr","raa","rbb","abr","bar"],
-- 425_1316
["rrr","arr","rar","brr","rbr","raa","rbb","abr","bar"],
-- 426_1316
["aaa","rrr","arr","rar","brr","rbr","raa","rbb","abr","bar"],
-- 427_1316
["aaa","bbb","rrr","arr","rar","brr","rbr","raa","rbb","abr","bar"],
-- 428_1316
["rrr","rrR","arr","rar","brr","rbr","raa","rbb","abr","bar"],
-- 429_1316
["aaa","rrr","rrR","arr","rar","brr","rbr","raa","rbb","abr","bar"],
-- 430_1316
["aaa","bbb","rrr","rrR","arr","rar","brr","rbr","raa","rbb","abr","bar"],
-- 431_1316
["rrr","abb","arr","rar","brr","rbr","raa","rbb","abr","bar"],
-- 432_1316
["aaa","rrr","abb","arr","rar","brr","rbr","raa","rbb","abr","bar"],
-- 433_1316
["bbb","rrr","abb","arr","rar","brr","rbr","raa","rbb","abr","bar"],
-- 434_1316
["aaa","bbb","rrr","abb","arr","rar","brr","rbr","raa","rbb","abr","bar"],
-- 435_1316
["rrr","rrR","abb","arr","rar","brr","rbr","raa","rbb","abr","bar"],
-- 436_1316
["aaa","rrr","rrR","abb","arr","rar","brr","rbr","raa","rbb","abr","bar"],
-- 437_1316
["bbb","rrr","rrR","abb","arr","rar","brr","rbr","raa","rbb","abr","bar"],
-- 438_1316
["aaa","bbb","rrr","rrR","abb","arr","rar","brr","rbr","raa","rbb","abr","bar"],
-- 439_1316
["rrr","abb","baa","arr","rar","brr","rbr","raa","rbb","abr","bar"],
-- 440_1316
["aaa","rrr","abb","baa","arr","rar","brr","rbr","raa","rbb","abr","bar"],
-- 441_1316
["aaa","bbb","rrr","abb","baa","arr","rar","brr","rbr","raa","rbb","abr","bar"],
-- 442_1316
["rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","abr","bar"],
-- 443_1316
["aaa","rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","abr","bar"],
-- 444_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","abr","bar"],
-- 445_1316
["aaa","abb","arr","rar","rra","abr","bar"],
-- 446_1316
["aaa","bbb","rrr","abb","arr","rar","brr","rbr","rra","abr","bar"],
-- 447_1316
["aaa","bbb","rrR","abb","arr","rar","brr","rbr","rra","abr","bar"],
-- 448_1316
["aaa","bbb","rrr","rrR","abb","arr","rar","brr","rbr","rra","abr","bar"],
-- 449_1316
["aaa","bbb","rrr","abb","baa","arr","rar","brr","rbr","rra","abr","bar"],
-- 450_1316
["aaa","bbb","rrR","abb","baa","arr","rar","brr","rbr","rra","abr","bar"],
-- 451_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","rar","brr","rbr","rra","abr","bar"],
-- 452_1316
["aaa","abb","baa","arr","rar","raa","rra","abr","bar"],
-- 453_1316
["aaa","bbb","abb","baa","arr","rar","raa","rra","abr","bar"],
-- 454_1316
["aaa","rrr","abb","baa","arr","rar","raa","rra","abr","bar"],
-- 455_1316
["aaa","bbb","rrr","abb","baa","arr","rar","raa","rra","abr","bar"],
-- 456_1316
["aaa","rrR","abb","baa","arr","rar","raa","rra","abr","bar"],
-- 457_1316
["aaa","bbb","rrR","abb","baa","arr","rar","raa","rra","abr","bar"],
-- 458_1316
["aaa","rrr","rrR","abb","baa","arr","rar","raa","rra","abr","bar"],
-- 459_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","rar","raa","rra","abr","bar"],
-- 460_1316
["aaa","abb","baa","arr","rar","brr","raa","rra","abr","bar"],
-- 461_1316
["aaa","bbb","abb","baa","arr","rar","brr","raa","rra","abr","bar"],
-- 462_1316
["aaa","rrr","abb","baa","arr","rar","brr","raa","rra","abr","bar"],
-- 463_1316
["aaa","bbb","rrr","abb","baa","arr","rar","brr","raa","rra","abr","bar"],
-- 464_1316
["aaa","rrR","abb","baa","arr","rar","brr","raa","rra","abr","bar"],
-- 465_1316
["aaa","bbb","rrR","abb","baa","arr","rar","brr","raa","rra","abr","bar"],
-- 466_1316
["aaa","rrr","rrR","abb","baa","arr","rar","brr","raa","rra","abr","bar"],
-- 467_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","rar","brr","raa","rra","abr","bar"],
-- 468_1316
["rrr","abb","brr","rbr","raa","rra","abr","bar"],
-- 469_1316
["aaa","rrr","abb","brr","rbr","raa","rra","abr","bar"],
-- 470_1316
["bbb","rrr","abb","brr","rbr","raa","rra","abr","bar"],
-- 471_1316
["aaa","bbb","rrr","abb","brr","rbr","raa","rra","abr","bar"],
-- 472_1316
["rrr","rrR","abb","brr","rbr","raa","rra","abr","bar"],
-- 473_1316
["aaa","rrr","rrR","abb","brr","rbr","raa","rra","abr","bar"],
-- 474_1316
["bbb","rrr","rrR","abb","brr","rbr","raa","rra","abr","bar"],
-- 475_1316
["aaa","bbb","rrr","rrR","abb","brr","rbr","raa","rra","abr","bar"],
-- 476_1316
["rrr","abb","baa","brr","rbr","raa","rra","abr","bar"],
-- 477_1316
["aaa","rrr","abb","baa","brr","rbr","raa","rra","abr","bar"],
-- 478_1316
["bbb","rrr","abb","baa","brr","rbr","raa","rra","abr","bar"],
-- 479_1316
["aaa","bbb","rrr","abb","baa","brr","rbr","raa","rra","abr","bar"],
-- 480_1316
["rrr","rrR","abb","baa","brr","rbr","raa","rra","abr","bar"],
-- 481_1316
["aaa","rrr","rrR","abb","baa","brr","rbr","raa","rra","abr","bar"],
-- 482_1316
["bbb","rrr","rrR","abb","baa","brr","rbr","raa","rra","abr","bar"],
-- 483_1316
["aaa","bbb","rrr","rrR","abb","baa","brr","rbr","raa","rra","abr","bar"],
-- 484_1316
["rrr","abb","arr","brr","rbr","raa","rra","abr","bar"],
-- 485_1316
["aaa","rrr","abb","arr","brr","rbr","raa","rra","abr","bar"],
-- 486_1316
["bbb","rrr","abb","arr","brr","rbr","raa","rra","abr","bar"],
-- 487_1316
["aaa","bbb","rrr","abb","arr","brr","rbr","raa","rra","abr","bar"],
-- 488_1316
["rrr","rrR","abb","arr","brr","rbr","raa","rra","abr","bar"],
-- 489_1316
["aaa","rrr","rrR","abb","arr","brr","rbr","raa","rra","abr","bar"],
-- 490_1316
["bbb","rrr","rrR","abb","arr","brr","rbr","raa","rra","abr","bar"],
-- 491_1316
["aaa","bbb","rrr","rrR","abb","arr","brr","rbr","raa","rra","abr","bar"],
-- 492_1316
["rrr","abb","baa","arr","brr","rbr","raa","rra","abr","bar"],
-- 493_1316
["aaa","rrr","abb","baa","arr","brr","rbr","raa","rra","abr","bar"],
-- 494_1316
["bbb","rrr","abb","baa","arr","brr","rbr","raa","rra","abr","bar"],
-- 495_1316
["aaa","bbb","rrr","abb","baa","arr","brr","rbr","raa","rra","abr","bar"],
-- 496_1316
["rrr","rrR","abb","baa","arr","brr","rbr","raa","rra","abr","bar"],
-- 497_1316
["aaa","rrr","rrR","abb","baa","arr","brr","rbr","raa","rra","abr","bar"],
-- 498_1316
["bbb","rrr","rrR","abb","baa","arr","brr","rbr","raa","rra","abr","bar"],
-- 499_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","brr","rbr","raa","rra","abr","bar"],
-- 500_1316
["rrr","abb","arr","rar","brr","rbr","raa","rra","abr","bar"],
-- 501_1316
["aaa","rrr","abb","arr","rar","brr","rbr","raa","rra","abr","bar"],
-- 502_1316
["bbb","rrr","abb","arr","rar","brr","rbr","raa","rra","abr","bar"],
-- 503_1316
["aaa","bbb","rrr","abb","arr","rar","brr","rbr","raa","rra","abr","bar"],
-- 504_1316
["rrR","abb","arr","rar","brr","rbr","raa","rra","abr","bar"],
-- 505_1316
["aaa","rrR","abb","arr","rar","brr","rbr","raa","rra","abr","bar"],
-- 506_1316
["bbb","rrR","abb","arr","rar","brr","rbr","raa","rra","abr","bar"],
-- 507_1316
["aaa","bbb","rrR","abb","arr","rar","brr","rbr","raa","rra","abr","bar"],
-- 508_1316
["rrr","rrR","abb","arr","rar","brr","rbr","raa","rra","abr","bar"],
-- 509_1316
["aaa","rrr","rrR","abb","arr","rar","brr","rbr","raa","rra","abr","bar"],
-- 510_1316
["bbb","rrr","rrR","abb","arr","rar","brr","rbr","raa","rra","abr","bar"],
-- 511_1316
["aaa","bbb","rrr","rrR","abb","arr","rar","brr","rbr","raa","rra","abr","bar"],
-- 512_1316
["aaa","abb","baa","arr","rar","brr","rbr","raa","rra","abr","bar"],
-- 513_1316
["aaa","bbb","abb","baa","arr","rar","brr","rbr","raa","rra","abr","bar"],
-- 514_1316
["rrr","abb","baa","arr","rar","brr","rbr","raa","rra","abr","bar"],
-- 515_1316
["aaa","rrr","abb","baa","arr","rar","brr","rbr","raa","rra","abr","bar"],
-- 516_1316
["bbb","rrr","abb","baa","arr","rar","brr","rbr","raa","rra","abr","bar"],
-- 517_1316
["aaa","bbb","rrr","abb","baa","arr","rar","brr","rbr","raa","rra","abr","bar"],
-- 518_1316
["rrR","abb","baa","arr","rar","brr","rbr","raa","rra","abr","bar"],
-- 519_1316
["aaa","rrR","abb","baa","arr","rar","brr","rbr","raa","rra","abr","bar"],
-- 520_1316
["bbb","rrR","abb","baa","arr","rar","brr","rbr","raa","rra","abr","bar"],
-- 521_1316
["aaa","bbb","rrR","abb","baa","arr","rar","brr","rbr","raa","rra","abr","bar"],
-- 522_1316
["rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rra","abr","bar"],
-- 523_1316
["aaa","rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rra","abr","bar"],
-- 524_1316
["bbb","rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rra","abr","bar"],
-- 525_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rra","abr","bar"],
-- 526_1316
["aaa","rrr","abb","arr","rar","rbb","rra","abr","bar"],
-- 527_1316
["aaa","bbb","rrr","abb","arr","rar","rbb","rra","abr","bar"],
-- 528_1316
["aaa","rrr","rrR","abb","arr","rar","rbb","rra","abr","bar"],
-- 529_1316
["aaa","bbb","rrr","rrR","abb","arr","rar","rbb","rra","abr","bar"],
-- 530_1316
["aaa","rrr","baa","arr","rar","rbb","rra","abr","bar"],
-- 531_1316
["aaa","bbb","rrr","baa","arr","rar","rbb","rra","abr","bar"],
-- 532_1316
["aaa","rrr","rrR","baa","arr","rar","rbb","rra","abr","bar"],
-- 533_1316
["aaa","bbb","rrr","rrR","baa","arr","rar","rbb","rra","abr","bar"],
-- 534_1316
["aaa","abb","baa","arr","rar","rbb","rra","abr","bar"],
-- 535_1316
["aaa","bbb","abb","baa","arr","rar","rbb","rra","abr","bar"],
-- 536_1316
["aaa","rrr","abb","baa","arr","rar","rbb","rra","abr","bar"],
-- 537_1316
["aaa","bbb","rrr","abb","baa","arr","rar","rbb","rra","abr","bar"],
-- 538_1316
["aaa","rrr","rrR","abb","baa","arr","rar","rbb","rra","abr","bar"],
-- 539_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","rar","rbb","rra","abr","bar"],
-- 540_1316
["aaa","rrr","rrR","abb","rar","brr","rbb","rra","abr","bar"],
-- 541_1316
["aaa","bbb","rrr","rrR","abb","rar","brr","rbb","rra","abr","bar"],
-- 542_1316
["aaa","bbb","rrr","rrR","baa","rar","brr","rbb","rra","abr","bar"],
-- 543_1316
["aaa","rrr","rrR","abb","baa","rar","brr","rbb","rra","abr","bar"],
-- 544_1316
["aaa","bbb","rrr","rrR","abb","baa","rar","brr","rbb","rra","abr","bar"],
-- 545_1316
["aaa","rrr","abb","arr","rar","brr","rbb","rra","abr","bar"],
-- 546_1316
["aaa","bbb","rrr","abb","arr","rar","brr","rbb","rra","abr","bar"],
-- 547_1316
["aaa","rrr","rrR","abb","arr","rar","brr","rbb","rra","abr","bar"],
-- 548_1316
["aaa","bbb","rrr","rrR","abb","arr","rar","brr","rbb","rra","abr","bar"],
-- 549_1316
["aaa","bbb","rrr","baa","arr","rar","brr","rbb","rra","abr","bar"],
-- 550_1316
["aaa","bbb","rrr","rrR","baa","arr","rar","brr","rbb","rra","abr","bar"],
-- 551_1316
["aaa","rrr","abb","baa","arr","rar","brr","rbb","rra","abr","bar"],
-- 552_1316
["aaa","bbb","rrr","abb","baa","arr","rar","brr","rbb","rra","abr","bar"],
-- 553_1316
["aaa","rrr","rrR","abb","baa","arr","rar","brr","rbb","rra","abr","bar"],
-- 554_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","rar","brr","rbb","rra","abr","bar"],
-- 555_1316
["aaa","rrr","rrR","brr","rbr","rbb","rra","abr","bar"],
-- 556_1316
["aaa","bbb","rrr","rrR","brr","rbr","rbb","rra","abr","bar"],
-- 557_1316
["aaa","rrR","abb","brr","rbr","rbb","rra","abr","bar"],
-- 558_1316
["aaa","bbb","rrR","abb","brr","rbr","rbb","rra","abr","bar"],
-- 559_1316
["aaa","rrr","rrR","abb","brr","rbr","rbb","rra","abr","bar"],
-- 560_1316
["aaa","bbb","rrr","rrR","abb","brr","rbr","rbb","rra","abr","bar"],
-- 561_1316
["aaa","rrr","rrR","baa","brr","rbr","rbb","rra","abr","bar"],
-- 562_1316
["aaa","bbb","rrr","rrR","baa","brr","rbr","rbb","rra","abr","bar"],
-- 563_1316
["aaa","rrR","abb","baa","brr","rbr","rbb","rra","abr","bar"],
-- 564_1316
["aaa","bbb","rrR","abb","baa","brr","rbr","rbb","rra","abr","bar"],
-- 565_1316
["aaa","rrr","rrR","abb","baa","brr","rbr","rbb","rra","abr","bar"],
-- 566_1316
["aaa","bbb","rrr","rrR","abb","baa","brr","rbr","rbb","rra","abr","bar"],
-- 567_1316
["aaa","rrr","rrR","arr","brr","rbr","rbb","rra","abr","bar"],
-- 568_1316
["aaa","bbb","rrr","rrR","arr","brr","rbr","rbb","rra","abr","bar"],
-- 569_1316
["aaa","rrr","rrR","abb","arr","brr","rbr","rbb","rra","abr","bar"],
-- 570_1316
["aaa","bbb","rrr","rrR","abb","arr","brr","rbr","rbb","rra","abr","bar"],
-- 571_1316
["aaa","rrr","rrR","baa","arr","brr","rbr","rbb","rra","abr","bar"],
-- 572_1316
["aaa","bbb","rrr","rrR","baa","arr","brr","rbr","rbb","rra","abr","bar"],
-- 573_1316
["aaa","rrr","rrR","abb","baa","arr","brr","rbr","rbb","rra","abr","bar"],
-- 574_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","brr","rbr","rbb","rra","abr","bar"],
-- 575_1316
["aaa","rrr","arr","rar","brr","rbr","rbb","rra","abr","bar"],
-- 576_1316
["aaa","bbb","rrr","arr","rar","brr","rbr","rbb","rra","abr","bar"],
-- 577_1316
["aaa","rrr","rrR","arr","rar","brr","rbr","rbb","rra","abr","bar"],
-- 578_1316
["aaa","bbb","rrr","rrR","arr","rar","brr","rbr","rbb","rra","abr","bar"],
-- 579_1316
["aaa","rrr","abb","arr","rar","brr","rbr","rbb","rra","abr","bar"],
-- 580_1316
["aaa","bbb","rrr","abb","arr","rar","brr","rbr","rbb","rra","abr","bar"],
-- 581_1316
["aaa","rrR","abb","arr","rar","brr","rbr","rbb","rra","abr","bar"],
-- 582_1316
["aaa","bbb","rrR","abb","arr","rar","brr","rbr","rbb","rra","abr","bar"],
-- 583_1316
["aaa","rrr","rrR","abb","arr","rar","brr","rbr","rbb","rra","abr","bar"],
-- 584_1316
["aaa","bbb","rrr","rrR","abb","arr","rar","brr","rbr","rbb","rra","abr","bar"],
-- 585_1316
["aaa","rrr","baa","arr","rar","brr","rbr","rbb","rra","abr","bar"],
-- 586_1316
["aaa","bbb","rrr","baa","arr","rar","brr","rbr","rbb","rra","abr","bar"],
-- 587_1316
["aaa","rrR","baa","arr","rar","brr","rbr","rbb","rra","abr","bar"],
-- 588_1316
["aaa","bbb","rrR","baa","arr","rar","brr","rbr","rbb","rra","abr","bar"],
-- 589_1316
["aaa","rrr","rrR","baa","arr","rar","brr","rbr","rbb","rra","abr","bar"],
-- 590_1316
["aaa","bbb","rrr","rrR","baa","arr","rar","brr","rbr","rbb","rra","abr","bar"],
-- 591_1316
["aaa","rrr","abb","baa","arr","rar","brr","rbr","rbb","rra","abr","bar"],
-- 592_1316
["aaa","bbb","rrr","abb","baa","arr","rar","brr","rbr","rbb","rra","abr","bar"],
-- 593_1316
["aaa","rrR","abb","baa","arr","rar","brr","rbr","rbb","rra","abr","bar"],
-- 594_1316
["aaa","bbb","rrR","abb","baa","arr","rar","brr","rbr","rbb","rra","abr","bar"],
-- 595_1316
["aaa","rrr","rrR","abb","baa","arr","rar","brr","rbr","rbb","rra","abr","bar"],
-- 596_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","rar","brr","rbr","rbb","rra","abr","bar"],
-- 597_1316
["aaa","rrr","abb","arr","rar","raa","rbb","rra","abr","bar"],
-- 598_1316
["aaa","bbb","rrr","abb","arr","rar","raa","rbb","rra","abr","bar"],
-- 599_1316
["aaa","rrr","rrR","abb","arr","rar","raa","rbb","rra","abr","bar"],
-- 600_1316
["aaa","bbb","rrr","rrR","abb","arr","rar","raa","rbb","rra","abr","bar"],
-- 601_1316
["rrr","baa","arr","rar","raa","rbb","rra","abr","bar"],
-- 602_1316
["aaa","rrr","baa","arr","rar","raa","rbb","rra","abr","bar"],
-- 603_1316
["bbb","rrr","baa","arr","rar","raa","rbb","rra","abr","bar"],
-- 604_1316
["aaa","bbb","rrr","baa","arr","rar","raa","rbb","rra","abr","bar"],
-- 605_1316
["rrR","baa","arr","rar","raa","rbb","rra","abr","bar"],
-- 606_1316
["aaa","rrR","baa","arr","rar","raa","rbb","rra","abr","bar"],
-- 607_1316
["bbb","rrR","baa","arr","rar","raa","rbb","rra","abr","bar"],
-- 608_1316
["aaa","bbb","rrR","baa","arr","rar","raa","rbb","rra","abr","bar"],
-- 609_1316
["rrr","rrR","baa","arr","rar","raa","rbb","rra","abr","bar"],
-- 610_1316
["aaa","rrr","rrR","baa","arr","rar","raa","rbb","rra","abr","bar"],
-- 611_1316
["bbb","rrr","rrR","baa","arr","rar","raa","rbb","rra","abr","bar"],
-- 612_1316
["aaa","bbb","rrr","rrR","baa","arr","rar","raa","rbb","rra","abr","bar"],
-- 613_1316
["aaa","abb","baa","arr","rar","raa","rbb","rra","abr","bar"],
-- 614_1316
["aaa","bbb","abb","baa","arr","rar","raa","rbb","rra","abr","bar"],
-- 615_1316
["rrr","abb","baa","arr","rar","raa","rbb","rra","abr","bar"],
-- 616_1316
["aaa","rrr","abb","baa","arr","rar","raa","rbb","rra","abr","bar"],
-- 617_1316
["bbb","rrr","abb","baa","arr","rar","raa","rbb","rra","abr","bar"],
-- 618_1316
["aaa","bbb","rrr","abb","baa","arr","rar","raa","rbb","rra","abr","bar"],
-- 619_1316
["rrR","abb","baa","arr","rar","raa","rbb","rra","abr","bar"],
-- 620_1316
["aaa","rrR","abb","baa","arr","rar","raa","rbb","rra","abr","bar"],
-- 621_1316
["bbb","rrR","abb","baa","arr","rar","raa","rbb","rra","abr","bar"],
-- 622_1316
["aaa","bbb","rrR","abb","baa","arr","rar","raa","rbb","rra","abr","bar"],
-- 623_1316
["rrr","rrR","abb","baa","arr","rar","raa","rbb","rra","abr","bar"],
-- 624_1316
["aaa","rrr","rrR","abb","baa","arr","rar","raa","rbb","rra","abr","bar"],
-- 625_1316
["bbb","rrr","rrR","abb","baa","arr","rar","raa","rbb","rra","abr","bar"],
-- 626_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","rar","raa","rbb","rra","abr","bar"],
-- 627_1316
["aaa","rrr","abb","rar","brr","raa","rbb","rra","abr","bar"],
-- 628_1316
["aaa","bbb","rrr","abb","rar","brr","raa","rbb","rra","abr","bar"],
-- 629_1316
["aaa","rrr","rrR","abb","rar","brr","raa","rbb","rra","abr","bar"],
-- 630_1316
["aaa","bbb","rrr","rrR","abb","rar","brr","raa","rbb","rra","abr","bar"],
-- 631_1316
["bbb","rrr","baa","rar","brr","raa","rbb","rra","abr","bar"],
-- 632_1316
["aaa","bbb","rrr","baa","rar","brr","raa","rbb","rra","abr","bar"],
-- 633_1316
["bbb","rrr","rrR","baa","rar","brr","raa","rbb","rra","abr","bar"],
-- 634_1316
["aaa","bbb","rrr","rrR","baa","rar","brr","raa","rbb","rra","abr","bar"],
-- 635_1316
["rrr","abb","baa","rar","brr","raa","rbb","rra","abr","bar"],
-- 636_1316
["aaa","rrr","abb","baa","rar","brr","raa","rbb","rra","abr","bar"],
-- 637_1316
["bbb","rrr","abb","baa","rar","brr","raa","rbb","rra","abr","bar"],
-- 638_1316
["aaa","bbb","rrr","abb","baa","rar","brr","raa","rbb","rra","abr","bar"],
-- 639_1316
["rrr","rrR","abb","baa","rar","brr","raa","rbb","rra","abr","bar"],
-- 640_1316
["aaa","rrr","rrR","abb","baa","rar","brr","raa","rbb","rra","abr","bar"],
-- 641_1316
["bbb","rrr","rrR","abb","baa","rar","brr","raa","rbb","rra","abr","bar"],
-- 642_1316
["aaa","bbb","rrr","rrR","abb","baa","rar","brr","raa","rbb","rra","abr","bar"],
-- 643_1316
["aaa","rrr","abb","arr","rar","brr","raa","rbb","rra","abr","bar"],
-- 644_1316
["aaa","bbb","rrr","abb","arr","rar","brr","raa","rbb","rra","abr","bar"],
-- 645_1316
["aaa","rrr","rrR","abb","arr","rar","brr","raa","rbb","rra","abr","bar"],
-- 646_1316
["aaa","bbb","rrr","rrR","abb","arr","rar","brr","raa","rbb","rra","abr","bar"],
-- 647_1316
["bbb","rrr","baa","arr","rar","brr","raa","rbb","rra","abr","bar"],
-- 648_1316
["aaa","bbb","rrr","baa","arr","rar","brr","raa","rbb","rra","abr","bar"],
-- 649_1316
["bbb","rrR","baa","arr","rar","brr","raa","rbb","rra","abr","bar"],
-- 650_1316
["aaa","bbb","rrR","baa","arr","rar","brr","raa","rbb","rra","abr","bar"],
-- 651_1316
["bbb","rrr","rrR","baa","arr","rar","brr","raa","rbb","rra","abr","bar"],
-- 652_1316
["aaa","bbb","rrr","rrR","baa","arr","rar","brr","raa","rbb","rra","abr","bar"],
-- 653_1316
["aaa","abb","baa","arr","rar","brr","raa","rbb","rra","abr","bar"],
-- 654_1316
["aaa","bbb","abb","baa","arr","rar","brr","raa","rbb","rra","abr","bar"],
-- 655_1316
["rrr","abb","baa","arr","rar","brr","raa","rbb","rra","abr","bar"],
-- 656_1316
["aaa","rrr","abb","baa","arr","rar","brr","raa","rbb","rra","abr","bar"],
-- 657_1316
["bbb","rrr","abb","baa","arr","rar","brr","raa","rbb","rra","abr","bar"],
-- 658_1316
["aaa","bbb","rrr","abb","baa","arr","rar","brr","raa","rbb","rra","abr","bar"],
-- 659_1316
["rrR","abb","baa","arr","rar","brr","raa","rbb","rra","abr","bar"],
-- 660_1316
["aaa","rrR","abb","baa","arr","rar","brr","raa","rbb","rra","abr","bar"],
-- 661_1316
["bbb","rrR","abb","baa","arr","rar","brr","raa","rbb","rra","abr","bar"],
-- 662_1316
["aaa","bbb","rrR","abb","baa","arr","rar","brr","raa","rbb","rra","abr","bar"],
-- 663_1316
["rrr","rrR","abb","baa","arr","rar","brr","raa","rbb","rra","abr","bar"],
-- 664_1316
["aaa","rrr","rrR","abb","baa","arr","rar","brr","raa","rbb","rra","abr","bar"],
-- 665_1316
["bbb","rrr","rrR","abb","baa","arr","rar","brr","raa","rbb","rra","abr","bar"],
-- 666_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","rar","brr","raa","rbb","rra","abr","bar"],
-- 667_1316
["rrr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 668_1316
["aaa","rrr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 669_1316
["bbb","rrr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 670_1316
["aaa","bbb","rrr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 671_1316
["rrr","rrR","brr","rbr","raa","rbb","rra","abr","bar"],
-- 672_1316
["aaa","rrr","rrR","brr","rbr","raa","rbb","rra","abr","bar"],
-- 673_1316
["bbb","rrr","rrR","brr","rbr","raa","rbb","rra","abr","bar"],
-- 674_1316
["aaa","bbb","rrr","rrR","brr","rbr","raa","rbb","rra","abr","bar"],
-- 675_1316
["rrr","abb","brr","rbr","raa","rbb","rra","abr","bar"],
-- 676_1316
["aaa","rrr","abb","brr","rbr","raa","rbb","rra","abr","bar"],
-- 677_1316
["bbb","rrr","abb","brr","rbr","raa","rbb","rra","abr","bar"],
-- 678_1316
["aaa","bbb","rrr","abb","brr","rbr","raa","rbb","rra","abr","bar"],
-- 679_1316
["rrR","abb","brr","rbr","raa","rbb","rra","abr","bar"],
-- 680_1316
["aaa","rrR","abb","brr","rbr","raa","rbb","rra","abr","bar"],
-- 681_1316
["bbb","rrR","abb","brr","rbr","raa","rbb","rra","abr","bar"],
-- 682_1316
["aaa","bbb","rrR","abb","brr","rbr","raa","rbb","rra","abr","bar"],
-- 683_1316
["rrr","rrR","abb","brr","rbr","raa","rbb","rra","abr","bar"],
-- 684_1316
["aaa","rrr","rrR","abb","brr","rbr","raa","rbb","rra","abr","bar"],
-- 685_1316
["bbb","rrr","rrR","abb","brr","rbr","raa","rbb","rra","abr","bar"],
-- 686_1316
["aaa","bbb","rrr","rrR","abb","brr","rbr","raa","rbb","rra","abr","bar"],
-- 687_1316
["rrr","baa","brr","rbr","raa","rbb","rra","abr","bar"],
-- 688_1316
["aaa","rrr","baa","brr","rbr","raa","rbb","rra","abr","bar"],
-- 689_1316
["bbb","rrr","baa","brr","rbr","raa","rbb","rra","abr","bar"],
-- 690_1316
["aaa","bbb","rrr","baa","brr","rbr","raa","rbb","rra","abr","bar"],
-- 691_1316
["rrr","rrR","baa","brr","rbr","raa","rbb","rra","abr","bar"],
-- 692_1316
["aaa","rrr","rrR","baa","brr","rbr","raa","rbb","rra","abr","bar"],
-- 693_1316
["bbb","rrr","rrR","baa","brr","rbr","raa","rbb","rra","abr","bar"],
-- 694_1316
["aaa","bbb","rrr","rrR","baa","brr","rbr","raa","rbb","rra","abr","bar"],
-- 695_1316
["aaa","abb","baa","brr","rbr","raa","rbb","rra","abr","bar"],
-- 696_1316
["aaa","bbb","abb","baa","brr","rbr","raa","rbb","rra","abr","bar"],
-- 697_1316
["rrr","abb","baa","brr","rbr","raa","rbb","rra","abr","bar"],
-- 698_1316
["aaa","rrr","abb","baa","brr","rbr","raa","rbb","rra","abr","bar"],
-- 699_1316
["bbb","rrr","abb","baa","brr","rbr","raa","rbb","rra","abr","bar"],
-- 700_1316
["aaa","bbb","rrr","abb","baa","brr","rbr","raa","rbb","rra","abr","bar"],
-- 701_1316
["rrR","abb","baa","brr","rbr","raa","rbb","rra","abr","bar"],
-- 702_1316
["aaa","rrR","abb","baa","brr","rbr","raa","rbb","rra","abr","bar"],
-- 703_1316
["bbb","rrR","abb","baa","brr","rbr","raa","rbb","rra","abr","bar"],
-- 704_1316
["aaa","bbb","rrR","abb","baa","brr","rbr","raa","rbb","rra","abr","bar"],
-- 705_1316
["rrr","rrR","abb","baa","brr","rbr","raa","rbb","rra","abr","bar"],
-- 706_1316
["aaa","rrr","rrR","abb","baa","brr","rbr","raa","rbb","rra","abr","bar"],
-- 707_1316
["bbb","rrr","rrR","abb","baa","brr","rbr","raa","rbb","rra","abr","bar"],
-- 708_1316
["aaa","bbb","rrr","rrR","abb","baa","brr","rbr","raa","rbb","rra","abr","bar"],
-- 709_1316
["rrr","arr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 710_1316
["aaa","rrr","arr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 711_1316
["bbb","rrr","arr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 712_1316
["aaa","bbb","rrr","arr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 713_1316
["rrr","rrR","arr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 714_1316
["aaa","rrr","rrR","arr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 715_1316
["bbb","rrr","rrR","arr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 716_1316
["aaa","bbb","rrr","rrR","arr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 717_1316
["rrr","abb","arr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 718_1316
["aaa","rrr","abb","arr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 719_1316
["bbb","rrr","abb","arr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 720_1316
["aaa","bbb","rrr","abb","arr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 721_1316
["rrr","rrR","abb","arr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 722_1316
["aaa","rrr","rrR","abb","arr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 723_1316
["bbb","rrr","rrR","abb","arr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 724_1316
["aaa","bbb","rrr","rrR","abb","arr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 725_1316
["rrr","baa","arr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 726_1316
["aaa","rrr","baa","arr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 727_1316
["bbb","rrr","baa","arr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 728_1316
["aaa","bbb","rrr","baa","arr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 729_1316
["rrr","rrR","baa","arr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 730_1316
["aaa","rrr","rrR","baa","arr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 731_1316
["bbb","rrr","rrR","baa","arr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 732_1316
["aaa","bbb","rrr","rrR","baa","arr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 733_1316
["rrr","abb","baa","arr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 734_1316
["aaa","rrr","abb","baa","arr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 735_1316
["bbb","rrr","abb","baa","arr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 736_1316
["aaa","bbb","rrr","abb","baa","arr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 737_1316
["rrr","rrR","abb","baa","arr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 738_1316
["aaa","rrr","rrR","abb","baa","arr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 739_1316
["bbb","rrr","rrR","abb","baa","arr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 740_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","brr","rbr","raa","rbb","rra","abr","bar"],
-- 741_1316
["rrr","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 742_1316
["aaa","rrr","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 743_1316
["bbb","rrr","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 744_1316
["aaa","bbb","rrr","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 745_1316
["rrr","rrR","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 746_1316
["aaa","rrr","rrR","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 747_1316
["bbb","rrr","rrR","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 748_1316
["aaa","bbb","rrr","rrR","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 749_1316
["rrr","abb","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 750_1316
["aaa","rrr","abb","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 751_1316
["bbb","rrr","abb","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 752_1316
["aaa","bbb","rrr","abb","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 753_1316
["rrR","abb","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 754_1316
["aaa","rrR","abb","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 755_1316
["bbb","rrR","abb","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 756_1316
["aaa","bbb","rrR","abb","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 757_1316
["rrr","rrR","abb","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 758_1316
["aaa","rrr","rrR","abb","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 759_1316
["bbb","rrr","rrR","abb","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 760_1316
["aaa","bbb","rrr","rrR","abb","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 761_1316
["rrr","baa","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 762_1316
["aaa","rrr","baa","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 763_1316
["bbb","rrr","baa","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 764_1316
["aaa","bbb","rrr","baa","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 765_1316
["rrR","baa","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 766_1316
["aaa","rrR","baa","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 767_1316
["bbb","rrR","baa","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 768_1316
["aaa","bbb","rrR","baa","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 769_1316
["rrr","rrR","baa","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 770_1316
["aaa","rrr","rrR","baa","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 771_1316
["bbb","rrr","rrR","baa","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 772_1316
["aaa","bbb","rrr","rrR","baa","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 773_1316
["aaa","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 774_1316
["aaa","bbb","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 775_1316
["rrr","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 776_1316
["aaa","rrr","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 777_1316
["bbb","rrr","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 778_1316
["aaa","bbb","rrr","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 779_1316
["rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 780_1316
["aaa","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 781_1316
["bbb","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 782_1316
["aaa","bbb","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 783_1316
["rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 784_1316
["aaa","rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 785_1316
["bbb","rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 786_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","abr","bar"],
-- 787_1316
["aaa","bbb","rrr","arr","rar","rra","rrb","abr","bar"],
-- 788_1316
["aaa","bbb","rrr","rrR","arr","rar","rra","rrb","abr","bar"],
-- 789_1316
["aaa","bbb","rrr","abb","arr","rar","rra","rrb","abr","bar"],
-- 790_1316
["aaa","bbb","rrr","rrR","abb","arr","rar","rra","rrb","abr","bar"],
-- 791_1316
["aaa","bbb","rrr","baa","arr","rar","rra","rrb","abr","bar"],
-- 792_1316
["aaa","bbb","rrr","rrR","baa","arr","rar","rra","rrb","abr","bar"],
-- 793_1316
["aaa","bbb","rrr","abb","baa","arr","rar","rra","rrb","abr","bar"],
-- 794_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","rar","rra","rrb","abr","bar"],
-- 795_1316
["aaa","bbb","rrr","arr","rar","brr","rra","rrb","abr","bar"],
-- 796_1316
["aaa","bbb","rrr","rrR","arr","rar","brr","rra","rrb","abr","bar"],
-- 797_1316
["aaa","bbb","rrr","abb","arr","rar","brr","rra","rrb","abr","bar"],
-- 798_1316
["aaa","bbb","rrr","rrR","abb","arr","rar","brr","rra","rrb","abr","bar"],
-- 799_1316
["aaa","bbb","rrr","baa","arr","rar","brr","rra","rrb","abr","bar"],
-- 800_1316
["aaa","bbb","rrr","rrR","baa","arr","rar","brr","rra","rrb","abr","bar"],
-- 801_1316
["aaa","bbb","rrr","abb","baa","arr","rar","brr","rra","rrb","abr","bar"],
-- 802_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","rar","brr","rra","rrb","abr","bar"],
-- 803_1316
["aaa","bbb","rrr","arr","rar","brr","rbr","rra","rrb","abr","bar"],
-- 804_1316
["aaa","bbb","rrr","rrR","arr","rar","brr","rbr","rra","rrb","abr","bar"],
-- 805_1316
["aaa","bbb","abb","arr","rar","brr","rbr","rra","rrb","abr","bar"],
-- 806_1316
["aaa","bbb","rrr","abb","arr","rar","brr","rbr","rra","rrb","abr","bar"],
-- 807_1316
["aaa","bbb","rrR","abb","arr","rar","brr","rbr","rra","rrb","abr","bar"],
-- 808_1316
["aaa","bbb","rrr","rrR","abb","arr","rar","brr","rbr","rra","rrb","abr","bar"],
-- 809_1316
["aaa","bbb","abb","baa","arr","rar","brr","rbr","rra","rrb","abr","bar"],
-- 810_1316
["aaa","bbb","rrr","abb","baa","arr","rar","brr","rbr","rra","rrb","abr","bar"],
-- 811_1316
["aaa","bbb","rrR","abb","baa","arr","rar","brr","rbr","rra","rrb","abr","bar"],
-- 812_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","rar","brr","rbr","rra","rrb","abr","bar"],
-- 813_1316
["bbb","rrr","raa","rra","rrb","abr","bar"],
-- 814_1316
["aaa","bbb","rrr","raa","rra","rrb","abr","bar"],
-- 815_1316
["bbb","rrr","rrR","raa","rra","rrb","abr","bar"],
-- 816_1316
["aaa","bbb","rrr","rrR","raa","rra","rrb","abr","bar"],
-- 817_1316
["rrr","abb","raa","rra","rrb","abr","bar"],
-- 818_1316
["aaa","rrr","abb","raa","rra","rrb","abr","bar"],
-- 819_1316
["bbb","rrr","abb","raa","rra","rrb","abr","bar"],
-- 820_1316
["aaa","bbb","rrr","abb","raa","rra","rrb","abr","bar"],
-- 821_1316
["rrr","rrR","abb","raa","rra","rrb","abr","bar"],
-- 822_1316
["aaa","rrr","rrR","abb","raa","rra","rrb","abr","bar"],
-- 823_1316
["bbb","rrr","rrR","abb","raa","rra","rrb","abr","bar"],
-- 824_1316
["aaa","bbb","rrr","rrR","abb","raa","rra","rrb","abr","bar"],
-- 825_1316
["bbb","rrr","baa","raa","rra","rrb","abr","bar"],
-- 826_1316
["aaa","bbb","rrr","baa","raa","rra","rrb","abr","bar"],
-- 827_1316
["bbb","rrr","rrR","baa","raa","rra","rrb","abr","bar"],
-- 828_1316
["aaa","bbb","rrr","rrR","baa","raa","rra","rrb","abr","bar"],
-- 829_1316
["rrr","abb","baa","raa","rra","rrb","abr","bar"],
-- 830_1316
["aaa","rrr","abb","baa","raa","rra","rrb","abr","bar"],
-- 831_1316
["bbb","rrr","abb","baa","raa","rra","rrb","abr","bar"],
-- 832_1316
["aaa","bbb","rrr","abb","baa","raa","rra","rrb","abr","bar"],
-- 833_1316
["rrr","rrR","abb","baa","raa","rra","rrb","abr","bar"],
-- 834_1316
["aaa","rrr","rrR","abb","baa","raa","rra","rrb","abr","bar"],
-- 835_1316
["bbb","rrr","rrR","abb","baa","raa","rra","rrb","abr","bar"],
-- 836_1316
["aaa","bbb","rrr","rrR","abb","baa","raa","rra","rrb","abr","bar"],
-- 837_1316
["bbb","rrr","arr","raa","rra","rrb","abr","bar"],
-- 838_1316
["aaa","bbb","rrr","arr","raa","rra","rrb","abr","bar"],
-- 839_1316
["bbb","rrr","rrR","arr","raa","rra","rrb","abr","bar"],
-- 840_1316
["aaa","bbb","rrr","rrR","arr","raa","rra","rrb","abr","bar"],
-- 841_1316
["rrr","abb","arr","raa","rra","rrb","abr","bar"],
-- 842_1316
["aaa","rrr","abb","arr","raa","rra","rrb","abr","bar"],
-- 843_1316
["bbb","rrr","abb","arr","raa","rra","rrb","abr","bar"],
-- 844_1316
["aaa","bbb","rrr","abb","arr","raa","rra","rrb","abr","bar"],
-- 845_1316
["rrr","rrR","abb","arr","raa","rra","rrb","abr","bar"],
-- 846_1316
["aaa","rrr","rrR","abb","arr","raa","rra","rrb","abr","bar"],
-- 847_1316
["bbb","rrr","rrR","abb","arr","raa","rra","rrb","abr","bar"],
-- 848_1316
["aaa","bbb","rrr","rrR","abb","arr","raa","rra","rrb","abr","bar"],
-- 849_1316
["bbb","rrr","baa","arr","raa","rra","rrb","abr","bar"],
-- 850_1316
["aaa","bbb","rrr","baa","arr","raa","rra","rrb","abr","bar"],
-- 851_1316
["bbb","rrr","rrR","baa","arr","raa","rra","rrb","abr","bar"],
-- 852_1316
["aaa","bbb","rrr","rrR","baa","arr","raa","rra","rrb","abr","bar"],
-- 853_1316
["rrr","abb","baa","arr","raa","rra","rrb","abr","bar"],
-- 854_1316
["aaa","rrr","abb","baa","arr","raa","rra","rrb","abr","bar"],
-- 855_1316
["bbb","rrr","abb","baa","arr","raa","rra","rrb","abr","bar"],
-- 856_1316
["aaa","bbb","rrr","abb","baa","arr","raa","rra","rrb","abr","bar"],
-- 857_1316
["rrr","rrR","abb","baa","arr","raa","rra","rrb","abr","bar"],
-- 858_1316
["aaa","rrr","rrR","abb","baa","arr","raa","rra","rrb","abr","bar"],
-- 859_1316
["bbb","rrr","rrR","abb","baa","arr","raa","rra","rrb","abr","bar"],
-- 860_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","raa","rra","rrb","abr","bar"],
-- 861_1316
["bbb","rrr","arr","rar","raa","rra","rrb","abr","bar"],
-- 862_1316
["aaa","bbb","rrr","arr","rar","raa","rra","rrb","abr","bar"],
-- 863_1316
["bbb","rrr","rrR","arr","rar","raa","rra","rrb","abr","bar"],
-- 864_1316
["aaa","bbb","rrr","rrR","arr","rar","raa","rra","rrb","abr","bar"],
-- 865_1316
["rrr","abb","arr","rar","raa","rra","rrb","abr","bar"],
-- 866_1316
["aaa","rrr","abb","arr","rar","raa","rra","rrb","abr","bar"],
-- 867_1316
["bbb","rrr","abb","arr","rar","raa","rra","rrb","abr","bar"],
-- 868_1316
["aaa","bbb","rrr","abb","arr","rar","raa","rra","rrb","abr","bar"],
-- 869_1316
["rrr","rrR","abb","arr","rar","raa","rra","rrb","abr","bar"],
-- 870_1316
["aaa","rrr","rrR","abb","arr","rar","raa","rra","rrb","abr","bar"],
-- 871_1316
["bbb","rrr","rrR","abb","arr","rar","raa","rra","rrb","abr","bar"],
-- 872_1316
["aaa","bbb","rrr","rrR","abb","arr","rar","raa","rra","rrb","abr","bar"],
-- 873_1316
["bbb","baa","arr","rar","raa","rra","rrb","abr","bar"],
-- 874_1316
["aaa","bbb","baa","arr","rar","raa","rra","rrb","abr","bar"],
-- 875_1316
["bbb","rrr","baa","arr","rar","raa","rra","rrb","abr","bar"],
-- 876_1316
["aaa","bbb","rrr","baa","arr","rar","raa","rra","rrb","abr","bar"],
-- 877_1316
["bbb","rrR","baa","arr","rar","raa","rra","rrb","abr","bar"],
-- 878_1316
["aaa","bbb","rrR","baa","arr","rar","raa","rra","rrb","abr","bar"],
-- 879_1316
["bbb","rrr","rrR","baa","arr","rar","raa","rra","rrb","abr","bar"],
-- 880_1316
["aaa","bbb","rrr","rrR","baa","arr","rar","raa","rra","rrb","abr","bar"],
-- 881_1316
["abb","baa","arr","rar","raa","rra","rrb","abr","bar"],
-- 882_1316
["aaa","abb","baa","arr","rar","raa","rra","rrb","abr","bar"],
-- 883_1316
["bbb","abb","baa","arr","rar","raa","rra","rrb","abr","bar"],
-- 884_1316
["aaa","bbb","abb","baa","arr","rar","raa","rra","rrb","abr","bar"],
-- 885_1316
["rrr","abb","baa","arr","rar","raa","rra","rrb","abr","bar"],
-- 886_1316
["aaa","rrr","abb","baa","arr","rar","raa","rra","rrb","abr","bar"],
-- 887_1316
["bbb","rrr","abb","baa","arr","rar","raa","rra","rrb","abr","bar"],
-- 888_1316
["aaa","bbb","rrr","abb","baa","arr","rar","raa","rra","rrb","abr","bar"],
-- 889_1316
["rrR","abb","baa","arr","rar","raa","rra","rrb","abr","bar"],
-- 890_1316
["aaa","rrR","abb","baa","arr","rar","raa","rra","rrb","abr","bar"],
-- 891_1316
["bbb","rrR","abb","baa","arr","rar","raa","rra","rrb","abr","bar"],
-- 892_1316
["aaa","bbb","rrR","abb","baa","arr","rar","raa","rra","rrb","abr","bar"],
-- 893_1316
["rrr","rrR","abb","baa","arr","rar","raa","rra","rrb","abr","bar"],
-- 894_1316
["aaa","rrr","rrR","abb","baa","arr","rar","raa","rra","rrb","abr","bar"],
-- 895_1316
["bbb","rrr","rrR","abb","baa","arr","rar","raa","rra","rrb","abr","bar"],
-- 896_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","rar","raa","rra","rrb","abr","bar"],
-- 897_1316
["bbb","rrr","brr","raa","rra","rrb","abr","bar"],
-- 898_1316
["aaa","bbb","rrr","brr","raa","rra","rrb","abr","bar"],
-- 899_1316
["bbb","rrr","rrR","brr","raa","rra","rrb","abr","bar"],
-- 900_1316
["aaa","bbb","rrr","rrR","brr","raa","rra","rrb","abr","bar"],
-- 901_1316
["rrr","abb","brr","raa","rra","rrb","abr","bar"],
-- 902_1316
["aaa","rrr","abb","brr","raa","rra","rrb","abr","bar"],
-- 903_1316
["bbb","rrr","abb","brr","raa","rra","rrb","abr","bar"],
-- 904_1316
["aaa","bbb","rrr","abb","brr","raa","rra","rrb","abr","bar"],
-- 905_1316
["rrr","rrR","abb","brr","raa","rra","rrb","abr","bar"],
-- 906_1316
["aaa","rrr","rrR","abb","brr","raa","rra","rrb","abr","bar"],
-- 907_1316
["bbb","rrr","rrR","abb","brr","raa","rra","rrb","abr","bar"],
-- 908_1316
["aaa","bbb","rrr","rrR","abb","brr","raa","rra","rrb","abr","bar"],
-- 909_1316
["bbb","rrr","baa","brr","raa","rra","rrb","abr","bar"],
-- 910_1316
["aaa","bbb","rrr","baa","brr","raa","rra","rrb","abr","bar"],
-- 911_1316
["bbb","rrr","rrR","baa","brr","raa","rra","rrb","abr","bar"],
-- 912_1316
["aaa","bbb","rrr","rrR","baa","brr","raa","rra","rrb","abr","bar"],
-- 913_1316
["rrr","abb","baa","brr","raa","rra","rrb","abr","bar"],
-- 914_1316
["aaa","rrr","abb","baa","brr","raa","rra","rrb","abr","bar"],
-- 915_1316
["bbb","rrr","abb","baa","brr","raa","rra","rrb","abr","bar"],
-- 916_1316
["aaa","bbb","rrr","abb","baa","brr","raa","rra","rrb","abr","bar"],
-- 917_1316
["rrr","rrR","abb","baa","brr","raa","rra","rrb","abr","bar"],
-- 918_1316
["aaa","rrr","rrR","abb","baa","brr","raa","rra","rrb","abr","bar"],
-- 919_1316
["bbb","rrr","rrR","abb","baa","brr","raa","rra","rrb","abr","bar"],
-- 920_1316
["aaa","bbb","rrr","rrR","abb","baa","brr","raa","rra","rrb","abr","bar"],
-- 921_1316
["bbb","rrr","arr","brr","raa","rra","rrb","abr","bar"],
-- 922_1316
["aaa","bbb","rrr","arr","brr","raa","rra","rrb","abr","bar"],
-- 923_1316
["bbb","rrr","rrR","arr","brr","raa","rra","rrb","abr","bar"],
-- 924_1316
["aaa","bbb","rrr","rrR","arr","brr","raa","rra","rrb","abr","bar"],
-- 925_1316
["rrr","abb","arr","brr","raa","rra","rrb","abr","bar"],
-- 926_1316
["aaa","rrr","abb","arr","brr","raa","rra","rrb","abr","bar"],
-- 927_1316
["bbb","rrr","abb","arr","brr","raa","rra","rrb","abr","bar"],
-- 928_1316
["aaa","bbb","rrr","abb","arr","brr","raa","rra","rrb","abr","bar"],
-- 929_1316
["rrr","rrR","abb","arr","brr","raa","rra","rrb","abr","bar"],
-- 930_1316
["aaa","rrr","rrR","abb","arr","brr","raa","rra","rrb","abr","bar"],
-- 931_1316
["bbb","rrr","rrR","abb","arr","brr","raa","rra","rrb","abr","bar"],
-- 932_1316
["aaa","bbb","rrr","rrR","abb","arr","brr","raa","rra","rrb","abr","bar"],
-- 933_1316
["bbb","rrr","baa","arr","brr","raa","rra","rrb","abr","bar"],
-- 934_1316
["aaa","bbb","rrr","baa","arr","brr","raa","rra","rrb","abr","bar"],
-- 935_1316
["bbb","rrr","rrR","baa","arr","brr","raa","rra","rrb","abr","bar"],
-- 936_1316
["aaa","bbb","rrr","rrR","baa","arr","brr","raa","rra","rrb","abr","bar"],
-- 937_1316
["rrr","abb","baa","arr","brr","raa","rra","rrb","abr","bar"],
-- 938_1316
["aaa","rrr","abb","baa","arr","brr","raa","rra","rrb","abr","bar"],
-- 939_1316
["bbb","rrr","abb","baa","arr","brr","raa","rra","rrb","abr","bar"],
-- 940_1316
["aaa","bbb","rrr","abb","baa","arr","brr","raa","rra","rrb","abr","bar"],
-- 941_1316
["rrr","rrR","abb","baa","arr","brr","raa","rra","rrb","abr","bar"],
-- 942_1316
["aaa","rrr","rrR","abb","baa","arr","brr","raa","rra","rrb","abr","bar"],
-- 943_1316
["bbb","rrr","rrR","abb","baa","arr","brr","raa","rra","rrb","abr","bar"],
-- 944_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","brr","raa","rra","rrb","abr","bar"],
-- 945_1316
["bbb","rrr","rar","brr","raa","rra","rrb","abr","bar"],
-- 946_1316
["aaa","bbb","rrr","rar","brr","raa","rra","rrb","abr","bar"],
-- 947_1316
["bbb","rrr","rrR","rar","brr","raa","rra","rrb","abr","bar"],
-- 948_1316
["aaa","bbb","rrr","rrR","rar","brr","raa","rra","rrb","abr","bar"],
-- 949_1316
["rrr","abb","rar","brr","raa","rra","rrb","abr","bar"],
-- 950_1316
["aaa","rrr","abb","rar","brr","raa","rra","rrb","abr","bar"],
-- 951_1316
["bbb","rrr","abb","rar","brr","raa","rra","rrb","abr","bar"],
-- 952_1316
["aaa","bbb","rrr","abb","rar","brr","raa","rra","rrb","abr","bar"],
-- 953_1316
["rrr","rrR","abb","rar","brr","raa","rra","rrb","abr","bar"],
-- 954_1316
["aaa","rrr","rrR","abb","rar","brr","raa","rra","rrb","abr","bar"],
-- 955_1316
["bbb","rrr","rrR","abb","rar","brr","raa","rra","rrb","abr","bar"],
-- 956_1316
["aaa","bbb","rrr","rrR","abb","rar","brr","raa","rra","rrb","abr","bar"],
-- 957_1316
["bbb","rrr","baa","rar","brr","raa","rra","rrb","abr","bar"],
-- 958_1316
["aaa","bbb","rrr","baa","rar","brr","raa","rra","rrb","abr","bar"],
-- 959_1316
["bbb","rrr","rrR","baa","rar","brr","raa","rra","rrb","abr","bar"],
-- 960_1316
["aaa","bbb","rrr","rrR","baa","rar","brr","raa","rra","rrb","abr","bar"],
-- 961_1316
["rrr","abb","baa","rar","brr","raa","rra","rrb","abr","bar"],
-- 962_1316
["aaa","rrr","abb","baa","rar","brr","raa","rra","rrb","abr","bar"],
-- 963_1316
["bbb","rrr","abb","baa","rar","brr","raa","rra","rrb","abr","bar"],
-- 964_1316
["aaa","bbb","rrr","abb","baa","rar","brr","raa","rra","rrb","abr","bar"],
-- 965_1316
["rrr","rrR","abb","baa","rar","brr","raa","rra","rrb","abr","bar"],
-- 966_1316
["aaa","rrr","rrR","abb","baa","rar","brr","raa","rra","rrb","abr","bar"],
-- 967_1316
["bbb","rrr","rrR","abb","baa","rar","brr","raa","rra","rrb","abr","bar"],
-- 968_1316
["aaa","bbb","rrr","rrR","abb","baa","rar","brr","raa","rra","rrb","abr","bar"],
-- 969_1316
["bbb","rrr","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 970_1316
["aaa","bbb","rrr","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 971_1316
["bbb","rrr","rrR","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 972_1316
["aaa","bbb","rrr","rrR","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 973_1316
["rrr","abb","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 974_1316
["aaa","rrr","abb","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 975_1316
["bbb","rrr","abb","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 976_1316
["aaa","bbb","rrr","abb","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 977_1316
["rrr","rrR","abb","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 978_1316
["aaa","rrr","rrR","abb","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 979_1316
["bbb","rrr","rrR","abb","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 980_1316
["aaa","bbb","rrr","rrR","abb","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 981_1316
["bbb","baa","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 982_1316
["aaa","bbb","baa","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 983_1316
["bbb","rrr","baa","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 984_1316
["aaa","bbb","rrr","baa","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 985_1316
["bbb","rrR","baa","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 986_1316
["aaa","bbb","rrR","baa","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 987_1316
["bbb","rrr","rrR","baa","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 988_1316
["aaa","bbb","rrr","rrR","baa","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 989_1316
["abb","baa","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 990_1316
["aaa","abb","baa","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 991_1316
["bbb","abb","baa","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 992_1316
["aaa","bbb","abb","baa","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 993_1316
["rrr","abb","baa","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 994_1316
["aaa","rrr","abb","baa","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 995_1316
["bbb","rrr","abb","baa","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 996_1316
["aaa","bbb","rrr","abb","baa","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 997_1316
["rrR","abb","baa","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 998_1316
["aaa","rrR","abb","baa","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 999_1316
["bbb","rrR","abb","baa","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 1000_1316
["aaa","bbb","rrR","abb","baa","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 1001_1316
["rrr","rrR","abb","baa","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 1002_1316
["aaa","rrr","rrR","abb","baa","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 1003_1316
["bbb","rrr","rrR","abb","baa","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 1004_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","rar","brr","raa","rra","rrb","abr","bar"],
-- 1005_1316
["bbb","rrr","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1006_1316
["aaa","bbb","rrr","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1007_1316
["bbb","rrr","rrR","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1008_1316
["aaa","bbb","rrr","rrR","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1009_1316
["rrr","abb","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1010_1316
["aaa","rrr","abb","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1011_1316
["bbb","rrr","abb","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1012_1316
["aaa","bbb","rrr","abb","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1013_1316
["rrr","rrR","abb","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1014_1316
["aaa","rrr","rrR","abb","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1015_1316
["bbb","rrr","rrR","abb","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1016_1316
["aaa","bbb","rrr","rrR","abb","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1017_1316
["bbb","rrr","baa","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1018_1316
["aaa","bbb","rrr","baa","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1019_1316
["bbb","rrr","rrR","baa","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1020_1316
["aaa","bbb","rrr","rrR","baa","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1021_1316
["rrr","abb","baa","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1022_1316
["aaa","rrr","abb","baa","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1023_1316
["bbb","rrr","abb","baa","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1024_1316
["aaa","bbb","rrr","abb","baa","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1025_1316
["rrr","rrR","abb","baa","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1026_1316
["aaa","rrr","rrR","abb","baa","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1027_1316
["bbb","rrr","rrR","abb","baa","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1028_1316
["aaa","bbb","rrr","rrR","abb","baa","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1029_1316
["bbb","rrr","arr","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1030_1316
["aaa","bbb","rrr","arr","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1031_1316
["bbb","rrr","rrR","arr","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1032_1316
["aaa","bbb","rrr","rrR","arr","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1033_1316
["rrr","abb","arr","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1034_1316
["aaa","rrr","abb","arr","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1035_1316
["bbb","rrr","abb","arr","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1036_1316
["aaa","bbb","rrr","abb","arr","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1037_1316
["rrr","rrR","abb","arr","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1038_1316
["aaa","rrr","rrR","abb","arr","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1039_1316
["bbb","rrr","rrR","abb","arr","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1040_1316
["aaa","bbb","rrr","rrR","abb","arr","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1041_1316
["bbb","rrr","baa","arr","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1042_1316
["aaa","bbb","rrr","baa","arr","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1043_1316
["bbb","rrr","rrR","baa","arr","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1044_1316
["aaa","bbb","rrr","rrR","baa","arr","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1045_1316
["rrr","abb","baa","arr","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1046_1316
["aaa","rrr","abb","baa","arr","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1047_1316
["bbb","rrr","abb","baa","arr","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1048_1316
["aaa","bbb","rrr","abb","baa","arr","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1049_1316
["rrr","rrR","abb","baa","arr","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1050_1316
["aaa","rrr","rrR","abb","baa","arr","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1051_1316
["bbb","rrr","rrR","abb","baa","arr","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1052_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1053_1316
["bbb","rrr","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1054_1316
["aaa","bbb","rrr","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1055_1316
["bbb","rrr","rrR","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1056_1316
["aaa","bbb","rrr","rrR","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1057_1316
["aaa","abb","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1058_1316
["aaa","bbb","abb","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1059_1316
["rrr","abb","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1060_1316
["aaa","rrr","abb","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1061_1316
["bbb","rrr","abb","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1062_1316
["aaa","bbb","rrr","abb","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1063_1316
["rrR","abb","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1064_1316
["aaa","rrR","abb","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1065_1316
["bbb","rrR","abb","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1066_1316
["aaa","bbb","rrR","abb","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1067_1316
["rrr","rrR","abb","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1068_1316
["aaa","rrr","rrR","abb","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1069_1316
["bbb","rrr","rrR","abb","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1070_1316
["aaa","bbb","rrr","rrR","abb","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1071_1316
["bbb","baa","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1072_1316
["aaa","bbb","baa","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1073_1316
["bbb","rrr","baa","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1074_1316
["aaa","bbb","rrr","baa","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1075_1316
["bbb","rrR","baa","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1076_1316
["aaa","bbb","rrR","baa","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1077_1316
["bbb","rrr","rrR","baa","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1078_1316
["aaa","bbb","rrr","rrR","baa","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1079_1316
["abb","baa","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1080_1316
["aaa","abb","baa","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1081_1316
["bbb","abb","baa","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1082_1316
["aaa","bbb","abb","baa","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1083_1316
["rrr","abb","baa","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1084_1316
["aaa","rrr","abb","baa","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1085_1316
["bbb","rrr","abb","baa","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1086_1316
["aaa","bbb","rrr","abb","baa","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1087_1316
["rrR","abb","baa","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1088_1316
["aaa","rrR","abb","baa","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1089_1316
["bbb","rrR","abb","baa","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1090_1316
["aaa","bbb","rrR","abb","baa","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1091_1316
["rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1092_1316
["aaa","rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1093_1316
["bbb","rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1094_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rra","rrb","abr","bar"],
-- 1095_1316
["rrr","raa","rbb","rra","rrb","abr","bar"],
-- 1096_1316
["aaa","rrr","raa","rbb","rra","rrb","abr","bar"],
-- 1097_1316
["aaa","bbb","rrr","raa","rbb","rra","rrb","abr","bar"],
-- 1098_1316
["rrr","rrR","raa","rbb","rra","rrb","abr","bar"],
-- 1099_1316
["aaa","rrr","rrR","raa","rbb","rra","rrb","abr","bar"],
-- 1100_1316
["aaa","bbb","rrr","rrR","raa","rbb","rra","rrb","abr","bar"],
-- 1101_1316
["rrr","abb","raa","rbb","rra","rrb","abr","bar"],
-- 1102_1316
["aaa","rrr","abb","raa","rbb","rra","rrb","abr","bar"],
-- 1103_1316
["bbb","rrr","abb","raa","rbb","rra","rrb","abr","bar"],
-- 1104_1316
["aaa","bbb","rrr","abb","raa","rbb","rra","rrb","abr","bar"],
-- 1105_1316
["rrr","rrR","abb","raa","rbb","rra","rrb","abr","bar"],
-- 1106_1316
["aaa","rrr","rrR","abb","raa","rbb","rra","rrb","abr","bar"],
-- 1107_1316
["bbb","rrr","rrR","abb","raa","rbb","rra","rrb","abr","bar"],
-- 1108_1316
["aaa","bbb","rrr","rrR","abb","raa","rbb","rra","rrb","abr","bar"],
-- 1109_1316
["rrr","abb","baa","raa","rbb","rra","rrb","abr","bar"],
-- 1110_1316
["aaa","rrr","abb","baa","raa","rbb","rra","rrb","abr","bar"],
-- 1111_1316
["aaa","bbb","rrr","abb","baa","raa","rbb","rra","rrb","abr","bar"],
-- 1112_1316
["rrr","rrR","abb","baa","raa","rbb","rra","rrb","abr","bar"],
-- 1113_1316
["aaa","rrr","rrR","abb","baa","raa","rbb","rra","rrb","abr","bar"],
-- 1114_1316
["aaa","bbb","rrr","rrR","abb","baa","raa","rbb","rra","rrb","abr","bar"],
-- 1115_1316
["rrr","arr","raa","rbb","rra","rrb","abr","bar"],
-- 1116_1316
["aaa","rrr","arr","raa","rbb","rra","rrb","abr","bar"],
-- 1117_1316
["bbb","rrr","arr","raa","rbb","rra","rrb","abr","bar"],
-- 1118_1316
["aaa","bbb","rrr","arr","raa","rbb","rra","rrb","abr","bar"],
-- 1119_1316
["rrr","rrR","arr","raa","rbb","rra","rrb","abr","bar"],
-- 1120_1316
["aaa","rrr","rrR","arr","raa","rbb","rra","rrb","abr","bar"],
-- 1121_1316
["bbb","rrr","rrR","arr","raa","rbb","rra","rrb","abr","bar"],
-- 1122_1316
["aaa","bbb","rrr","rrR","arr","raa","rbb","rra","rrb","abr","bar"],
-- 1123_1316
["rrr","abb","arr","raa","rbb","rra","rrb","abr","bar"],
-- 1124_1316
["aaa","rrr","abb","arr","raa","rbb","rra","rrb","abr","bar"],
-- 1125_1316
["bbb","rrr","abb","arr","raa","rbb","rra","rrb","abr","bar"],
-- 1126_1316
["aaa","bbb","rrr","abb","arr","raa","rbb","rra","rrb","abr","bar"],
-- 1127_1316
["rrr","rrR","abb","arr","raa","rbb","rra","rrb","abr","bar"],
-- 1128_1316
["aaa","rrr","rrR","abb","arr","raa","rbb","rra","rrb","abr","bar"],
-- 1129_1316
["bbb","rrr","rrR","abb","arr","raa","rbb","rra","rrb","abr","bar"],
-- 1130_1316
["aaa","bbb","rrr","rrR","abb","arr","raa","rbb","rra","rrb","abr","bar"],
-- 1131_1316
["rrr","baa","arr","raa","rbb","rra","rrb","abr","bar"],
-- 1132_1316
["aaa","rrr","baa","arr","raa","rbb","rra","rrb","abr","bar"],
-- 1133_1316
["bbb","rrr","baa","arr","raa","rbb","rra","rrb","abr","bar"],
-- 1134_1316
["aaa","bbb","rrr","baa","arr","raa","rbb","rra","rrb","abr","bar"],
-- 1135_1316
["rrr","rrR","baa","arr","raa","rbb","rra","rrb","abr","bar"],
-- 1136_1316
["aaa","rrr","rrR","baa","arr","raa","rbb","rra","rrb","abr","bar"],
-- 1137_1316
["bbb","rrr","rrR","baa","arr","raa","rbb","rra","rrb","abr","bar"],
-- 1138_1316
["aaa","bbb","rrr","rrR","baa","arr","raa","rbb","rra","rrb","abr","bar"],
-- 1139_1316
["rrr","abb","baa","arr","raa","rbb","rra","rrb","abr","bar"],
-- 1140_1316
["aaa","rrr","abb","baa","arr","raa","rbb","rra","rrb","abr","bar"],
-- 1141_1316
["bbb","rrr","abb","baa","arr","raa","rbb","rra","rrb","abr","bar"],
-- 1142_1316
["aaa","bbb","rrr","abb","baa","arr","raa","rbb","rra","rrb","abr","bar"],
-- 1143_1316
["rrr","rrR","abb","baa","arr","raa","rbb","rra","rrb","abr","bar"],
-- 1144_1316
["aaa","rrr","rrR","abb","baa","arr","raa","rbb","rra","rrb","abr","bar"],
-- 1145_1316
["bbb","rrr","rrR","abb","baa","arr","raa","rbb","rra","rrb","abr","bar"],
-- 1146_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","raa","rbb","rra","rrb","abr","bar"],
-- 1147_1316
["rrr","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1148_1316
["aaa","rrr","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1149_1316
["bbb","rrr","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1150_1316
["aaa","bbb","rrr","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1151_1316
["rrr","rrR","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1152_1316
["aaa","rrr","rrR","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1153_1316
["bbb","rrr","rrR","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1154_1316
["aaa","bbb","rrr","rrR","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1155_1316
["rrr","abb","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1156_1316
["aaa","rrr","abb","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1157_1316
["bbb","rrr","abb","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1158_1316
["aaa","bbb","rrr","abb","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1159_1316
["rrr","rrR","abb","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1160_1316
["aaa","rrr","rrR","abb","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1161_1316
["bbb","rrr","rrR","abb","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1162_1316
["aaa","bbb","rrr","rrR","abb","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1163_1316
["bbb","baa","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1164_1316
["aaa","bbb","baa","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1165_1316
["rrr","baa","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1166_1316
["aaa","rrr","baa","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1167_1316
["bbb","rrr","baa","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1168_1316
["aaa","bbb","rrr","baa","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1169_1316
["rrR","baa","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1170_1316
["aaa","rrR","baa","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1171_1316
["bbb","rrR","baa","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1172_1316
["aaa","bbb","rrR","baa","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1173_1316
["rrr","rrR","baa","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1174_1316
["aaa","rrr","rrR","baa","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1175_1316
["bbb","rrr","rrR","baa","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1176_1316
["aaa","bbb","rrr","rrR","baa","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1177_1316
["abb","baa","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1178_1316
["aaa","abb","baa","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1179_1316
["bbb","abb","baa","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1180_1316
["aaa","bbb","abb","baa","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1181_1316
["rrr","abb","baa","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1182_1316
["aaa","rrr","abb","baa","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1183_1316
["bbb","rrr","abb","baa","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1184_1316
["aaa","bbb","rrr","abb","baa","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1185_1316
["rrR","abb","baa","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1186_1316
["aaa","rrR","abb","baa","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1187_1316
["bbb","rrR","abb","baa","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1188_1316
["aaa","bbb","rrR","abb","baa","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1189_1316
["rrr","rrR","abb","baa","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1190_1316
["aaa","rrr","rrR","abb","baa","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1191_1316
["bbb","rrr","rrR","abb","baa","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1192_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","rar","raa","rbb","rra","rrb","abr","bar"],
-- 1193_1316
["rrr","arr","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1194_1316
["aaa","rrr","arr","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1195_1316
["aaa","bbb","rrr","arr","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1196_1316
["rrr","rrR","arr","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1197_1316
["aaa","rrr","rrR","arr","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1198_1316
["aaa","bbb","rrr","rrR","arr","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1199_1316
["rrr","abb","arr","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1200_1316
["aaa","rrr","abb","arr","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1201_1316
["bbb","rrr","abb","arr","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1202_1316
["aaa","bbb","rrr","abb","arr","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1203_1316
["rrr","rrR","abb","arr","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1204_1316
["aaa","rrr","rrR","abb","arr","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1205_1316
["bbb","rrr","rrR","abb","arr","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1206_1316
["aaa","bbb","rrr","rrR","abb","arr","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1207_1316
["rrr","abb","baa","arr","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1208_1316
["aaa","rrr","abb","baa","arr","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1209_1316
["aaa","bbb","rrr","abb","baa","arr","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1210_1316
["rrr","rrR","abb","baa","arr","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1211_1316
["aaa","rrr","rrR","abb","baa","arr","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1212_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1213_1316
["rrr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1214_1316
["aaa","rrr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1215_1316
["aaa","bbb","rrr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1216_1316
["rrr","rrR","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1217_1316
["aaa","rrr","rrR","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1218_1316
["aaa","bbb","rrr","rrR","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1219_1316
["rrr","abb","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1220_1316
["aaa","rrr","abb","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1221_1316
["bbb","rrr","abb","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1222_1316
["aaa","bbb","rrr","abb","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1223_1316
["rrr","rrR","abb","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1224_1316
["aaa","rrr","rrR","abb","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1225_1316
["bbb","rrr","rrR","abb","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1226_1316
["aaa","bbb","rrr","rrR","abb","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1227_1316
["abb","baa","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1228_1316
["aaa","abb","baa","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1229_1316
["aaa","bbb","abb","baa","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1230_1316
["rrr","abb","baa","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1231_1316
["aaa","rrr","abb","baa","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1232_1316
["aaa","bbb","rrr","abb","baa","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1233_1316
["rrR","abb","baa","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1234_1316
["aaa","rrR","abb","baa","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1235_1316
["aaa","bbb","rrR","abb","baa","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1236_1316
["rrr","rrR","abb","baa","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1237_1316
["aaa","rrr","rrR","abb","baa","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1238_1316
["aaa","bbb","rrr","rrR","abb","baa","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1239_1316
["rrr","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1240_1316
["aaa","rrr","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1241_1316
["bbb","rrr","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1242_1316
["aaa","bbb","rrr","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1243_1316
["rrr","rrR","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1244_1316
["aaa","rrr","rrR","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1245_1316
["bbb","rrr","rrR","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1246_1316
["aaa","bbb","rrr","rrR","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1247_1316
["rrr","abb","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1248_1316
["aaa","rrr","abb","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1249_1316
["bbb","rrr","abb","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1250_1316
["aaa","bbb","rrr","abb","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1251_1316
["rrr","rrR","abb","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1252_1316
["aaa","rrr","rrR","abb","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1253_1316
["bbb","rrr","rrR","abb","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1254_1316
["aaa","bbb","rrr","rrR","abb","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1255_1316
["bbb","baa","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1256_1316
["aaa","bbb","baa","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1257_1316
["rrr","baa","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1258_1316
["aaa","rrr","baa","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1259_1316
["bbb","rrr","baa","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1260_1316
["aaa","bbb","rrr","baa","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1261_1316
["rrR","baa","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1262_1316
["aaa","rrR","baa","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1263_1316
["bbb","rrR","baa","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1264_1316
["aaa","bbb","rrR","baa","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1265_1316
["rrr","rrR","baa","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1266_1316
["aaa","rrr","rrR","baa","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1267_1316
["bbb","rrr","rrR","baa","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1268_1316
["aaa","bbb","rrr","rrR","baa","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1269_1316
["abb","baa","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1270_1316
["aaa","abb","baa","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1271_1316
["bbb","abb","baa","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1272_1316
["aaa","bbb","abb","baa","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1273_1316
["rrr","abb","baa","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1274_1316
["aaa","rrr","abb","baa","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1275_1316
["bbb","rrr","abb","baa","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1276_1316
["aaa","bbb","rrr","abb","baa","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1277_1316
["rrR","abb","baa","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1278_1316
["aaa","rrR","abb","baa","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1279_1316
["bbb","rrR","abb","baa","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1280_1316
["aaa","bbb","rrR","abb","baa","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1281_1316
["rrr","rrR","abb","baa","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1282_1316
["aaa","rrr","rrR","abb","baa","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1283_1316
["bbb","rrr","rrR","abb","baa","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1284_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","rar","brr","raa","rbb","rra","rrb","abr","bar"],
-- 1285_1316
["rrr","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr","bar"],
-- 1286_1316
["aaa","rrr","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr","bar"],
-- 1287_1316
["aaa","bbb","rrr","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr","bar"],
-- 1288_1316
["rrr","rrR","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr","bar"],
-- 1289_1316
["aaa","rrr","rrR","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr","bar"],
-- 1290_1316
["aaa","bbb","rrr","rrR","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr","bar"],
-- 1291_1316
["aaa","abb","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr","bar"],
-- 1292_1316
["aaa","bbb","abb","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr","bar"],
-- 1293_1316
["rrr","abb","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr","bar"],
-- 1294_1316
["aaa","rrr","abb","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr","bar"],
-- 1295_1316
["bbb","rrr","abb","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr","bar"],
-- 1296_1316
["aaa","bbb","rrr","abb","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr","bar"],
-- 1297_1316
["rrR","abb","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr","bar"],
-- 1298_1316
["aaa","rrR","abb","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr","bar"],
-- 1299_1316
["bbb","rrR","abb","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr","bar"],
-- 1300_1316
["aaa","bbb","rrR","abb","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr","bar"],
-- 1301_1316
["rrr","rrR","abb","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr","bar"],
-- 1302_1316
["aaa","rrr","rrR","abb","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr","bar"],
-- 1303_1316
["bbb","rrr","rrR","abb","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr","bar"],
-- 1304_1316
["aaa","bbb","rrr","rrR","abb","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr","bar"],
-- 1305_1316
["abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr","bar"],
-- 1306_1316
["aaa","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr","bar"],
-- 1307_1316
["aaa","bbb","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr","bar"],
-- 1308_1316
["rrr","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr","bar"],
-- 1309_1316
["aaa","rrr","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr","bar"],
-- 1310_1316
["aaa","bbb","rrr","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr","bar"],
-- 1311_1316
["rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr","bar"],
-- 1312_1316
["aaa","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr","bar"],
-- 1313_1316
["aaa","bbb","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr","bar"],
-- 1314_1316
["rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr","bar"],
-- 1315_1316
["aaa","rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr","bar"],
-- 1316_1316
["aaa","bbb","rrr","rrR","abb","baa","arr","rar","brr","rbr","raa","rbb","rra","rrb","abr","bar"]
],
[
-- 1_3013
["abb","acc","add","bcc","bdd","cdd"],
-- 2_3013
["aaa","abb","acc","add","bcc","bdd","cdd"],
-- 3_3013
["bbb","abb","acc","add","bcc","bdd","cdd"],
-- 4_3013
["aaa","bbb","abb","acc","add","bcc","bdd","cdd"],
-- 5_3013
["ccc","abb","acc","add","bcc","bdd","cdd"],
-- 6_3013
["aaa","ccc","abb","acc","add","bcc","bdd","cdd"],
-- 7_3013
["bbb","ccc","abb","acc","add","bcc","bdd","cdd"],
-- 8_3013
["aaa","bbb","ccc","abb","acc","add","bcc","bdd","cdd"],
-- 9_3013
["ddd","abb","acc","add","bcc","bdd","cdd"],
-- 10_3013
["aaa","ddd","abb","acc","add","bcc","bdd","cdd"],
-- 11_3013
["bbb","ddd","abb","acc","add","bcc","bdd","cdd"],
-- 12_3013
["aaa","bbb","ddd","abb","acc","add","bcc","bdd","cdd"],
-- 13_3013
["ccc","ddd","abb","acc","add","bcc","bdd","cdd"],
-- 14_3013
["aaa","ccc","ddd","abb","acc","add","bcc","bdd","cdd"],
-- 15_3013
["bbb","ccc","ddd","abb","acc","add","bcc","bdd","cdd"],
-- 16_3013
["aaa","bbb","ccc","ddd","abb","acc","add","bcc","bdd","cdd"],
-- 17_3013
["abb","baa","acc","add","bcc","bdd","cdd"],
-- 18_3013
["aaa","abb","baa","acc","add","bcc","bdd","cdd"],
-- 19_3013
["aaa","bbb","abb","baa","acc","add","bcc","bdd","cdd"],
-- 20_3013
["ccc","abb","baa","acc","add","bcc","bdd","cdd"],
-- 21_3013
["aaa","ccc","abb","baa","acc","add","bcc","bdd","cdd"],
-- 22_3013
["aaa","bbb","ccc","abb","baa","acc","add","bcc","bdd","cdd"],
-- 23_3013
["ddd","abb","baa","acc","add","bcc","bdd","cdd"],
-- 24_3013
["aaa","ddd","abb","baa","acc","add","bcc","bdd","cdd"],
-- 25_3013
["aaa","bbb","ddd","abb","baa","acc","add","bcc","bdd","cdd"],
-- 26_3013
["ccc","ddd","abb","baa","acc","add","bcc","bdd","cdd"],
-- 27_3013
["aaa","ccc","ddd","abb","baa","acc","add","bcc","bdd","cdd"],
-- 28_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","add","bcc","bdd","cdd"],
-- 29_3013
["baa","acc","caa","add","bcc","bdd","cdd"],
-- 30_3013
["aaa","baa","acc","caa","add","bcc","bdd","cdd"],
-- 31_3013
["bbb","baa","acc","caa","add","bcc","bdd","cdd"],
-- 32_3013
["aaa","bbb","baa","acc","caa","add","bcc","bdd","cdd"],
-- 33_3013
["aaa","ccc","baa","acc","caa","add","bcc","bdd","cdd"],
-- 34_3013
["aaa","bbb","ccc","baa","acc","caa","add","bcc","bdd","cdd"],
-- 35_3013
["ddd","baa","acc","caa","add","bcc","bdd","cdd"],
-- 36_3013
["aaa","ddd","baa","acc","caa","add","bcc","bdd","cdd"],
-- 37_3013
["bbb","ddd","baa","acc","caa","add","bcc","bdd","cdd"],
-- 38_3013
["aaa","bbb","ddd","baa","acc","caa","add","bcc","bdd","cdd"],
-- 39_3013
["aaa","ccc","ddd","baa","acc","caa","add","bcc","bdd","cdd"],
-- 40_3013
["aaa","bbb","ccc","ddd","baa","acc","caa","add","bcc","bdd","cdd"],
-- 41_3013
["baa","caa","add","daa","bcc","bdd","cdd"],
-- 42_3013
["aaa","baa","caa","add","daa","bcc","bdd","cdd"],
-- 43_3013
["bbb","baa","caa","add","daa","bcc","bdd","cdd"],
-- 44_3013
["aaa","bbb","baa","caa","add","daa","bcc","bdd","cdd"],
-- 45_3013
["ccc","baa","caa","add","daa","bcc","bdd","cdd"],
-- 46_3013
["aaa","ccc","baa","caa","add","daa","bcc","bdd","cdd"],
-- 47_3013
["bbb","ccc","baa","caa","add","daa","bcc","bdd","cdd"],
-- 48_3013
["aaa","bbb","ccc","baa","caa","add","daa","bcc","bdd","cdd"],
-- 49_3013
["aaa","ddd","baa","caa","add","daa","bcc","bdd","cdd"],
-- 50_3013
["aaa","bbb","ddd","baa","caa","add","daa","bcc","bdd","cdd"],
-- 51_3013
["aaa","ccc","ddd","baa","caa","add","daa","bcc","bdd","cdd"],
-- 52_3013
["aaa","bbb","ccc","ddd","baa","caa","add","daa","bcc","bdd","cdd"],
-- 53_3013
["abb","baa","acc","caa","add","bcc","cbb","bdd","cdd"],
-- 54_3013
["aaa","abb","baa","acc","caa","add","bcc","cbb","bdd","cdd"],
-- 55_3013
["aaa","bbb","abb","baa","acc","caa","add","bcc","cbb","bdd","cdd"],
-- 56_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","bcc","cbb","bdd","cdd"],
-- 57_3013
["ddd","abb","baa","acc","caa","add","bcc","cbb","bdd","cdd"],
-- 58_3013
["aaa","ddd","abb","baa","acc","caa","add","bcc","cbb","bdd","cdd"],
-- 59_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","bcc","cbb","bdd","cdd"],
-- 60_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","bcc","cbb","bdd","cdd"],
-- 61_3013
["baa","caa","add","daa","bcc","cbb","bdd","cdd"],
-- 62_3013
["aaa","baa","caa","add","daa","bcc","cbb","bdd","cdd"],
-- 63_3013
["bbb","baa","caa","add","daa","bcc","cbb","bdd","cdd"],
-- 64_3013
["aaa","bbb","baa","caa","add","daa","bcc","cbb","bdd","cdd"],
-- 65_3013
["bbb","ccc","baa","caa","add","daa","bcc","cbb","bdd","cdd"],
-- 66_3013
["aaa","bbb","ccc","baa","caa","add","daa","bcc","cbb","bdd","cdd"],
-- 67_3013
["aaa","ddd","baa","caa","add","daa","bcc","cbb","bdd","cdd"],
-- 68_3013
["aaa","bbb","ddd","baa","caa","add","daa","bcc","cbb","bdd","cdd"],
-- 69_3013
["aaa","bbb","ccc","ddd","baa","caa","add","daa","bcc","cbb","bdd","cdd"],
-- 70_3013
["abb","baa","caa","add","daa","cbb","bdd","dbb","cdd"],
-- 71_3013
["aaa","abb","baa","caa","add","daa","cbb","bdd","dbb","cdd"],
-- 72_3013
["aaa","bbb","abb","baa","caa","add","daa","cbb","bdd","dbb","cdd"],
-- 73_3013
["ccc","abb","baa","caa","add","daa","cbb","bdd","dbb","cdd"],
-- 74_3013
["aaa","ccc","abb","baa","caa","add","daa","cbb","bdd","dbb","cdd"],
-- 75_3013
["aaa","bbb","ccc","abb","baa","caa","add","daa","cbb","bdd","dbb","cdd"],
-- 76_3013
["aaa","bbb","ddd","abb","baa","caa","add","daa","cbb","bdd","dbb","cdd"],
-- 77_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","add","daa","cbb","bdd","dbb","cdd"],
-- 78_3013
["abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc"],
-- 79_3013
["aaa","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc"],
-- 80_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc"],
-- 81_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc"],
-- 82_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc"],
-- 83_3013
["add","bdd","cdd","abc"],
-- 84_3013
["ddd","add","bdd","cdd","abc"],
-- 85_3013
["aaa","abb","add","bdd","cdd","abc"],
-- 86_3013
["aaa","ddd","abb","add","bdd","cdd","abc"],
-- 87_3013
["aaa","bbb","abb","baa","add","bdd","cdd","abc"],
-- 88_3013
["aaa","bbb","ddd","abb","baa","add","bdd","cdd","abc"],
-- 89_3013
["aaa","abb","acc","add","bdd","cdd","abc"],
-- 90_3013
["aaa","ddd","abb","acc","add","bdd","cdd","abc"],
-- 91_3013
["aaa","bbb","ccc","baa","caa","add","bdd","cdd","abc"],
-- 92_3013
["aaa","bbb","ccc","ddd","baa","caa","add","bdd","cdd","abc"],
-- 93_3013
["aaa","ccc","abb","baa","caa","add","bdd","cdd","abc"],
-- 94_3013
["aaa","bbb","ccc","abb","baa","caa","add","bdd","cdd","abc"],
-- 95_3013
["aaa","ccc","ddd","abb","baa","caa","add","bdd","cdd","abc"],
-- 96_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","add","bdd","cdd","abc"],
-- 97_3013
["aaa","abb","baa","acc","caa","add","bdd","cdd","abc"],
-- 98_3013
["aaa","bbb","abb","baa","acc","caa","add","bdd","cdd","abc"],
-- 99_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","bdd","cdd","abc"],
-- 100_3013
["aaa","ddd","abb","baa","acc","caa","add","bdd","cdd","abc"],
-- 101_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","bdd","cdd","abc"],
-- 102_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","bdd","cdd","abc"],
-- 103_3013
["aaa","bbb","abb","acc","add","bcc","bdd","cdd","abc"],
-- 104_3013
["aaa","bbb","ccc","abb","acc","add","bcc","bdd","cdd","abc"],
-- 105_3013
["aaa","bbb","ddd","abb","acc","add","bcc","bdd","cdd","abc"],
-- 106_3013
["aaa","bbb","ccc","ddd","abb","acc","add","bcc","bdd","cdd","abc"],
-- 107_3013
["aaa","bbb","abb","baa","acc","add","bcc","bdd","cdd","abc"],
-- 108_3013
["aaa","bbb","ccc","abb","baa","acc","add","bcc","bdd","cdd","abc"],
-- 109_3013
["aaa","bbb","ddd","abb","baa","acc","add","bcc","bdd","cdd","abc"],
-- 110_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","add","bcc","bdd","cdd","abc"],
-- 111_3013
["abb","caa","add","bcc","bdd","cdd","abc"],
-- 112_3013
["aaa","abb","caa","add","bcc","bdd","cdd","abc"],
-- 113_3013
["aaa","bbb","abb","caa","add","bcc","bdd","cdd","abc"],
-- 114_3013
["aaa","bbb","ccc","abb","caa","add","bcc","bdd","cdd","abc"],
-- 115_3013
["ddd","abb","caa","add","bcc","bdd","cdd","abc"],
-- 116_3013
["aaa","ddd","abb","caa","add","bcc","bdd","cdd","abc"],
-- 117_3013
["aaa","bbb","ddd","abb","caa","add","bcc","bdd","cdd","abc"],
-- 118_3013
["aaa","bbb","ccc","ddd","abb","caa","add","bcc","bdd","cdd","abc"],
-- 119_3013
["abb","baa","caa","add","bcc","bdd","cdd","abc"],
-- 120_3013
["aaa","abb","baa","caa","add","bcc","bdd","cdd","abc"],
-- 121_3013
["bbb","abb","baa","caa","add","bcc","bdd","cdd","abc"],
-- 122_3013
["aaa","bbb","abb","baa","caa","add","bcc","bdd","cdd","abc"],
-- 123_3013
["ccc","abb","baa","caa","add","bcc","bdd","cdd","abc"],
-- 124_3013
["aaa","ccc","abb","baa","caa","add","bcc","bdd","cdd","abc"],
-- 125_3013
["bbb","ccc","abb","baa","caa","add","bcc","bdd","cdd","abc"],
-- 126_3013
["aaa","bbb","ccc","abb","baa","caa","add","bcc","bdd","cdd","abc"],
-- 127_3013
["ddd","abb","baa","caa","add","bcc","bdd","cdd","abc"],
-- 128_3013
["aaa","ddd","abb","baa","caa","add","bcc","bdd","cdd","abc"],
-- 129_3013
["bbb","ddd","abb","baa","caa","add","bcc","bdd","cdd","abc"],
-- 130_3013
["aaa","bbb","ddd","abb","baa","caa","add","bcc","bdd","cdd","abc"],
-- 131_3013
["ccc","ddd","abb","baa","caa","add","bcc","bdd","cdd","abc"],
-- 132_3013
["aaa","ccc","ddd","abb","baa","caa","add","bcc","bdd","cdd","abc"],
-- 133_3013
["bbb","ccc","ddd","abb","baa","caa","add","bcc","bdd","cdd","abc"],
-- 134_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","add","bcc","bdd","cdd","abc"],
-- 135_3013
["bbb","baa","acc","caa","add","bcc","bdd","cdd","abc"],
-- 136_3013
["aaa","bbb","baa","acc","caa","add","bcc","bdd","cdd","abc"],
-- 137_3013
["aaa","bbb","ccc","baa","acc","caa","add","bcc","bdd","cdd","abc"],
-- 138_3013
["bbb","ddd","baa","acc","caa","add","bcc","bdd","cdd","abc"],
-- 139_3013
["aaa","bbb","ddd","baa","acc","caa","add","bcc","bdd","cdd","abc"],
-- 140_3013
["aaa","bbb","ccc","ddd","baa","acc","caa","add","bcc","bdd","cdd","abc"],
-- 141_3013
["abb","baa","acc","caa","add","bcc","bdd","cdd","abc"],
-- 142_3013
["aaa","abb","baa","acc","caa","add","bcc","bdd","cdd","abc"],
-- 143_3013
["bbb","abb","baa","acc","caa","add","bcc","bdd","cdd","abc"],
-- 144_3013
["aaa","bbb","abb","baa","acc","caa","add","bcc","bdd","cdd","abc"],
-- 145_3013
["ccc","abb","baa","acc","caa","add","bcc","bdd","cdd","abc"],
-- 146_3013
["aaa","ccc","abb","baa","acc","caa","add","bcc","bdd","cdd","abc"],
-- 147_3013
["bbb","ccc","abb","baa","acc","caa","add","bcc","bdd","cdd","abc"],
-- 148_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","bcc","bdd","cdd","abc"],
-- 149_3013
["ddd","abb","baa","acc","caa","add","bcc","bdd","cdd","abc"],
-- 150_3013
["aaa","ddd","abb","baa","acc","caa","add","bcc","bdd","cdd","abc"],
-- 151_3013
["bbb","ddd","abb","baa","acc","caa","add","bcc","bdd","cdd","abc"],
-- 152_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","bcc","bdd","cdd","abc"],
-- 153_3013
["ccc","ddd","abb","baa","acc","caa","add","bcc","bdd","cdd","abc"],
-- 154_3013
["aaa","ccc","ddd","abb","baa","acc","caa","add","bcc","bdd","cdd","abc"],
-- 155_3013
["bbb","ccc","ddd","abb","baa","acc","caa","add","bcc","bdd","cdd","abc"],
-- 156_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","bcc","bdd","cdd","abc"],
-- 157_3013
["abb","baa","acc","caa","add","bcc","cbb","bdd","cdd","abc"],
-- 158_3013
["aaa","abb","baa","acc","caa","add","bcc","cbb","bdd","cdd","abc"],
-- 159_3013
["aaa","bbb","abb","baa","acc","caa","add","bcc","cbb","bdd","cdd","abc"],
-- 160_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","bcc","cbb","bdd","cdd","abc"],
-- 161_3013
["ddd","abb","baa","acc","caa","add","bcc","cbb","bdd","cdd","abc"],
-- 162_3013
["aaa","ddd","abb","baa","acc","caa","add","bcc","cbb","bdd","cdd","abc"],
-- 163_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","bcc","cbb","bdd","cdd","abc"],
-- 164_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","bcc","cbb","bdd","cdd","abc"],
-- 165_3013
["daa","dbb","dcc","abc"],
-- 166_3013
["ddd","daa","dbb","dcc","abc"],
-- 167_3013
["aaa","abb","daa","dbb","dcc","abc"],
-- 168_3013
["aaa","ddd","abb","daa","dbb","dcc","abc"],
-- 169_3013
["aaa","bbb","abb","baa","daa","dbb","dcc","abc"],
-- 170_3013
["aaa","bbb","ddd","abb","baa","daa","dbb","dcc","abc"],
-- 171_3013
["aaa","abb","acc","daa","dbb","dcc","abc"],
-- 172_3013
["aaa","ddd","abb","acc","daa","dbb","dcc","abc"],
-- 173_3013
["aaa","bbb","ccc","baa","caa","daa","dbb","dcc","abc"],
-- 174_3013
["aaa","bbb","ccc","ddd","baa","caa","daa","dbb","dcc","abc"],
-- 175_3013
["aaa","ccc","abb","baa","caa","daa","dbb","dcc","abc"],
-- 176_3013
["aaa","bbb","ccc","abb","baa","caa","daa","dbb","dcc","abc"],
-- 177_3013
["aaa","ccc","ddd","abb","baa","caa","daa","dbb","dcc","abc"],
-- 178_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","daa","dbb","dcc","abc"],
-- 179_3013
["aaa","abb","baa","acc","caa","daa","dbb","dcc","abc"],
-- 180_3013
["aaa","bbb","abb","baa","acc","caa","daa","dbb","dcc","abc"],
-- 181_3013
["aaa","bbb","ccc","abb","baa","acc","caa","daa","dbb","dcc","abc"],
-- 182_3013
["aaa","ddd","abb","baa","acc","caa","daa","dbb","dcc","abc"],
-- 183_3013
["aaa","bbb","ddd","abb","baa","acc","caa","daa","dbb","dcc","abc"],
-- 184_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","daa","dbb","dcc","abc"],
-- 185_3013
["aaa","bbb","abb","acc","daa","bcc","dbb","dcc","abc"],
-- 186_3013
["aaa","bbb","ccc","abb","acc","daa","bcc","dbb","dcc","abc"],
-- 187_3013
["aaa","bbb","ddd","abb","acc","daa","bcc","dbb","dcc","abc"],
-- 188_3013
["aaa","bbb","ccc","ddd","abb","acc","daa","bcc","dbb","dcc","abc"],
-- 189_3013
["aaa","bbb","abb","baa","acc","daa","bcc","dbb","dcc","abc"],
-- 190_3013
["aaa","bbb","ccc","abb","baa","acc","daa","bcc","dbb","dcc","abc"],
-- 191_3013
["aaa","bbb","ddd","abb","baa","acc","daa","bcc","dbb","dcc","abc"],
-- 192_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","daa","bcc","dbb","dcc","abc"],
-- 193_3013
["abb","caa","daa","bcc","dbb","dcc","abc"],
-- 194_3013
["aaa","abb","caa","daa","bcc","dbb","dcc","abc"],
-- 195_3013
["aaa","bbb","abb","caa","daa","bcc","dbb","dcc","abc"],
-- 196_3013
["aaa","bbb","ccc","abb","caa","daa","bcc","dbb","dcc","abc"],
-- 197_3013
["ddd","abb","caa","daa","bcc","dbb","dcc","abc"],
-- 198_3013
["aaa","ddd","abb","caa","daa","bcc","dbb","dcc","abc"],
-- 199_3013
["aaa","bbb","ddd","abb","caa","daa","bcc","dbb","dcc","abc"],
-- 200_3013
["aaa","bbb","ccc","ddd","abb","caa","daa","bcc","dbb","dcc","abc"],
-- 201_3013
["abb","baa","caa","daa","bcc","dbb","dcc","abc"],
-- 202_3013
["aaa","abb","baa","caa","daa","bcc","dbb","dcc","abc"],
-- 203_3013
["bbb","abb","baa","caa","daa","bcc","dbb","dcc","abc"],
-- 204_3013
["aaa","bbb","abb","baa","caa","daa","bcc","dbb","dcc","abc"],
-- 205_3013
["ccc","abb","baa","caa","daa","bcc","dbb","dcc","abc"],
-- 206_3013
["aaa","ccc","abb","baa","caa","daa","bcc","dbb","dcc","abc"],
-- 207_3013
["bbb","ccc","abb","baa","caa","daa","bcc","dbb","dcc","abc"],
-- 208_3013
["aaa","bbb","ccc","abb","baa","caa","daa","bcc","dbb","dcc","abc"],
-- 209_3013
["ddd","abb","baa","caa","daa","bcc","dbb","dcc","abc"],
-- 210_3013
["aaa","ddd","abb","baa","caa","daa","bcc","dbb","dcc","abc"],
-- 211_3013
["bbb","ddd","abb","baa","caa","daa","bcc","dbb","dcc","abc"],
-- 212_3013
["aaa","bbb","ddd","abb","baa","caa","daa","bcc","dbb","dcc","abc"],
-- 213_3013
["ccc","ddd","abb","baa","caa","daa","bcc","dbb","dcc","abc"],
-- 214_3013
["aaa","ccc","ddd","abb","baa","caa","daa","bcc","dbb","dcc","abc"],
-- 215_3013
["bbb","ccc","ddd","abb","baa","caa","daa","bcc","dbb","dcc","abc"],
-- 216_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","daa","bcc","dbb","dcc","abc"],
-- 217_3013
["bbb","baa","acc","caa","daa","bcc","dbb","dcc","abc"],
-- 218_3013
["aaa","bbb","baa","acc","caa","daa","bcc","dbb","dcc","abc"],
-- 219_3013
["aaa","bbb","ccc","baa","acc","caa","daa","bcc","dbb","dcc","abc"],
-- 220_3013
["bbb","ddd","baa","acc","caa","daa","bcc","dbb","dcc","abc"],
-- 221_3013
["aaa","bbb","ddd","baa","acc","caa","daa","bcc","dbb","dcc","abc"],
-- 222_3013
["aaa","bbb","ccc","ddd","baa","acc","caa","daa","bcc","dbb","dcc","abc"],
-- 223_3013
["abb","baa","acc","caa","daa","bcc","dbb","dcc","abc"],
-- 224_3013
["aaa","abb","baa","acc","caa","daa","bcc","dbb","dcc","abc"],
-- 225_3013
["bbb","abb","baa","acc","caa","daa","bcc","dbb","dcc","abc"],
-- 226_3013
["aaa","bbb","abb","baa","acc","caa","daa","bcc","dbb","dcc","abc"],
-- 227_3013
["ccc","abb","baa","acc","caa","daa","bcc","dbb","dcc","abc"],
-- 228_3013
["aaa","ccc","abb","baa","acc","caa","daa","bcc","dbb","dcc","abc"],
-- 229_3013
["bbb","ccc","abb","baa","acc","caa","daa","bcc","dbb","dcc","abc"],
-- 230_3013
["aaa","bbb","ccc","abb","baa","acc","caa","daa","bcc","dbb","dcc","abc"],
-- 231_3013
["ddd","abb","baa","acc","caa","daa","bcc","dbb","dcc","abc"],
-- 232_3013
["aaa","ddd","abb","baa","acc","caa","daa","bcc","dbb","dcc","abc"],
-- 233_3013
["bbb","ddd","abb","baa","acc","caa","daa","bcc","dbb","dcc","abc"],
-- 234_3013
["aaa","bbb","ddd","abb","baa","acc","caa","daa","bcc","dbb","dcc","abc"],
-- 235_3013
["ccc","ddd","abb","baa","acc","caa","daa","bcc","dbb","dcc","abc"],
-- 236_3013
["aaa","ccc","ddd","abb","baa","acc","caa","daa","bcc","dbb","dcc","abc"],
-- 237_3013
["bbb","ccc","ddd","abb","baa","acc","caa","daa","bcc","dbb","dcc","abc"],
-- 238_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","daa","bcc","dbb","dcc","abc"],
-- 239_3013
["abb","baa","acc","caa","daa","bcc","cbb","dbb","dcc","abc"],
-- 240_3013
["aaa","abb","baa","acc","caa","daa","bcc","cbb","dbb","dcc","abc"],
-- 241_3013
["aaa","bbb","abb","baa","acc","caa","daa","bcc","cbb","dbb","dcc","abc"],
-- 242_3013
["aaa","bbb","ccc","abb","baa","acc","caa","daa","bcc","cbb","dbb","dcc","abc"],
-- 243_3013
["ddd","abb","baa","acc","caa","daa","bcc","cbb","dbb","dcc","abc"],
-- 244_3013
["aaa","ddd","abb","baa","acc","caa","daa","bcc","cbb","dbb","dcc","abc"],
-- 245_3013
["aaa","bbb","ddd","abb","baa","acc","caa","daa","bcc","cbb","dbb","dcc","abc"],
-- 246_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","daa","bcc","cbb","dbb","dcc","abc"],
-- 247_3013
["abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc"],
-- 248_3013
["aaa","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc"],
-- 249_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc"],
-- 250_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc"],
-- 251_3013
["ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc"],
-- 252_3013
["aaa","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc"],
-- 253_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc"],
-- 254_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc"],
-- 255_3013
["daa","dbb","cdd","abc","abd"],
-- 256_3013
["ddd","daa","dbb","cdd","abc","abd"],
-- 257_3013
["aaa","abb","daa","dbb","cdd","abc","abd"],
-- 258_3013
["aaa","ddd","abb","daa","dbb","cdd","abc","abd"],
-- 259_3013
["aaa","bbb","abb","baa","daa","dbb","cdd","abc","abd"],
-- 260_3013
["aaa","bbb","ddd","abb","baa","daa","dbb","cdd","abc","abd"],
-- 261_3013
["ccc","caa","daa","dbb","cdd","abc","abd"],
-- 262_3013
["ccc","ddd","caa","daa","dbb","cdd","abc","abd"],
-- 263_3013
["aaa","bbb","ccc","baa","caa","daa","dbb","cdd","abc","abd"],
-- 264_3013
["aaa","bbb","ccc","ddd","baa","caa","daa","dbb","cdd","abc","abd"],
-- 265_3013
["aaa","ccc","abb","baa","caa","daa","dbb","cdd","abc","abd"],
-- 266_3013
["aaa","bbb","ccc","abb","baa","caa","daa","dbb","cdd","abc","abd"],
-- 267_3013
["aaa","ccc","ddd","abb","baa","caa","daa","dbb","cdd","abc","abd"],
-- 268_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","daa","dbb","cdd","abc","abd"],
-- 269_3013
["ccc","caa","daa","cbb","dbb","cdd","abc","abd"],
-- 270_3013
["ccc","ddd","caa","daa","cbb","dbb","cdd","abc","abd"],
-- 271_3013
["aaa","ccc","abb","caa","daa","cbb","dbb","cdd","abc","abd"],
-- 272_3013
["aaa","bbb","ccc","abb","caa","daa","cbb","dbb","cdd","abc","abd"],
-- 273_3013
["aaa","ccc","ddd","abb","caa","daa","cbb","dbb","cdd","abc","abd"],
-- 274_3013
["aaa","bbb","ccc","ddd","abb","caa","daa","cbb","dbb","cdd","abc","abd"],
-- 275_3013
["ccc","abb","baa","caa","daa","cbb","dbb","cdd","abc","abd"],
-- 276_3013
["aaa","ccc","abb","baa","caa","daa","cbb","dbb","cdd","abc","abd"],
-- 277_3013
["aaa","bbb","ccc","abb","baa","caa","daa","cbb","dbb","cdd","abc","abd"],
-- 278_3013
["ccc","ddd","abb","baa","caa","daa","cbb","dbb","cdd","abc","abd"],
-- 279_3013
["aaa","ccc","ddd","abb","baa","caa","daa","cbb","dbb","cdd","abc","abd"],
-- 280_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","daa","cbb","dbb","cdd","abc","abd"],
-- 281_3013
["add","daa","bdd","dbb","cdd","abc","abd"],
-- 282_3013
["ddd","add","daa","bdd","dbb","cdd","abc","abd"],
-- 283_3013
["aaa","abb","add","daa","bdd","dbb","cdd","abc","abd"],
-- 284_3013
["aaa","ddd","abb","add","daa","bdd","dbb","cdd","abc","abd"],
-- 285_3013
["aaa","bbb","abb","baa","add","daa","bdd","dbb","cdd","abc","abd"],
-- 286_3013
["aaa","bbb","ddd","abb","baa","add","daa","bdd","dbb","cdd","abc","abd"],
-- 287_3013
["ccc","caa","add","daa","bdd","dbb","cdd","abc","abd"],
-- 288_3013
["ccc","ddd","caa","add","daa","bdd","dbb","cdd","abc","abd"],
-- 289_3013
["aaa","bbb","ccc","baa","caa","add","daa","bdd","dbb","cdd","abc","abd"],
-- 290_3013
["aaa","bbb","ccc","ddd","baa","caa","add","daa","bdd","dbb","cdd","abc","abd"],
-- 291_3013
["aaa","ccc","abb","baa","caa","add","daa","bdd","dbb","cdd","abc","abd"],
-- 292_3013
["aaa","bbb","ccc","abb","baa","caa","add","daa","bdd","dbb","cdd","abc","abd"],
-- 293_3013
["aaa","ccc","ddd","abb","baa","caa","add","daa","bdd","dbb","cdd","abc","abd"],
-- 294_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","add","daa","bdd","dbb","cdd","abc","abd"],
-- 295_3013
["ccc","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd"],
-- 296_3013
["ccc","ddd","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd"],
-- 297_3013
["aaa","ccc","abb","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd"],
-- 298_3013
["aaa","bbb","ccc","abb","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd"],
-- 299_3013
["aaa","ccc","ddd","abb","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd"],
-- 300_3013
["aaa","bbb","ccc","ddd","abb","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd"],
-- 301_3013
["ccc","abb","baa","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd"],
-- 302_3013
["aaa","ccc","abb","baa","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd"],
-- 303_3013
["aaa","bbb","ccc","abb","baa","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd"],
-- 304_3013
["ccc","ddd","abb","baa","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd"],
-- 305_3013
["aaa","ccc","ddd","abb","baa","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd"],
-- 306_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd"],
-- 307_3013
["caa","daa","cbb","cdd","dcc","abc","abd"],
-- 308_3013
["ccc","caa","daa","cbb","cdd","dcc","abc","abd"],
-- 309_3013
["ddd","caa","daa","cbb","cdd","dcc","abc","abd"],
-- 310_3013
["ccc","ddd","caa","daa","cbb","cdd","dcc","abc","abd"],
-- 311_3013
["aaa","bbb","baa","caa","daa","cbb","cdd","dcc","abc","abd"],
-- 312_3013
["aaa","bbb","ccc","baa","caa","daa","cbb","cdd","dcc","abc","abd"],
-- 313_3013
["aaa","bbb","ddd","baa","caa","daa","cbb","cdd","dcc","abc","abd"],
-- 314_3013
["aaa","bbb","ccc","ddd","baa","caa","daa","cbb","cdd","dcc","abc","abd"],
-- 315_3013
["aaa","abb","baa","caa","daa","cbb","cdd","dcc","abc","abd"],
-- 316_3013
["aaa","bbb","abb","baa","caa","daa","cbb","cdd","dcc","abc","abd"],
-- 317_3013
["aaa","ccc","abb","baa","caa","daa","cbb","cdd","dcc","abc","abd"],
-- 318_3013
["aaa","bbb","ccc","abb","baa","caa","daa","cbb","cdd","dcc","abc","abd"],
-- 319_3013
["aaa","ddd","abb","baa","caa","daa","cbb","cdd","dcc","abc","abd"],
-- 320_3013
["aaa","bbb","ddd","abb","baa","caa","daa","cbb","cdd","dcc","abc","abd"],
-- 321_3013
["aaa","ccc","ddd","abb","baa","caa","daa","cbb","cdd","dcc","abc","abd"],
-- 322_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","daa","cbb","cdd","dcc","abc","abd"],
-- 323_3013
["aaa","bbb","acc","caa","add","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 324_3013
["aaa","bbb","ccc","acc","caa","add","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 325_3013
["aaa","bbb","ddd","acc","caa","add","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 326_3013
["aaa","bbb","ccc","ddd","acc","caa","add","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 327_3013
["aaa","bbb","abb","acc","caa","add","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 328_3013
["aaa","bbb","ccc","abb","acc","caa","add","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 329_3013
["aaa","bbb","ddd","abb","acc","caa","add","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 330_3013
["aaa","bbb","ccc","ddd","abb","acc","caa","add","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 331_3013
["aaa","bbb","abb","baa","acc","caa","add","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 332_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 333_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 334_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 335_3013
["bbb","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 336_3013
["aaa","bbb","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 337_3013
["bbb","ccc","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 338_3013
["aaa","bbb","ccc","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 339_3013
["bbb","ddd","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 340_3013
["aaa","bbb","ddd","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 341_3013
["bbb","ccc","ddd","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 342_3013
["aaa","bbb","ccc","ddd","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 343_3013
["abb","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 344_3013
["aaa","abb","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 345_3013
["bbb","abb","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 346_3013
["aaa","bbb","abb","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 347_3013
["ccc","abb","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 348_3013
["aaa","ccc","abb","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 349_3013
["bbb","ccc","abb","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 350_3013
["aaa","bbb","ccc","abb","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 351_3013
["ddd","abb","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 352_3013
["aaa","ddd","abb","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 353_3013
["bbb","ddd","abb","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 354_3013
["aaa","bbb","ddd","abb","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 355_3013
["ccc","ddd","abb","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 356_3013
["aaa","ccc","ddd","abb","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 357_3013
["bbb","ccc","ddd","abb","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 358_3013
["aaa","bbb","ccc","ddd","abb","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 359_3013
["bbb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 360_3013
["aaa","bbb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 361_3013
["bbb","ccc","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 362_3013
["aaa","bbb","ccc","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 363_3013
["bbb","ddd","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 364_3013
["aaa","bbb","ddd","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 365_3013
["bbb","ccc","ddd","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 366_3013
["aaa","bbb","ccc","ddd","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 367_3013
["abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 368_3013
["aaa","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 369_3013
["bbb","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 370_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 371_3013
["ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 372_3013
["aaa","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 373_3013
["bbb","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 374_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 375_3013
["ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 376_3013
["aaa","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 377_3013
["bbb","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 378_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 379_3013
["ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 380_3013
["aaa","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 381_3013
["bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 382_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","dcc","abc","abd"],
-- 383_3013
["caa","daa","cbb","dbb","cdd","dcc","abc","abd"],
-- 384_3013
["ccc","caa","daa","cbb","dbb","cdd","dcc","abc","abd"],
-- 385_3013
["ccc","ddd","caa","daa","cbb","dbb","cdd","dcc","abc","abd"],
-- 386_3013
["aaa","abb","caa","daa","cbb","dbb","cdd","dcc","abc","abd"],
-- 387_3013
["aaa","bbb","abb","caa","daa","cbb","dbb","cdd","dcc","abc","abd"],
-- 388_3013
["aaa","ccc","abb","caa","daa","cbb","dbb","cdd","dcc","abc","abd"],
-- 389_3013
["aaa","bbb","ccc","abb","caa","daa","cbb","dbb","cdd","dcc","abc","abd"],
-- 390_3013
["aaa","ccc","ddd","abb","caa","daa","cbb","dbb","cdd","dcc","abc","abd"],
-- 391_3013
["aaa","bbb","ccc","ddd","abb","caa","daa","cbb","dbb","cdd","dcc","abc","abd"],
-- 392_3013
["abb","baa","caa","daa","cbb","dbb","cdd","dcc","abc","abd"],
-- 393_3013
["aaa","abb","baa","caa","daa","cbb","dbb","cdd","dcc","abc","abd"],
-- 394_3013
["aaa","bbb","abb","baa","caa","daa","cbb","dbb","cdd","dcc","abc","abd"],
-- 395_3013
["ccc","abb","baa","caa","daa","cbb","dbb","cdd","dcc","abc","abd"],
-- 396_3013
["aaa","ccc","abb","baa","caa","daa","cbb","dbb","cdd","dcc","abc","abd"],
-- 397_3013
["aaa","bbb","ccc","abb","baa","caa","daa","cbb","dbb","cdd","dcc","abc","abd"],
-- 398_3013
["ccc","ddd","abb","baa","caa","daa","cbb","dbb","cdd","dcc","abc","abd"],
-- 399_3013
["aaa","ccc","ddd","abb","baa","caa","daa","cbb","dbb","cdd","dcc","abc","abd"],
-- 400_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","daa","cbb","dbb","cdd","dcc","abc","abd"],
-- 401_3013
["acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd"],
-- 402_3013
["aaa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd"],
-- 403_3013
["aaa","bbb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd"],
-- 404_3013
["ccc","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd"],
-- 405_3013
["aaa","ccc","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd"],
-- 406_3013
["aaa","bbb","ccc","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd"],
-- 407_3013
["ccc","ddd","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd"],
-- 408_3013
["aaa","ccc","ddd","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd"],
-- 409_3013
["aaa","bbb","ccc","ddd","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd"],
-- 410_3013
["abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd"],
-- 411_3013
["aaa","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd"],
-- 412_3013
["bbb","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd"],
-- 413_3013
["aaa","bbb","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd"],
-- 414_3013
["ccc","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd"],
-- 415_3013
["aaa","ccc","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd"],
-- 416_3013
["bbb","ccc","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd"],
-- 417_3013
["aaa","bbb","ccc","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd"],
-- 418_3013
["ccc","ddd","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd"],
-- 419_3013
["aaa","ccc","ddd","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd"],
-- 420_3013
["bbb","ccc","ddd","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd"],
-- 421_3013
["aaa","bbb","ccc","ddd","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd"],
-- 422_3013
["abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd"],
-- 423_3013
["aaa","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd"],
-- 424_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd"],
-- 425_3013
["ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd"],
-- 426_3013
["aaa","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd"],
-- 427_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd"],
-- 428_3013
["ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd"],
-- 429_3013
["aaa","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd"],
-- 430_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd"],
-- 431_3013
["aaa","abb","acc","add","abc","abd","acd"],
-- 432_3013
["aaa","abb","baa","acc","caa","add","daa","abc","abd","acd"],
-- 433_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","abc","abd","acd"],
-- 434_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","abc","abd","acd"],
-- 435_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","abc","abd","acd"],
-- 436_3013
["aaa","abb","baa","acc","caa","add","daa","bcc","abc","abd","acd"],
-- 437_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","bcc","abc","abd","acd"],
-- 438_3013
["aaa","ccc","abb","baa","acc","caa","add","daa","bcc","abc","abd","acd"],
-- 439_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","bcc","abc","abd","acd"],
-- 440_3013
["aaa","ddd","abb","baa","acc","caa","add","daa","bcc","abc","abd","acd"],
-- 441_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","daa","bcc","abc","abd","acd"],
-- 442_3013
["aaa","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","abc","abd","acd"],
-- 443_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","abc","abd","acd"],
-- 444_3013
["aaa","abb","baa","acc","caa","add","daa","bcc","cbb","abc","abd","acd"],
-- 445_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","bcc","cbb","abc","abd","acd"],
-- 446_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","abc","abd","acd"],
-- 447_3013
["aaa","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","abc","abd","acd"],
-- 448_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","abc","abd","acd"],
-- 449_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","abc","abd","acd"],
-- 450_3013
["aaa","abb","baa","acc","caa","add","daa","bcc","bdd","abc","abd","acd"],
-- 451_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","bcc","bdd","abc","abd","acd"],
-- 452_3013
["aaa","ccc","abb","baa","acc","caa","add","daa","bcc","bdd","abc","abd","acd"],
-- 453_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","bcc","bdd","abc","abd","acd"],
-- 454_3013
["aaa","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","bdd","abc","abd","acd"],
-- 455_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","bdd","abc","abd","acd"],
-- 456_3013
["aaa","abb","baa","acc","caa","daa","cbb","bdd","abc","abd","acd"],
-- 457_3013
["aaa","bbb","abb","baa","acc","caa","daa","cbb","bdd","abc","abd","acd"],
-- 458_3013
["aaa","ccc","abb","baa","acc","caa","daa","cbb","bdd","abc","abd","acd"],
-- 459_3013
["aaa","bbb","ccc","abb","baa","acc","caa","daa","cbb","bdd","abc","abd","acd"],
-- 460_3013
["aaa","ddd","abb","baa","acc","caa","daa","cbb","bdd","abc","abd","acd"],
-- 461_3013
["aaa","bbb","ddd","abb","baa","acc","caa","daa","cbb","bdd","abc","abd","acd"],
-- 462_3013
["aaa","ccc","ddd","abb","baa","acc","caa","daa","cbb","bdd","abc","abd","acd"],
-- 463_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","daa","cbb","bdd","abc","abd","acd"],
-- 464_3013
["aaa","abb","baa","acc","caa","add","daa","cbb","bdd","abc","abd","acd"],
-- 465_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","cbb","bdd","abc","abd","acd"],
-- 466_3013
["aaa","ccc","abb","baa","acc","caa","add","daa","cbb","bdd","abc","abd","acd"],
-- 467_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","cbb","bdd","abc","abd","acd"],
-- 468_3013
["aaa","ddd","abb","baa","acc","caa","add","daa","cbb","bdd","abc","abd","acd"],
-- 469_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","daa","cbb","bdd","abc","abd","acd"],
-- 470_3013
["aaa","ccc","ddd","abb","baa","acc","caa","add","daa","cbb","bdd","abc","abd","acd"],
-- 471_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","cbb","bdd","abc","abd","acd"],
-- 472_3013
["aaa","abb","baa","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd"],
-- 473_3013
["aaa","bbb","abb","baa","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd"],
-- 474_3013
["aaa","ccc","abb","baa","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd"],
-- 475_3013
["aaa","bbb","ccc","abb","baa","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd"],
-- 476_3013
["aaa","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd"],
-- 477_3013
["aaa","bbb","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd"],
-- 478_3013
["aaa","ccc","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd"],
-- 479_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd"],
-- 480_3013
["aaa","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd"],
-- 481_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd"],
-- 482_3013
["aaa","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd"],
-- 483_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd"],
-- 484_3013
["aaa","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd"],
-- 485_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd"],
-- 486_3013
["aaa","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd"],
-- 487_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd"],
-- 488_3013
["aaa","abb","baa","acc","add","cbb","dbb","abc","abd","acd"],
-- 489_3013
["aaa","bbb","abb","baa","acc","add","cbb","dbb","abc","abd","acd"],
-- 490_3013
["aaa","abb","baa","acc","caa","add","daa","cbb","dbb","abc","abd","acd"],
-- 491_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","cbb","dbb","abc","abd","acd"],
-- 492_3013
["aaa","ccc","abb","baa","acc","caa","add","daa","cbb","dbb","abc","abd","acd"],
-- 493_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","cbb","dbb","abc","abd","acd"],
-- 494_3013
["aaa","ccc","ddd","abb","baa","acc","caa","add","daa","cbb","dbb","abc","abd","acd"],
-- 495_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","cbb","dbb","abc","abd","acd"],
-- 496_3013
["aaa","abb","baa","caa","add","daa","bcc","cbb","dbb","abc","abd","acd"],
-- 497_3013
["aaa","bbb","abb","baa","caa","add","daa","bcc","cbb","dbb","abc","abd","acd"],
-- 498_3013
["aaa","ccc","abb","baa","caa","add","daa","bcc","cbb","dbb","abc","abd","acd"],
-- 499_3013
["aaa","bbb","ccc","abb","baa","caa","add","daa","bcc","cbb","dbb","abc","abd","acd"],
-- 500_3013
["aaa","ddd","abb","baa","caa","add","daa","bcc","cbb","dbb","abc","abd","acd"],
-- 501_3013
["aaa","bbb","ddd","abb","baa","caa","add","daa","bcc","cbb","dbb","abc","abd","acd"],
-- 502_3013
["aaa","ccc","ddd","abb","baa","caa","add","daa","bcc","cbb","dbb","abc","abd","acd"],
-- 503_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","add","daa","bcc","cbb","dbb","abc","abd","acd"],
-- 504_3013
["aaa","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd"],
-- 505_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd"],
-- 506_3013
["aaa","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd"],
-- 507_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd"],
-- 508_3013
["aaa","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd"],
-- 509_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd"],
-- 510_3013
["aaa","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd"],
-- 511_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd"],
-- 512_3013
["aaa","abb","baa","caa","daa","bcc","cbb","bdd","dbb","abc","abd","acd"],
-- 513_3013
["aaa","bbb","abb","baa","caa","daa","bcc","cbb","bdd","dbb","abc","abd","acd"],
-- 514_3013
["aaa","ccc","abb","baa","caa","daa","bcc","cbb","bdd","dbb","abc","abd","acd"],
-- 515_3013
["aaa","bbb","ccc","abb","baa","caa","daa","bcc","cbb","bdd","dbb","abc","abd","acd"],
-- 516_3013
["aaa","ccc","ddd","abb","baa","caa","daa","bcc","cbb","bdd","dbb","abc","abd","acd"],
-- 517_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","daa","bcc","cbb","bdd","dbb","abc","abd","acd"],
-- 518_3013
["aaa","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","abc","abd","acd"],
-- 519_3013
["aaa","bbb","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","abc","abd","acd"],
-- 520_3013
["aaa","ccc","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","abc","abd","acd"],
-- 521_3013
["aaa","bbb","ccc","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","abc","abd","acd"],
-- 522_3013
["aaa","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","abc","abd","acd"],
-- 523_3013
["aaa","bbb","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","abc","abd","acd"],
-- 524_3013
["aaa","ccc","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","abc","abd","acd"],
-- 525_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","abc","abd","acd"],
-- 526_3013
["aaa","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","abc","abd","acd"],
-- 527_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","abc","abd","acd"],
-- 528_3013
["aaa","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","abc","abd","acd"],
-- 529_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","abc","abd","acd"],
-- 530_3013
["aaa","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","abc","abd","acd"],
-- 531_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","abc","abd","acd"],
-- 532_3013
["aaa","bbb","abb","acc","add","bcc","bdd","cdd","abc","abd","acd"],
-- 533_3013
["aaa","bbb","ccc","abb","acc","add","bcc","bdd","cdd","abc","abd","acd"],
-- 534_3013
["aaa","bbb","ddd","abb","acc","add","bcc","bdd","cdd","abc","abd","acd"],
-- 535_3013
["aaa","bbb","ccc","ddd","abb","acc","add","bcc","bdd","cdd","abc","abd","acd"],
-- 536_3013
["aaa","bbb","abb","baa","acc","add","bcc","bdd","cdd","abc","abd","acd"],
-- 537_3013
["aaa","bbb","ccc","abb","baa","acc","add","bcc","bdd","cdd","abc","abd","acd"],
-- 538_3013
["aaa","bbb","ddd","abb","baa","acc","add","bcc","bdd","cdd","abc","abd","acd"],
-- 539_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","add","bcc","bdd","cdd","abc","abd","acd"],
-- 540_3013
["aaa","bbb","abb","acc","caa","add","bcc","bdd","cdd","abc","abd","acd"],
-- 541_3013
["aaa","bbb","ccc","abb","acc","caa","add","bcc","bdd","cdd","abc","abd","acd"],
-- 542_3013
["aaa","bbb","ddd","abb","acc","caa","add","bcc","bdd","cdd","abc","abd","acd"],
-- 543_3013
["aaa","bbb","ccc","ddd","abb","acc","caa","add","bcc","bdd","cdd","abc","abd","acd"],
-- 544_3013
["aaa","bbb","abb","baa","acc","caa","add","bcc","bdd","cdd","abc","abd","acd"],
-- 545_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","bcc","bdd","cdd","abc","abd","acd"],
-- 546_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","bcc","bdd","cdd","abc","abd","acd"],
-- 547_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","bcc","bdd","cdd","abc","abd","acd"],
-- 548_3013
["aaa","bbb","abb","acc","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 549_3013
["aaa","bbb","ccc","abb","acc","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 550_3013
["aaa","bbb","ddd","abb","acc","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 551_3013
["aaa","bbb","ccc","ddd","abb","acc","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 552_3013
["aaa","bbb","abb","baa","acc","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 553_3013
["aaa","bbb","ccc","abb","baa","acc","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 554_3013
["aaa","bbb","ddd","abb","baa","acc","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 555_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 556_3013
["abb","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 557_3013
["aaa","abb","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 558_3013
["bbb","abb","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 559_3013
["aaa","bbb","abb","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 560_3013
["ccc","abb","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 561_3013
["aaa","ccc","abb","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 562_3013
["bbb","ccc","abb","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 563_3013
["aaa","bbb","ccc","abb","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 564_3013
["ddd","abb","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 565_3013
["aaa","ddd","abb","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 566_3013
["bbb","ddd","abb","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 567_3013
["aaa","bbb","ddd","abb","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 568_3013
["ccc","ddd","abb","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 569_3013
["aaa","ccc","ddd","abb","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 570_3013
["bbb","ccc","ddd","abb","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 571_3013
["aaa","bbb","ccc","ddd","abb","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 572_3013
["abb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 573_3013
["aaa","abb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 574_3013
["bbb","abb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 575_3013
["aaa","bbb","abb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 576_3013
["ccc","abb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 577_3013
["aaa","ccc","abb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 578_3013
["bbb","ccc","abb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 579_3013
["aaa","bbb","ccc","abb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 580_3013
["ddd","abb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 581_3013
["aaa","ddd","abb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 582_3013
["bbb","ddd","abb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 583_3013
["aaa","bbb","ddd","abb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 584_3013
["ccc","ddd","abb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 585_3013
["aaa","ccc","ddd","abb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 586_3013
["bbb","ccc","ddd","abb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 587_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 588_3013
["aaa","bbb","abb","acc","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 589_3013
["aaa","bbb","ccc","abb","acc","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 590_3013
["aaa","bbb","ddd","abb","acc","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 591_3013
["aaa","bbb","ccc","ddd","abb","acc","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 592_3013
["aaa","bbb","abb","baa","acc","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 593_3013
["aaa","bbb","ccc","abb","baa","acc","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 594_3013
["aaa","bbb","ddd","abb","baa","acc","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 595_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 596_3013
["abb","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 597_3013
["aaa","abb","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 598_3013
["bbb","abb","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 599_3013
["aaa","bbb","abb","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 600_3013
["ccc","abb","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 601_3013
["aaa","ccc","abb","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 602_3013
["bbb","ccc","abb","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 603_3013
["aaa","bbb","ccc","abb","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 604_3013
["ddd","abb","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 605_3013
["aaa","ddd","abb","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 606_3013
["bbb","ddd","abb","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 607_3013
["aaa","bbb","ddd","abb","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 608_3013
["ccc","ddd","abb","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 609_3013
["aaa","ccc","ddd","abb","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 610_3013
["bbb","ccc","ddd","abb","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 611_3013
["aaa","bbb","ccc","ddd","abb","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 612_3013
["abb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 613_3013
["aaa","abb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 614_3013
["bbb","abb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 615_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 616_3013
["ccc","abb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 617_3013
["aaa","ccc","abb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 618_3013
["bbb","ccc","abb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 619_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 620_3013
["ddd","abb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 621_3013
["aaa","ddd","abb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 622_3013
["bbb","ddd","abb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 623_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 624_3013
["ccc","ddd","abb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 625_3013
["aaa","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 626_3013
["bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 627_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd"],
-- 628_3013
["aaa","abb","acc","add","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 629_3013
["aaa","bbb","abb","acc","add","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 630_3013
["aaa","bbb","ccc","abb","acc","add","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 631_3013
["aaa","ddd","abb","acc","add","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 632_3013
["aaa","bbb","ddd","abb","acc","add","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 633_3013
["aaa","bbb","ccc","ddd","abb","acc","add","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 634_3013
["aaa","abb","baa","acc","add","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 635_3013
["aaa","bbb","abb","baa","acc","add","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 636_3013
["aaa","ccc","abb","baa","acc","add","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 637_3013
["aaa","bbb","ccc","abb","baa","acc","add","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 638_3013
["aaa","ddd","abb","baa","acc","add","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 639_3013
["aaa","bbb","ddd","abb","baa","acc","add","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 640_3013
["aaa","ccc","ddd","abb","baa","acc","add","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 641_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","add","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 642_3013
["aaa","abb","baa","acc","caa","add","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 643_3013
["aaa","bbb","abb","baa","acc","caa","add","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 644_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 645_3013
["aaa","ddd","abb","baa","acc","caa","add","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 646_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 647_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 648_3013
["aaa","abb","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 649_3013
["aaa","bbb","abb","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 650_3013
["aaa","bbb","ccc","abb","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 651_3013
["aaa","ddd","abb","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 652_3013
["aaa","bbb","ddd","abb","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 653_3013
["aaa","bbb","ccc","ddd","abb","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 654_3013
["abb","baa","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 655_3013
["aaa","abb","baa","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 656_3013
["bbb","abb","baa","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 657_3013
["aaa","bbb","abb","baa","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 658_3013
["ccc","abb","baa","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 659_3013
["aaa","ccc","abb","baa","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 660_3013
["bbb","ccc","abb","baa","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 661_3013
["aaa","bbb","ccc","abb","baa","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 662_3013
["ddd","abb","baa","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 663_3013
["aaa","ddd","abb","baa","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 664_3013
["bbb","ddd","abb","baa","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 665_3013
["aaa","bbb","ddd","abb","baa","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 666_3013
["ccc","ddd","abb","baa","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 667_3013
["aaa","ccc","ddd","abb","baa","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 668_3013
["bbb","ccc","ddd","abb","baa","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 669_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 670_3013
["abb","baa","acc","caa","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 671_3013
["aaa","abb","baa","acc","caa","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 672_3013
["bbb","abb","baa","acc","caa","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 673_3013
["aaa","bbb","abb","baa","acc","caa","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 674_3013
["bbb","ccc","abb","baa","acc","caa","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 675_3013
["aaa","bbb","ccc","abb","baa","acc","caa","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 676_3013
["ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 677_3013
["aaa","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 678_3013
["bbb","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 679_3013
["aaa","bbb","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 680_3013
["bbb","ccc","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 681_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 682_3013
["aaa","abb","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 683_3013
["aaa","bbb","abb","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 684_3013
["aaa","bbb","ccc","abb","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 685_3013
["aaa","ddd","abb","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 686_3013
["aaa","bbb","ddd","abb","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 687_3013
["aaa","bbb","ccc","ddd","abb","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 688_3013
["abb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 689_3013
["aaa","abb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 690_3013
["bbb","abb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 691_3013
["aaa","bbb","abb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 692_3013
["ccc","abb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 693_3013
["aaa","ccc","abb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 694_3013
["bbb","ccc","abb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 695_3013
["aaa","bbb","ccc","abb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 696_3013
["ddd","abb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 697_3013
["aaa","ddd","abb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 698_3013
["bbb","ddd","abb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 699_3013
["aaa","bbb","ddd","abb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 700_3013
["ccc","ddd","abb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 701_3013
["aaa","ccc","ddd","abb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 702_3013
["bbb","ccc","ddd","abb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 703_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 704_3013
["abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 705_3013
["aaa","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 706_3013
["bbb","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 707_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 708_3013
["bbb","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 709_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 710_3013
["ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 711_3013
["aaa","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 712_3013
["bbb","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 713_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 714_3013
["bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 715_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd"],
-- 716_3013
["aaa","bcc","dbb","cdd","abc","abd","acd"],
-- 717_3013
["aaa","bbb","baa","bcc","dbb","cdd","abc","abd","acd"],
-- 718_3013
["aaa","bbb","abb","caa","bcc","dbb","cdd","abc","abd","acd"],
-- 719_3013
["aaa","bbb","ccc","abb","caa","bcc","dbb","cdd","abc","abd","acd"],
-- 720_3013
["aaa","bbb","ccc","baa","caa","bcc","dbb","cdd","abc","abd","acd"],
-- 721_3013
["aaa","bbb","abb","baa","caa","bcc","dbb","cdd","abc","abd","acd"],
-- 722_3013
["aaa","bbb","ccc","abb","baa","caa","bcc","dbb","cdd","abc","abd","acd"],
-- 723_3013
["aaa","abb","acc","add","bcc","dbb","cdd","abc","abd","acd"],
-- 724_3013
["aaa","bbb","abb","acc","add","bcc","dbb","cdd","abc","abd","acd"],
-- 725_3013
["aaa","bbb","ccc","abb","acc","add","bcc","dbb","cdd","abc","abd","acd"],
-- 726_3013
["aaa","bbb","ccc","ddd","abb","acc","add","bcc","dbb","cdd","abc","abd","acd"],
-- 727_3013
["aaa","baa","acc","add","bcc","dbb","cdd","abc","abd","acd"],
-- 728_3013
["aaa","bbb","baa","acc","add","bcc","dbb","cdd","abc","abd","acd"],
-- 729_3013
["aaa","ccc","baa","acc","add","bcc","dbb","cdd","abc","abd","acd"],
-- 730_3013
["aaa","bbb","ccc","baa","acc","add","bcc","dbb","cdd","abc","abd","acd"],
-- 731_3013
["aaa","ddd","baa","acc","add","bcc","dbb","cdd","abc","abd","acd"],
-- 732_3013
["aaa","bbb","ddd","baa","acc","add","bcc","dbb","cdd","abc","abd","acd"],
-- 733_3013
["aaa","ccc","ddd","baa","acc","add","bcc","dbb","cdd","abc","abd","acd"],
-- 734_3013
["aaa","bbb","ccc","ddd","baa","acc","add","bcc","dbb","cdd","abc","abd","acd"],
-- 735_3013
["aaa","abb","baa","acc","add","bcc","dbb","cdd","abc","abd","acd"],
-- 736_3013
["aaa","bbb","abb","baa","acc","add","bcc","dbb","cdd","abc","abd","acd"],
-- 737_3013
["aaa","ccc","abb","baa","acc","add","bcc","dbb","cdd","abc","abd","acd"],
-- 738_3013
["aaa","bbb","ccc","abb","baa","acc","add","bcc","dbb","cdd","abc","abd","acd"],
-- 739_3013
["aaa","ddd","abb","baa","acc","add","bcc","dbb","cdd","abc","abd","acd"],
-- 740_3013
["aaa","bbb","ddd","abb","baa","acc","add","bcc","dbb","cdd","abc","abd","acd"],
-- 741_3013
["aaa","ccc","ddd","abb","baa","acc","add","bcc","dbb","cdd","abc","abd","acd"],
-- 742_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","add","bcc","dbb","cdd","abc","abd","acd"],
-- 743_3013
["aaa","ccc","baa","caa","add","bcc","dbb","cdd","abc","abd","acd"],
-- 744_3013
["aaa","bbb","ccc","baa","caa","add","bcc","dbb","cdd","abc","abd","acd"],
-- 745_3013
["aaa","ccc","ddd","baa","caa","add","bcc","dbb","cdd","abc","abd","acd"],
-- 746_3013
["aaa","bbb","ccc","ddd","baa","caa","add","bcc","dbb","cdd","abc","abd","acd"],
-- 747_3013
["aaa","abb","baa","caa","add","bcc","dbb","cdd","abc","abd","acd"],
-- 748_3013
["aaa","bbb","abb","baa","caa","add","bcc","dbb","cdd","abc","abd","acd"],
-- 749_3013
["aaa","ccc","abb","baa","caa","add","bcc","dbb","cdd","abc","abd","acd"],
-- 750_3013
["aaa","bbb","ccc","abb","baa","caa","add","bcc","dbb","cdd","abc","abd","acd"],
-- 751_3013
["aaa","ddd","abb","baa","caa","add","bcc","dbb","cdd","abc","abd","acd"],
-- 752_3013
["aaa","bbb","ddd","abb","baa","caa","add","bcc","dbb","cdd","abc","abd","acd"],
-- 753_3013
["aaa","ccc","ddd","abb","baa","caa","add","bcc","dbb","cdd","abc","abd","acd"],
-- 754_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","add","bcc","dbb","cdd","abc","abd","acd"],
-- 755_3013
["aaa","baa","acc","caa","add","bcc","dbb","cdd","abc","abd","acd"],
-- 756_3013
["aaa","bbb","baa","acc","caa","add","bcc","dbb","cdd","abc","abd","acd"],
-- 757_3013
["aaa","ccc","baa","acc","caa","add","bcc","dbb","cdd","abc","abd","acd"],
-- 758_3013
["aaa","bbb","ccc","baa","acc","caa","add","bcc","dbb","cdd","abc","abd","acd"],
-- 759_3013
["aaa","ddd","baa","acc","caa","add","bcc","dbb","cdd","abc","abd","acd"],
-- 760_3013
["aaa","bbb","ddd","baa","acc","caa","add","bcc","dbb","cdd","abc","abd","acd"],
-- 761_3013
["aaa","ccc","ddd","baa","acc","caa","add","bcc","dbb","cdd","abc","abd","acd"],
-- 762_3013
["aaa","bbb","ccc","ddd","baa","acc","caa","add","bcc","dbb","cdd","abc","abd","acd"],
-- 763_3013
["aaa","abb","baa","acc","caa","add","bcc","dbb","cdd","abc","abd","acd"],
-- 764_3013
["aaa","bbb","abb","baa","acc","caa","add","bcc","dbb","cdd","abc","abd","acd"],
-- 765_3013
["aaa","ccc","abb","baa","acc","caa","add","bcc","dbb","cdd","abc","abd","acd"],
-- 766_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","bcc","dbb","cdd","abc","abd","acd"],
-- 767_3013
["aaa","ddd","abb","baa","acc","caa","add","bcc","dbb","cdd","abc","abd","acd"],
-- 768_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","bcc","dbb","cdd","abc","abd","acd"],
-- 769_3013
["aaa","ccc","ddd","abb","baa","acc","caa","add","bcc","dbb","cdd","abc","abd","acd"],
-- 770_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","bcc","dbb","cdd","abc","abd","acd"],
-- 771_3013
["bbb","ccc","ddd","baa","caa","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 772_3013
["aaa","bbb","ccc","ddd","baa","caa","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 773_3013
["ddd","abb","baa","caa","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 774_3013
["aaa","ddd","abb","baa","caa","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 775_3013
["bbb","ddd","abb","baa","caa","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 776_3013
["aaa","bbb","ddd","abb","baa","caa","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 777_3013
["ccc","ddd","abb","baa","caa","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 778_3013
["aaa","ccc","ddd","abb","baa","caa","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 779_3013
["bbb","ccc","ddd","abb","baa","caa","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 780_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 781_3013
["abb","baa","acc","caa","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 782_3013
["aaa","abb","baa","acc","caa","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 783_3013
["bbb","abb","baa","acc","caa","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 784_3013
["aaa","bbb","abb","baa","acc","caa","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 785_3013
["ccc","abb","baa","acc","caa","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 786_3013
["aaa","ccc","abb","baa","acc","caa","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 787_3013
["bbb","ccc","abb","baa","acc","caa","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 788_3013
["aaa","bbb","ccc","abb","baa","acc","caa","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 789_3013
["ddd","abb","baa","acc","caa","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 790_3013
["aaa","ddd","abb","baa","acc","caa","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 791_3013
["bbb","ddd","abb","baa","acc","caa","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 792_3013
["aaa","bbb","ddd","abb","baa","acc","caa","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 793_3013
["ccc","ddd","abb","baa","acc","caa","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 794_3013
["aaa","ccc","ddd","abb","baa","acc","caa","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 795_3013
["bbb","ccc","ddd","abb","baa","acc","caa","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 796_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 797_3013
["abb","baa","acc","caa","add","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 798_3013
["aaa","abb","baa","acc","caa","add","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 799_3013
["bbb","abb","baa","acc","caa","add","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 800_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 801_3013
["bbb","ccc","abb","baa","acc","caa","add","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 802_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 803_3013
["bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 804_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","dbb","cdd","abc","abd","acd"],
-- 805_3013
["aaa","abb","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 806_3013
["aaa","bbb","abb","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 807_3013
["aaa","ccc","abb","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 808_3013
["aaa","bbb","ccc","abb","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 809_3013
["aaa","ccc","baa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 810_3013
["aaa","bbb","ccc","baa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 811_3013
["aaa","abb","baa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 812_3013
["aaa","bbb","abb","baa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 813_3013
["aaa","ccc","abb","baa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 814_3013
["aaa","bbb","ccc","abb","baa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 815_3013
["aaa","abb","caa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 816_3013
["aaa","bbb","abb","caa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 817_3013
["aaa","ccc","abb","caa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 818_3013
["aaa","bbb","ccc","abb","caa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 819_3013
["aaa","ccc","baa","caa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 820_3013
["aaa","bbb","ccc","baa","caa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 821_3013
["aaa","abb","baa","caa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 822_3013
["aaa","bbb","abb","baa","caa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 823_3013
["aaa","ccc","abb","baa","caa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 824_3013
["aaa","bbb","ccc","abb","baa","caa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 825_3013
["aaa","ddd","abb","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 826_3013
["aaa","bbb","ddd","abb","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 827_3013
["aaa","ccc","ddd","abb","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 828_3013
["aaa","bbb","ccc","ddd","abb","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 829_3013
["aaa","ccc","ddd","baa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 830_3013
["aaa","bbb","ccc","ddd","baa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 831_3013
["aaa","ddd","abb","baa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 832_3013
["aaa","bbb","ddd","abb","baa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 833_3013
["aaa","ccc","ddd","abb","baa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 834_3013
["aaa","bbb","ccc","ddd","abb","baa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 835_3013
["aaa","abb","acc","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 836_3013
["aaa","bbb","abb","acc","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 837_3013
["aaa","ccc","abb","acc","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 838_3013
["aaa","bbb","ccc","abb","acc","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 839_3013
["aaa","ddd","abb","acc","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 840_3013
["aaa","bbb","ddd","abb","acc","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 841_3013
["aaa","ccc","ddd","abb","acc","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 842_3013
["aaa","bbb","ccc","ddd","abb","acc","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 843_3013
["aaa","baa","acc","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 844_3013
["aaa","bbb","baa","acc","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 845_3013
["aaa","ccc","baa","acc","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 846_3013
["aaa","bbb","ccc","baa","acc","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 847_3013
["aaa","ddd","baa","acc","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 848_3013
["aaa","bbb","ddd","baa","acc","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 849_3013
["aaa","ccc","ddd","baa","acc","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 850_3013
["aaa","bbb","ccc","ddd","baa","acc","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 851_3013
["aaa","abb","baa","acc","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 852_3013
["aaa","bbb","abb","baa","acc","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 853_3013
["aaa","ccc","abb","baa","acc","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 854_3013
["aaa","bbb","ccc","abb","baa","acc","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 855_3013
["aaa","ddd","abb","baa","acc","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 856_3013
["aaa","bbb","ddd","abb","baa","acc","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 857_3013
["aaa","ccc","ddd","abb","baa","acc","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 858_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 859_3013
["aaa","abb","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 860_3013
["aaa","bbb","abb","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 861_3013
["aaa","ccc","abb","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 862_3013
["aaa","bbb","ccc","abb","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 863_3013
["aaa","ddd","abb","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 864_3013
["aaa","bbb","ddd","abb","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 865_3013
["aaa","ccc","ddd","abb","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 866_3013
["aaa","bbb","ccc","ddd","abb","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 867_3013
["aaa","ccc","baa","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 868_3013
["aaa","bbb","ccc","baa","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 869_3013
["aaa","ccc","ddd","baa","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 870_3013
["aaa","bbb","ccc","ddd","baa","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 871_3013
["aaa","abb","baa","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 872_3013
["aaa","bbb","abb","baa","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 873_3013
["aaa","ccc","abb","baa","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 874_3013
["aaa","bbb","ccc","abb","baa","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 875_3013
["aaa","ddd","abb","baa","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 876_3013
["aaa","bbb","ddd","abb","baa","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 877_3013
["aaa","ccc","ddd","abb","baa","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 878_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 879_3013
["aaa","abb","acc","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 880_3013
["aaa","bbb","abb","acc","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 881_3013
["aaa","ccc","abb","acc","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 882_3013
["aaa","bbb","ccc","abb","acc","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 883_3013
["aaa","ddd","abb","acc","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 884_3013
["aaa","bbb","ddd","abb","acc","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 885_3013
["aaa","ccc","ddd","abb","acc","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 886_3013
["aaa","bbb","ccc","ddd","abb","acc","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 887_3013
["aaa","baa","acc","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 888_3013
["aaa","bbb","baa","acc","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 889_3013
["aaa","ccc","baa","acc","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 890_3013
["aaa","bbb","ccc","baa","acc","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 891_3013
["aaa","ddd","baa","acc","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 892_3013
["aaa","bbb","ddd","baa","acc","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 893_3013
["aaa","ccc","ddd","baa","acc","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 894_3013
["aaa","bbb","ccc","ddd","baa","acc","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 895_3013
["aaa","abb","baa","acc","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 896_3013
["aaa","bbb","abb","baa","acc","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 897_3013
["aaa","ccc","abb","baa","acc","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 898_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 899_3013
["aaa","ddd","abb","baa","acc","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 900_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 901_3013
["aaa","ccc","ddd","abb","baa","acc","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 902_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 903_3013
["aaa","ddd","abb","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 904_3013
["aaa","bbb","ddd","abb","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 905_3013
["aaa","ccc","ddd","abb","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 906_3013
["aaa","bbb","ccc","ddd","abb","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 907_3013
["ccc","ddd","baa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 908_3013
["aaa","ccc","ddd","baa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 909_3013
["bbb","ccc","ddd","baa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 910_3013
["aaa","bbb","ccc","ddd","baa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 911_3013
["ddd","abb","baa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 912_3013
["aaa","ddd","abb","baa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 913_3013
["bbb","ddd","abb","baa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 914_3013
["aaa","bbb","ddd","abb","baa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 915_3013
["ccc","ddd","abb","baa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 916_3013
["aaa","ccc","ddd","abb","baa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 917_3013
["bbb","ccc","ddd","abb","baa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 918_3013
["aaa","bbb","ccc","ddd","abb","baa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 919_3013
["aaa","abb","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 920_3013
["aaa","bbb","abb","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 921_3013
["aaa","ccc","abb","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 922_3013
["aaa","bbb","ccc","abb","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 923_3013
["aaa","ddd","abb","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 924_3013
["aaa","bbb","ddd","abb","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 925_3013
["aaa","ccc","ddd","abb","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 926_3013
["aaa","bbb","ccc","ddd","abb","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 927_3013
["baa","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 928_3013
["aaa","baa","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 929_3013
["bbb","baa","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 930_3013
["aaa","bbb","baa","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 931_3013
["ccc","baa","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 932_3013
["aaa","ccc","baa","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 933_3013
["bbb","ccc","baa","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 934_3013
["aaa","bbb","ccc","baa","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 935_3013
["ddd","baa","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 936_3013
["aaa","ddd","baa","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 937_3013
["bbb","ddd","baa","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 938_3013
["aaa","bbb","ddd","baa","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 939_3013
["ccc","ddd","baa","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 940_3013
["aaa","ccc","ddd","baa","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 941_3013
["bbb","ccc","ddd","baa","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 942_3013
["aaa","bbb","ccc","ddd","baa","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 943_3013
["abb","baa","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 944_3013
["aaa","abb","baa","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 945_3013
["bbb","abb","baa","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 946_3013
["aaa","bbb","abb","baa","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 947_3013
["ccc","abb","baa","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 948_3013
["aaa","ccc","abb","baa","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 949_3013
["bbb","ccc","abb","baa","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 950_3013
["aaa","bbb","ccc","abb","baa","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 951_3013
["ddd","abb","baa","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 952_3013
["aaa","ddd","abb","baa","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 953_3013
["bbb","ddd","abb","baa","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 954_3013
["aaa","bbb","ddd","abb","baa","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 955_3013
["ccc","ddd","abb","baa","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 956_3013
["aaa","ccc","ddd","abb","baa","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 957_3013
["bbb","ccc","ddd","abb","baa","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 958_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 959_3013
["aaa","ddd","abb","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 960_3013
["aaa","bbb","ddd","abb","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 961_3013
["aaa","ccc","ddd","abb","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 962_3013
["aaa","bbb","ccc","ddd","abb","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 963_3013
["ccc","ddd","baa","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 964_3013
["aaa","ccc","ddd","baa","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 965_3013
["bbb","ccc","ddd","baa","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 966_3013
["aaa","bbb","ccc","ddd","baa","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 967_3013
["ddd","abb","baa","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 968_3013
["aaa","ddd","abb","baa","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 969_3013
["bbb","ddd","abb","baa","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 970_3013
["aaa","bbb","ddd","abb","baa","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 971_3013
["ccc","ddd","abb","baa","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 972_3013
["aaa","ccc","ddd","abb","baa","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 973_3013
["bbb","ccc","ddd","abb","baa","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 974_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 975_3013
["aaa","abb","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 976_3013
["aaa","bbb","abb","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 977_3013
["aaa","ccc","abb","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 978_3013
["aaa","bbb","ccc","abb","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 979_3013
["aaa","ddd","abb","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 980_3013
["aaa","bbb","ddd","abb","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 981_3013
["aaa","ccc","ddd","abb","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 982_3013
["aaa","bbb","ccc","ddd","abb","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 983_3013
["baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 984_3013
["aaa","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 985_3013
["bbb","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 986_3013
["aaa","bbb","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 987_3013
["ccc","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 988_3013
["aaa","ccc","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 989_3013
["bbb","ccc","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 990_3013
["aaa","bbb","ccc","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 991_3013
["ddd","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 992_3013
["aaa","ddd","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 993_3013
["bbb","ddd","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 994_3013
["aaa","bbb","ddd","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 995_3013
["ccc","ddd","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 996_3013
["aaa","ccc","ddd","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 997_3013
["bbb","ccc","ddd","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 998_3013
["aaa","bbb","ccc","ddd","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 999_3013
["abb","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1000_3013
["aaa","abb","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1001_3013
["bbb","abb","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1002_3013
["aaa","bbb","abb","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1003_3013
["ccc","abb","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1004_3013
["aaa","ccc","abb","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1005_3013
["bbb","ccc","abb","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1006_3013
["aaa","bbb","ccc","abb","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1007_3013
["ddd","abb","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1008_3013
["aaa","ddd","abb","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1009_3013
["bbb","ddd","abb","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1010_3013
["aaa","bbb","ddd","abb","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1011_3013
["ccc","ddd","abb","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1012_3013
["aaa","ccc","ddd","abb","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1013_3013
["bbb","ccc","ddd","abb","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1014_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1015_3013
["aaa","ddd","abb","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1016_3013
["aaa","bbb","ddd","abb","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1017_3013
["aaa","ccc","ddd","abb","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1018_3013
["aaa","bbb","ccc","ddd","abb","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1019_3013
["ccc","ddd","baa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1020_3013
["aaa","ccc","ddd","baa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1021_3013
["bbb","ccc","ddd","baa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1022_3013
["aaa","bbb","ccc","ddd","baa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1023_3013
["ddd","abb","baa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1024_3013
["aaa","ddd","abb","baa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1025_3013
["bbb","ddd","abb","baa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1026_3013
["aaa","bbb","ddd","abb","baa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1027_3013
["ccc","ddd","abb","baa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1028_3013
["aaa","ccc","ddd","abb","baa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1029_3013
["bbb","ccc","ddd","abb","baa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1030_3013
["aaa","bbb","ccc","ddd","abb","baa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1031_3013
["aaa","abb","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1032_3013
["aaa","bbb","abb","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1033_3013
["aaa","ccc","abb","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1034_3013
["aaa","bbb","ccc","abb","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1035_3013
["aaa","ddd","abb","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1036_3013
["aaa","bbb","ddd","abb","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1037_3013
["aaa","ccc","ddd","abb","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1038_3013
["aaa","bbb","ccc","ddd","abb","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1039_3013
["baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1040_3013
["aaa","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1041_3013
["bbb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1042_3013
["aaa","bbb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1043_3013
["ccc","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1044_3013
["aaa","ccc","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1045_3013
["bbb","ccc","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1046_3013
["aaa","bbb","ccc","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1047_3013
["ddd","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1048_3013
["aaa","ddd","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1049_3013
["bbb","ddd","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1050_3013
["aaa","bbb","ddd","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1051_3013
["ccc","ddd","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1052_3013
["aaa","ccc","ddd","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1053_3013
["bbb","ccc","ddd","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1054_3013
["aaa","bbb","ccc","ddd","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1055_3013
["abb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1056_3013
["aaa","abb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1057_3013
["bbb","abb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1058_3013
["aaa","bbb","abb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1059_3013
["ccc","abb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1060_3013
["aaa","ccc","abb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1061_3013
["bbb","ccc","abb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1062_3013
["aaa","bbb","ccc","abb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1063_3013
["ddd","abb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1064_3013
["aaa","ddd","abb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1065_3013
["bbb","ddd","abb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1066_3013
["aaa","bbb","ddd","abb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1067_3013
["ccc","ddd","abb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1068_3013
["aaa","ccc","ddd","abb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1069_3013
["bbb","ccc","ddd","abb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1070_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1071_3013
["aaa","abb","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1072_3013
["aaa","bbb","abb","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1073_3013
["aaa","ccc","abb","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1074_3013
["aaa","bbb","ccc","abb","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1075_3013
["aaa","ddd","abb","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1076_3013
["aaa","bbb","ddd","abb","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1077_3013
["aaa","ccc","ddd","abb","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1078_3013
["aaa","bbb","ccc","ddd","abb","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1079_3013
["ccc","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1080_3013
["aaa","ccc","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1081_3013
["bbb","ccc","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1082_3013
["aaa","bbb","ccc","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1083_3013
["ccc","ddd","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1084_3013
["aaa","ccc","ddd","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1085_3013
["bbb","ccc","ddd","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1086_3013
["aaa","bbb","ccc","ddd","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1087_3013
["abb","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1088_3013
["aaa","abb","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1089_3013
["bbb","abb","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1090_3013
["aaa","bbb","abb","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1091_3013
["ccc","abb","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1092_3013
["aaa","ccc","abb","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1093_3013
["bbb","ccc","abb","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1094_3013
["aaa","bbb","ccc","abb","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1095_3013
["ddd","abb","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1096_3013
["aaa","ddd","abb","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1097_3013
["bbb","ddd","abb","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1098_3013
["aaa","bbb","ddd","abb","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1099_3013
["ccc","ddd","abb","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1100_3013
["aaa","ccc","ddd","abb","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1101_3013
["bbb","ccc","ddd","abb","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1102_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1103_3013
["aaa","abb","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1104_3013
["aaa","bbb","abb","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1105_3013
["aaa","ccc","abb","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1106_3013
["aaa","bbb","ccc","abb","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1107_3013
["aaa","ddd","abb","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1108_3013
["aaa","bbb","ddd","abb","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1109_3013
["aaa","ccc","ddd","abb","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1110_3013
["aaa","bbb","ccc","ddd","abb","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1111_3013
["baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1112_3013
["aaa","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1113_3013
["bbb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1114_3013
["aaa","bbb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1115_3013
["ccc","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1116_3013
["aaa","ccc","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1117_3013
["bbb","ccc","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1118_3013
["aaa","bbb","ccc","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1119_3013
["ddd","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1120_3013
["aaa","ddd","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1121_3013
["bbb","ddd","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1122_3013
["aaa","bbb","ddd","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1123_3013
["ccc","ddd","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1124_3013
["aaa","ccc","ddd","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1125_3013
["bbb","ccc","ddd","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1126_3013
["aaa","bbb","ccc","ddd","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1127_3013
["abb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1128_3013
["aaa","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1129_3013
["bbb","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1130_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1131_3013
["ccc","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1132_3013
["aaa","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1133_3013
["bbb","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1134_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1135_3013
["ddd","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1136_3013
["aaa","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1137_3013
["bbb","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1138_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1139_3013
["ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1140_3013
["aaa","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1141_3013
["bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1142_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd"],
-- 1143_3013
["aaa","ccc","abb","acc","add","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1144_3013
["aaa","bbb","ccc","abb","acc","add","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1145_3013
["aaa","bbb","ccc","ddd","abb","acc","add","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1146_3013
["aaa","ccc","baa","acc","add","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1147_3013
["aaa","bbb","ccc","baa","acc","add","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1148_3013
["aaa","ccc","ddd","baa","acc","add","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1149_3013
["aaa","bbb","ccc","ddd","baa","acc","add","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1150_3013
["aaa","ccc","abb","baa","acc","add","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1151_3013
["aaa","bbb","ccc","abb","baa","acc","add","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1152_3013
["aaa","ccc","ddd","abb","baa","acc","add","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1153_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","add","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1154_3013
["aaa","ccc","abb","acc","caa","add","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1155_3013
["aaa","bbb","ccc","abb","acc","caa","add","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1156_3013
["aaa","bbb","ccc","ddd","abb","acc","caa","add","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1157_3013
["aaa","ccc","baa","acc","caa","add","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1158_3013
["aaa","bbb","ccc","baa","acc","caa","add","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1159_3013
["aaa","ccc","ddd","baa","acc","caa","add","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1160_3013
["aaa","bbb","ccc","ddd","baa","acc","caa","add","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1161_3013
["aaa","ccc","abb","baa","acc","caa","add","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1162_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1163_3013
["aaa","ccc","ddd","abb","baa","acc","caa","add","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1164_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1165_3013
["baa","acc","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1166_3013
["aaa","baa","acc","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1167_3013
["bbb","baa","acc","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1168_3013
["aaa","bbb","baa","acc","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1169_3013
["ccc","baa","acc","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1170_3013
["aaa","ccc","baa","acc","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1171_3013
["bbb","ccc","baa","acc","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1172_3013
["aaa","bbb","ccc","baa","acc","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1173_3013
["bbb","ddd","baa","acc","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1174_3013
["aaa","bbb","ddd","baa","acc","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1175_3013
["bbb","ccc","ddd","baa","acc","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1176_3013
["aaa","bbb","ccc","ddd","baa","acc","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1177_3013
["abb","baa","acc","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1178_3013
["aaa","abb","baa","acc","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1179_3013
["bbb","abb","baa","acc","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1180_3013
["aaa","bbb","abb","baa","acc","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1181_3013
["ccc","abb","baa","acc","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1182_3013
["aaa","ccc","abb","baa","acc","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1183_3013
["bbb","ccc","abb","baa","acc","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1184_3013
["aaa","bbb","ccc","abb","baa","acc","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1185_3013
["ddd","abb","baa","acc","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1186_3013
["aaa","ddd","abb","baa","acc","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1187_3013
["bbb","ddd","abb","baa","acc","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1188_3013
["aaa","bbb","ddd","abb","baa","acc","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1189_3013
["ccc","ddd","abb","baa","acc","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1190_3013
["aaa","ccc","ddd","abb","baa","acc","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1191_3013
["bbb","ccc","ddd","abb","baa","acc","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1192_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1193_3013
["baa","acc","caa","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1194_3013
["aaa","baa","acc","caa","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1195_3013
["bbb","baa","acc","caa","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1196_3013
["aaa","bbb","baa","acc","caa","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1197_3013
["ccc","baa","acc","caa","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1198_3013
["aaa","ccc","baa","acc","caa","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1199_3013
["bbb","ccc","baa","acc","caa","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1200_3013
["aaa","bbb","ccc","baa","acc","caa","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1201_3013
["bbb","ddd","baa","acc","caa","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1202_3013
["aaa","bbb","ddd","baa","acc","caa","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1203_3013
["bbb","ccc","ddd","baa","acc","caa","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1204_3013
["aaa","bbb","ccc","ddd","baa","acc","caa","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1205_3013
["abb","baa","acc","caa","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1206_3013
["aaa","abb","baa","acc","caa","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1207_3013
["bbb","abb","baa","acc","caa","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1208_3013
["aaa","bbb","abb","baa","acc","caa","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1209_3013
["ccc","abb","baa","acc","caa","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1210_3013
["aaa","ccc","abb","baa","acc","caa","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1211_3013
["bbb","ccc","abb","baa","acc","caa","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1212_3013
["aaa","bbb","ccc","abb","baa","acc","caa","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1213_3013
["ddd","abb","baa","acc","caa","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1214_3013
["aaa","ddd","abb","baa","acc","caa","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1215_3013
["bbb","ddd","abb","baa","acc","caa","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1216_3013
["aaa","bbb","ddd","abb","baa","acc","caa","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1217_3013
["ccc","ddd","abb","baa","acc","caa","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1218_3013
["aaa","ccc","ddd","abb","baa","acc","caa","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1219_3013
["bbb","ccc","ddd","abb","baa","acc","caa","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1220_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1221_3013
["abb","baa","acc","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1222_3013
["aaa","abb","baa","acc","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1223_3013
["bbb","abb","baa","acc","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1224_3013
["aaa","bbb","abb","baa","acc","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1225_3013
["ccc","abb","baa","acc","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1226_3013
["aaa","ccc","abb","baa","acc","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1227_3013
["bbb","ccc","abb","baa","acc","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1228_3013
["aaa","bbb","ccc","abb","baa","acc","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1229_3013
["bbb","ddd","abb","baa","acc","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1230_3013
["aaa","bbb","ddd","abb","baa","acc","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1231_3013
["bbb","ccc","ddd","abb","baa","acc","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1232_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1233_3013
["abb","baa","acc","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1234_3013
["aaa","abb","baa","acc","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1235_3013
["bbb","abb","baa","acc","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1236_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1237_3013
["ccc","abb","baa","acc","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1238_3013
["aaa","ccc","abb","baa","acc","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1239_3013
["bbb","ccc","abb","baa","acc","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1240_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1241_3013
["bbb","ddd","abb","baa","acc","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1242_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1243_3013
["bbb","ccc","ddd","abb","baa","acc","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1244_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1245_3013
["aaa","ccc","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1246_3013
["aaa","bbb","ccc","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1247_3013
["aaa","ccc","ddd","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1248_3013
["aaa","bbb","ccc","ddd","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1249_3013
["aaa","abb","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1250_3013
["aaa","bbb","abb","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1251_3013
["aaa","ccc","abb","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1252_3013
["aaa","bbb","ccc","abb","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1253_3013
["aaa","ddd","abb","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1254_3013
["aaa","bbb","ddd","abb","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1255_3013
["aaa","ccc","ddd","abb","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1256_3013
["aaa","bbb","ccc","ddd","abb","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1257_3013
["aaa","ccc","baa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1258_3013
["aaa","bbb","ccc","baa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1259_3013
["aaa","ccc","ddd","baa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1260_3013
["aaa","bbb","ccc","ddd","baa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1261_3013
["aaa","abb","baa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1262_3013
["aaa","bbb","abb","baa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1263_3013
["aaa","ccc","abb","baa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1264_3013
["aaa","bbb","ccc","abb","baa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1265_3013
["aaa","ddd","abb","baa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1266_3013
["aaa","bbb","ddd","abb","baa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1267_3013
["aaa","ccc","ddd","abb","baa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1268_3013
["aaa","bbb","ccc","ddd","abb","baa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1269_3013
["aaa","ccc","acc","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1270_3013
["aaa","bbb","ccc","acc","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1271_3013
["aaa","ccc","ddd","acc","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1272_3013
["aaa","bbb","ccc","ddd","acc","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1273_3013
["aaa","abb","acc","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1274_3013
["aaa","bbb","abb","acc","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1275_3013
["aaa","ccc","abb","acc","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1276_3013
["aaa","bbb","ccc","abb","acc","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1277_3013
["aaa","ddd","abb","acc","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1278_3013
["aaa","bbb","ddd","abb","acc","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1279_3013
["aaa","ccc","ddd","abb","acc","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1280_3013
["aaa","bbb","ccc","ddd","abb","acc","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1281_3013
["aaa","baa","acc","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1282_3013
["aaa","bbb","baa","acc","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1283_3013
["aaa","ccc","baa","acc","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1284_3013
["aaa","bbb","ccc","baa","acc","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1285_3013
["aaa","ddd","baa","acc","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1286_3013
["aaa","bbb","ddd","baa","acc","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1287_3013
["aaa","ccc","ddd","baa","acc","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1288_3013
["aaa","bbb","ccc","ddd","baa","acc","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1289_3013
["aaa","abb","baa","acc","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1290_3013
["aaa","bbb","abb","baa","acc","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1291_3013
["aaa","ccc","abb","baa","acc","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1292_3013
["aaa","bbb","ccc","abb","baa","acc","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1293_3013
["aaa","ddd","abb","baa","acc","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1294_3013
["aaa","bbb","ddd","abb","baa","acc","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1295_3013
["aaa","ccc","ddd","abb","baa","acc","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1296_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1297_3013
["aaa","ccc","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1298_3013
["aaa","bbb","ccc","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1299_3013
["aaa","ccc","ddd","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1300_3013
["aaa","bbb","ccc","ddd","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1301_3013
["aaa","abb","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1302_3013
["aaa","bbb","abb","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1303_3013
["aaa","ccc","abb","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1304_3013
["aaa","bbb","ccc","abb","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1305_3013
["aaa","ddd","abb","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1306_3013
["aaa","bbb","ddd","abb","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1307_3013
["aaa","ccc","ddd","abb","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1308_3013
["aaa","bbb","ccc","ddd","abb","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1309_3013
["aaa","ccc","baa","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1310_3013
["aaa","bbb","ccc","baa","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1311_3013
["aaa","ccc","ddd","baa","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1312_3013
["aaa","bbb","ccc","ddd","baa","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1313_3013
["aaa","abb","baa","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1314_3013
["aaa","bbb","abb","baa","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1315_3013
["aaa","ccc","abb","baa","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1316_3013
["aaa","bbb","ccc","abb","baa","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1317_3013
["aaa","ddd","abb","baa","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1318_3013
["aaa","bbb","ddd","abb","baa","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1319_3013
["aaa","ccc","ddd","abb","baa","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1320_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1321_3013
["aaa","ccc","acc","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1322_3013
["aaa","bbb","ccc","acc","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1323_3013
["aaa","ccc","ddd","acc","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1324_3013
["aaa","bbb","ccc","ddd","acc","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1325_3013
["aaa","abb","acc","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1326_3013
["aaa","bbb","abb","acc","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1327_3013
["aaa","ccc","abb","acc","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1328_3013
["aaa","bbb","ccc","abb","acc","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1329_3013
["aaa","ddd","abb","acc","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1330_3013
["aaa","bbb","ddd","abb","acc","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1331_3013
["aaa","ccc","ddd","abb","acc","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1332_3013
["aaa","bbb","ccc","ddd","abb","acc","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1333_3013
["aaa","baa","acc","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1334_3013
["aaa","bbb","baa","acc","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1335_3013
["aaa","ccc","baa","acc","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1336_3013
["aaa","bbb","ccc","baa","acc","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1337_3013
["aaa","ddd","baa","acc","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1338_3013
["aaa","bbb","ddd","baa","acc","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1339_3013
["aaa","ccc","ddd","baa","acc","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1340_3013
["aaa","bbb","ccc","ddd","baa","acc","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1341_3013
["aaa","abb","baa","acc","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1342_3013
["aaa","bbb","abb","baa","acc","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1343_3013
["aaa","ccc","abb","baa","acc","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1344_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1345_3013
["aaa","ddd","abb","baa","acc","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1346_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1347_3013
["aaa","ccc","ddd","abb","baa","acc","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1348_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1349_3013
["aaa","ccc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1350_3013
["aaa","bbb","ccc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1351_3013
["aaa","ccc","ddd","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1352_3013
["aaa","bbb","ccc","ddd","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1353_3013
["aaa","abb","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1354_3013
["aaa","bbb","abb","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1355_3013
["aaa","ccc","abb","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1356_3013
["aaa","bbb","ccc","abb","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1357_3013
["aaa","ddd","abb","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1358_3013
["aaa","bbb","ddd","abb","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1359_3013
["aaa","ccc","ddd","abb","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1360_3013
["aaa","bbb","ccc","ddd","abb","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1361_3013
["ccc","baa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1362_3013
["aaa","ccc","baa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1363_3013
["bbb","ccc","baa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1364_3013
["aaa","bbb","ccc","baa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1365_3013
["ccc","ddd","baa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1366_3013
["aaa","ccc","ddd","baa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1367_3013
["bbb","ccc","ddd","baa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1368_3013
["aaa","bbb","ccc","ddd","baa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1369_3013
["abb","baa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1370_3013
["aaa","abb","baa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1371_3013
["bbb","abb","baa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1372_3013
["aaa","bbb","abb","baa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1373_3013
["ccc","abb","baa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1374_3013
["aaa","ccc","abb","baa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1375_3013
["bbb","ccc","abb","baa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1376_3013
["aaa","bbb","ccc","abb","baa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1377_3013
["ddd","abb","baa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1378_3013
["aaa","ddd","abb","baa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1379_3013
["bbb","ddd","abb","baa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1380_3013
["aaa","bbb","ddd","abb","baa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1381_3013
["ccc","ddd","abb","baa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1382_3013
["aaa","ccc","ddd","abb","baa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1383_3013
["bbb","ccc","ddd","abb","baa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1384_3013
["aaa","bbb","ccc","ddd","abb","baa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1385_3013
["aaa","ccc","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1386_3013
["aaa","bbb","ccc","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1387_3013
["aaa","ccc","ddd","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1388_3013
["aaa","bbb","ccc","ddd","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1389_3013
["aaa","abb","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1390_3013
["aaa","bbb","abb","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1391_3013
["aaa","ccc","abb","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1392_3013
["aaa","bbb","ccc","abb","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1393_3013
["aaa","ddd","abb","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1394_3013
["aaa","bbb","ddd","abb","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1395_3013
["aaa","ccc","ddd","abb","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1396_3013
["aaa","bbb","ccc","ddd","abb","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1397_3013
["baa","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1398_3013
["aaa","baa","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1399_3013
["bbb","baa","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1400_3013
["aaa","bbb","baa","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1401_3013
["ccc","baa","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1402_3013
["aaa","ccc","baa","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1403_3013
["bbb","ccc","baa","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1404_3013
["aaa","bbb","ccc","baa","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1405_3013
["ddd","baa","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1406_3013
["aaa","ddd","baa","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1407_3013
["bbb","ddd","baa","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1408_3013
["aaa","bbb","ddd","baa","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1409_3013
["ccc","ddd","baa","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1410_3013
["aaa","ccc","ddd","baa","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1411_3013
["bbb","ccc","ddd","baa","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1412_3013
["aaa","bbb","ccc","ddd","baa","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1413_3013
["abb","baa","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1414_3013
["aaa","abb","baa","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1415_3013
["bbb","abb","baa","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1416_3013
["aaa","bbb","abb","baa","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1417_3013
["ccc","abb","baa","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1418_3013
["aaa","ccc","abb","baa","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1419_3013
["bbb","ccc","abb","baa","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1420_3013
["aaa","bbb","ccc","abb","baa","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1421_3013
["ddd","abb","baa","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1422_3013
["aaa","ddd","abb","baa","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1423_3013
["bbb","ddd","abb","baa","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1424_3013
["aaa","bbb","ddd","abb","baa","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1425_3013
["ccc","ddd","abb","baa","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1426_3013
["aaa","ccc","ddd","abb","baa","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1427_3013
["bbb","ccc","ddd","abb","baa","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1428_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1429_3013
["ccc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1430_3013
["aaa","ccc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1431_3013
["bbb","ccc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1432_3013
["aaa","bbb","ccc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1433_3013
["ccc","ddd","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1434_3013
["aaa","ccc","ddd","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1435_3013
["bbb","ccc","ddd","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1436_3013
["aaa","bbb","ccc","ddd","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1437_3013
["abb","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1438_3013
["aaa","abb","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1439_3013
["bbb","abb","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1440_3013
["aaa","bbb","abb","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1441_3013
["ccc","abb","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1442_3013
["aaa","ccc","abb","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1443_3013
["bbb","ccc","abb","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1444_3013
["aaa","bbb","ccc","abb","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1445_3013
["ddd","abb","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1446_3013
["aaa","ddd","abb","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1447_3013
["bbb","ddd","abb","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1448_3013
["aaa","bbb","ddd","abb","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1449_3013
["ccc","ddd","abb","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1450_3013
["aaa","ccc","ddd","abb","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1451_3013
["bbb","ccc","ddd","abb","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1452_3013
["aaa","bbb","ccc","ddd","abb","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1453_3013
["ccc","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1454_3013
["aaa","ccc","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1455_3013
["bbb","ccc","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1456_3013
["aaa","bbb","ccc","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1457_3013
["ccc","ddd","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1458_3013
["aaa","ccc","ddd","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1459_3013
["bbb","ccc","ddd","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1460_3013
["aaa","bbb","ccc","ddd","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1461_3013
["abb","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1462_3013
["aaa","abb","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1463_3013
["bbb","abb","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1464_3013
["aaa","bbb","abb","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1465_3013
["ccc","abb","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1466_3013
["aaa","ccc","abb","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1467_3013
["bbb","ccc","abb","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1468_3013
["aaa","bbb","ccc","abb","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1469_3013
["ddd","abb","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1470_3013
["aaa","ddd","abb","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1471_3013
["bbb","ddd","abb","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1472_3013
["aaa","bbb","ddd","abb","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1473_3013
["ccc","ddd","abb","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1474_3013
["aaa","ccc","ddd","abb","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1475_3013
["bbb","ccc","ddd","abb","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1476_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1477_3013
["ccc","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1478_3013
["aaa","ccc","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1479_3013
["bbb","ccc","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1480_3013
["aaa","bbb","ccc","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1481_3013
["ccc","ddd","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1482_3013
["aaa","ccc","ddd","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1483_3013
["bbb","ccc","ddd","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1484_3013
["aaa","bbb","ccc","ddd","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1485_3013
["abb","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1486_3013
["aaa","abb","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1487_3013
["bbb","abb","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1488_3013
["aaa","bbb","abb","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1489_3013
["ccc","abb","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1490_3013
["aaa","ccc","abb","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1491_3013
["bbb","ccc","abb","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1492_3013
["aaa","bbb","ccc","abb","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1493_3013
["ddd","abb","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1494_3013
["aaa","ddd","abb","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1495_3013
["bbb","ddd","abb","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1496_3013
["aaa","bbb","ddd","abb","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1497_3013
["ccc","ddd","abb","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1498_3013
["aaa","ccc","ddd","abb","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1499_3013
["bbb","ccc","ddd","abb","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1500_3013
["aaa","bbb","ccc","ddd","abb","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1501_3013
["baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1502_3013
["aaa","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1503_3013
["bbb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1504_3013
["aaa","bbb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1505_3013
["ccc","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1506_3013
["aaa","ccc","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1507_3013
["bbb","ccc","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1508_3013
["aaa","bbb","ccc","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1509_3013
["ddd","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1510_3013
["aaa","ddd","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1511_3013
["bbb","ddd","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1512_3013
["aaa","bbb","ddd","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1513_3013
["ccc","ddd","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1514_3013
["aaa","ccc","ddd","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1515_3013
["bbb","ccc","ddd","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1516_3013
["aaa","bbb","ccc","ddd","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1517_3013
["abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1518_3013
["aaa","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1519_3013
["bbb","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1520_3013
["aaa","bbb","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1521_3013
["ccc","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1522_3013
["aaa","ccc","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1523_3013
["bbb","ccc","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1524_3013
["aaa","bbb","ccc","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1525_3013
["ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1526_3013
["aaa","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1527_3013
["bbb","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1528_3013
["aaa","bbb","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1529_3013
["ccc","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1530_3013
["aaa","ccc","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1531_3013
["bbb","ccc","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1532_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1533_3013
["aaa","ccc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1534_3013
["aaa","bbb","ccc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1535_3013
["aaa","ccc","ddd","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1536_3013
["aaa","bbb","ccc","ddd","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1537_3013
["aaa","abb","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1538_3013
["aaa","bbb","abb","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1539_3013
["aaa","ccc","abb","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1540_3013
["aaa","bbb","ccc","abb","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1541_3013
["aaa","ddd","abb","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1542_3013
["aaa","bbb","ddd","abb","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1543_3013
["aaa","ccc","ddd","abb","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1544_3013
["aaa","bbb","ccc","ddd","abb","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1545_3013
["ccc","baa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1546_3013
["aaa","ccc","baa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1547_3013
["bbb","ccc","baa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1548_3013
["aaa","bbb","ccc","baa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1549_3013
["ccc","ddd","baa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1550_3013
["aaa","ccc","ddd","baa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1551_3013
["bbb","ccc","ddd","baa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1552_3013
["aaa","bbb","ccc","ddd","baa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1553_3013
["abb","baa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1554_3013
["aaa","abb","baa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1555_3013
["bbb","abb","baa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1556_3013
["aaa","bbb","abb","baa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1557_3013
["ccc","abb","baa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1558_3013
["aaa","ccc","abb","baa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1559_3013
["bbb","ccc","abb","baa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1560_3013
["aaa","bbb","ccc","abb","baa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1561_3013
["ddd","abb","baa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1562_3013
["aaa","ddd","abb","baa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1563_3013
["bbb","ddd","abb","baa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1564_3013
["aaa","bbb","ddd","abb","baa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1565_3013
["ccc","ddd","abb","baa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1566_3013
["aaa","ccc","ddd","abb","baa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1567_3013
["bbb","ccc","ddd","abb","baa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1568_3013
["aaa","bbb","ccc","ddd","abb","baa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1569_3013
["aaa","ccc","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1570_3013
["aaa","bbb","ccc","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1571_3013
["aaa","ccc","ddd","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1572_3013
["aaa","bbb","ccc","ddd","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1573_3013
["aaa","abb","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1574_3013
["aaa","bbb","abb","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1575_3013
["aaa","ccc","abb","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1576_3013
["aaa","bbb","ccc","abb","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1577_3013
["aaa","ddd","abb","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1578_3013
["aaa","bbb","ddd","abb","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1579_3013
["aaa","ccc","ddd","abb","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1580_3013
["aaa","bbb","ccc","ddd","abb","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1581_3013
["baa","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1582_3013
["aaa","baa","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1583_3013
["bbb","baa","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1584_3013
["aaa","bbb","baa","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1585_3013
["ccc","baa","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1586_3013
["aaa","ccc","baa","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1587_3013
["bbb","ccc","baa","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1588_3013
["aaa","bbb","ccc","baa","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1589_3013
["ddd","baa","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1590_3013
["aaa","ddd","baa","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1591_3013
["bbb","ddd","baa","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1592_3013
["aaa","bbb","ddd","baa","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1593_3013
["ccc","ddd","baa","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1594_3013
["aaa","ccc","ddd","baa","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1595_3013
["bbb","ccc","ddd","baa","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1596_3013
["aaa","bbb","ccc","ddd","baa","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1597_3013
["abb","baa","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1598_3013
["aaa","abb","baa","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1599_3013
["bbb","abb","baa","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1600_3013
["aaa","bbb","abb","baa","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1601_3013
["ccc","abb","baa","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1602_3013
["aaa","ccc","abb","baa","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1603_3013
["bbb","ccc","abb","baa","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1604_3013
["aaa","bbb","ccc","abb","baa","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1605_3013
["ddd","abb","baa","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1606_3013
["aaa","ddd","abb","baa","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1607_3013
["bbb","ddd","abb","baa","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1608_3013
["aaa","bbb","ddd","abb","baa","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1609_3013
["ccc","ddd","abb","baa","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1610_3013
["aaa","ccc","ddd","abb","baa","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1611_3013
["bbb","ccc","ddd","abb","baa","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1612_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1613_3013
["ccc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1614_3013
["aaa","ccc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1615_3013
["bbb","ccc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1616_3013
["aaa","bbb","ccc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1617_3013
["ccc","ddd","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1618_3013
["aaa","ccc","ddd","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1619_3013
["bbb","ccc","ddd","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1620_3013
["aaa","bbb","ccc","ddd","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1621_3013
["abb","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1622_3013
["aaa","abb","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1623_3013
["bbb","abb","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1624_3013
["aaa","bbb","abb","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1625_3013
["ccc","abb","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1626_3013
["aaa","ccc","abb","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1627_3013
["bbb","ccc","abb","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1628_3013
["aaa","bbb","ccc","abb","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1629_3013
["ddd","abb","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1630_3013
["aaa","ddd","abb","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1631_3013
["bbb","ddd","abb","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1632_3013
["aaa","bbb","ddd","abb","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1633_3013
["ccc","ddd","abb","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1634_3013
["aaa","ccc","ddd","abb","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1635_3013
["bbb","ccc","ddd","abb","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1636_3013
["aaa","bbb","ccc","ddd","abb","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1637_3013
["ccc","baa","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1638_3013
["aaa","ccc","baa","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1639_3013
["bbb","ccc","baa","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1640_3013
["aaa","bbb","ccc","baa","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1641_3013
["ccc","ddd","baa","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1642_3013
["aaa","ccc","ddd","baa","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1643_3013
["bbb","ccc","ddd","baa","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1644_3013
["aaa","bbb","ccc","ddd","baa","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1645_3013
["abb","baa","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1646_3013
["aaa","abb","baa","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1647_3013
["bbb","abb","baa","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1648_3013
["aaa","bbb","abb","baa","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1649_3013
["ccc","abb","baa","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1650_3013
["aaa","ccc","abb","baa","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1651_3013
["bbb","ccc","abb","baa","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1652_3013
["aaa","bbb","ccc","abb","baa","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1653_3013
["ddd","abb","baa","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1654_3013
["aaa","ddd","abb","baa","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1655_3013
["bbb","ddd","abb","baa","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1656_3013
["aaa","bbb","ddd","abb","baa","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1657_3013
["ccc","ddd","abb","baa","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1658_3013
["aaa","ccc","ddd","abb","baa","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1659_3013
["bbb","ccc","ddd","abb","baa","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1660_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1661_3013
["ccc","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1662_3013
["aaa","ccc","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1663_3013
["bbb","ccc","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1664_3013
["aaa","bbb","ccc","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1665_3013
["ccc","ddd","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1666_3013
["aaa","ccc","ddd","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1667_3013
["bbb","ccc","ddd","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1668_3013
["aaa","bbb","ccc","ddd","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1669_3013
["abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1670_3013
["aaa","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1671_3013
["bbb","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1672_3013
["aaa","bbb","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1673_3013
["ccc","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1674_3013
["aaa","ccc","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1675_3013
["bbb","ccc","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1676_3013
["aaa","bbb","ccc","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1677_3013
["ddd","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1678_3013
["aaa","ddd","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1679_3013
["bbb","ddd","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1680_3013
["aaa","bbb","ddd","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1681_3013
["ccc","ddd","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1682_3013
["aaa","ccc","ddd","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1683_3013
["bbb","ccc","ddd","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1684_3013
["aaa","bbb","ccc","ddd","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1685_3013
["baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1686_3013
["aaa","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1687_3013
["bbb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1688_3013
["aaa","bbb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1689_3013
["ccc","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1690_3013
["aaa","ccc","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1691_3013
["bbb","ccc","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1692_3013
["aaa","bbb","ccc","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1693_3013
["ddd","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1694_3013
["aaa","ddd","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1695_3013
["bbb","ddd","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1696_3013
["aaa","bbb","ddd","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1697_3013
["ccc","ddd","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1698_3013
["aaa","ccc","ddd","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1699_3013
["bbb","ccc","ddd","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1700_3013
["aaa","bbb","ccc","ddd","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1701_3013
["abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1702_3013
["aaa","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1703_3013
["bbb","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1704_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1705_3013
["ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1706_3013
["aaa","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1707_3013
["bbb","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1708_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1709_3013
["ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1710_3013
["aaa","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1711_3013
["bbb","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1712_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1713_3013
["ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1714_3013
["aaa","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1715_3013
["bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1716_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd"],
-- 1717_3013
["aaa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1718_3013
["aaa","bbb","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1719_3013
["aaa","bbb","ccc","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1720_3013
["aaa","bbb","ccc","ddd","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1721_3013
["aaa","abb","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1722_3013
["aaa","bbb","abb","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1723_3013
["aaa","ccc","abb","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1724_3013
["aaa","bbb","ccc","abb","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1725_3013
["aaa","ccc","ddd","abb","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1726_3013
["aaa","bbb","ccc","ddd","abb","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1727_3013
["aaa","baa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1728_3013
["aaa","bbb","baa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1729_3013
["aaa","ccc","baa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1730_3013
["aaa","bbb","ccc","baa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1731_3013
["aaa","ccc","ddd","baa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1732_3013
["aaa","bbb","ccc","ddd","baa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1733_3013
["aaa","abb","baa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1734_3013
["aaa","bbb","abb","baa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1735_3013
["aaa","ccc","abb","baa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1736_3013
["aaa","bbb","ccc","abb","baa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1737_3013
["aaa","ccc","ddd","abb","baa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1738_3013
["aaa","bbb","ccc","ddd","abb","baa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1739_3013
["aaa","abb","acc","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1740_3013
["aaa","bbb","abb","acc","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1741_3013
["aaa","bbb","ccc","abb","acc","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1742_3013
["aaa","ddd","abb","acc","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1743_3013
["aaa","bbb","ddd","abb","acc","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1744_3013
["aaa","bbb","ccc","ddd","abb","acc","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1745_3013
["aaa","baa","acc","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1746_3013
["aaa","bbb","baa","acc","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1747_3013
["aaa","ccc","baa","acc","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1748_3013
["aaa","bbb","ccc","baa","acc","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1749_3013
["aaa","ddd","baa","acc","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1750_3013
["aaa","bbb","ddd","baa","acc","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1751_3013
["aaa","ccc","ddd","baa","acc","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1752_3013
["aaa","bbb","ccc","ddd","baa","acc","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1753_3013
["aaa","abb","baa","acc","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1754_3013
["aaa","bbb","abb","baa","acc","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1755_3013
["aaa","ccc","abb","baa","acc","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1756_3013
["aaa","bbb","ccc","abb","baa","acc","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1757_3013
["aaa","ddd","abb","baa","acc","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1758_3013
["aaa","bbb","ddd","abb","baa","acc","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1759_3013
["aaa","ccc","ddd","abb","baa","acc","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1760_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1761_3013
["baa","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1762_3013
["aaa","baa","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1763_3013
["bbb","baa","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1764_3013
["aaa","bbb","baa","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1765_3013
["bbb","ccc","baa","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1766_3013
["aaa","bbb","ccc","baa","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1767_3013
["ddd","baa","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1768_3013
["aaa","ddd","baa","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1769_3013
["bbb","ddd","baa","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1770_3013
["aaa","bbb","ddd","baa","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1771_3013
["bbb","ccc","ddd","baa","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1772_3013
["aaa","bbb","ccc","ddd","baa","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1773_3013
["abb","baa","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1774_3013
["aaa","abb","baa","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1775_3013
["bbb","abb","baa","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1776_3013
["aaa","bbb","abb","baa","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1777_3013
["ccc","abb","baa","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1778_3013
["aaa","ccc","abb","baa","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1779_3013
["bbb","ccc","abb","baa","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1780_3013
["aaa","bbb","ccc","abb","baa","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1781_3013
["ddd","abb","baa","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1782_3013
["aaa","ddd","abb","baa","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1783_3013
["bbb","ddd","abb","baa","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1784_3013
["aaa","bbb","ddd","abb","baa","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1785_3013
["ccc","ddd","abb","baa","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1786_3013
["aaa","ccc","ddd","abb","baa","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1787_3013
["bbb","ccc","ddd","abb","baa","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1788_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1789_3013
["abb","baa","acc","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1790_3013
["aaa","abb","baa","acc","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1791_3013
["bbb","abb","baa","acc","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1792_3013
["aaa","bbb","abb","baa","acc","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1793_3013
["bbb","ccc","abb","baa","acc","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1794_3013
["aaa","bbb","ccc","abb","baa","acc","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1795_3013
["ddd","abb","baa","acc","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1796_3013
["aaa","ddd","abb","baa","acc","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1797_3013
["bbb","ddd","abb","baa","acc","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1798_3013
["aaa","bbb","ddd","abb","baa","acc","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1799_3013
["bbb","ccc","ddd","abb","baa","acc","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1800_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1801_3013
["aaa","abb","acc","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1802_3013
["aaa","bbb","abb","acc","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1803_3013
["aaa","bbb","ccc","abb","acc","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1804_3013
["aaa","bbb","ccc","ddd","abb","acc","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1805_3013
["aaa","baa","acc","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1806_3013
["aaa","bbb","baa","acc","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1807_3013
["aaa","ccc","baa","acc","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1808_3013
["aaa","bbb","ccc","baa","acc","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1809_3013
["aaa","ccc","ddd","baa","acc","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1810_3013
["aaa","bbb","ccc","ddd","baa","acc","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1811_3013
["aaa","abb","baa","acc","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1812_3013
["aaa","bbb","abb","baa","acc","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1813_3013
["aaa","ccc","abb","baa","acc","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1814_3013
["aaa","bbb","ccc","abb","baa","acc","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1815_3013
["aaa","ccc","ddd","abb","baa","acc","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1816_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1817_3013
["baa","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1818_3013
["aaa","baa","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1819_3013
["bbb","baa","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1820_3013
["aaa","bbb","baa","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1821_3013
["bbb","ccc","baa","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1822_3013
["aaa","bbb","ccc","baa","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1823_3013
["ddd","baa","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1824_3013
["aaa","ddd","baa","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1825_3013
["bbb","ddd","baa","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1826_3013
["aaa","bbb","ddd","baa","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1827_3013
["bbb","ccc","ddd","baa","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1828_3013
["aaa","bbb","ccc","ddd","baa","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1829_3013
["abb","baa","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1830_3013
["aaa","abb","baa","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1831_3013
["bbb","abb","baa","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1832_3013
["aaa","bbb","abb","baa","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1833_3013
["ccc","abb","baa","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1834_3013
["aaa","ccc","abb","baa","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1835_3013
["bbb","ccc","abb","baa","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1836_3013
["aaa","bbb","ccc","abb","baa","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1837_3013
["ddd","abb","baa","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1838_3013
["aaa","ddd","abb","baa","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1839_3013
["bbb","ddd","abb","baa","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1840_3013
["aaa","bbb","ddd","abb","baa","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1841_3013
["ccc","ddd","abb","baa","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1842_3013
["aaa","ccc","ddd","abb","baa","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1843_3013
["bbb","ccc","ddd","abb","baa","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1844_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1845_3013
["abb","baa","acc","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1846_3013
["aaa","abb","baa","acc","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1847_3013
["bbb","abb","baa","acc","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1848_3013
["aaa","bbb","abb","baa","acc","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1849_3013
["bbb","ccc","abb","baa","acc","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1850_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1851_3013
["ddd","abb","baa","acc","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1852_3013
["aaa","ddd","abb","baa","acc","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1853_3013
["bbb","ddd","abb","baa","acc","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1854_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1855_3013
["bbb","ccc","ddd","abb","baa","acc","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1856_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1857_3013
["baa","caa","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1858_3013
["aaa","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1859_3013
["bbb","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1860_3013
["aaa","bbb","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1861_3013
["bbb","ccc","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1862_3013
["aaa","bbb","ccc","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1863_3013
["bbb","ccc","ddd","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1864_3013
["aaa","bbb","ccc","ddd","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1865_3013
["abb","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1866_3013
["aaa","abb","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1867_3013
["bbb","abb","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1868_3013
["aaa","bbb","abb","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1869_3013
["ccc","abb","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1870_3013
["aaa","ccc","abb","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1871_3013
["bbb","ccc","abb","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1872_3013
["aaa","bbb","ccc","abb","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1873_3013
["ccc","ddd","abb","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1874_3013
["aaa","ccc","ddd","abb","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1875_3013
["bbb","ccc","ddd","abb","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1876_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1877_3013
["abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1878_3013
["aaa","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1879_3013
["bbb","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1880_3013
["aaa","bbb","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1881_3013
["bbb","ccc","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1882_3013
["aaa","bbb","ccc","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1883_3013
["ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1884_3013
["aaa","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1885_3013
["bbb","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1886_3013
["aaa","bbb","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1887_3013
["bbb","ccc","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1888_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1889_3013
["abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1890_3013
["aaa","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1891_3013
["bbb","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1892_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1893_3013
["bbb","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1894_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1895_3013
["bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1896_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd"],
-- 1897_3013
["aaa","bbb","ccc","ddd","abc","abd","acd","bcd"],
-- 1898_3013
["aaa","bbb","ccc","ddd","abb","acc","add","abc","abd","acd","bcd"],
-- 1899_3013
["aaa","bbb","ccc","ddd","baa","acc","add","abc","abd","acd","bcd"],
-- 1900_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","add","abc","abd","acd","bcd"],
-- 1901_3013
["aaa","bbb","ccc","baa","caa","add","abc","abd","acd","bcd"],
-- 1902_3013
["aaa","bbb","ccc","ddd","baa","caa","add","abc","abd","acd","bcd"],
-- 1903_3013
["aaa","bbb","ccc","abb","baa","caa","add","abc","abd","acd","bcd"],
-- 1904_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","add","abc","abd","acd","bcd"],
-- 1905_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","abc","abd","acd","bcd"],
-- 1906_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","abc","abd","acd","bcd"],
-- 1907_3013
["bbb","ccc","ddd","baa","caa","daa","abc","abd","acd","bcd"],
-- 1908_3013
["aaa","bbb","ccc","ddd","baa","caa","daa","abc","abd","acd","bcd"],
-- 1909_3013
["ccc","ddd","abb","baa","caa","daa","abc","abd","acd","bcd"],
-- 1910_3013
["aaa","ccc","ddd","abb","baa","caa","daa","abc","abd","acd","bcd"],
-- 1911_3013
["bbb","ccc","ddd","abb","baa","caa","daa","abc","abd","acd","bcd"],
-- 1912_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","daa","abc","abd","acd","bcd"],
-- 1913_3013
["ddd","abb","baa","acc","caa","daa","abc","abd","acd","bcd"],
-- 1914_3013
["aaa","ddd","abb","baa","acc","caa","daa","abc","abd","acd","bcd"],
-- 1915_3013
["bbb","ddd","abb","baa","acc","caa","daa","abc","abd","acd","bcd"],
-- 1916_3013
["aaa","bbb","ddd","abb","baa","acc","caa","daa","abc","abd","acd","bcd"],
-- 1917_3013
["bbb","ccc","ddd","abb","baa","acc","caa","daa","abc","abd","acd","bcd"],
-- 1918_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","daa","abc","abd","acd","bcd"],
-- 1919_3013
["abb","baa","acc","caa","add","daa","abc","abd","acd","bcd"],
-- 1920_3013
["aaa","abb","baa","acc","caa","add","daa","abc","abd","acd","bcd"],
-- 1921_3013
["bbb","abb","baa","acc","caa","add","daa","abc","abd","acd","bcd"],
-- 1922_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","abc","abd","acd","bcd"],
-- 1923_3013
["bbb","ccc","abb","baa","acc","caa","add","daa","abc","abd","acd","bcd"],
-- 1924_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","abc","abd","acd","bcd"],
-- 1925_3013
["bbb","ccc","ddd","abb","baa","acc","caa","add","daa","abc","abd","acd","bcd"],
-- 1926_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","abc","abd","acd","bcd"],
-- 1927_3013
["aaa","bbb","ddd","abb","acc","bcc","abc","abd","acd","bcd"],
-- 1928_3013
["aaa","bbb","ccc","ddd","abb","acc","bcc","abc","abd","acd","bcd"],
-- 1929_3013
["aaa","bbb","ddd","abb","baa","acc","bcc","abc","abd","acd","bcd"],
-- 1930_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","bcc","abc","abd","acd","bcd"],
-- 1931_3013
["aaa","bbb","ccc","ddd","abb","caa","bcc","abc","abd","acd","bcd"],
-- 1932_3013
["bbb","ccc","ddd","abb","baa","caa","bcc","abc","abd","acd","bcd"],
-- 1933_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","bcc","abc","abd","acd","bcd"],
-- 1934_3013
["bbb","ddd","baa","acc","caa","bcc","abc","abd","acd","bcd"],
-- 1935_3013
["aaa","bbb","ddd","baa","acc","caa","bcc","abc","abd","acd","bcd"],
-- 1936_3013
["aaa","bbb","ccc","ddd","baa","acc","caa","bcc","abc","abd","acd","bcd"],
-- 1937_3013
["bbb","ddd","abb","baa","acc","caa","bcc","abc","abd","acd","bcd"],
-- 1938_3013
["aaa","bbb","ddd","abb","baa","acc","caa","bcc","abc","abd","acd","bcd"],
-- 1939_3013
["bbb","ccc","ddd","abb","baa","acc","caa","bcc","abc","abd","acd","bcd"],
-- 1940_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","bcc","abc","abd","acd","bcd"],
-- 1941_3013
["aaa","bbb","ddd","abb","acc","add","bcc","abc","abd","acd","bcd"],
-- 1942_3013
["aaa","bbb","ccc","ddd","abb","acc","add","bcc","abc","abd","acd","bcd"],
-- 1943_3013
["aaa","bbb","ddd","baa","acc","add","bcc","abc","abd","acd","bcd"],
-- 1944_3013
["aaa","bbb","ccc","ddd","baa","acc","add","bcc","abc","abd","acd","bcd"],
-- 1945_3013
["aaa","bbb","ddd","abb","baa","acc","add","bcc","abc","abd","acd","bcd"],
-- 1946_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","add","bcc","abc","abd","acd","bcd"],
-- 1947_3013
["aaa","bbb","ccc","ddd","abb","caa","add","bcc","abc","abd","acd","bcd"],
-- 1948_3013
["bbb","ccc","baa","caa","add","bcc","abc","abd","acd","bcd"],
-- 1949_3013
["aaa","bbb","ccc","baa","caa","add","bcc","abc","abd","acd","bcd"],
-- 1950_3013
["bbb","ccc","ddd","baa","caa","add","bcc","abc","abd","acd","bcd"],
-- 1951_3013
["aaa","bbb","ccc","ddd","baa","caa","add","bcc","abc","abd","acd","bcd"],
-- 1952_3013
["bbb","ccc","abb","baa","caa","add","bcc","abc","abd","acd","bcd"],
-- 1953_3013
["aaa","bbb","ccc","abb","baa","caa","add","bcc","abc","abd","acd","bcd"],
-- 1954_3013
["bbb","ccc","ddd","abb","baa","caa","add","bcc","abc","abd","acd","bcd"],
-- 1955_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","add","bcc","abc","abd","acd","bcd"],
-- 1956_3013
["aaa","bbb","ddd","abb","acc","caa","add","bcc","abc","abd","acd","bcd"],
-- 1957_3013
["aaa","bbb","ccc","ddd","abb","acc","caa","add","bcc","abc","abd","acd","bcd"],
-- 1958_3013
["bbb","baa","acc","caa","add","bcc","abc","abd","acd","bcd"],
-- 1959_3013
["aaa","bbb","baa","acc","caa","add","bcc","abc","abd","acd","bcd"],
-- 1960_3013
["bbb","ccc","baa","acc","caa","add","bcc","abc","abd","acd","bcd"],
-- 1961_3013
["aaa","bbb","ccc","baa","acc","caa","add","bcc","abc","abd","acd","bcd"],
-- 1962_3013
["bbb","ddd","baa","acc","caa","add","bcc","abc","abd","acd","bcd"],
-- 1963_3013
["aaa","bbb","ddd","baa","acc","caa","add","bcc","abc","abd","acd","bcd"],
-- 1964_3013
["bbb","ccc","ddd","baa","acc","caa","add","bcc","abc","abd","acd","bcd"],
-- 1965_3013
["aaa","bbb","ccc","ddd","baa","acc","caa","add","bcc","abc","abd","acd","bcd"],
-- 1966_3013
["bbb","abb","baa","acc","caa","add","bcc","abc","abd","acd","bcd"],
-- 1967_3013
["aaa","bbb","abb","baa","acc","caa","add","bcc","abc","abd","acd","bcd"],
-- 1968_3013
["bbb","ccc","abb","baa","acc","caa","add","bcc","abc","abd","acd","bcd"],
-- 1969_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","bcc","abc","abd","acd","bcd"],
-- 1970_3013
["bbb","ddd","abb","baa","acc","caa","add","bcc","abc","abd","acd","bcd"],
-- 1971_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","bcc","abc","abd","acd","bcd"],
-- 1972_3013
["bbb","ccc","ddd","abb","baa","acc","caa","add","bcc","abc","abd","acd","bcd"],
-- 1973_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","bcc","abc","abd","acd","bcd"],
-- 1974_3013
["aaa","bbb","ddd","abb","acc","daa","bcc","abc","abd","acd","bcd"],
-- 1975_3013
["aaa","bbb","ccc","ddd","abb","acc","daa","bcc","abc","abd","acd","bcd"],
-- 1976_3013
["aaa","bbb","ddd","baa","acc","daa","bcc","abc","abd","acd","bcd"],
-- 1977_3013
["aaa","bbb","ccc","ddd","baa","acc","daa","bcc","abc","abd","acd","bcd"],
-- 1978_3013
["aaa","bbb","ddd","abb","baa","acc","daa","bcc","abc","abd","acd","bcd"],
-- 1979_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","daa","bcc","abc","abd","acd","bcd"],
-- 1980_3013
["aaa","ccc","ddd","abb","caa","daa","bcc","abc","abd","acd","bcd"],
-- 1981_3013
["aaa","bbb","ccc","ddd","abb","caa","daa","bcc","abc","abd","acd","bcd"],
-- 1982_3013
["bbb","ccc","ddd","baa","caa","daa","bcc","abc","abd","acd","bcd"],
-- 1983_3013
["aaa","bbb","ccc","ddd","baa","caa","daa","bcc","abc","abd","acd","bcd"],
-- 1984_3013
["ccc","ddd","abb","baa","caa","daa","bcc","abc","abd","acd","bcd"],
-- 1985_3013
["aaa","ccc","ddd","abb","baa","caa","daa","bcc","abc","abd","acd","bcd"],
-- 1986_3013
["bbb","ccc","ddd","abb","baa","caa","daa","bcc","abc","abd","acd","bcd"],
-- 1987_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","daa","bcc","abc","abd","acd","bcd"],
-- 1988_3013
["aaa","ddd","abb","acc","caa","daa","bcc","abc","abd","acd","bcd"],
-- 1989_3013
["aaa","bbb","ddd","abb","acc","caa","daa","bcc","abc","abd","acd","bcd"],
-- 1990_3013
["aaa","ccc","ddd","abb","acc","caa","daa","bcc","abc","abd","acd","bcd"],
-- 1991_3013
["aaa","bbb","ccc","ddd","abb","acc","caa","daa","bcc","abc","abd","acd","bcd"],
-- 1992_3013
["bbb","ddd","baa","acc","caa","daa","bcc","abc","abd","acd","bcd"],
-- 1993_3013
["aaa","bbb","ddd","baa","acc","caa","daa","bcc","abc","abd","acd","bcd"],
-- 1994_3013
["bbb","ccc","ddd","baa","acc","caa","daa","bcc","abc","abd","acd","bcd"],
-- 1995_3013
["aaa","bbb","ccc","ddd","baa","acc","caa","daa","bcc","abc","abd","acd","bcd"],
-- 1996_3013
["ddd","abb","baa","acc","caa","daa","bcc","abc","abd","acd","bcd"],
-- 1997_3013
["aaa","ddd","abb","baa","acc","caa","daa","bcc","abc","abd","acd","bcd"],
-- 1998_3013
["bbb","ddd","abb","baa","acc","caa","daa","bcc","abc","abd","acd","bcd"],
-- 1999_3013
["aaa","bbb","ddd","abb","baa","acc","caa","daa","bcc","abc","abd","acd","bcd"],
-- 2000_3013
["ccc","ddd","abb","baa","acc","caa","daa","bcc","abc","abd","acd","bcd"],
-- 2001_3013
["aaa","ccc","ddd","abb","baa","acc","caa","daa","bcc","abc","abd","acd","bcd"],
-- 2002_3013
["bbb","ccc","ddd","abb","baa","acc","caa","daa","bcc","abc","abd","acd","bcd"],
-- 2003_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","daa","bcc","abc","abd","acd","bcd"],
-- 2004_3013
["aaa","bbb","ddd","abb","acc","add","daa","bcc","abc","abd","acd","bcd"],
-- 2005_3013
["aaa","bbb","ccc","ddd","abb","acc","add","daa","bcc","abc","abd","acd","bcd"],
-- 2006_3013
["aaa","bbb","ddd","baa","acc","add","daa","bcc","abc","abd","acd","bcd"],
-- 2007_3013
["aaa","bbb","ccc","ddd","baa","acc","add","daa","bcc","abc","abd","acd","bcd"],
-- 2008_3013
["aaa","bbb","ddd","abb","baa","acc","add","daa","bcc","abc","abd","acd","bcd"],
-- 2009_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","add","daa","bcc","abc","abd","acd","bcd"],
-- 2010_3013
["aaa","ccc","ddd","abb","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2011_3013
["aaa","bbb","ccc","ddd","abb","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2012_3013
["bbb","ccc","baa","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2013_3013
["aaa","bbb","ccc","baa","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2014_3013
["bbb","ccc","ddd","baa","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2015_3013
["aaa","bbb","ccc","ddd","baa","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2016_3013
["ccc","abb","baa","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2017_3013
["aaa","ccc","abb","baa","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2018_3013
["bbb","ccc","abb","baa","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2019_3013
["aaa","bbb","ccc","abb","baa","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2020_3013
["ccc","ddd","abb","baa","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2021_3013
["aaa","ccc","ddd","abb","baa","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2022_3013
["bbb","ccc","ddd","abb","baa","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2023_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2024_3013
["aaa","ddd","abb","acc","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2025_3013
["aaa","bbb","ddd","abb","acc","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2026_3013
["aaa","ccc","ddd","abb","acc","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2027_3013
["aaa","bbb","ccc","ddd","abb","acc","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2028_3013
["bbb","baa","acc","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2029_3013
["aaa","bbb","baa","acc","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2030_3013
["bbb","ccc","baa","acc","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2031_3013
["aaa","bbb","ccc","baa","acc","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2032_3013
["bbb","ddd","baa","acc","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2033_3013
["aaa","bbb","ddd","baa","acc","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2034_3013
["bbb","ccc","ddd","baa","acc","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2035_3013
["aaa","bbb","ccc","ddd","baa","acc","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2036_3013
["abb","baa","acc","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2037_3013
["aaa","abb","baa","acc","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2038_3013
["bbb","abb","baa","acc","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2039_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2040_3013
["ccc","abb","baa","acc","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2041_3013
["aaa","ccc","abb","baa","acc","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2042_3013
["bbb","ccc","abb","baa","acc","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2043_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2044_3013
["ddd","abb","baa","acc","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2045_3013
["aaa","ddd","abb","baa","acc","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2046_3013
["bbb","ddd","abb","baa","acc","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2047_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2048_3013
["ccc","ddd","abb","baa","acc","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2049_3013
["aaa","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2050_3013
["bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2051_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","abc","abd","acd","bcd"],
-- 2052_3013
["ddd","abb","baa","acc","caa","bcc","cbb","abc","abd","acd","bcd"],
-- 2053_3013
["aaa","ddd","abb","baa","acc","caa","bcc","cbb","abc","abd","acd","bcd"],
-- 2054_3013
["aaa","bbb","ddd","abb","baa","acc","caa","bcc","cbb","abc","abd","acd","bcd"],
-- 2055_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","bcc","cbb","abc","abd","acd","bcd"],
-- 2056_3013
["aaa","ddd","abb","acc","add","bcc","cbb","abc","abd","acd","bcd"],
-- 2057_3013
["aaa","bbb","ddd","abb","acc","add","bcc","cbb","abc","abd","acd","bcd"],
-- 2058_3013
["aaa","bbb","ccc","ddd","abb","acc","add","bcc","cbb","abc","abd","acd","bcd"],
-- 2059_3013
["aaa","bbb","ddd","baa","acc","add","bcc","cbb","abc","abd","acd","bcd"],
-- 2060_3013
["aaa","bbb","ccc","ddd","baa","acc","add","bcc","cbb","abc","abd","acd","bcd"],
-- 2061_3013
["aaa","ddd","abb","baa","acc","add","bcc","cbb","abc","abd","acd","bcd"],
-- 2062_3013
["aaa","bbb","ddd","abb","baa","acc","add","bcc","cbb","abc","abd","acd","bcd"],
-- 2063_3013
["aaa","ccc","ddd","abb","baa","acc","add","bcc","cbb","abc","abd","acd","bcd"],
-- 2064_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","add","bcc","cbb","abc","abd","acd","bcd"],
-- 2065_3013
["bbb","ccc","baa","caa","add","bcc","cbb","abc","abd","acd","bcd"],
-- 2066_3013
["aaa","bbb","ccc","baa","caa","add","bcc","cbb","abc","abd","acd","bcd"],
-- 2067_3013
["bbb","ccc","ddd","baa","caa","add","bcc","cbb","abc","abd","acd","bcd"],
-- 2068_3013
["aaa","bbb","ccc","ddd","baa","caa","add","bcc","cbb","abc","abd","acd","bcd"],
-- 2069_3013
["ccc","abb","baa","caa","add","bcc","cbb","abc","abd","acd","bcd"],
-- 2070_3013
["aaa","ccc","abb","baa","caa","add","bcc","cbb","abc","abd","acd","bcd"],
-- 2071_3013
["bbb","ccc","abb","baa","caa","add","bcc","cbb","abc","abd","acd","bcd"],
-- 2072_3013
["aaa","bbb","ccc","abb","baa","caa","add","bcc","cbb","abc","abd","acd","bcd"],
-- 2073_3013
["ccc","ddd","abb","baa","caa","add","bcc","cbb","abc","abd","acd","bcd"],
-- 2074_3013
["aaa","ccc","ddd","abb","baa","caa","add","bcc","cbb","abc","abd","acd","bcd"],
-- 2075_3013
["bbb","ccc","ddd","abb","baa","caa","add","bcc","cbb","abc","abd","acd","bcd"],
-- 2076_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","add","bcc","cbb","abc","abd","acd","bcd"],
-- 2077_3013
["abb","baa","acc","caa","add","bcc","cbb","abc","abd","acd","bcd"],
-- 2078_3013
["aaa","abb","baa","acc","caa","add","bcc","cbb","abc","abd","acd","bcd"],
-- 2079_3013
["bbb","abb","baa","acc","caa","add","bcc","cbb","abc","abd","acd","bcd"],
-- 2080_3013
["aaa","bbb","abb","baa","acc","caa","add","bcc","cbb","abc","abd","acd","bcd"],
-- 2081_3013
["bbb","ccc","abb","baa","acc","caa","add","bcc","cbb","abc","abd","acd","bcd"],
-- 2082_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","bcc","cbb","abc","abd","acd","bcd"],
-- 2083_3013
["ddd","abb","baa","acc","caa","add","bcc","cbb","abc","abd","acd","bcd"],
-- 2084_3013
["aaa","ddd","abb","baa","acc","caa","add","bcc","cbb","abc","abd","acd","bcd"],
-- 2085_3013
["bbb","ddd","abb","baa","acc","caa","add","bcc","cbb","abc","abd","acd","bcd"],
-- 2086_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","bcc","cbb","abc","abd","acd","bcd"],
-- 2087_3013
["bbb","ccc","ddd","abb","baa","acc","caa","add","bcc","cbb","abc","abd","acd","bcd"],
-- 2088_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","bcc","cbb","abc","abd","acd","bcd"],
-- 2089_3013
["aaa","ddd","abb","acc","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2090_3013
["aaa","bbb","ddd","abb","acc","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2091_3013
["aaa","bbb","ccc","ddd","abb","acc","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2092_3013
["aaa","bbb","ddd","baa","acc","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2093_3013
["aaa","bbb","ccc","ddd","baa","acc","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2094_3013
["aaa","ddd","abb","baa","acc","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2095_3013
["aaa","bbb","ddd","abb","baa","acc","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2096_3013
["aaa","ccc","ddd","abb","baa","acc","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2097_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2098_3013
["bbb","ccc","ddd","baa","caa","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2099_3013
["aaa","bbb","ccc","ddd","baa","caa","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2100_3013
["ccc","ddd","abb","baa","caa","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2101_3013
["aaa","ccc","ddd","abb","baa","caa","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2102_3013
["bbb","ccc","ddd","abb","baa","caa","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2103_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2104_3013
["ddd","abb","baa","acc","caa","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2105_3013
["aaa","ddd","abb","baa","acc","caa","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2106_3013
["bbb","ddd","abb","baa","acc","caa","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2107_3013
["aaa","bbb","ddd","abb","baa","acc","caa","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2108_3013
["bbb","ccc","ddd","abb","baa","acc","caa","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2109_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2110_3013
["aaa","ddd","abb","acc","add","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2111_3013
["aaa","bbb","ddd","abb","acc","add","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2112_3013
["aaa","bbb","ccc","ddd","abb","acc","add","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2113_3013
["aaa","bbb","ddd","baa","acc","add","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2114_3013
["aaa","bbb","ccc","ddd","baa","acc","add","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2115_3013
["aaa","ddd","abb","baa","acc","add","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2116_3013
["aaa","bbb","ddd","abb","baa","acc","add","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2117_3013
["aaa","ccc","ddd","abb","baa","acc","add","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2118_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","add","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2119_3013
["bbb","ccc","baa","caa","add","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2120_3013
["aaa","bbb","ccc","baa","caa","add","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2121_3013
["bbb","ccc","ddd","baa","caa","add","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2122_3013
["aaa","bbb","ccc","ddd","baa","caa","add","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2123_3013
["ccc","abb","baa","caa","add","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2124_3013
["aaa","ccc","abb","baa","caa","add","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2125_3013
["bbb","ccc","abb","baa","caa","add","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2126_3013
["aaa","bbb","ccc","abb","baa","caa","add","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2127_3013
["ccc","ddd","abb","baa","caa","add","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2128_3013
["aaa","ccc","ddd","abb","baa","caa","add","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2129_3013
["bbb","ccc","ddd","abb","baa","caa","add","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2130_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","add","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2131_3013
["abb","baa","acc","caa","add","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2132_3013
["aaa","abb","baa","acc","caa","add","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2133_3013
["bbb","abb","baa","acc","caa","add","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2134_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2135_3013
["bbb","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2136_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2137_3013
["ddd","abb","baa","acc","caa","add","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2138_3013
["aaa","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2139_3013
["bbb","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2140_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2141_3013
["bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2142_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","abc","abd","acd","bcd"],
-- 2143_3013
["aaa","bbb","abb","acc","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2144_3013
["aaa","bbb","ccc","abb","acc","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2145_3013
["aaa","bbb","ccc","ddd","abb","acc","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2146_3013
["aaa","bbb","abb","baa","acc","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2147_3013
["aaa","bbb","ccc","abb","baa","acc","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2148_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2149_3013
["aaa","bbb","ccc","abb","caa","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2150_3013
["aaa","bbb","ccc","ddd","abb","caa","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2151_3013
["bbb","ccc","baa","caa","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2152_3013
["aaa","bbb","ccc","baa","caa","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2153_3013
["bbb","ccc","ddd","baa","caa","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2154_3013
["aaa","bbb","ccc","ddd","baa","caa","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2155_3013
["bbb","ccc","abb","baa","caa","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2156_3013
["aaa","bbb","ccc","abb","baa","caa","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2157_3013
["bbb","ccc","ddd","abb","baa","caa","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2158_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2159_3013
["aaa","bbb","abb","acc","caa","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2160_3013
["aaa","bbb","ccc","abb","acc","caa","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2161_3013
["aaa","bbb","ddd","abb","acc","caa","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2162_3013
["aaa","bbb","ccc","ddd","abb","acc","caa","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2163_3013
["bbb","baa","acc","caa","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2164_3013
["aaa","bbb","baa","acc","caa","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2165_3013
["bbb","ccc","baa","acc","caa","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2166_3013
["aaa","bbb","ccc","baa","acc","caa","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2167_3013
["bbb","ddd","baa","acc","caa","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2168_3013
["aaa","bbb","ddd","baa","acc","caa","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2169_3013
["bbb","ccc","ddd","baa","acc","caa","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2170_3013
["aaa","bbb","ccc","ddd","baa","acc","caa","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2171_3013
["bbb","abb","baa","acc","caa","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2172_3013
["aaa","bbb","abb","baa","acc","caa","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2173_3013
["bbb","ccc","abb","baa","acc","caa","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2174_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2175_3013
["bbb","ddd","abb","baa","acc","caa","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2176_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2177_3013
["bbb","ccc","ddd","abb","baa","acc","caa","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2178_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","bcc","bdd","abc","abd","acd","bcd"],
-- 2179_3013
["aaa","ccc","ddd","abb","caa","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2180_3013
["aaa","bbb","ccc","ddd","abb","caa","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2181_3013
["bbb","ccc","ddd","baa","caa","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2182_3013
["aaa","bbb","ccc","ddd","baa","caa","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2183_3013
["ccc","ddd","abb","baa","caa","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2184_3013
["aaa","ccc","ddd","abb","baa","caa","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2185_3013
["bbb","ccc","ddd","abb","baa","caa","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2186_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2187_3013
["aaa","ddd","abb","acc","caa","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2188_3013
["aaa","bbb","ddd","abb","acc","caa","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2189_3013
["aaa","ccc","ddd","abb","acc","caa","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2190_3013
["aaa","bbb","ccc","ddd","abb","acc","caa","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2191_3013
["bbb","ddd","baa","acc","caa","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2192_3013
["aaa","bbb","ddd","baa","acc","caa","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2193_3013
["bbb","ccc","ddd","baa","acc","caa","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2194_3013
["aaa","bbb","ccc","ddd","baa","acc","caa","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2195_3013
["ddd","abb","baa","acc","caa","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2196_3013
["aaa","ddd","abb","baa","acc","caa","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2197_3013
["bbb","ddd","abb","baa","acc","caa","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2198_3013
["aaa","bbb","ddd","abb","baa","acc","caa","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2199_3013
["ccc","ddd","abb","baa","acc","caa","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2200_3013
["aaa","ccc","ddd","abb","baa","acc","caa","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2201_3013
["bbb","ccc","ddd","abb","baa","acc","caa","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2202_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2203_3013
["aaa","abb","acc","caa","add","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2204_3013
["aaa","bbb","abb","acc","caa","add","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2205_3013
["aaa","ccc","abb","acc","caa","add","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2206_3013
["aaa","bbb","ccc","abb","acc","caa","add","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2207_3013
["aaa","ccc","ddd","abb","acc","caa","add","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2208_3013
["aaa","bbb","ccc","ddd","abb","acc","caa","add","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2209_3013
["bbb","baa","acc","caa","add","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2210_3013
["aaa","bbb","baa","acc","caa","add","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2211_3013
["bbb","ccc","baa","acc","caa","add","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2212_3013
["aaa","bbb","ccc","baa","acc","caa","add","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2213_3013
["bbb","ccc","ddd","baa","acc","caa","add","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2214_3013
["aaa","bbb","ccc","ddd","baa","acc","caa","add","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2215_3013
["abb","baa","acc","caa","add","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2216_3013
["aaa","abb","baa","acc","caa","add","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2217_3013
["bbb","abb","baa","acc","caa","add","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2218_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2219_3013
["ccc","abb","baa","acc","caa","add","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2220_3013
["aaa","ccc","abb","baa","acc","caa","add","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2221_3013
["bbb","ccc","abb","baa","acc","caa","add","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2222_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2223_3013
["ccc","ddd","abb","baa","acc","caa","add","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2224_3013
["aaa","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2225_3013
["bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2226_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","bdd","abc","abd","acd","bcd"],
-- 2227_3013
["aaa","ccc","abb","caa","add","cbb","bdd","abc","abd","acd","bcd"],
-- 2228_3013
["aaa","bbb","ccc","abb","caa","add","cbb","bdd","abc","abd","acd","bcd"],
-- 2229_3013
["aaa","ccc","ddd","abb","caa","add","cbb","bdd","abc","abd","acd","bcd"],
-- 2230_3013
["aaa","bbb","ccc","ddd","abb","caa","add","cbb","bdd","abc","abd","acd","bcd"],
-- 2231_3013
["ccc","abb","baa","caa","add","cbb","bdd","abc","abd","acd","bcd"],
-- 2232_3013
["aaa","ccc","abb","baa","caa","add","cbb","bdd","abc","abd","acd","bcd"],
-- 2233_3013
["aaa","bbb","ccc","abb","baa","caa","add","cbb","bdd","abc","abd","acd","bcd"],
-- 2234_3013
["ccc","ddd","abb","baa","caa","add","cbb","bdd","abc","abd","acd","bcd"],
-- 2235_3013
["aaa","ccc","ddd","abb","baa","caa","add","cbb","bdd","abc","abd","acd","bcd"],
-- 2236_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","add","cbb","bdd","abc","abd","acd","bcd"],
-- 2237_3013
["aaa","ccc","abb","acc","caa","add","cbb","bdd","abc","abd","acd","bcd"],
-- 2238_3013
["aaa","bbb","ccc","abb","acc","caa","add","cbb","bdd","abc","abd","acd","bcd"],
-- 2239_3013
["aaa","ccc","ddd","abb","acc","caa","add","cbb","bdd","abc","abd","acd","bcd"],
-- 2240_3013
["aaa","bbb","ccc","ddd","abb","acc","caa","add","cbb","bdd","abc","abd","acd","bcd"],
-- 2241_3013
["bbb","ccc","baa","acc","caa","add","cbb","bdd","abc","abd","acd","bcd"],
-- 2242_3013
["aaa","bbb","ccc","baa","acc","caa","add","cbb","bdd","abc","abd","acd","bcd"],
-- 2243_3013
["bbb","ccc","ddd","baa","acc","caa","add","cbb","bdd","abc","abd","acd","bcd"],
-- 2244_3013
["aaa","bbb","ccc","ddd","baa","acc","caa","add","cbb","bdd","abc","abd","acd","bcd"],
-- 2245_3013
["ccc","abb","baa","acc","caa","add","cbb","bdd","abc","abd","acd","bcd"],
-- 2246_3013
["aaa","ccc","abb","baa","acc","caa","add","cbb","bdd","abc","abd","acd","bcd"],
-- 2247_3013
["bbb","ccc","abb","baa","acc","caa","add","cbb","bdd","abc","abd","acd","bcd"],
-- 2248_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","cbb","bdd","abc","abd","acd","bcd"],
-- 2249_3013
["ccc","ddd","abb","baa","acc","caa","add","cbb","bdd","abc","abd","acd","bcd"],
-- 2250_3013
["aaa","ccc","ddd","abb","baa","acc","caa","add","cbb","bdd","abc","abd","acd","bcd"],
-- 2251_3013
["bbb","ccc","ddd","abb","baa","acc","caa","add","cbb","bdd","abc","abd","acd","bcd"],
-- 2252_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","cbb","bdd","abc","abd","acd","bcd"],
-- 2253_3013
["aaa","ccc","abb","acc","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2254_3013
["aaa","bbb","ccc","abb","acc","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2255_3013
["aaa","ccc","ddd","abb","acc","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2256_3013
["aaa","bbb","ccc","ddd","abb","acc","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2257_3013
["abb","baa","acc","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2258_3013
["aaa","abb","baa","acc","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2259_3013
["aaa","bbb","abb","baa","acc","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2260_3013
["ccc","abb","baa","acc","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2261_3013
["aaa","ccc","abb","baa","acc","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2262_3013
["bbb","ccc","abb","baa","acc","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2263_3013
["aaa","bbb","ccc","abb","baa","acc","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2264_3013
["ccc","ddd","abb","baa","acc","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2265_3013
["aaa","ccc","ddd","abb","baa","acc","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2266_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2267_3013
["aaa","ccc","abb","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2268_3013
["aaa","bbb","ccc","abb","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2269_3013
["aaa","ccc","ddd","abb","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2270_3013
["aaa","bbb","ccc","ddd","abb","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2271_3013
["bbb","ccc","ddd","baa","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2272_3013
["aaa","bbb","ccc","ddd","baa","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2273_3013
["ccc","abb","baa","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2274_3013
["aaa","ccc","abb","baa","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2275_3013
["bbb","ccc","abb","baa","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2276_3013
["aaa","bbb","ccc","abb","baa","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2277_3013
["ccc","ddd","abb","baa","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2278_3013
["aaa","ccc","ddd","abb","baa","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2279_3013
["bbb","ccc","ddd","abb","baa","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2280_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2281_3013
["aaa","ccc","abb","acc","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2282_3013
["aaa","bbb","ccc","abb","acc","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2283_3013
["aaa","ccc","ddd","abb","acc","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2284_3013
["aaa","bbb","ccc","ddd","abb","acc","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2285_3013
["bbb","ddd","baa","acc","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2286_3013
["aaa","bbb","ddd","baa","acc","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2287_3013
["bbb","ccc","ddd","baa","acc","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2288_3013
["aaa","bbb","ccc","ddd","baa","acc","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2289_3013
["abb","baa","acc","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2290_3013
["aaa","abb","baa","acc","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2291_3013
["bbb","abb","baa","acc","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2292_3013
["aaa","bbb","abb","baa","acc","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2293_3013
["ccc","abb","baa","acc","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2294_3013
["aaa","ccc","abb","baa","acc","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2295_3013
["bbb","ccc","abb","baa","acc","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2296_3013
["aaa","bbb","ccc","abb","baa","acc","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2297_3013
["ddd","abb","baa","acc","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2298_3013
["aaa","ddd","abb","baa","acc","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2299_3013
["bbb","ddd","abb","baa","acc","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2300_3013
["aaa","bbb","ddd","abb","baa","acc","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2301_3013
["ccc","ddd","abb","baa","acc","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2302_3013
["aaa","ccc","ddd","abb","baa","acc","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2303_3013
["bbb","ccc","ddd","abb","baa","acc","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2304_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2305_3013
["aaa","ccc","abb","acc","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2306_3013
["aaa","bbb","ccc","abb","acc","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2307_3013
["aaa","ccc","ddd","abb","acc","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2308_3013
["aaa","bbb","ccc","ddd","abb","acc","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2309_3013
["bbb","baa","acc","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2310_3013
["aaa","bbb","baa","acc","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2311_3013
["bbb","ccc","baa","acc","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2312_3013
["aaa","bbb","ccc","baa","acc","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2313_3013
["bbb","ddd","baa","acc","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2314_3013
["aaa","bbb","ddd","baa","acc","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2315_3013
["bbb","ccc","ddd","baa","acc","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2316_3013
["aaa","bbb","ccc","ddd","baa","acc","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2317_3013
["abb","baa","acc","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2318_3013
["aaa","abb","baa","acc","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2319_3013
["bbb","abb","baa","acc","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2320_3013
["aaa","bbb","abb","baa","acc","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2321_3013
["ccc","abb","baa","acc","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2322_3013
["aaa","ccc","abb","baa","acc","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2323_3013
["bbb","ccc","abb","baa","acc","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2324_3013
["aaa","bbb","ccc","abb","baa","acc","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2325_3013
["ddd","abb","baa","acc","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2326_3013
["aaa","ddd","abb","baa","acc","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2327_3013
["bbb","ddd","abb","baa","acc","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2328_3013
["aaa","bbb","ddd","abb","baa","acc","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2329_3013
["ccc","ddd","abb","baa","acc","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2330_3013
["aaa","ccc","ddd","abb","baa","acc","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2331_3013
["bbb","ccc","ddd","abb","baa","acc","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2332_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2333_3013
["aaa","ccc","abb","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2334_3013
["aaa","bbb","ccc","abb","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2335_3013
["aaa","ccc","ddd","abb","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2336_3013
["aaa","bbb","ccc","ddd","abb","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2337_3013
["bbb","ccc","baa","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2338_3013
["aaa","bbb","ccc","baa","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2339_3013
["bbb","ccc","ddd","baa","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2340_3013
["aaa","bbb","ccc","ddd","baa","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2341_3013
["ccc","abb","baa","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2342_3013
["aaa","ccc","abb","baa","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2343_3013
["bbb","ccc","abb","baa","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2344_3013
["aaa","bbb","ccc","abb","baa","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2345_3013
["ccc","ddd","abb","baa","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2346_3013
["aaa","ccc","ddd","abb","baa","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2347_3013
["bbb","ccc","ddd","abb","baa","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2348_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2349_3013
["aaa","ccc","abb","acc","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2350_3013
["aaa","bbb","ccc","abb","acc","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2351_3013
["aaa","ccc","ddd","abb","acc","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2352_3013
["aaa","bbb","ccc","ddd","abb","acc","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2353_3013
["bbb","baa","acc","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2354_3013
["aaa","bbb","baa","acc","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2355_3013
["bbb","ccc","baa","acc","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2356_3013
["aaa","bbb","ccc","baa","acc","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2357_3013
["bbb","ddd","baa","acc","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2358_3013
["aaa","bbb","ddd","baa","acc","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2359_3013
["bbb","ccc","ddd","baa","acc","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2360_3013
["aaa","bbb","ccc","ddd","baa","acc","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2361_3013
["abb","baa","acc","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2362_3013
["aaa","abb","baa","acc","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2363_3013
["bbb","abb","baa","acc","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2364_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2365_3013
["ccc","abb","baa","acc","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2366_3013
["aaa","ccc","abb","baa","acc","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2367_3013
["bbb","ccc","abb","baa","acc","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2368_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2369_3013
["ddd","abb","baa","acc","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2370_3013
["aaa","ddd","abb","baa","acc","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2371_3013
["bbb","ddd","abb","baa","acc","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2372_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2373_3013
["ccc","ddd","abb","baa","acc","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2374_3013
["aaa","ccc","ddd","abb","baa","acc","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2375_3013
["bbb","ccc","ddd","abb","baa","acc","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2376_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","cbb","bdd","abc","abd","acd","bcd"],
-- 2377_3013
["aaa","abb","acc","caa","add","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2378_3013
["aaa","bbb","abb","acc","caa","add","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2379_3013
["aaa","ccc","abb","acc","caa","add","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2380_3013
["aaa","bbb","ccc","abb","acc","caa","add","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2381_3013
["aaa","ddd","abb","acc","caa","add","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2382_3013
["aaa","bbb","ddd","abb","acc","caa","add","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2383_3013
["aaa","ccc","ddd","abb","acc","caa","add","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2384_3013
["aaa","bbb","ccc","ddd","abb","acc","caa","add","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2385_3013
["abb","baa","acc","caa","add","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2386_3013
["aaa","abb","baa","acc","caa","add","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2387_3013
["aaa","bbb","abb","baa","acc","caa","add","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2388_3013
["ccc","abb","baa","acc","caa","add","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2389_3013
["aaa","ccc","abb","baa","acc","caa","add","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2390_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2391_3013
["ddd","abb","baa","acc","caa","add","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2392_3013
["aaa","ddd","abb","baa","acc","caa","add","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2393_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2394_3013
["ccc","ddd","abb","baa","acc","caa","add","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2395_3013
["aaa","ccc","ddd","abb","baa","acc","caa","add","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2396_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2397_3013
["aaa","ccc","abb","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2398_3013
["aaa","bbb","ccc","abb","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2399_3013
["aaa","ccc","ddd","abb","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2400_3013
["aaa","bbb","ccc","ddd","abb","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2401_3013
["bbb","ccc","ddd","baa","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2402_3013
["aaa","bbb","ccc","ddd","baa","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2403_3013
["ccc","abb","baa","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2404_3013
["aaa","ccc","abb","baa","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2405_3013
["bbb","ccc","abb","baa","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2406_3013
["aaa","bbb","ccc","abb","baa","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2407_3013
["ccc","ddd","abb","baa","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2408_3013
["aaa","ccc","ddd","abb","baa","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2409_3013
["bbb","ccc","ddd","abb","baa","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2410_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2411_3013
["aaa","abb","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2412_3013
["aaa","bbb","abb","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2413_3013
["aaa","ccc","abb","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2414_3013
["aaa","bbb","ccc","abb","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2415_3013
["aaa","ddd","abb","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2416_3013
["aaa","bbb","ddd","abb","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2417_3013
["aaa","ccc","ddd","abb","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2418_3013
["aaa","bbb","ccc","ddd","abb","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2419_3013
["bbb","ddd","baa","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2420_3013
["aaa","bbb","ddd","baa","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2421_3013
["bbb","ccc","ddd","baa","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2422_3013
["aaa","bbb","ccc","ddd","baa","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2423_3013
["abb","baa","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2424_3013
["aaa","abb","baa","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2425_3013
["bbb","abb","baa","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2426_3013
["aaa","bbb","abb","baa","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2427_3013
["ccc","abb","baa","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2428_3013
["aaa","ccc","abb","baa","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2429_3013
["bbb","ccc","abb","baa","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2430_3013
["aaa","bbb","ccc","abb","baa","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2431_3013
["ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2432_3013
["aaa","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2433_3013
["bbb","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2434_3013
["aaa","bbb","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2435_3013
["ccc","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2436_3013
["aaa","ccc","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2437_3013
["bbb","ccc","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2438_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2439_3013
["aaa","abb","acc","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2440_3013
["aaa","bbb","abb","acc","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2441_3013
["aaa","ccc","abb","acc","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2442_3013
["aaa","bbb","ccc","abb","acc","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2443_3013
["aaa","ddd","abb","acc","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2444_3013
["aaa","bbb","ddd","abb","acc","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2445_3013
["aaa","ccc","ddd","abb","acc","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2446_3013
["aaa","bbb","ccc","ddd","abb","acc","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2447_3013
["abb","baa","acc","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2448_3013
["aaa","abb","baa","acc","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2449_3013
["aaa","bbb","abb","baa","acc","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2450_3013
["ccc","abb","baa","acc","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2451_3013
["aaa","ccc","abb","baa","acc","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2452_3013
["bbb","ccc","abb","baa","acc","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2453_3013
["aaa","bbb","ccc","abb","baa","acc","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2454_3013
["ccc","ddd","abb","baa","acc","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2455_3013
["aaa","ccc","ddd","abb","baa","acc","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2456_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2457_3013
["aaa","ccc","abb","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2458_3013
["aaa","bbb","ccc","abb","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2459_3013
["aaa","ccc","ddd","abb","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2460_3013
["aaa","bbb","ccc","ddd","abb","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2461_3013
["bbb","ccc","baa","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2462_3013
["aaa","bbb","ccc","baa","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2463_3013
["bbb","ccc","ddd","baa","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2464_3013
["aaa","bbb","ccc","ddd","baa","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2465_3013
["ccc","abb","baa","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2466_3013
["aaa","ccc","abb","baa","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2467_3013
["bbb","ccc","abb","baa","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2468_3013
["aaa","bbb","ccc","abb","baa","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2469_3013
["ccc","ddd","abb","baa","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2470_3013
["aaa","ccc","ddd","abb","baa","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2471_3013
["bbb","ccc","ddd","abb","baa","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2472_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2473_3013
["aaa","abb","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2474_3013
["aaa","bbb","abb","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2475_3013
["aaa","ccc","abb","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2476_3013
["aaa","bbb","ccc","abb","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2477_3013
["aaa","ddd","abb","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2478_3013
["aaa","bbb","ddd","abb","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2479_3013
["aaa","ccc","ddd","abb","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2480_3013
["aaa","bbb","ccc","ddd","abb","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2481_3013
["bbb","baa","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2482_3013
["aaa","bbb","baa","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2483_3013
["bbb","ccc","baa","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2484_3013
["aaa","bbb","ccc","baa","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2485_3013
["bbb","ddd","baa","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2486_3013
["aaa","bbb","ddd","baa","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2487_3013
["bbb","ccc","ddd","baa","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2488_3013
["aaa","bbb","ccc","ddd","baa","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2489_3013
["abb","baa","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2490_3013
["aaa","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2491_3013
["bbb","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2492_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2493_3013
["ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2494_3013
["aaa","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2495_3013
["bbb","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2496_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2497_3013
["ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2498_3013
["aaa","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2499_3013
["bbb","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2500_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2501_3013
["ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2502_3013
["aaa","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2503_3013
["bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2504_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","abc","abd","acd","bcd"],
-- 2505_3013
["aaa","ccc","ddd","abb","caa","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2506_3013
["aaa","bbb","ccc","ddd","abb","caa","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2507_3013
["ccc","ddd","abb","baa","caa","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2508_3013
["aaa","ccc","ddd","abb","baa","caa","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2509_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2510_3013
["aaa","ccc","ddd","abb","acc","caa","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2511_3013
["aaa","bbb","ccc","ddd","abb","acc","caa","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2512_3013
["bbb","ddd","baa","acc","caa","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2513_3013
["aaa","bbb","ddd","baa","acc","caa","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2514_3013
["bbb","ccc","ddd","baa","acc","caa","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2515_3013
["aaa","bbb","ccc","ddd","baa","acc","caa","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2516_3013
["ddd","abb","baa","acc","caa","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2517_3013
["aaa","ddd","abb","baa","acc","caa","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2518_3013
["bbb","ddd","abb","baa","acc","caa","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2519_3013
["aaa","bbb","ddd","abb","baa","acc","caa","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2520_3013
["ccc","ddd","abb","baa","acc","caa","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2521_3013
["aaa","ccc","ddd","abb","baa","acc","caa","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2522_3013
["bbb","ccc","ddd","abb","baa","acc","caa","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2523_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2524_3013
["aaa","ccc","ddd","abb","acc","caa","add","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2525_3013
["aaa","bbb","ccc","ddd","abb","acc","caa","add","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2526_3013
["bbb","baa","acc","caa","add","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2527_3013
["aaa","bbb","baa","acc","caa","add","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2528_3013
["bbb","ccc","baa","acc","caa","add","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2529_3013
["aaa","bbb","ccc","baa","acc","caa","add","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2530_3013
["bbb","ccc","ddd","baa","acc","caa","add","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2531_3013
["aaa","bbb","ccc","ddd","baa","acc","caa","add","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2532_3013
["abb","baa","acc","caa","add","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2533_3013
["aaa","abb","baa","acc","caa","add","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2534_3013
["bbb","abb","baa","acc","caa","add","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2535_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2536_3013
["ccc","abb","baa","acc","caa","add","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2537_3013
["aaa","ccc","abb","baa","acc","caa","add","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2538_3013
["bbb","ccc","abb","baa","acc","caa","add","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2539_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2540_3013
["ccc","ddd","abb","baa","acc","caa","add","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2541_3013
["aaa","ccc","ddd","abb","baa","acc","caa","add","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2542_3013
["bbb","ccc","ddd","abb","baa","acc","caa","add","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2543_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","cbb","dbb","abc","abd","acd","bcd"],
-- 2544_3013
["aaa","ddd","abb","acc","caa","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2545_3013
["aaa","bbb","ddd","abb","acc","caa","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2546_3013
["aaa","ccc","ddd","abb","acc","caa","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2547_3013
["aaa","bbb","ccc","ddd","abb","acc","caa","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2548_3013
["ddd","abb","baa","acc","caa","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2549_3013
["aaa","ddd","abb","baa","acc","caa","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2550_3013
["aaa","bbb","ddd","abb","baa","acc","caa","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2551_3013
["ccc","ddd","abb","baa","acc","caa","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2552_3013
["aaa","ccc","ddd","abb","baa","acc","caa","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2553_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2554_3013
["aaa","ddd","abb","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2555_3013
["aaa","bbb","ddd","abb","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2556_3013
["aaa","ccc","ddd","abb","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2557_3013
["aaa","bbb","ccc","ddd","abb","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2558_3013
["abb","baa","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2559_3013
["aaa","abb","baa","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2560_3013
["aaa","bbb","abb","baa","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2561_3013
["ccc","abb","baa","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2562_3013
["aaa","ccc","abb","baa","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2563_3013
["bbb","ccc","abb","baa","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2564_3013
["aaa","bbb","ccc","abb","baa","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2565_3013
["ccc","ddd","abb","baa","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2566_3013
["aaa","ccc","ddd","abb","baa","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2567_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2568_3013
["aaa","ddd","abb","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2569_3013
["aaa","bbb","ddd","abb","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2570_3013
["aaa","ccc","ddd","abb","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2571_3013
["aaa","bbb","ccc","ddd","abb","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2572_3013
["bbb","baa","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2573_3013
["aaa","bbb","baa","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2574_3013
["bbb","ccc","baa","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2575_3013
["aaa","bbb","ccc","baa","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2576_3013
["bbb","ddd","baa","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2577_3013
["aaa","bbb","ddd","baa","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2578_3013
["bbb","ccc","ddd","baa","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2579_3013
["aaa","bbb","ccc","ddd","baa","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2580_3013
["abb","baa","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2581_3013
["aaa","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2582_3013
["bbb","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2583_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2584_3013
["ccc","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2585_3013
["aaa","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2586_3013
["bbb","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2587_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2588_3013
["ddd","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2589_3013
["aaa","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2590_3013
["bbb","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2591_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2592_3013
["ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2593_3013
["aaa","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2594_3013
["bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2595_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","abc","abd","acd","bcd"],
-- 2596_3013
["aaa","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","abc","abd","acd","bcd"],
-- 2597_3013
["aaa","bbb","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","abc","abd","acd","bcd"],
-- 2598_3013
["aaa","ccc","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","abc","abd","acd","bcd"],
-- 2599_3013
["aaa","bbb","ccc","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","abc","abd","acd","bcd"],
-- 2600_3013
["aaa","ccc","ddd","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","abc","abd","acd","bcd"],
-- 2601_3013
["aaa","bbb","ccc","ddd","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","abc","abd","acd","bcd"],
-- 2602_3013
["abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","abc","abd","acd","bcd"],
-- 2603_3013
["aaa","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","abc","abd","acd","bcd"],
-- 2604_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","abc","abd","acd","bcd"],
-- 2605_3013
["ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","abc","abd","acd","bcd"],
-- 2606_3013
["aaa","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","abc","abd","acd","bcd"],
-- 2607_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","abc","abd","acd","bcd"],
-- 2608_3013
["ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","abc","abd","acd","bcd"],
-- 2609_3013
["aaa","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","abc","abd","acd","bcd"],
-- 2610_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","abc","abd","acd","bcd"],
-- 2611_3013
["aaa","bbb","abb","acc","add","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2612_3013
["aaa","bbb","ccc","abb","acc","add","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2613_3013
["aaa","bbb","ddd","abb","acc","add","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2614_3013
["aaa","bbb","ccc","ddd","abb","acc","add","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2615_3013
["aaa","bbb","abb","baa","acc","add","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2616_3013
["aaa","bbb","ccc","abb","baa","acc","add","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2617_3013
["aaa","bbb","ddd","abb","baa","acc","add","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2618_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","add","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2619_3013
["aaa","bbb","ccc","abb","caa","add","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2620_3013
["aaa","bbb","ccc","ddd","abb","caa","add","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2621_3013
["bbb","ccc","abb","baa","caa","add","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2622_3013
["aaa","bbb","ccc","abb","baa","caa","add","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2623_3013
["bbb","ccc","ddd","abb","baa","caa","add","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2624_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","add","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2625_3013
["bbb","baa","acc","caa","add","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2626_3013
["aaa","bbb","baa","acc","caa","add","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2627_3013
["aaa","bbb","ccc","baa","acc","caa","add","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2628_3013
["bbb","ddd","baa","acc","caa","add","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2629_3013
["aaa","bbb","ddd","baa","acc","caa","add","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2630_3013
["aaa","bbb","ccc","ddd","baa","acc","caa","add","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2631_3013
["bbb","abb","baa","acc","caa","add","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2632_3013
["aaa","bbb","abb","baa","acc","caa","add","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2633_3013
["bbb","ccc","abb","baa","acc","caa","add","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2634_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2635_3013
["bbb","ddd","abb","baa","acc","caa","add","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2636_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2637_3013
["bbb","ccc","ddd","abb","baa","acc","caa","add","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2638_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2639_3013
["bbb","abb","acc","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2640_3013
["aaa","bbb","abb","acc","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2641_3013
["bbb","ccc","abb","acc","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2642_3013
["aaa","bbb","ccc","abb","acc","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2643_3013
["bbb","ddd","abb","acc","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2644_3013
["aaa","bbb","ddd","abb","acc","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2645_3013
["bbb","ccc","ddd","abb","acc","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2646_3013
["aaa","bbb","ccc","ddd","abb","acc","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2647_3013
["bbb","baa","acc","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2648_3013
["aaa","bbb","baa","acc","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2649_3013
["aaa","bbb","ccc","baa","acc","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2650_3013
["aaa","bbb","ccc","ddd","baa","acc","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2651_3013
["bbb","abb","baa","acc","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2652_3013
["aaa","bbb","abb","baa","acc","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2653_3013
["bbb","ccc","abb","baa","acc","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2654_3013
["aaa","bbb","ccc","abb","baa","acc","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2655_3013
["bbb","ddd","abb","baa","acc","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2656_3013
["aaa","bbb","ddd","abb","baa","acc","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2657_3013
["bbb","ccc","ddd","abb","baa","acc","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2658_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2659_3013
["ccc","abb","baa","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2660_3013
["aaa","ccc","abb","baa","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2661_3013
["bbb","ccc","abb","baa","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2662_3013
["aaa","bbb","ccc","abb","baa","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2663_3013
["ccc","ddd","abb","baa","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2664_3013
["aaa","ccc","ddd","abb","baa","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2665_3013
["bbb","ccc","ddd","abb","baa","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2666_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2667_3013
["abb","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2668_3013
["aaa","abb","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2669_3013
["bbb","abb","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2670_3013
["aaa","bbb","abb","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2671_3013
["ccc","abb","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2672_3013
["aaa","ccc","abb","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2673_3013
["bbb","ccc","abb","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2674_3013
["aaa","bbb","ccc","abb","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2675_3013
["ddd","abb","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2676_3013
["aaa","ddd","abb","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2677_3013
["bbb","ddd","abb","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2678_3013
["aaa","bbb","ddd","abb","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2679_3013
["ccc","ddd","abb","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2680_3013
["aaa","ccc","ddd","abb","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2681_3013
["bbb","ccc","ddd","abb","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2682_3013
["aaa","bbb","ccc","ddd","abb","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2683_3013
["bbb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2684_3013
["aaa","bbb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2685_3013
["bbb","ccc","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2686_3013
["aaa","bbb","ccc","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2687_3013
["bbb","ddd","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2688_3013
["aaa","bbb","ddd","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2689_3013
["bbb","ccc","ddd","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2690_3013
["aaa","bbb","ccc","ddd","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2691_3013
["abb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2692_3013
["aaa","abb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2693_3013
["bbb","abb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2694_3013
["aaa","bbb","abb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2695_3013
["ccc","abb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2696_3013
["aaa","ccc","abb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2697_3013
["bbb","ccc","abb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2698_3013
["aaa","bbb","ccc","abb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2699_3013
["ddd","abb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2700_3013
["aaa","ddd","abb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2701_3013
["bbb","ddd","abb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2702_3013
["aaa","bbb","ddd","abb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2703_3013
["ccc","ddd","abb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2704_3013
["aaa","ccc","ddd","abb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2705_3013
["bbb","ccc","ddd","abb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2706_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2707_3013
["bbb","abb","baa","acc","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2708_3013
["aaa","bbb","abb","baa","acc","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2709_3013
["bbb","ccc","abb","baa","acc","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2710_3013
["aaa","bbb","ccc","abb","baa","acc","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2711_3013
["bbb","ddd","abb","baa","acc","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2712_3013
["aaa","bbb","ddd","abb","baa","acc","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2713_3013
["bbb","ccc","ddd","abb","baa","acc","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2714_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2715_3013
["ccc","abb","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2716_3013
["aaa","ccc","abb","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2717_3013
["bbb","ccc","abb","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2718_3013
["aaa","bbb","ccc","abb","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2719_3013
["ccc","ddd","abb","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2720_3013
["aaa","ccc","ddd","abb","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2721_3013
["bbb","ccc","ddd","abb","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2722_3013
["aaa","bbb","ccc","ddd","abb","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2723_3013
["bbb","ccc","baa","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2724_3013
["aaa","bbb","ccc","baa","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2725_3013
["aaa","bbb","ccc","ddd","baa","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2726_3013
["ccc","abb","baa","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2727_3013
["aaa","ccc","abb","baa","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2728_3013
["bbb","ccc","abb","baa","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2729_3013
["aaa","bbb","ccc","abb","baa","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2730_3013
["ccc","ddd","abb","baa","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2731_3013
["aaa","ccc","ddd","abb","baa","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2732_3013
["bbb","ccc","ddd","abb","baa","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2733_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2734_3013
["abb","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2735_3013
["aaa","abb","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2736_3013
["bbb","abb","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2737_3013
["aaa","bbb","abb","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2738_3013
["ccc","abb","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2739_3013
["aaa","ccc","abb","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2740_3013
["bbb","ccc","abb","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2741_3013
["aaa","bbb","ccc","abb","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2742_3013
["ddd","abb","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2743_3013
["aaa","ddd","abb","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2744_3013
["bbb","ddd","abb","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2745_3013
["aaa","bbb","ddd","abb","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2746_3013
["ccc","ddd","abb","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2747_3013
["aaa","ccc","ddd","abb","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2748_3013
["bbb","ccc","ddd","abb","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2749_3013
["aaa","bbb","ccc","ddd","abb","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2750_3013
["bbb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2751_3013
["aaa","bbb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2752_3013
["bbb","ccc","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2753_3013
["aaa","bbb","ccc","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2754_3013
["bbb","ddd","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2755_3013
["aaa","bbb","ddd","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2756_3013
["bbb","ccc","ddd","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2757_3013
["aaa","bbb","ccc","ddd","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2758_3013
["abb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2759_3013
["aaa","abb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2760_3013
["bbb","abb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2761_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2762_3013
["ccc","abb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2763_3013
["aaa","ccc","abb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2764_3013
["bbb","ccc","abb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2765_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2766_3013
["ddd","abb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2767_3013
["aaa","ddd","abb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2768_3013
["bbb","ddd","abb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2769_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2770_3013
["ccc","ddd","abb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2771_3013
["aaa","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2772_3013
["bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2773_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","bdd","cdd","abc","abd","acd","bcd"],
-- 2774_3013
["abb","baa","acc","caa","add","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2775_3013
["aaa","abb","baa","acc","caa","add","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2776_3013
["aaa","bbb","abb","baa","acc","caa","add","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2777_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2778_3013
["ddd","abb","baa","acc","caa","add","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2779_3013
["aaa","ddd","abb","baa","acc","caa","add","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2780_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2781_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2782_3013
["abb","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2783_3013
["aaa","abb","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2784_3013
["bbb","abb","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2785_3013
["aaa","bbb","abb","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2786_3013
["bbb","ccc","abb","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2787_3013
["aaa","bbb","ccc","abb","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2788_3013
["ddd","abb","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2789_3013
["aaa","ddd","abb","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2790_3013
["bbb","ddd","abb","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2791_3013
["aaa","bbb","ddd","abb","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2792_3013
["bbb","ccc","ddd","abb","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2793_3013
["aaa","bbb","ccc","ddd","abb","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2794_3013
["abb","baa","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2795_3013
["aaa","abb","baa","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2796_3013
["bbb","abb","baa","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2797_3013
["aaa","bbb","abb","baa","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2798_3013
["ccc","abb","baa","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2799_3013
["aaa","ccc","abb","baa","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2800_3013
["bbb","ccc","abb","baa","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2801_3013
["aaa","bbb","ccc","abb","baa","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2802_3013
["ddd","abb","baa","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2803_3013
["aaa","ddd","abb","baa","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2804_3013
["bbb","ddd","abb","baa","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2805_3013
["aaa","bbb","ddd","abb","baa","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2806_3013
["ccc","ddd","abb","baa","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2807_3013
["aaa","ccc","ddd","abb","baa","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2808_3013
["bbb","ccc","ddd","abb","baa","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2809_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2810_3013
["abb","baa","acc","caa","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2811_3013
["aaa","abb","baa","acc","caa","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2812_3013
["bbb","abb","baa","acc","caa","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2813_3013
["aaa","bbb","abb","baa","acc","caa","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2814_3013
["bbb","ccc","abb","baa","acc","caa","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2815_3013
["aaa","bbb","ccc","abb","baa","acc","caa","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2816_3013
["ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2817_3013
["aaa","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2818_3013
["bbb","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2819_3013
["aaa","bbb","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2820_3013
["bbb","ccc","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2821_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2822_3013
["abb","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2823_3013
["aaa","abb","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2824_3013
["bbb","abb","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2825_3013
["aaa","bbb","abb","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2826_3013
["bbb","ccc","abb","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2827_3013
["aaa","bbb","ccc","abb","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2828_3013
["ddd","abb","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2829_3013
["aaa","ddd","abb","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2830_3013
["bbb","ddd","abb","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2831_3013
["aaa","bbb","ddd","abb","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2832_3013
["bbb","ccc","ddd","abb","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2833_3013
["aaa","bbb","ccc","ddd","abb","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2834_3013
["bbb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2835_3013
["aaa","bbb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2836_3013
["bbb","ccc","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2837_3013
["aaa","bbb","ccc","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2838_3013
["bbb","ddd","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2839_3013
["aaa","bbb","ddd","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2840_3013
["bbb","ccc","ddd","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2841_3013
["aaa","bbb","ccc","ddd","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2842_3013
["abb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2843_3013
["aaa","abb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2844_3013
["bbb","abb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2845_3013
["aaa","bbb","abb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2846_3013
["ccc","abb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2847_3013
["aaa","ccc","abb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2848_3013
["bbb","ccc","abb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2849_3013
["aaa","bbb","ccc","abb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2850_3013
["ddd","abb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2851_3013
["aaa","ddd","abb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2852_3013
["bbb","ddd","abb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2853_3013
["aaa","bbb","ddd","abb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2854_3013
["ccc","ddd","abb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2855_3013
["aaa","ccc","ddd","abb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2856_3013
["bbb","ccc","ddd","abb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2857_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2858_3013
["bbb","ccc","baa","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2859_3013
["aaa","bbb","ccc","baa","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2860_3013
["aaa","bbb","ccc","ddd","baa","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2861_3013
["ccc","abb","baa","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2862_3013
["aaa","ccc","abb","baa","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2863_3013
["bbb","ccc","abb","baa","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2864_3013
["aaa","bbb","ccc","abb","baa","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2865_3013
["ccc","ddd","abb","baa","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2866_3013
["aaa","ccc","ddd","abb","baa","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2867_3013
["bbb","ccc","ddd","abb","baa","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2868_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2869_3013
["abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2870_3013
["aaa","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2871_3013
["bbb","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2872_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2873_3013
["bbb","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2874_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2875_3013
["ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2876_3013
["aaa","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2877_3013
["bbb","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2878_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2879_3013
["bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2880_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","cdd","abc","abd","acd","bcd"],
-- 2881_3013
["abb","baa","acc","caa","daa","bcc","dbb","cdd","abc","abd","acd","bcd"],
-- 2882_3013
["aaa","abb","baa","acc","caa","daa","bcc","dbb","cdd","abc","abd","acd","bcd"],
-- 2883_3013
["bbb","abb","baa","acc","caa","daa","bcc","dbb","cdd","abc","abd","acd","bcd"],
-- 2884_3013
["aaa","bbb","abb","baa","acc","caa","daa","bcc","dbb","cdd","abc","abd","acd","bcd"],
-- 2885_3013
["ccc","abb","baa","acc","caa","daa","bcc","dbb","cdd","abc","abd","acd","bcd"],
-- 2886_3013
["aaa","ccc","abb","baa","acc","caa","daa","bcc","dbb","cdd","abc","abd","acd","bcd"],
-- 2887_3013
["bbb","ccc","abb","baa","acc","caa","daa","bcc","dbb","cdd","abc","abd","acd","bcd"],
-- 2888_3013
["aaa","bbb","ccc","abb","baa","acc","caa","daa","bcc","dbb","cdd","abc","abd","acd","bcd"],
-- 2889_3013
["ddd","abb","baa","acc","caa","daa","bcc","dbb","cdd","abc","abd","acd","bcd"],
-- 2890_3013
["aaa","ddd","abb","baa","acc","caa","daa","bcc","dbb","cdd","abc","abd","acd","bcd"],
-- 2891_3013
["bbb","ddd","abb","baa","acc","caa","daa","bcc","dbb","cdd","abc","abd","acd","bcd"],
-- 2892_3013
["aaa","bbb","ddd","abb","baa","acc","caa","daa","bcc","dbb","cdd","abc","abd","acd","bcd"],
-- 2893_3013
["ccc","ddd","abb","baa","acc","caa","daa","bcc","dbb","cdd","abc","abd","acd","bcd"],
-- 2894_3013
["aaa","ccc","ddd","abb","baa","acc","caa","daa","bcc","dbb","cdd","abc","abd","acd","bcd"],
-- 2895_3013
["bbb","ccc","ddd","abb","baa","acc","caa","daa","bcc","dbb","cdd","abc","abd","acd","bcd"],
-- 2896_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","daa","bcc","dbb","cdd","abc","abd","acd","bcd"],
-- 2897_3013
["abb","baa","acc","caa","add","daa","bcc","dbb","cdd","abc","abd","acd","bcd"],
-- 2898_3013
["aaa","abb","baa","acc","caa","add","daa","bcc","dbb","cdd","abc","abd","acd","bcd"],
-- 2899_3013
["bbb","abb","baa","acc","caa","add","daa","bcc","dbb","cdd","abc","abd","acd","bcd"],
-- 2900_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","bcc","dbb","cdd","abc","abd","acd","bcd"],
-- 2901_3013
["bbb","ccc","abb","baa","acc","caa","add","daa","bcc","dbb","cdd","abc","abd","acd","bcd"],
-- 2902_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","bcc","dbb","cdd","abc","abd","acd","bcd"],
-- 2903_3013
["bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","dbb","cdd","abc","abd","acd","bcd"],
-- 2904_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","dbb","cdd","abc","abd","acd","bcd"],
-- 2905_3013
["abb","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2906_3013
["aaa","abb","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2907_3013
["aaa","bbb","abb","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2908_3013
["ccc","abb","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2909_3013
["aaa","ccc","abb","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2910_3013
["aaa","bbb","ccc","abb","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2911_3013
["ddd","abb","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2912_3013
["aaa","ddd","abb","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2913_3013
["aaa","bbb","ddd","abb","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2914_3013
["ccc","ddd","abb","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2915_3013
["aaa","ccc","ddd","abb","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2916_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2917_3013
["baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2918_3013
["aaa","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2919_3013
["aaa","bbb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2920_3013
["bbb","ccc","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2921_3013
["aaa","bbb","ccc","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2922_3013
["aaa","bbb","ccc","ddd","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2923_3013
["abb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2924_3013
["aaa","abb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2925_3013
["bbb","abb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2926_3013
["aaa","bbb","abb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2927_3013
["ccc","abb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2928_3013
["aaa","ccc","abb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2929_3013
["bbb","ccc","abb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2930_3013
["aaa","bbb","ccc","abb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2931_3013
["ddd","abb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2932_3013
["aaa","ddd","abb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2933_3013
["bbb","ddd","abb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2934_3013
["aaa","bbb","ddd","abb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2935_3013
["ccc","ddd","abb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2936_3013
["aaa","ccc","ddd","abb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2937_3013
["bbb","ccc","ddd","abb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2938_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2939_3013
["abb","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2940_3013
["aaa","abb","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2941_3013
["bbb","abb","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2942_3013
["aaa","bbb","abb","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2943_3013
["ccc","abb","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2944_3013
["aaa","ccc","abb","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2945_3013
["bbb","ccc","abb","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2946_3013
["aaa","bbb","ccc","abb","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2947_3013
["ddd","abb","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2948_3013
["aaa","ddd","abb","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2949_3013
["bbb","ddd","abb","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2950_3013
["aaa","bbb","ddd","abb","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2951_3013
["ccc","ddd","abb","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2952_3013
["aaa","ccc","ddd","abb","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2953_3013
["bbb","ccc","ddd","abb","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2954_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2955_3013
["abb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2956_3013
["aaa","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2957_3013
["bbb","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2958_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2959_3013
["ccc","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2960_3013
["aaa","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2961_3013
["bbb","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2962_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2963_3013
["ddd","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2964_3013
["aaa","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2965_3013
["bbb","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2966_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2967_3013
["ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2968_3013
["aaa","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2969_3013
["bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2970_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","dbb","cdd","abc","abd","acd","bcd"],
-- 2971_3013
["ccc","abb","baa","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 2972_3013
["aaa","ccc","abb","baa","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 2973_3013
["aaa","bbb","ccc","abb","baa","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 2974_3013
["aaa","bbb","ccc","ddd","abb","baa","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 2975_3013
["abb","baa","acc","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 2976_3013
["aaa","abb","baa","acc","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 2977_3013
["bbb","abb","baa","acc","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 2978_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 2979_3013
["ccc","abb","baa","acc","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 2980_3013
["aaa","ccc","abb","baa","acc","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 2981_3013
["bbb","ccc","abb","baa","acc","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 2982_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 2983_3013
["bbb","ddd","abb","baa","acc","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 2984_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 2985_3013
["bbb","ccc","ddd","abb","baa","acc","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 2986_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 2987_3013
["abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 2988_3013
["aaa","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 2989_3013
["bbb","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 2990_3013
["aaa","bbb","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 2991_3013
["aaa","ccc","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 2992_3013
["bbb","ccc","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 2993_3013
["aaa","bbb","ccc","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 2994_3013
["bbb","ddd","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 2995_3013
["aaa","bbb","ddd","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 2996_3013
["aaa","bbb","ccc","ddd","abb","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 2997_3013
["abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 2998_3013
["aaa","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 2999_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 3000_3013
["ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 3001_3013
["aaa","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 3002_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 3003_3013
["ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 3004_3013
["aaa","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 3005_3013
["aaa","bbb","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 3006_3013
["ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 3007_3013
["aaa","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 3008_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","abc","abd","acd","bcd"],
-- 3009_3013
["abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd","bcd"],
-- 3010_3013
["aaa","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd","bcd"],
-- 3011_3013
["aaa","bbb","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd","bcd"],
-- 3012_3013
["aaa","bbb","ccc","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd","bcd"],
-- 3013_3013
["aaa","bbb","ccc","ddd","abb","baa","acc","caa","add","daa","bcc","cbb","bdd","dbb","cdd","dcc","abc","abd","acd","bcd"]
]]

#eval ra5[8].length
