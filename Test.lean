import Mathlib.Logic.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Order.ModularLattice

#check CommRing (ZMod 3)

#eval (1 : ZMod 3)+2

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

class Group₂ (G : Type*) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ x y z : G, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : G, mul x one = x
  one_mul : ∀ x : G, mul one x = x
  inv_mul_cancel : ∀ x : G, mul (inv x) x = one

instance {G : Type*} : Group₂ (Equiv.Perm G) where
  mul f g := Equiv.trans g f
  one := Equiv.refl G
  inv := Equiv.symm
  mul_assoc _ _ _ := (Equiv.trans_assoc _ _ _).symm
  one_mul := Equiv.trans_refl
  mul_one := Equiv.refl_trans
  inv_mul_cancel := Equiv.self_trans_symm

#check Group₂.mul

def mySquare {G : Type*} [Group₂ G] (x : G) :=
  Group₂.mul x x

#check mySquare

section
variable {X : Type*} (f g : Equiv.Perm X)

example : Group₂.mul f g = g.trans f :=
  rfl

example : mySquare f = f.trans f :=
  rfl

end


inductive Z₂: Type | e:Z₂ | a:Z₂
--export Z₂ (e a)
open Z₂
def add:  Z₂ → Z₂ → Z₂ := fun | e, x => x  | x, e => x | a, a => a

inductive Z₂': Type | e:Z₂' | a:Z₂' | b:Z₂'

lemma add_zero': add x e = x := by cases x <;> rfl
lemma zero_add': add e x = x := by cases x <;> rfl
lemma assoc: add (add x y) z = add x (add y z) := by cases x <;> cases y <;> cases z <;> rfl
lemma idem: add x x = x := by cases x <;> rfl

class Semigroup' {A : Type u} (o : A → A → A) where   --Semigroups
(assoc: o (o x y) z = o x (o y z))

instance: Semigroup' add := ⟨assoc⟩




class CSgrp{α:Type u}(o:α→α → α) extends Sgrp o :=      --Commutative semigroups
(comm: commutative o)

class Band {α:Type u}(m:α→α → α) extends Sgrp m :=      --Bands
(idem: idempotent m)

class Slat {α:Type u}(m:α→α → α) extends Band m :=      --Semiattices
(comm: commutative m)
-- how to tell Lean that every Slat is an idempotent CSgrp?

class Lat {α:Type u}(j:α→α → α)(m:α→α → α) :=           --Lattices
(asso_j: associative j)(asso_m: associative m)
(comm_j: commutative j)(comm_m: commutative m)
(abs_jm: absorption j m)(abs_mj: absorption m j)

class Mon {α:Type u}(o:α→α → α)(e:α) extends Sgrp o :=  --Monoids
(l_id: l_identity o e)
(r_id: r_identity o e)

class CMon {α:Type u}(o:α→α → α)(e:α) extends Mon o e :=--Commutative monoids
(comm: commutative o)

class Grp {α:Type u}(o:α→α → α)(i:α → α)(e:α) extends Sgrp o := --Groups
(l_id:  l_identity o e)
(l_inv: l_inverse o i e)

instance: Band add := ⟨⟨add_assoc⟩, add_idem⟩
instance: Mon add e := ⟨⟨add_assoc⟩, zero_add, add_zero⟩

end Z₂


-- In a comment at the top of Prelude.lean (left over from Lean 3?):
--show T' from e

-- Define the pentagon lattice N₅
def N₅ : Type := Fin 5

-- Define the lattice structure on N₅
instance : Lattice N₅ where
  le a b := a = 0 ∨ b = 1 ∨ (a = 2 ∧ b = 2) ∨ (a = 3 ∧ b = 3) ∨ (a = 4 ∧ b = 4)
  le_refl a := by cases a <;> simp
  le_trans a b c hab hbc := by cases a <;> cases b <;> cases c <;> simp [*]
  le_antisymm a b hab hba := by cases a <;> cases b <;> simp [*]
  sup a b :=
    if a = 0 then b
    else if b = 0 then a
    else if a = 1 ∨ b = 1 then 1
    else if a = 2 ∨ b = 2 then 2
    else if a = 3 ∨ b = 3 then 3
    else 4
  inf a b :=
    if a = 1 then b
    else if b = 1 then a
    else if a = 0 ∨ b = 0 then 0
    else if a = 2 ∨ b = 2 then 2
    else if a = 3 ∨ b = 3 then 3
    else 4

-- Prove that N₅ is non-modular
lemma N₅_non_modular : ¬ IsModularLattice N₅ := by
  intro h
  have h_mod : ∀ x y z : N₅, x ≤ z → (x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ z) := h.modular_law
  specialize h_mod 0 2 1 (by simp)
  simp at h_mod
  contradiction

-- Main theorem: If a lattice is not modular, it contains a copy of N₅
theorem contains_N₅_if_not_modular (L : Type*) [Lattice L] :
    ¬ IsModularLattice L → ∃ (f : N₅ → L), Function.Injective f ∧ ∀ a b : N₅, a ≤ b ↔ f a ≤ f b := by
  intro h_not_mod
  -- Use the fact that non-modularity implies the existence of a pentagon sublattice
  obtain ⟨x, y, z, hxz, h_neq⟩ := exists_three_elements_violating_modular_law h_not_mod
  let a := x ⊔ (y ⊓ z)
  let b := (x ⊔ y) ⊓ z
  let c := y
  let zero := y ⊓ z
  let one := x ⊔ y
  -- Define the embedding f : N₅ → L
  let f : N₅ → L := λ i =>
    match i with
    | 0 => zero
    | 1 => a
    | 2 => b
    | 3 => c
    | 4 => one
  -- Prove that f is injective and preserves order
  refine ⟨f, ?_, ?_⟩
  · -- Injectivity
    intro i j hf
    cases i <;> cases j <;> simp [f] at hf <;> try contradiction
    all_goals rfl
  · -- Order preservation
    intro i j
    cases i <;> cases j <;> simp [f, zero, a, b, c, one]
    -- Prove the necessary inequalities and equalities
    all_goals
      try apply le_refl
      try apply le_sup_left
      try apply le_sup_right
      try apply inf_le_left
      try apply inf_le_right
      try assumption
