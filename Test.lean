import Mathlib.Logic.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.ZMod.Defs

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
