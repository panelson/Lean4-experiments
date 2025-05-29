import Mathlib.Order.Lattice
import Mathlib.Order.ModularLattice
import Mathlib.Tactic.Tauto
import Mathlib.Order.BooleanAlgebra

/--
C₂ denotes the set {0,1} viewed as a (complete) lattice, which in Lean is constructed
from Prop, so 0 is denoted as ⊥ and 1 is denoted as ⊤
--/

inductive C₂ : Type where | a₀ : C₂ | a₁ : C₂
instance latticeC₂ : Lattice C₂ where
  le  := fun | C₂.a₁, C₂.a₀ => False | _, _ => True
  sup := fun | C₂.a₀, C₂.a₀ => C₂.a₀ | _, _ => C₂.a₁
  inf := fun | C₂.a₁, C₂.a₁ => C₂.a₁ | _, _ => C₂.a₀
  le_refl      := by intro x; cases x; trivial; trivial
  le_trans     := by intro x y z; cases x <;> cases y <;> simp
  le_antisymm  := by intro x y; cases x <;> cases y <;> tauto
  le_sup_left  := by intro x y; cases x <;> tauto
  le_sup_right := by intro x y; cases x <;> cases y <;> tauto
  sup_le       := by intro x y z; cases x <;> cases y <;> cases z <;> tauto
  inf_le_left  := by intro x y; cases x <;> cases y <;> tauto
  inf_le_right := by intro x y; cases x <;> cases y <;> tauto
  le_inf       := by intro x y z; cases x <;> cases y <;> cases z <;> simp

inductive C₃ : Type where | a₀ : C₃ | a₁ : C₃ | a₂ : C₃
instance latticeC₃ : Lattice C₃ where
  le  := fun
    | C₃.a₁, C₃.a₀ => False | C₃.a₂, C₃.a₁ => False | C₃.a₂, C₃.a₀ => False
    | _, _ => True
  sup := fun
    | C₃.a₀, C₃.a₀ => C₃.a₀ | C₃.a₁, C₃.a₀ => C₃.a₁ | C₃.a₀, C₃.a₁ => C₃.a₁
    | C₃.a₁, C₃.a₁ => C₃.a₁ | _, _ => C₃.a₂
  inf := fun
    | C₃.a₂, C₃.a₂ => C₃.a₂ | C₃.a₁, C₃.a₂ => C₃.a₁ | C₃.a₂, C₃.a₁ => C₃.a₁
    | C₃.a₁, C₃.a₁ => C₃.a₁ | _, _ => C₃.a₀
  le_refl      := by intro x; cases x <;> trivial
  le_trans     := by intro x y z; cases x <;> cases y <;> cases z <;> simp
  le_antisymm  := by intro x y; cases x <;> cases y <;> tauto
  le_sup_left  := by intro x y; cases x <;> cases y <;> tauto
  le_sup_right := by intro x y; cases x <;> cases y <;> tauto
  sup_le       := by intro x y z; cases x <;> cases y <;> cases z <;> tauto
  inf_le_left  := by intro x y; cases x <;> cases y <;> tauto
  inf_le_right := by intro x y; cases x <;> cases y <;> tauto
  le_inf       := by intro x y z; cases x <;> cases y <;> cases z <;> simp

set_option maxHeartbeats 300000

inductive N₅ : Type where | z : N₅ | a : N₅ | b : N₅ | c : N₅ | t : N₅
open N₅
instance latticeN₅ : Lattice N₅ where
  le  := fun
    | a, z => False | a, b => False | b, z => False | b, a => False
    | b, c => False | c, z => False | c, a => False | c, b => False
    | t, z => False | t, a => False | t, b => False | t, c => False
    | _, _ => True
  sup := fun
    | z, z => z | z, a => a | z, b => b | z, c => c
    | a, z => a | a, a => a | a, b => t | a, c => c
    | b, z => b | b, a => t | b, b => b | b, c => t
    | c, z => c | c, a => c | c, b => t | c, c => c
    | _, _ => t
  inf := fun
    | a, a => a | a, b => z | a, c => a | a, t => a
    | b, a => z | b, b => b | b, c => z | b, t => b
    | c, a => a | c, b => z | c, c => c | c, t => c
    | t, a => a | t, b => b | t, c => c | t, t => t
    | _, _ => z
  le_refl      := by intro x; cases x <;> trivial
  le_trans     := by intro x y z; cases x <;> cases y <;> cases z <;> simp
  le_antisymm  := by intro x y; cases x <;> cases y <;> tauto
  le_sup_left  := by intro x y; cases x <;> cases y <;> tauto
  le_sup_right := by intro x y; cases x <;> cases y <;> tauto
  sup_le       := by intro x y z; cases x <;> cases y <;> cases z <;> simp
  inf_le_left  := by intro x y; cases x <;> cases y <;> tauto
  inf_le_right := by intro x y; cases x <;> cases y <;> tauto
  le_inf       := by intro x y z; cases x <;> cases y <;> cases z <;> simp

theorem N₅notModular : ¬ (IsModularLattice N₅) := by
  intro h
  sorry

--#eval IsModularLattice N₅

#print BooleanAlgebra
#print latticeC₃

instance preorder : Preorder C₂ where
  le := fun | C₂.a₁, C₂.a₀ => False | _, _ => True
  le_refl := by intro x ; cases x ; trivial ; trivial
  le_trans := by intro x y z ; cases x <;> cases y <;> cases z <;> simp
  --lt_iff_le_not_le := by intro x y; cases x <;> cases y <;> simp

/-instance poset : PartialOrder C₂ where
  le_antisymm := by intro x y; cases x <;> cases y <;> tauto

instance joinsemilattice : SemilatticeSup C₂ where
  sup := fun | C₂.a₀, C₂.a₀ => C₂.a₀ | _, _ => C₂.a₁
  le_sup_left := by intro x y ; cases x <;> tauto
  le_sup_right := by intro x y ; cases x <;> cases y <;> tauto
  sup_le := by intro x y ; cases x <;> cases y <;> tauto

instance meetsemilattice : SemilatticeInf C₂ where
  inf := fun | C₂.a₁, C₂.a₁ => C₂.a₁ | _, _ => C₂.a₀
  inf_le_left := by intro x y ; cases x <;> cases y <;> tauto
  inf_le_right := by intro x y ; cases x <;> cases y <;> tauto
  le_inf := by intro x y z ; cases x <;> cases y <;> cases z <;> tauto
-/


instance Bool.linearOrder1 : LinearOrder Bool where
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
  le_total := by decide
  decidableLE := inferInstance
  decidableEq := inferInstance
  decidableLT := inferInstance
  lt_iff_le_not_le := by decide
  max_def := by decide
  min_def := by decide

instance instCompleteLatticeC₂ : CompleteLattice C₂ := inferInstance

#print PartialOrder

instance instDistribLattice2 : DistribLattice Two :=
  inferInstance

instance Bool.instDistribLattice1 : DistribLattice Bool :=
  inferInstance

#eval false < true
#eval (false ≤ true)

instance Bool.instBooleanAlgebra₁ : BooleanAlgebra Bool where
  __ := instDistribLattice1
  __ := linearOrder
  __ := instBoundedOrder
  compl := not
  inf_compl_le_bot a := a.and_not_self.le
  top_le_sup_compl a := a.or_not_self.ge
