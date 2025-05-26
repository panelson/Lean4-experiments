import Mathlib.Order.Lattice
import Mathlib.Tactic.Tauto

/--
C₂ denotes the set {0,1} viewed as a (complete) lattice, which in Lean is constructed
from Prop, so 0 is denoted as ⊥ and 1 is denoted as ⊤
--/

inductive C₂ : Type where | a0 : C₂ | a1 : C₂
instance latticeC₂ : Lattice C₂ where
  le  := fun | C₂.a1, C₂.a0 => False | _, _ => True
  sup := fun | C₂.a0, C₂.a0 => C₂.a0 | _, _ => C₂.a1
  inf := fun | C₂.a1, C₂.a1 => C₂.a1 | _, _ => C₂.a0
  le_refl      := by intro x; cases x; trivial; trivial
  le_trans     := by intro x y z; cases x <;> cases y <;> simp
  le_antisymm  := by intro x y; cases x <;> cases y <;> tauto
  le_sup_left  := by intro x y; cases x <;> tauto
  le_sup_right := by intro x y; cases x <;> cases y <;> tauto
  sup_le       := by intro x y z; cases x <;> cases y <;> cases z <;> tauto
  inf_le_left  := by intro x y; cases x <;> cases y <;> tauto
  inf_le_right := by intro x y; cases x <;> cases y <;> tauto
  le_inf       := by intro x y z; cases x <;> cases y <;> cases z <;> tauto

inductive C₃ : Type where | a0 : C₃ | a1 : C₃ | a2 : C₃
instance latticeC₃ : Lattice C₃ where
  le  := fun
    | C₃.a1, C₃.a0 => False | C₃.a2, C₃.a1 => False | C₃.a2, C₃.a0 => False
    | _, _ => True
  sup := fun
    | C₃.a0, C₃.a0 => C₃.a0 | C₃.a1, C₃.a0 => C₃.a1 | C₃.a0, C₃.a1 => C₃.a1
    | C₃.a1, C₃.a1 => C₃.a1 | _, _ => C₃.a2
  inf := fun
    | C₃.a2, C₃.a2 => C₃.a2 | C₃.a1, C₃.a2 => C₃.a1 | C₃.a2, C₃.a1 => C₃.a1
    | C₃.a1, C₃.a1 => C₃.a1 | _, _ => C₃.a0
  le_refl      := by intro x; cases x <;> trivial
  le_trans     := by intro x y z; cases x <;> cases y <;> cases z <;> simp
  le_antisymm  := by intro x y; cases x <;> cases y <;> tauto
  le_sup_left  := by intro x y; cases x <;> cases y <;> tauto
  le_sup_right := by intro x y; cases x <;> cases y <;> tauto
  sup_le       := by intro x y z; cases x <;> cases y <;> cases z <;> tauto
  inf_le_left  := by intro x y; cases x <;> cases y <;> tauto
  inf_le_right := by intro x y; cases x <;> cases y <;> tauto
  le_inf       := by intro x y z; cases x <;> cases y <;> cases z <;> tauto

#print Preorder

instance preorder : Preorder C₂ where
  le := fun | C₂.a1, C₂.a0 => False | _, _ => True
  le_refl := by intro x ; cases x ; trivial ; trivial
  le_trans := by intro x y z ; cases x <;> cases y <;> cases z <;> simp
  --lt_iff_le_not_le := by intro x y; cases x <;> cases y <;> simp

/-instance poset : PartialOrder C₂ where
  le_antisymm := by intro x y; cases x <;> cases y <;> tauto

instance joinsemilattice : SemilatticeSup C₂ where
  sup := fun | C₂.a0, C₂.a0 => C₂.a0 | _, _ => C₂.a1
  le_sup_left := by intro x y ; cases x <;> tauto
  le_sup_right := by intro x y ; cases x <;> cases y <;> tauto
  sup_le := by intro x y ; cases x <;> cases y <;> tauto

instance meetsemilattice : SemilatticeInf C₂ where
  inf := fun | C₂.a1, C₂.a1 => C₂.a1 | _, _ => C₂.a0
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

instance Bool.instBooleanAlgebra1 : BooleanAlgebra Bool where
  __ := instDistribLattice1
  __ := linearOrder
  __ := instBoundedOrder
  compl := not
  inf_compl_le_bot a := a.and_not_self.le
  top_le_sup_compl a := a.or_not_self.ge
