import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Defs.LinearOrder

/--
C₂ denotes the set {0,1} viewed as a (complete) lattice, which in Lean is constructed
from Prop, so 0 is denoted as ⊥ and 1 is denoted as ⊤
--/

inductive C₂ : Type where | a0 : C₂ | a1 : C₂

def C₂.jn (x y : C₂) : C₂ :=
  match x with
  | C₂.a1 => C₂.a1
  | C₂.a0 => y

#print PartialOrder

--instance instLE : LE C₂ := ⟨C₂.le⟩
--instance : LT C₂ := ⟨C₂.lt⟩


instance preorder : Preorder C₂ where
  le := fun | C₂.a1, C₂.a0 => False | _, _ => True 
  le_refl := by intro x ; cases x ; trivial ; trivial
  le_trans := by intro x y z ; cases x <;> cases y <;> cases z <;> simp
  lt_iff_le_not_le := by intro x y; cases x <;> cases y <;> simp

--open Classical

instance poset : PartialOrder C₂ where
  le_antisymm := by 
    intro x y; cases x <;> cases y <;> aesop



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
