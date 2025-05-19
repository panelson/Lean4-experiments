import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Relator
import Mathlib.Tactic.Use
import Mathlib.Tactic.MkIffOfInductiveProp
import Mathlib.Tactic.SimpRw

variable {X : Type u} (R S T : Set (X × X))
variable (t u v w x y z : Set (X × X))

def com (R S : Set (X × X)) : Set (X × X) :=
  { (x, y) | ∃ z, (x, z) ∈ R ∧ (z, y) ∈ S }

def inv (R : Set (X × X)) : Set (X × X) :=
  { (y, x) | (x, y) ∈ R }

infixl:90 " ; "  => com

postfix:100 "⁻¹" => inv

theorem comp_assoc : (R ; S) ; T = R ; (S ; T) := by
  rw [Set.ext_iff]
  intro (a,b)
  constructor
  · intro h
    rcases h with ⟨z, h₁, _⟩
    rcases h₁ with ⟨x,_,_⟩
    use x
    constructor
    trivial
    use z
  · intro h₂
    rcases h₂ with ⟨x, h₃, h₄⟩
    rcases h₄ with ⟨y,_,_⟩
    use y
    constructor
    use x
    trivial

theorem rdist : (R ∪ S) ; T = R ; T ∪ S ; T := by
  rw [Set.ext_iff]
  intro (a,b)
  constructor
  · intro h
    rcases h with ⟨c, h₁, h₂⟩
    rcases h₁
    have h₃ : (a,b) ∈ R ; T := by use c
    constructor
    trivial
  · intro h
    rcases h
    rcases









theorem comp_assoc1 : (r ∘r p) ∘r q = r ∘r p ∘r q := by
  funext a d
  --apply propext
  constructor
  · exact fun ⟨c, ⟨b, hab, hbc⟩, hcd⟩ ↦ ⟨b, hab, c, hbc, hcd⟩
  · exact fun ⟨b, hab, c, hbc, hcd⟩ ↦ ⟨c, ⟨b, hab, hbc⟩, hcd⟩


def isJtrue (t u v w x y z : Set (X × X)) : Prop :=
  t ⊆ u;v ∩ w;x  ∧  u⁻¹;w ∩ v;x⁻¹ ⊆ y;z → t ⊆ (u;y ∩ w;z⁻¹);(y⁻¹;v ∩ x;z)

def isLtrue (u v w x y z : Set (X × X)) : Prop :=
  x;y ∩ z;w ∩ u;v ⊆ x;((x⁻¹;z ∩ y;w⁻¹);(z⁻¹;u ∩ w;v⁻¹) ∩ x⁻¹;u ∩ y;v⁻¹);v

def isMtrue (t u v w x y z : Set (X × X)) : Prop :=
  t ∩ (u ∩ v;w);(x ∩ y;z) ⊆ v;((v⁻¹;t ∩ w;x);z ∩ w;y ∩ v⁻¹;(u;y ∩ t;z⁻¹));z

variable {X : Type}(t u v w x y z : Set (X × X))

theorem Mtrue :
  t ∩ (u ∩ v ; w) ; (x ∩ y;z) ⊆ v;((v⁻¹;t ∩ w;x);z⁻¹ ∩ w;y ∩ v⁻¹;(u;y ∩ t;z⁻¹));z := by
  intro (a,b)
  intro h
  rcases h with ⟨h1,h2⟩
  rcases h2 with ⟨c,h1,h2⟩
  rcases h1 with ⟨h3,h4⟩
  rcases h4 with ⟨d,h5,h6⟩
  rcases h2 with ⟨h7,h8⟩
  rcases h8 with ⟨e,h9,h10⟩
  use e
  constructor
  use d
  constructor
  trivial
  constructor
  constructor
  use b
  constructor
  constructor
  use a
  constructor
  rw [inv]
  dsimp
  trivial
  trivial
  use c
  rw [inv]
  dsimp
  trivial
  use c
  use a
  constructor
  rw [inv]
  dsimp
  trivial
  constructor
  use c
  use b
  constructor
  trivial
  rw [inv]
  dsimp
  trivial
  trivial

theorem Jtrue :
  t ⊆ u;v ∩ w;x  ∧  u⁻¹;w ∩ v;x⁻¹ ⊆ y;z → t ⊆ (u;y ∩ w;z⁻¹);(y⁻¹;v ∩ z;x) := by
  intro h
  intro (a,b)
  intro h₁
  rcases h with ⟨h₂,h₃⟩
  have h₄ : (a, b) ∈ u ; v ∩ w ; x := Set.mem_of_mem_of_subset h₁ h₂
  rcases h₄ with ⟨h₅, h₆⟩
  rcases h₅ with ⟨c, h₇, h₈⟩
  rcases h₆ with ⟨d, h₉, H₁⟩
  have H₂ : (c, a) ∈ u⁻¹ := by rw [inv]; dsimp; trivial
  have H₃ : (c, d) ∈ u⁻¹ ; w := by use a
  have H₄ : (b, d) ∈ x⁻¹ := by rw [inv]; dsimp; trivial
  have H₅ : (c, d) ∈ v ; x⁻¹ := by use b
  have H₆ : (c, d) ∈ u⁻¹ ; w ∩ v ; x⁻¹ := by constructor; trivial; trivial
  have H₇ : (c, d) ∈ y ; z := Set.mem_of_mem_of_subset H₆ h₃
  rcases H₇ with ⟨e, H₈, H₉⟩
  use e
  constructor
  constructor
  use c
  constructor
  trivial
  constructor
  use c
  constructor
  rw [inv]
  dsimp
  trivial
  trivial
  use d

theorem Ltrue :
  x;y ∩ z;w ∩ u;v ⊆ x;((x⁻¹;z ∩ y;w⁻¹);(z⁻¹;u ∩ w;v⁻¹) ∩ x⁻¹;u ∩ y;v⁻¹);v := by
  intro (a,b)
  intro h
  rcases h with ⟨h1, h2⟩
  rcases h1 with ⟨h3,h4⟩
  rcases h3 with ⟨e, h3, h5⟩
  rcases h4 with ⟨d, h3, h4⟩
  rcases h2 with ⟨c, h6, h7⟩
  use c
  constructor
  use e
  constructor
  trivial
  constructor
  constructor
  use d
  constructor
  constructor
  use a
  constructor
  rw [inv]
  dsimp
  trivial
  trivial
  use b
  constructor
  trivial
  rw [inv]
  dsimp
  trivial
  constructor
  use a
  constructor
  rw [inv]
  dsimp
  trivial
  trivial
  use b
  constructor
  trivial
  rw [inv]
  dsimp
  trivial
  use a
  constructor
  rw [inv]
  dsimp
  trivial
  trivial
  use b
  constructor
  trivial
  rw [inv]
  dsimp
  trivial
  trivial
