import Mathlib.Data.Set.Basic

variable {X : Type u} (R S T : Set (X × X))
variable (t u v w x y z : Set (X × X))

def com (R S : Set (X × X)) : Set (X × X) :=
  { (x, y) | ∃ z, (x, z) ∈ R ∧ (z, y) ∈ S }

def inv (R : Set (X × X)) : Set (X × X) :=
  { (y, x) | (x, y) ∈ R }

infixl:90 " ; "  => com

postfix:100 "⁻¹" => inv

theorem comp_assoc : (a, b) ∈ (R ; S) ; T → (a, b) ∈ R ; (S ; T) := by
  intro h
  rcases h with ⟨z, h₁, _⟩
  rcases h₁ with ⟨x,_,_⟩
  use x
  constructor
  trivial
  use z


def isJtrue (t u v w x y z : Set (X × X)) : Prop :=
  t ≤ u;v ∩ w;x  ∧  u⁻¹;w ∩ v;x⁻¹ ⊆ y;z → t ≤ (u;y ∩ w;z⁻¹);(y⁻¹;v ∩ x;z)

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
  t ⊆ u;v ∩ w;x  ∧  u⁻¹;w ∩ v;x⁻¹ ⊆ y;z → t ⊆ (u;y ∩ w;z⁻¹);(y⁻¹;v ∩ x;z) := by
  intro h
  intro (a,b)
  intro h₁
  rcases h with ⟨h2,h3⟩
  sorry

theorem Ltrue :
  x;y ∩ z;w ∩ u;v ⊆ x;((x⁻¹;z ∩ y;w⁻¹);(z⁻¹;u ∩ w;v⁻¹) ∩ x⁻¹;u ∩ y;v⁻¹);v := by
  intro (a,b)
  intro h
  rcases h with ⟨h1, h2⟩
  rcases h1 with ⟨h3,h4⟩
  rcases h3 with ⟨e, h3, h5⟩
  rcases h4 with ⟨d, h3, h4⟩
  rcases h2 with ⟨c, h1, h2⟩
  use e
  constructor
  use d
  constructor




  sorry
