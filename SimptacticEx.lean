import Mathlib.Algebra.Group.Defs

variable (G : Type) [Group G] (a b c : G)

example : a * a⁻¹ * 1 * b = b * c * c⁻¹ := by
  simp

  /-
  NOTE: if proof for lemma is reflexive (rfl), can use dsimp instead of simp.

  Simp just simplifies the hypothesis by checking the database for applicable lemmas and using them to reduce the hypothesis as much as possible, from left to right

  Behind the scene:

  [Meta.Tactic.simp.rewrite] @mul_right_inv:1000, a * a⁻¹ ==> 1

  [Meta.Tactic.simp.rewrite] @mul_one:1000, 1 * 1 ==> 1

  [Meta.Tactic.simp.rewrite] @one_mul:1000, 1 * b ==> b

  [Meta.Tactic.simp.rewrite] @mul_inv_cancel_right:1000, b * c * c⁻¹ ==> b

  [Meta.Tactic.simp.rewrite] @eq_self:1000, b = b ==> True
  -/
