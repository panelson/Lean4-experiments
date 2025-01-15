/-Import not necessary, couldnt find right one so I just copied the function for continuity-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

def IsContinuousAt (D : Set ℝ) (f : D → ℝ) (a : D) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : D, (|x.val - a.val| < δ  →  |f x - f a| < ε)

def IsContinuous (D : Set ℝ) (f : D → ℝ) : Prop :=
  ∀ a : D, IsContinuousAt D f a

theorem constant_function_cont_at_a_point (D : Set ℝ) (c : ℝ) (a : D): IsContinuousAt D (fun _ ↦ c ) a:= by
  dsimp [IsContinuousAt] --dsimp is used because rlf proof
  intro ε hεbigger0
  exists 1
  simp only [one_pos, true_and]
  intro x _h_xδ_criterion
  simp only [sub_self, abs_zero]
  exact hεbigger0

theorem constant_function_is_continuous (D : Set ℝ) (c : ℝ): IsContinuous D (fun _ ↦ c) := by
  intro a
  exact constant_function_cont_at_a_point D c a
