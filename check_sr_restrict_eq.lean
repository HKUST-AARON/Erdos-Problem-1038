import Mathlib

open MeasureTheory

example (ε : ℝ) (hε : 0 < ε) (f : ℝ → ℝ) :
    (∫ x : ℝ, f x ∂(volume.restrict (Set.Ioo (-ε) ε))) = ∫ x : ℝ in Set.Ioo (-ε) ε, f x ∂volume := by
  simp

example (ε : ℝ) (hε : 0 < ε) (f : ℝ → ℝ) :
    (∫ x : ℝ, f x ∂(volume.restrict (Set.Ioo (-ε) ε))) = ∫ x in Set.Ioo (-ε) ε, f x ∂volume := by
  -- maybe by integral_indicator
  simp [MeasureTheory.integral_indicator, isOpen_Ioo.measurableSet]
