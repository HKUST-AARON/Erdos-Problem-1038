import Mathlib
open MeasureTheory

example : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
  simp

example : ∀ᵐ x : ℝ ∂volume, x = 0 := by
  simp
