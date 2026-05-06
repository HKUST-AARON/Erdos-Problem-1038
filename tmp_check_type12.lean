import Mathlib
example (f : ℝ → ℝ≥0∞) (μ : MeasureTheory.Measure ℝ) (s : Set ℝ) : (∫⁻ x : ℝ in s, f x ∂μ) = ∫⁻ x : ℝ, f x ∂(μ.restrict s) := by
  rfl
