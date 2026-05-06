import Mathlib
open MeasureTheory

lemma test : (∀ᵐ x : ℝ ∂volume, x ≠ 0) := by
  refine (ae_iff).2 ?_
  simpa using (MeasureTheory.NoAtoms.measure_singleton (μ := volume) (0 : ℝ))
