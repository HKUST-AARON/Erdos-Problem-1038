import Mathlib

example {ε : ℝ} (hε : 0 < ε) (x : ℝ) (hx : x ∈ Set.uIoc 0 ε) : x ∈ Set.Icc (0:ℝ) ε := by
  simpa [Set.uIoc_of_le hε.le] using hx

example {ε : ℝ} (hε : 0 < ε) (x : ℝ) (hx : x ∈ Set.uIoc 0 ε) : x ∈ Set.Ioo (0:ℝ) ε := by
  simpa [Set.uIoc_of_le hε.le] using hx
