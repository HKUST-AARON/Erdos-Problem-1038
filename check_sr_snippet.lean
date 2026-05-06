import Mathlib

open MeasureTheory
open scoped ENNReal

lemma test_posInt (ε : ℝ) (hεpos : 0 < ε) :
    (∫ (x : ℝ) in 0..ε, Real.log (ε / |x|) ∂volume) = ε := by
  have hlog_eq : ∀ᵐ x ∂volume, x ∈ Set.uIoc 0 ε → Real.log (ε / |x|) = Real.log ε - Real.log x := by
    refine Filter.Eventually.of_forall ?_
    intro x hx
    have hx' : 0 < x ∧ x ≤ ε := by
      simpa [Set.uIoc_of_le hεpos.le] using hx
    have hxab : |x| = x := abs_of_pos hx'.1
    calc
      Real.log (ε / |x|) = Real.log (ε / x) := by simpa [hxab]
      _ = Real.log ε - Real.log x := by
            rw [Real.log_div hεpos.ne' (ne_of_gt hx'.1)]
  have hconst : IntervalIntegrable (fun _ : ℝ => Real.log ε) volume 0 ε :=
    intervalIntegral.intervalIntegrable_const
  have hlog : IntervalIntegrable (fun x : ℝ => Real.log x) volume 0 ε :=
    intervalIntegral.intervalIntegrable_log'
  have hconstInt : (∫ (x : ℝ) in 0..ε, (fun x : ℝ => Real.log ε) x ∂volume) = (ε - 0) * Real.log ε := by
    simpa [smul_eq_mul] using (intervalIntegral.integral_const (μ := volume) (c := Real.log ε) (a := 0) (b := ε))
  calc
    (∫ (x : ℝ) in 0..ε, Real.log (ε / |x|) ∂volume)
        = ∫ (x : ℝ) in 0..ε, (fun x => Real.log ε - Real.log x) x ∂volume := by
            exact intervalIntegral.integral_congr_ae hlog_eq
    _ = ∫ (x : ℝ) in 0..ε, (fun _ : ℝ => Real.log ε) x ∂volume -
        ∫ (x : ℝ) in 0..ε, (fun x => Real.log x) x ∂volume := by
            simpa [sub_eq_add_neg] using intervalIntegral.integral_sub hconst hlog
    _ = (ε - 0) * Real.log ε - (ε * Real.log ε - ε) := by
          rw [hconstInt, integral_log_from_zero_of_pos hεpos]
    _ = ε := by
          ring
