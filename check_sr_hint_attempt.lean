import Mathlib.Tactic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Semicontinuity.Basic

open MeasureTheory
open scoped ENNReal

lemma test_hint_attempt (ε : ℝ) (hεpos : 0 < ε) :
    (∫⁻ x : ℝ, Set.indicator (Set.Ioo (-ε) ε) (fun x => ENNReal.ofReal (Real.log (ε / |x|))) ∂volume)
      = ENNReal.ofReal (2 * ε) := by
  let f : ℝ → ℝ := fun x => Real.log (ε / |x|)
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (-ε) ε)] f := by
    rw [ae_restrict_iff' (s := Set.Ioo (-ε) ε) isOpen_Ioo.measurableSet]
    refine Filter.Eventually.of_forall ?_
    intro x hx
    by_cases hx0 : x = 0
    · simpa [f, hx0]
    · have hxabs : |x| < ε := by
        exact (abs_lt).2 (by simpa [Set.mem_Ioo] using hx)
      have h1 : 1 ≤ ε / |x| := (one_le_div (abs_pos.2 hx0)).2 (le_of_lt hxabs)
      have hlognn : 0 ≤ Real.log (ε / |x|) := Real.log_nonneg h1
      simpa [f] using hlognn
  have hfm : AEStronglyMeasurable f (volume.restrict (Set.Ioo (-ε) ε)) := by
    have hmf : Measurable f := by measurability
    exact hmf.aestronglyMeasurable
  have hEq_toReal :
      (∫ x : ℝ, f x ∂(volume.restrict (Set.Ioo (-ε) ε))) =
        (∫⁻ x : ℝ, ENNReal.ofReal (f x) ∂(volume.restrict (Set.Ioo (-ε) ε))).toReal := by
    exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnn hfm
  have hIoo_to_Int :
      (∫ x : ℝ, f x ∂(volume.restrict (Set.Ioo (-ε) ε))) =
        ∫ (x : ℝ) in (-ε)..ε, f x ∂volume := by
    calc
      (∫ x : ℝ, f x ∂(volume.restrict (Set.Ioo (-ε) ε)))
          = ∫ (x : ℝ) in Set.Ioo (-ε) ε, f x ∂volume := by simp
      _ = ∫ (x : ℝ) in Set.Icc (-ε) ε, f x ∂volume := by
          simpa using (MeasureTheory.integral_Icc_eq_integral_Ioo (μ := volume) (f := f)).symm
      _ = ∫ (x : ℝ) in Set.Ioc (-ε) ε, f x ∂volume := by
          simpa using (MeasureTheory.integral_Icc_eq_integral_Ioc (μ := volume) (f := f))
      _ = ∫ (x : ℝ) in (-ε)..ε, f x ∂volume := by
          simpa [Set.uIoc_of_le hεpos.le] using
            (intervalIntegral.integral_of_le (μ := volume) (f := f) hεpos.le)
  have hnegEq :
      (∫ (x : ℝ) in (-ε)..0, f x ∂volume) = (∫ (x : ℝ) in 0..ε, f x ∂volume) := by
    calc
      (∫ (x : ℝ) in (-ε)..0, f x ∂volume)
          = ∫ (x : ℝ) in 0..ε, f (-x) ∂volume := by
              simpa using (intervalIntegral.integral_comp_neg (μ := volume) (a := 0) (b := ε) f).symm
      _ = ∫ (x : ℝ) in 0..ε, f x ∂volume := by
            simp [f, abs_neg]
  have hposInt : (∫ (x : ℝ) in 0..ε, f x ∂volume) = ε := by
    have h0_eq :
        f =ᵐ[volume.restrict (Set.uIoc 0 ε)] fun x => Real.log ε - Real.log x := by
      rw [ae_restrict_iff' (s := Set.uIoc 0 ε) (isOpen_Ioc.measurableSet)]
      refine Filter.Eventually.of_forall ?_
      intro x hx
      have hx' : x ∈ Set.Ioc 0 ε := by
        simpa [Set.uIoc_of_le hεpos.le] using hx
      have hxpos : 0 < x := hx'.1
      have hxabs : |x| = x := abs_of_pos hxpos
      have hxne : x ≠ 0 := ne_of_gt hxpos
      simp [f, hxabs, Real.log_div hεpos.ne' hxne]
    have hconst : IntervalIntegrable (fun _ : ℝ => Real.log ε) volume 0 ε :=
      intervalIntegral.intervalIntegrable_const
    have hlog : IntervalIntegrable (fun x : ℝ => Real.log x) volume 0 ε :=
      intervalIntegral.intervalIntegrable_log'
    have hsub : IntervalIntegrable (fun x : ℝ => Real.log ε - Real.log x) volume 0 ε :=
      hconst.sub hlog
    have h_int : IntervalIntegrable f volume 0 ε := by
      exact hsub.congr_ae h0_eq.symm
    calc
      (∫ (x : ℝ) in 0..ε, f x ∂volume)
          = ∫ (x : ℝ) in 0..ε, (fun x => Real.log ε - Real.log x) x ∂volume := by
              exact intervalIntegral.integral_congr_ae_restrict h0_eq
      _ = ∫ (x : ℝ) in 0..ε, (fun _ : ℝ => Real.log ε) x ∂volume
            - ∫ (x : ℝ) in 0..ε, (fun x => Real.log x) x ∂volume := by
              simpa [sub_eq_add_neg] using (intervalIntegral.integral_sub hconst hlog)
      _ = (ε - 0) * Real.log ε - (ε * Real.log ε - ε) := by
            rw [intervalIntegral.integral_const, intervalIntegral.integral_log_from_zero_of_pos hεpos]
      _ = ε := by ring
  have hnegInt : IntervalIntegrable f volume (-ε) 0 := by
    have haux : IntervalIntegrable (fun x : ℝ => f (x * (-1))) volume 0 (-ε) := by
      have hfn : ‖f (min (0:ℝ) (-ε))‖ₑ ≠ ⊤ := by simp [f]
      have hfn' : ‖f ((-1) * min (0 / (-1)) (ε / (-1)))‖ₑ ≠ ⊤ := by simp [f]
      exact hposIntInterval.comp_mul_right hfn hfn'
    exact haux.symm.congr_ae (Filter.EventuallyEq.of_forall (by intro x; simp [f, mul_comm, mul_left_comm, mul_assoc, abs_neg]))
  have hhalf :
      (∫ (x : ℝ) in (-ε)..ε, f x ∂volume) =
        2 * ∫ (x : ℝ) in 0..ε, f x ∂volume := by
    have hneg : IntervalIntegrable f volume (-ε) 0 := hnegInt
    calc
      (∫ (x : ℝ) in (-ε)..ε, f x ∂volume)
          = (∫ (x : ℝ) in (-ε)..0, f x ∂volume) + ∫ (x : ℝ) in 0..ε, f x ∂volume := by
            exact (intervalIntegral.integral_add_adjacent_intervals hneg hposIntInterval).symm
      _ = (∫ (x : ℝ) in 0..ε, f x ∂volume) + ∫ (x : ℝ) in 0..ε, f x ∂volume := by
            rw [hnegEq]
      _ = 2 * ∫ (x : ℝ) in 0..ε, f x ∂volume := by ring
  have hint' :
      (∫ x : ℝ, f x ∂(volume.restrict (Set.Ioo (-ε) ε))) = 2 * ε := by
    calc
      (∫ x : ℝ, f x ∂(volume.restrict (Set.Ioo (-ε) ε)))
          = ∫ (x : ℝ) in (-ε)..ε, f x ∂volume := hIoo_to_Int
      _ = 2 * ∫ (x : ℝ) in 0..ε, f x ∂volume := hhalf
      _ = 2 * ε := by rw [hposInt]
  have htoReal :
      (∫⁻ x : ℝ in Set.Ioo (-ε) ε, ENNReal.ofReal (f x) ∂volume).toReal = 2 * ε := by
    calc
      (∫⁻ x : ℝ in Set.Ioo (-ε) ε, ENNReal.ofReal (f x) ∂volume).toReal
          = (∫ x : ℝ, f x ∂(volume.restrict (Set.Ioo (-ε) ε))) := hEq_toReal.symm
      _ = 2 * ε := hint'
  have htop : (∫⁻ x : ℝ in Set.Ioo (-ε) ε, ENNReal.ofReal (f x) ∂volume) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at htoReal
    have hεne : ¬ 2 * ε = 0 := by linarith [hεpos]
    nlinarith
  have htarget :
      (∫⁻ x : ℝ in Set.Ioo (-ε) ε, ENNReal.ofReal (f x) ∂volume) = ENNReal.ofReal (2 * ε) := by
    refine (ENNReal.toReal_eq_toReal htop (by simp)).1 ?_
    simpa [ENNReal.toReal_ofReal (show 0 ≤ 2 * ε by positivity)] using htoReal
  simpa [f, href] using htarget
where hposIntInterval : IntervalIntegrable f volume 0 ε := by
  sorry
