import Mathlib

noncomputable section

open MeasureTheory
open scoped ENNReal

lemma test_hint (ε : ℝ) (hεpos : 0 < ε) :
    (∫⁻ x : ℝ, Set.indicator (Set.Ioo (-ε) ε)
      (fun x => ENNReal.ofReal (Real.log (ε / |x|))) ∂volume)
      = ENNReal.ofReal (2 * ε) := by
  let f : ℝ → ℝ := fun x => Real.log (ε / |x|)
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (-ε) ε)] f := by
    refine (ae_restrict_iff' (μ := volume) (hs := isOpen_Ioo.measurableSet)).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    by_cases hx0 : x = 0
    · simp [f, hx0]
    · have hlt : |x| < ε := by
        exact abs_lt.mp (by simpa [Set.mem_Ioo] using hx)
      have hdiv : 1 ≤ ε / |x| := by
        refine (le_div_iff (abs_pos.mpr hx0)).2 ?_
        exact le_of_lt hlt
      exact Real.log_nonneg hdiv
  have hfm : AEStronglyMeasurable f (volume.restrict (Set.Ioo (-ε) ε)) := by
    have hmf : Measurable f := by
      measurability
    exact hmf.aestronglyMeasurable
  have hEq_toReal :
      (∫ x : ℝ, f x ∂(volume.restrict (Set.Ioo (-ε) ε))) =
        (∫⁻ x : ℝ, ENNReal.ofReal (f x) ∂(volume.restrict (Set.Ioo (-ε) ε))).toReal := by
    exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnn hfm
  have hIoo_to_Int :
      (∫ x : ℝ, f x ∂(volume.restrict (Set.Ioo (-ε) ε))) =
        ∫ (x : ℝ) in (-ε)..ε, f x ∂volume := by
    simp [f]
  have hlogEq : ∀ᵐ x ∂volume, x ∈ Set.uIoc 0 ε → f x = Real.log ε - Real.log x := by
    refine Filter.Eventually.of_forall ?_
    intro x hx
    have hx' : 0 < x ∧ x ≤ ε := by
      simpa [Set.uIoc_of_le hεpos.le] using hx
    have hxab : |x| = x := abs_of_pos hx'.1
    calc
      f x = Real.log (ε / x) := by
        simp [f, hxab]
      _ = Real.log ε - Real.log x := by
        rw [Real.log_div hεpos.ne' hx'.1.ne']
  have hsub : IntervalIntegrable f volume 0 ε := by
    have hconst : IntervalIntegrable (fun _ : ℝ => Real.log ε) volume 0 ε := by
      intervalIntegral.intervalIntegrable_const
    have hlog : IntervalIntegrable (fun x : ℝ => Real.log x) volume 0 ε :=
      intervalIntegral.intervalIntegrable_log'
    exact (hconst.sub hlog).congr_ae (ae_restrict_iff'.1 (hlogEq) )
  have hneg : IntervalIntegrable f volume (-ε) 0 := by
    have hIaux : IntervalIntegrable (fun x : ℝ => f (x * (-1 : ℝ))) volume 0 (-ε) := by
      refine hsub.comp_mul_right (c := (-1 : ℝ)) ?_ ?_
      · simp
      · simp [f, le_of_lt hεpos]
    have haux : IntervalIntegrable (fun x : ℝ => f (x * (-1 : ℝ))) volume (-ε) 0 := hIaux.symm
    exact haux.congr_ae (Filter.Eventually.of_forall (by
      intro x
      simp [f]))
  have hnegEq :
      (∫ (x : ℝ) in (-ε)..0, f x ∂volume) = ∫ (x : ℝ) in 0..ε, f x ∂volume := by
    calc
      (∫ (x : ℝ) in (-ε)..0, f x ∂volume)
          = ∫ (x : ℝ) in 0..ε, f (-x) ∂volume := by
              simpa using
                (intervalIntegral.integral_comp_neg (f := f) (a := 0) (b := ε)).symm
      _ = ∫ (x : ℝ) in 0..ε, f x ∂volume := by
          simpa using
            (intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (by
              intro x
              simp [f, abs_neg]))
  have hhalf :
      (∫ (x : ℝ) in (-ε)..ε, f x ∂volume) = 2 * ∫ (x : ℝ) in 0..ε, f x ∂volume := by
    calc
      (∫ (x : ℝ) in (-ε)..ε, f x ∂volume)
          = (∫ (x : ℝ) in (-ε)..0, f x ∂volume) + ∫ (x : ℝ) in 0..ε, f x ∂volume := by
            simpa using (intervalIntegral.integral_add_adjacent_intervals hneg hsub).symm
      _ = (∫ (x : ℝ) in 0..ε, f x ∂volume) + ∫ (x : ℝ) in 0..ε, f x ∂volume := by
            rw [hnegEq]
      _ = 2 * ∫ (x : ℝ) in 0..ε, f x ∂volume := by ring
  have hposInt :
      (∫ (x : ℝ) in 0..ε, f x ∂volume) = ε := by
    have hconstInt : (∫ (x : ℝ) in 0..ε, (fun _ : ℝ => Real.log ε) x ∂volume) = (ε - 0) * Real.log ε := by
      simpa [smul_eq_mul] using
        (intervalIntegral.integral_const (μ := volume) (c := Real.log ε) (a := (0 : ℝ)) (b := ε))
    calc
      (∫ (x : ℝ) in 0..ε, f x ∂volume)
          = ∫ (x : ℝ) in 0..ε, (fun x => Real.log ε - Real.log x) x ∂volume := by
              exact intervalIntegral.integral_congr_ae hlogEq
      _ = ∫ (x : ℝ) in 0..ε, (fun _ : ℝ => Real.log ε) x ∂volume -
          ∫ (x : ℝ) in 0..ε, (fun x => Real.log x) x ∂volume := by
          simpa [sub_eq_add_neg] using intervalIntegral.integral_sub (hconst :=
            intervalIntegral.intervalIntegrable_const) (hlog := intervalIntegral.intervalIntegrable_log')
      _ = (ε - 0) * Real.log ε - (ε * Real.log ε - ε) := by
          rw [hconstInt, integral_log_from_zero_of_pos hεpos]
      _ = ε := by
          ring
  have hint :
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
          = ∫ x : ℝ, f x ∂(volume.restrict (Set.Ioo (-ε) ε)) := by
            exact hEq_toReal.symm
      _ = 2 * ε := hint
  have hto :
      (∫⁻ x : ℝ in Set.Ioo (-ε) ε, ENNReal.ofReal (f x) ∂volume) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at htoReal
    nlinarith [hεpos, htoReal]
  have htarget :
      (∫⁻ x : ℝ in Set.Ioo (-ε) ε, ENNReal.ofReal (f x) ∂volume) = ENNReal.ofReal (2 * ε) := by
    apply (ENNReal.toReal_eq_toReal hto (by simp [show 0 ≤ 2 * ε by positivity])).1
    simpa [show 0 ≤ 2 * ε by positivity] using htoReal
  simpa [f] using htarget
