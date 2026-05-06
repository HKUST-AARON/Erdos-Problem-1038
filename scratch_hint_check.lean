import Mathlib

lemma test_hint (ε : ℝ) (hεpos : 0 < ε) :
    (∫⁻ x : ℝ,
      Set.indicator (Set.Ioo (-ε) ε) (fun x => ENNReal.ofReal (Real.log (ε / |x|)) ∂volume)
      ) = ENNReal.ofReal (2 * ε) := by
  let f : ℝ → ℝ := fun x => Real.log (ε / |x|)
  have href :
      (∫⁻ x : ℝ, Set.indicator (Set.Ioo (-ε) ε) (fun x => ENNReal.ofReal (f x)) ∂volume) =
      ∫⁻ x : ℝ in Set.Ioo (-ε) ε, ENNReal.ofReal (f x) ∂volume := by
    simpa [f] using
      (MeasureTheory.lintegral_indicator (μ := volume) (h := isOpen_Ioo.measurableSet)
        (f := fun x => ENNReal.ofReal (f x)))
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (-ε) ε)] f := by
    refine Filter.Eventually.of_forall ?_
    intro x
    by_cases hx0 : x = 0
    · simp [f, hx0]
    · have hxmem : |x| < ε := by
        exact (abs_lt.2 (by
          have hxmem : x ∈ Set.Ioo (-ε) ε := by
            sorry)
          ).1 ?
      have hratio_ge : 1 ≤ ε / |x| := by
        exact (one_le_div (b := |x|) (a := ε) (by exact abs_pos.2 hx0)).2 (by
          simpa using le_of_lt hxmem)
      exact Real.log_nonneg hratio_ge
  have hfm : AEStronglyMeasurable f (volume.restrict (Set.Ioo (-ε) ε)) := by
    have hmf : Measurable f := by
      measurability
    exact hmf.aestronglyMeasurable
  have hEq_toReal :
      (∫ x : ℝ, f x ∂(volume.restrict (Set.Ioo (-ε) ε))) =
        (∫⁻ x : ℝ, ENNReal.ofReal (f x) ∂(volume.restrict (Set.Ioo (-ε) ε))).toReal :=
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnn hfm
  have hIcc :
      (∫ x : ℝ, f x ∂(volume.restrict (Set.Ioo (-ε) ε))) =
        ∫ x : ℝ in Set.Ioo (-ε) ε, f x ∂volume := by
    simp
  have hint' : (∫ x : ℝ, f x ∂(volume.restrict (Set.Ioo (-ε) ε))) = 2 * ε := by
    have hIoo_to_Int :
        (∫ x : ℝ, f x ∂(volume.restrict (Set.Ioo (-ε) ε))) =
          ∫ (x : ℝ) in (-ε)..ε, f x ∂volume := by
      calc
        (∫ x : ℝ, f x ∂(volume.restrict (Set.Ioo (-ε) ε)))
            = ∫ (x : ℝ) in Set.Ioo (-ε) ε, f x ∂volume := by simp
        _ = ∫ (x : ℝ) in Set.Icc (-ε) ε, f x ∂volume := by
            simpa using (MeasureTheory.integral_Icc_eq_integral_Ioo (μ := volume) (f := f)).symm
        _ = ∫ (x : ℝ) in Set.Ioc (-ε) ε, f x ∂volume := by
            exact MeasureTheory.integral_Icc_eq_integral_Ioc (μ := volume) (f := f)
        _ = ∫ (x : ℝ) in (-ε)..ε, f x ∂volume := by
            simpa [Set.uIoc_of_le hεpos.le] using
              (intervalIntegral.integral_of_le (μ := volume) (f := f) (a := -ε) (b := ε)
                (by nlinarith))
    have hnegEq :
        (∫ (x : ℝ) in (-ε)..0, f x ∂volume) = (∫ (x : ℝ) in 0..ε, f x ∂volume) := by
      simpa [f, abs_neg] using
        (intervalIntegral.integral_comp_neg (μ := volume) (a := -ε) (b := 0) f)
    have hposInt : (∫ (x : ℝ) in 0..ε, f x ∂volume) = ε := by
      have h0_eq :
          f =ᵐ[volume.restrict (Set.uIcc 0 ε)] fun x => Real.log ε - Real.log x := by
        refine Filter.EventuallyEq.of_forall ?_
        intro x
        by_cases hx0 : x = 0
        · simp [f, hx0]
        · have hxmem : x ∈ Set.Icc (0 : ℝ) ε := by
            simpa [Set.mem_uIcc, hεpos.le] using
              (show x ∈ Set.uIcc (0 : ℝ) ε from by
                simp [Set.mem_uIcc, hεpos.le, hx0])
            
            have hxabs : |x| = x := by
              exact abs_of_nonneg hxmem.1
            have hxne : x ≠ 0 := hx0
            simp [f, hxabs, Real.log_div hεpos.ne' hxne]
      have hconst : IntervalIntegrable (fun _ : ℝ => Real.log ε) volume 0 ε :=
        intervalIntegral.intervalIntegrable_const
      have hlog : IntervalIntegrable (fun x : ℝ => Real.log x) volume 0 ε :=
        intervalIntegral.intervalIntegrable_log'
      have hsub : IntervalIntegrable (fun x => Real.log ε - Real.log x) volume 0 ε :=
        hconst.sub hlog
      have h_int : IntervalIntegrable f volume 0 ε := by
        exact hsub.congr_ae h0_eq.symm
      calc
        (∫ (x : ℝ) in 0..ε, f x ∂volume)
            = ∫ (x : ℝ) in 0..ε, (fun x => Real.log ε - Real.log x) x ∂volume := by
                exact intervalIntegral.integral_congr_ae h0_eq
        _ = ∫ (x : ℝ) in 0..ε, (fun _ : ℝ => Real.log ε) x ∂volume
              - ∫ (x : ℝ) in 0..ε, (fun x => Real.log x) x ∂volume := by
                simpa [sub_eq_add_neg] using (intervalIntegral.integral_sub hconst hlog)
        _ = ε := by
              rw [intervalIntegral.integral_const, integral_log_from_zero_of_pos hεpos]
              ring
    have hhalf : (∫ (x : ℝ) in (-ε)..ε, f x ∂volume) = 2 * ∫ (x : ℝ) in 0..ε, f x ∂volume := by
      calc
        (∫ (x : ℝ) in (-ε)..ε, f x ∂volume)
            = (∫ (x : ℝ) in (-ε)..0, f x ∂volume)
              + ∫ (x : ℝ) in 0..ε, f x ∂volume := by
            have hneg : IntervalIntegrable f volume (-ε) 0 := by
              sorry
            have hpos : IntervalIntegrable f volume 0 ε := by
              sorry
            symm
            exact intervalIntegral.integral_add_adjacent_intervals hneg hpos
        _ = (∫ (x : ℝ) in 0..ε, f x ∂volume)
              + ∫ (x : ℝ) in 0..ε, f x ∂volume := by rw [hnegEq]
        _ = 2 * ∫ (x : ℝ) in 0..ε, f x ∂volume := by ring
    calc
      (∫ x : ℝ, f x ∂(volume.restrict (Set.Ioo (-ε) ε))) =
          ∫ (x : ℝ) in (-ε)..ε, f x ∂volume := hIoo_to_Int
      _ = 2 * ∫ (x : ℝ) in 0..ε, f x ∂volume := hhalf
      _ = 2 * ε := by rw [hposInt]
  have htoReal :
      (∫⁻ x : ℝ in Set.Ioo (-ε) ε, ENNReal.ofReal (f x) ∂volume).toReal = 2 * ε := by
    calc
      (∫⁻ x : ℝ in Set.Ioo (-ε) ε, ENNReal.ofReal (f x) ∂volume).toReal
          = (∫ x : ℝ, f x ∂(volume.restrict (Set.Ioo (-ε) ε))) := by
              exact hEq_toReal.symm
      _ = 2 * ε := by simpa [hIcc] using hint'
  have hto :
      (∫⁻ x : ℝ in Set.Ioo (-ε) ε, ENNReal.ofReal (f x) ∂volume)
        ≠ ⊤ := by
    intro htop
    have hεne : ¬ (2 * ε = 0) := by nlinarith [hεpos]
    rw [htop, ENNReal.toReal_top] at htoReal
    nlinarith
  have htarget :
      (∫⁻ x : ℝ in Set.Ioo (-ε) ε, ENNReal.ofReal (f x) ∂volume)
        = ENNReal.ofReal (2 * ε) := by
    apply (ENNReal.toReal_eq_toReal hto (by simp [show 0 ≤ 2 * ε by positivity])).1
    simpa [ENNReal.toReal_ofReal (show 0 ≤ 2 * ε by positivity)] using htoReal
  simpa [href, f] using htarget
