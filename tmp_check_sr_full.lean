import Mathlib

lemma test_hint (ε : ℝ) (hεpos : 0 < ε) :
    (∫⁻ x : ℝ, Set.indicator (Set.Ioo (-ε) ε) (fun x => ENNReal.ofReal (Real.log (ε / |x|))) ∂volume)
      = ENNReal.ofReal (2 * ε) := by
  let f : ℝ → ℝ := fun x => Real.log (ε / |x|)
  have href :
      (∫⁻ x : ℝ, Set.indicator (Set.Ioo (-ε) ε) (fun x => ENNReal.ofReal f x) ∂volume) =
      ∫⁻ x : ℝ in Set.Ioo (-ε) ε, ENNReal.ofReal (f x) ∂volume := by
    simpa [f] using
      (MeasureTheory.lintegral_indicator (μ := volume) (h := isOpen_Ioo.measurableSet)
        (f := fun x => ENNReal.ofReal (f x)))
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (-ε) ε)] f := by
    refine Filter.Eventually.of_forall ?_
    intro x
    exact Real.log_nonneg (div_nonneg hεpos.le (abs_nonneg x))
  have hfm : AEStronglyMeasurable f (volume.restrict (Set.Ioo (-ε) ε)) := by
    have hmf : Measurable f := by
      measurability
    exact hmf.aestronglyMeasurable
  have hEq_toReal :
      (∫ x : ℝ, f x ∂(volume.restrict (Set.Ioo (-ε) ε)))
        = (∫⁻ x : ℝ, ENNReal.ofReal (f x) ∂(volume.restrict (Set.Ioo (-ε) ε))).toReal :=
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
      calc
        (∫ (x : ℝ) in (-ε)..0, f x ∂volume)
            = ∫ (x : ℝ) in (-0)..ε, f x ∂volume := by
                simpa [neg_zero, add_comm, add_left_comm, add_assoc] using
                  (intervalIntegral.integral_comp_neg (μ := volume) (a := -ε) (b := 0) f)
        _ = (∫ (x : ℝ) in 0..ε, f x ∂volume) := by
              ring_nf
              congr
              simp [f]
    have hposInt : (∫ (x : ℝ) in 0..ε, f x ∂volume) = ε := by
      have h0_eq :
          f =ᵐ[volume.restrict (Set.uIoc 0 ε)] fun x => Real.log ε - Real.log x := by
        refine Filter.EventuallyEq.of_forall ?_
        intro x
        have hx' : x ∈ Set.Ioc 0 ε := by
          simpa [Set.uIoc_of_le hεpos.le] using (by simp : x ∈ Set.uIoc 0 ε)
        have hxpos : 0 < x := (Set.mem_Ioc.mp hx').1
        have hxabs : |x| = x := abs_of_nonneg (le_of_lt hxpos)
        have hne : x ≠ 0 := ne_of_gt hxpos
        simp [f, hxabs, Real.log_div hεpos.ne' hne]
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
              rw [intervalIntegral.integral_const, interval_log_from_zero_of_pos hεpos]
        _ = ε := by ring
    have hhalf : (∫ (x : ℝ) in (-ε)..ε, f x ∫ (x : ℝ) in 0..ε, f x ∂volume := by
      calc
        (∫ (x : ℝ) in (-ε)..ε, f x ∂volume)
            = (∫ (x : ℝ) in (-ε)..0, f x ∂volume)
              + ∫ (x : ℝ) in 0..ε, f x ∂volume := by
            have hneg : IntervalIntegrable f volume (-ε) 0 := by
              have hIaux : IntervalIntegrable (fun x : ℝ => f (x * (-1))) volume 0 (-ε) := by
                refine hsub.comp_mul_right (c := (-1)) ?_ ?_
                · simp [f, hεpos]
                · have : 0 ≤ ε := le_of_lt hεpos
                  simp [f, this]
              exact hIaux.symm.congr_ae (Filter.EventuallyEq.of_forall (by intro x; simp [f]))
            exact (intervalIntegral.integral_add_adjacent_intervals hneg h_int)
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
  simpa [f] using htarget
