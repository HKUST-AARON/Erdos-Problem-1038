import Mathlib
#check (intervalIntegral.intervalIntegrable_const).comp_mul_right
#check (intervalIntegral.intervalIntegrable_log').comp_mul_right
#check (by
  have hε : (0:ℝ) < 1 := by norm_num
  have hI : IntervalIntegrable (fun x => Real.log (1 / x)) MeasureTheory.volume 0 1 := by
    simpa [sub_eq_add_neg] using
      ((intervalIntegral.intervalIntegrable_const.sub intervalIntegral.intervalIntegrable_log').comp_mul_right (c := (-(1:ℝ))) )
  exact hI)
