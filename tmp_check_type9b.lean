import Mathlib
#check (intervalIntegral.intervalIntegrable_log' : IntervalIntegrable Real.log MeasureTheory.volume (0:ℝ) (1:ℝ))
#check (intervalIntegral.intervalIntegrable_log' (a := (0:ℝ)) (b := (1:ℝ))
)
#check (intervalIntegral.intervalIntegrable_log' (a := (0:ℝ)) (b := (1:ℝ))).comp_mul_left
#check (intervalIntegral.intervalIntegrable_log' (a := (0:ℝ)) (b := (1:ℝ))).comp_mul_right
