import Mathlib
#check (intervalIntegral.intervalIntegrable_log' (μ := MeasureTheory.volume) (a := (0:ℝ)) (b := (1:ℝ)))
#check (intervalIntegral.intervalIntegrable_log' (μ := MeasureTheory.volume) (a := (0:ℝ)) (b := (1:ℝ))).comp_mul_left
#check (intervalIntegral.intervalIntegrable_log' (μ := MeasureTheory.volume) (a := (0:ℝ)) (b := (1:ℝ))).comp_mul_right
#check (intervalIntegral.intervalIntegrable_log' (μ := MeasureTheory.volume) (a := (0:ℝ)) (b := (1:ℝ))).comp_mul_left (show (| (1:ℝ) |:ℝ) ≠ ⊤ by norm_num)
#check (intervalIntegral.intervalIntegrable_log' (μ := MeasureTheory.volume) (a := (0:ℝ)) (b := (1:ℝ))).comp_mul_right (show (| (1:ℝ) |:ℝ) ≠ ⊤ by norm_num)
