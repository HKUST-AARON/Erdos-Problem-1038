import Mathlib

noncomputable section
open MeasureTheory

def f (ε : ℝ) : ℝ → ℝ := fun x => Real.log (ε / |x|)

lemma test (ε : ℝ) (hε : 0 < ε) :
    IntervalIntegrable (f ε) volume 0 ε := by
  have hconst : IntervalIntegrable (fun _ : ℝ => Real.log ε) volume 0 ε := intervalIntegral.intervalIntegrable_const
  have hlog : IntervalIntegrable (fun x : ℝ => Real.log x) volume 0 ε := intervalIntegral.intervalIntegrable_log'
  have hlogEq : f ε =ᵐ[volume.restrict (Set.uIoc 0 ε)] (fun x => Real.log ε - Real.log x) := by
    refine (ae_restrict_iff' (μ := volume) (hs := isOpen_Ioo.measurableSet) |>.2 ?_)?
    sorry
  exact (hconst.sub hlog).congr_ae hlogEq

lemma test2 (ε : ℝ) (hε : 0 < ε) :
    IntervalIntegrable (f ε) volume (-ε) 0 := by
  have hI0 : IntervalIntegrable (f ε) volume 0 ε := test ε hε
  have hneg : IntervalIntegrable (fun x => f ε (x * (-1))) volume (0 / (-1:ℝ)) (ε / (-1:ℝ)) :=
    hI0.comp_mul_right (c := (-1:ℝ)) (by simp) (by simp)
  have hneg0 : IntervalIntegrable (fun x => f ε (x * (-1))) volume 0 (-ε) := by
    simpa by
    simpa
  have hneg' : IntervalIntegrable (fun x => f ε (x * (-1))) volume (-ε) 0 := hneg0.symm
  exact hneg'.congr_ae (Filter.Eventually.of_forall (by
    intro x
    simp [f, mul_comm]))
