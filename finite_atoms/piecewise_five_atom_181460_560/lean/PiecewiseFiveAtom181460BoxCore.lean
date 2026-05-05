import PiecewiseFiveAtom181460Mathlib

/-!
# Box-core lemmas for the 560-block piecewise certificate

This file contains the reusable Mathlib bridge from rational box distance bounds
and rational log lower bounds to positivity of the real logarithmic potential.
Generated chunk files instantiate these lemmas with concrete rational boxes.
-/

namespace Erdos1038
namespace PiecewiseFiveAtom181460Mathlib

noncomputable section

open Set

/-- Weighted rational lower bound for the five logarithmic terms. -/
def weightedLogLowerRat (nPos nNeg : Nat)
    (w1 w2 w3 w4 D0 D1 D2 D3 D4 : Rat) : Rat :=
    logInvLowerRat nPos nNeg D0
  + w1 * logInvLowerRat nPos nNeg D1
  + w2 * logInvLowerRat nPos nNeg D2
  + w3 * logInvLowerRat nPos nNeg D3
  + w4 * logInvLowerRat nPos nNeg D4

lemma abs_sub_le_of_box_bounds
    {L R p D y : ℝ}
    (hy : y ∈ Icc L R)
    (hL : |L - p| ≤ D)
    (hR : |R - p| ≤ D) :
    |y - p| ≤ D := by
  rw [abs_sub_le_iff] at hL hR ⊢
  constructor <;> linarith [hy.1, hy.2, hL.1, hL.2, hR.1, hR.2]

lemma weightedLogLowerRat_le_V
    (nPos nNeg : Nat)
    (w1q w2q w3q w4q D0 D1 D2 D3 D4 : Rat)
    {y : ℝ}
    (hw1 : 0 ≤ (w1q : ℝ))
    (hw2 : 0 ≤ (w2q : ℝ))
    (hw3 : 0 ≤ (w3q : ℝ))
    (hw4 : 0 ≤ (w4q : ℝ))
    (hD0 : 0 < D0) (hD1 : 0 < D1) (hD2 : 0 < D2) (hD3 : 0 < D3) (hD4 : 0 < D4)
    (hy0 : 0 < |y|)
    (hy1 : 0 < |y - d1|)
    (hy2 : 0 < |y - d2|)
    (hy3 : 0 < |y - d3|)
    (hy4 : 0 < |y - d4|)
    (hb0 : |y| ≤ (D0 : ℝ))
    (hb1 : |y - d1| ≤ (D1 : ℝ))
    (hb2 : |y - d2| ≤ (D2 : ℝ))
    (hb3 : |y - d3| ≤ (D3 : ℝ))
    (hb4 : |y - d4| ≤ (D4 : ℝ)) :
    ((weightedLogLowerRat nPos nNeg w1q w2q w3q w4q D0 D1 D2 D3 D4 : Rat) : ℝ)
      ≤ V (w1q : ℝ) (w2q : ℝ) (w3q : ℝ) (w4q : ℝ) y := by
  have h0 := logInvLowerRat_le_log_actual_inv nPos nNeg D0 hD0 hy0 hb0
  have h1 := logInvLowerRat_le_log_actual_inv nPos nNeg D1 hD1 hy1 hb1
  have h2 := logInvLowerRat_le_log_actual_inv nPos nNeg D2 hD2 hy2 hb2
  have h3 := logInvLowerRat_le_log_actual_inv nPos nNeg D3 hD3 hy3 hb3
  have h4 := logInvLowerRat_le_log_actual_inv nPos nNeg D4 hD4 hy4 hb4
  have hw1mul : ((w1q : Rat) : ℝ) * ((logInvLowerRat nPos nNeg D1 : Rat) : ℝ)
      ≤ ((w1q : Rat) : ℝ) * Real.log (|y - d1|)⁻¹ :=
    mul_le_mul_of_nonneg_left h1 hw1
  have hw2mul : ((w2q : Rat) : ℝ) * ((logInvLowerRat nPos nNeg D2 : Rat) : ℝ)
      ≤ ((w2q : Rat) : ℝ) * Real.log (|y - d2|)⁻¹ :=
    mul_le_mul_of_nonneg_left h2 hw2
  have hw3mul : ((w3q : Rat) : ℝ) * ((logInvLowerRat nPos nNeg D3 : Rat) : ℝ)
      ≤ ((w3q : Rat) : ℝ) * Real.log (|y - d3|)⁻¹ :=
    mul_le_mul_of_nonneg_left h3 hw3
  have hw4mul : ((w4q : Rat) : ℝ) * ((logInvLowerRat nPos nNeg D4 : Rat) : ℝ)
      ≤ ((w4q : Rat) : ℝ) * Real.log (|y - d4|)⁻¹ :=
    mul_le_mul_of_nonneg_left h4 hw4
  calc
    ((weightedLogLowerRat nPos nNeg w1q w2q w3q w4q D0 D1 D2 D3 D4 : Rat) : ℝ)
        = ((logInvLowerRat nPos nNeg D0 : Rat) : ℝ)
          + (w1q : ℝ) * ((logInvLowerRat nPos nNeg D1 : Rat) : ℝ)
          + (w2q : ℝ) * ((logInvLowerRat nPos nNeg D2 : Rat) : ℝ)
          + (w3q : ℝ) * ((logInvLowerRat nPos nNeg D3 : Rat) : ℝ)
          + (w4q : ℝ) * ((logInvLowerRat nPos nNeg D4 : Rat) : ℝ) := by
            simp [weightedLogLowerRat]
    _ ≤ Real.log |y|⁻¹
          + (w1q : ℝ) * Real.log |y - d1|⁻¹
          + (w2q : ℝ) * Real.log |y - d2|⁻¹
          + (w3q : ℝ) * Real.log |y - d3|⁻¹
          + (w4q : ℝ) * Real.log |y - d4|⁻¹ := by
            nlinarith
    _ = V (w1q : ℝ) (w2q : ℝ) (w3q : ℝ) (w4q : ℝ) y := by
            simp [V]

/-- A single rational box proves positivity of `V` on that box. -/
lemma V_pos_of_rat_box
    (nPos nNeg : Nat)
    (w1q w2q w3q w4q L R D0 D1 D2 D3 D4 : Rat)
    (hrat : (0 : Rat) < weightedLogLowerRat nPos nNeg w1q w2q w3q w4q D0 D1 D2 D3 D4)
    (hw1 : 0 ≤ (w1q : ℝ))
    (hw2 : 0 ≤ (w2q : ℝ))
    (hw3 : 0 ≤ (w3q : ℝ))
    (hw4 : 0 ≤ (w4q : ℝ))
    (hD0 : 0 < D0) (hD1 : 0 < D1) (hD2 : 0 < D2) (hD3 : 0 < D3) (hD4 : 0 < D4)
    (hL0 : |(L : ℝ) - 0| ≤ (D0 : ℝ))
    (hR0 : |(R : ℝ) - 0| ≤ (D0 : ℝ))
    (hL1 : |(L : ℝ) - d1| ≤ (D1 : ℝ))
    (hR1 : |(R : ℝ) - d1| ≤ (D1 : ℝ))
    (hL2 : |(L : ℝ) - d2| ≤ (D2 : ℝ))
    (hR2 : |(R : ℝ) - d2| ≤ (D2 : ℝ))
    (hL3 : |(L : ℝ) - d3| ≤ (D3 : ℝ))
    (hR3 : |(R : ℝ) - d3| ≤ (D3 : ℝ))
    (hL4 : |(L : ℝ) - d4| ≤ (D4 : ℝ))
    (hR4 : |(R : ℝ) - d4| ≤ (D4 : ℝ))
    {y : ℝ}
    (hy : y ∈ Icc (L : ℝ) (R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ d1)
    (hy2ne : y ≠ d2)
    (hy3ne : y ≠ d3)
    (hy4ne : y ≠ d4) :
    0 < V (w1q : ℝ) (w2q : ℝ) (w3q : ℝ) (w4q : ℝ) y := by
  have hratR : (0 : ℝ) < ((weightedLogLowerRat nPos nNeg w1q w2q w3q w4q D0 D1 D2 D3 D4 : Rat) : ℝ) := by
    exact_mod_cast hrat
  have hb0 : |y| ≤ (D0 : ℝ) := by
    simpa using abs_sub_le_of_box_bounds (L := (L : ℝ)) (R := (R : ℝ)) (p := 0) (D := (D0 : ℝ)) hy hL0 hR0
  have hb1 : |y - d1| ≤ (D1 : ℝ) :=
    abs_sub_le_of_box_bounds (L := (L : ℝ)) (R := (R : ℝ)) (p := d1) (D := (D1 : ℝ)) hy hL1 hR1
  have hb2 : |y - d2| ≤ (D2 : ℝ) :=
    abs_sub_le_of_box_bounds (L := (L : ℝ)) (R := (R : ℝ)) (p := d2) (D := (D2 : ℝ)) hy hL2 hR2
  have hb3 : |y - d3| ≤ (D3 : ℝ) :=
    abs_sub_le_of_box_bounds (L := (L : ℝ)) (R := (R : ℝ)) (p := d3) (D := (D3 : ℝ)) hy hL3 hR3
  have hb4 : |y - d4| ≤ (D4 : ℝ) :=
    abs_sub_le_of_box_bounds (L := (L : ℝ)) (R := (R : ℝ)) (p := d4) (D := (D4 : ℝ)) hy hL4 hR4
  have hle := weightedLogLowerRat_le_V nPos nNeg w1q w2q w3q w4q D0 D1 D2 D3 D4
    hw1 hw2 hw3 hw4 hD0 hD1 hD2 hD3 hD4
    (abs_pos.mpr hy0ne) (abs_pos.mpr (sub_ne_zero.mpr hy1ne))
    (abs_pos.mpr (sub_ne_zero.mpr hy2ne)) (abs_pos.mpr (sub_ne_zero.mpr hy3ne))
    (abs_pos.mpr (sub_ne_zero.mpr hy4ne)) hb0 hb1 hb2 hb3 hb4
  exact hratR.trans_le hle

end

end PiecewiseFiveAtom181460Mathlib
end Erdos1038
