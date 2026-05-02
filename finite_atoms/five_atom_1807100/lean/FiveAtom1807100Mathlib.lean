import Mathlib

/-!
# Mathlib layer for the five-atom `M = 1.807100` certificate

This file defines the one-variable five-atom potential using `Real.log` and
proves the endpoint and critical-bracket positivity checks in Mathlib.

The logarithm estimates use rational Taylor/atanh bounds from Mathlib:

* `Real.sum_range_le_log_div`
* `Real.log_div_le_sum_range_add`
-/

namespace Erdos1038
namespace FiveAtom1807100Mathlib

noncomputable section

open Set

def q (n d : ℕ) : ℝ := (n : ℝ) / (d : ℝ)

def M : ℝ := q 1807100 1000000
def T : ℝ := q 1708 1000
def yLo : ℝ := q 708 1000
def yHi : ℝ := q 2807100 1000000

def w1 : ℝ := q 118287976 100000000
def w2 : ℝ := q 3349753 100000000
def w3 : ℝ := q 11739956 100000000
def w4 : ℝ := q 17267833 100000000

def s1 : ℝ := q 180710376 100000000
def s2 : ℝ := q 257979789 100000000
def s3 : ℝ := q 269319012 100000000
def s4 : ℝ := q 279229832 100000000

def V (y : ℝ) : ℝ :=
    Real.log (|y|)⁻¹
  + w1 * Real.log (|y - s1|)⁻¹
  + w2 * Real.log (|y - s2|)⁻¹
  + w3 * Real.log (|y - s3|)⁻¹
  + w4 * Real.log (|y - s4|)⁻¹

def PoleFreeOneVariableLogPositivity : Prop :=
  ∀ y : ℝ, y ∈ Icc yLo yHi →
    y ≠ s1 → y ≠ s2 → y ≠ s3 → y ≠ s4 → 0 < V y

/-! ## Exact real arithmetic for the moving tail interval -/

theorem y_range_of_tail {a x : ℝ}
    (ha : a ∈ Icc (-M) (-T))
    (hx : x ∈ Icc (-1) 1) :
    x - a ∈ Icc yLo yHi := by
  constructor
  · have hxlo : (-1 : ℝ) ≤ x := hx.1
    have ahi : a ≤ -T := ha.2
    have h : (-1 : ℝ) - (-T) ≤ x - a := by linarith
    norm_num [yLo, T, q] at h ⊢
    exact h
  · have hxhi : x ≤ (1 : ℝ) := hx.2
    have alo : -M ≤ a := ha.1
    have h : x - a ≤ (1 : ℝ) - (-M) := by linarith
    norm_num [yHi, M, q] at h ⊢
    exact h

theorem V_positive_on_tail
    (hlog : PoleFreeOneVariableLogPositivity)
    {a x : ℝ}
    (ha : a ∈ Icc (-M) (-T))
    (hx : x ∈ Icc (-1) 1)
    (hne1 : x - a ≠ s1)
    (hne2 : x - a ≠ s2)
    (hne3 : x - a ≠ s3)
    (hne4 : x - a ≠ s4) :
    0 < V (x - a) :=
  hlog (x - a) (y_range_of_tail ha hx) hne1 hne2 hne3 hne4

/-! ## Exact disjointness of the five swept intervals -/

def I0 : Set ℝ := Icc (-M) (-T)
def I1 : Set ℝ := Icc (s1 - M) (s1 - T)
def I2 : Set ℝ := Icc (s2 - M) (s2 - T)
def I3 : Set ℝ := Icc (s3 - M) (s3 - T)
def I4 : Set ℝ := Icc (s4 - M) (s4 - T)
def LongInterval : Set ℝ := Ioo (-T) 0


theorem tail_length : M - T = q 99100 1000000 := by
  norm_num [M, T, q]

theorem first_shift_after_M : M < s1 := by
  norm_num [M, s1, q]

theorem gap12 : M - T < s2 - s1 := by
  norm_num [M, T, s1, s2, q]

theorem gap23 : M - T < s3 - s2 := by
  norm_num [M, T, s2, s3, q]

theorem gap34 : M - T < s4 - s3 := by
  norm_num [M, T, s3, s4, q]

theorem I0_disjoint_Long : Disjoint I0 LongInterval := by
  rw [Set.disjoint_left]
  intro x hx0 hxLong
  simp [I0, LongInterval] at hx0 hxLong
  linarith

theorem I1_disjoint_Long : Disjoint I1 LongInterval := by
  rw [Set.disjoint_left]
  intro x hx1 hxLong
  simp [I1, LongInterval] at hx1 hxLong
  have hpos : 0 < s1 - M := by
    norm_num [s1, M, q]
  linarith

theorem I2_disjoint_Long : Disjoint I2 LongInterval := by
  rw [Set.disjoint_left]
  intro x hx2 hxLong
  simp [I2, LongInterval] at hx2 hxLong
  have hpos : 0 < s2 - M := by
    norm_num [s2, M, q]
  linarith

theorem I3_disjoint_Long : Disjoint I3 LongInterval := by
  rw [Set.disjoint_left]
  intro x hx3 hxLong
  simp [I3, LongInterval] at hx3 hxLong
  have hpos : 0 < s3 - M := by
    norm_num [s3, M, q]
  linarith

theorem I4_disjoint_Long : Disjoint I4 LongInterval := by
  rw [Set.disjoint_left]
  intro x hx4 hxLong
  simp [I4, LongInterval] at hx4 hxLong
  have hpos : 0 < s4 - M := by
    norm_num [s4, M, q]
  linarith

theorem I0_I1_disjoint : Disjoint I0 I1 := by
  rw [Set.disjoint_left]
  intro x hx0 hx1
  simp [I0, I1] at hx0 hx1
  have h : -T < s1 - M := by
    norm_num [T, s1, M, q]
  linarith

theorem I1_I2_disjoint : Disjoint I1 I2 := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  simp [I1, I2] at hx1 hx2
  have h : s1 - T < s2 - M := by
    norm_num [T, s1, s2, M, q]
  linarith

theorem I2_I3_disjoint : Disjoint I2 I3 := by
  rw [Set.disjoint_left]
  intro x hx2 hx3
  simp [I2, I3] at hx2 hx3
  have h : s2 - T < s3 - M := by
    norm_num [T, s2, s3, M, q]
  linarith

theorem I3_I4_disjoint : Disjoint I3 I4 := by
  rw [Set.disjoint_left]
  intro x hx3 hx4
  simp [I3, I4] at hx3 hx4
  have h : s3 - T < s4 - M := by
    norm_num [T, s3, s4, M, q]
  linarith

theorem sweep_disjointness_certificate :
    Disjoint I0 LongInterval ∧
    Disjoint I1 LongInterval ∧
    Disjoint I2 LongInterval ∧
    Disjoint I3 LongInterval ∧
    Disjoint I4 LongInterval ∧
    Disjoint I0 I1 ∧
    Disjoint I1 I2 ∧
    Disjoint I2 I3 ∧
    Disjoint I3 I4 := by
  exact ⟨I0_disjoint_Long, I1_disjoint_Long, I2_disjoint_Long,
    I3_disjoint_Long, I4_disjoint_Long, I0_I1_disjoint,
    I1_I2_disjoint, I2_I3_disjoint, I3_I4_disjoint⟩

/-! ## Internal Mathlib proof of the weakest endpoint log check -/

open Finset

def atanhLowerRat : Nat → Rat → Rat
  | 0, _ => 0
  | n + 1, t => atanhLowerRat n t + 2 * t ^ (2 * n + 1) / (2 * n + 1)

def atanhUpperRat (n : Nat) (t : Rat) : Rat :=
  atanhLowerRat n t + 2 * t ^ (2 * n + 1) / (1 - t ^ 2)

def atanhLowerReal (n : Nat) (t : ℝ) : ℝ :=
  2 * (∑ i ∈ Finset.range n, t ^ (2 * i + 1) / (2 * (i : ℝ) + 1))

def atanhUpperReal (n : Nat) (t : ℝ) : ℝ :=
  atanhLowerReal n t + 2 * t ^ (2 * n + 1) / (1 - t ^ 2)

lemma atanhLowerRat_cast (n : Nat) (t : Rat) :
    ((atanhLowerRat n t : Rat) : ℝ) = atanhLowerReal n (t : ℝ) := by
  induction n with
  | zero =>
      simp [atanhLowerRat, atanhLowerReal]
  | succ n ih =>
      rw [atanhLowerRat]
      simp only [Rat.cast_add, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow]
      rw [ih]
      simp [atanhLowerReal, Finset.sum_range_succ]
      ring

lemma atanhUpperRat_cast (n : Nat) (t : Rat) :
    ((atanhUpperRat n t : Rat) : ℝ) = atanhUpperReal n (t : ℝ) := by
  simp [atanhUpperRat, atanhUpperReal, atanhLowerRat_cast]

lemma log_lower_bound_of_rat (r t : Rat) (n : Nat)
    (ht0 : 0 ≤ (t : ℝ)) (ht1 : (t : ℝ) < 1)
    (hr : (r : ℝ) = (1 + (t : ℝ)) / (1 - (t : ℝ))) :
    ((atanhLowerRat n t : Rat) : ℝ) ≤ Real.log (r : ℝ) := by
  have h := Real.sum_range_le_log_div ht0 ht1 n
  rw [atanhLowerRat_cast]
  unfold atanhLowerReal
  rw [hr]
  nlinarith

lemma log_upper_bound_of_rat (r t : Rat) (n : Nat)
    (ht0 : 0 ≤ (t : ℝ)) (ht1 : (t : ℝ) < 1)
    (hr : (r : ℝ) = (1 + (t : ℝ)) / (1 - (t : ℝ))) :
    Real.log (r : ℝ) ≤ ((atanhUpperRat n t : Rat) : ℝ) := by
  have h := Real.log_div_le_sum_range_add ht0 ht1 n
  rw [atanhUpperRat_cast]
  unfold atanhUpperReal atanhLowerReal
  rw [hr]
  have h2 := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)
  calc
    Real.log ((1 + (t : ℝ)) / (1 - (t : ℝ)))
        = 2 * (1 / 2 * Real.log ((1 + (t : ℝ)) / (1 - (t : ℝ)))) := by ring
    _ ≤ 2 * (∑ i ∈ Finset.range n, (t : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1) + (t : ℝ) ^ (2 * n + 1) / (1 - (t : ℝ) ^ 2)) := h2
    _ = 2 * ∑ i ∈ Finset.range n, (t : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1) + 2 * (t : ℝ) ^ (2 * n + 1) / (1 - (t : ℝ) ^ 2) := by ring

/-! ## Reusable rational lower bounds for `log d⁻¹` -/

def tInv (d : Rat) : Rat := (1 - d) / (1 + d)
def tSelf (d : Rat) : Rat := (d - 1) / (d + 1)

def logInvLowerRat (nPos nNeg : Nat) (d : Rat) : Rat :=
  if d < 1 then
    atanhLowerRat nPos (tInv d)
  else
    -atanhUpperRat nNeg (tSelf d)

def rw1 : Rat := (118287976 / 100000000 : Rat)
def rw2 : Rat := (3349753 / 100000000 : Rat)
def rw3 : Rat := (11739956 / 100000000 : Rat)
def rw4 : Rat := (17267833 / 100000000 : Rat)

lemma tInv_cast_eq (d : Rat) :
    (tInv d : ℝ) = (1 - (d : ℝ)) / (1 + (d : ℝ)) := by
  unfold tInv
  norm_num

lemma tSelf_cast_eq (d : Rat) :
    (tSelf d : ℝ) = ((d : ℝ) - 1) / ((d : ℝ) + 1) := by
  unfold tSelf
  norm_num

lemma logInvLowerRat_le_log_inv (nPos nNeg : Nat) (d : Rat) (hd : 0 < d) :
    ((logInvLowerRat nPos nNeg d : Rat) : ℝ) ≤ Real.log ((d : ℝ)⁻¹) := by
  by_cases hlt : d < 1
  · simp [logInvLowerRat, hlt]
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hltR : (d : ℝ) < 1 := by exact_mod_cast hlt
    have htEq := tInv_cast_eq d
    have denompos : 0 < 1 + (d : ℝ) := by positivity
    have ht0 : 0 ≤ (tInv d : ℝ) := by
      rw [htEq]
      exact div_nonneg (sub_nonneg.mpr hltR.le) denompos.le
    have ht1 : (tInv d : ℝ) < 1 := by
      rw [htEq]
      field_simp [denompos.ne']
      linarith
    have hr : ((1 / d : Rat) : ℝ) = (1 + (tInv d : ℝ)) / (1 - (tInv d : ℝ)) := by
      rw [htEq]
      norm_num
      field_simp [show (d : ℝ) ≠ 0 by positivity, denompos.ne']
      ring
    simpa using log_lower_bound_of_rat (1 / d) (tInv d) nPos ht0 ht1 hr
  · simp [logInvLowerRat, hlt]
    have hge : (1 : Rat) ≤ d := le_of_not_gt hlt
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hgeR : (1 : ℝ) ≤ d := by exact_mod_cast hge
    have htEq := tSelf_cast_eq d
    have denompos : 0 < (d : ℝ) + 1 := by positivity
    have ht0 : 0 ≤ (tSelf d : ℝ) := by
      rw [htEq]
      exact div_nonneg (sub_nonneg.mpr hgeR) denompos.le
    have ht1 : (tSelf d : ℝ) < 1 := by
      rw [htEq]
      field_simp [denompos.ne']
      linarith
    have hr : (d : ℝ) = (1 + (tSelf d : ℝ)) / (1 - (tSelf d : ℝ)) := by
      rw [htEq]
      field_simp [denompos.ne']
      ring
    exact log_upper_bound_of_rat d (tSelf d) nNeg ht0 ht1 hr

lemma logInvLowerRat_le_log_actual_inv
    (nPos nNeg : Nat) (d : Rat) {actual : ℝ}
    (hd : 0 < d) (hactual : 0 < actual) (hle : actual ≤ (d : ℝ)) :
    ((logInvLowerRat nPos nNeg d : Rat) : ℝ) ≤ Real.log actual⁻¹ := by
  have hbase := logInvLowerRat_le_log_inv nPos nNeg d hd
  have hdinv : ((d : ℝ)⁻¹) ≤ actual⁻¹ := by
    exact (inv_le_inv₀ (by exact_mod_cast hd : (0 : ℝ) < d) hactual).2 hle
  exact hbase.trans (Real.log_le_log (inv_pos.mpr (by exact_mod_cast hd)) hdinv)

def fiveLogLowerRat (nPos nNeg : Nat) (d0 d1 d2 d3 d4 : Rat) : Rat :=
    logInvLowerRat nPos nNeg d0
  + rw1 * logInvLowerRat nPos nNeg d1
  + rw2 * logInvLowerRat nPos nNeg d2
  + rw3 * logInvLowerRat nPos nNeg d3
  + rw4 * logInvLowerRat nPos nNeg d4

lemma fiveLogLowerRat_le
    (nPos nNeg : Nat) (d0 d1 d2 d3 d4 : Rat)
    {a0 a1 a2 a3 a4 : ℝ}
    (hd0 : 0 < d0) (hd1 : 0 < d1) (hd2 : 0 < d2) (hd3 : 0 < d3) (hd4 : 0 < d4)
    (ha0 : 0 < a0) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (ha4 : 0 < a4)
    (h0 : a0 ≤ (d0 : ℝ)) (h1 : a1 ≤ (d1 : ℝ)) (h2 : a2 ≤ (d2 : ℝ))
    (h3 : a3 ≤ (d3 : ℝ)) (h4 : a4 ≤ (d4 : ℝ)) :
    ((fiveLogLowerRat nPos nNeg d0 d1 d2 d3 d4 : Rat) : ℝ) ≤
        Real.log a0⁻¹
      + w1 * Real.log a1⁻¹
      + w2 * Real.log a2⁻¹
      + w3 * Real.log a3⁻¹
      + w4 * Real.log a4⁻¹ := by
  have l0 := logInvLowerRat_le_log_actual_inv nPos nNeg d0 hd0 ha0 h0
  have l1 := logInvLowerRat_le_log_actual_inv nPos nNeg d1 hd1 ha1 h1
  have l2 := logInvLowerRat_le_log_actual_inv nPos nNeg d2 hd2 ha2 h2
  have l3 := logInvLowerRat_le_log_actual_inv nPos nNeg d3 hd3 ha3 h3
  have l4 := logInvLowerRat_le_log_actual_inv nPos nNeg d4 hd4 ha4 h4
  norm_num [fiveLogLowerRat, rw1, rw2, rw3, rw4, w1, w2, w3, w4, q] at l0 l1 l2 l3 l4 ⊢
  nlinarith


end

end FiveAtom1807100Mathlib
end Erdos1038
