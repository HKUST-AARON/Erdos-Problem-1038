import Mathlib

/-!
# Mathlib layer for the five-atom `M = 1.806304` certificate

This file defines the one-variable five-atom potential using `Real.log` and
proves the endpoint and critical-bracket positivity checks in Mathlib.

The logarithm estimates use rational Taylor/atanh bounds from Mathlib:

* `Real.sum_range_le_log_div`
* `Real.log_div_le_sum_range_add`
-/

namespace Erdos1038
namespace FiveAtom1806304Mathlib

noncomputable section

open Set

def q (n d : ℕ) : ℝ := (n : ℝ) / (d : ℝ)

def M : ℝ := q 1806304 1000000
def T : ℝ := q 1708 1000
def yLo : ℝ := q 708 1000
def yHi : ℝ := q 2806304 1000000

def w1 : ℝ := q 1174168821 1000000000
def w2 : ℝ := q 25921118 1000000000
def w3 : ℝ := q 118647936 1000000000
def w4 : ℝ := q 180553554 1000000000

def s1 : ℝ := q 180650001 100000000
def s2 : ℝ := q 257053197 100000000
def s3 : ℝ := q 268367709 100000000
def s4 : ℝ := q 279017717 100000000

def V (y : ℝ) : ℝ :=
    Real.log (|y|)⁻¹
  + w1 * Real.log (|y - s1|)⁻¹
  + w2 * Real.log (|y - s2|)⁻¹
  + w3 * Real.log (|y - s3|)⁻¹
  + w4 * Real.log (|y - s4|)⁻¹

def OneVariableLogPositivity : Prop :=
  ∀ y : ℝ, y ∈ Icc yLo yHi → 0 < V y

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
    (hlog : OneVariableLogPositivity)
    {a x : ℝ}
    (ha : a ∈ Icc (-M) (-T))
    (hx : x ∈ Icc (-1) 1) :
    0 < V (x - a) :=
  hlog (x - a) (y_range_of_tail ha hx)

/-! ## Exact disjointness of the five swept intervals -/

def I0 : Set ℝ := Icc (-M) (-T)
def I1 : Set ℝ := Icc (s1 - M) (s1 - T)
def I2 : Set ℝ := Icc (s2 - M) (s2 - T)
def I3 : Set ℝ := Icc (s3 - M) (s3 - T)
def I4 : Set ℝ := Icc (s4 - M) (s4 - T)
def LongInterval : Set ℝ := Ioo (-T) 0


theorem tail_length : M - T = q 98304 1000000 := by
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

def rt0 : Rat := (2806304 / 1000000 : Rat)
def tt0 : Rat := (rt0 - 1) / (rt0 + 1)

def rt1 : Rat := (100000000 / 99980399 : Rat)
def tt1 : Rat := (rt1 - 1) / (rt1 + 1)

def rt2 : Rat := (100000000 / 23577203 : Rat)
def tt2 : Rat := (rt2 - 1) / (rt2 + 1)

def rt3 : Rat := (100000000 / 12262691 : Rat)
def tt3 : Rat := (rt3 - 1) / (rt3 + 1)

def rt4 : Rat := (100000000 / 1612683 : Rat)
def tt4 : Rat := (rt4 - 1) / (rt4 + 1)

def rw1 : Rat := (1174168821 / 1000000000 : Rat)
def rw2 : Rat := (25921118 / 1000000000 : Rat)
def rw3 : Rat := (118647936 / 1000000000 : Rat)
def rw4 : Rat := (180553554 / 1000000000 : Rat)

def yHiLowerRat : Rat :=
    - atanhUpperRat 30 tt0
  + rw1 * atanhLowerRat 150 tt1
  + rw2 * atanhLowerRat 150 tt2
  + rw3 * atanhLowerRat 150 tt3
  + rw4 * atanhLowerRat 150 tt4

theorem yHiLowerRat_pos : 0 < yHiLowerRat := by
  native_decide

theorem log_rt0_upper :
    Real.log (rt0 : ℝ) ≤ ((atanhUpperRat 30 tt0 : Rat) : ℝ) := by
  apply log_upper_bound_of_rat
  · norm_num [tt0, rt0]
  · norm_num [tt0, rt0]
  · norm_num [tt0, rt0]

theorem log_rt1_lower :
    ((atanhLowerRat 150 tt1 : Rat) : ℝ) ≤ Real.log (rt1 : ℝ) := by
  apply log_lower_bound_of_rat
  · norm_num [tt1, rt1]
  · norm_num [tt1, rt1]
  · norm_num [tt1, rt1]

theorem log_rt2_lower :
    ((atanhLowerRat 150 tt2 : Rat) : ℝ) ≤ Real.log (rt2 : ℝ) := by
  apply log_lower_bound_of_rat
  · norm_num [tt2, rt2]
  · norm_num [tt2, rt2]
  · norm_num [tt2, rt2]

theorem log_rt3_lower :
    ((atanhLowerRat 150 tt3 : Rat) : ℝ) ≤ Real.log (rt3 : ℝ) := by
  apply log_lower_bound_of_rat
  · norm_num [tt3, rt3]
  · norm_num [tt3, rt3]
  · norm_num [tt3, rt3]

theorem log_rt4_lower :
    ((atanhLowerRat 150 tt4 : Rat) : ℝ) ≤ Real.log (rt4 : ℝ) := by
  apply log_lower_bound_of_rat
  · norm_num [tt4, rt4]
  · norm_num [tt4, rt4]
  · norm_num [tt4, rt4]

theorem V_yHi_positive_internal : 0 < V yHi := by
  have h0 := log_rt0_upper
  have h1 := log_rt1_lower
  have h2 := log_rt2_lower
  have h3 := log_rt3_lower
  have h4 := log_rt4_lower
  have hrat : (0 : ℝ) < (yHiLowerRat : ℝ) := by
    exact_mod_cast yHiLowerRat_pos
  have hv :
      V yHi =
          Real.log ((2806304 : ℝ) / 1000000)⁻¹
        + ((1174168821 : ℝ) / 1000000000) * Real.log ((99980399 : ℝ) / 100000000)⁻¹
        + ((25921118 : ℝ) / 1000000000) * Real.log ((23577203 : ℝ) / 100000000)⁻¹
        + ((118647936 : ℝ) / 1000000000) * Real.log ((12262691 : ℝ) / 100000000)⁻¹
        + ((180553554 : ℝ) / 1000000000) * Real.log ((1612683 : ℝ) / 100000000)⁻¹ := by
    norm_num [V, yHi, s1, s2, s3, s4, w1, w2, w3, w4, q]
  rw [hv]
  rw [Real.log_inv ((2806304 : ℝ) / 1000000)]
  norm_num [rt0, rt1, rt2, rt3, rt4, rw1, rw2, rw3, rw4, yHiLowerRat] at h0 h1 h2 h3 h4 hrat ⊢
  nlinarith

/-! ## Reusable rational lower bounds for `log d⁻¹` -/

def tInv (d : Rat) : Rat := (1 - d) / (1 + d)
def tSelf (d : Rat) : Rat := (d - 1) / (d + 1)

def logInvLowerRat (nPos nNeg : Nat) (d : Rat) : Rat :=
  if d < 1 then
    atanhLowerRat nPos (tInv d)
  else
    -atanhUpperRat nNeg (tSelf d)

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

theorem V_yLo_positive_internal : 0 < V yLo := by
  let d0 : Rat := (708 / 1000 : Rat)
  let d1 : Rat := (109850001 / 100000000 : Rat)
  let d2 : Rat := (186253197 / 100000000 : Rat)
  let d3 : Rat := (197567709 / 100000000 : Rat)
  let d4 : Rat := (208217717 / 100000000 : Rat)
  have hrat : (0 : Rat) < fiveLogLowerRat 150 30 d0 d1 d2 d3 d4 := by
    native_decide
  have hratR : (0 : ℝ) < (fiveLogLowerRat 150 30 d0 d1 d2 d3 d4 : Rat) := by
    exact_mod_cast hrat
  have hle : ((fiveLogLowerRat 150 30 d0 d1 d2 d3 d4 : Rat) : ℝ) ≤ V yLo := by
    simpa [V, yLo, s1, s2, s3, s4, q, d0, d1, d2, d3, d4] using
      (fiveLogLowerRat_le 150 30 d0 d1 d2 d3 d4
        (a0 := |yLo|) (a1 := |yLo - s1|) (a2 := |yLo - s2|)
        (a3 := |yLo - s3|) (a4 := |yLo - s4|)
        (by norm_num [d0]) (by norm_num [d1]) (by norm_num [d2])
        (by norm_num [d3]) (by norm_num [d4])
        (by norm_num [yLo, q]) (by norm_num [yLo, s1, q])
        (by norm_num [yLo, s2, q]) (by norm_num [yLo, s3, q])
        (by norm_num [yLo, s4, q])
        (by norm_num [yLo, d0, q]) (by norm_num [yLo, s1, d1, q])
        (by norm_num [yLo, s2, d2, q]) (by norm_num [yLo, s3, d3, q])
        (by norm_num [yLo, s4, d4, q]))
  exact hratR.trans_le hle

theorem V_r1_bracket_positive_internal
    {y : ℝ} (hy : y ∈ Icc (q 77003805 100000000) (q 77003806 100000000)) :
    0 < V y := by
  let d0 : Rat := (77003806 / 100000000 : Rat)
  let d1 : Rat := (103646196 / 100000000 : Rat)
  let d2 : Rat := (180049392 / 100000000 : Rat)
  let d3 : Rat := (191363904 / 100000000 : Rat)
  let d4 : Rat := (202013912 / 100000000 : Rat)
  have hrat : (0 : Rat) < fiveLogLowerRat 150 30 d0 d1 d2 d3 d4 := by
    native_decide
  have hratR : (0 : ℝ) < (fiveLogLowerRat 150 30 d0 d1 d2 d3 d4 : Rat) := by
    exact_mod_cast hrat
  have hy0 : 0 < y := by
    norm_num [q] at hy
    linarith
  have hy_s1 : y < s1 := by
    norm_num [q, s1] at hy ⊢
    linarith
  have hy_s2 : y < s2 := by
    norm_num [q, s2] at hy ⊢
    linarith
  have hy_s3 : y < s3 := by
    norm_num [q, s3] at hy ⊢
    linarith
  have hy_s4 : y < s4 := by
    norm_num [q, s4] at hy ⊢
    linarith
  have hle : ((fiveLogLowerRat 150 30 d0 d1 d2 d3 d4 : Rat) : ℝ) ≤ V y := by
    simpa [V] using
      (fiveLogLowerRat_le 150 30 d0 d1 d2 d3 d4
        (a0 := |y|) (a1 := |y - s1|) (a2 := |y - s2|)
        (a3 := |y - s3|) (a4 := |y - s4|)
        (by norm_num [d0]) (by norm_num [d1]) (by norm_num [d2])
        (by norm_num [d3]) (by norm_num [d4])
        (abs_pos.mpr (ne_of_gt hy0)) (abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt hy_s1)))
        (abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt hy_s2)))
        (abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt hy_s3)))
        (abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt hy_s4)))
        (by rw [abs_of_pos hy0]; norm_num [q, d0] at hy ⊢; linarith)
        (by rw [abs_of_neg (sub_neg.mpr hy_s1)]; norm_num [q, s1, d1] at hy ⊢; linarith)
        (by rw [abs_of_neg (sub_neg.mpr hy_s2)]; norm_num [q, s2, d2] at hy ⊢; linarith)
        (by rw [abs_of_neg (sub_neg.mpr hy_s3)]; norm_num [q, s3, d3] at hy ⊢; linarith)
        (by rw [abs_of_neg (sub_neg.mpr hy_s4)]; norm_num [q, s4, d4] at hy ⊢; linarith))
  exact hratR.trans_le hle

theorem V_r2_bracket_positive_internal
    {y : ℝ} (hy : y ∈ Icc (q 252642600 100000000) (q 252642601 100000000)) :
    0 < V y := by
  let d0 : Rat := (252642601 / 100000000 : Rat)
  let d1 : Rat := (71992600 / 100000000 : Rat)
  let d2 : Rat := (4420597 / 100000000 : Rat)
  let d3 : Rat := (15725109 / 100000000 : Rat)
  let d4 : Rat := (26375117 / 100000000 : Rat)
  have hrat : (0 : Rat) < fiveLogLowerRat 150 30 d0 d1 d2 d3 d4 := by
    native_decide
  have hratR : (0 : ℝ) < (fiveLogLowerRat 150 30 d0 d1 d2 d3 d4 : Rat) := by
    exact_mod_cast hrat
  have hy0 : 0 < y := by norm_num [q] at hy; linarith
  have hs1_y : s1 < y := by norm_num [q, s1] at hy ⊢; linarith
  have hy_s2 : y < s2 := by norm_num [q, s2] at hy ⊢; linarith
  have hy_s3 : y < s3 := by norm_num [q, s3] at hy ⊢; linarith
  have hy_s4 : y < s4 := by norm_num [q, s4] at hy ⊢; linarith
  have hle : ((fiveLogLowerRat 150 30 d0 d1 d2 d3 d4 : Rat) : ℝ) ≤ V y := by
    simpa [V] using
      (fiveLogLowerRat_le 150 30 d0 d1 d2 d3 d4
        (a0 := |y|) (a1 := |y - s1|) (a2 := |y - s2|)
        (a3 := |y - s3|) (a4 := |y - s4|)
        (by norm_num [d0]) (by norm_num [d1]) (by norm_num [d2])
        (by norm_num [d3]) (by norm_num [d4])
        (abs_pos.mpr (ne_of_gt hy0)) (abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hs1_y)))
        (abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt hy_s2)))
        (abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt hy_s3)))
        (abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt hy_s4)))
        (by rw [abs_of_pos hy0]; norm_num [q, d0] at hy ⊢; linarith)
        (by rw [abs_of_pos (sub_pos.mpr hs1_y)]; norm_num [q, s1, d1] at hy ⊢; linarith)
        (by rw [abs_of_neg (sub_neg.mpr hy_s2)]; norm_num [q, s2, d2] at hy ⊢; linarith)
        (by rw [abs_of_neg (sub_neg.mpr hy_s3)]; norm_num [q, s3, d3] at hy ⊢; linarith)
        (by rw [abs_of_neg (sub_neg.mpr hy_s4)]; norm_num [q, s4, d4] at hy ⊢; linarith))
  exact hratR.trans_le hle

theorem V_r3_bracket_positive_internal
    {y : ℝ} (hy : y ∈ Icc (q 260759965 100000000) (q 260759966 100000000)) :
    0 < V y := by
  let d0 : Rat := (260759966 / 100000000 : Rat)
  let d1 : Rat := (80109965 / 100000000 : Rat)
  let d2 : Rat := (3706769 / 100000000 : Rat)
  let d3 : Rat := (7607744 / 100000000 : Rat)
  let d4 : Rat := (18257752 / 100000000 : Rat)
  have hrat : (0 : Rat) < fiveLogLowerRat 150 30 d0 d1 d2 d3 d4 := by
    native_decide
  have hratR : (0 : ℝ) < (fiveLogLowerRat 150 30 d0 d1 d2 d3 d4 : Rat) := by
    exact_mod_cast hrat
  have hy0 : 0 < y := by norm_num [q] at hy; linarith
  have hs1_y : s1 < y := by norm_num [q, s1] at hy ⊢; linarith
  have hs2_y : s2 < y := by norm_num [q, s2] at hy ⊢; linarith
  have hy_s3 : y < s3 := by norm_num [q, s3] at hy ⊢; linarith
  have hy_s4 : y < s4 := by norm_num [q, s4] at hy ⊢; linarith
  have hle : ((fiveLogLowerRat 150 30 d0 d1 d2 d3 d4 : Rat) : ℝ) ≤ V y := by
    simpa [V] using
      (fiveLogLowerRat_le 150 30 d0 d1 d2 d3 d4
        (a0 := |y|) (a1 := |y - s1|) (a2 := |y - s2|)
        (a3 := |y - s3|) (a4 := |y - s4|)
        (by norm_num [d0]) (by norm_num [d1]) (by norm_num [d2])
        (by norm_num [d3]) (by norm_num [d4])
        (abs_pos.mpr (ne_of_gt hy0)) (abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hs1_y)))
        (abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hs2_y)))
        (abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt hy_s3)))
        (abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt hy_s4)))
        (by rw [abs_of_pos hy0]; norm_num [q, d0] at hy ⊢; linarith)
        (by rw [abs_of_pos (sub_pos.mpr hs1_y)]; norm_num [q, s1, d1] at hy ⊢; linarith)
        (by rw [abs_of_pos (sub_pos.mpr hs2_y)]; norm_num [q, s2, d2] at hy ⊢; linarith)
        (by rw [abs_of_neg (sub_neg.mpr hy_s3)]; norm_num [q, s3, d3] at hy ⊢; linarith)
        (by rw [abs_of_neg (sub_neg.mpr hy_s4)]; norm_num [q, s4, d4] at hy ⊢; linarith))
  exact hratR.trans_le hle

theorem V_r4_bracket_positive_internal
    {y : ℝ} (hy : y ∈ Icc (q 274249871 100000000) (q 274249872 100000000)) :
    0 < V y := by
  let d0 : Rat := (274249872 / 100000000 : Rat)
  let d1 : Rat := (93599871 / 100000000 : Rat)
  let d2 : Rat := (17196675 / 100000000 : Rat)
  let d3 : Rat := (5882163 / 100000000 : Rat)
  let d4 : Rat := (4767846 / 100000000 : Rat)
  have hrat : (0 : Rat) < fiveLogLowerRat 150 30 d0 d1 d2 d3 d4 := by
    native_decide
  have hratR : (0 : ℝ) < (fiveLogLowerRat 150 30 d0 d1 d2 d3 d4 : Rat) := by
    exact_mod_cast hrat
  have hy0 : 0 < y := by norm_num [q] at hy; linarith
  have hs1_y : s1 < y := by norm_num [q, s1] at hy ⊢; linarith
  have hs2_y : s2 < y := by norm_num [q, s2] at hy ⊢; linarith
  have hs3_y : s3 < y := by norm_num [q, s3] at hy ⊢; linarith
  have hy_s4 : y < s4 := by norm_num [q, s4] at hy ⊢; linarith
  have hle : ((fiveLogLowerRat 150 30 d0 d1 d2 d3 d4 : Rat) : ℝ) ≤ V y := by
    simpa [V] using
      (fiveLogLowerRat_le 150 30 d0 d1 d2 d3 d4
        (a0 := |y|) (a1 := |y - s1|) (a2 := |y - s2|)
        (a3 := |y - s3|) (a4 := |y - s4|)
        (by norm_num [d0]) (by norm_num [d1]) (by norm_num [d2])
        (by norm_num [d3]) (by norm_num [d4])
        (abs_pos.mpr (ne_of_gt hy0)) (abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hs1_y)))
        (abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hs2_y)))
        (abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hs3_y)))
        (abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt hy_s4)))
        (by rw [abs_of_pos hy0]; norm_num [q, d0] at hy ⊢; linarith)
        (by rw [abs_of_pos (sub_pos.mpr hs1_y)]; norm_num [q, s1, d1] at hy ⊢; linarith)
        (by rw [abs_of_pos (sub_pos.mpr hs2_y)]; norm_num [q, s2, d2] at hy ⊢; linarith)
        (by rw [abs_of_pos (sub_pos.mpr hs3_y)]; norm_num [q, s3, d3] at hy ⊢; linarith)
        (by rw [abs_of_neg (sub_neg.mpr hy_s4)]; norm_num [q, s4, d4] at hy ⊢; linarith))
  exact hratR.trans_le hle

theorem all_five_atom_log_checks_internal :
    0 < V yLo ∧
    (∀ y : ℝ, y ∈ Icc (q 77003805 100000000) (q 77003806 100000000) → 0 < V y) ∧
    (∀ y : ℝ, y ∈ Icc (q 252642600 100000000) (q 252642601 100000000) → 0 < V y) ∧
    (∀ y : ℝ, y ∈ Icc (q 260759965 100000000) (q 260759966 100000000) → 0 < V y) ∧
    (∀ y : ℝ, y ∈ Icc (q 274249871 100000000) (q 274249872 100000000) → 0 < V y) ∧
    0 < V yHi := by
  exact ⟨V_yLo_positive_internal,
    (fun y hy => V_r1_bracket_positive_internal hy),
    (fun y hy => V_r2_bracket_positive_internal hy),
    (fun y hy => V_r3_bracket_positive_internal hy),
    (fun y hy => V_r4_bracket_positive_internal hy),
    V_yHi_positive_internal⟩

end

end FiveAtom1806304Mathlib
end Erdos1038
