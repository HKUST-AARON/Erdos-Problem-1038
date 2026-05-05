import Mathlib

/-!
# Mathlib layer for the 560-block piecewise five-atom certificate (M = 1.814600)

This file defines the piecewise five-atom potential using `Real.log` and
provides the framework for proving positivity on each block.

The logarithm estimates use rational Taylor/atanh bounds from Mathlib:
* `Real.sum_range_le_log_div`
* `Real.log_div_le_sum_range_add`
-/

namespace Erdos1038
namespace PiecewiseFiveAtom181460Mathlib

noncomputable section

open Set

def q (n d : ℕ) : ℝ := (n : ℝ) / (d : ℝ)

/-- Target M = 1.814600 -/
def M : ℝ := q 1814600 1000000

/-- Forcing boundary B = 1.708 -/
def B : ℝ := q 1708 1000

/-- Tail length L = M - B = 0.106600 -/
def L : ℝ := M - B

/-- Number of blocks -/
def K : Nat := 560

/-- Block length h = L / K -/
def h : ℝ := L / K

/-- Right endpoint of block `i` in the positive parameter `r = -a`. -/
def blockA (i : Nat) : ℝ := M - (i : ℝ) * h

/-- Left endpoint of block `i` in the positive parameter `r = -a`. -/
def blockC (i : Nat) : ℝ := M - ((i : ℝ) + 1) * h

/-- The two required `y = x - a` domains for a block `[C,A]`. -/
def requiredDomain (C A : ℝ) : Set ℝ :=
  Icc (C - 1) (A - 1) ∪ Icc C (A + 1)

/-- The four shifts (d1, d2, d3, d4) -/
def d1 : ℝ := q 18146001 10000000   -- 1.8146001
def d2 : ℝ := q 255506 100000       -- 2.55506
def d3 : ℝ := q 2675215475 1000000000   -- 2.675215475
def d4 : ℝ := q 2781815575 1000000000   -- 2.781815575

/-- Swept intervals (as sets) -/
def I0 : Set ℝ := Icc (-M) (-B)
def I1 : Set ℝ := Icc (d1 - M) (d1 - B)
def I2 : Set ℝ := Icc (d2 - M) (d2 - B)
def I3 : Set ℝ := Icc (d3 - M) (d3 - B)
def I4 : Set ℝ := Icc (d4 - M) (d4 - B)
def LongInterval : Set ℝ := Ioo (-B) 0

/-- The five-atom potential for a given block with weights (w1, w2, w3, w4) -/
def V (w1 w2 w3 w4 : ℝ) (y : ℝ) : ℝ :=
    Real.log (|y|)⁻¹
  + w1 * Real.log (|y - d1|)⁻¹
  + w2 * Real.log (|y - d2|)⁻¹
  + w3 * Real.log (|y - d3|)⁻¹
  + w4 * Real.log (|y - d4|)⁻¹

/-- Verified: tail length -/
theorem tail_length : M - B = q 1066 10000 := by
  norm_num [M, B, q]

theorem h_pos : 0 < h := by
  norm_num [h, L, M, B, K, q]

theorem K_mul_h : (K : ℝ) * h = L := by
  norm_num [h, L, M, B, K, q]

theorem blockC_le_blockA (i : Nat) : blockC i ≤ blockA i := by
  have hh := h_pos
  simp [blockC, blockA]
  nlinarith

/--
The 560 blocks cover the full tail parameter interval `[B,M]`.
The endpoint case `r = B` is assigned to the last block.
-/
theorem block_cover_tail {r : ℝ} (hr : r ∈ Icc B M) :
    ∃ i : Nat, i < K ∧ r ∈ Icc (blockC i) (blockA i) := by
  by_cases hrB : r = B
  · refine ⟨559, by norm_num [K], ?_⟩
    simp [blockC, blockA, h, L, M, B, K, q, hrB]
    norm_num
  · have hBlt : B < r := by
      have hBr : B ≤ r := hr.1
      exact lt_of_le_of_ne hBr (Ne.symm hrB)
    let u : ℝ := (M - r) / h
    have hu_nonneg : 0 ≤ u := by
      have hrM : r ≤ M := hr.2
      have hh : 0 < h := h_pos
      exact div_nonneg (sub_nonneg.mpr hrM) hh.le
    have hu_lt_K : u < (K : ℝ) := by
      have hh : 0 < h := h_pos
      have hlt : M - r < M - B := by linarith
      have hKh : (K : ℝ) * h = M - B := by
        simpa [L] using K_mul_h
      have hlt' : M - r < (K : ℝ) * h := by
        simpa [hKh] using hlt
      rw [show (K : ℝ) = ((K : ℝ) * h) / h by field_simp [ne_of_gt hh]]
      exact div_lt_div_of_pos_right hlt' hh
    let i : Nat := Nat.floor u
    have hi_lt : i < K := by
      simpa [i] using (Nat.floor_lt (R := ℝ) (n := K) hu_nonneg).2 hu_lt_K
    refine ⟨i, hi_lt, ?_⟩
    have hle_u : (i : ℝ) ≤ u := by
      simpa [i] using Nat.floor_le (R := ℝ) hu_nonneg
    have hu_lt_succ : u < (i : ℝ) + 1 := by
      simpa [i] using Nat.lt_floor_add_one (R := ℝ) u
    have hh : 0 < h := h_pos
    have hright : r ≤ blockA i := by
      have : (i : ℝ) * h ≤ M - r := by
        calc
          (i : ℝ) * h ≤ u * h := mul_le_mul_of_nonneg_right hle_u hh.le
          _ = M - r := by
                simp [u]
                field_simp [ne_of_gt hh]
      simp [blockA]
      linarith
    have hleft : blockC i ≤ r := by
      have : M - r < ((i : ℝ) + 1) * h := by
        calc
          M - r = u * h := by
            simp [u]
            field_simp [ne_of_gt hh]
          _ < ((i : ℝ) + 1) * h := mul_lt_mul_of_pos_right hu_lt_succ hh
      simp [blockC]
      linarith
    exact ⟨hleft, hright⟩

/--
For a block `[C,A]`, normalized support `{-1} ∪ [0,1]` maps into exactly the
two required `y`-domains used by the checker.
-/
theorem requiredDomain_of_normalized_support
    {C A r x : ℝ}
    (hr : r ∈ Icc C A)
    (hx : x = -1 ∨ x ∈ Icc 0 1) :
    x + r ∈ requiredDomain C A := by
  rcases hx with hx | hx
  · left
    simp [hx] at *
    constructor <;> linarith
  · right
    simp at *
    constructor <;> linarith

theorem requiredDomain_of_negative_parameter
    {C A a x : ℝ}
    (ha : a ∈ Icc (-A) (-C))
    (hx : x = -1 ∨ x ∈ Icc 0 1) :
    x - a ∈ requiredDomain C A := by
  have hr : -a ∈ Icc C A := by
    simp at ha ⊢
    constructor <;> linarith
  simpa [sub_eq_add_neg] using requiredDomain_of_normalized_support (C := C) (A := A) hr hx

/-- Verified: first shift after M -/
theorem first_shift_after_M : M < d1 := by
  norm_num [M, d1, q]

/-- Verified: swept intervals are disjoint -/
theorem gap_1_2 : d1 + L < d2 := by
  norm_num [d1, d2, L, M, B, q]

theorem gap_2_3 : d2 + L < d3 := by
  norm_num [d2, d3, L, M, B, q]

theorem gap_3_4 : d3 + L < d4 := by
  norm_num [d3, d4, L, M, B, q]

/-- Interval disjointness theorems -/
theorem I0_disjoint_Long : Disjoint I0 LongInterval := by
  rw [Set.disjoint_left]
  intro x hx0 hxLong
  simp [I0, LongInterval] at hx0 hxLong
  linarith

theorem I1_disjoint_Long : Disjoint I1 LongInterval := by
  rw [Set.disjoint_left]
  intro x hx1 hxLong
  simp [I1, LongInterval] at hx1 hxLong
  have hpos : 0 < d1 - M := by norm_num [d1, M, q]
  linarith

theorem I2_disjoint_Long : Disjoint I2 LongInterval := by
  rw [Set.disjoint_left]
  intro x hx2 hxLong
  simp [I2, LongInterval] at hx2 hxLong
  have hpos : 0 < d2 - M := by norm_num [d2, M, q]
  linarith

theorem I3_disjoint_Long : Disjoint I3 LongInterval := by
  rw [Set.disjoint_left]
  intro x hx3 hxLong
  simp [I3, LongInterval] at hx3 hxLong
  have hpos : 0 < d3 - M := by norm_num [d3, M, q]
  linarith

theorem I4_disjoint_Long : Disjoint I4 LongInterval := by
  rw [Set.disjoint_left]
  intro x hx4 hxLong
  simp [I4, LongInterval] at hx4 hxLong
  have hpos : 0 < d4 - M := by norm_num [d4, M, q]
  linarith

theorem I0_I1_disjoint : Disjoint I0 I1 := by
  rw [Set.disjoint_left]
  intro x hx0 hx1
  simp [I0, I1] at hx0 hx1
  have h : -B < d1 - M := by norm_num [B, d1, M, q]
  linarith

theorem I1_I2_disjoint : Disjoint I1 I2 := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  simp [I1, I2] at hx1 hx2
  have h : d1 - B < d2 - M := by norm_num [B, d1, d2, M, q]
  linarith

theorem I2_I3_disjoint : Disjoint I2 I3 := by
  rw [Set.disjoint_left]
  intro x hx2 hx3
  simp [I2, I3] at hx2 hx3
  have h : d2 - B < d3 - M := by norm_num [B, d2, d3, M, q]
  linarith

theorem I3_I4_disjoint : Disjoint I3 I4 := by
  rw [Set.disjoint_left]
  intro x hx3 hx4
  simp [I3, I4] at hx3 hx4
  have h : d3 - B < d4 - M := by norm_num [B, d3, d4, M, q]
  linarith

/-- Master theorem: all swept intervals are pairwise disjoint -/
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

/-! ## Log positivity framework using atanh bounds -/

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
  | zero => simp [atanhLowerRat, atanhLowerReal]
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

/-! ## Rational bounds for log(d⁻¹) -/

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

end

end PiecewiseFiveAtom181460Mathlib
end Erdos1038
