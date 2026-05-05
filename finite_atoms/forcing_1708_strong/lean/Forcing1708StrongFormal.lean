import Mathlib

/-!
# Formal constants for the `[-1.708,0]` forcing branch

This file contains the exact parameter arithmetic for the stronger forcing
branch used before the `M = 1.814600` piecewise five-atom tail block.
-/

namespace Erdos1038
namespace Forcing1708Strong

noncomputable section

open Set

def q (n d : ℕ) : ℝ := (n : ℝ) / (d : ℝ)

def aMin : ℝ := -(q 427 250)
def aMax : ℝ := -(q 1414213562373095 1000000000000000)
def bOffset : ℝ := q 459 250
def k : ℝ := q 1395 1000
def cShift : ℝ := q 1071 1000
def boundaryEps : ℝ := q 1 10000

def bOf (a s : ℝ) : ℝ := s * (bOffset + a)
def wOf (a s : ℝ) : ℝ := k - bOf a s
def cOf (a s : ℝ) : ℝ := cShift - bOf a s

def ADomain : Set ℝ := Icc aMin aMax
def SDomain : Set ℝ := Icc 0 1
def XDomain : Set ℝ := Icc 0 1

/-! ## Domain endpoint arithmetic -/

theorem aMin_lt_aMax : aMin < aMax := by
  norm_num [aMin, aMax, q]

theorem aMax_lt_neg_one : aMax < -1 := by
  norm_num [aMax, q]

theorem bLength_nonnegative {a : ℝ} (ha : a ∈ ADomain) :
    0 ≤ bOffset + a := by
  simp [ADomain, aMin, aMax, bOffset, q] at ha ⊢
  linarith

theorem bLength_upper {a : ℝ} (ha : a ∈ ADomain) :
    bOffset + a ≤ q 421786437626905 1000000000000000 := by
  simp [ADomain, aMin, aMax, bOffset, q] at ha ⊢
  linarith

theorem bOf_nonnegative {a s : ℝ} (ha : a ∈ ADomain) (hs : s ∈ SDomain) :
    0 ≤ bOf a s := by
  exact mul_nonneg hs.1 (bLength_nonnegative ha)

theorem bOf_upper {a s : ℝ} (ha : a ∈ ADomain) (hs : s ∈ SDomain) :
    bOf a s ≤ q 421786437626905 1000000000000000 := by
  have hs_nonneg : 0 ≤ s := hs.1
  have hs_le : s ≤ 1 := hs.2
  have hlen_nonneg : 0 ≤ bOffset + a := bLength_nonnegative ha
  have hlen_upper : bOffset + a ≤ q 421786437626905 1000000000000000 :=
    bLength_upper ha
  calc
    bOf a s = s * (bOffset + a) := rfl
    _ ≤ 1 * (bOffset + a) := by
      exact mul_le_mul_of_nonneg_right hs_le hlen_nonneg
    _ ≤ q 421786437626905 1000000000000000 := by
      simpa using hlen_upper

theorem wOf_positive {a s : ℝ} (ha : a ∈ ADomain) (hs : s ∈ SDomain) :
    0 < wOf a s := by
  have hb := bOf_upper ha hs
  simp [wOf, k, q] at hb ⊢
  linarith

theorem cOf_lower {a s : ℝ} (ha : a ∈ ADomain) (hs : s ∈ SDomain) :
    q 649213562373095 1000000000000000 ≤ cOf a s := by
  have hb := bOf_upper ha hs
  simp [cOf, cShift, q] at hb ⊢
  linarith

theorem cOf_upper {a s : ℝ} (ha : a ∈ ADomain) (hs : s ∈ SDomain) :
    cOf a s ≤ cShift := by
  have hb := bOf_nonnegative ha hs
  simp [cOf] at hb ⊢
  linarith

theorem minus_one_minus_a_positive {a : ℝ} (ha : a ∈ ADomain) :
    0 < -1 - a := by
  have h : a ≤ aMax := ha.2
  have hmax : aMax < -1 := aMax_lt_neg_one
  linarith

theorem log_denominator_argument_positive {a s : ℝ}
    (ha : a ∈ ADomain) (hs : s ∈ SDomain) :
    1 < q 2071 1000 - bOf a s := by
  have hb := bOf_upper ha hs
  simp [q] at hb ⊢
  linarith

theorem forcing_domain_arithmetic_certificate {a s : ℝ}
    (ha : a ∈ ADomain) (hs : s ∈ SDomain) :
    0 ≤ bOf a s ∧
    bOf a s ≤ q 421786437626905 1000000000000000 ∧
    0 < wOf a s ∧
    q 649213562373095 1000000000000000 ≤ cOf a s ∧
    cOf a s ≤ cShift ∧
    0 < -1 - a ∧
    1 < q 2071 1000 - bOf a s := by
  exact ⟨bOf_nonnegative ha hs, bOf_upper ha hs, wOf_positive ha hs,
    cOf_lower ha hs, cOf_upper ha hs, minus_one_minus_a_positive ha,
    log_denominator_argument_positive ha hs⟩

end

end Forcing1708Strong
end Erdos1038
