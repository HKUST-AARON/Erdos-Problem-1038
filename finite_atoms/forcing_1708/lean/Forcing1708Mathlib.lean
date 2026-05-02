import Mathlib

/-!
# Mathlib interval kernel for the `[-1.7,0]` forcing branch

This file defines the two-parameter forcing family and proves the generic
soundness lemma used by the finite box certificate.
-/

namespace Erdos1038
namespace Forcing1708Mathlib

noncomputable section

open Set

def q (n d : ℕ) : ℝ := (n : ℝ) / (d : ℝ)

def aMin : ℝ := -(q 17 10)
def aMax : ℝ := -(q 1414213562373095 1000000000000000)
def bOffset : ℝ := q 182 100
def k : ℝ := q 1395 1000
def cShift : ℝ := q 1071 1000
def boundaryEps : ℝ := q 1 10000

def ADomain : Set ℝ := Icc aMin aMax
def SDomain : Set ℝ := Icc 0 1
def XDomain : Set ℝ := Icc 0 1

def bOf (a s : ℝ) : ℝ := s * (bOffset + a)
def wOf (a s : ℝ) : ℝ := k - bOf a s
def cOf (a s : ℝ) : ℝ := cShift - bOf a s

def cWeight (a s : ℝ) : ℝ :=
  (-boundaryEps - Real.log (-1 - a) - wOf a s * Real.log (1 + bOf a s)) /
    Real.log (q 2071 1000 - bOf a s)

def forcingPotentialWithC (a s x C : ℝ) : ℝ :=
    Real.log (|x - a|)⁻¹
  + wOf a s * Real.log (|x - bOf a s|)⁻¹
  + C * Real.log (|x - cOf a s|)⁻¹

def forcingPotential (a s x : ℝ) : ℝ :=
  forcingPotentialWithC a s x (cWeight a s)

/-! ## Domain arithmetic -/

theorem bLength_nonnegative {a : ℝ} (ha : a ∈ ADomain) :
    0 ≤ bOffset + a := by
  simp [ADomain, aMin, aMax, bOffset, q] at ha ⊢
  linarith

theorem bLength_upper {a : ℝ} (ha : a ∈ ADomain) :
    bOffset + a ≤ q 405786437626905 1000000000000000 := by
  simp [ADomain, aMin, aMax, bOffset, q] at ha ⊢
  linarith

theorem bOf_nonnegative {a s : ℝ} (ha : a ∈ ADomain) (hs : s ∈ SDomain) :
    0 ≤ bOf a s := by
  exact mul_nonneg hs.1 (bLength_nonnegative ha)

theorem bOf_upper {a s : ℝ} (ha : a ∈ ADomain) (hs : s ∈ SDomain) :
    bOf a s ≤ q 405786437626905 1000000000000000 := by
  have hs_le : s ≤ 1 := hs.2
  have hlen_nonneg : 0 ≤ bOffset + a := bLength_nonnegative ha
  have hlen_upper : bOffset + a ≤ q 405786437626905 1000000000000000 :=
    bLength_upper ha
  calc
    bOf a s = s * (bOffset + a) := rfl
    _ ≤ 1 * (bOffset + a) := by
      exact mul_le_mul_of_nonneg_right hs_le hlen_nonneg
    _ ≤ q 405786437626905 1000000000000000 := by
      simpa using hlen_upper

theorem wOf_positive {a s : ℝ} (ha : a ∈ ADomain) (hs : s ∈ SDomain) :
    0 < wOf a s := by
  have hb := bOf_upper ha hs
  simp [wOf, k, q] at hb ⊢
  linarith

theorem cOf_positive {a s : ℝ} (ha : a ∈ ADomain) (hs : s ∈ SDomain) :
    0 < cOf a s := by
  have hb := bOf_upper ha hs
  simp [cOf, cShift, q] at hb ⊢
  linarith

/-! ## Generic interval lower-bound kernel -/

structure BoxBounds where
  c_lo : ℝ
  c_hi : ℝ
  w_lo : ℝ
  w_hi : ℝ
  base_a : ℝ
  base_b : ℝ
  base_c : ℝ

/-- Product lower bound with positive weight interval. -/
def productLower (lo hi base : ℝ) : ℝ :=
  if 0 ≤ base then lo * base else hi * base

lemma productLower_le_mul
    {lo hi w base : ℝ}
    (hlo : lo ≤ w) (hhi : w ≤ hi) :
    productLower lo hi base ≤ w * base := by
  unfold productLower
  by_cases hbase : 0 ≤ base
  · simp [hbase]
    exact mul_le_mul_of_nonneg_right hlo hbase
  · simp [hbase]
    have hbase_nonpos : base ≤ 0 := le_of_not_ge hbase
    exact mul_le_mul_of_nonpos_right hhi hbase_nonpos

lemma log_inv_lower_of_distance_bound
    {distBound actual base : ℝ}
    (hactual_pos : 0 < actual)
    (hdist_pos : 0 < distBound)
    (hactual_le : actual ≤ distBound)
    (hbase : base ≤ Real.log distBound⁻¹) :
    base ≤ Real.log actual⁻¹ := by
  have hinv : distBound⁻¹ ≤ actual⁻¹ := by
    exact (inv_le_inv₀ hdist_pos hactual_pos).2 hactual_le
  exact hbase.trans (Real.log_le_log (inv_pos.mpr hdist_pos) hinv)

/--
Soundness of a single interval-box lower bound.  The caller supplies bounds for
`C`, `w`, and the three logarithmic base terms.
-/
theorem box_lower_bound_sound
    {a s x : ℝ} {B : BoxBounds}
    (hc_lo : B.c_lo ≤ cWeight a s)
    (hc_hi : cWeight a s ≤ B.c_hi)
    (hw_lo : B.w_lo ≤ wOf a s)
    (hw_hi : wOf a s ≤ B.w_hi)
    (hc_nonneg : 0 ≤ B.c_lo)
    (hw_nonneg : 0 ≤ B.w_lo)
    (ha_log : B.base_a ≤ Real.log (|x - a|)⁻¹)
    (hb_log : B.base_b ≤ Real.log (|x - bOf a s|)⁻¹)
    (hc_log : B.base_c ≤ Real.log (|x - cOf a s|)⁻¹)
    (hpos : 0 < B.base_a
      + productLower B.w_lo B.w_hi B.base_b
      + productLower B.c_lo B.c_hi B.base_c) :
    0 < forcingPotential a s x := by
  have hbmul : productLower B.w_lo B.w_hi B.base_b ≤
      wOf a s * Real.log (|x - bOf a s|)⁻¹ := by
    exact (productLower_le_mul hw_lo hw_hi).trans
      (mul_le_mul_of_nonneg_left hb_log (le_trans hw_nonneg hw_lo))
  have hcmul : productLower B.c_lo B.c_hi B.base_c ≤
      cWeight a s * Real.log (|x - cOf a s|)⁻¹ := by
    exact (productLower_le_mul hc_lo hc_hi).trans
      (mul_le_mul_of_nonneg_left hc_log (le_trans hc_nonneg hc_lo))
  have hle : B.base_a
      + productLower B.w_lo B.w_hi B.base_b
      + productLower B.c_lo B.c_hi B.base_c ≤ forcingPotential a s x := by
    unfold forcingPotential forcingPotentialWithC
    linarith
  exact hpos.trans_le hle

end

end Forcing1708Mathlib
end Erdos1038
