import Mathlib

/-!
# Analytic interval kernel for the `[-1.7,0]` forcing branch

This file supplies the reusable analytic part that is not contained in the
finite box data itself:

* rational Taylor bounds for `Real.log`;
* distance-to-log lower bounds for terms of the form `log |x-t|^{-1}`;
* interval bounds for the normalizing coefficient `C(a,b)`.

The box data files prove the finite rational arithmetic and coverage checks.
This file proves the general real-analysis lemmas used to turn those rational
checks into `Real.log` inequalities.
-/

namespace Erdos1038
namespace Forcing1708AnalyticKernel

noncomputable section

open Finset

def q (n d : ℕ) : ℝ := (n : ℝ) / (d : ℝ)

def bOffset : ℝ := q 182 100
def k : ℝ := q 1395 1000
def cShift : ℝ := q 1071 1000
def boundaryEps : ℝ := q 1 10000

def bOf (a s : ℝ) : ℝ := s * (bOffset + a)
def wOf (a s : ℝ) : ℝ := k - bOf a s

def cWeight (a s : ℝ) : ℝ :=
  (-boundaryEps - Real.log (-1 - a) - wOf a s * Real.log (1 + bOf a s)) /
    Real.log (q 2071 1000 - bOf a s)

/-! ## Rational log bounds -/

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
    _ ≤ 2 * (∑ i ∈ Finset.range n,
          (t : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)
        + (t : ℝ) ^ (2 * n + 1) / (1 - (t : ℝ) ^ 2)) := h2
    _ = 2 * ∑ i ∈ Finset.range n,
          (t : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)
        + 2 * (t : ℝ) ^ (2 * n + 1) / (1 - (t : ℝ) ^ 2) := by ring

def tInv (d : Rat) : Rat := (1 - d) / (1 + d)
def tSelf (d : Rat) : Rat := (d - 1) / (d + 1)

def logLowerRat (n : Nat) (d : Rat) : Rat :=
  if d < 1 then
    -atanhUpperRat n (tInv d)
  else
    atanhLowerRat n (tSelf d)

def logUpperRat (n : Nat) (d : Rat) : Rat :=
  if d < 1 then
    -atanhLowerRat n (tInv d)
  else
    atanhUpperRat n (tSelf d)

lemma tInv_cast_eq (d : Rat) :
    (tInv d : ℝ) = (1 - (d : ℝ)) / (1 + (d : ℝ)) := by
  unfold tInv
  norm_num

lemma tSelf_cast_eq (d : Rat) :
    (tSelf d : ℝ) = ((d : ℝ) - 1) / ((d : ℝ) + 1) := by
  unfold tSelf
  norm_num

lemma logLowerRat_le_log (n : Nat) (d : Rat) (hd : 0 < d) :
    ((logLowerRat n d : Rat) : ℝ) ≤ Real.log (d : ℝ) := by
  by_cases hlt : d < 1
  · simp [logLowerRat, hlt]
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
    have hr : ((1 / d : Rat) : ℝ) =
        (1 + (tInv d : ℝ)) / (1 - (tInv d : ℝ)) := by
      rw [htEq]
      norm_num
      field_simp [show (d : ℝ) ≠ 0 by positivity, denompos.ne']
      ring
    have hupper := log_upper_bound_of_rat (1 / d) (tInv d) n ht0 ht1 hr
    have hlog_inv : Real.log ((1 / d : Rat) : ℝ) = -Real.log (d : ℝ) := by
      rw [show ((1 / d : Rat) : ℝ) = ((d : ℝ)⁻¹) by norm_num]
      rw [Real.log_inv]
    linarith
  · simp [logLowerRat, hlt]
    have hge : (1 : Rat) ≤ d := le_of_not_gt hlt
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
    exact log_lower_bound_of_rat d (tSelf d) n ht0 ht1 hr

lemma log_le_logUpperRat (n : Nat) (d : Rat) (hd : 0 < d) :
    Real.log (d : ℝ) ≤ ((logUpperRat n d : Rat) : ℝ) := by
  by_cases hlt : d < 1
  · simp [logUpperRat, hlt]
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
    have hr : ((1 / d : Rat) : ℝ) =
        (1 + (tInv d : ℝ)) / (1 - (tInv d : ℝ)) := by
      rw [htEq]
      norm_num
      field_simp [show (d : ℝ) ≠ 0 by positivity, denompos.ne']
      ring
    have hlower := log_lower_bound_of_rat (1 / d) (tInv d) n ht0 ht1 hr
    have hlog_inv : Real.log ((1 / d : Rat) : ℝ) = -Real.log (d : ℝ) := by
      rw [show ((1 / d : Rat) : ℝ) = ((d : ℝ)⁻¹) by norm_num]
      rw [Real.log_inv]
    linarith
  · simp [logUpperRat, hlt]
    have hge : (1 : Rat) ≤ d := le_of_not_gt hlt
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
    exact log_upper_bound_of_rat d (tSelf d) n ht0 ht1 hr

/-! ## Distance-to-log bounds -/

lemma logInvLower_from_distance_bound
    (n : Nat) (d : Rat) {actual : ℝ}
    (hd : 0 < d) (hactual : 0 < actual) (hle : actual ≤ (d : ℝ)) :
    (-(logUpperRat n d : Rat) : ℝ) ≤ Real.log actual⁻¹ := by
  have hlog := log_le_logUpperRat n d hd
  have hdinv : ((d : ℝ)⁻¹) ≤ actual⁻¹ := by
    exact (inv_le_inv₀ (by exact_mod_cast hd : (0 : ℝ) < d) hactual).2 hle
  have hlog_inv : Real.log ((d : ℝ)⁻¹) ≤ Real.log actual⁻¹ :=
    Real.log_le_log (inv_pos.mpr (by exact_mod_cast hd)) hdinv
  rw [Real.log_inv] at hlog_inv
  linarith

/-! ## Power-of-two scaled log bounds

For small distances the direct atanh bound converges slowly.  The certificate
therefore scales `d` by a power of two so the argument is close to one, and
uses `log 2` separately.
-/

def pow2Rat (k : Nat) : Rat := (2 : Rat) ^ k

def logLowerScaledUpRat (n k : Nat) (d : Rat) : Rat :=
  logLowerRat n (d * pow2Rat k) - (k : Rat) * logUpperRat n (2 : Rat)

def logUpperScaledUpRat (n k : Nat) (d : Rat) : Rat :=
  logUpperRat n (d * pow2Rat k) - (k : Rat) * logLowerRat n (2 : Rat)

def logLowerScaledDownRat (n k : Nat) (d : Rat) : Rat :=
  logLowerRat n (d / pow2Rat k) + (k : Rat) * logLowerRat n (2 : Rat)

def logUpperScaledDownRat (n k : Nat) (d : Rat) : Rat :=
  logUpperRat n (d / pow2Rat k) + (k : Rat) * logUpperRat n (2 : Rat)

lemma pow2Rat_pos (k : Nat) : 0 < pow2Rat k := by
  unfold pow2Rat
  positivity

lemma pow2Rat_cast (k : Nat) :
    ((pow2Rat k : Rat) : ℝ) = (2 : ℝ) ^ k := by
  unfold pow2Rat
  norm_num

lemma logLowerScaledUpRat_le_log
    (n k : Nat) (d : Rat)
    (hd : 0 < d) (hscaled : 0 < d * pow2Rat k) :
    ((logLowerScaledUpRat n k d : Rat) : ℝ) ≤ Real.log (d : ℝ) := by
  have hScaledLog := logLowerRat_le_log n (d * pow2Rat k) hscaled
  have hTwoLog := log_le_logUpperRat n (2 : Rat) (by norm_num)
  have hpow : Real.log (((pow2Rat k : Rat) : ℝ)) = (k : ℝ) * Real.log (2 : ℝ) := by
    rw [pow2Rat_cast, Real.log_pow]
  have hmul : Real.log ((d : ℝ) * ((pow2Rat k : Rat) : ℝ)) =
      Real.log (d : ℝ) + Real.log (((pow2Rat k : Rat) : ℝ)) := by
    rw [Real.log_mul]
    · exact_mod_cast ne_of_gt hd
    · exact_mod_cast ne_of_gt (pow2Rat_pos k)
  norm_num [logLowerScaledUpRat] at hScaledLog hTwoLog ⊢
  rw [hmul, hpow] at hScaledLog
  nlinarith

lemma log_le_logUpperScaledUpRat
    (n k : Nat) (d : Rat)
    (hd : 0 < d) (hscaled : 0 < d * pow2Rat k) :
    Real.log (d : ℝ) ≤ ((logUpperScaledUpRat n k d : Rat) : ℝ) := by
  have hScaledLog := log_le_logUpperRat n (d * pow2Rat k) hscaled
  have hTwoLog := logLowerRat_le_log n (2 : Rat) (by norm_num)
  have hpow : Real.log (((pow2Rat k : Rat) : ℝ)) = (k : ℝ) * Real.log (2 : ℝ) := by
    rw [pow2Rat_cast, Real.log_pow]
  have hmul : Real.log ((d : ℝ) * ((pow2Rat k : Rat) : ℝ)) =
      Real.log (d : ℝ) + Real.log (((pow2Rat k : Rat) : ℝ)) := by
    rw [Real.log_mul]
    · exact_mod_cast ne_of_gt hd
    · exact_mod_cast ne_of_gt (pow2Rat_pos k)
  norm_num [logUpperScaledUpRat] at hScaledLog hTwoLog ⊢
  rw [hmul, hpow] at hScaledLog
  nlinarith

lemma logLowerScaledDownRat_le_log
    (n k : Nat) (d : Rat)
    (hd : 0 < d) (hscaled : 0 < d / pow2Rat k) :
    ((logLowerScaledDownRat n k d : Rat) : ℝ) ≤ Real.log (d : ℝ) := by
  have hScaledLog := logLowerRat_le_log n (d / pow2Rat k) hscaled
  have hTwoLog := logLowerRat_le_log n (2 : Rat) (by norm_num)
  have hpow : Real.log (((pow2Rat k : Rat) : ℝ)) = (k : ℝ) * Real.log (2 : ℝ) := by
    rw [pow2Rat_cast, Real.log_pow]
  have hdiv : Real.log ((d : ℝ) / ((pow2Rat k : Rat) : ℝ)) =
      Real.log (d : ℝ) - Real.log (((pow2Rat k : Rat) : ℝ)) := by
    rw [Real.log_div]
    · exact_mod_cast ne_of_gt hd
    · exact_mod_cast ne_of_gt (pow2Rat_pos k)
  norm_num [logLowerScaledDownRat] at hScaledLog hTwoLog ⊢
  rw [hdiv, hpow] at hScaledLog
  nlinarith

lemma log_le_logUpperScaledDownRat
    (n k : Nat) (d : Rat)
    (hd : 0 < d) (hscaled : 0 < d / pow2Rat k) :
    Real.log (d : ℝ) ≤ ((logUpperScaledDownRat n k d : Rat) : ℝ) := by
  have hScaledLog := log_le_logUpperRat n (d / pow2Rat k) hscaled
  have hTwoLog := log_le_logUpperRat n (2 : Rat) (by norm_num)
  have hpow : Real.log (((pow2Rat k : Rat) : ℝ)) = (k : ℝ) * Real.log (2 : ℝ) := by
    rw [pow2Rat_cast, Real.log_pow]
  have hdiv : Real.log ((d : ℝ) / ((pow2Rat k : Rat) : ℝ)) =
      Real.log (d : ℝ) - Real.log (((pow2Rat k : Rat) : ℝ)) := by
    rw [Real.log_div]
    · exact_mod_cast ne_of_gt hd
    · exact_mod_cast ne_of_gt (pow2Rat_pos k)
  norm_num [logUpperScaledDownRat] at hScaledLog hTwoLog ⊢
  rw [hdiv, hpow] at hScaledLog
  nlinarith

lemma abs_sub_le_of_interval
    {y lo hi D : ℝ}
    (hlo : lo ≤ y) (hhi : y ≤ hi)
    (hDlo : |lo| ≤ D) (hDhi : |hi| ≤ D) :
    |y| ≤ D := by
  have hcases : -D ≤ y ∧ y ≤ D := by
    constructor
    · have hneg : -D ≤ lo := by
        have := neg_abs_le lo
        linarith
      linarith
    · have hpos : hi ≤ D := by
        exact (le_abs_self hi).trans hDhi
      linarith
  exact abs_le.mpr hcases

/-! ## Coefficient interval bounds -/

def cNumerator (a b : ℝ) : ℝ :=
  -boundaryEps - Real.log (-1 - a) - (k - b) * Real.log (1 + b)

def cDenominator (b : ℝ) : ℝ :=
  Real.log (q 2071 1000 - b)

lemma cWeight_eq_b (a s : ℝ) :
    cWeight a s = cNumerator a (bOf a s) / cDenominator (bOf a s) := by
  unfold cWeight cNumerator cDenominator wOf
  ring

lemma div_lower_of_bounds
    {N D Nlo Dhi : ℝ}
    (hNlo : Nlo ≤ N) (hDhi : D ≤ Dhi)
    (hNlo_pos : 0 < Nlo) (hD_pos : 0 < D) (hDhi_pos : 0 < Dhi) :
    Nlo / Dhi ≤ N / D := by
  have hN_pos : 0 < N := hNlo_pos.trans_le hNlo
  have hmul : Nlo * D ≤ N * Dhi := by
    have h1 : Nlo * D ≤ Nlo * Dhi :=
      mul_le_mul_of_nonneg_left hDhi hNlo_pos.le
    have h2 : Nlo * Dhi ≤ N * Dhi :=
      mul_le_mul_of_nonneg_right hNlo hDhi_pos.le
    exact h1.trans h2
  rw [div_le_div_iff₀ hDhi_pos hD_pos]
  exact hmul

lemma div_upper_of_bounds
    {N D Nhi Dlo : ℝ}
    (hNhi : N ≤ Nhi) (hDlo : Dlo ≤ D)
    (hN_pos : 0 < N) (hDlo_pos : 0 < Dlo) (hD_pos : 0 < D) :
    N / D ≤ Nhi / Dlo := by
  have hNhi_pos : 0 < Nhi := hN_pos.trans_le hNhi
  have hmul : N * Dlo ≤ Nhi * D := by
    have h1 : N * Dlo ≤ N * D :=
      mul_le_mul_of_nonneg_left hDlo hN_pos.le
    have h2 : N * D ≤ Nhi * D :=
      mul_le_mul_of_nonneg_right hNhi hD_pos.le
    exact h1.trans h2
  rw [div_le_div_iff₀ hD_pos hDlo_pos]
  exact hmul

lemma cNumerator_lower_bound
    {a b logAUpper logBUpper wHi Nlo : ℝ}
    (hlogA : Real.log (-1 - a) ≤ logAUpper)
    (hlogB : Real.log (1 + b) ≤ logBUpper)
    (hw : k - b ≤ wHi)
    (hwHi_nonneg : 0 ≤ wHi)
    (hlogB_nonneg : 0 ≤ Real.log (1 + b))
    (hNlo : Nlo ≤ -boundaryEps - logAUpper - wHi * logBUpper) :
    Nlo ≤ cNumerator a b := by
  have hmul : (k - b) * Real.log (1 + b) ≤ wHi * logBUpper := by
    exact mul_le_mul hw hlogB hlogB_nonneg hwHi_nonneg
  unfold cNumerator
  linarith

lemma cNumerator_upper_bound
    {a b logALower logBLower wLo Nhi : ℝ}
    (hlogA : logALower ≤ Real.log (-1 - a))
    (hlogB : logBLower ≤ Real.log (1 + b))
    (hw : wLo ≤ k - b)
    (hwLo_nonneg : 0 ≤ wLo)
    (hlogBLower_nonneg : 0 ≤ logBLower)
    (hNhi : -boundaryEps - logALower - wLo * logBLower ≤ Nhi) :
    cNumerator a b ≤ Nhi := by
  have hmul : wLo * logBLower ≤ (k - b) * Real.log (1 + b) := by
    exact mul_le_mul hw hlogB hlogBLower_nonneg (le_trans hwLo_nonneg hw)
  unfold cNumerator
  linarith

lemma cWeight_lower_bound_from_num_den
    {a s Nlo Dhi : ℝ}
    (hNlo : Nlo ≤ cNumerator a (bOf a s))
    (hDhi : cDenominator (bOf a s) ≤ Dhi)
    (hNlo_pos : 0 < Nlo)
    (hD_pos : 0 < cDenominator (bOf a s))
    (hDhi_pos : 0 < Dhi) :
    Nlo / Dhi ≤ cWeight a s := by
  rw [cWeight_eq_b]
  exact div_lower_of_bounds hNlo hDhi hNlo_pos hD_pos hDhi_pos

lemma cWeight_upper_bound_from_num_den
    {a s Nhi Dlo : ℝ}
    (hNhi : cNumerator a (bOf a s) ≤ Nhi)
    (hDlo : Dlo ≤ cDenominator (bOf a s))
    (hN_pos : 0 < cNumerator a (bOf a s))
    (hDlo_pos : 0 < Dlo)
    (hD_pos : 0 < cDenominator (bOf a s)) :
    cWeight a s ≤ Nhi / Dlo := by
  rw [cWeight_eq_b]
  exact div_upper_of_bounds hNhi hDlo hN_pos hDlo_pos hD_pos

lemma cWeight_bounds_from_num_den
    {a s Nlo Nhi Dlo Dhi : ℝ}
    (hNlo : Nlo ≤ cNumerator a (bOf a s))
    (hNhi : cNumerator a (bOf a s) ≤ Nhi)
    (hDlo : Dlo ≤ cDenominator (bOf a s))
    (hDhi : cDenominator (bOf a s) ≤ Dhi)
    (hNlo_pos : 0 < Nlo)
    (hDlo_pos : 0 < Dlo)
    (hD_pos : 0 < cDenominator (bOf a s))
    (hDhi_pos : 0 < Dhi) :
    Nlo / Dhi ≤ cWeight a s ∧ cWeight a s ≤ Nhi / Dlo := by
  have hN_pos : 0 < cNumerator a (bOf a s) := hNlo_pos.trans_le hNlo
  exact ⟨
    cWeight_lower_bound_from_num_den hNlo hDhi hNlo_pos hD_pos hDhi_pos,
    cWeight_upper_bound_from_num_den hNhi hDlo hN_pos hDlo_pos hD_pos⟩

end

end Forcing1708AnalyticKernel
end Erdos1038
