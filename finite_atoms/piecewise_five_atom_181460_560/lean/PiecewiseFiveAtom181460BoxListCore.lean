import PiecewiseFiveAtom181460BoxCore

/-!
# List-based rational box certificates for the 560-block piecewise route

This layer packages each rational box as data.  Chunk files can then prove
`∀ b ∈ boxes, boxValid b` by `native_decide`, while this file supplies the
single theorem converting a valid rational box into real `Real.log` positivity.
-/

namespace Erdos1038
namespace PiecewiseFiveAtom181460Mathlib

noncomputable section

open Set

def rd1 : Rat := (18146001 : Rat) / 10000000
def rd2 : Rat := (255506 : Rat) / 100000
def rd3 : Rat := (2675215475 : Rat) / 1000000000
def rd4 : Rat := (2781815575 : Rat) / 1000000000

lemma rd1_cast : (rd1 : ℝ) = d1 := by norm_num [rd1, d1, q]
lemma rd2_cast : (rd2 : ℝ) = d2 := by norm_num [rd2, d2, q]
lemma rd3_cast : (rd3 : ℝ) = d3 := by norm_num [rd3, d3, q]
lemma rd4_cast : (rd4 : ℝ) = d4 := by norm_num [rd4, d4, q]

structure RatBox where
  w1 : Rat
  w2 : Rat
  w3 : Rat
  w4 : Rat
  L : Rat
  R : Rat
  D0 : Rat
  D1 : Rat
  D2 : Rat
  D3 : Rat
  D4 : Rat
  deriving DecidableEq, Repr

def RatBox.lower (b : RatBox) : Rat :=
  weightedLogLowerRat 150 60 b.w1 b.w2 b.w3 b.w4 b.D0 b.D1 b.D2 b.D3 b.D4

def RatBox.Valid (b : RatBox) : Prop :=
  0 ≤ b.w1 ∧ 0 ≤ b.w2 ∧ 0 ≤ b.w3 ∧ 0 ≤ b.w4 ∧
  b.L ≤ b.R ∧
  0 < b.D0 ∧ 0 < b.D1 ∧ 0 < b.D2 ∧ 0 < b.D3 ∧ 0 < b.D4 ∧
  0 < b.lower ∧
  |b.L - 0| ≤ b.D0 ∧ |b.R - 0| ≤ b.D0 ∧
  |b.L - rd1| ≤ b.D1 ∧ |b.R - rd1| ≤ b.D1 ∧
  |b.L - rd2| ≤ b.D2 ∧ |b.R - rd2| ≤ b.D2 ∧
  |b.L - rd3| ≤ b.D3 ∧ |b.R - rd3| ≤ b.D3 ∧
  |b.L - rd4| ≤ b.D4 ∧ |b.R - rd4| ≤ b.D4

instance (b : RatBox) : Decidable b.Valid := by
  unfold RatBox.Valid RatBox.lower weightedLogLowerRat logInvLowerRat
  infer_instance

/-- A rational interval `[lo, hi]` is covered by a list of closed rational boxes.

The recursive form is intentionally simple and decidable by `native_decide` for
generated chunk files: the first box must cover the current left endpoint, and
the remaining list must cover from the first box's right endpoint to `hi`.
-/
def RatBox.coversFromBool : List RatBox → Rat → Rat → Bool
  | [], _lo, _hi => false
  | [b], lo, hi => decide (b.L ≤ lo ∧ hi ≤ b.R)
  | b :: b' :: bs, lo, hi =>
      decide (b.L ≤ lo ∧ lo ≤ b.R) && coversFromBool (b' :: bs) b.R hi

def RatBox.CoversFrom (boxes : List RatBox) (lo hi : Rat) : Prop :=
  RatBox.coversFromBool boxes lo hi = true

instance (boxes : List RatBox) (lo hi : Rat) : Decidable (RatBox.CoversFrom boxes lo hi) := by
  unfold RatBox.CoversFrom
  infer_instance

lemma RatBox.mem_of_coversFrom
    {boxes : List RatBox} {lo hi : Rat}
    (hc : RatBox.CoversFrom boxes lo hi)
    {y : ℝ} (hy : y ∈ Icc (lo : ℝ) (hi : ℝ)) :
    ∃ b ∈ boxes, y ∈ Icc (b.L : ℝ) (b.R : ℝ) := by
  induction boxes generalizing lo with
  | nil =>
      simp [RatBox.CoversFrom, RatBox.coversFromBool] at hc
  | cons b bs ih =>
      cases bs with
      | nil =>
          have hcdec :
              decide (b.L ≤ lo ∧ hi ≤ b.R) = true := by
            simpa [RatBox.CoversFrom, RatBox.coversFromBool] using hc
          have hprop : b.L ≤ lo ∧ hi ≤ b.R := of_decide_eq_true hcdec
          rcases hprop with ⟨hbL, hhiR⟩
          refine ⟨b, by simp, ?_⟩
          constructor
          · have hbLR : (b.L : ℝ) ≤ (lo : ℝ) := by exact_mod_cast hbL
            linarith [hbLR, hy.1]
          · have hhiRR : (hi : ℝ) ≤ (b.R : ℝ) := by exact_mod_cast hhiR
            linarith [hhiRR, hy.2]
      | cons b' bs =>
          have hcbool :
              decide (b.L ≤ lo ∧ lo ≤ b.R) && RatBox.coversFromBool (b' :: bs) b.R hi = true := by
            simpa [RatBox.CoversFrom, RatBox.coversFromBool] using hc
          have hheadBool : decide (b.L ≤ lo ∧ lo ≤ b.R) = true := by
            cases h : decide (b.L ≤ lo ∧ lo ≤ b.R) <;> simp [h] at hcbool ⊢
          have hrest : RatBox.CoversFrom (b' :: bs) b.R hi := by
            unfold RatBox.CoversFrom
            cases h : decide (b.L ≤ lo ∧ lo ≤ b.R)
            · simp [h] at hcbool
            · simpa [h] using hcbool
          have hhead : b.L ≤ lo ∧ lo ≤ b.R := of_decide_eq_true hheadBool
          rcases hhead with ⟨hbL, hloR⟩
          by_cases hyR : y ≤ (b.R : ℝ)
          · refine ⟨b, by simp, ?_⟩
            constructor
            · have hbLR : (b.L : ℝ) ≤ (lo : ℝ) := by exact_mod_cast hbL
              linarith [hbLR, hy.1]
            · exact hyR
          · have hbRy : (b.R : ℝ) ≤ y := le_of_lt (lt_of_not_ge hyR)
            have hy' : y ∈ Icc (b.R : ℝ) (hi : ℝ) := ⟨hbRy, hy.2⟩
            rcases ih hrest hy' with ⟨b'', hb''mem, hb''y⟩
            exact ⟨b'', by simp [hb''mem], hb''y⟩

def RatBox.SameWeights (b : RatBox) (w1 w2 w3 w4 : Rat) : Prop :=
  b.w1 = w1 ∧ b.w2 = w2 ∧ b.w3 = w3 ∧ b.w4 = w4

instance (b : RatBox) (w1 w2 w3 w4 : Rat) :
    Decidable (RatBox.SameWeights b w1 w2 w3 w4) := by
  unfold RatBox.SameWeights
  infer_instance

lemma RatBox.real_abs_bound_zero_L {b : RatBox} (h : |b.L - 0| ≤ b.D0) :
    |(b.L : ℝ) - 0| ≤ (b.D0 : ℝ) := by
  have hc : ((|b.L - 0| : Rat) : ℝ) ≤ (b.D0 : ℝ) := by exact_mod_cast h
  simpa using hc

lemma RatBox.real_abs_bound_zero_R {b : RatBox} (h : |b.R - 0| ≤ b.D0) :
    |(b.R : ℝ) - 0| ≤ (b.D0 : ℝ) := by
  have hc : ((|b.R - 0| : Rat) : ℝ) ≤ (b.D0 : ℝ) := by exact_mod_cast h
  simpa using hc

lemma RatBox.real_abs_bound_d1_L {b : RatBox} (h : |b.L - rd1| ≤ b.D1) :
    |(b.L : ℝ) - d1| ≤ (b.D1 : ℝ) := by
  have hc : ((|b.L - rd1| : Rat) : ℝ) ≤ (b.D1 : ℝ) := by exact_mod_cast h
  simpa [rd1_cast] using hc

lemma RatBox.real_abs_bound_d1_R {b : RatBox} (h : |b.R - rd1| ≤ b.D1) :
    |(b.R : ℝ) - d1| ≤ (b.D1 : ℝ) := by
  have hc : ((|b.R - rd1| : Rat) : ℝ) ≤ (b.D1 : ℝ) := by exact_mod_cast h
  simpa [rd1_cast] using hc

lemma RatBox.real_abs_bound_d2_L {b : RatBox} (h : |b.L - rd2| ≤ b.D2) :
    |(b.L : ℝ) - d2| ≤ (b.D2 : ℝ) := by
  have hc : ((|b.L - rd2| : Rat) : ℝ) ≤ (b.D2 : ℝ) := by exact_mod_cast h
  simpa [rd2_cast] using hc

lemma RatBox.real_abs_bound_d2_R {b : RatBox} (h : |b.R - rd2| ≤ b.D2) :
    |(b.R : ℝ) - d2| ≤ (b.D2 : ℝ) := by
  have hc : ((|b.R - rd2| : Rat) : ℝ) ≤ (b.D2 : ℝ) := by exact_mod_cast h
  simpa [rd2_cast] using hc

lemma RatBox.real_abs_bound_d3_L {b : RatBox} (h : |b.L - rd3| ≤ b.D3) :
    |(b.L : ℝ) - d3| ≤ (b.D3 : ℝ) := by
  have hc : ((|b.L - rd3| : Rat) : ℝ) ≤ (b.D3 : ℝ) := by exact_mod_cast h
  simpa [rd3_cast] using hc

lemma RatBox.real_abs_bound_d3_R {b : RatBox} (h : |b.R - rd3| ≤ b.D3) :
    |(b.R : ℝ) - d3| ≤ (b.D3 : ℝ) := by
  have hc : ((|b.R - rd3| : Rat) : ℝ) ≤ (b.D3 : ℝ) := by exact_mod_cast h
  simpa [rd3_cast] using hc

lemma RatBox.real_abs_bound_d4_L {b : RatBox} (h : |b.L - rd4| ≤ b.D4) :
    |(b.L : ℝ) - d4| ≤ (b.D4 : ℝ) := by
  have hc : ((|b.L - rd4| : Rat) : ℝ) ≤ (b.D4 : ℝ) := by exact_mod_cast h
  simpa [rd4_cast] using hc

lemma RatBox.real_abs_bound_d4_R {b : RatBox} (h : |b.R - rd4| ≤ b.D4) :
    |(b.R : ℝ) - d4| ≤ (b.D4 : ℝ) := by
  have hc : ((|b.R - rd4| : Rat) : ℝ) ≤ (b.D4 : ℝ) := by exact_mod_cast h
  simpa [rd4_cast] using hc

lemma V_pos_of_valid_ratbox
    {b : RatBox} (hv : b.Valid) {y : ℝ}
    (hy : y ∈ Icc (b.L : ℝ) (b.R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ d1)
    (hy2ne : y ≠ d2)
    (hy3ne : y ≠ d3)
    (hy4ne : y ≠ d4) :
    0 < V (b.w1 : ℝ) (b.w2 : ℝ) (b.w3 : ℝ) (b.w4 : ℝ) y := by
  rcases hv with ⟨hw1, hw2, hw3, hw4, _hLR,
    hD0, hD1, hD2, hD3, hD4, hrat,
    hL0, hR0, hL1, hR1, hL2, hR2, hL3, hR3, hL4, hR4⟩
  exact V_pos_of_rat_box 150 60 b.w1 b.w2 b.w3 b.w4 b.L b.R b.D0 b.D1 b.D2 b.D3 b.D4
    hrat
    (by exact_mod_cast hw1) (by exact_mod_cast hw2) (by exact_mod_cast hw3) (by exact_mod_cast hw4)
    hD0 hD1 hD2 hD3 hD4
    (b.real_abs_bound_zero_L hL0) (b.real_abs_bound_zero_R hR0)
    (b.real_abs_bound_d1_L hL1) (b.real_abs_bound_d1_R hR1)
    (b.real_abs_bound_d2_L hL2) (b.real_abs_bound_d2_R hR2)
    (b.real_abs_bound_d3_L hL3) (b.real_abs_bound_d3_R hR3)
    (b.real_abs_bound_d4_L hL4) (b.real_abs_bound_d4_R hR4)
    hy hy0ne hy1ne hy2ne hy3ne hy4ne

end

end PiecewiseFiveAtom181460Mathlib
end Erdos1038
