import FiveAtom1806304Mathlib

/-!
# One-variable interval-box closure for the five-atom tail certificate

This file closes the pole-free one-variable positivity target by covering each
smooth component between consecutive poles with rational interval boxes.
-/

namespace Erdos1038
namespace FiveAtom1806304Mathlib

noncomputable section

open Set

def scaleN : Nat := 100000000
def qr (n : Nat) : Rat := (n : Rat) / (scaleN : Rat)

def s1N : Nat := 180650001
def s2N : Nat := 257053197
def s3N : Nat := 268367709
def s4N : Nat := 279017717

lemma qr_cast (n : Nat) : ((qr n : Rat) : ℝ) = q n scaleN := by
  unfold qr q scaleN
  norm_num

lemma qr_sub_cast {A B : Nat} (h : B ≤ A) :
    ((qr (A - B) : Rat) : ℝ) = q A scaleN - q B scaleN := by
  unfold qr q scaleN
  rw [Nat.cast_sub h]
  norm_num
  ring

lemma s1_eq_q : s1 = q s1N scaleN := by
  norm_num [s1, s1N, scaleN, q]

lemma s2_eq_q : s2 = q s2N scaleN := by
  norm_num [s2, s2N, scaleN, q]

lemma s3_eq_q : s3 = q s3N scaleN := by
  norm_num [s3, s3N, scaleN, q]

lemma s4_eq_q : s4 = q s4N scaleN := by
  norm_num [s4, s4N, scaleN, q]

lemma q_le_q_of_nat_le {A B : Nat} (h : A ≤ B) :
    q A scaleN ≤ q B scaleN := by
  unfold q scaleN
  apply div_le_div_of_nonneg_right
  · exact_mod_cast h
  · norm_num

lemma q_lt_q_of_nat_lt {A B : Nat} (h : A < B) :
    q A scaleN < q B scaleN := by
  unfold q scaleN
  apply div_lt_div_of_pos_right
  · exact_mod_cast h
  · norm_num

lemma V_pos_box_before_s1
    (L R : Nat)
    (hLpos : 0 < L)
    (hLR : L ≤ R)
    (hLlt : L < s1N)
    (hRle : R ≤ s1N)
    (hrat : (0 : Rat) <
      fiveLogLowerRat 150 30
        (qr R)
        (qr (s1N - L))
        (qr (s2N - L))
        (qr (s3N - L))
        (qr (s4N - L)))
    {y : ℝ}
    (hy : y ∈ Icc (q L scaleN) (q R scaleN))
    (hne1 : y ≠ s1) :
    0 < V y := by
  have hratR : (0 : ℝ) <
      ((fiveLogLowerRat 150 30
        (qr R)
        (qr (s1N - L))
        (qr (s2N - L))
        (qr (s3N - L))
        (qr (s4N - L)) : Rat) : ℝ) := by
    exact_mod_cast hrat
  have hLleS1 : L ≤ s1N := hLlt.le
  have hLleS2 : L ≤ s2N := by
    have hs : s1N ≤ s2N := by native_decide
    exact hLleS1.trans hs
  have hLleS3 : L ≤ s3N := by
    have hs : s1N ≤ s3N := by native_decide
    exact hLleS1.trans hs
  have hLleS4 : L ≤ s4N := by
    have hs : s1N ≤ s4N := by native_decide
    exact hLleS1.trans hs
  have hy0 : 0 < y := by
    have h : (0 : ℝ) < q L scaleN := by
      unfold q scaleN
      positivity
    exact lt_of_lt_of_le h hy.1
  have hys1le : y ≤ s1 := by
    have hRleR : q R scaleN ≤ s1 := by
      rw [s1_eq_q]
      unfold q scaleN
      apply div_le_div_of_nonneg_right
      · exact_mod_cast hRle
      · norm_num
    exact hy.2.trans hRleR
  have hys1 : y < s1 := lt_of_le_of_ne hys1le hne1
  have hys2 : y < s2 := by
    have hs : s1 < s2 := by norm_num [s1, s2, q]
    exact hys1.trans hs
  have hys3 : y < s3 := by
    have hs : s1 < s3 := by norm_num [s1, s3, q]
    exact hys1.trans hs
  have hys4 : y < s4 := by
    have hs : s1 < s4 := by norm_num [s1, s4, q]
    exact hys1.trans hs
  have hle : ((fiveLogLowerRat 150 30
        (qr R)
        (qr (s1N - L))
        (qr (s2N - L))
        (qr (s3N - L))
        (qr (s4N - L)) : Rat) : ℝ) ≤ V y := by
    simpa [V] using
      (fiveLogLowerRat_le 150 30
        (qr R)
        (qr (s1N - L))
        (qr (s2N - L))
        (qr (s3N - L))
        (qr (s4N - L))
        (a0 := |y|) (a1 := |y - s1|) (a2 := |y - s2|)
        (a3 := |y - s3|) (a4 := |y - s4|)
        (by
          unfold qr scaleN
          exact div_pos (by exact_mod_cast (lt_of_lt_of_le hLpos hLR)) (by norm_num))
        (by
          unfold qr scaleN
          exact div_pos (by exact_mod_cast (Nat.sub_pos_of_lt hLlt)) (by norm_num))
        (by
          unfold qr scaleN
          have h : L < s2N := hLlt.trans (by native_decide)
          exact div_pos (by exact_mod_cast (Nat.sub_pos_of_lt h)) (by norm_num))
        (by
          unfold qr scaleN
          have h : L < s3N := hLlt.trans (by native_decide)
          exact div_pos (by exact_mod_cast (Nat.sub_pos_of_lt h)) (by norm_num))
        (by
          unfold qr scaleN
          have h : L < s4N := hLlt.trans (by native_decide)
          exact div_pos (by exact_mod_cast (Nat.sub_pos_of_lt h)) (by norm_num))
        (abs_pos.mpr (ne_of_gt hy0))
        (abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt hys1)))
        (abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt hys2)))
        (abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt hys3)))
        (abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt hys4)))
        (by
          rw [abs_of_pos hy0]
          simpa [qr_cast] using hy.2)
        (by
          rw [abs_of_neg (sub_neg.mpr hys1)]
          have hdist : ((qr (s1N - L) : Rat) : ℝ) = s1 - q L scaleN := by
            rw [s1_eq_q, qr_sub_cast hLleS1]
          rw [hdist]
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            (sub_le_sub_left hy.1 s1))
        (by
          rw [abs_of_neg (sub_neg.mpr hys2)]
          have hdist : ((qr (s2N - L) : Rat) : ℝ) = s2 - q L scaleN := by
            rw [s2_eq_q, qr_sub_cast hLleS2]
          rw [hdist]
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            (sub_le_sub_left hy.1 s2))
        (by
          rw [abs_of_neg (sub_neg.mpr hys3)]
          have hdist : ((qr (s3N - L) : Rat) : ℝ) = s3 - q L scaleN := by
            rw [s3_eq_q, qr_sub_cast hLleS3]
          rw [hdist]
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            (sub_le_sub_left hy.1 s3))
        (by
          rw [abs_of_neg (sub_neg.mpr hys4)]
          have hdist : ((qr (s4N - L) : Rat) : ℝ) = s4 - q L scaleN := by
            rw [s4_eq_q, qr_sub_cast hLleS4]
          rw [hdist]
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            (sub_le_sub_left hy.1 s4))
      )
  exact hratR.trans_le hle

lemma V_pos_box_s1_s2
    (L R : Nat)
    (_hLR : L ≤ R)
    (hS1leL : s1N ≤ L)
    (hS1ltR : s1N < R)
    (hLltS2 : L < s2N)
    (hRleS2 : R ≤ s2N)
    (hrat : (0 : Rat) <
      fiveLogLowerRat 150 30
        (qr R)
        (qr (R - s1N))
        (qr (s2N - L))
        (qr (s3N - L))
        (qr (s4N - L)))
    {y : ℝ}
    (hy : y ∈ Icc (q L scaleN) (q R scaleN))
    (hne1 : y ≠ s1)
    (hne2 : y ≠ s2) :
    0 < V y := by
  have hratR : (0 : ℝ) <
      ((fiveLogLowerRat 150 30
        (qr R) (qr (R - s1N)) (qr (s2N - L))
        (qr (s3N - L)) (qr (s4N - L)) : Rat) : ℝ) := by
    exact_mod_cast hrat
  have hLleS2 : L ≤ s2N := hLltS2.le
  have hLleS3 : L ≤ s3N := hLleS2.trans (by native_decide)
  have hLleS4 : L ≤ s4N := hLleS2.trans (by native_decide)
  have hRpos : 0 < R := by
    exact lt_of_lt_of_le (by native_decide : 0 < s1N) hS1ltR.le
  have hy0 : 0 < y := by
    have h : 0 < q L scaleN := by
      have hLpos : 0 < L := lt_of_lt_of_le (by native_decide : 0 < s1N) hS1leL
      unfold q scaleN
      positivity
    exact lt_of_lt_of_le h hy.1
  have hs1le_y : s1 ≤ y := by
    have hq : s1 ≤ q L scaleN := by
      rw [s1_eq_q]
      exact q_le_q_of_nat_le hS1leL
    exact hq.trans hy.1
  have hs1y : s1 < y := lt_of_le_of_ne hs1le_y hne1.symm
  have hys2le : y ≤ s2 := by
    have hq : q R scaleN ≤ s2 := by
      rw [s2_eq_q]
      exact q_le_q_of_nat_le hRleS2
    exact hy.2.trans hq
  have hys2 : y < s2 := lt_of_le_of_ne hys2le hne2
  have hys3 : y < s3 := hys2.trans (by norm_num [s2, s3, q])
  have hys4 : y < s4 := hys2.trans (by norm_num [s2, s4, q])
  have hle : ((fiveLogLowerRat 150 30
        (qr R) (qr (R - s1N)) (qr (s2N - L))
        (qr (s3N - L)) (qr (s4N - L)) : Rat) : ℝ) ≤ V y := by
    simpa [V] using
      (fiveLogLowerRat_le 150 30
        (qr R) (qr (R - s1N)) (qr (s2N - L))
        (qr (s3N - L)) (qr (s4N - L))
        (a0 := |y|) (a1 := |y - s1|) (a2 := |y - s2|)
        (a3 := |y - s3|) (a4 := |y - s4|)
        (by unfold qr scaleN; exact div_pos (by exact_mod_cast hRpos) (by norm_num))
        (by unfold qr scaleN; exact div_pos (by exact_mod_cast (Nat.sub_pos_of_lt hS1ltR)) (by norm_num))
        (by unfold qr scaleN; exact div_pos (by exact_mod_cast (Nat.sub_pos_of_lt hLltS2)) (by norm_num))
        (by
          unfold qr scaleN
          have h : L < s3N := hLltS2.trans (by native_decide)
          exact div_pos (by exact_mod_cast (Nat.sub_pos_of_lt h)) (by norm_num))
        (by
          unfold qr scaleN
          have h : L < s4N := hLltS2.trans (by native_decide)
          exact div_pos (by exact_mod_cast (Nat.sub_pos_of_lt h)) (by norm_num))
        (abs_pos.mpr (ne_of_gt hy0))
        (abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hs1y)))
        (abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt hys2)))
        (abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt hys3)))
        (abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt hys4)))
        (by rw [abs_of_pos hy0]; simpa [qr_cast] using hy.2)
        (by
          rw [abs_of_pos (sub_pos.mpr hs1y)]
          have hdist : ((qr (R - s1N) : Rat) : ℝ) = q R scaleN - s1 := by
            rw [s1_eq_q, qr_sub_cast hS1ltR.le]
          rw [hdist]
          exact sub_le_sub_right hy.2 s1)
        (by
          rw [abs_of_neg (sub_neg.mpr hys2)]
          have hdist : ((qr (s2N - L) : Rat) : ℝ) = s2 - q L scaleN := by
            rw [s2_eq_q, qr_sub_cast hLleS2]
          rw [hdist]
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            (sub_le_sub_left hy.1 s2))
        (by
          rw [abs_of_neg (sub_neg.mpr hys3)]
          have hdist : ((qr (s3N - L) : Rat) : ℝ) = s3 - q L scaleN := by
            rw [s3_eq_q, qr_sub_cast hLleS3]
          rw [hdist]
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            (sub_le_sub_left hy.1 s3))
        (by
          rw [abs_of_neg (sub_neg.mpr hys4)]
          have hdist : ((qr (s4N - L) : Rat) : ℝ) = s4 - q L scaleN := by
            rw [s4_eq_q, qr_sub_cast hLleS4]
          rw [hdist]
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            (sub_le_sub_left hy.1 s4))
      )
  exact hratR.trans_le hle

lemma V_pos_box_s2_s3
    (L R : Nat)
    (_hLR : L ≤ R)
    (hS2leL : s2N ≤ L)
    (hS2ltR : s2N < R)
    (hLltS3 : L < s3N)
    (hRleS3 : R ≤ s3N)
    (hrat : (0 : Rat) <
      fiveLogLowerRat 150 30
        (qr R)
        (qr (R - s1N))
        (qr (R - s2N))
        (qr (s3N - L))
        (qr (s4N - L)))
    {y : ℝ}
    (hy : y ∈ Icc (q L scaleN) (q R scaleN))
    (hne2 : y ≠ s2)
    (hne3 : y ≠ s3) :
    0 < V y := by
  have hratR : (0 : ℝ) <
      ((fiveLogLowerRat 150 30
        (qr R) (qr (R - s1N)) (qr (R - s2N))
        (qr (s3N - L)) (qr (s4N - L)) : Rat) : ℝ) := by
    exact_mod_cast hrat
  have hS1leR : s1N ≤ R := (by native_decide : s1N ≤ s2N).trans (hS2ltR.le)
  have hLleS3 : L ≤ s3N := hLltS3.le
  have hLleS4 : L ≤ s4N := hLleS3.trans (by native_decide)
  have hRpos : 0 < R := lt_of_lt_of_le (by native_decide : 0 < s2N) hS2ltR.le
  have hy0 : 0 < y := by
    have h : 0 < q L scaleN := by
      have hLpos : 0 < L := lt_of_lt_of_le (by native_decide : 0 < s2N) hS2leL
      unfold q scaleN
      positivity
    exact lt_of_lt_of_le h hy.1
  have hs2le_y : s2 ≤ y := by
    have hq : s2 ≤ q L scaleN := by
      rw [s2_eq_q]
      exact q_le_q_of_nat_le hS2leL
    exact hq.trans hy.1
  have hs2y : s2 < y := lt_of_le_of_ne hs2le_y hne2.symm
  have hs1y : s1 < y := (by norm_num [s1, s2, q] : s1 < s2).trans hs2y
  have hys3le : y ≤ s3 := by
    have hq : q R scaleN ≤ s3 := by
      rw [s3_eq_q]
      exact q_le_q_of_nat_le hRleS3
    exact hy.2.trans hq
  have hys3 : y < s3 := lt_of_le_of_ne hys3le hne3
  have hys4 : y < s4 := hys3.trans (by norm_num [s3, s4, q])
  have hle : ((fiveLogLowerRat 150 30
        (qr R) (qr (R - s1N)) (qr (R - s2N))
        (qr (s3N - L)) (qr (s4N - L)) : Rat) : ℝ) ≤ V y := by
    simpa [V] using
      (fiveLogLowerRat_le 150 30
        (qr R) (qr (R - s1N)) (qr (R - s2N))
        (qr (s3N - L)) (qr (s4N - L))
        (a0 := |y|) (a1 := |y - s1|) (a2 := |y - s2|)
        (a3 := |y - s3|) (a4 := |y - s4|)
        (by unfold qr scaleN; exact div_pos (by exact_mod_cast hRpos) (by norm_num))
        (by
          unfold qr scaleN
          have h : s1N < R := lt_of_le_of_lt (by native_decide : s1N ≤ s2N) hS2ltR
          exact div_pos (by exact_mod_cast (Nat.sub_pos_of_lt h)) (by norm_num))
        (by unfold qr scaleN; exact div_pos (by exact_mod_cast (Nat.sub_pos_of_lt hS2ltR)) (by norm_num))
        (by unfold qr scaleN; exact div_pos (by exact_mod_cast (Nat.sub_pos_of_lt hLltS3)) (by norm_num))
        (by
          unfold qr scaleN
          have h : L < s4N := hLltS3.trans (by native_decide)
          exact div_pos (by exact_mod_cast (Nat.sub_pos_of_lt h)) (by norm_num))
        (abs_pos.mpr (ne_of_gt hy0))
        (abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hs1y)))
        (abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hs2y)))
        (abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt hys3)))
        (abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt hys4)))
        (by rw [abs_of_pos hy0]; simpa [qr_cast] using hy.2)
        (by
          rw [abs_of_pos (sub_pos.mpr hs1y)]
          have hdist : ((qr (R - s1N) : Rat) : ℝ) = q R scaleN - s1 := by
            rw [s1_eq_q, qr_sub_cast hS1leR]
          rw [hdist]
          exact sub_le_sub_right hy.2 s1)
        (by
          rw [abs_of_pos (sub_pos.mpr hs2y)]
          have hdist : ((qr (R - s2N) : Rat) : ℝ) = q R scaleN - s2 := by
            rw [s2_eq_q, qr_sub_cast hS2ltR.le]
          rw [hdist]
          exact sub_le_sub_right hy.2 s2)
        (by
          rw [abs_of_neg (sub_neg.mpr hys3)]
          have hdist : ((qr (s3N - L) : Rat) : ℝ) = s3 - q L scaleN := by
            rw [s3_eq_q, qr_sub_cast hLleS3]
          rw [hdist]
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            (sub_le_sub_left hy.1 s3))
        (by
          rw [abs_of_neg (sub_neg.mpr hys4)]
          have hdist : ((qr (s4N - L) : Rat) : ℝ) = s4 - q L scaleN := by
            rw [s4_eq_q, qr_sub_cast hLleS4]
          rw [hdist]
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            (sub_le_sub_left hy.1 s4))
      )
  exact hratR.trans_le hle

lemma V_pos_box_s3_s4
    (L R : Nat)
    (_hLR : L ≤ R)
    (hS3leL : s3N ≤ L)
    (hS3ltR : s3N < R)
    (hLltS4 : L < s4N)
    (hRleS4 : R ≤ s4N)
    (hrat : (0 : Rat) <
      fiveLogLowerRat 150 30
        (qr R)
        (qr (R - s1N))
        (qr (R - s2N))
        (qr (R - s3N))
        (qr (s4N - L)))
    {y : ℝ}
    (hy : y ∈ Icc (q L scaleN) (q R scaleN))
    (hne3 : y ≠ s3)
    (hne4 : y ≠ s4) :
    0 < V y := by
  have hratR : (0 : ℝ) <
      ((fiveLogLowerRat 150 30
        (qr R) (qr (R - s1N)) (qr (R - s2N))
        (qr (R - s3N)) (qr (s4N - L)) : Rat) : ℝ) := by
    exact_mod_cast hrat
  have hS1leR : s1N ≤ R := (by native_decide : s1N ≤ s3N).trans hS3ltR.le
  have hS2leR : s2N ≤ R := (by native_decide : s2N ≤ s3N).trans hS3ltR.le
  have hLleS4 : L ≤ s4N := hLltS4.le
  have hRpos : 0 < R := lt_of_lt_of_le (by native_decide : 0 < s3N) hS3ltR.le
  have hy0 : 0 < y := by
    have h : 0 < q L scaleN := by
      have hLpos : 0 < L := lt_of_lt_of_le (by native_decide : 0 < s3N) hS3leL
      unfold q scaleN
      positivity
    exact lt_of_lt_of_le h hy.1
  have hs3le_y : s3 ≤ y := by
    have hq : s3 ≤ q L scaleN := by
      rw [s3_eq_q]
      exact q_le_q_of_nat_le hS3leL
    exact hq.trans hy.1
  have hs3y : s3 < y := lt_of_le_of_ne hs3le_y hne3.symm
  have hs2y : s2 < y := (by norm_num [s2, s3, q] : s2 < s3).trans hs3y
  have hs1y : s1 < y := (by norm_num [s1, s3, q] : s1 < s3).trans hs3y
  have hys4le : y ≤ s4 := by
    have hq : q R scaleN ≤ s4 := by
      rw [s4_eq_q]
      exact q_le_q_of_nat_le hRleS4
    exact hy.2.trans hq
  have hys4 : y < s4 := lt_of_le_of_ne hys4le hne4
  have hle : ((fiveLogLowerRat 150 30
        (qr R) (qr (R - s1N)) (qr (R - s2N))
        (qr (R - s3N)) (qr (s4N - L)) : Rat) : ℝ) ≤ V y := by
    simpa [V] using
      (fiveLogLowerRat_le 150 30
        (qr R) (qr (R - s1N)) (qr (R - s2N))
        (qr (R - s3N)) (qr (s4N - L))
        (a0 := |y|) (a1 := |y - s1|) (a2 := |y - s2|)
        (a3 := |y - s3|) (a4 := |y - s4|)
        (by unfold qr scaleN; exact div_pos (by exact_mod_cast hRpos) (by norm_num))
        (by
          unfold qr scaleN
          have h : s1N < R := lt_of_le_of_lt (by native_decide : s1N ≤ s3N) hS3ltR
          exact div_pos (by exact_mod_cast (Nat.sub_pos_of_lt h)) (by norm_num))
        (by
          unfold qr scaleN
          have h : s2N < R := lt_of_le_of_lt (by native_decide : s2N ≤ s3N) hS3ltR
          exact div_pos (by exact_mod_cast (Nat.sub_pos_of_lt h)) (by norm_num))
        (by unfold qr scaleN; exact div_pos (by exact_mod_cast (Nat.sub_pos_of_lt hS3ltR)) (by norm_num))
        (by unfold qr scaleN; exact div_pos (by exact_mod_cast (Nat.sub_pos_of_lt hLltS4)) (by norm_num))
        (abs_pos.mpr (ne_of_gt hy0))
        (abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hs1y)))
        (abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hs2y)))
        (abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hs3y)))
        (abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt hys4)))
        (by rw [abs_of_pos hy0]; simpa [qr_cast] using hy.2)
        (by
          rw [abs_of_pos (sub_pos.mpr hs1y)]
          have hdist : ((qr (R - s1N) : Rat) : ℝ) = q R scaleN - s1 := by
            rw [s1_eq_q, qr_sub_cast hS1leR]
          rw [hdist]
          exact sub_le_sub_right hy.2 s1)
        (by
          rw [abs_of_pos (sub_pos.mpr hs2y)]
          have hdist : ((qr (R - s2N) : Rat) : ℝ) = q R scaleN - s2 := by
            rw [s2_eq_q, qr_sub_cast hS2leR]
          rw [hdist]
          exact sub_le_sub_right hy.2 s2)
        (by
          rw [abs_of_pos (sub_pos.mpr hs3y)]
          have hdist : ((qr (R - s3N) : Rat) : ℝ) = q R scaleN - s3 := by
            rw [s3_eq_q, qr_sub_cast hS3ltR.le]
          rw [hdist]
          exact sub_le_sub_right hy.2 s3)
        (by
          rw [abs_of_neg (sub_neg.mpr hys4)]
          have hdist : ((qr (s4N - L) : Rat) : ℝ) = s4 - q L scaleN := by
            rw [s4_eq_q, qr_sub_cast hLleS4]
          rw [hdist]
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            (sub_le_sub_left hy.1 s4))
      )
  exact hratR.trans_le hle

lemma V_pos_box_after_s4
    (L R : Nat)
    (_hLR : L ≤ R)
    (hS4leL : s4N ≤ L)
    (hS4ltR : s4N < R)
    (hrat : (0 : Rat) <
      fiveLogLowerRat 150 30
        (qr R)
        (qr (R - s1N))
        (qr (R - s2N))
        (qr (R - s3N))
        (qr (R - s4N)))
    {y : ℝ}
    (hy : y ∈ Icc (q L scaleN) (q R scaleN))
    (hne4 : y ≠ s4) :
    0 < V y := by
  have hratR : (0 : ℝ) <
      ((fiveLogLowerRat 150 30
        (qr R) (qr (R - s1N)) (qr (R - s2N))
        (qr (R - s3N)) (qr (R - s4N)) : Rat) : ℝ) := by
    exact_mod_cast hrat
  have hS1leR : s1N ≤ R := (by native_decide : s1N ≤ s4N).trans hS4ltR.le
  have hS2leR : s2N ≤ R := (by native_decide : s2N ≤ s4N).trans hS4ltR.le
  have hS3leR : s3N ≤ R := (by native_decide : s3N ≤ s4N).trans hS4ltR.le
  have hRpos : 0 < R := lt_of_lt_of_le (by native_decide : 0 < s4N) hS4ltR.le
  have hy0 : 0 < y := by
    have h : 0 < q L scaleN := by
      have hLpos : 0 < L := lt_of_lt_of_le (by native_decide : 0 < s4N) hS4leL
      unfold q scaleN
      positivity
    exact lt_of_lt_of_le h hy.1
  have hs4le_y : s4 ≤ y := by
    have hq : s4 ≤ q L scaleN := by
      rw [s4_eq_q]
      exact q_le_q_of_nat_le hS4leL
    exact hq.trans hy.1
  have hs4y : s4 < y := lt_of_le_of_ne hs4le_y hne4.symm
  have hs3y : s3 < y := (by norm_num [s3, s4, q] : s3 < s4).trans hs4y
  have hs2y : s2 < y := (by norm_num [s2, s4, q] : s2 < s4).trans hs4y
  have hs1y : s1 < y := (by norm_num [s1, s4, q] : s1 < s4).trans hs4y
  have hle : ((fiveLogLowerRat 150 30
        (qr R) (qr (R - s1N)) (qr (R - s2N))
        (qr (R - s3N)) (qr (R - s4N)) : Rat) : ℝ) ≤ V y := by
    simpa [V] using
      (fiveLogLowerRat_le 150 30
        (qr R) (qr (R - s1N)) (qr (R - s2N))
        (qr (R - s3N)) (qr (R - s4N))
        (a0 := |y|) (a1 := |y - s1|) (a2 := |y - s2|)
        (a3 := |y - s3|) (a4 := |y - s4|)
        (by unfold qr scaleN; exact div_pos (by exact_mod_cast hRpos) (by norm_num))
        (by
          unfold qr scaleN
          have h : s1N < R := lt_of_le_of_lt (by native_decide : s1N ≤ s4N) hS4ltR
          exact div_pos (by exact_mod_cast (Nat.sub_pos_of_lt h)) (by norm_num))
        (by
          unfold qr scaleN
          have h : s2N < R := lt_of_le_of_lt (by native_decide : s2N ≤ s4N) hS4ltR
          exact div_pos (by exact_mod_cast (Nat.sub_pos_of_lt h)) (by norm_num))
        (by
          unfold qr scaleN
          have h : s3N < R := lt_of_le_of_lt (by native_decide : s3N ≤ s4N) hS4ltR
          exact div_pos (by exact_mod_cast (Nat.sub_pos_of_lt h)) (by norm_num))
        (by unfold qr scaleN; exact div_pos (by exact_mod_cast (Nat.sub_pos_of_lt hS4ltR)) (by norm_num))
        (abs_pos.mpr (ne_of_gt hy0))
        (abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hs1y)))
        (abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hs2y)))
        (abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hs3y)))
        (abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hs4y)))
        (by rw [abs_of_pos hy0]; simpa [qr_cast] using hy.2)
        (by
          rw [abs_of_pos (sub_pos.mpr hs1y)]
          have hdist : ((qr (R - s1N) : Rat) : ℝ) = q R scaleN - s1 := by
            rw [s1_eq_q, qr_sub_cast hS1leR]
          rw [hdist]
          exact sub_le_sub_right hy.2 s1)
        (by
          rw [abs_of_pos (sub_pos.mpr hs2y)]
          have hdist : ((qr (R - s2N) : Rat) : ℝ) = q R scaleN - s2 := by
            rw [s2_eq_q, qr_sub_cast hS2leR]
          rw [hdist]
          exact sub_le_sub_right hy.2 s2)
        (by
          rw [abs_of_pos (sub_pos.mpr hs3y)]
          have hdist : ((qr (R - s3N) : Rat) : ℝ) = q R scaleN - s3 := by
            rw [s3_eq_q, qr_sub_cast hS3leR]
          rw [hdist]
          exact sub_le_sub_right hy.2 s3)
        (by
          rw [abs_of_pos (sub_pos.mpr hs4y)]
          have hdist : ((qr (R - s4N) : Rat) : ℝ) = q R scaleN - s4 := by
            rw [s4_eq_q, qr_sub_cast hS4ltR.le]
          rw [hdist]
          exact sub_le_sub_right hy.2 s4)
      )
  exact hratR.trans_le hle

theorem V_boxes_before_s1
    {y : ℝ}
    (hy : y ∈ Icc yLo s1)
    (hne1 : y ≠ s1)
    :
    0 < V y := by
  have hlo0 : q 70800000 scaleN ≤ y := by
    norm_num [yLo, q, scaleN] at hy ⊢
    exact hy.1
  have hhi0 : y ≤ q 180650001 scaleN := by
    simpa [s1_eq_q] using hy.2
  by_cases hcut0 : y ≤ q 77035381 scaleN
  ·
    by_cases hcut2 : y ≤ q 76458775 scaleN
    ·
      by_cases hcut4 : y ≤ q 75761485 scaleN
      ·
        by_cases hcut6 : y ≤ q 74903282 scaleN
        ·
          by_cases hcut8 : y ≤ q 73803710 scaleN
          ·
            by_cases hcut10 : y ≤ q 72730956 scaleN
            ·
              by_cases hcut12 : y ≤ q 71658203 scaleN
              ·
                by_cases hcut14 : y ≤ q 71229101 scaleN
                ·
                  by_cases hcut16 : y ≤ q 71014550 scaleN
                  ·
                    apply V_pos_box_before_s1 70800000 71014550
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo0, hcut16⟩
                    · exact hne1
                  ·
                    have hlo17 : q 71014550 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut16)
                    apply V_pos_box_before_s1 71014550 71229101
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo17, hcut14⟩
                    · exact hne1
                ·
                  have hlo15 : q 71229101 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut14)
                  by_cases hcut18 : y ≤ q 71443652 scaleN
                  ·
                    apply V_pos_box_before_s1 71229101 71443652
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo15, hcut18⟩
                    · exact hne1
                  ·
                    have hlo19 : q 71443652 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut18)
                    apply V_pos_box_before_s1 71443652 71658203
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo19, hcut12⟩
                    · exact hne1
              ·
                have hlo13 : q 71658203 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut12)
                by_cases hcut20 : y ≤ q 72087304 scaleN
                ·
                  by_cases hcut22 : y ≤ q 71872753 scaleN
                  ·
                    apply V_pos_box_before_s1 71658203 71872753
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo13, hcut22⟩
                    · exact hne1
                  ·
                    have hlo23 : q 71872753 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut22)
                    apply V_pos_box_before_s1 71872753 72087304
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo23, hcut20⟩
                    · exact hne1
                ·
                  have hlo21 : q 72087304 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut20)
                  by_cases hcut24 : y ≤ q 72301855 scaleN
                  ·
                    apply V_pos_box_before_s1 72087304 72301855
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo21, hcut24⟩
                    · exact hne1
                  ·
                    have hlo25 : q 72301855 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut24)
                    by_cases hcut26 : y ≤ q 72516406 scaleN
                    ·
                      apply V_pos_box_before_s1 72301855 72516406
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo25, hcut26⟩
                      · exact hne1
                    ·
                      have hlo27 : q 72516406 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut26)
                      apply V_pos_box_before_s1 72516406 72730956
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo27, hcut10⟩
                      · exact hne1
            ·
              have hlo11 : q 72730956 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut10)
              by_cases hcut28 : y ≤ q 73267333 scaleN
              ·
                by_cases hcut30 : y ≤ q 72945507 scaleN
                ·
                  by_cases hcut32 : y ≤ q 72838231 scaleN
                  ·
                    apply V_pos_box_before_s1 72730956 72838231
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo11, hcut32⟩
                    · exact hne1
                  ·
                    have hlo33 : q 72838231 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut32)
                    apply V_pos_box_before_s1 72838231 72945507
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo33, hcut30⟩
                    · exact hne1
                ·
                  have hlo31 : q 72945507 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut30)
                  by_cases hcut34 : y ≤ q 73052782 scaleN
                  ·
                    apply V_pos_box_before_s1 72945507 73052782
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo31, hcut34⟩
                    · exact hne1
                  ·
                    have hlo35 : q 73052782 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut34)
                    by_cases hcut36 : y ≤ q 73160058 scaleN
                    ·
                      apply V_pos_box_before_s1 73052782 73160058
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo35, hcut36⟩
                      · exact hne1
                    ·
                      have hlo37 : q 73160058 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut36)
                      apply V_pos_box_before_s1 73160058 73267333
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo37, hcut28⟩
                      · exact hne1
              ·
                have hlo29 : q 73267333 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut28)
                by_cases hcut38 : y ≤ q 73481884 scaleN
                ·
                  by_cases hcut40 : y ≤ q 73374609 scaleN
                  ·
                    apply V_pos_box_before_s1 73267333 73374609
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo29, hcut40⟩
                    · exact hne1
                  ·
                    have hlo41 : q 73374609 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut40)
                    apply V_pos_box_before_s1 73374609 73481884
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo41, hcut38⟩
                    · exact hne1
                ·
                  have hlo39 : q 73481884 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut38)
                  by_cases hcut42 : y ≤ q 73589159 scaleN
                  ·
                    apply V_pos_box_before_s1 73481884 73589159
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo39, hcut42⟩
                    · exact hne1
                  ·
                    have hlo43 : q 73589159 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut42)
                    by_cases hcut44 : y ≤ q 73696434 scaleN
                    ·
                      apply V_pos_box_before_s1 73589159 73696434
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo43, hcut44⟩
                      · exact hne1
                    ·
                      have hlo45 : q 73696434 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut44)
                      apply V_pos_box_before_s1 73696434 73803710
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo45, hcut8⟩
                      · exact hne1
          ·
            have hlo9 : q 73803710 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut8)
            by_cases hcut46 : y ≤ q 74393724 scaleN
            ·
              by_cases hcut48 : y ≤ q 74125536 scaleN
              ·
                by_cases hcut50 : y ≤ q 73964623 scaleN
                ·
                  by_cases hcut52 : y ≤ q 73910985 scaleN
                  ·
                    apply V_pos_box_before_s1 73803710 73910985
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo9, hcut52⟩
                    · exact hne1
                  ·
                    have hlo53 : q 73910985 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut52)
                    apply V_pos_box_before_s1 73910985 73964623
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo53, hcut50⟩
                    · exact hne1
                ·
                  have hlo51 : q 73964623 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut50)
                  by_cases hcut54 : y ≤ q 74018261 scaleN
                  ·
                    apply V_pos_box_before_s1 73964623 74018261
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo51, hcut54⟩
                    · exact hne1
                  ·
                    have hlo55 : q 74018261 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut54)
                    by_cases hcut56 : y ≤ q 74071898 scaleN
                    ·
                      apply V_pos_box_before_s1 74018261 74071898
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo55, hcut56⟩
                      · exact hne1
                    ·
                      have hlo57 : q 74071898 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut56)
                      apply V_pos_box_before_s1 74071898 74125536
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo57, hcut48⟩
                      · exact hne1
              ·
                have hlo49 : q 74125536 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut48)
                by_cases hcut58 : y ≤ q 74232812 scaleN
                ·
                  by_cases hcut60 : y ≤ q 74179174 scaleN
                  ·
                    apply V_pos_box_before_s1 74125536 74179174
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo49, hcut60⟩
                    · exact hne1
                  ·
                    have hlo61 : q 74179174 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut60)
                    apply V_pos_box_before_s1 74179174 74232812
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo61, hcut58⟩
                    · exact hne1
                ·
                  have hlo59 : q 74232812 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut58)
                  by_cases hcut62 : y ≤ q 74286449 scaleN
                  ·
                    apply V_pos_box_before_s1 74232812 74286449
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo59, hcut62⟩
                    · exact hne1
                  ·
                    have hlo63 : q 74286449 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut62)
                    by_cases hcut64 : y ≤ q 74340087 scaleN
                    ·
                      apply V_pos_box_before_s1 74286449 74340087
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo63, hcut64⟩
                      · exact hne1
                    ·
                      have hlo65 : q 74340087 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut64)
                      apply V_pos_box_before_s1 74340087 74393724
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo65, hcut46⟩
                      · exact hne1
            ·
              have hlo47 : q 74393724 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut46)
              by_cases hcut66 : y ≤ q 74661913 scaleN
              ·
                by_cases hcut68 : y ≤ q 74500999 scaleN
                ·
                  by_cases hcut70 : y ≤ q 74447362 scaleN
                  ·
                    apply V_pos_box_before_s1 74393724 74447362
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo47, hcut70⟩
                    · exact hne1
                  ·
                    have hlo71 : q 74447362 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut70)
                    apply V_pos_box_before_s1 74447362 74500999
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo71, hcut68⟩
                    · exact hne1
                ·
                  have hlo69 : q 74500999 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut68)
                  by_cases hcut72 : y ≤ q 74554637 scaleN
                  ·
                    apply V_pos_box_before_s1 74500999 74554637
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo69, hcut72⟩
                    · exact hne1
                  ·
                    have hlo73 : q 74554637 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut72)
                    by_cases hcut74 : y ≤ q 74608275 scaleN
                    ·
                      apply V_pos_box_before_s1 74554637 74608275
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo73, hcut74⟩
                      · exact hne1
                    ·
                      have hlo75 : q 74608275 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut74)
                      apply V_pos_box_before_s1 74608275 74661913
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo75, hcut66⟩
                      · exact hne1
              ·
                have hlo67 : q 74661913 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut66)
                by_cases hcut76 : y ≤ q 74769188 scaleN
                ·
                  by_cases hcut78 : y ≤ q 74715550 scaleN
                  ·
                    apply V_pos_box_before_s1 74661913 74715550
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo67, hcut78⟩
                    · exact hne1
                  ·
                    have hlo79 : q 74715550 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut78)
                    apply V_pos_box_before_s1 74715550 74769188
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo79, hcut76⟩
                    · exact hne1
                ·
                  have hlo77 : q 74769188 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut76)
                  by_cases hcut80 : y ≤ q 74822826 scaleN
                  ·
                    apply V_pos_box_before_s1 74769188 74822826
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo77, hcut80⟩
                    · exact hne1
                  ·
                    have hlo81 : q 74822826 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut80)
                    by_cases hcut82 : y ≤ q 74876464 scaleN
                    ·
                      apply V_pos_box_before_s1 74822826 74876464
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo81, hcut82⟩
                      · exact hne1
                    ·
                      have hlo83 : q 74876464 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut82)
                      apply V_pos_box_before_s1 74876464 74903282
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo83, hcut6⟩
                      · exact hne1
        ·
          have hlo7 : q 74903282 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut6)
          by_cases hcut84 : y ≤ q 75412840 scaleN
          ·
            by_cases hcut86 : y ≤ q 75144652 scaleN
            ·
              by_cases hcut88 : y ≤ q 75010558 scaleN
              ·
                by_cases hcut90 : y ≤ q 74956920 scaleN
                ·
                  by_cases hcut92 : y ≤ q 74930101 scaleN
                  ·
                    apply V_pos_box_before_s1 74903282 74930101
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo7, hcut92⟩
                    · exact hne1
                  ·
                    have hlo93 : q 74930101 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut92)
                    apply V_pos_box_before_s1 74930101 74956920
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo93, hcut90⟩
                    · exact hne1
                ·
                  have hlo91 : q 74956920 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut90)
                  by_cases hcut94 : y ≤ q 74983739 scaleN
                  ·
                    apply V_pos_box_before_s1 74956920 74983739
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo91, hcut94⟩
                    · exact hne1
                  ·
                    have hlo95 : q 74983739 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut94)
                    apply V_pos_box_before_s1 74983739 75010558
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo95, hcut88⟩
                    · exact hne1
              ·
                have hlo89 : q 75010558 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut88)
                by_cases hcut96 : y ≤ q 75064196 scaleN
                ·
                  by_cases hcut98 : y ≤ q 75037377 scaleN
                  ·
                    apply V_pos_box_before_s1 75010558 75037377
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo89, hcut98⟩
                    · exact hne1
                  ·
                    have hlo99 : q 75037377 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut98)
                    apply V_pos_box_before_s1 75037377 75064196
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo99, hcut96⟩
                    · exact hne1
                ·
                  have hlo97 : q 75064196 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut96)
                  by_cases hcut100 : y ≤ q 75091015 scaleN
                  ·
                    apply V_pos_box_before_s1 75064196 75091015
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo97, hcut100⟩
                    · exact hne1
                  ·
                    have hlo101 : q 75091015 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut100)
                    by_cases hcut102 : y ≤ q 75117833 scaleN
                    ·
                      apply V_pos_box_before_s1 75091015 75117833
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo101, hcut102⟩
                      · exact hne1
                    ·
                      have hlo103 : q 75117833 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut102)
                      apply V_pos_box_before_s1 75117833 75144652
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo103, hcut86⟩
                      · exact hne1
            ·
              have hlo87 : q 75144652 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut86)
              by_cases hcut104 : y ≤ q 75278746 scaleN
              ·
                by_cases hcut106 : y ≤ q 75198290 scaleN
                ·
                  by_cases hcut108 : y ≤ q 75171471 scaleN
                  ·
                    apply V_pos_box_before_s1 75144652 75171471
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo87, hcut108⟩
                    · exact hne1
                  ·
                    have hlo109 : q 75171471 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut108)
                    apply V_pos_box_before_s1 75171471 75198290
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo109, hcut106⟩
                    · exact hne1
                ·
                  have hlo107 : q 75198290 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut106)
                  by_cases hcut110 : y ≤ q 75225108 scaleN
                  ·
                    apply V_pos_box_before_s1 75198290 75225108
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo107, hcut110⟩
                    · exact hne1
                  ·
                    have hlo111 : q 75225108 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut110)
                    by_cases hcut112 : y ≤ q 75251927 scaleN
                    ·
                      apply V_pos_box_before_s1 75225108 75251927
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo111, hcut112⟩
                      · exact hne1
                    ·
                      have hlo113 : q 75251927 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut112)
                      apply V_pos_box_before_s1 75251927 75278746
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo113, hcut104⟩
                      · exact hne1
              ·
                have hlo105 : q 75278746 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut104)
                by_cases hcut114 : y ≤ q 75332383 scaleN
                ·
                  by_cases hcut116 : y ≤ q 75305565 scaleN
                  ·
                    apply V_pos_box_before_s1 75278746 75305565
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo105, hcut116⟩
                    · exact hne1
                  ·
                    have hlo117 : q 75305565 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut116)
                    apply V_pos_box_before_s1 75305565 75332383
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo117, hcut114⟩
                    · exact hne1
                ·
                  have hlo115 : q 75332383 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut114)
                  by_cases hcut118 : y ≤ q 75359202 scaleN
                  ·
                    apply V_pos_box_before_s1 75332383 75359202
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo115, hcut118⟩
                    · exact hne1
                  ·
                    have hlo119 : q 75359202 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut118)
                    by_cases hcut120 : y ≤ q 75386021 scaleN
                    ·
                      apply V_pos_box_before_s1 75359202 75386021
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo119, hcut120⟩
                      · exact hne1
                    ·
                      have hlo121 : q 75386021 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut120)
                      apply V_pos_box_before_s1 75386021 75412840
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo121, hcut84⟩
                      · exact hne1
          ·
            have hlo85 : q 75412840 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut84)
            by_cases hcut122 : y ≤ q 75627391 scaleN
            ·
              by_cases hcut124 : y ≤ q 75546934 scaleN
              ·
                by_cases hcut126 : y ≤ q 75466478 scaleN
                ·
                  by_cases hcut128 : y ≤ q 75439659 scaleN
                  ·
                    apply V_pos_box_before_s1 75412840 75439659
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo85, hcut128⟩
                    · exact hne1
                  ·
                    have hlo129 : q 75439659 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut128)
                    apply V_pos_box_before_s1 75439659 75466478
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo129, hcut126⟩
                    · exact hne1
                ·
                  have hlo127 : q 75466478 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut126)
                  by_cases hcut130 : y ≤ q 75493297 scaleN
                  ·
                    apply V_pos_box_before_s1 75466478 75493297
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo127, hcut130⟩
                    · exact hne1
                  ·
                    have hlo131 : q 75493297 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut130)
                    by_cases hcut132 : y ≤ q 75520116 scaleN
                    ·
                      apply V_pos_box_before_s1 75493297 75520116
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo131, hcut132⟩
                      · exact hne1
                    ·
                      have hlo133 : q 75520116 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut132)
                      apply V_pos_box_before_s1 75520116 75546934
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo133, hcut124⟩
                      · exact hne1
              ·
                have hlo125 : q 75546934 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut124)
                by_cases hcut134 : y ≤ q 75587162 scaleN
                ·
                  by_cases hcut136 : y ≤ q 75573753 scaleN
                  ·
                    apply V_pos_box_before_s1 75546934 75573753
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo125, hcut136⟩
                    · exact hne1
                  ·
                    have hlo137 : q 75573753 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut136)
                    apply V_pos_box_before_s1 75573753 75587162
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo137, hcut134⟩
                    · exact hne1
                ·
                  have hlo135 : q 75587162 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut134)
                  by_cases hcut138 : y ≤ q 75600572 scaleN
                  ·
                    apply V_pos_box_before_s1 75587162 75600572
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo135, hcut138⟩
                    · exact hne1
                  ·
                    have hlo139 : q 75600572 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut138)
                    by_cases hcut140 : y ≤ q 75613981 scaleN
                    ·
                      apply V_pos_box_before_s1 75600572 75613981
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo139, hcut140⟩
                      · exact hne1
                    ·
                      have hlo141 : q 75613981 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut140)
                      apply V_pos_box_before_s1 75613981 75627391
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo141, hcut122⟩
                      · exact hne1
            ·
              have hlo123 : q 75627391 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut122)
              by_cases hcut142 : y ≤ q 75694438 scaleN
              ·
                by_cases hcut144 : y ≤ q 75654210 scaleN
                ·
                  by_cases hcut146 : y ≤ q 75640800 scaleN
                  ·
                    apply V_pos_box_before_s1 75627391 75640800
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo123, hcut146⟩
                    · exact hne1
                  ·
                    have hlo147 : q 75640800 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut146)
                    apply V_pos_box_before_s1 75640800 75654210
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo147, hcut144⟩
                    · exact hne1
                ·
                  have hlo145 : q 75654210 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut144)
                  by_cases hcut148 : y ≤ q 75667619 scaleN
                  ·
                    apply V_pos_box_before_s1 75654210 75667619
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo145, hcut148⟩
                    · exact hne1
                  ·
                    have hlo149 : q 75667619 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut148)
                    by_cases hcut150 : y ≤ q 75681029 scaleN
                    ·
                      apply V_pos_box_before_s1 75667619 75681029
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo149, hcut150⟩
                      · exact hne1
                    ·
                      have hlo151 : q 75681029 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut150)
                      apply V_pos_box_before_s1 75681029 75694438
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo151, hcut142⟩
                      · exact hne1
              ·
                have hlo143 : q 75694438 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut142)
                by_cases hcut152 : y ≤ q 75721257 scaleN
                ·
                  by_cases hcut154 : y ≤ q 75707848 scaleN
                  ·
                    apply V_pos_box_before_s1 75694438 75707848
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo143, hcut154⟩
                    · exact hne1
                  ·
                    have hlo155 : q 75707848 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut154)
                    apply V_pos_box_before_s1 75707848 75721257
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo155, hcut152⟩
                    · exact hne1
                ·
                  have hlo153 : q 75721257 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut152)
                  by_cases hcut156 : y ≤ q 75734667 scaleN
                  ·
                    apply V_pos_box_before_s1 75721257 75734667
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo153, hcut156⟩
                    · exact hne1
                  ·
                    have hlo157 : q 75734667 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut156)
                    by_cases hcut158 : y ≤ q 75748076 scaleN
                    ·
                      apply V_pos_box_before_s1 75734667 75748076
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo157, hcut158⟩
                      · exact hne1
                    ·
                      have hlo159 : q 75748076 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut158)
                      apply V_pos_box_before_s1 75748076 75761485
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo159, hcut4⟩
                      · exact hne1
      ·
        have hlo5 : q 75761485 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut4)
        by_cases hcut160 : y ≤ q 76197290 scaleN
        ·
          by_cases hcut162 : y ≤ q 76016264 scaleN
          ·
            by_cases hcut164 : y ≤ q 75882170 scaleN
            ·
              by_cases hcut166 : y ≤ q 75815123 scaleN
              ·
                by_cases hcut168 : y ≤ q 75788304 scaleN
                ·
                  by_cases hcut170 : y ≤ q 75774894 scaleN
                  ·
                    apply V_pos_box_before_s1 75761485 75774894
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo5, hcut170⟩
                    · exact hne1
                  ·
                    have hlo171 : q 75774894 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut170)
                    apply V_pos_box_before_s1 75774894 75788304
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo171, hcut168⟩
                    · exact hne1
                ·
                  have hlo169 : q 75788304 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut168)
                  by_cases hcut172 : y ≤ q 75801713 scaleN
                  ·
                    apply V_pos_box_before_s1 75788304 75801713
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo169, hcut172⟩
                    · exact hne1
                  ·
                    have hlo173 : q 75801713 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut172)
                    apply V_pos_box_before_s1 75801713 75815123
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo173, hcut166⟩
                    · exact hne1
              ·
                have hlo167 : q 75815123 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut166)
                by_cases hcut174 : y ≤ q 75841942 scaleN
                ·
                  by_cases hcut176 : y ≤ q 75828532 scaleN
                  ·
                    apply V_pos_box_before_s1 75815123 75828532
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo167, hcut176⟩
                    · exact hne1
                  ·
                    have hlo177 : q 75828532 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut176)
                    apply V_pos_box_before_s1 75828532 75841942
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo177, hcut174⟩
                    · exact hne1
                ·
                  have hlo175 : q 75841942 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut174)
                  by_cases hcut178 : y ≤ q 75855351 scaleN
                  ·
                    apply V_pos_box_before_s1 75841942 75855351
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo175, hcut178⟩
                    · exact hne1
                  ·
                    have hlo179 : q 75855351 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut178)
                    by_cases hcut180 : y ≤ q 75868761 scaleN
                    ·
                      apply V_pos_box_before_s1 75855351 75868761
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo179, hcut180⟩
                      · exact hne1
                    ·
                      have hlo181 : q 75868761 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut180)
                      apply V_pos_box_before_s1 75868761 75882170
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo181, hcut164⟩
                      · exact hne1
            ·
              have hlo165 : q 75882170 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut164)
              by_cases hcut182 : y ≤ q 75949218 scaleN
              ·
                by_cases hcut184 : y ≤ q 75908989 scaleN
                ·
                  by_cases hcut186 : y ≤ q 75895580 scaleN
                  ·
                    apply V_pos_box_before_s1 75882170 75895580
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo165, hcut186⟩
                    · exact hne1
                  ·
                    have hlo187 : q 75895580 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut186)
                    apply V_pos_box_before_s1 75895580 75908989
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo187, hcut184⟩
                    · exact hne1
                ·
                  have hlo185 : q 75908989 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut184)
                  by_cases hcut188 : y ≤ q 75922399 scaleN
                  ·
                    apply V_pos_box_before_s1 75908989 75922399
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo185, hcut188⟩
                    · exact hne1
                  ·
                    have hlo189 : q 75922399 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut188)
                    by_cases hcut190 : y ≤ q 75935808 scaleN
                    ·
                      apply V_pos_box_before_s1 75922399 75935808
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo189, hcut190⟩
                      · exact hne1
                    ·
                      have hlo191 : q 75935808 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut190)
                      apply V_pos_box_before_s1 75935808 75949218
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo191, hcut182⟩
                      · exact hne1
              ·
                have hlo183 : q 75949218 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut182)
                by_cases hcut192 : y ≤ q 75976036 scaleN
                ·
                  by_cases hcut194 : y ≤ q 75962627 scaleN
                  ·
                    apply V_pos_box_before_s1 75949218 75962627
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo183, hcut194⟩
                    · exact hne1
                  ·
                    have hlo195 : q 75962627 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut194)
                    apply V_pos_box_before_s1 75962627 75976036
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo195, hcut192⟩
                    · exact hne1
                ·
                  have hlo193 : q 75976036 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut192)
                  by_cases hcut196 : y ≤ q 75989445 scaleN
                  ·
                    apply V_pos_box_before_s1 75976036 75989445
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo193, hcut196⟩
                    · exact hne1
                  ·
                    have hlo197 : q 75989445 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut196)
                    by_cases hcut198 : y ≤ q 76002855 scaleN
                    ·
                      apply V_pos_box_before_s1 75989445 76002855
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo197, hcut198⟩
                      · exact hne1
                    ·
                      have hlo199 : q 76002855 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut198)
                      apply V_pos_box_before_s1 76002855 76016264
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo199, hcut162⟩
                      · exact hne1
          ·
            have hlo163 : q 76016264 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut162)
            by_cases hcut200 : y ≤ q 76130244 scaleN
            ·
              by_cases hcut202 : y ≤ q 76083311 scaleN
              ·
                by_cases hcut204 : y ≤ q 76043083 scaleN
                ·
                  by_cases hcut206 : y ≤ q 76029674 scaleN
                  ·
                    apply V_pos_box_before_s1 76016264 76029674
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo163, hcut206⟩
                    · exact hne1
                  ·
                    have hlo207 : q 76029674 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut206)
                    apply V_pos_box_before_s1 76029674 76043083
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo207, hcut204⟩
                    · exact hne1
                ·
                  have hlo205 : q 76043083 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut204)
                  by_cases hcut208 : y ≤ q 76056493 scaleN
                  ·
                    apply V_pos_box_before_s1 76043083 76056493
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo205, hcut208⟩
                    · exact hne1
                  ·
                    have hlo209 : q 76056493 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut208)
                    by_cases hcut210 : y ≤ q 76069902 scaleN
                    ·
                      apply V_pos_box_before_s1 76056493 76069902
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo209, hcut210⟩
                      · exact hne1
                    ·
                      have hlo211 : q 76069902 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut210)
                      apply V_pos_box_before_s1 76069902 76083311
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo211, hcut202⟩
                      · exact hne1
              ·
                have hlo203 : q 76083311 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut202)
                by_cases hcut212 : y ≤ q 76110130 scaleN
                ·
                  by_cases hcut214 : y ≤ q 76096720 scaleN
                  ·
                    apply V_pos_box_before_s1 76083311 76096720
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo203, hcut214⟩
                    · exact hne1
                  ·
                    have hlo215 : q 76096720 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut214)
                    apply V_pos_box_before_s1 76096720 76110130
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo215, hcut212⟩
                    · exact hne1
                ·
                  have hlo213 : q 76110130 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut212)
                  by_cases hcut216 : y ≤ q 76116834 scaleN
                  ·
                    apply V_pos_box_before_s1 76110130 76116834
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo213, hcut216⟩
                    · exact hne1
                  ·
                    have hlo217 : q 76116834 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut216)
                    by_cases hcut218 : y ≤ q 76123539 scaleN
                    ·
                      apply V_pos_box_before_s1 76116834 76123539
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo217, hcut218⟩
                      · exact hne1
                    ·
                      have hlo219 : q 76123539 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut218)
                      apply V_pos_box_before_s1 76123539 76130244
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo219, hcut200⟩
                      · exact hne1
            ·
              have hlo201 : q 76130244 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut200)
              by_cases hcut220 : y ≤ q 76163768 scaleN
              ·
                by_cases hcut222 : y ≤ q 76143653 scaleN
                ·
                  by_cases hcut224 : y ≤ q 76136949 scaleN
                  ·
                    apply V_pos_box_before_s1 76130244 76136949
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo201, hcut224⟩
                    · exact hne1
                  ·
                    have hlo225 : q 76136949 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut224)
                    apply V_pos_box_before_s1 76136949 76143653
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo225, hcut222⟩
                    · exact hne1
                ·
                  have hlo223 : q 76143653 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut222)
                  by_cases hcut226 : y ≤ q 76150358 scaleN
                  ·
                    apply V_pos_box_before_s1 76143653 76150358
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo223, hcut226⟩
                    · exact hne1
                  ·
                    have hlo227 : q 76150358 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut226)
                    by_cases hcut228 : y ≤ q 76157063 scaleN
                    ·
                      apply V_pos_box_before_s1 76150358 76157063
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo227, hcut228⟩
                      · exact hne1
                    ·
                      have hlo229 : q 76157063 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut228)
                      apply V_pos_box_before_s1 76157063 76163768
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo229, hcut220⟩
                      · exact hne1
              ·
                have hlo221 : q 76163768 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut220)
                by_cases hcut230 : y ≤ q 76177177 scaleN
                ·
                  by_cases hcut232 : y ≤ q 76170472 scaleN
                  ·
                    apply V_pos_box_before_s1 76163768 76170472
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo221, hcut232⟩
                    · exact hne1
                  ·
                    have hlo233 : q 76170472 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut232)
                    apply V_pos_box_before_s1 76170472 76177177
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo233, hcut230⟩
                    · exact hne1
                ·
                  have hlo231 : q 76177177 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut230)
                  by_cases hcut234 : y ≤ q 76183881 scaleN
                  ·
                    apply V_pos_box_before_s1 76177177 76183881
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo231, hcut234⟩
                    · exact hne1
                  ·
                    have hlo235 : q 76183881 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut234)
                    by_cases hcut236 : y ≤ q 76190586 scaleN
                    ·
                      apply V_pos_box_before_s1 76183881 76190586
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo235, hcut236⟩
                      · exact hne1
                    ·
                      have hlo237 : q 76190586 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut236)
                      apply V_pos_box_before_s1 76190586 76197290
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo237, hcut160⟩
                      · exact hne1
        ·
          have hlo161 : q 76197290 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut160)
          by_cases hcut238 : y ≤ q 76324681 scaleN
          ·
            by_cases hcut240 : y ≤ q 76257633 scaleN
            ·
              by_cases hcut242 : y ≤ q 76224109 scaleN
              ·
                by_cases hcut244 : y ≤ q 76210700 scaleN
                ·
                  by_cases hcut246 : y ≤ q 76203995 scaleN
                  ·
                    apply V_pos_box_before_s1 76197290 76203995
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo161, hcut246⟩
                    · exact hne1
                  ·
                    have hlo247 : q 76203995 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut246)
                    apply V_pos_box_before_s1 76203995 76210700
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo247, hcut244⟩
                    · exact hne1
                ·
                  have hlo245 : q 76210700 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut244)
                  by_cases hcut248 : y ≤ q 76217405 scaleN
                  ·
                    apply V_pos_box_before_s1 76210700 76217405
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo245, hcut248⟩
                    · exact hne1
                  ·
                    have hlo249 : q 76217405 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut248)
                    apply V_pos_box_before_s1 76217405 76224109
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo249, hcut242⟩
                    · exact hne1
              ·
                have hlo243 : q 76224109 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut242)
                by_cases hcut250 : y ≤ q 76237519 scaleN
                ·
                  by_cases hcut252 : y ≤ q 76230814 scaleN
                  ·
                    apply V_pos_box_before_s1 76224109 76230814
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo243, hcut252⟩
                    · exact hne1
                  ·
                    have hlo253 : q 76230814 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut252)
                    apply V_pos_box_before_s1 76230814 76237519
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo253, hcut250⟩
                    · exact hne1
                ·
                  have hlo251 : q 76237519 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut250)
                  by_cases hcut254 : y ≤ q 76244224 scaleN
                  ·
                    apply V_pos_box_before_s1 76237519 76244224
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo251, hcut254⟩
                    · exact hne1
                  ·
                    have hlo255 : q 76244224 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut254)
                    by_cases hcut256 : y ≤ q 76250928 scaleN
                    ·
                      apply V_pos_box_before_s1 76244224 76250928
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo255, hcut256⟩
                      · exact hne1
                    ·
                      have hlo257 : q 76250928 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut256)
                      apply V_pos_box_before_s1 76250928 76257633
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo257, hcut240⟩
                      · exact hne1
            ·
              have hlo241 : q 76257633 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut240)
              by_cases hcut258 : y ≤ q 76291157 scaleN
              ·
                by_cases hcut260 : y ≤ q 76271043 scaleN
                ·
                  by_cases hcut262 : y ≤ q 76264338 scaleN
                  ·
                    apply V_pos_box_before_s1 76257633 76264338
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo241, hcut262⟩
                    · exact hne1
                  ·
                    have hlo263 : q 76264338 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut262)
                    apply V_pos_box_before_s1 76264338 76271043
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo263, hcut260⟩
                    · exact hne1
                ·
                  have hlo261 : q 76271043 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut260)
                  by_cases hcut264 : y ≤ q 76277747 scaleN
                  ·
                    apply V_pos_box_before_s1 76271043 76277747
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo261, hcut264⟩
                    · exact hne1
                  ·
                    have hlo265 : q 76277747 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut264)
                    by_cases hcut266 : y ≤ q 76284452 scaleN
                    ·
                      apply V_pos_box_before_s1 76277747 76284452
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo265, hcut266⟩
                      · exact hne1
                    ·
                      have hlo267 : q 76284452 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut266)
                      apply V_pos_box_before_s1 76284452 76291157
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo267, hcut258⟩
                      · exact hne1
              ·
                have hlo259 : q 76291157 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut258)
                by_cases hcut268 : y ≤ q 76304566 scaleN
                ·
                  by_cases hcut270 : y ≤ q 76297862 scaleN
                  ·
                    apply V_pos_box_before_s1 76291157 76297862
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo259, hcut270⟩
                    · exact hne1
                  ·
                    have hlo271 : q 76297862 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut270)
                    apply V_pos_box_before_s1 76297862 76304566
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo271, hcut268⟩
                    · exact hne1
                ·
                  have hlo269 : q 76304566 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut268)
                  by_cases hcut272 : y ≤ q 76311271 scaleN
                  ·
                    apply V_pos_box_before_s1 76304566 76311271
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo269, hcut272⟩
                    · exact hne1
                  ·
                    have hlo273 : q 76311271 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut272)
                    by_cases hcut274 : y ≤ q 76317976 scaleN
                    ·
                      apply V_pos_box_before_s1 76311271 76317976
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo273, hcut274⟩
                      · exact hne1
                    ·
                      have hlo275 : q 76317976 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut274)
                      apply V_pos_box_before_s1 76317976 76324681
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo275, hcut238⟩
                      · exact hne1
          ·
            have hlo239 : q 76324681 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut238)
            by_cases hcut276 : y ≤ q 76391728 scaleN
            ·
              by_cases hcut278 : y ≤ q 76358204 scaleN
              ·
                by_cases hcut280 : y ≤ q 76338090 scaleN
                ·
                  by_cases hcut282 : y ≤ q 76331385 scaleN
                  ·
                    apply V_pos_box_before_s1 76324681 76331385
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo239, hcut282⟩
                    · exact hne1
                  ·
                    have hlo283 : q 76331385 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut282)
                    apply V_pos_box_before_s1 76331385 76338090
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo283, hcut280⟩
                    · exact hne1
                ·
                  have hlo281 : q 76338090 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut280)
                  by_cases hcut284 : y ≤ q 76344795 scaleN
                  ·
                    apply V_pos_box_before_s1 76338090 76344795
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo281, hcut284⟩
                    · exact hne1
                  ·
                    have hlo285 : q 76344795 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut284)
                    by_cases hcut286 : y ≤ q 76351500 scaleN
                    ·
                      apply V_pos_box_before_s1 76344795 76351500
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo285, hcut286⟩
                      · exact hne1
                    ·
                      have hlo287 : q 76351500 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut286)
                      apply V_pos_box_before_s1 76351500 76358204
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo287, hcut278⟩
                      · exact hne1
              ·
                have hlo279 : q 76358204 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut278)
                by_cases hcut288 : y ≤ q 76371614 scaleN
                ·
                  by_cases hcut290 : y ≤ q 76364909 scaleN
                  ·
                    apply V_pos_box_before_s1 76358204 76364909
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo279, hcut290⟩
                    · exact hne1
                  ·
                    have hlo291 : q 76364909 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut290)
                    apply V_pos_box_before_s1 76364909 76371614
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo291, hcut288⟩
                    · exact hne1
                ·
                  have hlo289 : q 76371614 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut288)
                  by_cases hcut292 : y ≤ q 76378319 scaleN
                  ·
                    apply V_pos_box_before_s1 76371614 76378319
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo289, hcut292⟩
                    · exact hne1
                  ·
                    have hlo293 : q 76378319 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut292)
                    by_cases hcut294 : y ≤ q 76385023 scaleN
                    ·
                      apply V_pos_box_before_s1 76378319 76385023
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo293, hcut294⟩
                      · exact hne1
                    ·
                      have hlo295 : q 76385023 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut294)
                      apply V_pos_box_before_s1 76385023 76391728
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo295, hcut276⟩
                      · exact hne1
            ·
              have hlo277 : q 76391728 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut276)
              by_cases hcut296 : y ≤ q 76425251 scaleN
              ·
                by_cases hcut298 : y ≤ q 76405137 scaleN
                ·
                  by_cases hcut300 : y ≤ q 76398432 scaleN
                  ·
                    apply V_pos_box_before_s1 76391728 76398432
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo277, hcut300⟩
                    · exact hne1
                  ·
                    have hlo301 : q 76398432 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut300)
                    apply V_pos_box_before_s1 76398432 76405137
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo301, hcut298⟩
                    · exact hne1
                ·
                  have hlo299 : q 76405137 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut298)
                  by_cases hcut302 : y ≤ q 76411841 scaleN
                  ·
                    apply V_pos_box_before_s1 76405137 76411841
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo299, hcut302⟩
                    · exact hne1
                  ·
                    have hlo303 : q 76411841 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut302)
                    by_cases hcut304 : y ≤ q 76418546 scaleN
                    ·
                      apply V_pos_box_before_s1 76411841 76418546
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo303, hcut304⟩
                      · exact hne1
                    ·
                      have hlo305 : q 76418546 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut304)
                      apply V_pos_box_before_s1 76418546 76425251
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo305, hcut296⟩
                      · exact hne1
              ·
                have hlo297 : q 76425251 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut296)
                by_cases hcut306 : y ≤ q 76438660 scaleN
                ·
                  by_cases hcut308 : y ≤ q 76431956 scaleN
                  ·
                    apply V_pos_box_before_s1 76425251 76431956
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo297, hcut308⟩
                    · exact hne1
                  ·
                    have hlo309 : q 76431956 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut308)
                    apply V_pos_box_before_s1 76431956 76438660
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo309, hcut306⟩
                    · exact hne1
                ·
                  have hlo307 : q 76438660 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut306)
                  by_cases hcut310 : y ≤ q 76445365 scaleN
                  ·
                    apply V_pos_box_before_s1 76438660 76445365
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo307, hcut310⟩
                    · exact hne1
                  ·
                    have hlo311 : q 76445365 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut310)
                    by_cases hcut312 : y ≤ q 76452070 scaleN
                    ·
                      apply V_pos_box_before_s1 76445365 76452070
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo311, hcut312⟩
                      · exact hne1
                    ·
                      have hlo313 : q 76452070 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut312)
                      apply V_pos_box_before_s1 76452070 76458775
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo313, hcut2⟩
                      · exact hne1
    ·
      have hlo3 : q 76458775 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2)
      by_cases hcut314 : y ≤ q 76770544 scaleN
      ·
        by_cases hcut316 : y ≤ q 76639802 scaleN
        ·
          by_cases hcut318 : y ≤ q 76572755 scaleN
          ·
            by_cases hcut320 : y ≤ q 76519117 scaleN
            ·
              by_cases hcut322 : y ≤ q 76485594 scaleN
              ·
                by_cases hcut324 : y ≤ q 76472184 scaleN
                ·
                  by_cases hcut326 : y ≤ q 76465479 scaleN
                  ·
                    apply V_pos_box_before_s1 76458775 76465479
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo3, hcut326⟩
                    · exact hne1
                  ·
                    have hlo327 : q 76465479 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut326)
                    apply V_pos_box_before_s1 76465479 76472184
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo327, hcut324⟩
                    · exact hne1
                ·
                  have hlo325 : q 76472184 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut324)
                  by_cases hcut328 : y ≤ q 76478889 scaleN
                  ·
                    apply V_pos_box_before_s1 76472184 76478889
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo325, hcut328⟩
                    · exact hne1
                  ·
                    have hlo329 : q 76478889 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut328)
                    apply V_pos_box_before_s1 76478889 76485594
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo329, hcut322⟩
                    · exact hne1
              ·
                have hlo323 : q 76485594 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut322)
                by_cases hcut330 : y ≤ q 76499003 scaleN
                ·
                  by_cases hcut332 : y ≤ q 76492298 scaleN
                  ·
                    apply V_pos_box_before_s1 76485594 76492298
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo323, hcut332⟩
                    · exact hne1
                  ·
                    have hlo333 : q 76492298 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut332)
                    apply V_pos_box_before_s1 76492298 76499003
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo333, hcut330⟩
                    · exact hne1
                ·
                  have hlo331 : q 76499003 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut330)
                  by_cases hcut334 : y ≤ q 76505708 scaleN
                  ·
                    apply V_pos_box_before_s1 76499003 76505708
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo331, hcut334⟩
                    · exact hne1
                  ·
                    have hlo335 : q 76505708 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut334)
                    by_cases hcut336 : y ≤ q 76512413 scaleN
                    ·
                      apply V_pos_box_before_s1 76505708 76512413
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo335, hcut336⟩
                      · exact hne1
                    ·
                      have hlo337 : q 76512413 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut336)
                      apply V_pos_box_before_s1 76512413 76519117
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo337, hcut320⟩
                      · exact hne1
            ·
              have hlo321 : q 76519117 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut320)
              by_cases hcut338 : y ≤ q 76552641 scaleN
              ·
                by_cases hcut340 : y ≤ q 76532527 scaleN
                ·
                  by_cases hcut342 : y ≤ q 76525822 scaleN
                  ·
                    apply V_pos_box_before_s1 76519117 76525822
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo321, hcut342⟩
                    · exact hne1
                  ·
                    have hlo343 : q 76525822 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut342)
                    apply V_pos_box_before_s1 76525822 76532527
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo343, hcut340⟩
                    · exact hne1
                ·
                  have hlo341 : q 76532527 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut340)
                  by_cases hcut344 : y ≤ q 76539232 scaleN
                  ·
                    apply V_pos_box_before_s1 76532527 76539232
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo341, hcut344⟩
                    · exact hne1
                  ·
                    have hlo345 : q 76539232 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut344)
                    by_cases hcut346 : y ≤ q 76545936 scaleN
                    ·
                      apply V_pos_box_before_s1 76539232 76545936
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo345, hcut346⟩
                      · exact hne1
                    ·
                      have hlo347 : q 76545936 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut346)
                      apply V_pos_box_before_s1 76545936 76552641
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo347, hcut338⟩
                      · exact hne1
              ·
                have hlo339 : q 76552641 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut338)
                by_cases hcut348 : y ≤ q 76562698 scaleN
                ·
                  by_cases hcut350 : y ≤ q 76559346 scaleN
                  ·
                    apply V_pos_box_before_s1 76552641 76559346
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo339, hcut350⟩
                    · exact hne1
                  ·
                    have hlo351 : q 76559346 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut350)
                    apply V_pos_box_before_s1 76559346 76562698
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo351, hcut348⟩
                    · exact hne1
                ·
                  have hlo349 : q 76562698 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut348)
                  by_cases hcut352 : y ≤ q 76566051 scaleN
                  ·
                    apply V_pos_box_before_s1 76562698 76566051
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo349, hcut352⟩
                    · exact hne1
                  ·
                    have hlo353 : q 76566051 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut352)
                    by_cases hcut354 : y ≤ q 76569403 scaleN
                    ·
                      apply V_pos_box_before_s1 76566051 76569403
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo353, hcut354⟩
                      · exact hne1
                    ·
                      have hlo355 : q 76569403 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut354)
                      apply V_pos_box_before_s1 76569403 76572755
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo355, hcut318⟩
                      · exact hne1
          ·
            have hlo319 : q 76572755 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut318)
            by_cases hcut356 : y ≤ q 76606279 scaleN
            ·
              by_cases hcut358 : y ≤ q 76589517 scaleN
              ·
                by_cases hcut360 : y ≤ q 76579460 scaleN
                ·
                  by_cases hcut362 : y ≤ q 76576107 scaleN
                  ·
                    apply V_pos_box_before_s1 76572755 76576107
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo319, hcut362⟩
                    · exact hne1
                  ·
                    have hlo363 : q 76576107 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut362)
                    apply V_pos_box_before_s1 76576107 76579460
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo363, hcut360⟩
                    · exact hne1
                ·
                  have hlo361 : q 76579460 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut360)
                  by_cases hcut364 : y ≤ q 76582812 scaleN
                  ·
                    apply V_pos_box_before_s1 76579460 76582812
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo361, hcut364⟩
                    · exact hne1
                  ·
                    have hlo365 : q 76582812 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut364)
                    by_cases hcut366 : y ≤ q 76586165 scaleN
                    ·
                      apply V_pos_box_before_s1 76582812 76586165
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo365, hcut366⟩
                      · exact hne1
                    ·
                      have hlo367 : q 76586165 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut366)
                      apply V_pos_box_before_s1 76586165 76589517
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo367, hcut358⟩
                      · exact hne1
              ·
                have hlo359 : q 76589517 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut358)
                by_cases hcut368 : y ≤ q 76596222 scaleN
                ·
                  by_cases hcut370 : y ≤ q 76592870 scaleN
                  ·
                    apply V_pos_box_before_s1 76589517 76592870
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo359, hcut370⟩
                    · exact hne1
                  ·
                    have hlo371 : q 76592870 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut370)
                    apply V_pos_box_before_s1 76592870 76596222
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo371, hcut368⟩
                    · exact hne1
                ·
                  have hlo369 : q 76596222 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut368)
                  by_cases hcut372 : y ≤ q 76599574 scaleN
                  ·
                    apply V_pos_box_before_s1 76596222 76599574
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo369, hcut372⟩
                    · exact hne1
                  ·
                    have hlo373 : q 76599574 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut372)
                    by_cases hcut374 : y ≤ q 76602926 scaleN
                    ·
                      apply V_pos_box_before_s1 76599574 76602926
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo373, hcut374⟩
                      · exact hne1
                    ·
                      have hlo375 : q 76602926 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut374)
                      apply V_pos_box_before_s1 76602926 76606279
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo375, hcut356⟩
                      · exact hne1
            ·
              have hlo357 : q 76606279 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut356)
              by_cases hcut376 : y ≤ q 76623040 scaleN
              ·
                by_cases hcut378 : y ≤ q 76612983 scaleN
                ·
                  by_cases hcut380 : y ≤ q 76609631 scaleN
                  ·
                    apply V_pos_box_before_s1 76606279 76609631
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo357, hcut380⟩
                    · exact hne1
                  ·
                    have hlo381 : q 76609631 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut380)
                    apply V_pos_box_before_s1 76609631 76612983
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo381, hcut378⟩
                    · exact hne1
                ·
                  have hlo379 : q 76612983 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut378)
                  by_cases hcut382 : y ≤ q 76616335 scaleN
                  ·
                    apply V_pos_box_before_s1 76612983 76616335
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo379, hcut382⟩
                    · exact hne1
                  ·
                    have hlo383 : q 76616335 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut382)
                    by_cases hcut384 : y ≤ q 76619688 scaleN
                    ·
                      apply V_pos_box_before_s1 76616335 76619688
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo383, hcut384⟩
                      · exact hne1
                    ·
                      have hlo385 : q 76619688 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut384)
                      apply V_pos_box_before_s1 76619688 76623040
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo385, hcut376⟩
                      · exact hne1
              ·
                have hlo377 : q 76623040 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut376)
                by_cases hcut386 : y ≤ q 76629744 scaleN
                ·
                  by_cases hcut388 : y ≤ q 76626392 scaleN
                  ·
                    apply V_pos_box_before_s1 76623040 76626392
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo377, hcut388⟩
                    · exact hne1
                  ·
                    have hlo389 : q 76626392 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut388)
                    apply V_pos_box_before_s1 76626392 76629744
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo389, hcut386⟩
                    · exact hne1
                ·
                  have hlo387 : q 76629744 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut386)
                  by_cases hcut390 : y ≤ q 76633097 scaleN
                  ·
                    apply V_pos_box_before_s1 76629744 76633097
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo387, hcut390⟩
                    · exact hne1
                  ·
                    have hlo391 : q 76633097 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut390)
                    by_cases hcut392 : y ≤ q 76636449 scaleN
                    ·
                      apply V_pos_box_before_s1 76633097 76636449
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo391, hcut392⟩
                      · exact hne1
                    ·
                      have hlo393 : q 76636449 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut392)
                      apply V_pos_box_before_s1 76636449 76639802
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo393, hcut316⟩
                      · exact hne1
        ·
          have hlo317 : q 76639802 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut316)
          by_cases hcut394 : y ≤ q 76703497 scaleN
          ·
            by_cases hcut396 : y ≤ q 76669973 scaleN
            ·
              by_cases hcut398 : y ≤ q 76653211 scaleN
              ·
                by_cases hcut400 : y ≤ q 76646507 scaleN
                ·
                  by_cases hcut402 : y ≤ q 76643154 scaleN
                  ·
                    apply V_pos_box_before_s1 76639802 76643154
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo317, hcut402⟩
                    · exact hne1
                  ·
                    have hlo403 : q 76643154 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut402)
                    apply V_pos_box_before_s1 76643154 76646507
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo403, hcut400⟩
                    · exact hne1
                ·
                  have hlo401 : q 76646507 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut400)
                  by_cases hcut404 : y ≤ q 76649859 scaleN
                  ·
                    apply V_pos_box_before_s1 76646507 76649859
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo401, hcut404⟩
                    · exact hne1
                  ·
                    have hlo405 : q 76649859 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut404)
                    apply V_pos_box_before_s1 76649859 76653211
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo405, hcut398⟩
                    · exact hne1
              ·
                have hlo399 : q 76653211 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut398)
                by_cases hcut406 : y ≤ q 76659916 scaleN
                ·
                  by_cases hcut408 : y ≤ q 76656563 scaleN
                  ·
                    apply V_pos_box_before_s1 76653211 76656563
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo399, hcut408⟩
                    · exact hne1
                  ·
                    have hlo409 : q 76656563 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut408)
                    apply V_pos_box_before_s1 76656563 76659916
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo409, hcut406⟩
                    · exact hne1
                ·
                  have hlo407 : q 76659916 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut406)
                  by_cases hcut410 : y ≤ q 76663268 scaleN
                  ·
                    apply V_pos_box_before_s1 76659916 76663268
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo407, hcut410⟩
                    · exact hne1
                  ·
                    have hlo411 : q 76663268 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut410)
                    by_cases hcut412 : y ≤ q 76666621 scaleN
                    ·
                      apply V_pos_box_before_s1 76663268 76666621
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo411, hcut412⟩
                      · exact hne1
                    ·
                      have hlo413 : q 76666621 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut412)
                      apply V_pos_box_before_s1 76666621 76669973
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo413, hcut396⟩
                      · exact hne1
            ·
              have hlo397 : q 76669973 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut396)
              by_cases hcut414 : y ≤ q 76686735 scaleN
              ·
                by_cases hcut416 : y ≤ q 76676678 scaleN
                ·
                  by_cases hcut418 : y ≤ q 76673326 scaleN
                  ·
                    apply V_pos_box_before_s1 76669973 76673326
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo397, hcut418⟩
                    · exact hne1
                  ·
                    have hlo419 : q 76673326 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut418)
                    apply V_pos_box_before_s1 76673326 76676678
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo419, hcut416⟩
                    · exact hne1
                ·
                  have hlo417 : q 76676678 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut416)
                  by_cases hcut420 : y ≤ q 76680030 scaleN
                  ·
                    apply V_pos_box_before_s1 76676678 76680030
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo417, hcut420⟩
                    · exact hne1
                  ·
                    have hlo421 : q 76680030 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut420)
                    by_cases hcut422 : y ≤ q 76683382 scaleN
                    ·
                      apply V_pos_box_before_s1 76680030 76683382
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo421, hcut422⟩
                      · exact hne1
                    ·
                      have hlo423 : q 76683382 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut422)
                      apply V_pos_box_before_s1 76683382 76686735
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo423, hcut414⟩
                      · exact hne1
              ·
                have hlo415 : q 76686735 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut414)
                by_cases hcut424 : y ≤ q 76693440 scaleN
                ·
                  by_cases hcut426 : y ≤ q 76690087 scaleN
                  ·
                    apply V_pos_box_before_s1 76686735 76690087
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo415, hcut426⟩
                    · exact hne1
                  ·
                    have hlo427 : q 76690087 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut426)
                    apply V_pos_box_before_s1 76690087 76693440
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo427, hcut424⟩
                    · exact hne1
                ·
                  have hlo425 : q 76693440 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut424)
                  by_cases hcut428 : y ≤ q 76696792 scaleN
                  ·
                    apply V_pos_box_before_s1 76693440 76696792
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo425, hcut428⟩
                    · exact hne1
                  ·
                    have hlo429 : q 76696792 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut428)
                    by_cases hcut430 : y ≤ q 76700145 scaleN
                    ·
                      apply V_pos_box_before_s1 76696792 76700145
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo429, hcut430⟩
                      · exact hne1
                    ·
                      have hlo431 : q 76700145 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut430)
                      apply V_pos_box_before_s1 76700145 76703497
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo431, hcut394⟩
                      · exact hne1
          ·
            have hlo395 : q 76703497 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut394)
            by_cases hcut432 : y ≤ q 76737020 scaleN
            ·
              by_cases hcut434 : y ≤ q 76720259 scaleN
              ·
                by_cases hcut436 : y ≤ q 76710201 scaleN
                ·
                  by_cases hcut438 : y ≤ q 76706849 scaleN
                  ·
                    apply V_pos_box_before_s1 76703497 76706849
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo395, hcut438⟩
                    · exact hne1
                  ·
                    have hlo439 : q 76706849 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut438)
                    apply V_pos_box_before_s1 76706849 76710201
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo439, hcut436⟩
                    · exact hne1
                ·
                  have hlo437 : q 76710201 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut436)
                  by_cases hcut440 : y ≤ q 76713554 scaleN
                  ·
                    apply V_pos_box_before_s1 76710201 76713554
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo437, hcut440⟩
                    · exact hne1
                  ·
                    have hlo441 : q 76713554 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut440)
                    by_cases hcut442 : y ≤ q 76716906 scaleN
                    ·
                      apply V_pos_box_before_s1 76713554 76716906
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo441, hcut442⟩
                      · exact hne1
                    ·
                      have hlo443 : q 76716906 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut442)
                      apply V_pos_box_before_s1 76716906 76720259
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo443, hcut434⟩
                      · exact hne1
              ·
                have hlo435 : q 76720259 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut434)
                by_cases hcut444 : y ≤ q 76726964 scaleN
                ·
                  by_cases hcut446 : y ≤ q 76723611 scaleN
                  ·
                    apply V_pos_box_before_s1 76720259 76723611
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo435, hcut446⟩
                    · exact hne1
                  ·
                    have hlo447 : q 76723611 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut446)
                    apply V_pos_box_before_s1 76723611 76726964
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo447, hcut444⟩
                    · exact hne1
                ·
                  have hlo445 : q 76726964 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut444)
                  by_cases hcut448 : y ≤ q 76730316 scaleN
                  ·
                    apply V_pos_box_before_s1 76726964 76730316
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo445, hcut448⟩
                    · exact hne1
                  ·
                    have hlo449 : q 76730316 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut448)
                    by_cases hcut450 : y ≤ q 76733668 scaleN
                    ·
                      apply V_pos_box_before_s1 76730316 76733668
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo449, hcut450⟩
                      · exact hne1
                    ·
                      have hlo451 : q 76733668 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut450)
                      apply V_pos_box_before_s1 76733668 76737020
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo451, hcut432⟩
                      · exact hne1
            ·
              have hlo433 : q 76737020 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut432)
              by_cases hcut452 : y ≤ q 76753783 scaleN
              ·
                by_cases hcut454 : y ≤ q 76743725 scaleN
                ·
                  by_cases hcut456 : y ≤ q 76740373 scaleN
                  ·
                    apply V_pos_box_before_s1 76737020 76740373
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo433, hcut456⟩
                    · exact hne1
                  ·
                    have hlo457 : q 76740373 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut456)
                    apply V_pos_box_before_s1 76740373 76743725
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo457, hcut454⟩
                    · exact hne1
                ·
                  have hlo455 : q 76743725 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut454)
                  by_cases hcut458 : y ≤ q 76747078 scaleN
                  ·
                    apply V_pos_box_before_s1 76743725 76747078
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo455, hcut458⟩
                    · exact hne1
                  ·
                    have hlo459 : q 76747078 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut458)
                    by_cases hcut460 : y ≤ q 76750430 scaleN
                    ·
                      apply V_pos_box_before_s1 76747078 76750430
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo459, hcut460⟩
                      · exact hne1
                    ·
                      have hlo461 : q 76750430 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut460)
                      apply V_pos_box_before_s1 76750430 76753783
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo461, hcut452⟩
                      · exact hne1
              ·
                have hlo453 : q 76753783 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut452)
                by_cases hcut462 : y ≤ q 76760487 scaleN
                ·
                  by_cases hcut464 : y ≤ q 76757135 scaleN
                  ·
                    apply V_pos_box_before_s1 76753783 76757135
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo453, hcut464⟩
                    · exact hne1
                  ·
                    have hlo465 : q 76757135 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut464)
                    apply V_pos_box_before_s1 76757135 76760487
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo465, hcut462⟩
                    · exact hne1
                ·
                  have hlo463 : q 76760487 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut462)
                  by_cases hcut466 : y ≤ q 76763839 scaleN
                  ·
                    apply V_pos_box_before_s1 76760487 76763839
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo463, hcut466⟩
                    · exact hne1
                  ·
                    have hlo467 : q 76763839 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut466)
                    by_cases hcut468 : y ≤ q 76767192 scaleN
                    ·
                      apply V_pos_box_before_s1 76763839 76767192
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo467, hcut468⟩
                      · exact hne1
                    ·
                      have hlo469 : q 76767192 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut468)
                      apply V_pos_box_before_s1 76767192 76770544
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo469, hcut314⟩
                      · exact hne1
      ·
        have hlo315 : q 76770544 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut314)
        by_cases hcut470 : y ≤ q 76901286 scaleN
        ·
          by_cases hcut472 : y ≤ q 76834239 scaleN
          ·
            by_cases hcut474 : y ≤ q 76800716 scaleN
            ·
              by_cases hcut476 : y ≤ q 76783954 scaleN
              ·
                by_cases hcut478 : y ≤ q 76777249 scaleN
                ·
                  by_cases hcut480 : y ≤ q 76773897 scaleN
                  ·
                    apply V_pos_box_before_s1 76770544 76773897
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo315, hcut480⟩
                    · exact hne1
                  ·
                    have hlo481 : q 76773897 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut480)
                    apply V_pos_box_before_s1 76773897 76777249
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo481, hcut478⟩
                    · exact hne1
                ·
                  have hlo479 : q 76777249 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut478)
                  by_cases hcut482 : y ≤ q 76780602 scaleN
                  ·
                    apply V_pos_box_before_s1 76777249 76780602
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo479, hcut482⟩
                    · exact hne1
                  ·
                    have hlo483 : q 76780602 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut482)
                    apply V_pos_box_before_s1 76780602 76783954
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo483, hcut476⟩
                    · exact hne1
              ·
                have hlo477 : q 76783954 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut476)
                by_cases hcut484 : y ≤ q 76790658 scaleN
                ·
                  by_cases hcut486 : y ≤ q 76787306 scaleN
                  ·
                    apply V_pos_box_before_s1 76783954 76787306
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo477, hcut486⟩
                    · exact hne1
                  ·
                    have hlo487 : q 76787306 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut486)
                    apply V_pos_box_before_s1 76787306 76790658
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo487, hcut484⟩
                    · exact hne1
                ·
                  have hlo485 : q 76790658 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut484)
                  by_cases hcut488 : y ≤ q 76794011 scaleN
                  ·
                    apply V_pos_box_before_s1 76790658 76794011
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo485, hcut488⟩
                    · exact hne1
                  ·
                    have hlo489 : q 76794011 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut488)
                    by_cases hcut490 : y ≤ q 76797363 scaleN
                    ·
                      apply V_pos_box_before_s1 76794011 76797363
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo489, hcut490⟩
                      · exact hne1
                    ·
                      have hlo491 : q 76797363 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut490)
                      apply V_pos_box_before_s1 76797363 76800716
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo491, hcut474⟩
                      · exact hne1
            ·
              have hlo475 : q 76800716 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut474)
              by_cases hcut492 : y ≤ q 76817477 scaleN
              ·
                by_cases hcut494 : y ≤ q 76807421 scaleN
                ·
                  by_cases hcut496 : y ≤ q 76804068 scaleN
                  ·
                    apply V_pos_box_before_s1 76800716 76804068
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo475, hcut496⟩
                    · exact hne1
                  ·
                    have hlo497 : q 76804068 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut496)
                    apply V_pos_box_before_s1 76804068 76807421
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo497, hcut494⟩
                    · exact hne1
                ·
                  have hlo495 : q 76807421 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut494)
                  by_cases hcut498 : y ≤ q 76810773 scaleN
                  ·
                    apply V_pos_box_before_s1 76807421 76810773
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo495, hcut498⟩
                    · exact hne1
                  ·
                    have hlo499 : q 76810773 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut498)
                    by_cases hcut500 : y ≤ q 76814125 scaleN
                    ·
                      apply V_pos_box_before_s1 76810773 76814125
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo499, hcut500⟩
                      · exact hne1
                    ·
                      have hlo501 : q 76814125 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut500)
                      apply V_pos_box_before_s1 76814125 76817477
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo501, hcut492⟩
                      · exact hne1
              ·
                have hlo493 : q 76817477 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut492)
                by_cases hcut502 : y ≤ q 76824182 scaleN
                ·
                  by_cases hcut504 : y ≤ q 76820830 scaleN
                  ·
                    apply V_pos_box_before_s1 76817477 76820830
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo493, hcut504⟩
                    · exact hne1
                  ·
                    have hlo505 : q 76820830 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut504)
                    apply V_pos_box_before_s1 76820830 76824182
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo505, hcut502⟩
                    · exact hne1
                ·
                  have hlo503 : q 76824182 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut502)
                  by_cases hcut506 : y ≤ q 76827534 scaleN
                  ·
                    apply V_pos_box_before_s1 76824182 76827534
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo503, hcut506⟩
                    · exact hne1
                  ·
                    have hlo507 : q 76827534 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut506)
                    by_cases hcut508 : y ≤ q 76830886 scaleN
                    ·
                      apply V_pos_box_before_s1 76827534 76830886
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo507, hcut508⟩
                      · exact hne1
                    ·
                      have hlo509 : q 76830886 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut508)
                      apply V_pos_box_before_s1 76830886 76834239
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo509, hcut472⟩
                      · exact hne1
          ·
            have hlo473 : q 76834239 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut472)
            by_cases hcut510 : y ≤ q 76867762 scaleN
            ·
              by_cases hcut512 : y ≤ q 76851000 scaleN
              ·
                by_cases hcut514 : y ≤ q 76840943 scaleN
                ·
                  by_cases hcut516 : y ≤ q 76837591 scaleN
                  ·
                    apply V_pos_box_before_s1 76834239 76837591
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo473, hcut516⟩
                    · exact hne1
                  ·
                    have hlo517 : q 76837591 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut516)
                    apply V_pos_box_before_s1 76837591 76840943
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo517, hcut514⟩
                    · exact hne1
                ·
                  have hlo515 : q 76840943 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut514)
                  by_cases hcut518 : y ≤ q 76844295 scaleN
                  ·
                    apply V_pos_box_before_s1 76840943 76844295
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo515, hcut518⟩
                    · exact hne1
                  ·
                    have hlo519 : q 76844295 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut518)
                    by_cases hcut520 : y ≤ q 76847648 scaleN
                    ·
                      apply V_pos_box_before_s1 76844295 76847648
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo519, hcut520⟩
                      · exact hne1
                    ·
                      have hlo521 : q 76847648 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut520)
                      apply V_pos_box_before_s1 76847648 76851000
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo521, hcut512⟩
                      · exact hne1
              ·
                have hlo513 : q 76851000 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut512)
                by_cases hcut522 : y ≤ q 76857705 scaleN
                ·
                  by_cases hcut524 : y ≤ q 76854353 scaleN
                  ·
                    apply V_pos_box_before_s1 76851000 76854353
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo513, hcut524⟩
                    · exact hne1
                  ·
                    have hlo525 : q 76854353 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut524)
                    apply V_pos_box_before_s1 76854353 76857705
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo525, hcut522⟩
                    · exact hne1
                ·
                  have hlo523 : q 76857705 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut522)
                  by_cases hcut526 : y ≤ q 76861058 scaleN
                  ·
                    apply V_pos_box_before_s1 76857705 76861058
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo523, hcut526⟩
                    · exact hne1
                  ·
                    have hlo527 : q 76861058 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut526)
                    by_cases hcut528 : y ≤ q 76864410 scaleN
                    ·
                      apply V_pos_box_before_s1 76861058 76864410
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo527, hcut528⟩
                      · exact hne1
                    ·
                      have hlo529 : q 76864410 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut528)
                      apply V_pos_box_before_s1 76864410 76867762
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo529, hcut510⟩
                      · exact hne1
            ·
              have hlo511 : q 76867762 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut510)
              by_cases hcut530 : y ≤ q 76884524 scaleN
              ·
                by_cases hcut532 : y ≤ q 76874467 scaleN
                ·
                  by_cases hcut534 : y ≤ q 76871114 scaleN
                  ·
                    apply V_pos_box_before_s1 76867762 76871114
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo511, hcut534⟩
                    · exact hne1
                  ·
                    have hlo535 : q 76871114 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut534)
                    apply V_pos_box_before_s1 76871114 76874467
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo535, hcut532⟩
                    · exact hne1
                ·
                  have hlo533 : q 76874467 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut532)
                  by_cases hcut536 : y ≤ q 76877819 scaleN
                  ·
                    apply V_pos_box_before_s1 76874467 76877819
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo533, hcut536⟩
                    · exact hne1
                  ·
                    have hlo537 : q 76877819 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut536)
                    by_cases hcut538 : y ≤ q 76881172 scaleN
                    ·
                      apply V_pos_box_before_s1 76877819 76881172
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo537, hcut538⟩
                      · exact hne1
                    ·
                      have hlo539 : q 76881172 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut538)
                      apply V_pos_box_before_s1 76881172 76884524
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo539, hcut530⟩
                      · exact hne1
              ·
                have hlo531 : q 76884524 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut530)
                by_cases hcut540 : y ≤ q 76891229 scaleN
                ·
                  by_cases hcut542 : y ≤ q 76887877 scaleN
                  ·
                    apply V_pos_box_before_s1 76884524 76887877
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo531, hcut542⟩
                    · exact hne1
                  ·
                    have hlo543 : q 76887877 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut542)
                    apply V_pos_box_before_s1 76887877 76891229
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo543, hcut540⟩
                    · exact hne1
                ·
                  have hlo541 : q 76891229 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut540)
                  by_cases hcut544 : y ≤ q 76894581 scaleN
                  ·
                    apply V_pos_box_before_s1 76891229 76894581
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo541, hcut544⟩
                    · exact hne1
                  ·
                    have hlo545 : q 76894581 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut544)
                    by_cases hcut546 : y ≤ q 76897933 scaleN
                    ·
                      apply V_pos_box_before_s1 76894581 76897933
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo545, hcut546⟩
                      · exact hne1
                    ·
                      have hlo547 : q 76897933 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut546)
                      apply V_pos_box_before_s1 76897933 76901286
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo547, hcut470⟩
                      · exact hne1
        ·
          have hlo471 : q 76901286 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut470)
          by_cases hcut548 : y ≤ q 76968334 scaleN
          ·
            by_cases hcut550 : y ≤ q 76934810 scaleN
            ·
              by_cases hcut552 : y ≤ q 76918048 scaleN
              ·
                by_cases hcut554 : y ≤ q 76907991 scaleN
                ·
                  by_cases hcut556 : y ≤ q 76904638 scaleN
                  ·
                    apply V_pos_box_before_s1 76901286 76904638
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo471, hcut556⟩
                    · exact hne1
                  ·
                    have hlo557 : q 76904638 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut556)
                    apply V_pos_box_before_s1 76904638 76907991
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo557, hcut554⟩
                    · exact hne1
                ·
                  have hlo555 : q 76907991 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut554)
                  by_cases hcut558 : y ≤ q 76911343 scaleN
                  ·
                    apply V_pos_box_before_s1 76907991 76911343
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo555, hcut558⟩
                    · exact hne1
                  ·
                    have hlo559 : q 76911343 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut558)
                    by_cases hcut560 : y ≤ q 76914696 scaleN
                    ·
                      apply V_pos_box_before_s1 76911343 76914696
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo559, hcut560⟩
                      · exact hne1
                    ·
                      have hlo561 : q 76914696 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut560)
                      apply V_pos_box_before_s1 76914696 76918048
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo561, hcut552⟩
                      · exact hne1
              ·
                have hlo553 : q 76918048 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut552)
                by_cases hcut562 : y ≤ q 76924752 scaleN
                ·
                  by_cases hcut564 : y ≤ q 76921400 scaleN
                  ·
                    apply V_pos_box_before_s1 76918048 76921400
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo553, hcut564⟩
                    · exact hne1
                  ·
                    have hlo565 : q 76921400 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut564)
                    apply V_pos_box_before_s1 76921400 76924752
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo565, hcut562⟩
                    · exact hne1
                ·
                  have hlo563 : q 76924752 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut562)
                  by_cases hcut566 : y ≤ q 76928105 scaleN
                  ·
                    apply V_pos_box_before_s1 76924752 76928105
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo563, hcut566⟩
                    · exact hne1
                  ·
                    have hlo567 : q 76928105 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut566)
                    by_cases hcut568 : y ≤ q 76931457 scaleN
                    ·
                      apply V_pos_box_before_s1 76928105 76931457
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo567, hcut568⟩
                      · exact hne1
                    ·
                      have hlo569 : q 76931457 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut568)
                      apply V_pos_box_before_s1 76931457 76934810
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo569, hcut550⟩
                      · exact hne1
            ·
              have hlo551 : q 76934810 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut550)
              by_cases hcut570 : y ≤ q 76951571 scaleN
              ·
                by_cases hcut572 : y ≤ q 76941515 scaleN
                ·
                  by_cases hcut574 : y ≤ q 76938162 scaleN
                  ·
                    apply V_pos_box_before_s1 76934810 76938162
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo551, hcut574⟩
                    · exact hne1
                  ·
                    have hlo575 : q 76938162 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut574)
                    apply V_pos_box_before_s1 76938162 76941515
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo575, hcut572⟩
                    · exact hne1
                ·
                  have hlo573 : q 76941515 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut572)
                  by_cases hcut576 : y ≤ q 76944867 scaleN
                  ·
                    apply V_pos_box_before_s1 76941515 76944867
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo573, hcut576⟩
                    · exact hne1
                  ·
                    have hlo577 : q 76944867 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut576)
                    by_cases hcut578 : y ≤ q 76948219 scaleN
                    ·
                      apply V_pos_box_before_s1 76944867 76948219
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo577, hcut578⟩
                      · exact hne1
                    ·
                      have hlo579 : q 76948219 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut578)
                      apply V_pos_box_before_s1 76948219 76951571
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo579, hcut570⟩
                      · exact hne1
              ·
                have hlo571 : q 76951571 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut570)
                by_cases hcut580 : y ≤ q 76958276 scaleN
                ·
                  by_cases hcut582 : y ≤ q 76954924 scaleN
                  ·
                    apply V_pos_box_before_s1 76951571 76954924
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo571, hcut582⟩
                    · exact hne1
                  ·
                    have hlo583 : q 76954924 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut582)
                    apply V_pos_box_before_s1 76954924 76958276
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo583, hcut580⟩
                    · exact hne1
                ·
                  have hlo581 : q 76958276 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut580)
                  by_cases hcut584 : y ≤ q 76961629 scaleN
                  ·
                    apply V_pos_box_before_s1 76958276 76961629
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo581, hcut584⟩
                    · exact hne1
                  ·
                    have hlo585 : q 76961629 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut584)
                    by_cases hcut586 : y ≤ q 76964981 scaleN
                    ·
                      apply V_pos_box_before_s1 76961629 76964981
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo585, hcut586⟩
                      · exact hne1
                    ·
                      have hlo587 : q 76964981 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut586)
                      apply V_pos_box_before_s1 76964981 76968334
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo587, hcut548⟩
                      · exact hne1
          ·
            have hlo549 : q 76968334 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut548)
            by_cases hcut588 : y ≤ q 77001857 scaleN
            ·
              by_cases hcut590 : y ≤ q 76985095 scaleN
              ·
                by_cases hcut592 : y ≤ q 76975038 scaleN
                ·
                  by_cases hcut594 : y ≤ q 76971686 scaleN
                  ·
                    apply V_pos_box_before_s1 76968334 76971686
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo549, hcut594⟩
                    · exact hne1
                  ·
                    have hlo595 : q 76971686 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut594)
                    apply V_pos_box_before_s1 76971686 76975038
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo595, hcut592⟩
                    · exact hne1
                ·
                  have hlo593 : q 76975038 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut592)
                  by_cases hcut596 : y ≤ q 76978390 scaleN
                  ·
                    apply V_pos_box_before_s1 76975038 76978390
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo593, hcut596⟩
                    · exact hne1
                  ·
                    have hlo597 : q 76978390 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut596)
                    by_cases hcut598 : y ≤ q 76981743 scaleN
                    ·
                      apply V_pos_box_before_s1 76978390 76981743
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo597, hcut598⟩
                      · exact hne1
                    ·
                      have hlo599 : q 76981743 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut598)
                      apply V_pos_box_before_s1 76981743 76985095
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo599, hcut590⟩
                      · exact hne1
              ·
                have hlo591 : q 76985095 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut590)
                by_cases hcut600 : y ≤ q 76991800 scaleN
                ·
                  by_cases hcut602 : y ≤ q 76988448 scaleN
                  ·
                    apply V_pos_box_before_s1 76985095 76988448
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo591, hcut602⟩
                    · exact hne1
                  ·
                    have hlo603 : q 76988448 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut602)
                    apply V_pos_box_before_s1 76988448 76991800
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo603, hcut600⟩
                    · exact hne1
                ·
                  have hlo601 : q 76991800 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut600)
                  by_cases hcut604 : y ≤ q 76995153 scaleN
                  ·
                    apply V_pos_box_before_s1 76991800 76995153
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo601, hcut604⟩
                    · exact hne1
                  ·
                    have hlo605 : q 76995153 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut604)
                    by_cases hcut606 : y ≤ q 76998505 scaleN
                    ·
                      apply V_pos_box_before_s1 76995153 76998505
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo605, hcut606⟩
                      · exact hne1
                    ·
                      have hlo607 : q 76998505 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut606)
                      apply V_pos_box_before_s1 76998505 77001857
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo607, hcut588⟩
                      · exact hne1
            ·
              have hlo589 : q 77001857 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut588)
              by_cases hcut608 : y ≤ q 77018619 scaleN
              ·
                by_cases hcut610 : y ≤ q 77008562 scaleN
                ·
                  by_cases hcut612 : y ≤ q 77005209 scaleN
                  ·
                    apply V_pos_box_before_s1 77001857 77005209
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo589, hcut612⟩
                    · exact hne1
                  ·
                    have hlo613 : q 77005209 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut612)
                    apply V_pos_box_before_s1 77005209 77008562
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo613, hcut610⟩
                    · exact hne1
                ·
                  have hlo611 : q 77008562 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut610)
                  by_cases hcut614 : y ≤ q 77011914 scaleN
                  ·
                    apply V_pos_box_before_s1 77008562 77011914
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo611, hcut614⟩
                    · exact hne1
                  ·
                    have hlo615 : q 77011914 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut614)
                    by_cases hcut616 : y ≤ q 77015267 scaleN
                    ·
                      apply V_pos_box_before_s1 77011914 77015267
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo615, hcut616⟩
                      · exact hne1
                    ·
                      have hlo617 : q 77015267 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut616)
                      apply V_pos_box_before_s1 77015267 77018619
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo617, hcut608⟩
                      · exact hne1
              ·
                have hlo609 : q 77018619 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut608)
                by_cases hcut618 : y ≤ q 77025324 scaleN
                ·
                  by_cases hcut620 : y ≤ q 77021972 scaleN
                  ·
                    apply V_pos_box_before_s1 77018619 77021972
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo609, hcut620⟩
                    · exact hne1
                  ·
                    have hlo621 : q 77021972 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut620)
                    apply V_pos_box_before_s1 77021972 77025324
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo621, hcut618⟩
                    · exact hne1
                ·
                  have hlo619 : q 77025324 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut618)
                  by_cases hcut622 : y ≤ q 77028676 scaleN
                  ·
                    apply V_pos_box_before_s1 77025324 77028676
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo619, hcut622⟩
                    · exact hne1
                  ·
                    have hlo623 : q 77028676 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut622)
                    by_cases hcut624 : y ≤ q 77032028 scaleN
                    ·
                      apply V_pos_box_before_s1 77028676 77032028
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo623, hcut624⟩
                      · exact hne1
                    ·
                      have hlo625 : q 77032028 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut624)
                      apply V_pos_box_before_s1 77032028 77035381
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo625, hcut0⟩
                      · exact hne1
  ·
    have hlo1 : q 77035381 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut0)
    by_cases hcut626 : y ≤ q 77672329 scaleN
    ·
      by_cases hcut628 : y ≤ q 77296864 scaleN
      ·
        by_cases hcut630 : y ≤ q 77166122 scaleN
        ·
          by_cases hcut632 : y ≤ q 77099075 scaleN
          ·
            by_cases hcut634 : y ≤ q 77065551 scaleN
            ·
              by_cases hcut636 : y ≤ q 77048790 scaleN
              ·
                by_cases hcut638 : y ≤ q 77042085 scaleN
                ·
                  by_cases hcut640 : y ≤ q 77038733 scaleN
                  ·
                    apply V_pos_box_before_s1 77035381 77038733
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1, hcut640⟩
                    · exact hne1
                  ·
                    have hlo641 : q 77038733 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut640)
                    apply V_pos_box_before_s1 77038733 77042085
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo641, hcut638⟩
                    · exact hne1
                ·
                  have hlo639 : q 77042085 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut638)
                  by_cases hcut642 : y ≤ q 77045437 scaleN
                  ·
                    apply V_pos_box_before_s1 77042085 77045437
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo639, hcut642⟩
                    · exact hne1
                  ·
                    have hlo643 : q 77045437 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut642)
                    apply V_pos_box_before_s1 77045437 77048790
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo643, hcut636⟩
                    · exact hne1
              ·
                have hlo637 : q 77048790 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut636)
                by_cases hcut644 : y ≤ q 77055494 scaleN
                ·
                  by_cases hcut646 : y ≤ q 77052142 scaleN
                  ·
                    apply V_pos_box_before_s1 77048790 77052142
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo637, hcut646⟩
                    · exact hne1
                  ·
                    have hlo647 : q 77052142 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut646)
                    apply V_pos_box_before_s1 77052142 77055494
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo647, hcut644⟩
                    · exact hne1
                ·
                  have hlo645 : q 77055494 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut644)
                  by_cases hcut648 : y ≤ q 77058846 scaleN
                  ·
                    apply V_pos_box_before_s1 77055494 77058846
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo645, hcut648⟩
                    · exact hne1
                  ·
                    have hlo649 : q 77058846 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut648)
                    by_cases hcut650 : y ≤ q 77062199 scaleN
                    ·
                      apply V_pos_box_before_s1 77058846 77062199
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo649, hcut650⟩
                      · exact hne1
                    ·
                      have hlo651 : q 77062199 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut650)
                      apply V_pos_box_before_s1 77062199 77065551
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo651, hcut634⟩
                      · exact hne1
            ·
              have hlo635 : q 77065551 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut634)
              by_cases hcut652 : y ≤ q 77082313 scaleN
              ·
                by_cases hcut654 : y ≤ q 77072256 scaleN
                ·
                  by_cases hcut656 : y ≤ q 77068904 scaleN
                  ·
                    apply V_pos_box_before_s1 77065551 77068904
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo635, hcut656⟩
                    · exact hne1
                  ·
                    have hlo657 : q 77068904 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut656)
                    apply V_pos_box_before_s1 77068904 77072256
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo657, hcut654⟩
                    · exact hne1
                ·
                  have hlo655 : q 77072256 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut654)
                  by_cases hcut658 : y ≤ q 77075609 scaleN
                  ·
                    apply V_pos_box_before_s1 77072256 77075609
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo655, hcut658⟩
                    · exact hne1
                  ·
                    have hlo659 : q 77075609 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut658)
                    by_cases hcut660 : y ≤ q 77078961 scaleN
                    ·
                      apply V_pos_box_before_s1 77075609 77078961
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo659, hcut660⟩
                      · exact hne1
                    ·
                      have hlo661 : q 77078961 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut660)
                      apply V_pos_box_before_s1 77078961 77082313
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo661, hcut652⟩
                      · exact hne1
              ·
                have hlo653 : q 77082313 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut652)
                by_cases hcut662 : y ≤ q 77089018 scaleN
                ·
                  by_cases hcut664 : y ≤ q 77085665 scaleN
                  ·
                    apply V_pos_box_before_s1 77082313 77085665
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo653, hcut664⟩
                    · exact hne1
                  ·
                    have hlo665 : q 77085665 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut664)
                    apply V_pos_box_before_s1 77085665 77089018
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo665, hcut662⟩
                    · exact hne1
                ·
                  have hlo663 : q 77089018 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut662)
                  by_cases hcut666 : y ≤ q 77092370 scaleN
                  ·
                    apply V_pos_box_before_s1 77089018 77092370
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo663, hcut666⟩
                    · exact hne1
                  ·
                    have hlo667 : q 77092370 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut666)
                    by_cases hcut668 : y ≤ q 77095723 scaleN
                    ·
                      apply V_pos_box_before_s1 77092370 77095723
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo667, hcut668⟩
                      · exact hne1
                    ·
                      have hlo669 : q 77095723 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut668)
                      apply V_pos_box_before_s1 77095723 77099075
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo669, hcut632⟩
                      · exact hne1
          ·
            have hlo633 : q 77099075 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut632)
            by_cases hcut670 : y ≤ q 77132599 scaleN
            ·
              by_cases hcut672 : y ≤ q 77115837 scaleN
              ·
                by_cases hcut674 : y ≤ q 77105780 scaleN
                ·
                  by_cases hcut676 : y ≤ q 77102428 scaleN
                  ·
                    apply V_pos_box_before_s1 77099075 77102428
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo633, hcut676⟩
                    · exact hne1
                  ·
                    have hlo677 : q 77102428 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut676)
                    apply V_pos_box_before_s1 77102428 77105780
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo677, hcut674⟩
                    · exact hne1
                ·
                  have hlo675 : q 77105780 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut674)
                  by_cases hcut678 : y ≤ q 77109132 scaleN
                  ·
                    apply V_pos_box_before_s1 77105780 77109132
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo675, hcut678⟩
                    · exact hne1
                  ·
                    have hlo679 : q 77109132 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut678)
                    by_cases hcut680 : y ≤ q 77112484 scaleN
                    ·
                      apply V_pos_box_before_s1 77109132 77112484
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo679, hcut680⟩
                      · exact hne1
                    ·
                      have hlo681 : q 77112484 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut680)
                      apply V_pos_box_before_s1 77112484 77115837
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo681, hcut672⟩
                      · exact hne1
              ·
                have hlo673 : q 77115837 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut672)
                by_cases hcut682 : y ≤ q 77122542 scaleN
                ·
                  by_cases hcut684 : y ≤ q 77119189 scaleN
                  ·
                    apply V_pos_box_before_s1 77115837 77119189
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo673, hcut684⟩
                    · exact hne1
                  ·
                    have hlo685 : q 77119189 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut684)
                    apply V_pos_box_before_s1 77119189 77122542
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo685, hcut682⟩
                    · exact hne1
                ·
                  have hlo683 : q 77122542 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut682)
                  by_cases hcut686 : y ≤ q 77125894 scaleN
                  ·
                    apply V_pos_box_before_s1 77122542 77125894
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo683, hcut686⟩
                    · exact hne1
                  ·
                    have hlo687 : q 77125894 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut686)
                    by_cases hcut688 : y ≤ q 77129247 scaleN
                    ·
                      apply V_pos_box_before_s1 77125894 77129247
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo687, hcut688⟩
                      · exact hne1
                    ·
                      have hlo689 : q 77129247 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut688)
                      apply V_pos_box_before_s1 77129247 77132599
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo689, hcut670⟩
                      · exact hne1
            ·
              have hlo671 : q 77132599 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut670)
              by_cases hcut690 : y ≤ q 77149361 scaleN
              ·
                by_cases hcut692 : y ≤ q 77139303 scaleN
                ·
                  by_cases hcut694 : y ≤ q 77135951 scaleN
                  ·
                    apply V_pos_box_before_s1 77132599 77135951
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo671, hcut694⟩
                    · exact hne1
                  ·
                    have hlo695 : q 77135951 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut694)
                    apply V_pos_box_before_s1 77135951 77139303
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo695, hcut692⟩
                    · exact hne1
                ·
                  have hlo693 : q 77139303 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut692)
                  by_cases hcut696 : y ≤ q 77142656 scaleN
                  ·
                    apply V_pos_box_before_s1 77139303 77142656
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo693, hcut696⟩
                    · exact hne1
                  ·
                    have hlo697 : q 77142656 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut696)
                    by_cases hcut698 : y ≤ q 77146008 scaleN
                    ·
                      apply V_pos_box_before_s1 77142656 77146008
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo697, hcut698⟩
                      · exact hne1
                    ·
                      have hlo699 : q 77146008 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut698)
                      apply V_pos_box_before_s1 77146008 77149361
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo699, hcut690⟩
                      · exact hne1
              ·
                have hlo691 : q 77149361 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut690)
                by_cases hcut700 : y ≤ q 77156066 scaleN
                ·
                  by_cases hcut702 : y ≤ q 77152713 scaleN
                  ·
                    apply V_pos_box_before_s1 77149361 77152713
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo691, hcut702⟩
                    · exact hne1
                  ·
                    have hlo703 : q 77152713 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut702)
                    apply V_pos_box_before_s1 77152713 77156066
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo703, hcut700⟩
                    · exact hne1
                ·
                  have hlo701 : q 77156066 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut700)
                  by_cases hcut704 : y ≤ q 77159418 scaleN
                  ·
                    apply V_pos_box_before_s1 77156066 77159418
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo701, hcut704⟩
                    · exact hne1
                  ·
                    have hlo705 : q 77159418 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut704)
                    by_cases hcut706 : y ≤ q 77162770 scaleN
                    ·
                      apply V_pos_box_before_s1 77159418 77162770
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo705, hcut706⟩
                      · exact hne1
                    ·
                      have hlo707 : q 77162770 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut706)
                      apply V_pos_box_before_s1 77162770 77166122
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo707, hcut630⟩
                      · exact hne1
        ·
          have hlo631 : q 77166122 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut630)
          by_cases hcut708 : y ≤ q 77229818 scaleN
          ·
            by_cases hcut710 : y ≤ q 77196294 scaleN
            ·
              by_cases hcut712 : y ≤ q 77179532 scaleN
              ·
                by_cases hcut714 : y ≤ q 77172827 scaleN
                ·
                  by_cases hcut716 : y ≤ q 77169475 scaleN
                  ·
                    apply V_pos_box_before_s1 77166122 77169475
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo631, hcut716⟩
                    · exact hne1
                  ·
                    have hlo717 : q 77169475 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut716)
                    apply V_pos_box_before_s1 77169475 77172827
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo717, hcut714⟩
                    · exact hne1
                ·
                  have hlo715 : q 77172827 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut714)
                  by_cases hcut718 : y ≤ q 77176180 scaleN
                  ·
                    apply V_pos_box_before_s1 77172827 77176180
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo715, hcut718⟩
                    · exact hne1
                  ·
                    have hlo719 : q 77176180 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut718)
                    apply V_pos_box_before_s1 77176180 77179532
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo719, hcut712⟩
                    · exact hne1
              ·
                have hlo713 : q 77179532 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut712)
                by_cases hcut720 : y ≤ q 77186237 scaleN
                ·
                  by_cases hcut722 : y ≤ q 77182885 scaleN
                  ·
                    apply V_pos_box_before_s1 77179532 77182885
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo713, hcut722⟩
                    · exact hne1
                  ·
                    have hlo723 : q 77182885 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut722)
                    apply V_pos_box_before_s1 77182885 77186237
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo723, hcut720⟩
                    · exact hne1
                ·
                  have hlo721 : q 77186237 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut720)
                  by_cases hcut724 : y ≤ q 77189589 scaleN
                  ·
                    apply V_pos_box_before_s1 77186237 77189589
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo721, hcut724⟩
                    · exact hne1
                  ·
                    have hlo725 : q 77189589 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut724)
                    by_cases hcut726 : y ≤ q 77192941 scaleN
                    ·
                      apply V_pos_box_before_s1 77189589 77192941
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo725, hcut726⟩
                      · exact hne1
                    ·
                      have hlo727 : q 77192941 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut726)
                      apply V_pos_box_before_s1 77192941 77196294
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo727, hcut710⟩
                      · exact hne1
            ·
              have hlo711 : q 77196294 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut710)
              by_cases hcut728 : y ≤ q 77213056 scaleN
              ·
                by_cases hcut730 : y ≤ q 77202999 scaleN
                ·
                  by_cases hcut732 : y ≤ q 77199646 scaleN
                  ·
                    apply V_pos_box_before_s1 77196294 77199646
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo711, hcut732⟩
                    · exact hne1
                  ·
                    have hlo733 : q 77199646 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut732)
                    apply V_pos_box_before_s1 77199646 77202999
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo733, hcut730⟩
                    · exact hne1
                ·
                  have hlo731 : q 77202999 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut730)
                  by_cases hcut734 : y ≤ q 77206351 scaleN
                  ·
                    apply V_pos_box_before_s1 77202999 77206351
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo731, hcut734⟩
                    · exact hne1
                  ·
                    have hlo735 : q 77206351 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut734)
                    by_cases hcut736 : y ≤ q 77209704 scaleN
                    ·
                      apply V_pos_box_before_s1 77206351 77209704
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo735, hcut736⟩
                      · exact hne1
                    ·
                      have hlo737 : q 77209704 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut736)
                      apply V_pos_box_before_s1 77209704 77213056
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo737, hcut728⟩
                      · exact hne1
              ·
                have hlo729 : q 77213056 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut728)
                by_cases hcut738 : y ≤ q 77219760 scaleN
                ·
                  by_cases hcut740 : y ≤ q 77216408 scaleN
                  ·
                    apply V_pos_box_before_s1 77213056 77216408
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo729, hcut740⟩
                    · exact hne1
                  ·
                    have hlo741 : q 77216408 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut740)
                    apply V_pos_box_before_s1 77216408 77219760
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo741, hcut738⟩
                    · exact hne1
                ·
                  have hlo739 : q 77219760 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut738)
                  by_cases hcut742 : y ≤ q 77223113 scaleN
                  ·
                    apply V_pos_box_before_s1 77219760 77223113
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo739, hcut742⟩
                    · exact hne1
                  ·
                    have hlo743 : q 77223113 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut742)
                    by_cases hcut744 : y ≤ q 77226465 scaleN
                    ·
                      apply V_pos_box_before_s1 77223113 77226465
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo743, hcut744⟩
                      · exact hne1
                    ·
                      have hlo745 : q 77226465 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut744)
                      apply V_pos_box_before_s1 77226465 77229818
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo745, hcut708⟩
                      · exact hne1
          ·
            have hlo709 : q 77229818 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut708)
            by_cases hcut746 : y ≤ q 77263341 scaleN
            ·
              by_cases hcut748 : y ≤ q 77246579 scaleN
              ·
                by_cases hcut750 : y ≤ q 77236523 scaleN
                ·
                  by_cases hcut752 : y ≤ q 77233170 scaleN
                  ·
                    apply V_pos_box_before_s1 77229818 77233170
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo709, hcut752⟩
                    · exact hne1
                  ·
                    have hlo753 : q 77233170 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut752)
                    apply V_pos_box_before_s1 77233170 77236523
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo753, hcut750⟩
                    · exact hne1
                ·
                  have hlo751 : q 77236523 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut750)
                  by_cases hcut754 : y ≤ q 77239875 scaleN
                  ·
                    apply V_pos_box_before_s1 77236523 77239875
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo751, hcut754⟩
                    · exact hne1
                  ·
                    have hlo755 : q 77239875 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut754)
                    by_cases hcut756 : y ≤ q 77243227 scaleN
                    ·
                      apply V_pos_box_before_s1 77239875 77243227
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo755, hcut756⟩
                      · exact hne1
                    ·
                      have hlo757 : q 77243227 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut756)
                      apply V_pos_box_before_s1 77243227 77246579
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo757, hcut748⟩
                      · exact hne1
              ·
                have hlo749 : q 77246579 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut748)
                by_cases hcut758 : y ≤ q 77253284 scaleN
                ·
                  by_cases hcut760 : y ≤ q 77249932 scaleN
                  ·
                    apply V_pos_box_before_s1 77246579 77249932
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo749, hcut760⟩
                    · exact hne1
                  ·
                    have hlo761 : q 77249932 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut760)
                    apply V_pos_box_before_s1 77249932 77253284
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo761, hcut758⟩
                    · exact hne1
                ·
                  have hlo759 : q 77253284 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut758)
                  by_cases hcut762 : y ≤ q 77256636 scaleN
                  ·
                    apply V_pos_box_before_s1 77253284 77256636
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo759, hcut762⟩
                    · exact hne1
                  ·
                    have hlo763 : q 77256636 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut762)
                    by_cases hcut764 : y ≤ q 77259988 scaleN
                    ·
                      apply V_pos_box_before_s1 77256636 77259988
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo763, hcut764⟩
                      · exact hne1
                    ·
                      have hlo765 : q 77259988 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut764)
                      apply V_pos_box_before_s1 77259988 77263341
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo765, hcut746⟩
                      · exact hne1
            ·
              have hlo747 : q 77263341 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut746)
              by_cases hcut766 : y ≤ q 77280102 scaleN
              ·
                by_cases hcut768 : y ≤ q 77270045 scaleN
                ·
                  by_cases hcut770 : y ≤ q 77266693 scaleN
                  ·
                    apply V_pos_box_before_s1 77263341 77266693
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo747, hcut770⟩
                    · exact hne1
                  ·
                    have hlo771 : q 77266693 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut770)
                    apply V_pos_box_before_s1 77266693 77270045
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo771, hcut768⟩
                    · exact hne1
                ·
                  have hlo769 : q 77270045 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut768)
                  by_cases hcut772 : y ≤ q 77273397 scaleN
                  ·
                    apply V_pos_box_before_s1 77270045 77273397
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo769, hcut772⟩
                    · exact hne1
                  ·
                    have hlo773 : q 77273397 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut772)
                    by_cases hcut774 : y ≤ q 77276750 scaleN
                    ·
                      apply V_pos_box_before_s1 77273397 77276750
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo773, hcut774⟩
                      · exact hne1
                    ·
                      have hlo775 : q 77276750 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut774)
                      apply V_pos_box_before_s1 77276750 77280102
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo775, hcut766⟩
                      · exact hne1
              ·
                have hlo767 : q 77280102 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut766)
                by_cases hcut776 : y ≤ q 77286807 scaleN
                ·
                  by_cases hcut778 : y ≤ q 77283455 scaleN
                  ·
                    apply V_pos_box_before_s1 77280102 77283455
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo767, hcut778⟩
                    · exact hne1
                  ·
                    have hlo779 : q 77283455 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut778)
                    apply V_pos_box_before_s1 77283455 77286807
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo779, hcut776⟩
                    · exact hne1
                ·
                  have hlo777 : q 77286807 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut776)
                  by_cases hcut780 : y ≤ q 77290160 scaleN
                  ·
                    apply V_pos_box_before_s1 77286807 77290160
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo777, hcut780⟩
                    · exact hne1
                  ·
                    have hlo781 : q 77290160 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut780)
                    by_cases hcut782 : y ≤ q 77293512 scaleN
                    ·
                      apply V_pos_box_before_s1 77290160 77293512
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo781, hcut782⟩
                      · exact hne1
                    ·
                      have hlo783 : q 77293512 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut782)
                      apply V_pos_box_before_s1 77293512 77296864
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo783, hcut628⟩
                      · exact hne1
      ·
        have hlo629 : q 77296864 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut628)
        by_cases hcut784 : y ≤ q 77427607 scaleN
        ·
          by_cases hcut786 : y ≤ q 77360559 scaleN
          ·
            by_cases hcut788 : y ≤ q 77327035 scaleN
            ·
              by_cases hcut790 : y ≤ q 77310274 scaleN
              ·
                by_cases hcut792 : y ≤ q 77303569 scaleN
                ·
                  by_cases hcut794 : y ≤ q 77300216 scaleN
                  ·
                    apply V_pos_box_before_s1 77296864 77300216
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo629, hcut794⟩
                    · exact hne1
                  ·
                    have hlo795 : q 77300216 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut794)
                    apply V_pos_box_before_s1 77300216 77303569
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo795, hcut792⟩
                    · exact hne1
                ·
                  have hlo793 : q 77303569 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut792)
                  by_cases hcut796 : y ≤ q 77306921 scaleN
                  ·
                    apply V_pos_box_before_s1 77303569 77306921
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo793, hcut796⟩
                    · exact hne1
                  ·
                    have hlo797 : q 77306921 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut796)
                    apply V_pos_box_before_s1 77306921 77310274
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo797, hcut790⟩
                    · exact hne1
              ·
                have hlo791 : q 77310274 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut790)
                by_cases hcut798 : y ≤ q 77316979 scaleN
                ·
                  by_cases hcut800 : y ≤ q 77313626 scaleN
                  ·
                    apply V_pos_box_before_s1 77310274 77313626
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo791, hcut800⟩
                    · exact hne1
                  ·
                    have hlo801 : q 77313626 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut800)
                    apply V_pos_box_before_s1 77313626 77316979
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo801, hcut798⟩
                    · exact hne1
                ·
                  have hlo799 : q 77316979 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut798)
                  by_cases hcut802 : y ≤ q 77320331 scaleN
                  ·
                    apply V_pos_box_before_s1 77316979 77320331
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo799, hcut802⟩
                    · exact hne1
                  ·
                    have hlo803 : q 77320331 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut802)
                    by_cases hcut804 : y ≤ q 77323683 scaleN
                    ·
                      apply V_pos_box_before_s1 77320331 77323683
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo803, hcut804⟩
                      · exact hne1
                    ·
                      have hlo805 : q 77323683 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut804)
                      apply V_pos_box_before_s1 77323683 77327035
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo805, hcut788⟩
                      · exact hne1
            ·
              have hlo789 : q 77327035 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut788)
              by_cases hcut806 : y ≤ q 77343798 scaleN
              ·
                by_cases hcut808 : y ≤ q 77333740 scaleN
                ·
                  by_cases hcut810 : y ≤ q 77330388 scaleN
                  ·
                    apply V_pos_box_before_s1 77327035 77330388
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo789, hcut810⟩
                    · exact hne1
                  ·
                    have hlo811 : q 77330388 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut810)
                    apply V_pos_box_before_s1 77330388 77333740
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo811, hcut808⟩
                    · exact hne1
                ·
                  have hlo809 : q 77333740 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut808)
                  by_cases hcut812 : y ≤ q 77337093 scaleN
                  ·
                    apply V_pos_box_before_s1 77333740 77337093
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo809, hcut812⟩
                    · exact hne1
                  ·
                    have hlo813 : q 77337093 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut812)
                    by_cases hcut814 : y ≤ q 77340445 scaleN
                    ·
                      apply V_pos_box_before_s1 77337093 77340445
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo813, hcut814⟩
                      · exact hne1
                    ·
                      have hlo815 : q 77340445 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut814)
                      apply V_pos_box_before_s1 77340445 77343798
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo815, hcut806⟩
                      · exact hne1
              ·
                have hlo807 : q 77343798 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut806)
                by_cases hcut816 : y ≤ q 77350502 scaleN
                ·
                  by_cases hcut818 : y ≤ q 77347150 scaleN
                  ·
                    apply V_pos_box_before_s1 77343798 77347150
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo807, hcut818⟩
                    · exact hne1
                  ·
                    have hlo819 : q 77347150 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut818)
                    apply V_pos_box_before_s1 77347150 77350502
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo819, hcut816⟩
                    · exact hne1
                ·
                  have hlo817 : q 77350502 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut816)
                  by_cases hcut820 : y ≤ q 77353854 scaleN
                  ·
                    apply V_pos_box_before_s1 77350502 77353854
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo817, hcut820⟩
                    · exact hne1
                  ·
                    have hlo821 : q 77353854 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut820)
                    by_cases hcut822 : y ≤ q 77357207 scaleN
                    ·
                      apply V_pos_box_before_s1 77353854 77357207
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo821, hcut822⟩
                      · exact hne1
                    ·
                      have hlo823 : q 77357207 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut822)
                      apply V_pos_box_before_s1 77357207 77360559
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo823, hcut786⟩
                      · exact hne1
          ·
            have hlo787 : q 77360559 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut786)
            by_cases hcut824 : y ≤ q 77394083 scaleN
            ·
              by_cases hcut826 : y ≤ q 77377321 scaleN
              ·
                by_cases hcut828 : y ≤ q 77367264 scaleN
                ·
                  by_cases hcut830 : y ≤ q 77363912 scaleN
                  ·
                    apply V_pos_box_before_s1 77360559 77363912
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo787, hcut830⟩
                    · exact hne1
                  ·
                    have hlo831 : q 77363912 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut830)
                    apply V_pos_box_before_s1 77363912 77367264
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo831, hcut828⟩
                    · exact hne1
                ·
                  have hlo829 : q 77367264 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut828)
                  by_cases hcut832 : y ≤ q 77370617 scaleN
                  ·
                    apply V_pos_box_before_s1 77367264 77370617
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo829, hcut832⟩
                    · exact hne1
                  ·
                    have hlo833 : q 77370617 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut832)
                    by_cases hcut834 : y ≤ q 77373969 scaleN
                    ·
                      apply V_pos_box_before_s1 77370617 77373969
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo833, hcut834⟩
                      · exact hne1
                    ·
                      have hlo835 : q 77373969 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut834)
                      apply V_pos_box_before_s1 77373969 77377321
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo835, hcut826⟩
                      · exact hne1
              ·
                have hlo827 : q 77377321 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut826)
                by_cases hcut836 : y ≤ q 77384026 scaleN
                ·
                  by_cases hcut838 : y ≤ q 77380673 scaleN
                  ·
                    apply V_pos_box_before_s1 77377321 77380673
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo827, hcut838⟩
                    · exact hne1
                  ·
                    have hlo839 : q 77380673 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut838)
                    apply V_pos_box_before_s1 77380673 77384026
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo839, hcut836⟩
                    · exact hne1
                ·
                  have hlo837 : q 77384026 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut836)
                  by_cases hcut840 : y ≤ q 77387378 scaleN
                  ·
                    apply V_pos_box_before_s1 77384026 77387378
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo837, hcut840⟩
                    · exact hne1
                  ·
                    have hlo841 : q 77387378 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut840)
                    by_cases hcut842 : y ≤ q 77390731 scaleN
                    ·
                      apply V_pos_box_before_s1 77387378 77390731
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo841, hcut842⟩
                      · exact hne1
                    ·
                      have hlo843 : q 77390731 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut842)
                      apply V_pos_box_before_s1 77390731 77394083
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo843, hcut824⟩
                      · exact hne1
            ·
              have hlo825 : q 77394083 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut824)
              by_cases hcut844 : y ≤ q 77410845 scaleN
              ·
                by_cases hcut846 : y ≤ q 77400788 scaleN
                ·
                  by_cases hcut848 : y ≤ q 77397436 scaleN
                  ·
                    apply V_pos_box_before_s1 77394083 77397436
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo825, hcut848⟩
                    · exact hne1
                  ·
                    have hlo849 : q 77397436 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut848)
                    apply V_pos_box_before_s1 77397436 77400788
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo849, hcut846⟩
                    · exact hne1
                ·
                  have hlo847 : q 77400788 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut846)
                  by_cases hcut850 : y ≤ q 77404140 scaleN
                  ·
                    apply V_pos_box_before_s1 77400788 77404140
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo847, hcut850⟩
                    · exact hne1
                  ·
                    have hlo851 : q 77404140 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut850)
                    by_cases hcut852 : y ≤ q 77407492 scaleN
                    ·
                      apply V_pos_box_before_s1 77404140 77407492
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo851, hcut852⟩
                      · exact hne1
                    ·
                      have hlo853 : q 77407492 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut852)
                      apply V_pos_box_before_s1 77407492 77410845
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo853, hcut844⟩
                      · exact hne1
              ·
                have hlo845 : q 77410845 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut844)
                by_cases hcut854 : y ≤ q 77417550 scaleN
                ·
                  by_cases hcut856 : y ≤ q 77414197 scaleN
                  ·
                    apply V_pos_box_before_s1 77410845 77414197
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo845, hcut856⟩
                    · exact hne1
                  ·
                    have hlo857 : q 77414197 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut856)
                    apply V_pos_box_before_s1 77414197 77417550
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo857, hcut854⟩
                    · exact hne1
                ·
                  have hlo855 : q 77417550 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut854)
                  by_cases hcut858 : y ≤ q 77420902 scaleN
                  ·
                    apply V_pos_box_before_s1 77417550 77420902
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo855, hcut858⟩
                    · exact hne1
                  ·
                    have hlo859 : q 77420902 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut858)
                    by_cases hcut860 : y ≤ q 77424255 scaleN
                    ·
                      apply V_pos_box_before_s1 77420902 77424255
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo859, hcut860⟩
                      · exact hne1
                    ·
                      have hlo861 : q 77424255 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut860)
                      apply V_pos_box_before_s1 77424255 77427607
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo861, hcut784⟩
                      · exact hne1
        ·
          have hlo785 : q 77427607 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut784)
          by_cases hcut862 : y ≤ q 77538234 scaleN
          ·
            by_cases hcut864 : y ≤ q 77471187 scaleN
            ·
              by_cases hcut866 : y ≤ q 77441016 scaleN
              ·
                by_cases hcut868 : y ≤ q 77434311 scaleN
                ·
                  by_cases hcut870 : y ≤ q 77430959 scaleN
                  ·
                    apply V_pos_box_before_s1 77427607 77430959
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo785, hcut870⟩
                    · exact hne1
                  ·
                    have hlo871 : q 77430959 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut870)
                    apply V_pos_box_before_s1 77430959 77434311
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo871, hcut868⟩
                    · exact hne1
                ·
                  have hlo869 : q 77434311 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut868)
                  by_cases hcut872 : y ≤ q 77437664 scaleN
                  ·
                    apply V_pos_box_before_s1 77434311 77437664
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo869, hcut872⟩
                    · exact hne1
                  ·
                    have hlo873 : q 77437664 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut872)
                    apply V_pos_box_before_s1 77437664 77441016
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo873, hcut866⟩
                    · exact hne1
              ·
                have hlo867 : q 77441016 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut866)
                by_cases hcut874 : y ≤ q 77451074 scaleN
                ·
                  by_cases hcut876 : y ≤ q 77444369 scaleN
                  ·
                    apply V_pos_box_before_s1 77441016 77444369
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo867, hcut876⟩
                    · exact hne1
                  ·
                    have hlo877 : q 77444369 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut876)
                    apply V_pos_box_before_s1 77444369 77451074
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo877, hcut874⟩
                    · exact hne1
                ·
                  have hlo875 : q 77451074 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut874)
                  by_cases hcut878 : y ≤ q 77457778 scaleN
                  ·
                    apply V_pos_box_before_s1 77451074 77457778
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo875, hcut878⟩
                    · exact hne1
                  ·
                    have hlo879 : q 77457778 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut878)
                    by_cases hcut880 : y ≤ q 77464483 scaleN
                    ·
                      apply V_pos_box_before_s1 77457778 77464483
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo879, hcut880⟩
                      · exact hne1
                    ·
                      have hlo881 : q 77464483 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut880)
                      apply V_pos_box_before_s1 77464483 77471187
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo881, hcut864⟩
                      · exact hne1
            ·
              have hlo865 : q 77471187 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut864)
              by_cases hcut882 : y ≤ q 77504711 scaleN
              ·
                by_cases hcut884 : y ≤ q 77484596 scaleN
                ·
                  by_cases hcut886 : y ≤ q 77477892 scaleN
                  ·
                    apply V_pos_box_before_s1 77471187 77477892
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo865, hcut886⟩
                    · exact hne1
                  ·
                    have hlo887 : q 77477892 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut886)
                    apply V_pos_box_before_s1 77477892 77484596
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo887, hcut884⟩
                    · exact hne1
                ·
                  have hlo885 : q 77484596 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut884)
                  by_cases hcut888 : y ≤ q 77491301 scaleN
                  ·
                    apply V_pos_box_before_s1 77484596 77491301
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo885, hcut888⟩
                    · exact hne1
                  ·
                    have hlo889 : q 77491301 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut888)
                    by_cases hcut890 : y ≤ q 77498006 scaleN
                    ·
                      apply V_pos_box_before_s1 77491301 77498006
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo889, hcut890⟩
                      · exact hne1
                    ·
                      have hlo891 : q 77498006 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut890)
                      apply V_pos_box_before_s1 77498006 77504711
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo891, hcut882⟩
                      · exact hne1
              ·
                have hlo883 : q 77504711 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut882)
                by_cases hcut892 : y ≤ q 77518120 scaleN
                ·
                  by_cases hcut894 : y ≤ q 77511415 scaleN
                  ·
                    apply V_pos_box_before_s1 77504711 77511415
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo883, hcut894⟩
                    · exact hne1
                  ·
                    have hlo895 : q 77511415 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut894)
                    apply V_pos_box_before_s1 77511415 77518120
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo895, hcut892⟩
                    · exact hne1
                ·
                  have hlo893 : q 77518120 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut892)
                  by_cases hcut896 : y ≤ q 77524825 scaleN
                  ·
                    apply V_pos_box_before_s1 77518120 77524825
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo893, hcut896⟩
                    · exact hne1
                  ·
                    have hlo897 : q 77524825 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut896)
                    by_cases hcut898 : y ≤ q 77531530 scaleN
                    ·
                      apply V_pos_box_before_s1 77524825 77531530
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo897, hcut898⟩
                      · exact hne1
                    ·
                      have hlo899 : q 77531530 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut898)
                      apply V_pos_box_before_s1 77531530 77538234
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo899, hcut862⟩
                      · exact hne1
          ·
            have hlo863 : q 77538234 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut862)
            by_cases hcut900 : y ≤ q 77605282 scaleN
            ·
              by_cases hcut902 : y ≤ q 77571758 scaleN
              ·
                by_cases hcut904 : y ≤ q 77551644 scaleN
                ·
                  by_cases hcut906 : y ≤ q 77544939 scaleN
                  ·
                    apply V_pos_box_before_s1 77538234 77544939
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo863, hcut906⟩
                    · exact hne1
                  ·
                    have hlo907 : q 77544939 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut906)
                    apply V_pos_box_before_s1 77544939 77551644
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo907, hcut904⟩
                    · exact hne1
                ·
                  have hlo905 : q 77551644 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut904)
                  by_cases hcut908 : y ≤ q 77558349 scaleN
                  ·
                    apply V_pos_box_before_s1 77551644 77558349
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo905, hcut908⟩
                    · exact hne1
                  ·
                    have hlo909 : q 77558349 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut908)
                    by_cases hcut910 : y ≤ q 77565053 scaleN
                    ·
                      apply V_pos_box_before_s1 77558349 77565053
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo909, hcut910⟩
                      · exact hne1
                    ·
                      have hlo911 : q 77565053 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut910)
                      apply V_pos_box_before_s1 77565053 77571758
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo911, hcut902⟩
                      · exact hne1
              ·
                have hlo903 : q 77571758 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut902)
                by_cases hcut912 : y ≤ q 77585168 scaleN
                ·
                  by_cases hcut914 : y ≤ q 77578463 scaleN
                  ·
                    apply V_pos_box_before_s1 77571758 77578463
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo903, hcut914⟩
                    · exact hne1
                  ·
                    have hlo915 : q 77578463 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut914)
                    apply V_pos_box_before_s1 77578463 77585168
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo915, hcut912⟩
                    · exact hne1
                ·
                  have hlo913 : q 77585168 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut912)
                  by_cases hcut916 : y ≤ q 77591872 scaleN
                  ·
                    apply V_pos_box_before_s1 77585168 77591872
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo913, hcut916⟩
                    · exact hne1
                  ·
                    have hlo917 : q 77591872 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut916)
                    by_cases hcut918 : y ≤ q 77598577 scaleN
                    ·
                      apply V_pos_box_before_s1 77591872 77598577
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo917, hcut918⟩
                      · exact hne1
                    ·
                      have hlo919 : q 77598577 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut918)
                      apply V_pos_box_before_s1 77598577 77605282
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo919, hcut900⟩
                      · exact hne1
            ·
              have hlo901 : q 77605282 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut900)
              by_cases hcut920 : y ≤ q 77638806 scaleN
              ·
                by_cases hcut922 : y ≤ q 77618691 scaleN
                ·
                  by_cases hcut924 : y ≤ q 77611987 scaleN
                  ·
                    apply V_pos_box_before_s1 77605282 77611987
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo901, hcut924⟩
                    · exact hne1
                  ·
                    have hlo925 : q 77611987 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut924)
                    apply V_pos_box_before_s1 77611987 77618691
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo925, hcut922⟩
                    · exact hne1
                ·
                  have hlo923 : q 77618691 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut922)
                  by_cases hcut926 : y ≤ q 77625396 scaleN
                  ·
                    apply V_pos_box_before_s1 77618691 77625396
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo923, hcut926⟩
                    · exact hne1
                  ·
                    have hlo927 : q 77625396 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut926)
                    by_cases hcut928 : y ≤ q 77632101 scaleN
                    ·
                      apply V_pos_box_before_s1 77625396 77632101
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo927, hcut928⟩
                      · exact hne1
                    ·
                      have hlo929 : q 77632101 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut928)
                      apply V_pos_box_before_s1 77632101 77638806
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo929, hcut920⟩
                      · exact hne1
              ·
                have hlo921 : q 77638806 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut920)
                by_cases hcut930 : y ≤ q 77652215 scaleN
                ·
                  by_cases hcut932 : y ≤ q 77645510 scaleN
                  ·
                    apply V_pos_box_before_s1 77638806 77645510
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo921, hcut932⟩
                    · exact hne1
                  ·
                    have hlo933 : q 77645510 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut932)
                    apply V_pos_box_before_s1 77645510 77652215
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo933, hcut930⟩
                    · exact hne1
                ·
                  have hlo931 : q 77652215 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut930)
                  by_cases hcut934 : y ≤ q 77658920 scaleN
                  ·
                    apply V_pos_box_before_s1 77652215 77658920
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo931, hcut934⟩
                    · exact hne1
                  ·
                    have hlo935 : q 77658920 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut934)
                    by_cases hcut936 : y ≤ q 77665625 scaleN
                    ·
                      apply V_pos_box_before_s1 77658920 77665625
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo935, hcut936⟩
                      · exact hne1
                    ·
                      have hlo937 : q 77665625 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut936)
                      apply V_pos_box_before_s1 77665625 77672329
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo937, hcut626⟩
                      · exact hne1
    ·
      have hlo627 : q 77672329 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut626)
      by_cases hcut938 : y ≤ q 78577465 scaleN
      ·
        by_cases hcut940 : y ≤ q 77974040 scaleN
        ·
          by_cases hcut942 : y ≤ q 77799718 scaleN
          ·
            by_cases hcut944 : y ≤ q 77732671 scaleN
            ·
              by_cases hcut946 : y ≤ q 77699147 scaleN
              ·
                by_cases hcut948 : y ≤ q 77685738 scaleN
                ·
                  by_cases hcut950 : y ≤ q 77679034 scaleN
                  ·
                    apply V_pos_box_before_s1 77672329 77679034
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo627, hcut950⟩
                    · exact hne1
                  ·
                    have hlo951 : q 77679034 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut950)
                    apply V_pos_box_before_s1 77679034 77685738
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo951, hcut948⟩
                    · exact hne1
                ·
                  have hlo949 : q 77685738 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut948)
                  by_cases hcut952 : y ≤ q 77692443 scaleN
                  ·
                    apply V_pos_box_before_s1 77685738 77692443
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo949, hcut952⟩
                    · exact hne1
                  ·
                    have hlo953 : q 77692443 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut952)
                    apply V_pos_box_before_s1 77692443 77699147
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo953, hcut946⟩
                    · exact hne1
              ·
                have hlo947 : q 77699147 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut946)
                by_cases hcut954 : y ≤ q 77712557 scaleN
                ·
                  by_cases hcut956 : y ≤ q 77705852 scaleN
                  ·
                    apply V_pos_box_before_s1 77699147 77705852
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo947, hcut956⟩
                    · exact hne1
                  ·
                    have hlo957 : q 77705852 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut956)
                    apply V_pos_box_before_s1 77705852 77712557
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo957, hcut954⟩
                    · exact hne1
                ·
                  have hlo955 : q 77712557 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut954)
                  by_cases hcut958 : y ≤ q 77719262 scaleN
                  ·
                    apply V_pos_box_before_s1 77712557 77719262
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo955, hcut958⟩
                    · exact hne1
                  ·
                    have hlo959 : q 77719262 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut958)
                    by_cases hcut960 : y ≤ q 77725966 scaleN
                    ·
                      apply V_pos_box_before_s1 77719262 77725966
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo959, hcut960⟩
                      · exact hne1
                    ·
                      have hlo961 : q 77725966 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut960)
                      apply V_pos_box_before_s1 77725966 77732671
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo961, hcut944⟩
                      · exact hne1
            ·
              have hlo945 : q 77732671 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut944)
              by_cases hcut962 : y ≤ q 77766195 scaleN
              ·
                by_cases hcut964 : y ≤ q 77746081 scaleN
                ·
                  by_cases hcut966 : y ≤ q 77739376 scaleN
                  ·
                    apply V_pos_box_before_s1 77732671 77739376
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo945, hcut966⟩
                    · exact hne1
                  ·
                    have hlo967 : q 77739376 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut966)
                    apply V_pos_box_before_s1 77739376 77746081
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo967, hcut964⟩
                    · exact hne1
                ·
                  have hlo965 : q 77746081 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut964)
                  by_cases hcut968 : y ≤ q 77752785 scaleN
                  ·
                    apply V_pos_box_before_s1 77746081 77752785
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo965, hcut968⟩
                    · exact hne1
                  ·
                    have hlo969 : q 77752785 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut968)
                    by_cases hcut970 : y ≤ q 77759490 scaleN
                    ·
                      apply V_pos_box_before_s1 77752785 77759490
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo969, hcut970⟩
                      · exact hne1
                    ·
                      have hlo971 : q 77759490 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut970)
                      apply V_pos_box_before_s1 77759490 77766195
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo971, hcut962⟩
                      · exact hne1
              ·
                have hlo963 : q 77766195 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut962)
                by_cases hcut972 : y ≤ q 77779604 scaleN
                ·
                  by_cases hcut974 : y ≤ q 77772900 scaleN
                  ·
                    apply V_pos_box_before_s1 77766195 77772900
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo963, hcut974⟩
                    · exact hne1
                  ·
                    have hlo975 : q 77772900 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut974)
                    apply V_pos_box_before_s1 77772900 77779604
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo975, hcut972⟩
                    · exact hne1
                ·
                  have hlo973 : q 77779604 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut972)
                  by_cases hcut976 : y ≤ q 77786309 scaleN
                  ·
                    apply V_pos_box_before_s1 77779604 77786309
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo973, hcut976⟩
                    · exact hne1
                  ·
                    have hlo977 : q 77786309 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut976)
                    by_cases hcut978 : y ≤ q 77793013 scaleN
                    ·
                      apply V_pos_box_before_s1 77786309 77793013
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo977, hcut978⟩
                      · exact hne1
                    ·
                      have hlo979 : q 77793013 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut978)
                      apply V_pos_box_before_s1 77793013 77799718
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo979, hcut942⟩
                      · exact hne1
          ·
            have hlo943 : q 77799718 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut942)
            by_cases hcut980 : y ≤ q 77866765 scaleN
            ·
              by_cases hcut982 : y ≤ q 77833241 scaleN
              ·
                by_cases hcut984 : y ≤ q 77813127 scaleN
                ·
                  by_cases hcut986 : y ≤ q 77806422 scaleN
                  ·
                    apply V_pos_box_before_s1 77799718 77806422
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo943, hcut986⟩
                    · exact hne1
                  ·
                    have hlo987 : q 77806422 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut986)
                    apply V_pos_box_before_s1 77806422 77813127
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo987, hcut984⟩
                    · exact hne1
                ·
                  have hlo985 : q 77813127 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut984)
                  by_cases hcut988 : y ≤ q 77819832 scaleN
                  ·
                    apply V_pos_box_before_s1 77813127 77819832
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo985, hcut988⟩
                    · exact hne1
                  ·
                    have hlo989 : q 77819832 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut988)
                    by_cases hcut990 : y ≤ q 77826537 scaleN
                    ·
                      apply V_pos_box_before_s1 77819832 77826537
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo989, hcut990⟩
                      · exact hne1
                    ·
                      have hlo991 : q 77826537 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut990)
                      apply V_pos_box_before_s1 77826537 77833241
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo991, hcut982⟩
                      · exact hne1
              ·
                have hlo983 : q 77833241 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut982)
                by_cases hcut992 : y ≤ q 77846651 scaleN
                ·
                  by_cases hcut994 : y ≤ q 77839946 scaleN
                  ·
                    apply V_pos_box_before_s1 77833241 77839946
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo983, hcut994⟩
                    · exact hne1
                  ·
                    have hlo995 : q 77839946 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut994)
                    apply V_pos_box_before_s1 77839946 77846651
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo995, hcut992⟩
                    · exact hne1
                ·
                  have hlo993 : q 77846651 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut992)
                  by_cases hcut996 : y ≤ q 77853356 scaleN
                  ·
                    apply V_pos_box_before_s1 77846651 77853356
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo993, hcut996⟩
                    · exact hne1
                  ·
                    have hlo997 : q 77853356 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut996)
                    by_cases hcut998 : y ≤ q 77860060 scaleN
                    ·
                      apply V_pos_box_before_s1 77853356 77860060
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo997, hcut998⟩
                      · exact hne1
                    ·
                      have hlo999 : q 77860060 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut998)
                      apply V_pos_box_before_s1 77860060 77866765
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo999, hcut980⟩
                      · exact hne1
            ·
              have hlo981 : q 77866765 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut980)
              by_cases hcut1000 : y ≤ q 77906993 scaleN
              ·
                by_cases hcut1002 : y ≤ q 77880175 scaleN
                ·
                  by_cases hcut1004 : y ≤ q 77873470 scaleN
                  ·
                    apply V_pos_box_before_s1 77866765 77873470
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo981, hcut1004⟩
                    · exact hne1
                  ·
                    have hlo1005 : q 77873470 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1004)
                    apply V_pos_box_before_s1 77873470 77880175
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1005, hcut1002⟩
                    · exact hne1
                ·
                  have hlo1003 : q 77880175 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1002)
                  by_cases hcut1006 : y ≤ q 77886879 scaleN
                  ·
                    apply V_pos_box_before_s1 77880175 77886879
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1003, hcut1006⟩
                    · exact hne1
                  ·
                    have hlo1007 : q 77886879 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1006)
                    by_cases hcut1008 : y ≤ q 77893584 scaleN
                    ·
                      apply V_pos_box_before_s1 77886879 77893584
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1007, hcut1008⟩
                      · exact hne1
                    ·
                      have hlo1009 : q 77893584 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1008)
                      apply V_pos_box_before_s1 77893584 77906993
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1009, hcut1000⟩
                      · exact hne1
              ·
                have hlo1001 : q 77906993 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1000)
                by_cases hcut1010 : y ≤ q 77933812 scaleN
                ·
                  by_cases hcut1012 : y ≤ q 77920402 scaleN
                  ·
                    apply V_pos_box_before_s1 77906993 77920402
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1001, hcut1012⟩
                    · exact hne1
                  ·
                    have hlo1013 : q 77920402 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1012)
                    apply V_pos_box_before_s1 77920402 77933812
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1013, hcut1010⟩
                    · exact hne1
                ·
                  have hlo1011 : q 77933812 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1010)
                  by_cases hcut1014 : y ≤ q 77947221 scaleN
                  ·
                    apply V_pos_box_before_s1 77933812 77947221
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1011, hcut1014⟩
                    · exact hne1
                  ·
                    have hlo1015 : q 77947221 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1014)
                    by_cases hcut1016 : y ≤ q 77960631 scaleN
                    ·
                      apply V_pos_box_before_s1 77947221 77960631
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1015, hcut1016⟩
                      · exact hne1
                    ·
                      have hlo1017 : q 77960631 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1016)
                      apply V_pos_box_before_s1 77960631 77974040
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1017, hcut940⟩
                      · exact hne1
        ·
          have hlo941 : q 77974040 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut940)
          by_cases hcut1018 : y ≤ q 78228820 scaleN
          ·
            by_cases hcut1020 : y ≤ q 78094726 scaleN
            ·
              by_cases hcut1022 : y ≤ q 78027678 scaleN
              ·
                by_cases hcut1024 : y ≤ q 78000859 scaleN
                ·
                  by_cases hcut1026 : y ≤ q 77987450 scaleN
                  ·
                    apply V_pos_box_before_s1 77974040 77987450
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo941, hcut1026⟩
                    · exact hne1
                  ·
                    have hlo1027 : q 77987450 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1026)
                    apply V_pos_box_before_s1 77987450 78000859
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1027, hcut1024⟩
                    · exact hne1
                ·
                  have hlo1025 : q 78000859 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1024)
                  by_cases hcut1028 : y ≤ q 78014269 scaleN
                  ·
                    apply V_pos_box_before_s1 78000859 78014269
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1025, hcut1028⟩
                    · exact hne1
                  ·
                    have hlo1029 : q 78014269 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1028)
                    apply V_pos_box_before_s1 78014269 78027678
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1029, hcut1022⟩
                    · exact hne1
              ·
                have hlo1023 : q 78027678 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1022)
                by_cases hcut1030 : y ≤ q 78054497 scaleN
                ·
                  by_cases hcut1032 : y ≤ q 78041088 scaleN
                  ·
                    apply V_pos_box_before_s1 78027678 78041088
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1023, hcut1032⟩
                    · exact hne1
                  ·
                    have hlo1033 : q 78041088 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1032)
                    apply V_pos_box_before_s1 78041088 78054497
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1033, hcut1030⟩
                    · exact hne1
                ·
                  have hlo1031 : q 78054497 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1030)
                  by_cases hcut1034 : y ≤ q 78067907 scaleN
                  ·
                    apply V_pos_box_before_s1 78054497 78067907
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1031, hcut1034⟩
                    · exact hne1
                  ·
                    have hlo1035 : q 78067907 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1034)
                    by_cases hcut1036 : y ≤ q 78081316 scaleN
                    ·
                      apply V_pos_box_before_s1 78067907 78081316
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1035, hcut1036⟩
                      · exact hne1
                    ·
                      have hlo1037 : q 78081316 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1036)
                      apply V_pos_box_before_s1 78081316 78094726
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1037, hcut1020⟩
                      · exact hne1
            ·
              have hlo1021 : q 78094726 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1020)
              by_cases hcut1038 : y ≤ q 78161772 scaleN
              ·
                by_cases hcut1040 : y ≤ q 78121544 scaleN
                ·
                  by_cases hcut1042 : y ≤ q 78108135 scaleN
                  ·
                    apply V_pos_box_before_s1 78094726 78108135
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1021, hcut1042⟩
                    · exact hne1
                  ·
                    have hlo1043 : q 78108135 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1042)
                    apply V_pos_box_before_s1 78108135 78121544
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1043, hcut1040⟩
                    · exact hne1
                ·
                  have hlo1041 : q 78121544 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1040)
                  by_cases hcut1044 : y ≤ q 78134953 scaleN
                  ·
                    apply V_pos_box_before_s1 78121544 78134953
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1041, hcut1044⟩
                    · exact hne1
                  ·
                    have hlo1045 : q 78134953 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1044)
                    by_cases hcut1046 : y ≤ q 78148363 scaleN
                    ·
                      apply V_pos_box_before_s1 78134953 78148363
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1045, hcut1046⟩
                      · exact hne1
                    ·
                      have hlo1047 : q 78148363 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1046)
                      apply V_pos_box_before_s1 78148363 78161772
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1047, hcut1038⟩
                      · exact hne1
              ·
                have hlo1039 : q 78161772 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1038)
                by_cases hcut1048 : y ≤ q 78188591 scaleN
                ·
                  by_cases hcut1050 : y ≤ q 78175182 scaleN
                  ·
                    apply V_pos_box_before_s1 78161772 78175182
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1039, hcut1050⟩
                    · exact hne1
                  ·
                    have hlo1051 : q 78175182 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1050)
                    apply V_pos_box_before_s1 78175182 78188591
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1051, hcut1048⟩
                    · exact hne1
                ·
                  have hlo1049 : q 78188591 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1048)
                  by_cases hcut1052 : y ≤ q 78202001 scaleN
                  ·
                    apply V_pos_box_before_s1 78188591 78202001
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1049, hcut1052⟩
                    · exact hne1
                  ·
                    have hlo1053 : q 78202001 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1052)
                    by_cases hcut1054 : y ≤ q 78215410 scaleN
                    ·
                      apply V_pos_box_before_s1 78202001 78215410
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1053, hcut1054⟩
                      · exact hne1
                    ·
                      have hlo1055 : q 78215410 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1054)
                      apply V_pos_box_before_s1 78215410 78228820
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1055, hcut1018⟩
                      · exact hne1
          ·
            have hlo1019 : q 78228820 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1018)
            by_cases hcut1056 : y ≤ q 78362914 scaleN
            ·
              by_cases hcut1058 : y ≤ q 78295867 scaleN
              ·
                by_cases hcut1060 : y ≤ q 78255639 scaleN
                ·
                  by_cases hcut1062 : y ≤ q 78242229 scaleN
                  ·
                    apply V_pos_box_before_s1 78228820 78242229
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1019, hcut1062⟩
                    · exact hne1
                  ·
                    have hlo1063 : q 78242229 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1062)
                    apply V_pos_box_before_s1 78242229 78255639
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1063, hcut1060⟩
                    · exact hne1
                ·
                  have hlo1061 : q 78255639 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1060)
                  by_cases hcut1064 : y ≤ q 78269048 scaleN
                  ·
                    apply V_pos_box_before_s1 78255639 78269048
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1061, hcut1064⟩
                    · exact hne1
                  ·
                    have hlo1065 : q 78269048 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1064)
                    by_cases hcut1066 : y ≤ q 78282458 scaleN
                    ·
                      apply V_pos_box_before_s1 78269048 78282458
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1065, hcut1066⟩
                      · exact hne1
                    ·
                      have hlo1067 : q 78282458 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1066)
                      apply V_pos_box_before_s1 78282458 78295867
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1067, hcut1058⟩
                      · exact hne1
              ·
                have hlo1059 : q 78295867 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1058)
                by_cases hcut1068 : y ≤ q 78322686 scaleN
                ·
                  by_cases hcut1070 : y ≤ q 78309277 scaleN
                  ·
                    apply V_pos_box_before_s1 78295867 78309277
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1059, hcut1070⟩
                    · exact hne1
                  ·
                    have hlo1071 : q 78309277 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1070)
                    apply V_pos_box_before_s1 78309277 78322686
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1071, hcut1068⟩
                    · exact hne1
                ·
                  have hlo1069 : q 78322686 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1068)
                  by_cases hcut1072 : y ≤ q 78336095 scaleN
                  ·
                    apply V_pos_box_before_s1 78322686 78336095
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1069, hcut1072⟩
                    · exact hne1
                  ·
                    have hlo1073 : q 78336095 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1072)
                    by_cases hcut1074 : y ≤ q 78349504 scaleN
                    ·
                      apply V_pos_box_before_s1 78336095 78349504
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1073, hcut1074⟩
                      · exact hne1
                    ·
                      have hlo1075 : q 78349504 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1074)
                      apply V_pos_box_before_s1 78349504 78362914
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1075, hcut1056⟩
                      · exact hne1
            ·
              have hlo1057 : q 78362914 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1056)
              by_cases hcut1076 : y ≤ q 78443371 scaleN
              ·
                by_cases hcut1078 : y ≤ q 78389733 scaleN
                ·
                  by_cases hcut1080 : y ≤ q 78376323 scaleN
                  ·
                    apply V_pos_box_before_s1 78362914 78376323
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1057, hcut1080⟩
                    · exact hne1
                  ·
                    have hlo1081 : q 78376323 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1080)
                    apply V_pos_box_before_s1 78376323 78389733
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1081, hcut1078⟩
                    · exact hne1
                ·
                  have hlo1079 : q 78389733 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1078)
                  by_cases hcut1082 : y ≤ q 78403142 scaleN
                  ·
                    apply V_pos_box_before_s1 78389733 78403142
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1079, hcut1082⟩
                    · exact hne1
                  ·
                    have hlo1083 : q 78403142 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1082)
                    by_cases hcut1084 : y ≤ q 78416552 scaleN
                    ·
                      apply V_pos_box_before_s1 78403142 78416552
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1083, hcut1084⟩
                      · exact hne1
                    ·
                      have hlo1085 : q 78416552 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1084)
                      apply V_pos_box_before_s1 78416552 78443371
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1085, hcut1076⟩
                      · exact hne1
              ·
                have hlo1077 : q 78443371 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1076)
                by_cases hcut1086 : y ≤ q 78497009 scaleN
                ·
                  by_cases hcut1088 : y ≤ q 78470190 scaleN
                  ·
                    apply V_pos_box_before_s1 78443371 78470190
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1077, hcut1088⟩
                    · exact hne1
                  ·
                    have hlo1089 : q 78470190 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1088)
                    apply V_pos_box_before_s1 78470190 78497009
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1089, hcut1086⟩
                    · exact hne1
                ·
                  have hlo1087 : q 78497009 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1086)
                  by_cases hcut1090 : y ≤ q 78523828 scaleN
                  ·
                    apply V_pos_box_before_s1 78497009 78523828
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1087, hcut1090⟩
                    · exact hne1
                  ·
                    have hlo1091 : q 78523828 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1090)
                    by_cases hcut1092 : y ≤ q 78550646 scaleN
                    ·
                      apply V_pos_box_before_s1 78523828 78550646
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1091, hcut1092⟩
                      · exact hne1
                    ·
                      have hlo1093 : q 78550646 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1092)
                      apply V_pos_box_before_s1 78550646 78577465
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1093, hcut938⟩
                      · exact hne1
      ·
        have hlo939 : q 78577465 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut938)
        by_cases hcut1094 : y ≤ q 80240234 scaleN
        ·
          by_cases hcut1096 : y ≤ q 79087023 scaleN
          ·
            by_cases hcut1098 : y ≤ q 78818834 scaleN
            ·
              by_cases hcut1100 : y ≤ q 78684740 scaleN
              ·
                by_cases hcut1102 : y ≤ q 78631103 scaleN
                ·
                  by_cases hcut1104 : y ≤ q 78604284 scaleN
                  ·
                    apply V_pos_box_before_s1 78577465 78604284
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo939, hcut1104⟩
                    · exact hne1
                  ·
                    have hlo1105 : q 78604284 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1104)
                    apply V_pos_box_before_s1 78604284 78631103
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1105, hcut1102⟩
                    · exact hne1
                ·
                  have hlo1103 : q 78631103 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1102)
                  by_cases hcut1106 : y ≤ q 78657921 scaleN
                  ·
                    apply V_pos_box_before_s1 78631103 78657921
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1103, hcut1106⟩
                    · exact hne1
                  ·
                    have hlo1107 : q 78657921 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1106)
                    apply V_pos_box_before_s1 78657921 78684740
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1107, hcut1100⟩
                    · exact hne1
              ·
                have hlo1101 : q 78684740 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1100)
                by_cases hcut1108 : y ≤ q 78738378 scaleN
                ·
                  by_cases hcut1110 : y ≤ q 78711559 scaleN
                  ·
                    apply V_pos_box_before_s1 78684740 78711559
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1101, hcut1110⟩
                    · exact hne1
                  ·
                    have hlo1111 : q 78711559 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1110)
                    apply V_pos_box_before_s1 78711559 78738378
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1111, hcut1108⟩
                    · exact hne1
                ·
                  have hlo1109 : q 78738378 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1108)
                  by_cases hcut1112 : y ≤ q 78765196 scaleN
                  ·
                    apply V_pos_box_before_s1 78738378 78765196
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1109, hcut1112⟩
                    · exact hne1
                  ·
                    have hlo1113 : q 78765196 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1112)
                    by_cases hcut1114 : y ≤ q 78792015 scaleN
                    ·
                      apply V_pos_box_before_s1 78765196 78792015
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1113, hcut1114⟩
                      · exact hne1
                    ·
                      have hlo1115 : q 78792015 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1114)
                      apply V_pos_box_before_s1 78792015 78818834
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1115, hcut1098⟩
                      · exact hne1
            ·
              have hlo1099 : q 78818834 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1098)
              by_cases hcut1116 : y ≤ q 78952929 scaleN
              ·
                by_cases hcut1118 : y ≤ q 78872472 scaleN
                ·
                  by_cases hcut1120 : y ≤ q 78845653 scaleN
                  ·
                    apply V_pos_box_before_s1 78818834 78845653
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1099, hcut1120⟩
                    · exact hne1
                  ·
                    have hlo1121 : q 78845653 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1120)
                    apply V_pos_box_before_s1 78845653 78872472
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1121, hcut1118⟩
                    · exact hne1
                ·
                  have hlo1119 : q 78872472 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1118)
                  by_cases hcut1122 : y ≤ q 78899291 scaleN
                  ·
                    apply V_pos_box_before_s1 78872472 78899291
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1119, hcut1122⟩
                    · exact hne1
                  ·
                    have hlo1123 : q 78899291 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1122)
                    by_cases hcut1124 : y ≤ q 78926110 scaleN
                    ·
                      apply V_pos_box_before_s1 78899291 78926110
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1123, hcut1124⟩
                      · exact hne1
                    ·
                      have hlo1125 : q 78926110 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1124)
                      apply V_pos_box_before_s1 78926110 78952929
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1125, hcut1116⟩
                      · exact hne1
              ·
                have hlo1117 : q 78952929 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1116)
                by_cases hcut1126 : y ≤ q 79006566 scaleN
                ·
                  by_cases hcut1128 : y ≤ q 78979747 scaleN
                  ·
                    apply V_pos_box_before_s1 78952929 78979747
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1117, hcut1128⟩
                    · exact hne1
                  ·
                    have hlo1129 : q 78979747 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1128)
                    apply V_pos_box_before_s1 78979747 79006566
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1129, hcut1126⟩
                    · exact hne1
                ·
                  have hlo1127 : q 79006566 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1126)
                  by_cases hcut1130 : y ≤ q 79033385 scaleN
                  ·
                    apply V_pos_box_before_s1 79006566 79033385
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1127, hcut1130⟩
                    · exact hne1
                  ·
                    have hlo1131 : q 79033385 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1130)
                    by_cases hcut1132 : y ≤ q 79060204 scaleN
                    ·
                      apply V_pos_box_before_s1 79033385 79060204
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1131, hcut1132⟩
                      · exact hne1
                    ·
                      have hlo1133 : q 79060204 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1132)
                      apply V_pos_box_before_s1 79060204 79087023
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1133, hcut1096⟩
                      · exact hne1
          ·
            have hlo1097 : q 79087023 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1096)
            by_cases hcut1134 : y ≤ q 79596581 scaleN
            ·
              by_cases hcut1136 : y ≤ q 79328393 scaleN
              ·
                by_cases hcut1138 : y ≤ q 79167480 scaleN
                ·
                  by_cases hcut1140 : y ≤ q 79113842 scaleN
                  ·
                    apply V_pos_box_before_s1 79087023 79113842
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1097, hcut1140⟩
                    · exact hne1
                  ·
                    have hlo1141 : q 79113842 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1140)
                    apply V_pos_box_before_s1 79113842 79167480
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1141, hcut1138⟩
                    · exact hne1
                ·
                  have hlo1139 : q 79167480 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1138)
                  by_cases hcut1142 : y ≤ q 79221117 scaleN
                  ·
                    apply V_pos_box_before_s1 79167480 79221117
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1139, hcut1142⟩
                    · exact hne1
                  ·
                    have hlo1143 : q 79221117 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1142)
                    by_cases hcut1144 : y ≤ q 79274755 scaleN
                    ·
                      apply V_pos_box_before_s1 79221117 79274755
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1143, hcut1144⟩
                      · exact hne1
                    ·
                      have hlo1145 : q 79274755 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1144)
                      apply V_pos_box_before_s1 79274755 79328393
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1145, hcut1136⟩
                      · exact hne1
              ·
                have hlo1137 : q 79328393 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1136)
                by_cases hcut1146 : y ≤ q 79435668 scaleN
                ·
                  by_cases hcut1148 : y ≤ q 79382031 scaleN
                  ·
                    apply V_pos_box_before_s1 79328393 79382031
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1137, hcut1148⟩
                    · exact hne1
                  ·
                    have hlo1149 : q 79382031 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1148)
                    apply V_pos_box_before_s1 79382031 79435668
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1149, hcut1146⟩
                    · exact hne1
                ·
                  have hlo1147 : q 79435668 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1146)
                  by_cases hcut1150 : y ≤ q 79489306 scaleN
                  ·
                    apply V_pos_box_before_s1 79435668 79489306
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1147, hcut1150⟩
                    · exact hne1
                  ·
                    have hlo1151 : q 79489306 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1150)
                    by_cases hcut1152 : y ≤ q 79542943 scaleN
                    ·
                      apply V_pos_box_before_s1 79489306 79542943
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1151, hcut1152⟩
                      · exact hne1
                    ·
                      have hlo1153 : q 79542943 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1152)
                      apply V_pos_box_before_s1 79542943 79596581
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1153, hcut1134⟩
                      · exact hne1
            ·
              have hlo1135 : q 79596581 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1134)
              by_cases hcut1154 : y ≤ q 79864769 scaleN
              ·
                by_cases hcut1156 : y ≤ q 79703856 scaleN
                ·
                  by_cases hcut1158 : y ≤ q 79650218 scaleN
                  ·
                    apply V_pos_box_before_s1 79596581 79650218
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1135, hcut1158⟩
                    · exact hne1
                  ·
                    have hlo1159 : q 79650218 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1158)
                    apply V_pos_box_before_s1 79650218 79703856
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1159, hcut1156⟩
                    · exact hne1
                ·
                  have hlo1157 : q 79703856 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1156)
                  by_cases hcut1160 : y ≤ q 79757494 scaleN
                  ·
                    apply V_pos_box_before_s1 79703856 79757494
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1157, hcut1160⟩
                    · exact hne1
                  ·
                    have hlo1161 : q 79757494 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1160)
                    by_cases hcut1162 : y ≤ q 79811132 scaleN
                    ·
                      apply V_pos_box_before_s1 79757494 79811132
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1161, hcut1162⟩
                      · exact hne1
                    ·
                      have hlo1163 : q 79811132 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1162)
                      apply V_pos_box_before_s1 79811132 79864769
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1163, hcut1154⟩
                      · exact hne1
              ·
                have hlo1155 : q 79864769 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1154)
                by_cases hcut1164 : y ≤ q 79972045 scaleN
                ·
                  by_cases hcut1166 : y ≤ q 79918407 scaleN
                  ·
                    apply V_pos_box_before_s1 79864769 79918407
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1155, hcut1166⟩
                    · exact hne1
                  ·
                    have hlo1167 : q 79918407 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1166)
                    apply V_pos_box_before_s1 79918407 79972045
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1167, hcut1164⟩
                    · exact hne1
                ·
                  have hlo1165 : q 79972045 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1164)
                  by_cases hcut1168 : y ≤ q 80025683 scaleN
                  ·
                    apply V_pos_box_before_s1 79972045 80025683
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1165, hcut1168⟩
                    · exact hne1
                  ·
                    have hlo1169 : q 80025683 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1168)
                    by_cases hcut1170 : y ≤ q 80132958 scaleN
                    ·
                      apply V_pos_box_before_s1 80025683 80132958
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1169, hcut1170⟩
                      · exact hne1
                    ·
                      have hlo1171 : q 80132958 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1170)
                      apply V_pos_box_before_s1 80132958 80240234
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1171, hcut1094⟩
                      · exact hne1
        ·
          have hlo1095 : q 80240234 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1094)
          by_cases hcut1172 : y ≤ q 83673046 scaleN
          ·
            by_cases hcut1174 : y ≤ q 81312987 scaleN
            ·
              by_cases hcut1176 : y ≤ q 80776610 scaleN
              ·
                by_cases hcut1178 : y ≤ q 80454784 scaleN
                ·
                  by_cases hcut1180 : y ≤ q 80347509 scaleN
                  ·
                    apply V_pos_box_before_s1 80240234 80347509
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1095, hcut1180⟩
                    · exact hne1
                  ·
                    have hlo1181 : q 80347509 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1180)
                    apply V_pos_box_before_s1 80347509 80454784
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1181, hcut1178⟩
                    · exact hne1
                ·
                  have hlo1179 : q 80454784 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1178)
                  by_cases hcut1182 : y ≤ q 80562059 scaleN
                  ·
                    apply V_pos_box_before_s1 80454784 80562059
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1179, hcut1182⟩
                    · exact hne1
                  ·
                    have hlo1183 : q 80562059 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1182)
                    by_cases hcut1184 : y ≤ q 80669335 scaleN
                    ·
                      apply V_pos_box_before_s1 80562059 80669335
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1183, hcut1184⟩
                      · exact hne1
                    ·
                      have hlo1185 : q 80669335 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1184)
                      apply V_pos_box_before_s1 80669335 80776610
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1185, hcut1176⟩
                      · exact hne1
              ·
                have hlo1177 : q 80776610 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1176)
                by_cases hcut1186 : y ≤ q 80991161 scaleN
                ·
                  by_cases hcut1188 : y ≤ q 80883886 scaleN
                  ·
                    apply V_pos_box_before_s1 80776610 80883886
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1177, hcut1188⟩
                    · exact hne1
                  ·
                    have hlo1189 : q 80883886 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1188)
                    apply V_pos_box_before_s1 80883886 80991161
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1189, hcut1186⟩
                    · exact hne1
                ·
                  have hlo1187 : q 80991161 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1186)
                  by_cases hcut1190 : y ≤ q 81098437 scaleN
                  ·
                    apply V_pos_box_before_s1 80991161 81098437
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1187, hcut1190⟩
                    · exact hne1
                  ·
                    have hlo1191 : q 81098437 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1190)
                    by_cases hcut1192 : y ≤ q 81205712 scaleN
                    ·
                      apply V_pos_box_before_s1 81098437 81205712
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1191, hcut1192⟩
                      · exact hne1
                    ·
                      have hlo1193 : q 81205712 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1192)
                      apply V_pos_box_before_s1 81205712 81312987
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1193, hcut1174⟩
                      · exact hne1
            ·
              have hlo1175 : q 81312987 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1174)
              by_cases hcut1194 : y ≤ q 82385741 scaleN
              ·
                by_cases hcut1196 : y ≤ q 81742089 scaleN
                ·
                  by_cases hcut1198 : y ≤ q 81527538 scaleN
                  ·
                    apply V_pos_box_before_s1 81312987 81527538
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1175, hcut1198⟩
                    · exact hne1
                  ·
                    have hlo1199 : q 81527538 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1198)
                    apply V_pos_box_before_s1 81527538 81742089
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1199, hcut1196⟩
                    · exact hne1
                ·
                  have hlo1197 : q 81742089 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1196)
                  by_cases hcut1200 : y ≤ q 81956640 scaleN
                  ·
                    apply V_pos_box_before_s1 81742089 81956640
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1197, hcut1200⟩
                    · exact hne1
                  ·
                    have hlo1201 : q 81956640 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1200)
                    by_cases hcut1202 : y ≤ q 82171190 scaleN
                    ·
                      apply V_pos_box_before_s1 81956640 82171190
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1201, hcut1202⟩
                      · exact hne1
                    ·
                      have hlo1203 : q 82171190 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1202)
                      apply V_pos_box_before_s1 82171190 82385741
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1203, hcut1194⟩
                      · exact hne1
              ·
                have hlo1195 : q 82385741 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1194)
                by_cases hcut1204 : y ≤ q 82814843 scaleN
                ·
                  by_cases hcut1206 : y ≤ q 82600292 scaleN
                  ·
                    apply V_pos_box_before_s1 82385741 82600292
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1195, hcut1206⟩
                    · exact hne1
                  ·
                    have hlo1207 : q 82600292 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1206)
                    apply V_pos_box_before_s1 82600292 82814843
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1207, hcut1204⟩
                    · exact hne1
                ·
                  have hlo1205 : q 82814843 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1204)
                  by_cases hcut1208 : y ≤ q 83029393 scaleN
                  ·
                    apply V_pos_box_before_s1 82814843 83029393
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1205, hcut1208⟩
                    · exact hne1
                  ·
                    have hlo1209 : q 83029393 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1208)
                    by_cases hcut1210 : y ≤ q 83243944 scaleN
                    ·
                      apply V_pos_box_before_s1 83029393 83243944
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1209, hcut1210⟩
                      · exact hne1
                    ·
                      have hlo1211 : q 83243944 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1210)
                      apply V_pos_box_before_s1 83243944 83673046
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1211, hcut1172⟩
                      · exact hne1
          ·
            have hlo1173 : q 83673046 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1172)
            by_cases hcut1212 : y ≤ q 89680468 scaleN
            ·
              by_cases hcut1214 : y ≤ q 85818554 scaleN
              ·
                by_cases hcut1216 : y ≤ q 84531250 scaleN
                ·
                  by_cases hcut1218 : y ≤ q 84102148 scaleN
                  ·
                    apply V_pos_box_before_s1 83673046 84102148
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1173, hcut1218⟩
                    · exact hne1
                  ·
                    have hlo1219 : q 84102148 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1218)
                    apply V_pos_box_before_s1 84102148 84531250
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1219, hcut1216⟩
                    · exact hne1
                ·
                  have hlo1217 : q 84531250 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1216)
                  by_cases hcut1220 : y ≤ q 84960351 scaleN
                  ·
                    apply V_pos_box_before_s1 84531250 84960351
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1217, hcut1220⟩
                    · exact hne1
                  ·
                    have hlo1221 : q 84960351 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1220)
                    by_cases hcut1222 : y ≤ q 85389453 scaleN
                    ·
                      apply V_pos_box_before_s1 84960351 85389453
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1221, hcut1222⟩
                      · exact hne1
                    ·
                      have hlo1223 : q 85389453 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1222)
                      apply V_pos_box_before_s1 85389453 85818554
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1223, hcut1214⟩
                      · exact hne1
              ·
                have hlo1215 : q 85818554 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1214)
                by_cases hcut1224 : y ≤ q 87105859 scaleN
                ·
                  by_cases hcut1226 : y ≤ q 86247656 scaleN
                  ·
                    apply V_pos_box_before_s1 85818554 86247656
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1215, hcut1226⟩
                    · exact hne1
                  ·
                    have hlo1227 : q 86247656 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1226)
                    apply V_pos_box_before_s1 86247656 87105859
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1227, hcut1224⟩
                    · exact hne1
                ·
                  have hlo1225 : q 87105859 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1224)
                  by_cases hcut1228 : y ≤ q 87964062 scaleN
                  ·
                    apply V_pos_box_before_s1 87105859 87964062
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1225, hcut1228⟩
                    · exact hne1
                  ·
                    have hlo1229 : q 87964062 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1228)
                    by_cases hcut1230 : y ≤ q 88822265 scaleN
                    ·
                      apply V_pos_box_before_s1 87964062 88822265
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1229, hcut1230⟩
                      · exact hne1
                    ·
                      have hlo1231 : q 88822265 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1230)
                      apply V_pos_box_before_s1 88822265 89680468
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1231, hcut1212⟩
                      · exact hne1
            ·
              have hlo1213 : q 89680468 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1212)
              by_cases hcut1232 : y ≤ q 101695312 scaleN
              ·
                by_cases hcut1234 : y ≤ q 93113281 scaleN
                ·
                  by_cases hcut1236 : y ≤ q 91396875 scaleN
                  ·
                    apply V_pos_box_before_s1 89680468 91396875
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1213, hcut1236⟩
                    · exact hne1
                  ·
                    have hlo1237 : q 91396875 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1236)
                    apply V_pos_box_before_s1 91396875 93113281
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1237, hcut1234⟩
                    · exact hne1
                ·
                  have hlo1235 : q 93113281 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1234)
                  by_cases hcut1238 : y ≤ q 94829687 scaleN
                  ·
                    apply V_pos_box_before_s1 93113281 94829687
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1235, hcut1238⟩
                    · exact hne1
                  ·
                    have hlo1239 : q 94829687 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1238)
                    by_cases hcut1240 : y ≤ q 98262500 scaleN
                    ·
                      apply V_pos_box_before_s1 94829687 98262500
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1239, hcut1240⟩
                      · exact hne1
                    ·
                      have hlo1241 : q 98262500 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1240)
                      apply V_pos_box_before_s1 98262500 101695312
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1241, hcut1232⟩
                      · exact hne1
              ·
                have hlo1233 : q 101695312 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1232)
                by_cases hcut1242 : y ≤ q 111993750 scaleN
                ·
                  by_cases hcut1244 : y ≤ q 105128125 scaleN
                  ·
                    apply V_pos_box_before_s1 101695312 105128125
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1233, hcut1244⟩
                    · exact hne1
                  ·
                    have hlo1245 : q 105128125 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1244)
                    apply V_pos_box_before_s1 105128125 111993750
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1245, hcut1242⟩
                    · exact hne1
                ·
                  have hlo1243 : q 111993750 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1242)
                  by_cases hcut1246 : y ≤ q 125725000 scaleN
                  ·
                    apply V_pos_box_before_s1 111993750 125725000
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1243, hcut1246⟩
                    · exact hne1
                  ·
                    have hlo1247 : q 125725000 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1246)
                    by_cases hcut1248 : y ≤ q 153187500 scaleN
                    ·
                      apply V_pos_box_before_s1 125725000 153187500
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1247, hcut1248⟩
                      · exact hne1
                    ·
                      have hlo1249 : q 153187500 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1248)
                      apply V_pos_box_before_s1 153187500 180650001
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · native_decide
                      · exact ⟨hlo1249, hhi0⟩
                      · exact hne1

theorem V_boxes_s1_s2
    {y : ℝ}
    (hy : y ∈ Icc s1 s2)

    (hne1 : y ≠ s1)
    (hne2 : y ≠ s2)
    :
    0 < V y := by
  have hlo0 : q 180650001 scaleN ≤ y := by
    simpa [s1_eq_q] using hy.1
  have hhi0 : y ≤ q 257053197 scaleN := by
    simpa [s2_eq_q] using hy.2
  by_cases hcut1250 : y ≤ q 252625410 scaleN
  ·
    by_cases hcut1252 : y ≤ q 252380588 scaleN
    ·
      by_cases hcut1254 : y ≤ q 251998200 scaleN
      ·
        by_cases hcut1256 : y ≤ q 251158809 scaleN
        ·
          by_cases hcut1258 : y ≤ q 249293497 scaleN
          ·
            by_cases hcut1260 : y ≤ q 245115197 scaleN
            ·
              by_cases hcut1262 : y ≤ q 228401998 scaleN
              ·
                by_cases hcut1264 : y ≤ q 218851599 scaleN
                ·
                  apply V_pos_box_s1_s2 180650001 218851599
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo0, hcut1264⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1265 : q 218851599 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1264)
                  apply V_pos_box_s1_s2 218851599 228401998
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1265, hcut1262⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1263 : q 228401998 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1262)
                by_cases hcut1266 : y ≤ q 237952398 scaleN
                ·
                  apply V_pos_box_s1_s2 228401998 237952398
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1263, hcut1266⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1267 : q 237952398 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1266)
                  by_cases hcut1268 : y ≤ q 242727597 scaleN
                  ·
                    apply V_pos_box_s1_s2 237952398 242727597
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1267, hcut1268⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1269 : q 242727597 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1268)
                    apply V_pos_box_s1_s2 242727597 245115197
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1269, hcut1260⟩
                    · exact hne1
                    · exact hne2
            ·
              have hlo1261 : q 245115197 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1260)
              by_cases hcut1270 : y ≤ q 247502797 scaleN
              ·
                by_cases hcut1272 : y ≤ q 246308997 scaleN
                ·
                  apply V_pos_box_s1_s2 245115197 246308997
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1261, hcut1272⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1273 : q 246308997 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1272)
                  apply V_pos_box_s1_s2 246308997 247502797
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1273, hcut1270⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1271 : q 247502797 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1270)
                by_cases hcut1274 : y ≤ q 248099697 scaleN
                ·
                  apply V_pos_box_s1_s2 247502797 248099697
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1271, hcut1274⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1275 : q 248099697 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1274)
                  by_cases hcut1276 : y ≤ q 248696597 scaleN
                  ·
                    apply V_pos_box_s1_s2 248099697 248696597
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1275, hcut1276⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1277 : q 248696597 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1276)
                    apply V_pos_box_s1_s2 248696597 249293497
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1277, hcut1258⟩
                    · exact hne1
                    · exact hne2
          ·
            have hlo1259 : q 249293497 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1258)
            by_cases hcut1278 : y ≤ q 250487297 scaleN
            ·
              by_cases hcut1280 : y ≤ q 249890397 scaleN
              ·
                by_cases hcut1282 : y ≤ q 249591947 scaleN
                ·
                  apply V_pos_box_s1_s2 249293497 249591947
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1259, hcut1282⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1283 : q 249591947 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1282)
                  apply V_pos_box_s1_s2 249591947 249890397
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1283, hcut1280⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1281 : q 249890397 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1280)
                by_cases hcut1284 : y ≤ q 250188847 scaleN
                ·
                  apply V_pos_box_s1_s2 249890397 250188847
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1281, hcut1284⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1285 : q 250188847 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1284)
                  by_cases hcut1286 : y ≤ q 250338072 scaleN
                  ·
                    apply V_pos_box_s1_s2 250188847 250338072
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1285, hcut1286⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1287 : q 250338072 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1286)
                    apply V_pos_box_s1_s2 250338072 250487297
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1287, hcut1278⟩
                    · exact hne1
                    · exact hne2
            ·
              have hlo1279 : q 250487297 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1278)
              by_cases hcut1288 : y ≤ q 250934972 scaleN
              ·
                by_cases hcut1290 : y ≤ q 250636522 scaleN
                ·
                  apply V_pos_box_s1_s2 250487297 250636522
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1279, hcut1290⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1291 : q 250636522 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1290)
                  by_cases hcut1292 : y ≤ q 250785747 scaleN
                  ·
                    apply V_pos_box_s1_s2 250636522 250785747
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1291, hcut1292⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1293 : q 250785747 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1292)
                    apply V_pos_box_s1_s2 250785747 250934972
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1293, hcut1288⟩
                    · exact hne1
                    · exact hne2
              ·
                have hlo1289 : q 250934972 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1288)
                by_cases hcut1294 : y ≤ q 251009584 scaleN
                ·
                  apply V_pos_box_s1_s2 250934972 251009584
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1289, hcut1294⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1295 : q 251009584 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1294)
                  by_cases hcut1296 : y ≤ q 251084197 scaleN
                  ·
                    apply V_pos_box_s1_s2 251009584 251084197
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1295, hcut1296⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1297 : q 251084197 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1296)
                    apply V_pos_box_s1_s2 251084197 251158809
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1297, hcut1256⟩
                    · exact hne1
                    · exact hne2
        ·
          have hlo1257 : q 251158809 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1256)
          by_cases hcut1298 : y ≤ q 251718403 scaleN
          ·
            by_cases hcut1300 : y ≤ q 251494565 scaleN
            ·
              by_cases hcut1302 : y ≤ q 251308034 scaleN
              ·
                by_cases hcut1304 : y ≤ q 251233422 scaleN
                ·
                  apply V_pos_box_s1_s2 251158809 251233422
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1257, hcut1304⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1305 : q 251233422 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1304)
                  apply V_pos_box_s1_s2 251233422 251308034
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1305, hcut1302⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1303 : q 251308034 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1302)
                by_cases hcut1306 : y ≤ q 251382647 scaleN
                ·
                  apply V_pos_box_s1_s2 251308034 251382647
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1303, hcut1306⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1307 : q 251382647 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1306)
                  by_cases hcut1308 : y ≤ q 251457259 scaleN
                  ·
                    apply V_pos_box_s1_s2 251382647 251457259
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1307, hcut1308⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1309 : q 251457259 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1308)
                    apply V_pos_box_s1_s2 251457259 251494565
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1309, hcut1300⟩
                    · exact hne1
                    · exact hne2
            ·
              have hlo1301 : q 251494565 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1300)
              by_cases hcut1310 : y ≤ q 251606484 scaleN
              ·
                by_cases hcut1312 : y ≤ q 251531872 scaleN
                ·
                  apply V_pos_box_s1_s2 251494565 251531872
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1301, hcut1312⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1313 : q 251531872 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1312)
                  by_cases hcut1314 : y ≤ q 251569178 scaleN
                  ·
                    apply V_pos_box_s1_s2 251531872 251569178
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1313, hcut1314⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1315 : q 251569178 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1314)
                    apply V_pos_box_s1_s2 251569178 251606484
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1315, hcut1310⟩
                    · exact hne1
                    · exact hne2
              ·
                have hlo1311 : q 251606484 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1310)
                by_cases hcut1316 : y ≤ q 251643790 scaleN
                ·
                  apply V_pos_box_s1_s2 251606484 251643790
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1311, hcut1316⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1317 : q 251643790 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1316)
                  by_cases hcut1318 : y ≤ q 251681097 scaleN
                  ·
                    apply V_pos_box_s1_s2 251643790 251681097
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1317, hcut1318⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1319 : q 251681097 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1318)
                    apply V_pos_box_s1_s2 251681097 251718403
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1319, hcut1298⟩
                    · exact hne1
                    · exact hne2
          ·
            have hlo1299 : q 251718403 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1298)
            by_cases hcut1320 : y ≤ q 251886281 scaleN
            ·
              by_cases hcut1322 : y ≤ q 251793015 scaleN
              ·
                by_cases hcut1324 : y ≤ q 251755709 scaleN
                ·
                  apply V_pos_box_s1_s2 251718403 251755709
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1299, hcut1324⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1325 : q 251755709 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1324)
                  apply V_pos_box_s1_s2 251755709 251793015
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1325, hcut1322⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1323 : q 251793015 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1322)
                by_cases hcut1326 : y ≤ q 251830322 scaleN
                ·
                  apply V_pos_box_s1_s2 251793015 251830322
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1323, hcut1326⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1327 : q 251830322 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1326)
                  by_cases hcut1328 : y ≤ q 251867628 scaleN
                  ·
                    apply V_pos_box_s1_s2 251830322 251867628
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1327, hcut1328⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1329 : q 251867628 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1328)
                    apply V_pos_box_s1_s2 251867628 251886281
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1329, hcut1320⟩
                    · exact hne1
                    · exact hne2
            ·
              have hlo1321 : q 251886281 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1320)
              by_cases hcut1330 : y ≤ q 251942240 scaleN
              ·
                by_cases hcut1332 : y ≤ q 251904934 scaleN
                ·
                  apply V_pos_box_s1_s2 251886281 251904934
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1321, hcut1332⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1333 : q 251904934 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1332)
                  by_cases hcut1334 : y ≤ q 251923587 scaleN
                  ·
                    apply V_pos_box_s1_s2 251904934 251923587
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1333, hcut1334⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1335 : q 251923587 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1334)
                    apply V_pos_box_s1_s2 251923587 251942240
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1335, hcut1330⟩
                    · exact hne1
                    · exact hne2
              ·
                have hlo1331 : q 251942240 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1330)
                by_cases hcut1336 : y ≤ q 251960893 scaleN
                ·
                  apply V_pos_box_s1_s2 251942240 251960893
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1331, hcut1336⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1337 : q 251960893 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1336)
                  by_cases hcut1338 : y ≤ q 251979547 scaleN
                  ·
                    apply V_pos_box_s1_s2 251960893 251979547
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1337, hcut1338⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1339 : q 251979547 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1338)
                    apply V_pos_box_s1_s2 251979547 251998200
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1339, hcut1254⟩
                    · exact hne1
                    · exact hne2
      ·
        have hlo1255 : q 251998200 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1254)
        by_cases hcut1340 : y ≤ q 252250016 scaleN
        ·
          by_cases hcut1342 : y ≤ q 252147425 scaleN
          ·
            by_cases hcut1344 : y ≤ q 252091465 scaleN
            ·
              by_cases hcut1346 : y ≤ q 252035506 scaleN
              ·
                by_cases hcut1348 : y ≤ q 252016853 scaleN
                ·
                  apply V_pos_box_s1_s2 251998200 252016853
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1255, hcut1348⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1349 : q 252016853 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1348)
                  apply V_pos_box_s1_s2 252016853 252035506
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1349, hcut1346⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1347 : q 252035506 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1346)
                by_cases hcut1350 : y ≤ q 252054159 scaleN
                ·
                  apply V_pos_box_s1_s2 252035506 252054159
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1347, hcut1350⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1351 : q 252054159 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1350)
                  by_cases hcut1352 : y ≤ q 252072812 scaleN
                  ·
                    apply V_pos_box_s1_s2 252054159 252072812
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1351, hcut1352⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1353 : q 252072812 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1352)
                    apply V_pos_box_s1_s2 252072812 252091465
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1353, hcut1344⟩
                    · exact hne1
                    · exact hne2
            ·
              have hlo1345 : q 252091465 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1344)
              by_cases hcut1354 : y ≤ q 252119445 scaleN
              ·
                by_cases hcut1356 : y ≤ q 252110118 scaleN
                ·
                  apply V_pos_box_s1_s2 252091465 252110118
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1345, hcut1356⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1357 : q 252110118 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1356)
                  apply V_pos_box_s1_s2 252110118 252119445
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1357, hcut1354⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1355 : q 252119445 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1354)
                by_cases hcut1358 : y ≤ q 252128772 scaleN
                ·
                  apply V_pos_box_s1_s2 252119445 252128772
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1355, hcut1358⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1359 : q 252128772 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1358)
                  by_cases hcut1360 : y ≤ q 252138098 scaleN
                  ·
                    apply V_pos_box_s1_s2 252128772 252138098
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1359, hcut1360⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1361 : q 252138098 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1360)
                    apply V_pos_box_s1_s2 252138098 252147425
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1361, hcut1342⟩
                    · exact hne1
                    · exact hne2
          ·
            have hlo1343 : q 252147425 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1342)
            by_cases hcut1362 : y ≤ q 252194057 scaleN
            ·
              by_cases hcut1364 : y ≤ q 252166078 scaleN
              ·
                by_cases hcut1366 : y ≤ q 252156751 scaleN
                ·
                  apply V_pos_box_s1_s2 252147425 252156751
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1343, hcut1366⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1367 : q 252156751 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1366)
                  apply V_pos_box_s1_s2 252156751 252166078
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1367, hcut1364⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1365 : q 252166078 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1364)
                by_cases hcut1368 : y ≤ q 252175404 scaleN
                ·
                  apply V_pos_box_s1_s2 252166078 252175404
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1365, hcut1368⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1369 : q 252175404 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1368)
                  by_cases hcut1370 : y ≤ q 252184731 scaleN
                  ·
                    apply V_pos_box_s1_s2 252175404 252184731
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1369, hcut1370⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1371 : q 252184731 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1370)
                    apply V_pos_box_s1_s2 252184731 252194057
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1371, hcut1362⟩
                    · exact hne1
                    · exact hne2
            ·
              have hlo1363 : q 252194057 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1362)
              by_cases hcut1372 : y ≤ q 252222037 scaleN
              ·
                by_cases hcut1374 : y ≤ q 252203384 scaleN
                ·
                  apply V_pos_box_s1_s2 252194057 252203384
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1363, hcut1374⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1375 : q 252203384 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1374)
                  by_cases hcut1376 : y ≤ q 252212710 scaleN
                  ·
                    apply V_pos_box_s1_s2 252203384 252212710
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1375, hcut1376⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1377 : q 252212710 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1376)
                    apply V_pos_box_s1_s2 252212710 252222037
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1377, hcut1372⟩
                    · exact hne1
                    · exact hne2
              ·
                have hlo1373 : q 252222037 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1372)
                by_cases hcut1378 : y ≤ q 252231363 scaleN
                ·
                  apply V_pos_box_s1_s2 252222037 252231363
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1373, hcut1378⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1379 : q 252231363 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1378)
                  by_cases hcut1380 : y ≤ q 252240690 scaleN
                  ·
                    apply V_pos_box_s1_s2 252231363 252240690
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1379, hcut1380⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1381 : q 252240690 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1380)
                    apply V_pos_box_s1_s2 252240690 252250016
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1381, hcut1340⟩
                    · exact hne1
                    · exact hne2
        ·
          have hlo1341 : q 252250016 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1340)
          by_cases hcut1382 : y ≤ q 252329292 scaleN
          ·
            by_cases hcut1384 : y ≤ q 252296650 scaleN
            ·
              by_cases hcut1386 : y ≤ q 252268670 scaleN
              ·
                by_cases hcut1388 : y ≤ q 252259343 scaleN
                ·
                  apply V_pos_box_s1_s2 252250016 252259343
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1341, hcut1388⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1389 : q 252259343 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1388)
                  apply V_pos_box_s1_s2 252259343 252268670
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1389, hcut1386⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1387 : q 252268670 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1386)
                by_cases hcut1390 : y ≤ q 252277997 scaleN
                ·
                  apply V_pos_box_s1_s2 252268670 252277997
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1387, hcut1390⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1391 : q 252277997 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1390)
                  by_cases hcut1392 : y ≤ q 252287323 scaleN
                  ·
                    apply V_pos_box_s1_s2 252277997 252287323
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1391, hcut1392⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1393 : q 252287323 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1392)
                    apply V_pos_box_s1_s2 252287323 252296650
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1393, hcut1384⟩
                    · exact hne1
                    · exact hne2
            ·
              have hlo1385 : q 252296650 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1384)
              by_cases hcut1394 : y ≤ q 252315303 scaleN
              ·
                by_cases hcut1396 : y ≤ q 252305976 scaleN
                ·
                  apply V_pos_box_s1_s2 252296650 252305976
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1385, hcut1396⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1397 : q 252305976 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1396)
                  by_cases hcut1398 : y ≤ q 252310639 scaleN
                  ·
                    apply V_pos_box_s1_s2 252305976 252310639
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1397, hcut1398⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1399 : q 252310639 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1398)
                    apply V_pos_box_s1_s2 252310639 252315303
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1399, hcut1394⟩
                    · exact hne1
                    · exact hne2
              ·
                have hlo1395 : q 252315303 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1394)
                by_cases hcut1400 : y ≤ q 252319966 scaleN
                ·
                  apply V_pos_box_s1_s2 252315303 252319966
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1395, hcut1400⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1401 : q 252319966 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1400)
                  by_cases hcut1402 : y ≤ q 252324629 scaleN
                  ·
                    apply V_pos_box_s1_s2 252319966 252324629
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1401, hcut1402⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1403 : q 252324629 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1402)
                    apply V_pos_box_s1_s2 252324629 252329292
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1403, hcut1382⟩
                    · exact hne1
                    · exact hne2
          ·
            have hlo1383 : q 252329292 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1382)
            by_cases hcut1404 : y ≤ q 252352609 scaleN
            ·
              by_cases hcut1406 : y ≤ q 252338619 scaleN
              ·
                by_cases hcut1408 : y ≤ q 252333956 scaleN
                ·
                  apply V_pos_box_s1_s2 252329292 252333956
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1383, hcut1408⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1409 : q 252333956 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1408)
                  apply V_pos_box_s1_s2 252333956 252338619
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1409, hcut1406⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1407 : q 252338619 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1406)
                by_cases hcut1410 : y ≤ q 252343282 scaleN
                ·
                  apply V_pos_box_s1_s2 252338619 252343282
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1407, hcut1410⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1411 : q 252343282 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1410)
                  by_cases hcut1412 : y ≤ q 252347945 scaleN
                  ·
                    apply V_pos_box_s1_s2 252343282 252347945
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1411, hcut1412⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1413 : q 252347945 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1412)
                    apply V_pos_box_s1_s2 252347945 252352609
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1413, hcut1404⟩
                    · exact hne1
                    · exact hne2
            ·
              have hlo1405 : q 252352609 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1404)
              by_cases hcut1414 : y ≤ q 252366598 scaleN
              ·
                by_cases hcut1416 : y ≤ q 252357272 scaleN
                ·
                  apply V_pos_box_s1_s2 252352609 252357272
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1405, hcut1416⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1417 : q 252357272 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1416)
                  by_cases hcut1418 : y ≤ q 252361935 scaleN
                  ·
                    apply V_pos_box_s1_s2 252357272 252361935
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1417, hcut1418⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1419 : q 252361935 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1418)
                    apply V_pos_box_s1_s2 252361935 252366598
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1419, hcut1414⟩
                    · exact hne1
                    · exact hne2
              ·
                have hlo1415 : q 252366598 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1414)
                by_cases hcut1420 : y ≤ q 252371262 scaleN
                ·
                  apply V_pos_box_s1_s2 252366598 252371262
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1415, hcut1420⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1421 : q 252371262 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1420)
                  by_cases hcut1422 : y ≤ q 252375925 scaleN
                  ·
                    apply V_pos_box_s1_s2 252371262 252375925
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1421, hcut1422⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1423 : q 252375925 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1422)
                    apply V_pos_box_s1_s2 252375925 252380588
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1423, hcut1252⟩
                    · exact hne1
                    · exact hne2
    ·
      have hlo1253 : q 252380588 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1252)
      by_cases hcut1424 : y ≤ q 252525150 scaleN
      ·
        by_cases hcut1426 : y ≤ q 252473854 scaleN
        ·
          by_cases hcut1428 : y ≤ q 252427222 scaleN
          ·
            by_cases hcut1430 : y ≤ q 252403904 scaleN
            ·
              by_cases hcut1432 : y ≤ q 252389915 scaleN
              ·
                by_cases hcut1434 : y ≤ q 252385251 scaleN
                ·
                  apply V_pos_box_s1_s2 252380588 252385251
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1253, hcut1434⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1435 : q 252385251 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1434)
                  apply V_pos_box_s1_s2 252385251 252389915
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1435, hcut1432⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1433 : q 252389915 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1432)
                by_cases hcut1436 : y ≤ q 252394578 scaleN
                ·
                  apply V_pos_box_s1_s2 252389915 252394578
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1433, hcut1436⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1437 : q 252394578 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1436)
                  by_cases hcut1438 : y ≤ q 252399241 scaleN
                  ·
                    apply V_pos_box_s1_s2 252394578 252399241
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1437, hcut1438⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1439 : q 252399241 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1438)
                    apply V_pos_box_s1_s2 252399241 252403904
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1439, hcut1430⟩
                    · exact hne1
                    · exact hne2
            ·
              have hlo1431 : q 252403904 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1430)
              by_cases hcut1440 : y ≤ q 252413231 scaleN
              ·
                by_cases hcut1442 : y ≤ q 252408568 scaleN
                ·
                  apply V_pos_box_s1_s2 252403904 252408568
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1431, hcut1442⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1443 : q 252408568 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1442)
                  apply V_pos_box_s1_s2 252408568 252413231
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1443, hcut1440⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1441 : q 252413231 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1440)
                by_cases hcut1444 : y ≤ q 252417895 scaleN
                ·
                  apply V_pos_box_s1_s2 252413231 252417895
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1441, hcut1444⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1445 : q 252417895 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1444)
                  by_cases hcut1446 : y ≤ q 252422558 scaleN
                  ·
                    apply V_pos_box_s1_s2 252417895 252422558
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1445, hcut1446⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1447 : q 252422558 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1446)
                    apply V_pos_box_s1_s2 252422558 252427222
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1447, hcut1428⟩
                    · exact hne1
                    · exact hne2
          ·
            have hlo1429 : q 252427222 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1428)
            by_cases hcut1448 : y ≤ q 252450538 scaleN
            ·
              by_cases hcut1450 : y ≤ q 252436548 scaleN
              ·
                by_cases hcut1452 : y ≤ q 252431885 scaleN
                ·
                  apply V_pos_box_s1_s2 252427222 252431885
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1429, hcut1452⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1453 : q 252431885 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1452)
                  apply V_pos_box_s1_s2 252431885 252436548
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1453, hcut1450⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1451 : q 252436548 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1450)
                by_cases hcut1454 : y ≤ q 252441211 scaleN
                ·
                  apply V_pos_box_s1_s2 252436548 252441211
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1451, hcut1454⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1455 : q 252441211 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1454)
                  by_cases hcut1456 : y ≤ q 252445875 scaleN
                  ·
                    apply V_pos_box_s1_s2 252441211 252445875
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1455, hcut1456⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1457 : q 252445875 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1456)
                    apply V_pos_box_s1_s2 252445875 252450538
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1457, hcut1448⟩
                    · exact hne1
                    · exact hne2
            ·
              have hlo1449 : q 252450538 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1448)
              by_cases hcut1458 : y ≤ q 252464528 scaleN
              ·
                by_cases hcut1460 : y ≤ q 252455201 scaleN
                ·
                  apply V_pos_box_s1_s2 252450538 252455201
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1449, hcut1460⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1461 : q 252455201 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1460)
                  by_cases hcut1462 : y ≤ q 252459864 scaleN
                  ·
                    apply V_pos_box_s1_s2 252455201 252459864
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1461, hcut1462⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1463 : q 252459864 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1462)
                    apply V_pos_box_s1_s2 252459864 252464528
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1463, hcut1458⟩
                    · exact hne1
                    · exact hne2
              ·
                have hlo1459 : q 252464528 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1458)
                by_cases hcut1464 : y ≤ q 252469191 scaleN
                ·
                  apply V_pos_box_s1_s2 252464528 252469191
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1459, hcut1464⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1465 : q 252469191 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1464)
                  by_cases hcut1466 : y ≤ q 252471522 scaleN
                  ·
                    apply V_pos_box_s1_s2 252469191 252471522
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1465, hcut1466⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1467 : q 252471522 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1466)
                    apply V_pos_box_s1_s2 252471522 252473854
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1467, hcut1426⟩
                    · exact hne1
                    · exact hne2
        ·
          have hlo1427 : q 252473854 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1426)
          by_cases hcut1468 : y ≤ q 252499502 scaleN
          ·
            by_cases hcut1470 : y ≤ q 252485512 scaleN
            ·
              by_cases hcut1472 : y ≤ q 252478517 scaleN
              ·
                by_cases hcut1474 : y ≤ q 252476185 scaleN
                ·
                  apply V_pos_box_s1_s2 252473854 252476185
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1427, hcut1474⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1475 : q 252476185 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1474)
                  apply V_pos_box_s1_s2 252476185 252478517
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1475, hcut1472⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1473 : q 252478517 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1472)
                by_cases hcut1476 : y ≤ q 252480849 scaleN
                ·
                  apply V_pos_box_s1_s2 252478517 252480849
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1473, hcut1476⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1477 : q 252480849 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1476)
                  by_cases hcut1478 : y ≤ q 252483181 scaleN
                  ·
                    apply V_pos_box_s1_s2 252480849 252483181
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1477, hcut1478⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1479 : q 252483181 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1478)
                    apply V_pos_box_s1_s2 252483181 252485512
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1479, hcut1470⟩
                    · exact hne1
                    · exact hne2
            ·
              have hlo1471 : q 252485512 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1470)
              by_cases hcut1480 : y ≤ q 252492507 scaleN
              ·
                by_cases hcut1482 : y ≤ q 252487844 scaleN
                ·
                  apply V_pos_box_s1_s2 252485512 252487844
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1471, hcut1482⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1483 : q 252487844 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1482)
                  by_cases hcut1484 : y ≤ q 252490175 scaleN
                  ·
                    apply V_pos_box_s1_s2 252487844 252490175
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1483, hcut1484⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1485 : q 252490175 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1484)
                    apply V_pos_box_s1_s2 252490175 252492507
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1485, hcut1480⟩
                    · exact hne1
                    · exact hne2
              ·
                have hlo1481 : q 252492507 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1480)
                by_cases hcut1486 : y ≤ q 252494838 scaleN
                ·
                  apply V_pos_box_s1_s2 252492507 252494838
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1481, hcut1486⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1487 : q 252494838 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1486)
                  by_cases hcut1488 : y ≤ q 252497170 scaleN
                  ·
                    apply V_pos_box_s1_s2 252494838 252497170
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1487, hcut1488⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1489 : q 252497170 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1488)
                    apply V_pos_box_s1_s2 252497170 252499502
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1489, hcut1468⟩
                    · exact hne1
                    · exact hne2
          ·
            have hlo1469 : q 252499502 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1468)
            by_cases hcut1490 : y ≤ q 252511160 scaleN
            ·
              by_cases hcut1492 : y ≤ q 252504165 scaleN
              ·
                by_cases hcut1494 : y ≤ q 252501834 scaleN
                ·
                  apply V_pos_box_s1_s2 252499502 252501834
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1469, hcut1494⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1495 : q 252501834 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1494)
                  apply V_pos_box_s1_s2 252501834 252504165
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1495, hcut1492⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1493 : q 252504165 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1492)
                by_cases hcut1496 : y ≤ q 252506497 scaleN
                ·
                  apply V_pos_box_s1_s2 252504165 252506497
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1493, hcut1496⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1497 : q 252506497 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1496)
                  by_cases hcut1498 : y ≤ q 252508828 scaleN
                  ·
                    apply V_pos_box_s1_s2 252506497 252508828
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1497, hcut1498⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1499 : q 252508828 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1498)
                    apply V_pos_box_s1_s2 252508828 252511160
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1499, hcut1490⟩
                    · exact hne1
                    · exact hne2
            ·
              have hlo1491 : q 252511160 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1490)
              by_cases hcut1500 : y ≤ q 252518155 scaleN
              ·
                by_cases hcut1502 : y ≤ q 252513491 scaleN
                ·
                  apply V_pos_box_s1_s2 252511160 252513491
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1491, hcut1502⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1503 : q 252513491 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1502)
                  by_cases hcut1504 : y ≤ q 252515823 scaleN
                  ·
                    apply V_pos_box_s1_s2 252513491 252515823
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1503, hcut1504⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1505 : q 252515823 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1504)
                    apply V_pos_box_s1_s2 252515823 252518155
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1505, hcut1500⟩
                    · exact hne1
                    · exact hne2
              ·
                have hlo1501 : q 252518155 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1500)
                by_cases hcut1506 : y ≤ q 252520487 scaleN
                ·
                  apply V_pos_box_s1_s2 252518155 252520487
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1501, hcut1506⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1507 : q 252520487 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1506)
                  by_cases hcut1508 : y ≤ q 252522818 scaleN
                  ·
                    apply V_pos_box_s1_s2 252520487 252522818
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1507, hcut1508⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1509 : q 252522818 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1508)
                    apply V_pos_box_s1_s2 252522818 252525150
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1509, hcut1424⟩
                    · exact hne1
                    · exact hne2
      ·
        have hlo1425 : q 252525150 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1424)
        by_cases hcut1510 : y ≤ q 252574115 scaleN
        ·
          by_cases hcut1512 : y ≤ q 252548466 scaleN
          ·
            by_cases hcut1514 : y ≤ q 252536808 scaleN
            ·
              by_cases hcut1516 : y ≤ q 252529813 scaleN
              ·
                by_cases hcut1518 : y ≤ q 252527481 scaleN
                ·
                  apply V_pos_box_s1_s2 252525150 252527481
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1425, hcut1518⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1519 : q 252527481 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1518)
                  apply V_pos_box_s1_s2 252527481 252529813
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1519, hcut1516⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1517 : q 252529813 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1516)
                by_cases hcut1520 : y ≤ q 252532144 scaleN
                ·
                  apply V_pos_box_s1_s2 252529813 252532144
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1517, hcut1520⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1521 : q 252532144 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1520)
                  by_cases hcut1522 : y ≤ q 252534476 scaleN
                  ·
                    apply V_pos_box_s1_s2 252532144 252534476
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1521, hcut1522⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1523 : q 252534476 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1522)
                    apply V_pos_box_s1_s2 252534476 252536808
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1523, hcut1514⟩
                    · exact hne1
                    · exact hne2
            ·
              have hlo1515 : q 252536808 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1514)
              by_cases hcut1524 : y ≤ q 252541471 scaleN
              ·
                by_cases hcut1526 : y ≤ q 252539140 scaleN
                ·
                  apply V_pos_box_s1_s2 252536808 252539140
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1515, hcut1526⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1527 : q 252539140 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1526)
                  apply V_pos_box_s1_s2 252539140 252541471
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1527, hcut1524⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1525 : q 252541471 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1524)
                by_cases hcut1528 : y ≤ q 252543803 scaleN
                ·
                  apply V_pos_box_s1_s2 252541471 252543803
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1525, hcut1528⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1529 : q 252543803 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1528)
                  by_cases hcut1530 : y ≤ q 252546134 scaleN
                  ·
                    apply V_pos_box_s1_s2 252543803 252546134
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1529, hcut1530⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1531 : q 252546134 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1530)
                    apply V_pos_box_s1_s2 252546134 252548466
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1531, hcut1512⟩
                    · exact hne1
                    · exact hne2
          ·
            have hlo1513 : q 252548466 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1512)
            by_cases hcut1532 : y ≤ q 252560124 scaleN
            ·
              by_cases hcut1534 : y ≤ q 252553129 scaleN
              ·
                by_cases hcut1536 : y ≤ q 252550797 scaleN
                ·
                  apply V_pos_box_s1_s2 252548466 252550797
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1513, hcut1536⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1537 : q 252550797 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1536)
                  apply V_pos_box_s1_s2 252550797 252553129
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1537, hcut1534⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1535 : q 252553129 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1534)
                by_cases hcut1538 : y ≤ q 252555461 scaleN
                ·
                  apply V_pos_box_s1_s2 252553129 252555461
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1535, hcut1538⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1539 : q 252555461 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1538)
                  by_cases hcut1540 : y ≤ q 252557793 scaleN
                  ·
                    apply V_pos_box_s1_s2 252555461 252557793
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1539, hcut1540⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1541 : q 252557793 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1540)
                    apply V_pos_box_s1_s2 252557793 252560124
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1541, hcut1532⟩
                    · exact hne1
                    · exact hne2
            ·
              have hlo1533 : q 252560124 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1532)
              by_cases hcut1542 : y ≤ q 252567120 scaleN
              ·
                by_cases hcut1544 : y ≤ q 252562456 scaleN
                ·
                  apply V_pos_box_s1_s2 252560124 252562456
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1533, hcut1544⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1545 : q 252562456 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1544)
                  by_cases hcut1546 : y ≤ q 252564788 scaleN
                  ·
                    apply V_pos_box_s1_s2 252562456 252564788
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1545, hcut1546⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1547 : q 252564788 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1546)
                    apply V_pos_box_s1_s2 252564788 252567120
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1547, hcut1542⟩
                    · exact hne1
                    · exact hne2
              ·
                have hlo1543 : q 252567120 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1542)
                by_cases hcut1548 : y ≤ q 252569451 scaleN
                ·
                  apply V_pos_box_s1_s2 252567120 252569451
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1543, hcut1548⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1549 : q 252569451 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1548)
                  by_cases hcut1550 : y ≤ q 252571783 scaleN
                  ·
                    apply V_pos_box_s1_s2 252569451 252571783
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1549, hcut1550⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1551 : q 252571783 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1550)
                    apply V_pos_box_s1_s2 252571783 252574115
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1551, hcut1510⟩
                    · exact hne1
                    · exact hne2
        ·
          have hlo1511 : q 252574115 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1510)
          by_cases hcut1552 : y ≤ q 252599763 scaleN
          ·
            by_cases hcut1554 : y ≤ q 252585773 scaleN
            ·
              by_cases hcut1556 : y ≤ q 252578778 scaleN
              ·
                by_cases hcut1558 : y ≤ q 252576447 scaleN
                ·
                  apply V_pos_box_s1_s2 252574115 252576447
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1511, hcut1558⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1559 : q 252576447 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1558)
                  apply V_pos_box_s1_s2 252576447 252578778
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1559, hcut1556⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1557 : q 252578778 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1556)
                by_cases hcut1560 : y ≤ q 252581110 scaleN
                ·
                  apply V_pos_box_s1_s2 252578778 252581110
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1557, hcut1560⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1561 : q 252581110 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1560)
                  by_cases hcut1562 : y ≤ q 252583441 scaleN
                  ·
                    apply V_pos_box_s1_s2 252581110 252583441
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1561, hcut1562⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1563 : q 252583441 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1562)
                    apply V_pos_box_s1_s2 252583441 252585773
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1563, hcut1554⟩
                    · exact hne1
                    · exact hne2
            ·
              have hlo1555 : q 252585773 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1554)
              by_cases hcut1564 : y ≤ q 252592768 scaleN
              ·
                by_cases hcut1566 : y ≤ q 252588104 scaleN
                ·
                  apply V_pos_box_s1_s2 252585773 252588104
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1555, hcut1566⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1567 : q 252588104 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1566)
                  by_cases hcut1568 : y ≤ q 252590436 scaleN
                  ·
                    apply V_pos_box_s1_s2 252588104 252590436
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1567, hcut1568⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1569 : q 252590436 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1568)
                    apply V_pos_box_s1_s2 252590436 252592768
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1569, hcut1564⟩
                    · exact hne1
                    · exact hne2
              ·
                have hlo1565 : q 252592768 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1564)
                by_cases hcut1570 : y ≤ q 252595100 scaleN
                ·
                  apply V_pos_box_s1_s2 252592768 252595100
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1565, hcut1570⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1571 : q 252595100 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1570)
                  by_cases hcut1572 : y ≤ q 252597431 scaleN
                  ·
                    apply V_pos_box_s1_s2 252595100 252597431
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1571, hcut1572⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1573 : q 252597431 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1572)
                    apply V_pos_box_s1_s2 252597431 252599763
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1573, hcut1552⟩
                    · exact hne1
                    · exact hne2
          ·
            have hlo1553 : q 252599763 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1552)
            by_cases hcut1574 : y ≤ q 252611421 scaleN
            ·
              by_cases hcut1576 : y ≤ q 252604426 scaleN
              ·
                by_cases hcut1578 : y ≤ q 252602094 scaleN
                ·
                  apply V_pos_box_s1_s2 252599763 252602094
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1553, hcut1578⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1579 : q 252602094 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1578)
                  apply V_pos_box_s1_s2 252602094 252604426
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1579, hcut1576⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1577 : q 252604426 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1576)
                by_cases hcut1580 : y ≤ q 252606757 scaleN
                ·
                  apply V_pos_box_s1_s2 252604426 252606757
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1577, hcut1580⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1581 : q 252606757 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1580)
                  by_cases hcut1582 : y ≤ q 252609089 scaleN
                  ·
                    apply V_pos_box_s1_s2 252606757 252609089
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1581, hcut1582⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1583 : q 252609089 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1582)
                    apply V_pos_box_s1_s2 252609089 252611421
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1583, hcut1574⟩
                    · exact hne1
                    · exact hne2
            ·
              have hlo1575 : q 252611421 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1574)
              by_cases hcut1584 : y ≤ q 252618416 scaleN
              ·
                by_cases hcut1586 : y ≤ q 252613753 scaleN
                ·
                  apply V_pos_box_s1_s2 252611421 252613753
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1575, hcut1586⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1587 : q 252613753 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1586)
                  by_cases hcut1588 : y ≤ q 252616084 scaleN
                  ·
                    apply V_pos_box_s1_s2 252613753 252616084
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1587, hcut1588⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1589 : q 252616084 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1588)
                    apply V_pos_box_s1_s2 252616084 252618416
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1589, hcut1584⟩
                    · exact hne1
                    · exact hne2
              ·
                have hlo1585 : q 252618416 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1584)
                by_cases hcut1590 : y ≤ q 252620747 scaleN
                ·
                  apply V_pos_box_s1_s2 252618416 252620747
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1585, hcut1590⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1591 : q 252620747 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1590)
                  by_cases hcut1592 : y ≤ q 252623079 scaleN
                  ·
                    apply V_pos_box_s1_s2 252620747 252623079
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1591, hcut1592⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1593 : q 252623079 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1592)
                    apply V_pos_box_s1_s2 252623079 252625410
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1593, hcut1250⟩
                    · exact hne1
                    · exact hne2
  ·
    have hlo1251 : q 252625410 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1250)
    by_cases hcut1594 : y ≤ q 252832926 scaleN
    ·
      by_cases hcut1596 : y ≤ q 252725672 scaleN
      ·
        by_cases hcut1598 : y ≤ q 252674375 scaleN
        ·
          by_cases hcut1600 : y ≤ q 252648727 scaleN
          ·
            by_cases hcut1602 : y ≤ q 252637069 scaleN
            ·
              by_cases hcut1604 : y ≤ q 252630074 scaleN
              ·
                by_cases hcut1606 : y ≤ q 252627742 scaleN
                ·
                  apply V_pos_box_s1_s2 252625410 252627742
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1251, hcut1606⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1607 : q 252627742 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1606)
                  apply V_pos_box_s1_s2 252627742 252630074
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1607, hcut1604⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1605 : q 252630074 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1604)
                by_cases hcut1608 : y ≤ q 252632406 scaleN
                ·
                  apply V_pos_box_s1_s2 252630074 252632406
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1605, hcut1608⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1609 : q 252632406 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1608)
                  by_cases hcut1610 : y ≤ q 252634737 scaleN
                  ·
                    apply V_pos_box_s1_s2 252632406 252634737
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1609, hcut1610⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1611 : q 252634737 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1610)
                    apply V_pos_box_s1_s2 252634737 252637069
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1611, hcut1602⟩
                    · exact hne1
                    · exact hne2
            ·
              have hlo1603 : q 252637069 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1602)
              by_cases hcut1612 : y ≤ q 252641732 scaleN
              ·
                by_cases hcut1614 : y ≤ q 252639400 scaleN
                ·
                  apply V_pos_box_s1_s2 252637069 252639400
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1603, hcut1614⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1615 : q 252639400 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1614)
                  apply V_pos_box_s1_s2 252639400 252641732
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1615, hcut1612⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1613 : q 252641732 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1612)
                by_cases hcut1616 : y ≤ q 252644063 scaleN
                ·
                  apply V_pos_box_s1_s2 252641732 252644063
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1613, hcut1616⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1617 : q 252644063 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1616)
                  by_cases hcut1618 : y ≤ q 252646395 scaleN
                  ·
                    apply V_pos_box_s1_s2 252644063 252646395
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1617, hcut1618⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1619 : q 252646395 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1618)
                    apply V_pos_box_s1_s2 252646395 252648727
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1619, hcut1600⟩
                    · exact hne1
                    · exact hne2
          ·
            have hlo1601 : q 252648727 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1600)
            by_cases hcut1620 : y ≤ q 252660385 scaleN
            ·
              by_cases hcut1622 : y ≤ q 252653390 scaleN
              ·
                by_cases hcut1624 : y ≤ q 252651059 scaleN
                ·
                  apply V_pos_box_s1_s2 252648727 252651059
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1601, hcut1624⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1625 : q 252651059 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1624)
                  apply V_pos_box_s1_s2 252651059 252653390
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1625, hcut1622⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1623 : q 252653390 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1622)
                by_cases hcut1626 : y ≤ q 252655722 scaleN
                ·
                  apply V_pos_box_s1_s2 252653390 252655722
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1623, hcut1626⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1627 : q 252655722 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1626)
                  by_cases hcut1628 : y ≤ q 252658053 scaleN
                  ·
                    apply V_pos_box_s1_s2 252655722 252658053
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1627, hcut1628⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1629 : q 252658053 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1628)
                    apply V_pos_box_s1_s2 252658053 252660385
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1629, hcut1620⟩
                    · exact hne1
                    · exact hne2
            ·
              have hlo1621 : q 252660385 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1620)
              by_cases hcut1630 : y ≤ q 252667380 scaleN
              ·
                by_cases hcut1632 : y ≤ q 252662716 scaleN
                ·
                  apply V_pos_box_s1_s2 252660385 252662716
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1621, hcut1632⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1633 : q 252662716 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1632)
                  by_cases hcut1634 : y ≤ q 252665048 scaleN
                  ·
                    apply V_pos_box_s1_s2 252662716 252665048
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1633, hcut1634⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1635 : q 252665048 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1634)
                    apply V_pos_box_s1_s2 252665048 252667380
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1635, hcut1630⟩
                    · exact hne1
                    · exact hne2
              ·
                have hlo1631 : q 252667380 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1630)
                by_cases hcut1636 : y ≤ q 252669712 scaleN
                ·
                  apply V_pos_box_s1_s2 252667380 252669712
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1631, hcut1636⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1637 : q 252669712 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1636)
                  by_cases hcut1638 : y ≤ q 252672043 scaleN
                  ·
                    apply V_pos_box_s1_s2 252669712 252672043
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1637, hcut1638⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1639 : q 252672043 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1638)
                    apply V_pos_box_s1_s2 252672043 252674375
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1639, hcut1598⟩
                    · exact hne1
                    · exact hne2
        ·
          have hlo1599 : q 252674375 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1598)
          by_cases hcut1640 : y ≤ q 252700022 scaleN
          ·
            by_cases hcut1642 : y ≤ q 252686033 scaleN
            ·
              by_cases hcut1644 : y ≤ q 252679038 scaleN
              ·
                by_cases hcut1646 : y ≤ q 252676706 scaleN
                ·
                  apply V_pos_box_s1_s2 252674375 252676706
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1599, hcut1646⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1647 : q 252676706 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1646)
                  apply V_pos_box_s1_s2 252676706 252679038
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1647, hcut1644⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1645 : q 252679038 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1644)
                by_cases hcut1648 : y ≤ q 252681369 scaleN
                ·
                  apply V_pos_box_s1_s2 252679038 252681369
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1645, hcut1648⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1649 : q 252681369 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1648)
                  by_cases hcut1650 : y ≤ q 252683701 scaleN
                  ·
                    apply V_pos_box_s1_s2 252681369 252683701
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1649, hcut1650⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1651 : q 252683701 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1650)
                    apply V_pos_box_s1_s2 252683701 252686033
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1651, hcut1642⟩
                    · exact hne1
                    · exact hne2
            ·
              have hlo1643 : q 252686033 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1642)
              by_cases hcut1652 : y ≤ q 252693028 scaleN
              ·
                by_cases hcut1654 : y ≤ q 252688365 scaleN
                ·
                  apply V_pos_box_s1_s2 252686033 252688365
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1643, hcut1654⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1655 : q 252688365 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1654)
                  by_cases hcut1656 : y ≤ q 252690696 scaleN
                  ·
                    apply V_pos_box_s1_s2 252688365 252690696
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1655, hcut1656⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1657 : q 252690696 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1656)
                    apply V_pos_box_s1_s2 252690696 252693028
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1657, hcut1652⟩
                    · exact hne1
                    · exact hne2
              ·
                have hlo1653 : q 252693028 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1652)
                by_cases hcut1658 : y ≤ q 252695359 scaleN
                ·
                  apply V_pos_box_s1_s2 252693028 252695359
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1653, hcut1658⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1659 : q 252695359 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1658)
                  by_cases hcut1660 : y ≤ q 252697691 scaleN
                  ·
                    apply V_pos_box_s1_s2 252695359 252697691
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1659, hcut1660⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1661 : q 252697691 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1660)
                    apply V_pos_box_s1_s2 252697691 252700022
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1661, hcut1640⟩
                    · exact hne1
                    · exact hne2
          ·
            have hlo1641 : q 252700022 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1640)
            by_cases hcut1662 : y ≤ q 252711681 scaleN
            ·
              by_cases hcut1664 : y ≤ q 252704686 scaleN
              ·
                by_cases hcut1666 : y ≤ q 252702354 scaleN
                ·
                  apply V_pos_box_s1_s2 252700022 252702354
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1641, hcut1666⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1667 : q 252702354 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1666)
                  apply V_pos_box_s1_s2 252702354 252704686
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1667, hcut1664⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1665 : q 252704686 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1664)
                by_cases hcut1668 : y ≤ q 252707018 scaleN
                ·
                  apply V_pos_box_s1_s2 252704686 252707018
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1665, hcut1668⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1669 : q 252707018 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1668)
                  by_cases hcut1670 : y ≤ q 252709349 scaleN
                  ·
                    apply V_pos_box_s1_s2 252707018 252709349
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1669, hcut1670⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1671 : q 252709349 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1670)
                    apply V_pos_box_s1_s2 252709349 252711681
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1671, hcut1662⟩
                    · exact hne1
                    · exact hne2
            ·
              have hlo1663 : q 252711681 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1662)
              by_cases hcut1672 : y ≤ q 252718676 scaleN
              ·
                by_cases hcut1674 : y ≤ q 252714013 scaleN
                ·
                  apply V_pos_box_s1_s2 252711681 252714013
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1663, hcut1674⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1675 : q 252714013 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1674)
                  by_cases hcut1676 : y ≤ q 252716345 scaleN
                  ·
                    apply V_pos_box_s1_s2 252714013 252716345
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1675, hcut1676⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1677 : q 252716345 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1676)
                    apply V_pos_box_s1_s2 252716345 252718676
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1677, hcut1672⟩
                    · exact hne1
                    · exact hne2
              ·
                have hlo1673 : q 252718676 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1672)
                by_cases hcut1678 : y ≤ q 252721008 scaleN
                ·
                  apply V_pos_box_s1_s2 252718676 252721008
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1673, hcut1678⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1679 : q 252721008 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1678)
                  by_cases hcut1680 : y ≤ q 252723340 scaleN
                  ·
                    apply V_pos_box_s1_s2 252721008 252723340
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1679, hcut1680⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1681 : q 252723340 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1680)
                    apply V_pos_box_s1_s2 252723340 252725672
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1681, hcut1596⟩
                    · exact hne1
                    · exact hne2
      ·
        have hlo1597 : q 252725672 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1596)
        by_cases hcut1682 : y ≤ q 252774635 scaleN
        ·
          by_cases hcut1684 : y ≤ q 252748988 scaleN
          ·
            by_cases hcut1686 : y ≤ q 252737329 scaleN
            ·
              by_cases hcut1688 : y ≤ q 252730335 scaleN
              ·
                by_cases hcut1690 : y ≤ q 252728003 scaleN
                ·
                  apply V_pos_box_s1_s2 252725672 252728003
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1597, hcut1690⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1691 : q 252728003 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1690)
                  apply V_pos_box_s1_s2 252728003 252730335
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1691, hcut1688⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1689 : q 252730335 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1688)
                by_cases hcut1692 : y ≤ q 252732666 scaleN
                ·
                  apply V_pos_box_s1_s2 252730335 252732666
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1689, hcut1692⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1693 : q 252732666 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1692)
                  by_cases hcut1694 : y ≤ q 252734998 scaleN
                  ·
                    apply V_pos_box_s1_s2 252732666 252734998
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1693, hcut1694⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1695 : q 252734998 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1694)
                    apply V_pos_box_s1_s2 252734998 252737329
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1695, hcut1686⟩
                    · exact hne1
                    · exact hne2
            ·
              have hlo1687 : q 252737329 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1686)
              by_cases hcut1696 : y ≤ q 252741993 scaleN
              ·
                by_cases hcut1698 : y ≤ q 252739661 scaleN
                ·
                  apply V_pos_box_s1_s2 252737329 252739661
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1687, hcut1698⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1699 : q 252739661 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1698)
                  apply V_pos_box_s1_s2 252739661 252741993
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1699, hcut1696⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1697 : q 252741993 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1696)
                by_cases hcut1700 : y ≤ q 252744325 scaleN
                ·
                  apply V_pos_box_s1_s2 252741993 252744325
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1697, hcut1700⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1701 : q 252744325 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1700)
                  by_cases hcut1702 : y ≤ q 252746656 scaleN
                  ·
                    apply V_pos_box_s1_s2 252744325 252746656
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1701, hcut1702⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1703 : q 252746656 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1702)
                    apply V_pos_box_s1_s2 252746656 252748988
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1703, hcut1684⟩
                    · exact hne1
                    · exact hne2
          ·
            have hlo1685 : q 252748988 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1684)
            by_cases hcut1704 : y ≤ q 252760646 scaleN
            ·
              by_cases hcut1706 : y ≤ q 252753651 scaleN
              ·
                by_cases hcut1708 : y ≤ q 252751319 scaleN
                ·
                  apply V_pos_box_s1_s2 252748988 252751319
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1685, hcut1708⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1709 : q 252751319 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1708)
                  apply V_pos_box_s1_s2 252751319 252753651
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1709, hcut1706⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1707 : q 252753651 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1706)
                by_cases hcut1710 : y ≤ q 252755982 scaleN
                ·
                  apply V_pos_box_s1_s2 252753651 252755982
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1707, hcut1710⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1711 : q 252755982 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1710)
                  by_cases hcut1712 : y ≤ q 252758314 scaleN
                  ·
                    apply V_pos_box_s1_s2 252755982 252758314
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1711, hcut1712⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1713 : q 252758314 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1712)
                    apply V_pos_box_s1_s2 252758314 252760646
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1713, hcut1704⟩
                    · exact hne1
                    · exact hne2
            ·
              have hlo1705 : q 252760646 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1704)
              by_cases hcut1714 : y ≤ q 252767641 scaleN
              ·
                by_cases hcut1716 : y ≤ q 252762978 scaleN
                ·
                  apply V_pos_box_s1_s2 252760646 252762978
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1705, hcut1716⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1717 : q 252762978 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1716)
                  by_cases hcut1718 : y ≤ q 252765309 scaleN
                  ·
                    apply V_pos_box_s1_s2 252762978 252765309
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1717, hcut1718⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1719 : q 252765309 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1718)
                    apply V_pos_box_s1_s2 252765309 252767641
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1719, hcut1714⟩
                    · exact hne1
                    · exact hne2
              ·
                have hlo1715 : q 252767641 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1714)
                by_cases hcut1720 : y ≤ q 252769972 scaleN
                ·
                  apply V_pos_box_s1_s2 252767641 252769972
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1715, hcut1720⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1721 : q 252769972 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1720)
                  by_cases hcut1722 : y ≤ q 252772304 scaleN
                  ·
                    apply V_pos_box_s1_s2 252769972 252772304
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1721, hcut1722⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1723 : q 252772304 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1722)
                    apply V_pos_box_s1_s2 252772304 252774635
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1723, hcut1682⟩
                    · exact hne1
                    · exact hne2
        ·
          have hlo1683 : q 252774635 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1682)
          by_cases hcut1724 : y ≤ q 252800284 scaleN
          ·
            by_cases hcut1726 : y ≤ q 252786294 scaleN
            ·
              by_cases hcut1728 : y ≤ q 252779299 scaleN
              ·
                by_cases hcut1730 : y ≤ q 252776967 scaleN
                ·
                  apply V_pos_box_s1_s2 252774635 252776967
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1683, hcut1730⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1731 : q 252776967 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1730)
                  apply V_pos_box_s1_s2 252776967 252779299
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1731, hcut1728⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1729 : q 252779299 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1728)
                by_cases hcut1732 : y ≤ q 252781631 scaleN
                ·
                  apply V_pos_box_s1_s2 252779299 252781631
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1729, hcut1732⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1733 : q 252781631 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1732)
                  by_cases hcut1734 : y ≤ q 252783962 scaleN
                  ·
                    apply V_pos_box_s1_s2 252781631 252783962
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1733, hcut1734⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1735 : q 252783962 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1734)
                    apply V_pos_box_s1_s2 252783962 252786294
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1735, hcut1726⟩
                    · exact hne1
                    · exact hne2
            ·
              have hlo1727 : q 252786294 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1726)
              by_cases hcut1736 : y ≤ q 252793288 scaleN
              ·
                by_cases hcut1738 : y ≤ q 252788625 scaleN
                ·
                  apply V_pos_box_s1_s2 252786294 252788625
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1727, hcut1738⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1739 : q 252788625 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1738)
                  by_cases hcut1740 : y ≤ q 252790957 scaleN
                  ·
                    apply V_pos_box_s1_s2 252788625 252790957
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1739, hcut1740⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1741 : q 252790957 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1740)
                    apply V_pos_box_s1_s2 252790957 252793288
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1741, hcut1736⟩
                    · exact hne1
                    · exact hne2
              ·
                have hlo1737 : q 252793288 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1736)
                by_cases hcut1742 : y ≤ q 252795620 scaleN
                ·
                  apply V_pos_box_s1_s2 252793288 252795620
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1737, hcut1742⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1743 : q 252795620 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1742)
                  by_cases hcut1744 : y ≤ q 252797952 scaleN
                  ·
                    apply V_pos_box_s1_s2 252795620 252797952
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1743, hcut1744⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1745 : q 252797952 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1744)
                    apply V_pos_box_s1_s2 252797952 252800284
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1745, hcut1724⟩
                    · exact hne1
                    · exact hne2
          ·
            have hlo1725 : q 252800284 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1724)
            by_cases hcut1746 : y ≤ q 252811941 scaleN
            ·
              by_cases hcut1748 : y ≤ q 252804947 scaleN
              ·
                by_cases hcut1750 : y ≤ q 252802615 scaleN
                ·
                  apply V_pos_box_s1_s2 252800284 252802615
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1725, hcut1750⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1751 : q 252802615 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1750)
                  apply V_pos_box_s1_s2 252802615 252804947
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1751, hcut1748⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1749 : q 252804947 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1748)
                by_cases hcut1752 : y ≤ q 252807278 scaleN
                ·
                  apply V_pos_box_s1_s2 252804947 252807278
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1749, hcut1752⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1753 : q 252807278 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1752)
                  by_cases hcut1754 : y ≤ q 252809610 scaleN
                  ·
                    apply V_pos_box_s1_s2 252807278 252809610
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1753, hcut1754⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1755 : q 252809610 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1754)
                    apply V_pos_box_s1_s2 252809610 252811941
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1755, hcut1746⟩
                    · exact hne1
                    · exact hne2
            ·
              have hlo1747 : q 252811941 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1746)
              by_cases hcut1756 : y ≤ q 252818937 scaleN
              ·
                by_cases hcut1758 : y ≤ q 252814273 scaleN
                ·
                  apply V_pos_box_s1_s2 252811941 252814273
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1747, hcut1758⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1759 : q 252814273 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1758)
                  by_cases hcut1760 : y ≤ q 252816605 scaleN
                  ·
                    apply V_pos_box_s1_s2 252814273 252816605
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1759, hcut1760⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1761 : q 252816605 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1760)
                    apply V_pos_box_s1_s2 252816605 252818937
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1761, hcut1756⟩
                    · exact hne1
                    · exact hne2
              ·
                have hlo1757 : q 252818937 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1756)
                by_cases hcut1762 : y ≤ q 252823600 scaleN
                ·
                  apply V_pos_box_s1_s2 252818937 252823600
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1757, hcut1762⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1763 : q 252823600 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1762)
                  by_cases hcut1764 : y ≤ q 252828263 scaleN
                  ·
                    apply V_pos_box_s1_s2 252823600 252828263
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1763, hcut1764⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1765 : q 252828263 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1764)
                    apply V_pos_box_s1_s2 252828263 252832926
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1765, hcut1594⟩
                    · exact hne1
                    · exact hne2
    ·
      have hlo1595 : q 252832926 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1594)
      by_cases hcut1766 : y ≤ q 253089407 scaleN
      ·
        by_cases hcut1768 : y ≤ q 252930856 scaleN
        ·
          by_cases hcut1770 : y ≤ q 252879560 scaleN
          ·
            by_cases hcut1772 : y ≤ q 252856243 scaleN
            ·
              by_cases hcut1774 : y ≤ q 252842253 scaleN
              ·
                by_cases hcut1776 : y ≤ q 252837590 scaleN
                ·
                  apply V_pos_box_s1_s2 252832926 252837590
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1595, hcut1776⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1777 : q 252837590 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1776)
                  apply V_pos_box_s1_s2 252837590 252842253
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1777, hcut1774⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1775 : q 252842253 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1774)
                by_cases hcut1778 : y ≤ q 252846916 scaleN
                ·
                  apply V_pos_box_s1_s2 252842253 252846916
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1775, hcut1778⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1779 : q 252846916 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1778)
                  by_cases hcut1780 : y ≤ q 252851579 scaleN
                  ·
                    apply V_pos_box_s1_s2 252846916 252851579
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1779, hcut1780⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1781 : q 252851579 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1780)
                    apply V_pos_box_s1_s2 252851579 252856243
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1781, hcut1772⟩
                    · exact hne1
                    · exact hne2
            ·
              have hlo1773 : q 252856243 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1772)
              by_cases hcut1782 : y ≤ q 252865570 scaleN
              ·
                by_cases hcut1784 : y ≤ q 252860906 scaleN
                ·
                  apply V_pos_box_s1_s2 252856243 252860906
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1773, hcut1784⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1785 : q 252860906 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1784)
                  apply V_pos_box_s1_s2 252860906 252865570
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1785, hcut1782⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1783 : q 252865570 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1782)
                by_cases hcut1786 : y ≤ q 252870233 scaleN
                ·
                  apply V_pos_box_s1_s2 252865570 252870233
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1783, hcut1786⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1787 : q 252870233 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1786)
                  by_cases hcut1788 : y ≤ q 252874897 scaleN
                  ·
                    apply V_pos_box_s1_s2 252870233 252874897
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1787, hcut1788⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1789 : q 252874897 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1788)
                    apply V_pos_box_s1_s2 252874897 252879560
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1789, hcut1770⟩
                    · exact hne1
                    · exact hne2
          ·
            have hlo1771 : q 252879560 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1770)
            by_cases hcut1790 : y ≤ q 252902876 scaleN
            ·
              by_cases hcut1792 : y ≤ q 252888886 scaleN
              ·
                by_cases hcut1794 : y ≤ q 252884223 scaleN
                ·
                  apply V_pos_box_s1_s2 252879560 252884223
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1771, hcut1794⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1795 : q 252884223 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1794)
                  apply V_pos_box_s1_s2 252884223 252888886
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1795, hcut1792⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1793 : q 252888886 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1792)
                by_cases hcut1796 : y ≤ q 252893550 scaleN
                ·
                  apply V_pos_box_s1_s2 252888886 252893550
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1793, hcut1796⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1797 : q 252893550 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1796)
                  by_cases hcut1798 : y ≤ q 252898213 scaleN
                  ·
                    apply V_pos_box_s1_s2 252893550 252898213
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1797, hcut1798⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1799 : q 252898213 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1798)
                    apply V_pos_box_s1_s2 252898213 252902876
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1799, hcut1790⟩
                    · exact hne1
                    · exact hne2
            ·
              have hlo1791 : q 252902876 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1790)
              by_cases hcut1800 : y ≤ q 252916866 scaleN
              ·
                by_cases hcut1802 : y ≤ q 252907539 scaleN
                ·
                  apply V_pos_box_s1_s2 252902876 252907539
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1791, hcut1802⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1803 : q 252907539 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1802)
                  by_cases hcut1804 : y ≤ q 252912203 scaleN
                  ·
                    apply V_pos_box_s1_s2 252907539 252912203
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1803, hcut1804⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1805 : q 252912203 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1804)
                    apply V_pos_box_s1_s2 252912203 252916866
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1805, hcut1800⟩
                    · exact hne1
                    · exact hne2
              ·
                have hlo1801 : q 252916866 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1800)
                by_cases hcut1806 : y ≤ q 252921529 scaleN
                ·
                  apply V_pos_box_s1_s2 252916866 252921529
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1801, hcut1806⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1807 : q 252921529 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1806)
                  by_cases hcut1808 : y ≤ q 252926192 scaleN
                  ·
                    apply V_pos_box_s1_s2 252921529 252926192
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1807, hcut1808⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1809 : q 252926192 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1808)
                    apply V_pos_box_s1_s2 252926192 252930856
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1809, hcut1768⟩
                    · exact hne1
                    · exact hne2
        ·
          have hlo1769 : q 252930856 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1768)
          by_cases hcut1810 : y ≤ q 252986815 scaleN
          ·
            by_cases hcut1812 : y ≤ q 252954172 scaleN
            ·
              by_cases hcut1814 : y ≤ q 252940182 scaleN
              ·
                by_cases hcut1816 : y ≤ q 252935519 scaleN
                ·
                  apply V_pos_box_s1_s2 252930856 252935519
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1769, hcut1816⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1817 : q 252935519 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1816)
                  apply V_pos_box_s1_s2 252935519 252940182
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1817, hcut1814⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1815 : q 252940182 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1814)
                by_cases hcut1818 : y ≤ q 252944845 scaleN
                ·
                  apply V_pos_box_s1_s2 252940182 252944845
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1815, hcut1818⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1819 : q 252944845 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1818)
                  by_cases hcut1820 : y ≤ q 252949509 scaleN
                  ·
                    apply V_pos_box_s1_s2 252944845 252949509
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1819, hcut1820⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1821 : q 252949509 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1820)
                    apply V_pos_box_s1_s2 252949509 252954172
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1821, hcut1812⟩
                    · exact hne1
                    · exact hne2
            ·
              have hlo1813 : q 252954172 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1812)
              by_cases hcut1822 : y ≤ q 252968162 scaleN
              ·
                by_cases hcut1824 : y ≤ q 252958835 scaleN
                ·
                  apply V_pos_box_s1_s2 252954172 252958835
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1813, hcut1824⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1825 : q 252958835 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1824)
                  by_cases hcut1826 : y ≤ q 252963498 scaleN
                  ·
                    apply V_pos_box_s1_s2 252958835 252963498
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1825, hcut1826⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1827 : q 252963498 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1826)
                    apply V_pos_box_s1_s2 252963498 252968162
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1827, hcut1822⟩
                    · exact hne1
                    · exact hne2
              ·
                have hlo1823 : q 252968162 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1822)
                by_cases hcut1828 : y ≤ q 252972825 scaleN
                ·
                  apply V_pos_box_s1_s2 252968162 252972825
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1823, hcut1828⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1829 : q 252972825 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1828)
                  by_cases hcut1830 : y ≤ q 252977488 scaleN
                  ·
                    apply V_pos_box_s1_s2 252972825 252977488
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1829, hcut1830⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1831 : q 252977488 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1830)
                    apply V_pos_box_s1_s2 252977488 252986815
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1831, hcut1810⟩
                    · exact hne1
                    · exact hne2
          ·
            have hlo1811 : q 252986815 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1810)
            by_cases hcut1832 : y ≤ q 253033448 scaleN
            ·
              by_cases hcut1834 : y ≤ q 253005468 scaleN
              ·
                by_cases hcut1836 : y ≤ q 252996141 scaleN
                ·
                  apply V_pos_box_s1_s2 252986815 252996141
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1811, hcut1836⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1837 : q 252996141 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1836)
                  apply V_pos_box_s1_s2 252996141 253005468
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1837, hcut1834⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1835 : q 253005468 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1834)
                by_cases hcut1838 : y ≤ q 253014795 scaleN
                ·
                  apply V_pos_box_s1_s2 253005468 253014795
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1835, hcut1838⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1839 : q 253014795 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1838)
                  by_cases hcut1840 : y ≤ q 253024122 scaleN
                  ·
                    apply V_pos_box_s1_s2 253014795 253024122
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1839, hcut1840⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1841 : q 253024122 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1840)
                    apply V_pos_box_s1_s2 253024122 253033448
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1841, hcut1832⟩
                    · exact hne1
                    · exact hne2
            ·
              have hlo1833 : q 253033448 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1832)
              by_cases hcut1842 : y ≤ q 253061428 scaleN
              ·
                by_cases hcut1844 : y ≤ q 253042775 scaleN
                ·
                  apply V_pos_box_s1_s2 253033448 253042775
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1833, hcut1844⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1845 : q 253042775 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1844)
                  by_cases hcut1846 : y ≤ q 253052101 scaleN
                  ·
                    apply V_pos_box_s1_s2 253042775 253052101
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1845, hcut1846⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1847 : q 253052101 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1846)
                    apply V_pos_box_s1_s2 253052101 253061428
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1847, hcut1842⟩
                    · exact hne1
                    · exact hne2
              ·
                have hlo1843 : q 253061428 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1842)
                by_cases hcut1848 : y ≤ q 253070754 scaleN
                ·
                  apply V_pos_box_s1_s2 253061428 253070754
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1843, hcut1848⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1849 : q 253070754 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1848)
                  by_cases hcut1850 : y ≤ q 253080081 scaleN
                  ·
                    apply V_pos_box_s1_s2 253070754 253080081
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1849, hcut1850⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1851 : q 253080081 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1850)
                    apply V_pos_box_s1_s2 253080081 253089407
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1851, hcut1766⟩
                    · exact hne1
                    · exact hne2
      ·
        have hlo1767 : q 253089407 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1766)
        by_cases hcut1852 : y ≤ q 253471797 scaleN
        ·
          by_cases hcut1854 : y ≤ q 253229306 scaleN
          ·
            by_cases hcut1856 : y ≤ q 253136040 scaleN
            ·
              by_cases hcut1858 : y ≤ q 253108060 scaleN
              ·
                by_cases hcut1860 : y ≤ q 253098734 scaleN
                ·
                  apply V_pos_box_s1_s2 253089407 253098734
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1767, hcut1860⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1861 : q 253098734 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1860)
                  apply V_pos_box_s1_s2 253098734 253108060
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1861, hcut1858⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1859 : q 253108060 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1858)
                by_cases hcut1862 : y ≤ q 253117387 scaleN
                ·
                  apply V_pos_box_s1_s2 253108060 253117387
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1859, hcut1862⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1863 : q 253117387 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1862)
                  by_cases hcut1864 : y ≤ q 253126713 scaleN
                  ·
                    apply V_pos_box_s1_s2 253117387 253126713
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1863, hcut1864⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1865 : q 253126713 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1864)
                    apply V_pos_box_s1_s2 253126713 253136040
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1865, hcut1856⟩
                    · exact hne1
                    · exact hne2
            ·
              have hlo1857 : q 253136040 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1856)
              by_cases hcut1866 : y ≤ q 253173347 scaleN
              ·
                by_cases hcut1868 : y ≤ q 253145366 scaleN
                ·
                  apply V_pos_box_s1_s2 253136040 253145366
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1857, hcut1868⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1869 : q 253145366 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1868)
                  by_cases hcut1870 : y ≤ q 253154693 scaleN
                  ·
                    apply V_pos_box_s1_s2 253145366 253154693
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1869, hcut1870⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1871 : q 253154693 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1870)
                    apply V_pos_box_s1_s2 253154693 253173347
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1871, hcut1866⟩
                    · exact hne1
                    · exact hne2
              ·
                have hlo1867 : q 253173347 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1866)
                by_cases hcut1872 : y ≤ q 253192000 scaleN
                ·
                  apply V_pos_box_s1_s2 253173347 253192000
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1867, hcut1872⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1873 : q 253192000 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1872)
                  by_cases hcut1874 : y ≤ q 253210653 scaleN
                  ·
                    apply V_pos_box_s1_s2 253192000 253210653
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1873, hcut1874⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1875 : q 253210653 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1874)
                    apply V_pos_box_s1_s2 253210653 253229306
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1875, hcut1854⟩
                    · exact hne1
                    · exact hne2
          ·
            have hlo1855 : q 253229306 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1854)
            by_cases hcut1876 : y ≤ q 253322572 scaleN
            ·
              by_cases hcut1878 : y ≤ q 253266612 scaleN
              ·
                by_cases hcut1880 : y ≤ q 253247959 scaleN
                ·
                  apply V_pos_box_s1_s2 253229306 253247959
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1855, hcut1880⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1881 : q 253247959 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1880)
                  apply V_pos_box_s1_s2 253247959 253266612
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1881, hcut1878⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1879 : q 253266612 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1878)
                by_cases hcut1882 : y ≤ q 253285265 scaleN
                ·
                  apply V_pos_box_s1_s2 253266612 253285265
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1879, hcut1882⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1883 : q 253285265 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1882)
                  by_cases hcut1884 : y ≤ q 253303918 scaleN
                  ·
                    apply V_pos_box_s1_s2 253285265 253303918
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1883, hcut1884⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1885 : q 253303918 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1884)
                    apply V_pos_box_s1_s2 253303918 253322572
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1885, hcut1876⟩
                    · exact hne1
                    · exact hne2
            ·
              have hlo1877 : q 253322572 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1876)
              by_cases hcut1886 : y ≤ q 253378531 scaleN
              ·
                by_cases hcut1888 : y ≤ q 253341225 scaleN
                ·
                  apply V_pos_box_s1_s2 253322572 253341225
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1877, hcut1888⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1889 : q 253341225 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1888)
                  by_cases hcut1890 : y ≤ q 253359878 scaleN
                  ·
                    apply V_pos_box_s1_s2 253341225 253359878
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1889, hcut1890⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1891 : q 253359878 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1890)
                    apply V_pos_box_s1_s2 253359878 253378531
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1891, hcut1886⟩
                    · exact hne1
                    · exact hne2
              ·
                have hlo1887 : q 253378531 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1886)
                by_cases hcut1892 : y ≤ q 253397184 scaleN
                ·
                  apply V_pos_box_s1_s2 253378531 253397184
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1887, hcut1892⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1893 : q 253397184 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1892)
                  by_cases hcut1894 : y ≤ q 253434490 scaleN
                  ·
                    apply V_pos_box_s1_s2 253397184 253434490
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1893, hcut1894⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1895 : q 253434490 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1894)
                    apply V_pos_box_s1_s2 253434490 253471797
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1895, hcut1852⟩
                    · exact hne1
                    · exact hne2
        ·
          have hlo1853 : q 253471797 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1852)
          by_cases hcut1896 : y ≤ q 254068697 scaleN
          ·
            by_cases hcut1898 : y ≤ q 253658328 scaleN
            ·
              by_cases hcut1900 : y ≤ q 253546409 scaleN
              ·
                by_cases hcut1902 : y ≤ q 253509103 scaleN
                ·
                  apply V_pos_box_s1_s2 253471797 253509103
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1853, hcut1902⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1903 : q 253509103 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1902)
                  apply V_pos_box_s1_s2 253509103 253546409
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1903, hcut1900⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1901 : q 253546409 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1900)
                by_cases hcut1904 : y ≤ q 253583715 scaleN
                ·
                  apply V_pos_box_s1_s2 253546409 253583715
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1901, hcut1904⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1905 : q 253583715 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1904)
                  by_cases hcut1906 : y ≤ q 253621022 scaleN
                  ·
                    apply V_pos_box_s1_s2 253583715 253621022
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1905, hcut1906⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1907 : q 253621022 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1906)
                    apply V_pos_box_s1_s2 253621022 253658328
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1907, hcut1898⟩
                    · exact hne1
                    · exact hne2
            ·
              have hlo1899 : q 253658328 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1898)
              by_cases hcut1908 : y ≤ q 253844859 scaleN
              ·
                by_cases hcut1910 : y ≤ q 253695634 scaleN
                ·
                  apply V_pos_box_s1_s2 253658328 253695634
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1899, hcut1910⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1911 : q 253695634 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1910)
                  by_cases hcut1912 : y ≤ q 253770247 scaleN
                  ·
                    apply V_pos_box_s1_s2 253695634 253770247
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1911, hcut1912⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1913 : q 253770247 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1912)
                    apply V_pos_box_s1_s2 253770247 253844859
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1913, hcut1908⟩
                    · exact hne1
                    · exact hne2
              ·
                have hlo1909 : q 253844859 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1908)
                by_cases hcut1914 : y ≤ q 253919472 scaleN
                ·
                  apply V_pos_box_s1_s2 253844859 253919472
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1909, hcut1914⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1915 : q 253919472 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1914)
                  by_cases hcut1916 : y ≤ q 253994084 scaleN
                  ·
                    apply V_pos_box_s1_s2 253919472 253994084
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1915, hcut1916⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1917 : q 253994084 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1916)
                    apply V_pos_box_s1_s2 253994084 254068697
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1917, hcut1896⟩
                    · exact hne1
                    · exact hne2
          ·
            have hlo1897 : q 254068697 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1896)
            by_cases hcut1918 : y ≤ q 254665597 scaleN
            ·
              by_cases hcut1920 : y ≤ q 254217922 scaleN
              ·
                by_cases hcut1922 : y ≤ q 254143309 scaleN
                ·
                  apply V_pos_box_s1_s2 254068697 254143309
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1897, hcut1922⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1923 : q 254143309 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1922)
                  apply V_pos_box_s1_s2 254143309 254217922
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1923, hcut1920⟩
                  · exact hne1
                  · exact hne2
              ·
                have hlo1921 : q 254217922 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1920)
                by_cases hcut1924 : y ≤ q 254367147 scaleN
                ·
                  apply V_pos_box_s1_s2 254217922 254367147
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1921, hcut1924⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1925 : q 254367147 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1924)
                  by_cases hcut1926 : y ≤ q 254516372 scaleN
                  ·
                    apply V_pos_box_s1_s2 254367147 254516372
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1925, hcut1926⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1927 : q 254516372 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1926)
                    apply V_pos_box_s1_s2 254516372 254665597
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1927, hcut1918⟩
                    · exact hne1
                    · exact hne2
            ·
              have hlo1919 : q 254665597 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1918)
              by_cases hcut1928 : y ≤ q 255560947 scaleN
              ·
                by_cases hcut1930 : y ≤ q 254964047 scaleN
                ·
                  apply V_pos_box_s1_s2 254665597 254964047
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1919, hcut1930⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1931 : q 254964047 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1930)
                  by_cases hcut1932 : y ≤ q 255262497 scaleN
                  ·
                    apply V_pos_box_s1_s2 254964047 255262497
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1931, hcut1932⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1933 : q 255262497 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1932)
                    apply V_pos_box_s1_s2 255262497 255560947
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1933, hcut1928⟩
                    · exact hne1
                    · exact hne2
              ·
                have hlo1929 : q 255560947 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1928)
                by_cases hcut1934 : y ≤ q 255859397 scaleN
                ·
                  apply V_pos_box_s1_s2 255560947 255859397
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1929, hcut1934⟩
                  · exact hne1
                  · exact hne2
                ·
                  have hlo1935 : q 255859397 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1934)
                  by_cases hcut1936 : y ≤ q 256456297 scaleN
                  ·
                    apply V_pos_box_s1_s2 255859397 256456297
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1935, hcut1936⟩
                    · exact hne1
                    · exact hne2
                  ·
                    have hlo1937 : q 256456297 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1936)
                    apply V_pos_box_s1_s2 256456297 257053197
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1937, hhi0⟩
                    · exact hne1
                    · exact hne2

theorem V_boxes_s2_s3
    {y : ℝ}
    (hy : y ∈ Icc s2 s3)

    (hne2 : y ≠ s2)
    (hne3 : y ≠ s3)
    :
    0 < V y := by
  have hlo0 : q 257053197 scaleN ≤ y := by
    simpa [s2_eq_q] using hy.1
  have hhi0 : y ≤ q 268367709 scaleN := by
    simpa [s3_eq_q] using hy.2
  by_cases hcut1938 : y ≤ q 260763008 scaleN
  ·
    by_cases hcut1940 : y ≤ q 260616604 scaleN
    ·
      by_cases hcut1942 : y ≤ q 260434290 scaleN
      ·
        by_cases hcut1944 : y ≤ q 260124909 scaleN
        ·
          by_cases hcut1946 : y ≤ q 259616640 scaleN
          ·
            by_cases hcut1948 : y ≤ q 258997878 scaleN
            ·
              by_cases hcut1950 : y ≤ q 258467511 scaleN
              ·
                by_cases hcut1952 : y ≤ q 257760354 scaleN
                ·
                  apply V_pos_box_s2_s3 257053197 257760354
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo0, hcut1952⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo1953 : q 257760354 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1952)
                  apply V_pos_box_s2_s3 257760354 258467511
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1953, hcut1950⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo1951 : q 258467511 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1950)
                by_cases hcut1954 : y ≤ q 258821089 scaleN
                ·
                  apply V_pos_box_s2_s3 258467511 258821089
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1951, hcut1954⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo1955 : q 258821089 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1954)
                  apply V_pos_box_s2_s3 258821089 258997878
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1955, hcut1948⟩
                  · exact hne2
                  · exact hne3
            ·
              have hlo1949 : q 258997878 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1948)
              by_cases hcut1956 : y ≤ q 259351457 scaleN
              ·
                by_cases hcut1958 : y ≤ q 259174668 scaleN
                ·
                  apply V_pos_box_s2_s3 258997878 259174668
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1949, hcut1958⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo1959 : q 259174668 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1958)
                  apply V_pos_box_s2_s3 259174668 259351457
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1959, hcut1956⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo1957 : q 259351457 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1956)
                by_cases hcut1960 : y ≤ q 259439851 scaleN
                ·
                  apply V_pos_box_s2_s3 259351457 259439851
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1957, hcut1960⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo1961 : q 259439851 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1960)
                  by_cases hcut1962 : y ≤ q 259528246 scaleN
                  ·
                    apply V_pos_box_s2_s3 259439851 259528246
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1961, hcut1962⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo1963 : q 259528246 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1962)
                    apply V_pos_box_s2_s3 259528246 259616640
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1963, hcut1946⟩
                    · exact hne2
                    · exact hne3
          ·
            have hlo1947 : q 259616640 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1946)
            by_cases hcut1964 : y ≤ q 259926022 scaleN
            ·
              by_cases hcut1966 : y ≤ q 259793430 scaleN
              ·
                by_cases hcut1968 : y ≤ q 259705035 scaleN
                ·
                  apply V_pos_box_s2_s3 259616640 259705035
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1947, hcut1968⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo1969 : q 259705035 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1968)
                  apply V_pos_box_s2_s3 259705035 259793430
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1969, hcut1966⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo1967 : q 259793430 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1966)
                by_cases hcut1970 : y ≤ q 259837627 scaleN
                ·
                  apply V_pos_box_s2_s3 259793430 259837627
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1967, hcut1970⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo1971 : q 259837627 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1970)
                  by_cases hcut1972 : y ≤ q 259881825 scaleN
                  ·
                    apply V_pos_box_s2_s3 259837627 259881825
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1971, hcut1972⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo1973 : q 259881825 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1972)
                    apply V_pos_box_s2_s3 259881825 259926022
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1973, hcut1964⟩
                    · exact hne2
                    · exact hne3
            ·
              have hlo1965 : q 259926022 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1964)
              by_cases hcut1974 : y ≤ q 260014416 scaleN
              ·
                by_cases hcut1976 : y ≤ q 259970219 scaleN
                ·
                  apply V_pos_box_s2_s3 259926022 259970219
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1965, hcut1976⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo1977 : q 259970219 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1976)
                  apply V_pos_box_s2_s3 259970219 260014416
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1977, hcut1974⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo1975 : q 260014416 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1974)
                by_cases hcut1978 : y ≤ q 260058614 scaleN
                ·
                  apply V_pos_box_s2_s3 260014416 260058614
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1975, hcut1978⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo1979 : q 260058614 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1978)
                  by_cases hcut1980 : y ≤ q 260102811 scaleN
                  ·
                    apply V_pos_box_s2_s3 260058614 260102811
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1979, hcut1980⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo1981 : q 260102811 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1980)
                    apply V_pos_box_s2_s3 260102811 260124909
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1981, hcut1944⟩
                    · exact hne2
                    · exact hne3
        ·
          have hlo1945 : q 260124909 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1944)
          by_cases hcut1982 : y ≤ q 260323797 scaleN
          ·
            by_cases hcut1984 : y ≤ q 260235403 scaleN
            ·
              by_cases hcut1986 : y ≤ q 260169106 scaleN
              ·
                by_cases hcut1988 : y ≤ q 260147008 scaleN
                ·
                  apply V_pos_box_s2_s3 260124909 260147008
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1945, hcut1988⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo1989 : q 260147008 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1988)
                  apply V_pos_box_s2_s3 260147008 260169106
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1989, hcut1986⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo1987 : q 260169106 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1986)
                by_cases hcut1990 : y ≤ q 260191205 scaleN
                ·
                  apply V_pos_box_s2_s3 260169106 260191205
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1987, hcut1990⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo1991 : q 260191205 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1990)
                  by_cases hcut1992 : y ≤ q 260213304 scaleN
                  ·
                    apply V_pos_box_s2_s3 260191205 260213304
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1991, hcut1992⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo1993 : q 260213304 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1992)
                    apply V_pos_box_s2_s3 260213304 260235403
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1993, hcut1984⟩
                    · exact hne2
                    · exact hne3
            ·
              have hlo1985 : q 260235403 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1984)
              by_cases hcut1994 : y ≤ q 260279600 scaleN
              ·
                by_cases hcut1996 : y ≤ q 260257501 scaleN
                ·
                  apply V_pos_box_s2_s3 260235403 260257501
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1985, hcut1996⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo1997 : q 260257501 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1996)
                  apply V_pos_box_s2_s3 260257501 260279600
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1997, hcut1994⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo1995 : q 260279600 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1994)
                by_cases hcut1998 : y ≤ q 260301698 scaleN
                ·
                  apply V_pos_box_s2_s3 260279600 260301698
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1995, hcut1998⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo1999 : q 260301698 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1998)
                  by_cases hcut2000 : y ≤ q 260312747 scaleN
                  ·
                    apply V_pos_box_s2_s3 260301698 260312747
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo1999, hcut2000⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2001 : q 260312747 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2000)
                    apply V_pos_box_s2_s3 260312747 260323797
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2001, hcut1982⟩
                    · exact hne2
                    · exact hne3
          ·
            have hlo1983 : q 260323797 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1982)
            by_cases hcut2002 : y ≤ q 260379043 scaleN
            ·
              by_cases hcut2004 : y ≤ q 260345895 scaleN
              ·
                by_cases hcut2006 : y ≤ q 260334846 scaleN
                ·
                  apply V_pos_box_s2_s3 260323797 260334846
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1983, hcut2006⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2007 : q 260334846 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2006)
                  apply V_pos_box_s2_s3 260334846 260345895
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2007, hcut2004⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2005 : q 260345895 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2004)
                by_cases hcut2008 : y ≤ q 260356944 scaleN
                ·
                  apply V_pos_box_s2_s3 260345895 260356944
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2005, hcut2008⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2009 : q 260356944 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2008)
                  by_cases hcut2010 : y ≤ q 260367994 scaleN
                  ·
                    apply V_pos_box_s2_s3 260356944 260367994
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2009, hcut2010⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2011 : q 260367994 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2010)
                    apply V_pos_box_s2_s3 260367994 260379043
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2011, hcut2002⟩
                    · exact hne2
                    · exact hne3
            ·
              have hlo2003 : q 260379043 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2002)
              by_cases hcut2012 : y ≤ q 260401142 scaleN
              ·
                by_cases hcut2014 : y ≤ q 260390093 scaleN
                ·
                  apply V_pos_box_s2_s3 260379043 260390093
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2003, hcut2014⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2015 : q 260390093 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2014)
                  apply V_pos_box_s2_s3 260390093 260401142
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2015, hcut2012⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2013 : q 260401142 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2012)
                by_cases hcut2016 : y ≤ q 260412192 scaleN
                ·
                  apply V_pos_box_s2_s3 260401142 260412192
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2013, hcut2016⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2017 : q 260412192 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2016)
                  by_cases hcut2018 : y ≤ q 260423241 scaleN
                  ·
                    apply V_pos_box_s2_s3 260412192 260423241
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2017, hcut2018⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2019 : q 260423241 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2018)
                    apply V_pos_box_s2_s3 260423241 260434290
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2019, hcut1942⟩
                    · exact hne2
                    · exact hne3
      ·
        have hlo1943 : q 260434290 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1942)
        by_cases hcut2020 : y ≤ q 260550308 scaleN
        ·
          by_cases hcut2022 : y ≤ q 260495062 scaleN
          ·
            by_cases hcut2024 : y ≤ q 260467438 scaleN
            ·
              by_cases hcut2026 : y ≤ q 260456389 scaleN
              ·
                by_cases hcut2028 : y ≤ q 260445339 scaleN
                ·
                  apply V_pos_box_s2_s3 260434290 260445339
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1943, hcut2028⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2029 : q 260445339 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2028)
                  apply V_pos_box_s2_s3 260445339 260456389
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2029, hcut2026⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2027 : q 260456389 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2026)
                by_cases hcut2030 : y ≤ q 260461913 scaleN
                ·
                  apply V_pos_box_s2_s3 260456389 260461913
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2027, hcut2030⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2031 : q 260461913 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2030)
                  apply V_pos_box_s2_s3 260461913 260467438
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2031, hcut2024⟩
                  · exact hne2
                  · exact hne3
            ·
              have hlo2025 : q 260467438 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2024)
              by_cases hcut2032 : y ≤ q 260478488 scaleN
              ·
                by_cases hcut2034 : y ≤ q 260472963 scaleN
                ·
                  apply V_pos_box_s2_s3 260467438 260472963
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2025, hcut2034⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2035 : q 260472963 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2034)
                  apply V_pos_box_s2_s3 260472963 260478488
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2035, hcut2032⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2033 : q 260478488 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2032)
                by_cases hcut2036 : y ≤ q 260484012 scaleN
                ·
                  apply V_pos_box_s2_s3 260478488 260484012
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2033, hcut2036⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2037 : q 260484012 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2036)
                  by_cases hcut2038 : y ≤ q 260489537 scaleN
                  ·
                    apply V_pos_box_s2_s3 260484012 260489537
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2037, hcut2038⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2039 : q 260489537 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2038)
                    apply V_pos_box_s2_s3 260489537 260495062
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2039, hcut2022⟩
                    · exact hne2
                    · exact hne3
          ·
            have hlo2023 : q 260495062 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2022)
            by_cases hcut2040 : y ≤ q 260522685 scaleN
            ·
              by_cases hcut2042 : y ≤ q 260506111 scaleN
              ·
                by_cases hcut2044 : y ≤ q 260500587 scaleN
                ·
                  apply V_pos_box_s2_s3 260495062 260500587
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2023, hcut2044⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2045 : q 260500587 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2044)
                  apply V_pos_box_s2_s3 260500587 260506111
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2045, hcut2042⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2043 : q 260506111 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2042)
                by_cases hcut2046 : y ≤ q 260511636 scaleN
                ·
                  apply V_pos_box_s2_s3 260506111 260511636
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2043, hcut2046⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2047 : q 260511636 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2046)
                  by_cases hcut2048 : y ≤ q 260517160 scaleN
                  ·
                    apply V_pos_box_s2_s3 260511636 260517160
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2047, hcut2048⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2049 : q 260517160 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2048)
                    apply V_pos_box_s2_s3 260517160 260522685
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2049, hcut2040⟩
                    · exact hne2
                    · exact hne3
            ·
              have hlo2041 : q 260522685 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2040)
              by_cases hcut2050 : y ≤ q 260533734 scaleN
              ·
                by_cases hcut2052 : y ≤ q 260528209 scaleN
                ·
                  apply V_pos_box_s2_s3 260522685 260528209
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2041, hcut2052⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2053 : q 260528209 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2052)
                  apply V_pos_box_s2_s3 260528209 260533734
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2053, hcut2050⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2051 : q 260533734 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2050)
                by_cases hcut2054 : y ≤ q 260539259 scaleN
                ·
                  apply V_pos_box_s2_s3 260533734 260539259
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2051, hcut2054⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2055 : q 260539259 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2054)
                  by_cases hcut2056 : y ≤ q 260544784 scaleN
                  ·
                    apply V_pos_box_s2_s3 260539259 260544784
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2055, hcut2056⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2057 : q 260544784 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2056)
                    apply V_pos_box_s2_s3 260544784 260550308
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2057, hcut2020⟩
                    · exact hne2
                    · exact hne3
        ·
          have hlo2021 : q 260550308 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2020)
          by_cases hcut2058 : y ≤ q 260588982 scaleN
          ·
            by_cases hcut2060 : y ≤ q 260575169 scaleN
            ·
              by_cases hcut2062 : y ≤ q 260561358 scaleN
              ·
                by_cases hcut2064 : y ≤ q 260555833 scaleN
                ·
                  apply V_pos_box_s2_s3 260550308 260555833
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2021, hcut2064⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2065 : q 260555833 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2064)
                  apply V_pos_box_s2_s3 260555833 260561358
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2065, hcut2062⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2063 : q 260561358 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2062)
                by_cases hcut2066 : y ≤ q 260566883 scaleN
                ·
                  apply V_pos_box_s2_s3 260561358 260566883
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2063, hcut2066⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2067 : q 260566883 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2066)
                  by_cases hcut2068 : y ≤ q 260572407 scaleN
                  ·
                    apply V_pos_box_s2_s3 260566883 260572407
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2067, hcut2068⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2069 : q 260572407 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2068)
                    apply V_pos_box_s2_s3 260572407 260575169
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2069, hcut2060⟩
                    · exact hne2
                    · exact hne3
            ·
              have hlo2061 : q 260575169 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2060)
              by_cases hcut2070 : y ≤ q 260580694 scaleN
              ·
                by_cases hcut2072 : y ≤ q 260577932 scaleN
                ·
                  apply V_pos_box_s2_s3 260575169 260577932
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2061, hcut2072⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2073 : q 260577932 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2072)
                  apply V_pos_box_s2_s3 260577932 260580694
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2073, hcut2070⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2071 : q 260580694 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2070)
                by_cases hcut2074 : y ≤ q 260583457 scaleN
                ·
                  apply V_pos_box_s2_s3 260580694 260583457
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2071, hcut2074⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2075 : q 260583457 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2074)
                  by_cases hcut2076 : y ≤ q 260586219 scaleN
                  ·
                    apply V_pos_box_s2_s3 260583457 260586219
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2075, hcut2076⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2077 : q 260586219 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2076)
                    apply V_pos_box_s2_s3 260586219 260588982
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2077, hcut2058⟩
                    · exact hne2
                    · exact hne3
          ·
            have hlo2059 : q 260588982 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2058)
            by_cases hcut2078 : y ≤ q 260602793 scaleN
            ·
              by_cases hcut2080 : y ≤ q 260594506 scaleN
              ·
                by_cases hcut2082 : y ≤ q 260591744 scaleN
                ·
                  apply V_pos_box_s2_s3 260588982 260591744
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2059, hcut2082⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2083 : q 260591744 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2082)
                  apply V_pos_box_s2_s3 260591744 260594506
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2083, hcut2080⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2081 : q 260594506 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2080)
                by_cases hcut2084 : y ≤ q 260597268 scaleN
                ·
                  apply V_pos_box_s2_s3 260594506 260597268
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2081, hcut2084⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2085 : q 260597268 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2084)
                  by_cases hcut2086 : y ≤ q 260600031 scaleN
                  ·
                    apply V_pos_box_s2_s3 260597268 260600031
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2085, hcut2086⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2087 : q 260600031 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2086)
                    apply V_pos_box_s2_s3 260600031 260602793
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2087, hcut2078⟩
                    · exact hne2
                    · exact hne3
            ·
              have hlo2079 : q 260602793 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2078)
              by_cases hcut2088 : y ≤ q 260608317 scaleN
              ·
                by_cases hcut2090 : y ≤ q 260605555 scaleN
                ·
                  apply V_pos_box_s2_s3 260602793 260605555
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2079, hcut2090⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2091 : q 260605555 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2090)
                  apply V_pos_box_s2_s3 260605555 260608317
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2091, hcut2088⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2089 : q 260608317 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2088)
                by_cases hcut2092 : y ≤ q 260611080 scaleN
                ·
                  apply V_pos_box_s2_s3 260608317 260611080
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2089, hcut2092⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2093 : q 260611080 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2092)
                  by_cases hcut2094 : y ≤ q 260613842 scaleN
                  ·
                    apply V_pos_box_s2_s3 260611080 260613842
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2093, hcut2094⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2095 : q 260613842 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2094)
                    apply V_pos_box_s2_s3 260613842 260616604
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2095, hcut1940⟩
                    · exact hne2
                    · exact hne3
    ·
      have hlo1941 : q 260616604 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1940)
      by_cases hcut2096 : y ≤ q 260707760 scaleN
      ·
        by_cases hcut2098 : y ≤ q 260669088 scaleN
        ·
          by_cases hcut2100 : y ≤ q 260641465 scaleN
          ·
            by_cases hcut2102 : y ≤ q 260627654 scaleN
            ·
              by_cases hcut2104 : y ≤ q 260622129 scaleN
              ·
                by_cases hcut2106 : y ≤ q 260619366 scaleN
                ·
                  apply V_pos_box_s2_s3 260616604 260619366
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1941, hcut2106⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2107 : q 260619366 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2106)
                  apply V_pos_box_s2_s3 260619366 260622129
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2107, hcut2104⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2105 : q 260622129 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2104)
                by_cases hcut2108 : y ≤ q 260624891 scaleN
                ·
                  apply V_pos_box_s2_s3 260622129 260624891
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2105, hcut2108⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2109 : q 260624891 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2108)
                  apply V_pos_box_s2_s3 260624891 260627654
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2109, hcut2102⟩
                  · exact hne2
                  · exact hne3
            ·
              have hlo2103 : q 260627654 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2102)
              by_cases hcut2110 : y ≤ q 260633179 scaleN
              ·
                by_cases hcut2112 : y ≤ q 260630416 scaleN
                ·
                  apply V_pos_box_s2_s3 260627654 260630416
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2103, hcut2112⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2113 : q 260630416 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2112)
                  apply V_pos_box_s2_s3 260630416 260633179
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2113, hcut2110⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2111 : q 260633179 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2110)
                by_cases hcut2114 : y ≤ q 260635941 scaleN
                ·
                  apply V_pos_box_s2_s3 260633179 260635941
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2111, hcut2114⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2115 : q 260635941 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2114)
                  by_cases hcut2116 : y ≤ q 260638703 scaleN
                  ·
                    apply V_pos_box_s2_s3 260635941 260638703
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2115, hcut2116⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2117 : q 260638703 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2116)
                    apply V_pos_box_s2_s3 260638703 260641465
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2117, hcut2100⟩
                    · exact hne2
                    · exact hne3
          ·
            have hlo2101 : q 260641465 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2100)
            by_cases hcut2118 : y ≤ q 260655277 scaleN
            ·
              by_cases hcut2120 : y ≤ q 260646990 scaleN
              ·
                by_cases hcut2122 : y ≤ q 260644228 scaleN
                ·
                  apply V_pos_box_s2_s3 260641465 260644228
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2101, hcut2122⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2123 : q 260644228 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2122)
                  apply V_pos_box_s2_s3 260644228 260646990
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2123, hcut2120⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2121 : q 260646990 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2120)
                by_cases hcut2124 : y ≤ q 260649752 scaleN
                ·
                  apply V_pos_box_s2_s3 260646990 260649752
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2121, hcut2124⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2125 : q 260649752 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2124)
                  by_cases hcut2126 : y ≤ q 260652514 scaleN
                  ·
                    apply V_pos_box_s2_s3 260649752 260652514
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2125, hcut2126⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2127 : q 260652514 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2126)
                    apply V_pos_box_s2_s3 260652514 260655277
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2127, hcut2118⟩
                    · exact hne2
                    · exact hne3
            ·
              have hlo2119 : q 260655277 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2118)
              by_cases hcut2128 : y ≤ q 260660801 scaleN
              ·
                by_cases hcut2130 : y ≤ q 260658039 scaleN
                ·
                  apply V_pos_box_s2_s3 260655277 260658039
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2119, hcut2130⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2131 : q 260658039 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2130)
                  apply V_pos_box_s2_s3 260658039 260660801
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2131, hcut2128⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2129 : q 260660801 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2128)
                by_cases hcut2132 : y ≤ q 260663563 scaleN
                ·
                  apply V_pos_box_s2_s3 260660801 260663563
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2129, hcut2132⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2133 : q 260663563 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2132)
                  by_cases hcut2134 : y ≤ q 260666326 scaleN
                  ·
                    apply V_pos_box_s2_s3 260663563 260666326
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2133, hcut2134⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2135 : q 260666326 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2134)
                    apply V_pos_box_s2_s3 260666326 260669088
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2135, hcut2098⟩
                    · exact hne2
                    · exact hne3
        ·
          have hlo2099 : q 260669088 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2098)
          by_cases hcut2136 : y ≤ q 260693949 scaleN
          ·
            by_cases hcut2138 : y ≤ q 260682900 scaleN
            ·
              by_cases hcut2140 : y ≤ q 260674613 scaleN
              ·
                by_cases hcut2142 : y ≤ q 260671851 scaleN
                ·
                  apply V_pos_box_s2_s3 260669088 260671851
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2099, hcut2142⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2143 : q 260671851 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2142)
                  apply V_pos_box_s2_s3 260671851 260674613
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2143, hcut2140⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2141 : q 260674613 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2140)
                by_cases hcut2144 : y ≤ q 260677376 scaleN
                ·
                  apply V_pos_box_s2_s3 260674613 260677376
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2141, hcut2144⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2145 : q 260677376 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2144)
                  by_cases hcut2146 : y ≤ q 260680138 scaleN
                  ·
                    apply V_pos_box_s2_s3 260677376 260680138
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2145, hcut2146⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2147 : q 260680138 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2146)
                    apply V_pos_box_s2_s3 260680138 260682900
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2147, hcut2138⟩
                    · exact hne2
                    · exact hne3
            ·
              have hlo2139 : q 260682900 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2138)
              by_cases hcut2148 : y ≤ q 260688425 scaleN
              ·
                by_cases hcut2150 : y ≤ q 260685662 scaleN
                ·
                  apply V_pos_box_s2_s3 260682900 260685662
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2139, hcut2150⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2151 : q 260685662 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2150)
                  apply V_pos_box_s2_s3 260685662 260688425
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2151, hcut2148⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2149 : q 260688425 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2148)
                by_cases hcut2152 : y ≤ q 260691187 scaleN
                ·
                  apply V_pos_box_s2_s3 260688425 260691187
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2149, hcut2152⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2153 : q 260691187 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2152)
                  by_cases hcut2154 : y ≤ q 260692568 scaleN
                  ·
                    apply V_pos_box_s2_s3 260691187 260692568
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2153, hcut2154⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2155 : q 260692568 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2154)
                    apply V_pos_box_s2_s3 260692568 260693949
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2155, hcut2136⟩
                    · exact hne2
                    · exact hne3
          ·
            have hlo2137 : q 260693949 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2136)
            by_cases hcut2156 : y ≤ q 260700855 scaleN
            ·
              by_cases hcut2158 : y ≤ q 260696711 scaleN
              ·
                by_cases hcut2160 : y ≤ q 260695330 scaleN
                ·
                  apply V_pos_box_s2_s3 260693949 260695330
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2137, hcut2160⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2161 : q 260695330 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2160)
                  apply V_pos_box_s2_s3 260695330 260696711
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2161, hcut2158⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2159 : q 260696711 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2158)
                by_cases hcut2162 : y ≤ q 260698092 scaleN
                ·
                  apply V_pos_box_s2_s3 260696711 260698092
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2159, hcut2162⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2163 : q 260698092 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2162)
                  by_cases hcut2164 : y ≤ q 260699474 scaleN
                  ·
                    apply V_pos_box_s2_s3 260698092 260699474
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2163, hcut2164⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2165 : q 260699474 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2164)
                    apply V_pos_box_s2_s3 260699474 260700855
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2165, hcut2156⟩
                    · exact hne2
                    · exact hne3
            ·
              have hlo2157 : q 260700855 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2156)
              by_cases hcut2166 : y ≤ q 260703617 scaleN
              ·
                by_cases hcut2168 : y ≤ q 260702236 scaleN
                ·
                  apply V_pos_box_s2_s3 260700855 260702236
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2157, hcut2168⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2169 : q 260702236 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2168)
                  apply V_pos_box_s2_s3 260702236 260703617
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2169, hcut2166⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2167 : q 260703617 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2166)
                by_cases hcut2170 : y ≤ q 260704998 scaleN
                ·
                  apply V_pos_box_s2_s3 260703617 260704998
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2167, hcut2170⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2171 : q 260704998 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2170)
                  by_cases hcut2172 : y ≤ q 260706379 scaleN
                  ·
                    apply V_pos_box_s2_s3 260704998 260706379
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2171, hcut2172⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2173 : q 260706379 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2172)
                    apply V_pos_box_s2_s3 260706379 260707760
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2173, hcut2096⟩
                    · exact hne2
                    · exact hne3
      ·
        have hlo2097 : q 260707760 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2096)
        by_cases hcut2174 : y ≤ q 260735384 scaleN
        ·
          by_cases hcut2176 : y ≤ q 260721573 scaleN
          ·
            by_cases hcut2178 : y ≤ q 260714666 scaleN
            ·
              by_cases hcut2180 : y ≤ q 260710523 scaleN
              ·
                by_cases hcut2182 : y ≤ q 260709141 scaleN
                ·
                  apply V_pos_box_s2_s3 260707760 260709141
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2097, hcut2182⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2183 : q 260709141 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2182)
                  apply V_pos_box_s2_s3 260709141 260710523
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2183, hcut2180⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2181 : q 260710523 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2180)
                by_cases hcut2184 : y ≤ q 260711904 scaleN
                ·
                  apply V_pos_box_s2_s3 260710523 260711904
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2181, hcut2184⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2185 : q 260711904 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2184)
                  by_cases hcut2186 : y ≤ q 260713285 scaleN
                  ·
                    apply V_pos_box_s2_s3 260711904 260713285
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2185, hcut2186⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2187 : q 260713285 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2186)
                    apply V_pos_box_s2_s3 260713285 260714666
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2187, hcut2178⟩
                    · exact hne2
                    · exact hne3
            ·
              have hlo2179 : q 260714666 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2178)
              by_cases hcut2188 : y ≤ q 260717429 scaleN
              ·
                by_cases hcut2190 : y ≤ q 260716048 scaleN
                ·
                  apply V_pos_box_s2_s3 260714666 260716048
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2179, hcut2190⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2191 : q 260716048 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2190)
                  apply V_pos_box_s2_s3 260716048 260717429
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2191, hcut2188⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2189 : q 260717429 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2188)
                by_cases hcut2192 : y ≤ q 260718810 scaleN
                ·
                  apply V_pos_box_s2_s3 260717429 260718810
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2189, hcut2192⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2193 : q 260718810 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2192)
                  by_cases hcut2194 : y ≤ q 260720191 scaleN
                  ·
                    apply V_pos_box_s2_s3 260718810 260720191
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2193, hcut2194⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2195 : q 260720191 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2194)
                    apply V_pos_box_s2_s3 260720191 260721573
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2195, hcut2176⟩
                    · exact hne2
                    · exact hne3
          ·
            have hlo2177 : q 260721573 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2176)
            by_cases hcut2196 : y ≤ q 260728478 scaleN
            ·
              by_cases hcut2198 : y ≤ q 260724335 scaleN
              ·
                by_cases hcut2200 : y ≤ q 260722954 scaleN
                ·
                  apply V_pos_box_s2_s3 260721573 260722954
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2177, hcut2200⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2201 : q 260722954 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2200)
                  apply V_pos_box_s2_s3 260722954 260724335
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2201, hcut2198⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2199 : q 260724335 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2198)
                by_cases hcut2202 : y ≤ q 260725716 scaleN
                ·
                  apply V_pos_box_s2_s3 260724335 260725716
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2199, hcut2202⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2203 : q 260725716 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2202)
                  by_cases hcut2204 : y ≤ q 260727097 scaleN
                  ·
                    apply V_pos_box_s2_s3 260725716 260727097
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2203, hcut2204⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2205 : q 260727097 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2204)
                    apply V_pos_box_s2_s3 260727097 260728478
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2205, hcut2196⟩
                    · exact hne2
                    · exact hne3
            ·
              have hlo2197 : q 260728478 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2196)
              by_cases hcut2206 : y ≤ q 260731240 scaleN
              ·
                by_cases hcut2208 : y ≤ q 260729859 scaleN
                ·
                  apply V_pos_box_s2_s3 260728478 260729859
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2197, hcut2208⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2209 : q 260729859 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2208)
                  apply V_pos_box_s2_s3 260729859 260731240
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2209, hcut2206⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2207 : q 260731240 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2206)
                by_cases hcut2210 : y ≤ q 260732622 scaleN
                ·
                  apply V_pos_box_s2_s3 260731240 260732622
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2207, hcut2210⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2211 : q 260732622 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2210)
                  by_cases hcut2212 : y ≤ q 260734003 scaleN
                  ·
                    apply V_pos_box_s2_s3 260732622 260734003
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2211, hcut2212⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2213 : q 260734003 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2212)
                    apply V_pos_box_s2_s3 260734003 260735384
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2213, hcut2174⟩
                    · exact hne2
                    · exact hne3
        ·
          have hlo2175 : q 260735384 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2174)
          by_cases hcut2214 : y ≤ q 260749196 scaleN
          ·
            by_cases hcut2216 : y ≤ q 260742290 scaleN
            ·
              by_cases hcut2218 : y ≤ q 260738147 scaleN
              ·
                by_cases hcut2220 : y ≤ q 260736765 scaleN
                ·
                  apply V_pos_box_s2_s3 260735384 260736765
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2175, hcut2220⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2221 : q 260736765 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2220)
                  apply V_pos_box_s2_s3 260736765 260738147
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2221, hcut2218⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2219 : q 260738147 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2218)
                by_cases hcut2222 : y ≤ q 260739528 scaleN
                ·
                  apply V_pos_box_s2_s3 260738147 260739528
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2219, hcut2222⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2223 : q 260739528 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2222)
                  by_cases hcut2224 : y ≤ q 260740909 scaleN
                  ·
                    apply V_pos_box_s2_s3 260739528 260740909
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2223, hcut2224⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2225 : q 260740909 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2224)
                    apply V_pos_box_s2_s3 260740909 260742290
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2225, hcut2216⟩
                    · exact hne2
                    · exact hne3
            ·
              have hlo2217 : q 260742290 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2216)
              by_cases hcut2226 : y ≤ q 260745053 scaleN
              ·
                by_cases hcut2228 : y ≤ q 260743672 scaleN
                ·
                  apply V_pos_box_s2_s3 260742290 260743672
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2217, hcut2228⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2229 : q 260743672 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2228)
                  apply V_pos_box_s2_s3 260743672 260745053
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2229, hcut2226⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2227 : q 260745053 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2226)
                by_cases hcut2230 : y ≤ q 260746434 scaleN
                ·
                  apply V_pos_box_s2_s3 260745053 260746434
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2227, hcut2230⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2231 : q 260746434 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2230)
                  by_cases hcut2232 : y ≤ q 260747815 scaleN
                  ·
                    apply V_pos_box_s2_s3 260746434 260747815
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2231, hcut2232⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2233 : q 260747815 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2232)
                    apply V_pos_box_s2_s3 260747815 260749196
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2233, hcut2214⟩
                    · exact hne2
                    · exact hne3
          ·
            have hlo2215 : q 260749196 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2214)
            by_cases hcut2234 : y ≤ q 260756102 scaleN
            ·
              by_cases hcut2236 : y ≤ q 260751958 scaleN
              ·
                by_cases hcut2238 : y ≤ q 260750577 scaleN
                ·
                  apply V_pos_box_s2_s3 260749196 260750577
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2215, hcut2238⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2239 : q 260750577 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2238)
                  apply V_pos_box_s2_s3 260750577 260751958
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2239, hcut2236⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2237 : q 260751958 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2236)
                by_cases hcut2240 : y ≤ q 260753339 scaleN
                ·
                  apply V_pos_box_s2_s3 260751958 260753339
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2237, hcut2240⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2241 : q 260753339 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2240)
                  by_cases hcut2242 : y ≤ q 260754721 scaleN
                  ·
                    apply V_pos_box_s2_s3 260753339 260754721
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2241, hcut2242⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2243 : q 260754721 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2242)
                    apply V_pos_box_s2_s3 260754721 260756102
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2243, hcut2234⟩
                    · exact hne2
                    · exact hne3
            ·
              have hlo2235 : q 260756102 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2234)
              by_cases hcut2244 : y ≤ q 260758864 scaleN
              ·
                by_cases hcut2246 : y ≤ q 260757483 scaleN
                ·
                  apply V_pos_box_s2_s3 260756102 260757483
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2235, hcut2246⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2247 : q 260757483 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2246)
                  apply V_pos_box_s2_s3 260757483 260758864
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2247, hcut2244⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2245 : q 260758864 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2244)
                by_cases hcut2248 : y ≤ q 260760246 scaleN
                ·
                  apply V_pos_box_s2_s3 260758864 260760246
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2245, hcut2248⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2249 : q 260760246 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2248)
                  by_cases hcut2250 : y ≤ q 260761627 scaleN
                  ·
                    apply V_pos_box_s2_s3 260760246 260761627
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2249, hcut2250⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2251 : q 260761627 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2250)
                    apply V_pos_box_s2_s3 260761627 260763008
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2251, hcut1938⟩
                    · exact hne2
                    · exact hne3
  ·
    have hlo1939 : q 260763008 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut1938)
    by_cases hcut2252 : y ≤ q 260914936 scaleN
    ·
      by_cases hcut2254 : y ≤ q 260816873 scaleN
      ·
        by_cases hcut2256 : y ≤ q 260789250 scaleN
        ·
          by_cases hcut2258 : y ≤ q 260775438 scaleN
          ·
            by_cases hcut2260 : y ≤ q 260768533 scaleN
            ·
              by_cases hcut2262 : y ≤ q 260765771 scaleN
              ·
                by_cases hcut2264 : y ≤ q 260764389 scaleN
                ·
                  apply V_pos_box_s2_s3 260763008 260764389
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo1939, hcut2264⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2265 : q 260764389 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2264)
                  apply V_pos_box_s2_s3 260764389 260765771
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2265, hcut2262⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2263 : q 260765771 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2262)
                by_cases hcut2266 : y ≤ q 260767152 scaleN
                ·
                  apply V_pos_box_s2_s3 260765771 260767152
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2263, hcut2266⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2267 : q 260767152 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2266)
                  apply V_pos_box_s2_s3 260767152 260768533
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2267, hcut2260⟩
                  · exact hne2
                  · exact hne3
            ·
              have hlo2261 : q 260768533 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2260)
              by_cases hcut2268 : y ≤ q 260771295 scaleN
              ·
                by_cases hcut2270 : y ≤ q 260769914 scaleN
                ·
                  apply V_pos_box_s2_s3 260768533 260769914
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2261, hcut2270⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2271 : q 260769914 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2270)
                  apply V_pos_box_s2_s3 260769914 260771295
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2271, hcut2268⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2269 : q 260771295 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2268)
                by_cases hcut2272 : y ≤ q 260772676 scaleN
                ·
                  apply V_pos_box_s2_s3 260771295 260772676
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2269, hcut2272⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2273 : q 260772676 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2272)
                  by_cases hcut2274 : y ≤ q 260774057 scaleN
                  ·
                    apply V_pos_box_s2_s3 260772676 260774057
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2273, hcut2274⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2275 : q 260774057 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2274)
                    apply V_pos_box_s2_s3 260774057 260775438
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2275, hcut2258⟩
                    · exact hne2
                    · exact hne3
          ·
            have hlo2259 : q 260775438 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2258)
            by_cases hcut2276 : y ≤ q 260782344 scaleN
            ·
              by_cases hcut2278 : y ≤ q 260778201 scaleN
              ·
                by_cases hcut2280 : y ≤ q 260776820 scaleN
                ·
                  apply V_pos_box_s2_s3 260775438 260776820
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2259, hcut2280⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2281 : q 260776820 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2280)
                  apply V_pos_box_s2_s3 260776820 260778201
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2281, hcut2278⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2279 : q 260778201 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2278)
                by_cases hcut2282 : y ≤ q 260779582 scaleN
                ·
                  apply V_pos_box_s2_s3 260778201 260779582
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2279, hcut2282⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2283 : q 260779582 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2282)
                  by_cases hcut2284 : y ≤ q 260780963 scaleN
                  ·
                    apply V_pos_box_s2_s3 260779582 260780963
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2283, hcut2284⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2285 : q 260780963 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2284)
                    apply V_pos_box_s2_s3 260780963 260782344
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2285, hcut2276⟩
                    · exact hne2
                    · exact hne3
            ·
              have hlo2277 : q 260782344 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2276)
              by_cases hcut2286 : y ≤ q 260785106 scaleN
              ·
                by_cases hcut2288 : y ≤ q 260783725 scaleN
                ·
                  apply V_pos_box_s2_s3 260782344 260783725
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2277, hcut2288⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2289 : q 260783725 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2288)
                  apply V_pos_box_s2_s3 260783725 260785106
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2289, hcut2286⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2287 : q 260785106 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2286)
                by_cases hcut2290 : y ≤ q 260786487 scaleN
                ·
                  apply V_pos_box_s2_s3 260785106 260786487
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2287, hcut2290⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2291 : q 260786487 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2290)
                  by_cases hcut2292 : y ≤ q 260787869 scaleN
                  ·
                    apply V_pos_box_s2_s3 260786487 260787869
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2291, hcut2292⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2293 : q 260787869 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2292)
                    apply V_pos_box_s2_s3 260787869 260789250
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2293, hcut2256⟩
                    · exact hne2
                    · exact hne3
        ·
          have hlo2257 : q 260789250 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2256)
          by_cases hcut2294 : y ≤ q 260803061 scaleN
          ·
            by_cases hcut2296 : y ≤ q 260796155 scaleN
            ·
              by_cases hcut2298 : y ≤ q 260792012 scaleN
              ·
                by_cases hcut2300 : y ≤ q 260790631 scaleN
                ·
                  apply V_pos_box_s2_s3 260789250 260790631
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2257, hcut2300⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2301 : q 260790631 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2300)
                  apply V_pos_box_s2_s3 260790631 260792012
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2301, hcut2298⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2299 : q 260792012 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2298)
                by_cases hcut2302 : y ≤ q 260793393 scaleN
                ·
                  apply V_pos_box_s2_s3 260792012 260793393
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2299, hcut2302⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2303 : q 260793393 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2302)
                  by_cases hcut2304 : y ≤ q 260794774 scaleN
                  ·
                    apply V_pos_box_s2_s3 260793393 260794774
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2303, hcut2304⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2305 : q 260794774 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2304)
                    apply V_pos_box_s2_s3 260794774 260796155
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2305, hcut2296⟩
                    · exact hne2
                    · exact hne3
            ·
              have hlo2297 : q 260796155 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2296)
              by_cases hcut2306 : y ≤ q 260798918 scaleN
              ·
                by_cases hcut2308 : y ≤ q 260797536 scaleN
                ·
                  apply V_pos_box_s2_s3 260796155 260797536
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2297, hcut2308⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2309 : q 260797536 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2308)
                  apply V_pos_box_s2_s3 260797536 260798918
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2309, hcut2306⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2307 : q 260798918 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2306)
                by_cases hcut2310 : y ≤ q 260800299 scaleN
                ·
                  apply V_pos_box_s2_s3 260798918 260800299
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2307, hcut2310⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2311 : q 260800299 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2310)
                  by_cases hcut2312 : y ≤ q 260801680 scaleN
                  ·
                    apply V_pos_box_s2_s3 260800299 260801680
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2311, hcut2312⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2313 : q 260801680 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2312)
                    apply V_pos_box_s2_s3 260801680 260803061
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2313, hcut2294⟩
                    · exact hne2
                    · exact hne3
          ·
            have hlo2295 : q 260803061 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2294)
            by_cases hcut2314 : y ≤ q 260809968 scaleN
            ·
              by_cases hcut2316 : y ≤ q 260805824 scaleN
              ·
                by_cases hcut2318 : y ≤ q 260804443 scaleN
                ·
                  apply V_pos_box_s2_s3 260803061 260804443
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2295, hcut2318⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2319 : q 260804443 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2318)
                  apply V_pos_box_s2_s3 260804443 260805824
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2319, hcut2316⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2317 : q 260805824 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2316)
                by_cases hcut2320 : y ≤ q 260807205 scaleN
                ·
                  apply V_pos_box_s2_s3 260805824 260807205
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2317, hcut2320⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2321 : q 260807205 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2320)
                  by_cases hcut2322 : y ≤ q 260808586 scaleN
                  ·
                    apply V_pos_box_s2_s3 260807205 260808586
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2321, hcut2322⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2323 : q 260808586 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2322)
                    apply V_pos_box_s2_s3 260808586 260809968
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2323, hcut2314⟩
                    · exact hne2
                    · exact hne3
            ·
              have hlo2315 : q 260809968 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2314)
              by_cases hcut2324 : y ≤ q 260812730 scaleN
              ·
                by_cases hcut2326 : y ≤ q 260811349 scaleN
                ·
                  apply V_pos_box_s2_s3 260809968 260811349
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2315, hcut2326⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2327 : q 260811349 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2326)
                  apply V_pos_box_s2_s3 260811349 260812730
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2327, hcut2324⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2325 : q 260812730 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2324)
                by_cases hcut2328 : y ≤ q 260814111 scaleN
                ·
                  apply V_pos_box_s2_s3 260812730 260814111
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2325, hcut2328⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2329 : q 260814111 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2328)
                  by_cases hcut2330 : y ≤ q 260815492 scaleN
                  ·
                    apply V_pos_box_s2_s3 260814111 260815492
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2329, hcut2330⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2331 : q 260815492 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2330)
                    apply V_pos_box_s2_s3 260815492 260816873
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2331, hcut2254⟩
                    · exact hne2
                    · exact hne3
      ·
        have hlo2255 : q 260816873 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2254)
        by_cases hcut2332 : y ≤ q 260859689 scaleN
        ·
          by_cases hcut2334 : y ≤ q 260832066 scaleN
          ·
            by_cases hcut2336 : y ≤ q 260823779 scaleN
            ·
              by_cases hcut2338 : y ≤ q 260819635 scaleN
              ·
                by_cases hcut2340 : y ≤ q 260818254 scaleN
                ·
                  apply V_pos_box_s2_s3 260816873 260818254
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2255, hcut2340⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2341 : q 260818254 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2340)
                  apply V_pos_box_s2_s3 260818254 260819635
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2341, hcut2338⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2339 : q 260819635 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2338)
                by_cases hcut2342 : y ≤ q 260821017 scaleN
                ·
                  apply V_pos_box_s2_s3 260819635 260821017
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2339, hcut2342⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2343 : q 260821017 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2342)
                  by_cases hcut2344 : y ≤ q 260822398 scaleN
                  ·
                    apply V_pos_box_s2_s3 260821017 260822398
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2343, hcut2344⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2345 : q 260822398 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2344)
                    apply V_pos_box_s2_s3 260822398 260823779
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2345, hcut2336⟩
                    · exact hne2
                    · exact hne3
            ·
              have hlo2337 : q 260823779 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2336)
              by_cases hcut2346 : y ≤ q 260826541 scaleN
              ·
                by_cases hcut2348 : y ≤ q 260825160 scaleN
                ·
                  apply V_pos_box_s2_s3 260823779 260825160
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2337, hcut2348⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2349 : q 260825160 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2348)
                  apply V_pos_box_s2_s3 260825160 260826541
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2349, hcut2346⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2347 : q 260826541 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2346)
                by_cases hcut2350 : y ≤ q 260827922 scaleN
                ·
                  apply V_pos_box_s2_s3 260826541 260827922
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2347, hcut2350⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2351 : q 260827922 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2350)
                  by_cases hcut2352 : y ≤ q 260829303 scaleN
                  ·
                    apply V_pos_box_s2_s3 260827922 260829303
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2351, hcut2352⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2353 : q 260829303 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2352)
                    apply V_pos_box_s2_s3 260829303 260832066
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2353, hcut2334⟩
                    · exact hne2
                    · exact hne3
          ·
            have hlo2335 : q 260832066 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2334)
            by_cases hcut2354 : y ≤ q 260845877 scaleN
            ·
              by_cases hcut2356 : y ≤ q 260837590 scaleN
              ·
                by_cases hcut2358 : y ≤ q 260834828 scaleN
                ·
                  apply V_pos_box_s2_s3 260832066 260834828
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2335, hcut2358⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2359 : q 260834828 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2358)
                  apply V_pos_box_s2_s3 260834828 260837590
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2359, hcut2356⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2357 : q 260837590 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2356)
                by_cases hcut2360 : y ≤ q 260840352 scaleN
                ·
                  apply V_pos_box_s2_s3 260837590 260840352
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2357, hcut2360⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2361 : q 260840352 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2360)
                  by_cases hcut2362 : y ≤ q 260843115 scaleN
                  ·
                    apply V_pos_box_s2_s3 260840352 260843115
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2361, hcut2362⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2363 : q 260843115 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2362)
                    apply V_pos_box_s2_s3 260843115 260845877
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2363, hcut2354⟩
                    · exact hne2
                    · exact hne3
            ·
              have hlo2355 : q 260845877 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2354)
              by_cases hcut2364 : y ≤ q 260851402 scaleN
              ·
                by_cases hcut2366 : y ≤ q 260848640 scaleN
                ·
                  apply V_pos_box_s2_s3 260845877 260848640
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2355, hcut2366⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2367 : q 260848640 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2366)
                  apply V_pos_box_s2_s3 260848640 260851402
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2367, hcut2364⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2365 : q 260851402 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2364)
                by_cases hcut2368 : y ≤ q 260854165 scaleN
                ·
                  apply V_pos_box_s2_s3 260851402 260854165
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2365, hcut2368⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2369 : q 260854165 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2368)
                  by_cases hcut2370 : y ≤ q 260856927 scaleN
                  ·
                    apply V_pos_box_s2_s3 260854165 260856927
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2369, hcut2370⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2371 : q 260856927 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2370)
                    apply V_pos_box_s2_s3 260856927 260859689
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2371, hcut2332⟩
                    · exact hne2
                    · exact hne3
        ·
          have hlo2333 : q 260859689 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2332)
          by_cases hcut2372 : y ≤ q 260887312 scaleN
          ·
            by_cases hcut2374 : y ≤ q 260873500 scaleN
            ·
              by_cases hcut2376 : y ≤ q 260865214 scaleN
              ·
                by_cases hcut2378 : y ≤ q 260862451 scaleN
                ·
                  apply V_pos_box_s2_s3 260859689 260862451
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2333, hcut2378⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2379 : q 260862451 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2378)
                  apply V_pos_box_s2_s3 260862451 260865214
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2379, hcut2376⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2377 : q 260865214 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2376)
                by_cases hcut2380 : y ≤ q 260867976 scaleN
                ·
                  apply V_pos_box_s2_s3 260865214 260867976
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2377, hcut2380⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2381 : q 260867976 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2380)
                  by_cases hcut2382 : y ≤ q 260870738 scaleN
                  ·
                    apply V_pos_box_s2_s3 260867976 260870738
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2381, hcut2382⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2383 : q 260870738 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2382)
                    apply V_pos_box_s2_s3 260870738 260873500
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2383, hcut2374⟩
                    · exact hne2
                    · exact hne3
            ·
              have hlo2375 : q 260873500 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2374)
              by_cases hcut2384 : y ≤ q 260879025 scaleN
              ·
                by_cases hcut2386 : y ≤ q 260876263 scaleN
                ·
                  apply V_pos_box_s2_s3 260873500 260876263
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2375, hcut2386⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2387 : q 260876263 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2386)
                  apply V_pos_box_s2_s3 260876263 260879025
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2387, hcut2384⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2385 : q 260879025 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2384)
                by_cases hcut2388 : y ≤ q 260881787 scaleN
                ·
                  apply V_pos_box_s2_s3 260879025 260881787
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2385, hcut2388⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2389 : q 260881787 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2388)
                  by_cases hcut2390 : y ≤ q 260884549 scaleN
                  ·
                    apply V_pos_box_s2_s3 260881787 260884549
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2389, hcut2390⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2391 : q 260884549 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2390)
                    apply V_pos_box_s2_s3 260884549 260887312
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2391, hcut2372⟩
                    · exact hne2
                    · exact hne3
          ·
            have hlo2373 : q 260887312 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2372)
            by_cases hcut2392 : y ≤ q 260901124 scaleN
            ·
              by_cases hcut2394 : y ≤ q 260892837 scaleN
              ·
                by_cases hcut2396 : y ≤ q 260890074 scaleN
                ·
                  apply V_pos_box_s2_s3 260887312 260890074
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2373, hcut2396⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2397 : q 260890074 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2396)
                  apply V_pos_box_s2_s3 260890074 260892837
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2397, hcut2394⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2395 : q 260892837 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2394)
                by_cases hcut2398 : y ≤ q 260895599 scaleN
                ·
                  apply V_pos_box_s2_s3 260892837 260895599
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2395, hcut2398⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2399 : q 260895599 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2398)
                  by_cases hcut2400 : y ≤ q 260898362 scaleN
                  ·
                    apply V_pos_box_s2_s3 260895599 260898362
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2399, hcut2400⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2401 : q 260898362 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2400)
                    apply V_pos_box_s2_s3 260898362 260901124
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2401, hcut2392⟩
                    · exact hne2
                    · exact hne3
            ·
              have hlo2393 : q 260901124 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2392)
              by_cases hcut2402 : y ≤ q 260906648 scaleN
              ·
                by_cases hcut2404 : y ≤ q 260903886 scaleN
                ·
                  apply V_pos_box_s2_s3 260901124 260903886
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2393, hcut2404⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2405 : q 260903886 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2404)
                  apply V_pos_box_s2_s3 260903886 260906648
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2405, hcut2402⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2403 : q 260906648 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2402)
                by_cases hcut2406 : y ≤ q 260909411 scaleN
                ·
                  apply V_pos_box_s2_s3 260906648 260909411
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2403, hcut2406⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2407 : q 260909411 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2406)
                  by_cases hcut2408 : y ≤ q 260912173 scaleN
                  ·
                    apply V_pos_box_s2_s3 260909411 260912173
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2407, hcut2408⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2409 : q 260912173 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2408)
                    apply V_pos_box_s2_s3 260912173 260914936
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2409, hcut2252⟩
                    · exact hne2
                    · exact hne3
    ·
      have hlo2253 : q 260914936 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2252)
      by_cases hcut2410 : y ≤ q 261119349 scaleN
      ·
        by_cases hcut2412 : y ≤ q 260986757 scaleN
        ·
          by_cases hcut2414 : y ≤ q 260939797 scaleN
          ·
            by_cases hcut2416 : y ≤ q 260925985 scaleN
            ·
              by_cases hcut2418 : y ≤ q 260920461 scaleN
              ·
                by_cases hcut2420 : y ≤ q 260917698 scaleN
                ·
                  apply V_pos_box_s2_s3 260914936 260917698
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2253, hcut2420⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2421 : q 260917698 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2420)
                  apply V_pos_box_s2_s3 260917698 260920461
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2421, hcut2418⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2419 : q 260920461 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2418)
                by_cases hcut2422 : y ≤ q 260923223 scaleN
                ·
                  apply V_pos_box_s2_s3 260920461 260923223
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2419, hcut2422⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2423 : q 260923223 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2422)
                  apply V_pos_box_s2_s3 260923223 260925985
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2423, hcut2416⟩
                  · exact hne2
                  · exact hne3
            ·
              have hlo2417 : q 260925985 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2416)
              by_cases hcut2424 : y ≤ q 260931510 scaleN
              ·
                by_cases hcut2426 : y ≤ q 260928747 scaleN
                ·
                  apply V_pos_box_s2_s3 260925985 260928747
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2417, hcut2426⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2427 : q 260928747 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2426)
                  apply V_pos_box_s2_s3 260928747 260931510
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2427, hcut2424⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2425 : q 260931510 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2424)
                by_cases hcut2428 : y ≤ q 260934272 scaleN
                ·
                  apply V_pos_box_s2_s3 260931510 260934272
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2425, hcut2428⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2429 : q 260934272 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2428)
                  by_cases hcut2430 : y ≤ q 260937035 scaleN
                  ·
                    apply V_pos_box_s2_s3 260934272 260937035
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2429, hcut2430⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2431 : q 260937035 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2430)
                    apply V_pos_box_s2_s3 260937035 260939797
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2431, hcut2414⟩
                    · exact hne2
                    · exact hne3
          ·
            have hlo2415 : q 260939797 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2414)
            by_cases hcut2432 : y ≤ q 260959133 scaleN
            ·
              by_cases hcut2434 : y ≤ q 260945322 scaleN
              ·
                by_cases hcut2436 : y ≤ q 260942560 scaleN
                ·
                  apply V_pos_box_s2_s3 260939797 260942560
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2415, hcut2436⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2437 : q 260942560 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2436)
                  apply V_pos_box_s2_s3 260942560 260945322
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2437, hcut2434⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2435 : q 260945322 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2434)
                by_cases hcut2438 : y ≤ q 260948084 scaleN
                ·
                  apply V_pos_box_s2_s3 260945322 260948084
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2435, hcut2438⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2439 : q 260948084 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2438)
                  by_cases hcut2440 : y ≤ q 260953609 scaleN
                  ·
                    apply V_pos_box_s2_s3 260948084 260953609
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2439, hcut2440⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2441 : q 260953609 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2440)
                    apply V_pos_box_s2_s3 260953609 260959133
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2441, hcut2432⟩
                    · exact hne2
                    · exact hne3
            ·
              have hlo2433 : q 260959133 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2432)
              by_cases hcut2442 : y ≤ q 260970182 scaleN
              ·
                by_cases hcut2444 : y ≤ q 260964658 scaleN
                ·
                  apply V_pos_box_s2_s3 260959133 260964658
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2433, hcut2444⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2445 : q 260964658 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2444)
                  apply V_pos_box_s2_s3 260964658 260970182
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2445, hcut2442⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2443 : q 260970182 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2442)
                by_cases hcut2446 : y ≤ q 260975707 scaleN
                ·
                  apply V_pos_box_s2_s3 260970182 260975707
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2443, hcut2446⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2447 : q 260975707 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2446)
                  by_cases hcut2448 : y ≤ q 260981232 scaleN
                  ·
                    apply V_pos_box_s2_s3 260975707 260981232
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2447, hcut2448⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2449 : q 260981232 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2448)
                    apply V_pos_box_s2_s3 260981232 260986757
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2449, hcut2412⟩
                    · exact hne2
                    · exact hne3
        ·
          have hlo2413 : q 260986757 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2412)
          by_cases hcut2450 : y ≤ q 261042003 scaleN
          ·
            by_cases hcut2452 : y ≤ q 261014379 scaleN
            ·
              by_cases hcut2454 : y ≤ q 260997806 scaleN
              ·
                by_cases hcut2456 : y ≤ q 260992281 scaleN
                ·
                  apply V_pos_box_s2_s3 260986757 260992281
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2413, hcut2456⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2457 : q 260992281 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2456)
                  apply V_pos_box_s2_s3 260992281 260997806
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2457, hcut2454⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2455 : q 260997806 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2454)
                by_cases hcut2458 : y ≤ q 261003330 scaleN
                ·
                  apply V_pos_box_s2_s3 260997806 261003330
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2455, hcut2458⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2459 : q 261003330 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2458)
                  by_cases hcut2460 : y ≤ q 261008855 scaleN
                  ·
                    apply V_pos_box_s2_s3 261003330 261008855
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2459, hcut2460⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2461 : q 261008855 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2460)
                    apply V_pos_box_s2_s3 261008855 261014379
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2461, hcut2452⟩
                    · exact hne2
                    · exact hne3
            ·
              have hlo2453 : q 261014379 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2452)
              by_cases hcut2462 : y ≤ q 261025429 scaleN
              ·
                by_cases hcut2464 : y ≤ q 261019904 scaleN
                ·
                  apply V_pos_box_s2_s3 261014379 261019904
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2453, hcut2464⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2465 : q 261019904 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2464)
                  apply V_pos_box_s2_s3 261019904 261025429
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2465, hcut2462⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2463 : q 261025429 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2462)
                by_cases hcut2466 : y ≤ q 261030954 scaleN
                ·
                  apply V_pos_box_s2_s3 261025429 261030954
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2463, hcut2466⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2467 : q 261030954 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2466)
                  by_cases hcut2468 : y ≤ q 261036478 scaleN
                  ·
                    apply V_pos_box_s2_s3 261030954 261036478
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2467, hcut2468⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2469 : q 261036478 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2468)
                    apply V_pos_box_s2_s3 261036478 261042003
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2469, hcut2450⟩
                    · exact hne2
                    · exact hne3
          ·
            have hlo2451 : q 261042003 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2450)
            by_cases hcut2470 : y ≤ q 261069626 scaleN
            ·
              by_cases hcut2472 : y ≤ q 261053052 scaleN
              ·
                by_cases hcut2474 : y ≤ q 261047527 scaleN
                ·
                  apply V_pos_box_s2_s3 261042003 261047527
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2451, hcut2474⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2475 : q 261047527 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2474)
                  apply V_pos_box_s2_s3 261047527 261053052
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2475, hcut2472⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2473 : q 261053052 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2472)
                by_cases hcut2476 : y ≤ q 261058576 scaleN
                ·
                  apply V_pos_box_s2_s3 261053052 261058576
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2473, hcut2476⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2477 : q 261058576 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2476)
                  by_cases hcut2478 : y ≤ q 261064101 scaleN
                  ·
                    apply V_pos_box_s2_s3 261058576 261064101
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2477, hcut2478⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2479 : q 261064101 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2478)
                    apply V_pos_box_s2_s3 261064101 261069626
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2479, hcut2470⟩
                    · exact hne2
                    · exact hne3
            ·
              have hlo2471 : q 261069626 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2470)
              by_cases hcut2480 : y ≤ q 261086200 scaleN
              ·
                by_cases hcut2482 : y ≤ q 261075151 scaleN
                ·
                  apply V_pos_box_s2_s3 261069626 261075151
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2471, hcut2482⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2483 : q 261075151 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2482)
                  apply V_pos_box_s2_s3 261075151 261086200
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2483, hcut2480⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2481 : q 261086200 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2480)
                by_cases hcut2484 : y ≤ q 261097250 scaleN
                ·
                  apply V_pos_box_s2_s3 261086200 261097250
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2481, hcut2484⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2485 : q 261097250 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2484)
                  by_cases hcut2486 : y ≤ q 261108299 scaleN
                  ·
                    apply V_pos_box_s2_s3 261097250 261108299
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2485, hcut2486⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2487 : q 261108299 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2486)
                    apply V_pos_box_s2_s3 261108299 261119349
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2487, hcut2410⟩
                    · exact hne2
                    · exact hne3
      ·
        have hlo2411 : q 261119349 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2410)
        by_cases hcut2488 : y ≤ q 261472928 scaleN
        ·
          by_cases hcut2490 : y ≤ q 261229842 scaleN
          ·
            by_cases hcut2492 : y ≤ q 261174595 scaleN
            ·
              by_cases hcut2494 : y ≤ q 261141447 scaleN
              ·
                by_cases hcut2496 : y ≤ q 261130398 scaleN
                ·
                  apply V_pos_box_s2_s3 261119349 261130398
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2411, hcut2496⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2497 : q 261130398 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2496)
                  apply V_pos_box_s2_s3 261130398 261141447
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2497, hcut2494⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2495 : q 261141447 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2494)
                by_cases hcut2498 : y ≤ q 261152496 scaleN
                ·
                  apply V_pos_box_s2_s3 261141447 261152496
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2495, hcut2498⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2499 : q 261152496 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2498)
                  by_cases hcut2500 : y ≤ q 261163546 scaleN
                  ·
                    apply V_pos_box_s2_s3 261152496 261163546
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2499, hcut2500⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2501 : q 261163546 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2500)
                    apply V_pos_box_s2_s3 261163546 261174595
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2501, hcut2492⟩
                    · exact hne2
                    · exact hne3
            ·
              have hlo2493 : q 261174595 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2492)
              by_cases hcut2502 : y ≤ q 261196694 scaleN
              ·
                by_cases hcut2504 : y ≤ q 261185645 scaleN
                ·
                  apply V_pos_box_s2_s3 261174595 261185645
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2493, hcut2504⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2505 : q 261185645 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2504)
                  apply V_pos_box_s2_s3 261185645 261196694
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2505, hcut2502⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2503 : q 261196694 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2502)
                by_cases hcut2506 : y ≤ q 261207744 scaleN
                ·
                  apply V_pos_box_s2_s3 261196694 261207744
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2503, hcut2506⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2507 : q 261207744 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2506)
                  by_cases hcut2508 : y ≤ q 261218793 scaleN
                  ·
                    apply V_pos_box_s2_s3 261207744 261218793
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2507, hcut2508⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2509 : q 261218793 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2508)
                    apply V_pos_box_s2_s3 261218793 261229842
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2509, hcut2490⟩
                    · exact hne2
                    · exact hne3
          ·
            have hlo2491 : q 261229842 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2490)
            by_cases hcut2510 : y ≤ q 261340336 scaleN
            ·
              by_cases hcut2512 : y ≤ q 261274040 scaleN
              ·
                by_cases hcut2514 : y ≤ q 261251941 scaleN
                ·
                  apply V_pos_box_s2_s3 261229842 261251941
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2491, hcut2514⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2515 : q 261251941 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2514)
                  apply V_pos_box_s2_s3 261251941 261274040
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2515, hcut2512⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2513 : q 261274040 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2512)
                by_cases hcut2516 : y ≤ q 261296139 scaleN
                ·
                  apply V_pos_box_s2_s3 261274040 261296139
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2513, hcut2516⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2517 : q 261296139 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2516)
                  by_cases hcut2518 : y ≤ q 261318237 scaleN
                  ·
                    apply V_pos_box_s2_s3 261296139 261318237
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2517, hcut2518⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2519 : q 261318237 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2518)
                    apply V_pos_box_s2_s3 261318237 261340336
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2519, hcut2510⟩
                    · exact hne2
                    · exact hne3
            ·
              have hlo2511 : q 261340336 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2510)
              by_cases hcut2520 : y ≤ q 261384533 scaleN
              ·
                by_cases hcut2522 : y ≤ q 261362434 scaleN
                ·
                  apply V_pos_box_s2_s3 261340336 261362434
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2511, hcut2522⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2523 : q 261362434 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2522)
                  apply V_pos_box_s2_s3 261362434 261384533
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2523, hcut2520⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2521 : q 261384533 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2520)
                by_cases hcut2524 : y ≤ q 261406631 scaleN
                ·
                  apply V_pos_box_s2_s3 261384533 261406631
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2521, hcut2524⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2525 : q 261406631 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2524)
                  by_cases hcut2526 : y ≤ q 261428730 scaleN
                  ·
                    apply V_pos_box_s2_s3 261406631 261428730
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2525, hcut2526⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2527 : q 261428730 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2526)
                    apply V_pos_box_s2_s3 261428730 261472928
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2527, hcut2488⟩
                    · exact hne2
                    · exact hne3
        ·
          have hlo2489 : q 261472928 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2488)
          by_cases hcut2528 : y ≤ q 262091690 scaleN
          ·
            by_cases hcut2530 : y ≤ q 261693914 scaleN
            ·
              by_cases hcut2532 : y ≤ q 261561322 scaleN
              ·
                by_cases hcut2534 : y ≤ q 261517125 scaleN
                ·
                  apply V_pos_box_s2_s3 261472928 261517125
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2489, hcut2534⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2535 : q 261517125 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2534)
                  apply V_pos_box_s2_s3 261517125 261561322
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2535, hcut2532⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2533 : q 261561322 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2532)
                by_cases hcut2536 : y ≤ q 261605519 scaleN
                ·
                  apply V_pos_box_s2_s3 261561322 261605519
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2533, hcut2536⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2537 : q 261605519 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2536)
                  by_cases hcut2538 : y ≤ q 261649717 scaleN
                  ·
                    apply V_pos_box_s2_s3 261605519 261649717
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2537, hcut2538⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2539 : q 261649717 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2538)
                    apply V_pos_box_s2_s3 261649717 261693914
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2539, hcut2530⟩
                    · exact hne2
                    · exact hne3
            ·
              have hlo2531 : q 261693914 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2530)
              by_cases hcut2540 : y ≤ q 261826506 scaleN
              ·
                by_cases hcut2542 : y ≤ q 261738111 scaleN
                ·
                  apply V_pos_box_s2_s3 261693914 261738111
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2531, hcut2542⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2543 : q 261738111 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2542)
                  apply V_pos_box_s2_s3 261738111 261826506
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2543, hcut2540⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2541 : q 261826506 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2540)
                by_cases hcut2544 : y ≤ q 261914901 scaleN
                ·
                  apply V_pos_box_s2_s3 261826506 261914901
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2541, hcut2544⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2545 : q 261914901 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2544)
                  by_cases hcut2546 : y ≤ q 262003296 scaleN
                  ·
                    apply V_pos_box_s2_s3 261914901 262003296
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2545, hcut2546⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2547 : q 262003296 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2546)
                    apply V_pos_box_s2_s3 262003296 262091690
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2547, hcut2528⟩
                    · exact hne2
                    · exact hne3
          ·
            have hlo2529 : q 262091690 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2528)
            by_cases hcut2548 : y ≤ q 263064031 scaleN
            ·
              by_cases hcut2550 : y ≤ q 262356874 scaleN
              ·
                by_cases hcut2552 : y ≤ q 262180085 scaleN
                ·
                  apply V_pos_box_s2_s3 262091690 262180085
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2529, hcut2552⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2553 : q 262180085 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2552)
                  apply V_pos_box_s2_s3 262180085 262356874
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2553, hcut2550⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2551 : q 262356874 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2550)
                by_cases hcut2554 : y ≤ q 262533663 scaleN
                ·
                  apply V_pos_box_s2_s3 262356874 262533663
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2551, hcut2554⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2555 : q 262533663 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2554)
                  by_cases hcut2556 : y ≤ q 262710453 scaleN
                  ·
                    apply V_pos_box_s2_s3 262533663 262710453
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2555, hcut2556⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2557 : q 262710453 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2556)
                    apply V_pos_box_s2_s3 262710453 263064031
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2557, hcut2548⟩
                    · exact hne2
                    · exact hne3
            ·
              have hlo2549 : q 263064031 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2548)
              by_cases hcut2558 : y ≤ q 264124767 scaleN
              ·
                by_cases hcut2560 : y ≤ q 263417610 scaleN
                ·
                  apply V_pos_box_s2_s3 263064031 263417610
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2549, hcut2560⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2561 : q 263417610 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2560)
                  apply V_pos_box_s2_s3 263417610 264124767
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2561, hcut2558⟩
                  · exact hne2
                  · exact hne3
              ·
                have hlo2559 : q 264124767 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2558)
                by_cases hcut2562 : y ≤ q 264831924 scaleN
                ·
                  apply V_pos_box_s2_s3 264124767 264831924
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2559, hcut2562⟩
                  · exact hne2
                  · exact hne3
                ·
                  have hlo2563 : q 264831924 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2562)
                  by_cases hcut2564 : y ≤ q 265539081 scaleN
                  ·
                    apply V_pos_box_s2_s3 264831924 265539081
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2563, hcut2564⟩
                    · exact hne2
                    · exact hne3
                  ·
                    have hlo2565 : q 265539081 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2564)
                    apply V_pos_box_s2_s3 265539081 268367709
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2565, hhi0⟩
                    · exact hne2
                    · exact hne3

theorem V_boxes_s3_s4
    {y : ℝ}
    (hy : y ∈ Icc s3 s4)

    (hne3 : y ≠ s3)
    (hne4 : y ≠ s4)
    :
    0 < V y := by
  have hlo0 : q 268367709 scaleN ≤ y := by
    simpa [s3_eq_q] using hy.1
  have hhi0 : y ≤ q 279017717 scaleN := by
    simpa [s4_eq_q] using hy.2
  by_cases hcut2566 : y ≤ q 274250432 scaleN
  ·
    by_cases hcut2568 : y ≤ q 274147728 scaleN
    ·
      by_cases hcut2570 : y ≤ q 274015124 scaleN
      ·
        by_cases hcut2572 : y ≤ q 273775916 scaleN
        ·
          by_cases hcut2574 : y ≤ q 273359900 scaleN
          ·
            by_cases hcut2576 : y ≤ q 272694274 scaleN
            ·
              by_cases hcut2578 : y ≤ q 271695836 scaleN
              ·
                by_cases hcut2580 : y ≤ q 271030211 scaleN
                ·
                  apply V_pos_box_s3_s4 268367709 271030211
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo0, hcut2580⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2581 : q 271030211 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2580)
                  apply V_pos_box_s3_s4 271030211 271695836
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2581, hcut2578⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2579 : q 271695836 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2578)
                by_cases hcut2582 : y ≤ q 272361462 scaleN
                ·
                  apply V_pos_box_s3_s4 271695836 272361462
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2579, hcut2582⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2583 : q 272361462 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2582)
                  apply V_pos_box_s3_s4 272361462 272694274
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2583, hcut2576⟩
                  · exact hne3
                  · exact hne4
            ·
              have hlo2577 : q 272694274 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2576)
              by_cases hcut2584 : y ≤ q 273027087 scaleN
              ·
                by_cases hcut2586 : y ≤ q 272860680 scaleN
                ·
                  apply V_pos_box_s3_s4 272694274 272860680
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2577, hcut2586⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2587 : q 272860680 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2586)
                  apply V_pos_box_s3_s4 272860680 273027087
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2587, hcut2584⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2585 : q 273027087 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2584)
                by_cases hcut2588 : y ≤ q 273193493 scaleN
                ·
                  apply V_pos_box_s3_s4 273027087 273193493
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2585, hcut2588⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2589 : q 273193493 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2588)
                  by_cases hcut2590 : y ≤ q 273276696 scaleN
                  ·
                    apply V_pos_box_s3_s4 273193493 273276696
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2589, hcut2590⟩
                    · exact hne3
                    · exact hne4
                  ·
                    have hlo2591 : q 273276696 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2590)
                    apply V_pos_box_s3_s4 273276696 273359900
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2591, hcut2574⟩
                    · exact hne3
                    · exact hne4
          ·
            have hlo2575 : q 273359900 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2574)
            by_cases hcut2592 : y ≤ q 273609509 scaleN
            ·
              by_cases hcut2594 : y ≤ q 273526306 scaleN
              ·
                by_cases hcut2596 : y ≤ q 273443103 scaleN
                ·
                  apply V_pos_box_s3_s4 273359900 273443103
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2575, hcut2596⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2597 : q 273443103 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2596)
                  apply V_pos_box_s3_s4 273443103 273526306
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2597, hcut2594⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2595 : q 273526306 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2594)
                by_cases hcut2598 : y ≤ q 273567907 scaleN
                ·
                  apply V_pos_box_s3_s4 273526306 273567907
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2595, hcut2598⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2599 : q 273567907 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2598)
                  apply V_pos_box_s3_s4 273567907 273609509
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2599, hcut2592⟩
                  · exact hne3
                  · exact hne4
            ·
              have hlo2593 : q 273609509 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2592)
              by_cases hcut2600 : y ≤ q 273692713 scaleN
              ·
                by_cases hcut2602 : y ≤ q 273651111 scaleN
                ·
                  apply V_pos_box_s3_s4 273609509 273651111
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2593, hcut2602⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2603 : q 273651111 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2602)
                  apply V_pos_box_s3_s4 273651111 273692713
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2603, hcut2600⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2601 : q 273692713 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2600)
                by_cases hcut2604 : y ≤ q 273734314 scaleN
                ·
                  apply V_pos_box_s3_s4 273692713 273734314
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2601, hcut2604⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2605 : q 273734314 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2604)
                  by_cases hcut2606 : y ≤ q 273755115 scaleN
                  ·
                    apply V_pos_box_s3_s4 273734314 273755115
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2605, hcut2606⟩
                    · exact hne3
                    · exact hne4
                  ·
                    have hlo2607 : q 273755115 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2606)
                    apply V_pos_box_s3_s4 273755115 273775916
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2607, hcut2572⟩
                    · exact hne3
                    · exact hne4
        ·
          have hlo2573 : q 273775916 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2572)
          by_cases hcut2608 : y ≤ q 273931921 scaleN
          ·
            by_cases hcut2610 : y ≤ q 273859119 scaleN
            ·
              by_cases hcut2612 : y ≤ q 273817517 scaleN
              ·
                by_cases hcut2614 : y ≤ q 273796716 scaleN
                ·
                  apply V_pos_box_s3_s4 273775916 273796716
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2573, hcut2614⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2615 : q 273796716 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2614)
                  apply V_pos_box_s3_s4 273796716 273817517
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2615, hcut2612⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2613 : q 273817517 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2612)
                by_cases hcut2616 : y ≤ q 273838318 scaleN
                ·
                  apply V_pos_box_s3_s4 273817517 273838318
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2613, hcut2616⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2617 : q 273838318 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2616)
                  apply V_pos_box_s3_s4 273838318 273859119
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2617, hcut2610⟩
                  · exact hne3
                  · exact hne4
            ·
              have hlo2611 : q 273859119 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2610)
              by_cases hcut2618 : y ≤ q 273900720 scaleN
              ·
                by_cases hcut2620 : y ≤ q 273879919 scaleN
                ·
                  apply V_pos_box_s3_s4 273859119 273879919
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2611, hcut2620⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2621 : q 273879919 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2620)
                  apply V_pos_box_s3_s4 273879919 273900720
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2621, hcut2618⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2619 : q 273900720 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2618)
                by_cases hcut2622 : y ≤ q 273911120 scaleN
                ·
                  apply V_pos_box_s3_s4 273900720 273911120
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2619, hcut2622⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2623 : q 273911120 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2622)
                  by_cases hcut2624 : y ≤ q 273921521 scaleN
                  ·
                    apply V_pos_box_s3_s4 273911120 273921521
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2623, hcut2624⟩
                    · exact hne3
                    · exact hne4
                  ·
                    have hlo2625 : q 273921521 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2624)
                    apply V_pos_box_s3_s4 273921521 273931921
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2625, hcut2608⟩
                    · exact hne3
                    · exact hne4
          ·
            have hlo2609 : q 273931921 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2608)
            by_cases hcut2626 : y ≤ q 273973522 scaleN
            ·
              by_cases hcut2628 : y ≤ q 273952722 scaleN
              ·
                by_cases hcut2630 : y ≤ q 273942322 scaleN
                ·
                  apply V_pos_box_s3_s4 273931921 273942322
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2609, hcut2630⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2631 : q 273942322 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2630)
                  apply V_pos_box_s3_s4 273942322 273952722
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2631, hcut2628⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2629 : q 273952722 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2628)
                by_cases hcut2632 : y ≤ q 273963122 scaleN
                ·
                  apply V_pos_box_s3_s4 273952722 273963122
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2629, hcut2632⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2633 : q 273963122 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2632)
                  apply V_pos_box_s3_s4 273963122 273973522
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2633, hcut2626⟩
                  · exact hne3
                  · exact hne4
            ·
              have hlo2627 : q 273973522 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2626)
              by_cases hcut2634 : y ≤ q 273994323 scaleN
              ·
                by_cases hcut2636 : y ≤ q 273983923 scaleN
                ·
                  apply V_pos_box_s3_s4 273973522 273983923
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2627, hcut2636⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2637 : q 273983923 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2636)
                  apply V_pos_box_s3_s4 273983923 273994323
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2637, hcut2634⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2635 : q 273994323 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2634)
                by_cases hcut2638 : y ≤ q 274004724 scaleN
                ·
                  apply V_pos_box_s3_s4 273994323 274004724
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2635, hcut2638⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2639 : q 274004724 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2638)
                  by_cases hcut2640 : y ≤ q 274009924 scaleN
                  ·
                    apply V_pos_box_s3_s4 274004724 274009924
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2639, hcut2640⟩
                    · exact hne3
                    · exact hne4
                  ·
                    have hlo2641 : q 274009924 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2640)
                    apply V_pos_box_s3_s4 274009924 274015124
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2641, hcut2570⟩
                    · exact hne3
                    · exact hne4
      ·
        have hlo2571 : q 274015124 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2570)
        by_cases hcut2642 : y ≤ q 274100927 scaleN
        ·
          by_cases hcut2644 : y ≤ q 274061925 scaleN
          ·
            by_cases hcut2646 : y ≤ q 274035925 scaleN
            ·
              by_cases hcut2648 : y ≤ q 274025525 scaleN
              ·
                by_cases hcut2650 : y ≤ q 274020324 scaleN
                ·
                  apply V_pos_box_s3_s4 274015124 274020324
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2571, hcut2650⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2651 : q 274020324 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2650)
                  apply V_pos_box_s3_s4 274020324 274025525
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2651, hcut2648⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2649 : q 274025525 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2648)
                by_cases hcut2652 : y ≤ q 274030725 scaleN
                ·
                  apply V_pos_box_s3_s4 274025525 274030725
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2649, hcut2652⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2653 : q 274030725 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2652)
                  apply V_pos_box_s3_s4 274030725 274035925
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2653, hcut2646⟩
                  · exact hne3
                  · exact hne4
            ·
              have hlo2647 : q 274035925 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2646)
              by_cases hcut2654 : y ≤ q 274046325 scaleN
              ·
                by_cases hcut2656 : y ≤ q 274041125 scaleN
                ·
                  apply V_pos_box_s3_s4 274035925 274041125
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2647, hcut2656⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2657 : q 274041125 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2656)
                  apply V_pos_box_s3_s4 274041125 274046325
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2657, hcut2654⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2655 : q 274046325 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2654)
                by_cases hcut2658 : y ≤ q 274051525 scaleN
                ·
                  apply V_pos_box_s3_s4 274046325 274051525
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2655, hcut2658⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2659 : q 274051525 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2658)
                  by_cases hcut2660 : y ≤ q 274056725 scaleN
                  ·
                    apply V_pos_box_s3_s4 274051525 274056725
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2659, hcut2660⟩
                    · exact hne3
                    · exact hne4
                  ·
                    have hlo2661 : q 274056725 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2660)
                    apply V_pos_box_s3_s4 274056725 274061925
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2661, hcut2644⟩
                    · exact hne3
                    · exact hne4
          ·
            have hlo2645 : q 274061925 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2644)
            by_cases hcut2662 : y ≤ q 274082726 scaleN
            ·
              by_cases hcut2664 : y ≤ q 274072326 scaleN
              ·
                by_cases hcut2666 : y ≤ q 274067126 scaleN
                ·
                  apply V_pos_box_s3_s4 274061925 274067126
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2645, hcut2666⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2667 : q 274067126 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2666)
                  apply V_pos_box_s3_s4 274067126 274072326
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2667, hcut2664⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2665 : q 274072326 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2664)
                by_cases hcut2668 : y ≤ q 274077526 scaleN
                ·
                  apply V_pos_box_s3_s4 274072326 274077526
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2665, hcut2668⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2669 : q 274077526 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2668)
                  apply V_pos_box_s3_s4 274077526 274082726
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2669, hcut2662⟩
                  · exact hne3
                  · exact hne4
            ·
              have hlo2663 : q 274082726 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2662)
              by_cases hcut2670 : y ≤ q 274093127 scaleN
              ·
                by_cases hcut2672 : y ≤ q 274087927 scaleN
                ·
                  apply V_pos_box_s3_s4 274082726 274087927
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2663, hcut2672⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2673 : q 274087927 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2672)
                  apply V_pos_box_s3_s4 274087927 274093127
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2673, hcut2670⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2671 : q 274093127 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2670)
                by_cases hcut2674 : y ≤ q 274095727 scaleN
                ·
                  apply V_pos_box_s3_s4 274093127 274095727
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2671, hcut2674⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2675 : q 274095727 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2674)
                  by_cases hcut2676 : y ≤ q 274098327 scaleN
                  ·
                    apply V_pos_box_s3_s4 274095727 274098327
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2675, hcut2676⟩
                    · exact hne3
                    · exact hne4
                  ·
                    have hlo2677 : q 274098327 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2676)
                    apply V_pos_box_s3_s4 274098327 274100927
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2677, hcut2642⟩
                    · exact hne3
                    · exact hne4
        ·
          have hlo2643 : q 274100927 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2642)
          by_cases hcut2678 : y ≤ q 274124328 scaleN
          ·
            by_cases hcut2680 : y ≤ q 274111328 scaleN
            ·
              by_cases hcut2682 : y ≤ q 274106127 scaleN
              ·
                by_cases hcut2684 : y ≤ q 274103527 scaleN
                ·
                  apply V_pos_box_s3_s4 274100927 274103527
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2643, hcut2684⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2685 : q 274103527 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2684)
                  apply V_pos_box_s3_s4 274103527 274106127
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2685, hcut2682⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2683 : q 274106127 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2682)
                by_cases hcut2686 : y ≤ q 274108728 scaleN
                ·
                  apply V_pos_box_s3_s4 274106127 274108728
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2683, hcut2686⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2687 : q 274108728 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2686)
                  apply V_pos_box_s3_s4 274108728 274111328
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2687, hcut2680⟩
                  · exact hne3
                  · exact hne4
            ·
              have hlo2681 : q 274111328 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2680)
              by_cases hcut2688 : y ≤ q 274116528 scaleN
              ·
                by_cases hcut2690 : y ≤ q 274113928 scaleN
                ·
                  apply V_pos_box_s3_s4 274111328 274113928
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2681, hcut2690⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2691 : q 274113928 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2690)
                  apply V_pos_box_s3_s4 274113928 274116528
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2691, hcut2688⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2689 : q 274116528 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2688)
                by_cases hcut2692 : y ≤ q 274119128 scaleN
                ·
                  apply V_pos_box_s3_s4 274116528 274119128
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2689, hcut2692⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2693 : q 274119128 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2692)
                  by_cases hcut2694 : y ≤ q 274121728 scaleN
                  ·
                    apply V_pos_box_s3_s4 274119128 274121728
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2693, hcut2694⟩
                    · exact hne3
                    · exact hne4
                  ·
                    have hlo2695 : q 274121728 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2694)
                    apply V_pos_box_s3_s4 274121728 274124328
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2695, hcut2678⟩
                    · exact hne3
                    · exact hne4
          ·
            have hlo2679 : q 274124328 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2678)
            by_cases hcut2696 : y ≤ q 274134728 scaleN
            ·
              by_cases hcut2698 : y ≤ q 274129528 scaleN
              ·
                by_cases hcut2700 : y ≤ q 274126928 scaleN
                ·
                  apply V_pos_box_s3_s4 274124328 274126928
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2679, hcut2700⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2701 : q 274126928 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2700)
                  apply V_pos_box_s3_s4 274126928 274129528
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2701, hcut2698⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2699 : q 274129528 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2698)
                by_cases hcut2702 : y ≤ q 274132128 scaleN
                ·
                  apply V_pos_box_s3_s4 274129528 274132128
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2699, hcut2702⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2703 : q 274132128 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2702)
                  apply V_pos_box_s3_s4 274132128 274134728
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2703, hcut2696⟩
                  · exact hne3
                  · exact hne4
            ·
              have hlo2697 : q 274134728 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2696)
              by_cases hcut2704 : y ≤ q 274139928 scaleN
              ·
                by_cases hcut2706 : y ≤ q 274137328 scaleN
                ·
                  apply V_pos_box_s3_s4 274134728 274137328
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2697, hcut2706⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2707 : q 274137328 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2706)
                  apply V_pos_box_s3_s4 274137328 274139928
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2707, hcut2704⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2705 : q 274139928 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2704)
                by_cases hcut2708 : y ≤ q 274142528 scaleN
                ·
                  apply V_pos_box_s3_s4 274139928 274142528
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2705, hcut2708⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2709 : q 274142528 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2708)
                  by_cases hcut2710 : y ≤ q 274145128 scaleN
                  ·
                    apply V_pos_box_s3_s4 274142528 274145128
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2709, hcut2710⟩
                    · exact hne3
                    · exact hne4
                  ·
                    have hlo2711 : q 274145128 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2710)
                    apply V_pos_box_s3_s4 274145128 274147728
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2711, hcut2568⟩
                    · exact hne3
                    · exact hne4
    ·
      have hlo2569 : q 274147728 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2568)
      by_cases hcut2712 : y ≤ q 274203631 scaleN
      ·
        by_cases hcut2714 : y ≤ q 274180230 scaleN
        ·
          by_cases hcut2716 : y ≤ q 274168529 scaleN
          ·
            by_cases hcut2718 : y ≤ q 274158129 scaleN
            ·
              by_cases hcut2720 : y ≤ q 274152929 scaleN
              ·
                by_cases hcut2722 : y ≤ q 274150329 scaleN
                ·
                  apply V_pos_box_s3_s4 274147728 274150329
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2569, hcut2722⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2723 : q 274150329 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2722)
                  apply V_pos_box_s3_s4 274150329 274152929
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2723, hcut2720⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2721 : q 274152929 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2720)
                by_cases hcut2724 : y ≤ q 274155529 scaleN
                ·
                  apply V_pos_box_s3_s4 274152929 274155529
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2721, hcut2724⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2725 : q 274155529 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2724)
                  apply V_pos_box_s3_s4 274155529 274158129
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2725, hcut2718⟩
                  · exact hne3
                  · exact hne4
            ·
              have hlo2719 : q 274158129 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2718)
              by_cases hcut2726 : y ≤ q 274163329 scaleN
              ·
                by_cases hcut2728 : y ≤ q 274160729 scaleN
                ·
                  apply V_pos_box_s3_s4 274158129 274160729
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2719, hcut2728⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2729 : q 274160729 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2728)
                  apply V_pos_box_s3_s4 274160729 274163329
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2729, hcut2726⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2727 : q 274163329 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2726)
                by_cases hcut2730 : y ≤ q 274165929 scaleN
                ·
                  apply V_pos_box_s3_s4 274163329 274165929
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2727, hcut2730⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2731 : q 274165929 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2730)
                  by_cases hcut2732 : y ≤ q 274167229 scaleN
                  ·
                    apply V_pos_box_s3_s4 274165929 274167229
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2731, hcut2732⟩
                    · exact hne3
                    · exact hne4
                  ·
                    have hlo2733 : q 274167229 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2732)
                    apply V_pos_box_s3_s4 274167229 274168529
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2733, hcut2716⟩
                    · exact hne3
                    · exact hne4
          ·
            have hlo2717 : q 274168529 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2716)
            by_cases hcut2734 : y ≤ q 274173730 scaleN
            ·
              by_cases hcut2736 : y ≤ q 274171130 scaleN
              ·
                by_cases hcut2738 : y ≤ q 274169829 scaleN
                ·
                  apply V_pos_box_s3_s4 274168529 274169829
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2717, hcut2738⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2739 : q 274169829 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2738)
                  apply V_pos_box_s3_s4 274169829 274171130
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2739, hcut2736⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2737 : q 274171130 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2736)
                by_cases hcut2740 : y ≤ q 274172430 scaleN
                ·
                  apply V_pos_box_s3_s4 274171130 274172430
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2737, hcut2740⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2741 : q 274172430 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2740)
                  apply V_pos_box_s3_s4 274172430 274173730
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2741, hcut2734⟩
                  · exact hne3
                  · exact hne4
            ·
              have hlo2735 : q 274173730 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2734)
              by_cases hcut2742 : y ≤ q 274176330 scaleN
              ·
                by_cases hcut2744 : y ≤ q 274175030 scaleN
                ·
                  apply V_pos_box_s3_s4 274173730 274175030
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2735, hcut2744⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2745 : q 274175030 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2744)
                  apply V_pos_box_s3_s4 274175030 274176330
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2745, hcut2742⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2743 : q 274176330 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2742)
                by_cases hcut2746 : y ≤ q 274177630 scaleN
                ·
                  apply V_pos_box_s3_s4 274176330 274177630
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2743, hcut2746⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2747 : q 274177630 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2746)
                  by_cases hcut2748 : y ≤ q 274178930 scaleN
                  ·
                    apply V_pos_box_s3_s4 274177630 274178930
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2747, hcut2748⟩
                    · exact hne3
                    · exact hne4
                  ·
                    have hlo2749 : q 274178930 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2748)
                    apply V_pos_box_s3_s4 274178930 274180230
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2749, hcut2714⟩
                    · exact hne3
                    · exact hne4
        ·
          have hlo2715 : q 274180230 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2714)
          by_cases hcut2750 : y ≤ q 274191931 scaleN
          ·
            by_cases hcut2752 : y ≤ q 274185430 scaleN
            ·
              by_cases hcut2754 : y ≤ q 274182830 scaleN
              ·
                by_cases hcut2756 : y ≤ q 274181530 scaleN
                ·
                  apply V_pos_box_s3_s4 274180230 274181530
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2715, hcut2756⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2757 : q 274181530 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2756)
                  apply V_pos_box_s3_s4 274181530 274182830
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2757, hcut2754⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2755 : q 274182830 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2754)
                by_cases hcut2758 : y ≤ q 274184130 scaleN
                ·
                  apply V_pos_box_s3_s4 274182830 274184130
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2755, hcut2758⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2759 : q 274184130 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2758)
                  apply V_pos_box_s3_s4 274184130 274185430
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2759, hcut2752⟩
                  · exact hne3
                  · exact hne4
            ·
              have hlo2753 : q 274185430 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2752)
              by_cases hcut2760 : y ≤ q 274188030 scaleN
              ·
                by_cases hcut2762 : y ≤ q 274186730 scaleN
                ·
                  apply V_pos_box_s3_s4 274185430 274186730
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2753, hcut2762⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2763 : q 274186730 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2762)
                  apply V_pos_box_s3_s4 274186730 274188030
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2763, hcut2760⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2761 : q 274188030 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2760)
                by_cases hcut2764 : y ≤ q 274189330 scaleN
                ·
                  apply V_pos_box_s3_s4 274188030 274189330
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2761, hcut2764⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2765 : q 274189330 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2764)
                  by_cases hcut2766 : y ≤ q 274190630 scaleN
                  ·
                    apply V_pos_box_s3_s4 274189330 274190630
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2765, hcut2766⟩
                    · exact hne3
                    · exact hne4
                  ·
                    have hlo2767 : q 274190630 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2766)
                    apply V_pos_box_s3_s4 274190630 274191931
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2767, hcut2750⟩
                    · exact hne3
                    · exact hne4
          ·
            have hlo2751 : q 274191931 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2750)
            by_cases hcut2768 : y ≤ q 274197131 scaleN
            ·
              by_cases hcut2770 : y ≤ q 274194531 scaleN
              ·
                by_cases hcut2772 : y ≤ q 274193231 scaleN
                ·
                  apply V_pos_box_s3_s4 274191931 274193231
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2751, hcut2772⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2773 : q 274193231 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2772)
                  apply V_pos_box_s3_s4 274193231 274194531
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2773, hcut2770⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2771 : q 274194531 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2770)
                by_cases hcut2774 : y ≤ q 274195831 scaleN
                ·
                  apply V_pos_box_s3_s4 274194531 274195831
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2771, hcut2774⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2775 : q 274195831 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2774)
                  apply V_pos_box_s3_s4 274195831 274197131
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2775, hcut2768⟩
                  · exact hne3
                  · exact hne4
            ·
              have hlo2769 : q 274197131 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2768)
              by_cases hcut2776 : y ≤ q 274199731 scaleN
              ·
                by_cases hcut2778 : y ≤ q 274198431 scaleN
                ·
                  apply V_pos_box_s3_s4 274197131 274198431
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2769, hcut2778⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2779 : q 274198431 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2778)
                  apply V_pos_box_s3_s4 274198431 274199731
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2779, hcut2776⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2777 : q 274199731 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2776)
                by_cases hcut2780 : y ≤ q 274201031 scaleN
                ·
                  apply V_pos_box_s3_s4 274199731 274201031
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2777, hcut2780⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2781 : q 274201031 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2780)
                  by_cases hcut2782 : y ≤ q 274202331 scaleN
                  ·
                    apply V_pos_box_s3_s4 274201031 274202331
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2781, hcut2782⟩
                    · exact hne3
                    · exact hne4
                  ·
                    have hlo2783 : q 274202331 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2782)
                    apply V_pos_box_s3_s4 274202331 274203631
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2783, hcut2712⟩
                    · exact hne3
                    · exact hne4
      ·
        have hlo2713 : q 274203631 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2712)
        by_cases hcut2784 : y ≤ q 274227031 scaleN
        ·
          by_cases hcut2786 : y ≤ q 274215331 scaleN
          ·
            by_cases hcut2788 : y ≤ q 274208831 scaleN
            ·
              by_cases hcut2790 : y ≤ q 274206231 scaleN
              ·
                by_cases hcut2792 : y ≤ q 274204931 scaleN
                ·
                  apply V_pos_box_s3_s4 274203631 274204931
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2713, hcut2792⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2793 : q 274204931 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2792)
                  apply V_pos_box_s3_s4 274204931 274206231
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2793, hcut2790⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2791 : q 274206231 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2790)
                by_cases hcut2794 : y ≤ q 274207531 scaleN
                ·
                  apply V_pos_box_s3_s4 274206231 274207531
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2791, hcut2794⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2795 : q 274207531 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2794)
                  apply V_pos_box_s3_s4 274207531 274208831
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2795, hcut2788⟩
                  · exact hne3
                  · exact hne4
            ·
              have hlo2789 : q 274208831 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2788)
              by_cases hcut2796 : y ≤ q 274211431 scaleN
              ·
                by_cases hcut2798 : y ≤ q 274210131 scaleN
                ·
                  apply V_pos_box_s3_s4 274208831 274210131
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2789, hcut2798⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2799 : q 274210131 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2798)
                  apply V_pos_box_s3_s4 274210131 274211431
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2799, hcut2796⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2797 : q 274211431 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2796)
                by_cases hcut2800 : y ≤ q 274212731 scaleN
                ·
                  apply V_pos_box_s3_s4 274211431 274212731
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2797, hcut2800⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2801 : q 274212731 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2800)
                  by_cases hcut2802 : y ≤ q 274214031 scaleN
                  ·
                    apply V_pos_box_s3_s4 274212731 274214031
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2801, hcut2802⟩
                    · exact hne3
                    · exact hne4
                  ·
                    have hlo2803 : q 274214031 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2802)
                    apply V_pos_box_s3_s4 274214031 274215331
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2803, hcut2786⟩
                    · exact hne3
                    · exact hne4
          ·
            have hlo2787 : q 274215331 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2786)
            by_cases hcut2804 : y ≤ q 274220531 scaleN
            ·
              by_cases hcut2806 : y ≤ q 274217931 scaleN
              ·
                by_cases hcut2808 : y ≤ q 274216631 scaleN
                ·
                  apply V_pos_box_s3_s4 274215331 274216631
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2787, hcut2808⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2809 : q 274216631 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2808)
                  apply V_pos_box_s3_s4 274216631 274217931
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2809, hcut2806⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2807 : q 274217931 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2806)
                by_cases hcut2810 : y ≤ q 274219231 scaleN
                ·
                  apply V_pos_box_s3_s4 274217931 274219231
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2807, hcut2810⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2811 : q 274219231 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2810)
                  apply V_pos_box_s3_s4 274219231 274220531
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2811, hcut2804⟩
                  · exact hne3
                  · exact hne4
            ·
              have hlo2805 : q 274220531 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2804)
              by_cases hcut2812 : y ≤ q 274223131 scaleN
              ·
                by_cases hcut2814 : y ≤ q 274221831 scaleN
                ·
                  apply V_pos_box_s3_s4 274220531 274221831
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2805, hcut2814⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2815 : q 274221831 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2814)
                  apply V_pos_box_s3_s4 274221831 274223131
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2815, hcut2812⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2813 : q 274223131 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2812)
                by_cases hcut2816 : y ≤ q 274224431 scaleN
                ·
                  apply V_pos_box_s3_s4 274223131 274224431
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2813, hcut2816⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2817 : q 274224431 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2816)
                  by_cases hcut2818 : y ≤ q 274225731 scaleN
                  ·
                    apply V_pos_box_s3_s4 274224431 274225731
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2817, hcut2818⟩
                    · exact hne3
                    · exact hne4
                  ·
                    have hlo2819 : q 274225731 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2818)
                    apply V_pos_box_s3_s4 274225731 274227031
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2819, hcut2784⟩
                    · exact hne3
                    · exact hne4
        ·
          have hlo2785 : q 274227031 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2784)
          by_cases hcut2820 : y ≤ q 274238732 scaleN
          ·
            by_cases hcut2822 : y ≤ q 274232231 scaleN
            ·
              by_cases hcut2824 : y ≤ q 274229631 scaleN
              ·
                by_cases hcut2826 : y ≤ q 274228331 scaleN
                ·
                  apply V_pos_box_s3_s4 274227031 274228331
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2785, hcut2826⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2827 : q 274228331 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2826)
                  apply V_pos_box_s3_s4 274228331 274229631
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2827, hcut2824⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2825 : q 274229631 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2824)
                by_cases hcut2828 : y ≤ q 274230931 scaleN
                ·
                  apply V_pos_box_s3_s4 274229631 274230931
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2825, hcut2828⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2829 : q 274230931 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2828)
                  apply V_pos_box_s3_s4 274230931 274232231
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2829, hcut2822⟩
                  · exact hne3
                  · exact hne4
            ·
              have hlo2823 : q 274232231 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2822)
              by_cases hcut2830 : y ≤ q 274234832 scaleN
              ·
                by_cases hcut2832 : y ≤ q 274233532 scaleN
                ·
                  apply V_pos_box_s3_s4 274232231 274233532
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2823, hcut2832⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2833 : q 274233532 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2832)
                  apply V_pos_box_s3_s4 274233532 274234832
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2833, hcut2830⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2831 : q 274234832 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2830)
                by_cases hcut2834 : y ≤ q 274236132 scaleN
                ·
                  apply V_pos_box_s3_s4 274234832 274236132
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2831, hcut2834⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2835 : q 274236132 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2834)
                  by_cases hcut2836 : y ≤ q 274237432 scaleN
                  ·
                    apply V_pos_box_s3_s4 274236132 274237432
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2835, hcut2836⟩
                    · exact hne3
                    · exact hne4
                  ·
                    have hlo2837 : q 274237432 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2836)
                    apply V_pos_box_s3_s4 274237432 274238732
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2837, hcut2820⟩
                    · exact hne3
                    · exact hne4
          ·
            have hlo2821 : q 274238732 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2820)
            by_cases hcut2838 : y ≤ q 274243932 scaleN
            ·
              by_cases hcut2840 : y ≤ q 274241332 scaleN
              ·
                by_cases hcut2842 : y ≤ q 274240032 scaleN
                ·
                  apply V_pos_box_s3_s4 274238732 274240032
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2821, hcut2842⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2843 : q 274240032 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2842)
                  apply V_pos_box_s3_s4 274240032 274241332
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2843, hcut2840⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2841 : q 274241332 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2840)
                by_cases hcut2844 : y ≤ q 274242632 scaleN
                ·
                  apply V_pos_box_s3_s4 274241332 274242632
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2841, hcut2844⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2845 : q 274242632 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2844)
                  apply V_pos_box_s3_s4 274242632 274243932
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2845, hcut2838⟩
                  · exact hne3
                  · exact hne4
            ·
              have hlo2839 : q 274243932 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2838)
              by_cases hcut2846 : y ≤ q 274246532 scaleN
              ·
                by_cases hcut2848 : y ≤ q 274245232 scaleN
                ·
                  apply V_pos_box_s3_s4 274243932 274245232
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2839, hcut2848⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2849 : q 274245232 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2848)
                  apply V_pos_box_s3_s4 274245232 274246532
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2849, hcut2846⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2847 : q 274246532 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2846)
                by_cases hcut2850 : y ≤ q 274247832 scaleN
                ·
                  apply V_pos_box_s3_s4 274246532 274247832
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2847, hcut2850⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2851 : q 274247832 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2850)
                  by_cases hcut2852 : y ≤ q 274249132 scaleN
                  ·
                    apply V_pos_box_s3_s4 274247832 274249132
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2851, hcut2852⟩
                    · exact hne3
                    · exact hne4
                  ·
                    have hlo2853 : q 274249132 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2852)
                    apply V_pos_box_s3_s4 274249132 274250432
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2853, hcut2566⟩
                    · exact hne3
                    · exact hne4
  ·
    have hlo2567 : q 274250432 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2566)
    by_cases hcut2854 : y ≤ q 274353137 scaleN
    ·
      by_cases hcut2856 : y ≤ q 274297235 scaleN
      ·
        by_cases hcut2858 : y ≤ q 274273833 scaleN
        ·
          by_cases hcut2860 : y ≤ q 274262133 scaleN
          ·
            by_cases hcut2862 : y ≤ q 274255633 scaleN
            ·
              by_cases hcut2864 : y ≤ q 274253032 scaleN
              ·
                by_cases hcut2866 : y ≤ q 274251732 scaleN
                ·
                  apply V_pos_box_s3_s4 274250432 274251732
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2567, hcut2866⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2867 : q 274251732 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2866)
                  apply V_pos_box_s3_s4 274251732 274253032
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2867, hcut2864⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2865 : q 274253032 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2864)
                by_cases hcut2868 : y ≤ q 274254333 scaleN
                ·
                  apply V_pos_box_s3_s4 274253032 274254333
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2865, hcut2868⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2869 : q 274254333 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2868)
                  apply V_pos_box_s3_s4 274254333 274255633
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2869, hcut2862⟩
                  · exact hne3
                  · exact hne4
            ·
              have hlo2863 : q 274255633 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2862)
              by_cases hcut2870 : y ≤ q 274258233 scaleN
              ·
                by_cases hcut2872 : y ≤ q 274256933 scaleN
                ·
                  apply V_pos_box_s3_s4 274255633 274256933
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2863, hcut2872⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2873 : q 274256933 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2872)
                  apply V_pos_box_s3_s4 274256933 274258233
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2873, hcut2870⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2871 : q 274258233 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2870)
                by_cases hcut2874 : y ≤ q 274259533 scaleN
                ·
                  apply V_pos_box_s3_s4 274258233 274259533
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2871, hcut2874⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2875 : q 274259533 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2874)
                  by_cases hcut2876 : y ≤ q 274260833 scaleN
                  ·
                    apply V_pos_box_s3_s4 274259533 274260833
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2875, hcut2876⟩
                    · exact hne3
                    · exact hne4
                  ·
                    have hlo2877 : q 274260833 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2876)
                    apply V_pos_box_s3_s4 274260833 274262133
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2877, hcut2860⟩
                    · exact hne3
                    · exact hne4
          ·
            have hlo2861 : q 274262133 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2860)
            by_cases hcut2878 : y ≤ q 274267333 scaleN
            ·
              by_cases hcut2880 : y ≤ q 274264733 scaleN
              ·
                by_cases hcut2882 : y ≤ q 274263433 scaleN
                ·
                  apply V_pos_box_s3_s4 274262133 274263433
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2861, hcut2882⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2883 : q 274263433 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2882)
                  apply V_pos_box_s3_s4 274263433 274264733
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2883, hcut2880⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2881 : q 274264733 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2880)
                by_cases hcut2884 : y ≤ q 274266033 scaleN
                ·
                  apply V_pos_box_s3_s4 274264733 274266033
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2881, hcut2884⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2885 : q 274266033 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2884)
                  apply V_pos_box_s3_s4 274266033 274267333
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2885, hcut2878⟩
                  · exact hne3
                  · exact hne4
            ·
              have hlo2879 : q 274267333 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2878)
              by_cases hcut2886 : y ≤ q 274269933 scaleN
              ·
                by_cases hcut2888 : y ≤ q 274268633 scaleN
                ·
                  apply V_pos_box_s3_s4 274267333 274268633
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2879, hcut2888⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2889 : q 274268633 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2888)
                  apply V_pos_box_s3_s4 274268633 274269933
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2889, hcut2886⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2887 : q 274269933 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2886)
                by_cases hcut2890 : y ≤ q 274271233 scaleN
                ·
                  apply V_pos_box_s3_s4 274269933 274271233
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2887, hcut2890⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2891 : q 274271233 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2890)
                  by_cases hcut2892 : y ≤ q 274272533 scaleN
                  ·
                    apply V_pos_box_s3_s4 274271233 274272533
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2891, hcut2892⟩
                    · exact hne3
                    · exact hne4
                  ·
                    have hlo2893 : q 274272533 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2892)
                    apply V_pos_box_s3_s4 274272533 274273833
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2893, hcut2858⟩
                    · exact hne3
                    · exact hne4
        ·
          have hlo2859 : q 274273833 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2858)
          by_cases hcut2894 : y ≤ q 274285534 scaleN
          ·
            by_cases hcut2896 : y ≤ q 274279034 scaleN
            ·
              by_cases hcut2898 : y ≤ q 274276434 scaleN
              ·
                by_cases hcut2900 : y ≤ q 274275134 scaleN
                ·
                  apply V_pos_box_s3_s4 274273833 274275134
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2859, hcut2900⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2901 : q 274275134 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2900)
                  apply V_pos_box_s3_s4 274275134 274276434
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2901, hcut2898⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2899 : q 274276434 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2898)
                by_cases hcut2902 : y ≤ q 274277734 scaleN
                ·
                  apply V_pos_box_s3_s4 274276434 274277734
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2899, hcut2902⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2903 : q 274277734 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2902)
                  apply V_pos_box_s3_s4 274277734 274279034
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2903, hcut2896⟩
                  · exact hne3
                  · exact hne4
            ·
              have hlo2897 : q 274279034 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2896)
              by_cases hcut2904 : y ≤ q 274281634 scaleN
              ·
                by_cases hcut2906 : y ≤ q 274280334 scaleN
                ·
                  apply V_pos_box_s3_s4 274279034 274280334
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2897, hcut2906⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2907 : q 274280334 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2906)
                  apply V_pos_box_s3_s4 274280334 274281634
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2907, hcut2904⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2905 : q 274281634 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2904)
                by_cases hcut2908 : y ≤ q 274282934 scaleN
                ·
                  apply V_pos_box_s3_s4 274281634 274282934
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2905, hcut2908⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2909 : q 274282934 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2908)
                  by_cases hcut2910 : y ≤ q 274284234 scaleN
                  ·
                    apply V_pos_box_s3_s4 274282934 274284234
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2909, hcut2910⟩
                    · exact hne3
                    · exact hne4
                  ·
                    have hlo2911 : q 274284234 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2910)
                    apply V_pos_box_s3_s4 274284234 274285534
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2911, hcut2894⟩
                    · exact hne3
                    · exact hne4
          ·
            have hlo2895 : q 274285534 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2894)
            by_cases hcut2912 : y ≤ q 274290734 scaleN
            ·
              by_cases hcut2914 : y ≤ q 274288134 scaleN
              ·
                by_cases hcut2916 : y ≤ q 274286834 scaleN
                ·
                  apply V_pos_box_s3_s4 274285534 274286834
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2895, hcut2916⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2917 : q 274286834 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2916)
                  apply V_pos_box_s3_s4 274286834 274288134
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2917, hcut2914⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2915 : q 274288134 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2914)
                by_cases hcut2918 : y ≤ q 274289434 scaleN
                ·
                  apply V_pos_box_s3_s4 274288134 274289434
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2915, hcut2918⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2919 : q 274289434 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2918)
                  apply V_pos_box_s3_s4 274289434 274290734
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2919, hcut2912⟩
                  · exact hne3
                  · exact hne4
            ·
              have hlo2913 : q 274290734 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2912)
              by_cases hcut2920 : y ≤ q 274293334 scaleN
              ·
                by_cases hcut2922 : y ≤ q 274292034 scaleN
                ·
                  apply V_pos_box_s3_s4 274290734 274292034
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2913, hcut2922⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2923 : q 274292034 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2922)
                  apply V_pos_box_s3_s4 274292034 274293334
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2923, hcut2920⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2921 : q 274293334 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2920)
                by_cases hcut2924 : y ≤ q 274294634 scaleN
                ·
                  apply V_pos_box_s3_s4 274293334 274294634
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2921, hcut2924⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2925 : q 274294634 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2924)
                  by_cases hcut2926 : y ≤ q 274295935 scaleN
                  ·
                    apply V_pos_box_s3_s4 274294634 274295935
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2925, hcut2926⟩
                    · exact hne3
                    · exact hne4
                  ·
                    have hlo2927 : q 274295935 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2926)
                    apply V_pos_box_s3_s4 274295935 274297235
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2927, hcut2856⟩
                    · exact hne3
                    · exact hne4
      ·
        have hlo2857 : q 274297235 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2856)
        by_cases hcut2928 : y ≤ q 274320636 scaleN
        ·
          by_cases hcut2930 : y ≤ q 274308935 scaleN
          ·
            by_cases hcut2932 : y ≤ q 274302435 scaleN
            ·
              by_cases hcut2934 : y ≤ q 274299835 scaleN
              ·
                by_cases hcut2936 : y ≤ q 274298535 scaleN
                ·
                  apply V_pos_box_s3_s4 274297235 274298535
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2857, hcut2936⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2937 : q 274298535 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2936)
                  apply V_pos_box_s3_s4 274298535 274299835
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2937, hcut2934⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2935 : q 274299835 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2934)
                by_cases hcut2938 : y ≤ q 274301135 scaleN
                ·
                  apply V_pos_box_s3_s4 274299835 274301135
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2935, hcut2938⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2939 : q 274301135 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2938)
                  apply V_pos_box_s3_s4 274301135 274302435
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2939, hcut2932⟩
                  · exact hne3
                  · exact hne4
            ·
              have hlo2933 : q 274302435 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2932)
              by_cases hcut2940 : y ≤ q 274305035 scaleN
              ·
                by_cases hcut2942 : y ≤ q 274303735 scaleN
                ·
                  apply V_pos_box_s3_s4 274302435 274303735
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2933, hcut2942⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2943 : q 274303735 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2942)
                  apply V_pos_box_s3_s4 274303735 274305035
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2943, hcut2940⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2941 : q 274305035 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2940)
                by_cases hcut2944 : y ≤ q 274306335 scaleN
                ·
                  apply V_pos_box_s3_s4 274305035 274306335
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2941, hcut2944⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2945 : q 274306335 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2944)
                  by_cases hcut2946 : y ≤ q 274307635 scaleN
                  ·
                    apply V_pos_box_s3_s4 274306335 274307635
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2945, hcut2946⟩
                    · exact hne3
                    · exact hne4
                  ·
                    have hlo2947 : q 274307635 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2946)
                    apply V_pos_box_s3_s4 274307635 274308935
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2947, hcut2930⟩
                    · exact hne3
                    · exact hne4
          ·
            have hlo2931 : q 274308935 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2930)
            by_cases hcut2948 : y ≤ q 274314135 scaleN
            ·
              by_cases hcut2950 : y ≤ q 274311535 scaleN
              ·
                by_cases hcut2952 : y ≤ q 274310235 scaleN
                ·
                  apply V_pos_box_s3_s4 274308935 274310235
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2931, hcut2952⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2953 : q 274310235 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2952)
                  apply V_pos_box_s3_s4 274310235 274311535
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2953, hcut2950⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2951 : q 274311535 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2950)
                by_cases hcut2954 : y ≤ q 274312835 scaleN
                ·
                  apply V_pos_box_s3_s4 274311535 274312835
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2951, hcut2954⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2955 : q 274312835 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2954)
                  apply V_pos_box_s3_s4 274312835 274314135
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2955, hcut2948⟩
                  · exact hne3
                  · exact hne4
            ·
              have hlo2949 : q 274314135 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2948)
              by_cases hcut2956 : y ≤ q 274316736 scaleN
              ·
                by_cases hcut2958 : y ≤ q 274315435 scaleN
                ·
                  apply V_pos_box_s3_s4 274314135 274315435
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2949, hcut2958⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2959 : q 274315435 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2958)
                  apply V_pos_box_s3_s4 274315435 274316736
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2959, hcut2956⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2957 : q 274316736 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2956)
                by_cases hcut2960 : y ≤ q 274318036 scaleN
                ·
                  apply V_pos_box_s3_s4 274316736 274318036
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2957, hcut2960⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2961 : q 274318036 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2960)
                  by_cases hcut2962 : y ≤ q 274319336 scaleN
                  ·
                    apply V_pos_box_s3_s4 274318036 274319336
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2961, hcut2962⟩
                    · exact hne3
                    · exact hne4
                  ·
                    have hlo2963 : q 274319336 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2962)
                    apply V_pos_box_s3_s4 274319336 274320636
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2963, hcut2928⟩
                    · exact hne3
                    · exact hne4
        ·
          have hlo2929 : q 274320636 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2928)
          by_cases hcut2964 : y ≤ q 274332336 scaleN
          ·
            by_cases hcut2966 : y ≤ q 274325836 scaleN
            ·
              by_cases hcut2968 : y ≤ q 274323236 scaleN
              ·
                by_cases hcut2970 : y ≤ q 274321936 scaleN
                ·
                  apply V_pos_box_s3_s4 274320636 274321936
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2929, hcut2970⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2971 : q 274321936 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2970)
                  apply V_pos_box_s3_s4 274321936 274323236
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2971, hcut2968⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2969 : q 274323236 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2968)
                by_cases hcut2972 : y ≤ q 274324536 scaleN
                ·
                  apply V_pos_box_s3_s4 274323236 274324536
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2969, hcut2972⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2973 : q 274324536 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2972)
                  apply V_pos_box_s3_s4 274324536 274325836
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2973, hcut2966⟩
                  · exact hne3
                  · exact hne4
            ·
              have hlo2967 : q 274325836 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2966)
              by_cases hcut2974 : y ≤ q 274328436 scaleN
              ·
                by_cases hcut2976 : y ≤ q 274327136 scaleN
                ·
                  apply V_pos_box_s3_s4 274325836 274327136
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2967, hcut2976⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2977 : q 274327136 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2976)
                  apply V_pos_box_s3_s4 274327136 274328436
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2977, hcut2974⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2975 : q 274328436 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2974)
                by_cases hcut2978 : y ≤ q 274329736 scaleN
                ·
                  apply V_pos_box_s3_s4 274328436 274329736
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2975, hcut2978⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2979 : q 274329736 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2978)
                  by_cases hcut2980 : y ≤ q 274331036 scaleN
                  ·
                    apply V_pos_box_s3_s4 274329736 274331036
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2979, hcut2980⟩
                    · exact hne3
                    · exact hne4
                  ·
                    have hlo2981 : q 274331036 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2980)
                    apply V_pos_box_s3_s4 274331036 274332336
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2981, hcut2964⟩
                    · exact hne3
                    · exact hne4
          ·
            have hlo2965 : q 274332336 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2964)
            by_cases hcut2982 : y ≤ q 274340137 scaleN
            ·
              by_cases hcut2984 : y ≤ q 274334936 scaleN
              ·
                by_cases hcut2986 : y ≤ q 274333636 scaleN
                ·
                  apply V_pos_box_s3_s4 274332336 274333636
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2965, hcut2986⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2987 : q 274333636 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2986)
                  apply V_pos_box_s3_s4 274333636 274334936
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2987, hcut2984⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2985 : q 274334936 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2984)
                by_cases hcut2988 : y ≤ q 274337537 scaleN
                ·
                  apply V_pos_box_s3_s4 274334936 274337537
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2985, hcut2988⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2989 : q 274337537 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2988)
                  apply V_pos_box_s3_s4 274337537 274340137
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2989, hcut2982⟩
                  · exact hne3
                  · exact hne4
            ·
              have hlo2983 : q 274340137 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2982)
              by_cases hcut2990 : y ≤ q 274345337 scaleN
              ·
                by_cases hcut2992 : y ≤ q 274342737 scaleN
                ·
                  apply V_pos_box_s3_s4 274340137 274342737
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2983, hcut2992⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2993 : q 274342737 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2992)
                  apply V_pos_box_s3_s4 274342737 274345337
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2993, hcut2990⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo2991 : q 274345337 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2990)
                by_cases hcut2994 : y ≤ q 274347937 scaleN
                ·
                  apply V_pos_box_s3_s4 274345337 274347937
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2991, hcut2994⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo2995 : q 274347937 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2994)
                  by_cases hcut2996 : y ≤ q 274350537 scaleN
                  ·
                    apply V_pos_box_s3_s4 274347937 274350537
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2995, hcut2996⟩
                    · exact hne3
                    · exact hne4
                  ·
                    have hlo2997 : q 274350537 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2996)
                    apply V_pos_box_s3_s4 274350537 274353137
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo2997, hcut2854⟩
                    · exact hne3
                    · exact hne4
    ·
      have hlo2855 : q 274353137 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2854)
      by_cases hcut2998 : y ≤ q 274488342 scaleN
      ·
        by_cases hcut3000 : y ≤ q 274399939 scaleN
        ·
          by_cases hcut3002 : y ≤ q 274376538 scaleN
          ·
            by_cases hcut3004 : y ≤ q 274363538 scaleN
            ·
              by_cases hcut3006 : y ≤ q 274358338 scaleN
              ·
                by_cases hcut3008 : y ≤ q 274355737 scaleN
                ·
                  apply V_pos_box_s3_s4 274353137 274355737
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2855, hcut3008⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo3009 : q 274355737 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3008)
                  apply V_pos_box_s3_s4 274355737 274358338
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3009, hcut3006⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo3007 : q 274358338 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3006)
                by_cases hcut3010 : y ≤ q 274360938 scaleN
                ·
                  apply V_pos_box_s3_s4 274358338 274360938
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3007, hcut3010⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo3011 : q 274360938 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3010)
                  apply V_pos_box_s3_s4 274360938 274363538
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3011, hcut3004⟩
                  · exact hne3
                  · exact hne4
            ·
              have hlo3005 : q 274363538 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3004)
              by_cases hcut3012 : y ≤ q 274368738 scaleN
              ·
                by_cases hcut3014 : y ≤ q 274366138 scaleN
                ·
                  apply V_pos_box_s3_s4 274363538 274366138
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3005, hcut3014⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo3015 : q 274366138 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3014)
                  apply V_pos_box_s3_s4 274366138 274368738
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3015, hcut3012⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo3013 : q 274368738 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3012)
                by_cases hcut3016 : y ≤ q 274371338 scaleN
                ·
                  apply V_pos_box_s3_s4 274368738 274371338
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3013, hcut3016⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo3017 : q 274371338 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3016)
                  by_cases hcut3018 : y ≤ q 274373938 scaleN
                  ·
                    apply V_pos_box_s3_s4 274371338 274373938
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo3017, hcut3018⟩
                    · exact hne3
                    · exact hne4
                  ·
                    have hlo3019 : q 274373938 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3018)
                    apply V_pos_box_s3_s4 274373938 274376538
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo3019, hcut3002⟩
                    · exact hne3
                    · exact hne4
          ·
            have hlo3003 : q 274376538 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3002)
            by_cases hcut3020 : y ≤ q 274386938 scaleN
            ·
              by_cases hcut3022 : y ≤ q 274381738 scaleN
              ·
                by_cases hcut3024 : y ≤ q 274379138 scaleN
                ·
                  apply V_pos_box_s3_s4 274376538 274379138
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3003, hcut3024⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo3025 : q 274379138 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3024)
                  apply V_pos_box_s3_s4 274379138 274381738
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3025, hcut3022⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo3023 : q 274381738 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3022)
                by_cases hcut3026 : y ≤ q 274384338 scaleN
                ·
                  apply V_pos_box_s3_s4 274381738 274384338
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3023, hcut3026⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo3027 : q 274384338 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3026)
                  apply V_pos_box_s3_s4 274384338 274386938
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3027, hcut3020⟩
                  · exact hne3
                  · exact hne4
            ·
              have hlo3021 : q 274386938 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3020)
              by_cases hcut3028 : y ≤ q 274392138 scaleN
              ·
                by_cases hcut3030 : y ≤ q 274389538 scaleN
                ·
                  apply V_pos_box_s3_s4 274386938 274389538
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3021, hcut3030⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo3031 : q 274389538 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3030)
                  apply V_pos_box_s3_s4 274389538 274392138
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3031, hcut3028⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo3029 : q 274392138 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3028)
                by_cases hcut3032 : y ≤ q 274394738 scaleN
                ·
                  apply V_pos_box_s3_s4 274392138 274394738
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3029, hcut3032⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo3033 : q 274394738 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3032)
                  by_cases hcut3034 : y ≤ q 274397338 scaleN
                  ·
                    apply V_pos_box_s3_s4 274394738 274397338
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo3033, hcut3034⟩
                    · exact hne3
                    · exact hne4
                  ·
                    have hlo3035 : q 274397338 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3034)
                    apply V_pos_box_s3_s4 274397338 274399939
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo3035, hcut3000⟩
                    · exact hne3
                    · exact hne4
        ·
          have hlo3001 : q 274399939 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3000)
          by_cases hcut3036 : y ≤ q 274441541 scaleN
          ·
            by_cases hcut3038 : y ≤ q 274415539 scaleN
            ·
              by_cases hcut3040 : y ≤ q 274405139 scaleN
              ·
                by_cases hcut3042 : y ≤ q 274402539 scaleN
                ·
                  apply V_pos_box_s3_s4 274399939 274402539
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3001, hcut3042⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo3043 : q 274402539 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3042)
                  apply V_pos_box_s3_s4 274402539 274405139
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3043, hcut3040⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo3041 : q 274405139 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3040)
                by_cases hcut3044 : y ≤ q 274410339 scaleN
                ·
                  apply V_pos_box_s3_s4 274405139 274410339
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3041, hcut3044⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo3045 : q 274410339 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3044)
                  apply V_pos_box_s3_s4 274410339 274415539
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3045, hcut3038⟩
                  · exact hne3
                  · exact hne4
            ·
              have hlo3039 : q 274415539 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3038)
              by_cases hcut3046 : y ≤ q 274425940 scaleN
              ·
                by_cases hcut3048 : y ≤ q 274420740 scaleN
                ·
                  apply V_pos_box_s3_s4 274415539 274420740
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3039, hcut3048⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo3049 : q 274420740 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3048)
                  apply V_pos_box_s3_s4 274420740 274425940
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3049, hcut3046⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo3047 : q 274425940 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3046)
                by_cases hcut3050 : y ≤ q 274431140 scaleN
                ·
                  apply V_pos_box_s3_s4 274425940 274431140
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3047, hcut3050⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo3051 : q 274431140 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3050)
                  by_cases hcut3052 : y ≤ q 274436340 scaleN
                  ·
                    apply V_pos_box_s3_s4 274431140 274436340
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo3051, hcut3052⟩
                    · exact hne3
                    · exact hne4
                  ·
                    have hlo3053 : q 274436340 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3052)
                    apply V_pos_box_s3_s4 274436340 274441541
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo3053, hcut3036⟩
                    · exact hne3
                    · exact hne4
          ·
            have hlo3037 : q 274441541 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3036)
            by_cases hcut3054 : y ≤ q 274462341 scaleN
            ·
              by_cases hcut3056 : y ≤ q 274451941 scaleN
              ·
                by_cases hcut3058 : y ≤ q 274446741 scaleN
                ·
                  apply V_pos_box_s3_s4 274441541 274446741
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3037, hcut3058⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo3059 : q 274446741 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3058)
                  apply V_pos_box_s3_s4 274446741 274451941
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3059, hcut3056⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo3057 : q 274451941 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3056)
                by_cases hcut3060 : y ≤ q 274457141 scaleN
                ·
                  apply V_pos_box_s3_s4 274451941 274457141
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3057, hcut3060⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo3061 : q 274457141 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3060)
                  apply V_pos_box_s3_s4 274457141 274462341
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3061, hcut3054⟩
                  · exact hne3
                  · exact hne4
            ·
              have hlo3055 : q 274462341 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3054)
              by_cases hcut3062 : y ≤ q 274472741 scaleN
              ·
                by_cases hcut3064 : y ≤ q 274467541 scaleN
                ·
                  apply V_pos_box_s3_s4 274462341 274467541
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3055, hcut3064⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo3065 : q 274467541 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3064)
                  apply V_pos_box_s3_s4 274467541 274472741
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3065, hcut3062⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo3063 : q 274472741 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3062)
                by_cases hcut3066 : y ≤ q 274477941 scaleN
                ·
                  apply V_pos_box_s3_s4 274472741 274477941
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3063, hcut3066⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo3067 : q 274477941 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3066)
                  by_cases hcut3068 : y ≤ q 274483142 scaleN
                  ·
                    apply V_pos_box_s3_s4 274477941 274483142
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo3067, hcut3068⟩
                    · exact hne3
                    · exact hne4
                  ·
                    have hlo3069 : q 274483142 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3068)
                    apply V_pos_box_s3_s4 274483142 274488342
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo3069, hcut2998⟩
                    · exact hne3
                    · exact hne4
      ·
        have hlo2999 : q 274488342 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut2998)
        by_cases hcut3070 : y ≤ q 274732752 scaleN
        ·
          by_cases hcut3072 : y ≤ q 274576745 scaleN
          ·
            by_cases hcut3074 : y ≤ q 274524744 scaleN
            ·
              by_cases hcut3076 : y ≤ q 274503943 scaleN
              ·
                by_cases hcut3078 : y ≤ q 274493542 scaleN
                ·
                  apply V_pos_box_s3_s4 274488342 274493542
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo2999, hcut3078⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo3079 : q 274493542 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3078)
                  apply V_pos_box_s3_s4 274493542 274503943
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3079, hcut3076⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo3077 : q 274503943 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3076)
                by_cases hcut3080 : y ≤ q 274514343 scaleN
                ·
                  apply V_pos_box_s3_s4 274503943 274514343
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3077, hcut3080⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo3081 : q 274514343 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3080)
                  apply V_pos_box_s3_s4 274514343 274524744
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3081, hcut3074⟩
                  · exact hne3
                  · exact hne4
            ·
              have hlo3075 : q 274524744 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3074)
              by_cases hcut3082 : y ≤ q 274545544 scaleN
              ·
                by_cases hcut3084 : y ≤ q 274535144 scaleN
                ·
                  apply V_pos_box_s3_s4 274524744 274535144
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3075, hcut3084⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo3085 : q 274535144 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3084)
                  apply V_pos_box_s3_s4 274535144 274545544
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3085, hcut3082⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo3083 : q 274545544 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3082)
                by_cases hcut3086 : y ≤ q 274555944 scaleN
                ·
                  apply V_pos_box_s3_s4 274545544 274555944
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3083, hcut3086⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo3087 : q 274555944 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3086)
                  by_cases hcut3088 : y ≤ q 274566345 scaleN
                  ·
                    apply V_pos_box_s3_s4 274555944 274566345
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo3087, hcut3088⟩
                    · exact hne3
                    · exact hne4
                  ·
                    have hlo3089 : q 274566345 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3088)
                    apply V_pos_box_s3_s4 274566345 274576745
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo3089, hcut3072⟩
                    · exact hne3
                    · exact hne4
          ·
            have hlo3073 : q 274576745 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3072)
            by_cases hcut3090 : y ≤ q 274628748 scaleN
            ·
              by_cases hcut3092 : y ≤ q 274597546 scaleN
              ·
                by_cases hcut3094 : y ≤ q 274587146 scaleN
                ·
                  apply V_pos_box_s3_s4 274576745 274587146
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3073, hcut3094⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo3095 : q 274587146 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3094)
                  apply V_pos_box_s3_s4 274587146 274597546
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3095, hcut3092⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo3093 : q 274597546 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3092)
                by_cases hcut3096 : y ≤ q 274607947 scaleN
                ·
                  apply V_pos_box_s3_s4 274597546 274607947
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3093, hcut3096⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo3097 : q 274607947 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3096)
                  apply V_pos_box_s3_s4 274607947 274628748
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3097, hcut3090⟩
                  · exact hne3
                  · exact hne4
            ·
              have hlo3091 : q 274628748 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3090)
              by_cases hcut3098 : y ≤ q 274670350 scaleN
              ·
                by_cases hcut3100 : y ≤ q 274649549 scaleN
                ·
                  apply V_pos_box_s3_s4 274628748 274649549
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3091, hcut3100⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo3101 : q 274649549 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3100)
                  apply V_pos_box_s3_s4 274649549 274670350
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3101, hcut3098⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo3099 : q 274670350 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3098)
                by_cases hcut3102 : y ≤ q 274691151 scaleN
                ·
                  apply V_pos_box_s3_s4 274670350 274691151
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3099, hcut3102⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo3103 : q 274691151 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3102)
                  by_cases hcut3104 : y ≤ q 274711951 scaleN
                  ·
                    apply V_pos_box_s3_s4 274691151 274711951
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo3103, hcut3104⟩
                    · exact hne3
                    · exact hne4
                  ·
                    have hlo3105 : q 274711951 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3104)
                    apply V_pos_box_s3_s4 274711951 274732752
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo3105, hcut3070⟩
                    · exact hne3
                    · exact hne4
        ·
          have hlo3071 : q 274732752 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3070)
          by_cases hcut3106 : y ≤ q 275190370 scaleN
          ·
            by_cases hcut3108 : y ≤ q 274857557 scaleN
            ·
              by_cases hcut3110 : y ≤ q 274774354 scaleN
              ·
                by_cases hcut3112 : y ≤ q 274753553 scaleN
                ·
                  apply V_pos_box_s3_s4 274732752 274753553
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3071, hcut3112⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo3113 : q 274753553 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3112)
                  apply V_pos_box_s3_s4 274753553 274774354
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3113, hcut3110⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo3111 : q 274774354 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3110)
                by_cases hcut3114 : y ≤ q 274815955 scaleN
                ·
                  apply V_pos_box_s3_s4 274774354 274815955
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3111, hcut3114⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo3115 : q 274815955 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3114)
                  apply V_pos_box_s3_s4 274815955 274857557
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3115, hcut3108⟩
                  · exact hne3
                  · exact hne4
            ·
              have hlo3109 : q 274857557 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3108)
              by_cases hcut3116 : y ≤ q 274940760 scaleN
              ·
                by_cases hcut3118 : y ≤ q 274899158 scaleN
                ·
                  apply V_pos_box_s3_s4 274857557 274899158
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3109, hcut3118⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo3119 : q 274899158 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3118)
                  apply V_pos_box_s3_s4 274899158 274940760
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3119, hcut3116⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo3117 : q 274940760 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3116)
                by_cases hcut3120 : y ≤ q 275023964 scaleN
                ·
                  apply V_pos_box_s3_s4 274940760 275023964
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3117, hcut3120⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo3121 : q 275023964 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3120)
                  by_cases hcut3122 : y ≤ q 275107167 scaleN
                  ·
                    apply V_pos_box_s3_s4 275023964 275107167
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo3121, hcut3122⟩
                    · exact hne3
                    · exact hne4
                  ·
                    have hlo3123 : q 275107167 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3122)
                    apply V_pos_box_s3_s4 275107167 275190370
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo3123, hcut3106⟩
                    · exact hne3
                    · exact hne4
          ·
            have hlo3107 : q 275190370 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3106)
            by_cases hcut3124 : y ≤ q 275689589 scaleN
            ·
              by_cases hcut3126 : y ≤ q 275356776 scaleN
              ·
                by_cases hcut3128 : y ≤ q 275273573 scaleN
                ·
                  apply V_pos_box_s3_s4 275190370 275273573
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3107, hcut3128⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo3129 : q 275273573 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3128)
                  apply V_pos_box_s3_s4 275273573 275356776
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3129, hcut3126⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo3127 : q 275356776 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3126)
                by_cases hcut3130 : y ≤ q 275523182 scaleN
                ·
                  apply V_pos_box_s3_s4 275356776 275523182
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3127, hcut3130⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo3131 : q 275523182 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3130)
                  apply V_pos_box_s3_s4 275523182 275689589
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3131, hcut3124⟩
                  · exact hne3
                  · exact hne4
            ·
              have hlo3125 : q 275689589 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3124)
              by_cases hcut3132 : y ≤ q 276355215 scaleN
              ·
                by_cases hcut3134 : y ≤ q 276022402 scaleN
                ·
                  apply V_pos_box_s3_s4 275689589 276022402
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3125, hcut3134⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo3135 : q 276022402 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3134)
                  apply V_pos_box_s3_s4 276022402 276355215
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3135, hcut3132⟩
                  · exact hne3
                  · exact hne4
              ·
                have hlo3133 : q 276355215 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3132)
                by_cases hcut3136 : y ≤ q 277020840 scaleN
                ·
                  apply V_pos_box_s3_s4 276355215 277020840
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · native_decide
                  · exact ⟨hlo3133, hcut3136⟩
                  · exact hne3
                  · exact hne4
                ·
                  have hlo3137 : q 277020840 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3136)
                  by_cases hcut3138 : y ≤ q 277686466 scaleN
                  ·
                    apply V_pos_box_s3_s4 277020840 277686466
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo3137, hcut3138⟩
                    · exact hne3
                    · exact hne4
                  ·
                    have hlo3139 : q 277686466 scaleN ≤ y := le_of_lt (lt_of_not_ge hcut3138)
                    apply V_pos_box_s3_s4 277686466 279017717
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · native_decide
                    · exact ⟨hlo3139, hhi0⟩
                    · exact hne3
                    · exact hne4

theorem V_boxes_after_s4
    {y : ℝ}
    (hy : y ∈ Icc s4 yHi)
    (hne4 : y ≠ s4)
    :
    0 < V y := by
  have hlo0 : q 279017717 scaleN ≤ y := by
    simpa [s4_eq_q] using hy.1
  have hhi0 : y ≤ q 280630400 scaleN := by
    norm_num [yHi, q, scaleN] at hy ⊢
    exact hy.2
  apply V_pos_box_after_s4 279017717 280630400
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · exact ⟨hlo0, hhi0⟩
  · exact hne4

theorem poleFreeOneVariableLogPositivity_from_boxes :
    PoleFreeOneVariableLogPositivity := by
  intro y hy hne1 hne2 hne3 hne4
  by_cases hys1 : y ≤ s1
  · exact V_boxes_before_s1 ⟨hy.1, hys1⟩ hne1
  · have hs1le : s1 ≤ y := le_of_lt (lt_of_not_ge hys1)
    by_cases hys2 : y ≤ s2
    · exact V_boxes_s1_s2 ⟨hs1le, hys2⟩ hne1 hne2
    · have hs2le : s2 ≤ y := le_of_lt (lt_of_not_ge hys2)
      by_cases hys3 : y ≤ s3
      · exact V_boxes_s2_s3 ⟨hs2le, hys3⟩ hne2 hne3
      · have hs3le : s3 ≤ y := le_of_lt (lt_of_not_ge hys3)
        by_cases hys4 : y ≤ s4
        · exact V_boxes_s3_s4 ⟨hs3le, hys4⟩ hne3 hne4
        · have hs4le : s4 ≤ y := le_of_lt (lt_of_not_ge hys4)
          exact V_boxes_after_s4 ⟨hs4le, hy.2⟩ hne4

end

end FiveAtom1806304Mathlib
end Erdos1038
