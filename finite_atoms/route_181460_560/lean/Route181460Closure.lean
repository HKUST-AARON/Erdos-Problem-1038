import Mathlib

/-!
# Route closure for the `M = 1.814600` five-atom piecewise tail candidate

This file records the route arithmetic needed for the tail part of the candidate.
It is conditional on a fixed forcing branch `(-1.708, 0)` and does not assert
that the block-positivity certificate is proven.
-/

namespace Erdos1038
namespace Route181460Closure

noncomputable section

open Set
open MeasureTheory
open scoped ENNReal

/-- Rational-to-real helper used across certificates. -/
def q (n d : ℕ) : ℝ := (n : ℝ) / (d : ℝ)

/-- Target parameter and forcing boundary. -/
def M : ℝ := q 1814600 1000000

def B : ℝ := q 1708 1000

def Tail : ℝ := M - B

def K : ℕ := 560

def h : ℝ := Tail / K

def shift1 : ℝ := q 18146001 10000000  -- 1.8146001

def shift2 : ℝ := q 255506 100000      -- 2.55506

def shift3 : ℝ := q 2675215475 1000000000  -- 2.675215475

def shift4 : ℝ := q 2781815575 1000000000  -- 2.781815575

/-! ## Swept intervals and tail selector -/

def I0 : Set ℝ := Icc (-M) (-B)
def I1 : Set ℝ := Icc (shift1 - M) (shift1 - B)
def I2 : Set ℝ := Icc (shift2 - M) (shift2 - B)
def I3 : Set ℝ := Icc (shift3 - M) (shift3 - B)
def I4 : Set ℝ := Icc (shift4 - M) (shift4 - B)
def LongInterval : Set ℝ := Ioo (-B) 0

def TailParameter : Set ℝ := I0

def swept0 (a : ℝ) : ℝ := a
def swept1 (a : ℝ) : ℝ := a + shift1
def swept2 (a : ℝ) : ℝ := a + shift2
def swept3 (a : ℝ) : ℝ := a + shift3
def swept4 (a : ℝ) : ℝ := a + shift4

def TailSelector (E : Set ℝ) : Prop :=
  ∀ a : ℝ, a ∈ TailParameter →
    swept0 a ∈ E ∨ swept1 a ∈ E ∨ swept2 a ∈ E ∨ swept3 a ∈ E ∨ swept4 a ∈ E

def TailPiece0 (E : Set ℝ) : Set ℝ := E ∩ I0
def TailPiece1 (E : Set ℝ) : Set ℝ := E ∩ I1
def TailPiece2 (E : Set ℝ) : Set ℝ := E ∩ I2
def TailPiece3 (E : Set ℝ) : Set ℝ := E ∩ I3
def TailPiece4 (E : Set ℝ) : Set ℝ := E ∩ I4

def TailPreimage0 (E : Set ℝ) : Set ℝ := I0 ∩ swept0 ⁻¹' E
def TailPreimage1 (E : Set ℝ) : Set ℝ := I0 ∩ swept1 ⁻¹' E
def TailPreimage2 (E : Set ℝ) : Set ℝ := I0 ∩ swept2 ⁻¹' E
def TailPreimage3 (E : Set ℝ) : Set ℝ := I0 ∩ swept3 ⁻¹' E
def TailPreimage4 (E : Set ℝ) : Set ℝ := I0 ∩ swept4 ⁻¹' E

lemma mem_shifted_tail_interval_iff {a s : ℝ} :
    a + s ∈ Icc (s - M) (s - B) ↔ a ∈ I0 := by
  constructor
  · intro h
    simp [I0] at h ⊢
    constructor <;> linarith
  · intro h
    simp [I0] at h ⊢
    constructor <;> linarith

lemma tailPreimage0_eq_piece (E : Set ℝ) :
    TailPreimage0 E = TailPiece0 E := by
  ext a
  simp [TailPreimage0, TailPiece0, swept0, and_comm]

lemma tailPreimage1_eq_shift_preimage_piece (E : Set ℝ) :
    TailPreimage1 E = swept1 ⁻¹' TailPiece1 E := by
  ext a
  simp only [TailPreimage1, TailPiece1, swept1, mem_inter_iff, mem_preimage]
  constructor
  · intro h
    exact ⟨h.2, by
      simpa [I1] using ((mem_shifted_tail_interval_iff (s := shift1)).2 h.1)⟩
  · intro h
    exact ⟨(mem_shifted_tail_interval_iff (s := shift1)).1 (by
      simpa [I1] using h.2), h.1⟩

lemma tailPreimage2_eq_shift_preimage_piece (E : Set ℝ) :
    TailPreimage2 E = swept2 ⁻¹' TailPiece2 E := by
  ext a
  simp only [TailPreimage2, TailPiece2, swept2, mem_inter_iff, mem_preimage]
  constructor
  · intro h
    exact ⟨h.2, by
      simpa [I2] using ((mem_shifted_tail_interval_iff (s := shift2)).2 h.1)⟩
  · intro h
    exact ⟨(mem_shifted_tail_interval_iff (s := shift2)).1 (by
      simpa [I2] using h.2), h.1⟩

lemma tailPreimage3_eq_shift_preimage_piece (E : Set ℝ) :
    TailPreimage3 E = swept3 ⁻¹' TailPiece3 E := by
  ext a
  simp only [TailPreimage3, TailPiece3, swept3, mem_inter_iff, mem_preimage]
  constructor
  · intro h
    exact ⟨h.2, by
      simpa [I3] using ((mem_shifted_tail_interval_iff (s := shift3)).2 h.1)⟩
  · intro h
    exact ⟨(mem_shifted_tail_interval_iff (s := shift3)).1 (by
      simpa [I3] using h.2), h.1⟩

lemma tailPreimage4_eq_shift_preimage_piece (E : Set ℝ) :
    TailPreimage4 E = swept4 ⁻¹' TailPiece4 E := by
  ext a
  simp only [TailPreimage4, TailPiece4, swept4, mem_inter_iff, mem_preimage]
  constructor
  · intro h
    exact ⟨h.2, by
      simpa [I4] using ((mem_shifted_tail_interval_iff (s := shift4)).2 h.1)⟩
  · intro h
    exact ⟨(mem_shifted_tail_interval_iff (s := shift4)).1 (by
      simpa [I4] using h.2), h.1⟩

lemma volume_preimage_add_const_eq (c : ℝ) (S : Set ℝ) (hS : MeasurableSet S) :
    volume ((fun x : ℝ => x + c) ⁻¹' S) = volume S := by
  rw [← Measure.map_apply (measurable_add_const c) hS]
  rw [map_add_right_eq_self]

lemma volume_tailPreimage0_eq_piece (E : Set ℝ) :
    volume (TailPreimage0 E) = volume (TailPiece0 E) := by
  rw [tailPreimage0_eq_piece]

lemma volume_tailPreimage1_eq_piece (E : Set ℝ) (hE : MeasurableSet E) :
    volume (TailPreimage1 E) = volume (TailPiece1 E) := by
  rw [tailPreimage1_eq_shift_preimage_piece]
  exact volume_preimage_add_const_eq shift1 (TailPiece1 E)
    (hE.inter measurableSet_Icc)

lemma volume_tailPreimage2_eq_piece (E : Set ℝ) (hE : MeasurableSet E) :
    volume (TailPreimage2 E) = volume (TailPiece2 E) := by
  rw [tailPreimage2_eq_shift_preimage_piece]
  exact volume_preimage_add_const_eq shift2 (TailPiece2 E)
    (hE.inter measurableSet_Icc)

lemma volume_tailPreimage3_eq_piece (E : Set ℝ) (hE : MeasurableSet E) :
    volume (TailPreimage3 E) = volume (TailPiece3 E) := by
  rw [tailPreimage3_eq_shift_preimage_piece]
  exact volume_preimage_add_const_eq shift3 (TailPiece3 E)
    (hE.inter measurableSet_Icc)

lemma volume_tailPreimage4_eq_piece (E : Set ℝ) (hE : MeasurableSet E) :
    volume (TailPreimage4 E) = volume (TailPiece4 E) := by
  rw [tailPreimage4_eq_shift_preimage_piece]
  exact volume_preimage_add_const_eq shift4 (TailPiece4 E)
    (hE.inter measurableSet_Icc)

lemma tailParameter_subset_preimage_union {E : Set ℝ}
    (selector : TailSelector E) :
    TailParameter ⊆
      TailPreimage0 E ∪ TailPreimage1 E ∪ TailPreimage2 E ∪
        TailPreimage3 E ∪ TailPreimage4 E := by
  intro a ha
  rcases selector a ha with h0 | h1 | h2 | h3 | h4
  · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨ha, h0⟩)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨ha, h1⟩)))
  · exact Or.inl (Or.inl (Or.inr ⟨ha, h2⟩))
  · exact Or.inl (Or.inr ⟨ha, h3⟩)
  · exact Or.inr ⟨ha, h4⟩

lemma measure_five_union_le_sum (A0 A1 A2 A3 A4 : Set ℝ) :
    volume (A0 ∪ A1 ∪ A2 ∪ A3 ∪ A4) ≤
      volume A0 + volume A1 + volume A2 + volume A3 + volume A4 := by
  calc
    volume (A0 ∪ A1 ∪ A2 ∪ A3 ∪ A4)
        ≤ volume (A0 ∪ A1 ∪ A2 ∪ A3) + volume A4 := by
          exact measure_union_le (μ := volume) (A0 ∪ A1 ∪ A2 ∪ A3) A4
    _ ≤ (volume (A0 ∪ A1 ∪ A2) + volume A3) + volume A4 := by
          gcongr
          exact measure_union_le (μ := volume) (A0 ∪ A1 ∪ A2) A3
    _ ≤ ((volume (A0 ∪ A1) + volume A2) + volume A3) + volume A4 := by
          gcongr
          exact measure_union_le (μ := volume) (A0 ∪ A1) A2
    _ ≤ (((volume A0 + volume A1) + volume A2) + volume A3) + volume A4 := by
          gcongr
          exact measure_union_le (μ := volume) A0 A1
    _ = volume A0 + volume A1 + volume A2 + volume A3 + volume A4 := by
          ac_rfl

theorem tailSelector_measure_sum_lower_bound
    {E : Set ℝ}
    (hE : MeasurableSet E)
    (selector : TailSelector E) :
    volume TailParameter ≤
      volume (TailPiece0 E) + volume (TailPiece1 E) + volume (TailPiece2 E) +
        volume (TailPiece3 E) + volume (TailPiece4 E) := by
  have hcover :
      volume TailParameter ≤
        volume (TailPreimage0 E ∪ TailPreimage1 E ∪ TailPreimage2 E ∪
          TailPreimage3 E ∪ TailPreimage4 E) := by
    exact measure_mono (μ := volume) (tailParameter_subset_preimage_union selector)
  have hunion := measure_five_union_le_sum
    (TailPreimage0 E) (TailPreimage1 E) (TailPreimage2 E)
    (TailPreimage3 E) (TailPreimage4 E)
  calc
    volume TailParameter
        ≤ volume (TailPreimage0 E ∪ TailPreimage1 E ∪ TailPreimage2 E ∪
            TailPreimage3 E ∪ TailPreimage4 E) := hcover
    _ ≤ volume (TailPreimage0 E) + volume (TailPreimage1 E) +
          volume (TailPreimage2 E) + volume (TailPreimage3 E) +
          volume (TailPreimage4 E) := hunion
    _ = volume (TailPiece0 E) + volume (TailPiece1 E) +
          volume (TailPiece2 E) + volume (TailPiece3 E) +
          volume (TailPiece4 E) := by
          rw [volume_tailPreimage0_eq_piece E,
            volume_tailPreimage1_eq_piece E hE,
            volume_tailPreimage2_eq_piece E hE,
            volume_tailPreimage3_eq_piece E hE,
            volume_tailPreimage4_eq_piece E hE]

theorem tailSelector_length_sum_lower_bound
    {E : Set ℝ}
    (hE : MeasurableSet E)
    (selector : TailSelector E) :
    ENNReal.ofReal (M - B) ≤
      volume (TailPiece0 E) + volume (TailPiece1 E) + volume (TailPiece2 E) +
        volume (TailPiece3 E) + volume (TailPiece4 E) := by
  have h := tailSelector_measure_sum_lower_bound hE selector
  have hMB : -B + M = M - B := by ring
  simpa [TailParameter, I0, Real.volume_Icc, hMB] using h

/-- Arithmetic facts used by route bookkeeping. -/
theorem shift1_gt_M : M < shift1 := by
  norm_num [M, shift1, q]

theorem swept_intervals_disjoint :
    M < shift1 ∧
    shift1 + Tail < shift2 ∧
    shift2 + Tail < shift3 ∧
    shift3 + Tail < shift4 := by
  norm_num [M, B, Tail, shift1, shift2, shift3, shift4, q]

theorem tail_value : Tail = q 1066 10000 := by
  norm_num [Tail, M, B, q]

/-- Bundle of arithmetic used in the route closure. -/
theorem route_181460_arithmetic_certificate :
    Tail = q 1066 10000 ∧ B + Tail = M ∧ M < q 1836 1000 := by
  refine ⟨tail_value, ?_, ?_⟩
  · norm_num [Tail, M, B, q]
  · norm_num [M, q]

/-- Route abstraction: if one has a predicate giving the long part length `B` and
    the tail part length `Tail`, then the target length `M` is obtained by additivity. -/
def HasLengthAtLeast (_E : Set ℝ) (_L : ℝ) : Prop := True

def LongContribution (LengthAtLeast : ℝ → Prop) : Prop := LengthAtLeast B

def TailContribution (LengthAtLeast : ℝ → Prop) : Prop := LengthAtLeast Tail

def AddContributionRule (LengthAtLeast : ℝ → Prop) : Prop :=
  LengthAtLeast B → LengthAtLeast Tail → LengthAtLeast M

/-- Conditional route closure theorem for this candidate format. -/
theorem route_181460_closure
    {LengthAtLeast : ℝ → Prop}
  (hLong : LongContribution LengthAtLeast)
  (hTail : TailContribution LengthAtLeast)
  (hAdd : AddContributionRule LengthAtLeast) :
    LengthAtLeast M := by
  exact hAdd hLong hTail

end

end Route181460Closure
end Erdos1038
