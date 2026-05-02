import Mathlib

/-!
# Route spine for the `M = 1.806304` finite-atom certificate

This file formalizes the bookkeeping layer that combines the earlier forcing
step with the five-atom tail block.

The one-variable logarithmic checks are in `FiveAtom1806304Mathlib.lean`.
This file keeps the route-level assumptions explicit: the earlier forcing
branch, the dual-forcing selector, and the measure-theoretic sweep lemma enter
as hypotheses.  Under those hypotheses, the final `1.806304` target is proved
inside Lean.
-/

namespace Erdos1038
namespace FiveAtom1806304Route

noncomputable section

open Set
open MeasureTheory
open scoped ENNReal

def q (n d : ℕ) : ℝ := (n : ℝ) / (d : ℝ)

def M : ℝ := q 1806304 1000000
def T : ℝ := q 1708 1000

def s1 : ℝ := q 180650001 100000000
def s2 : ℝ := q 257053197 100000000
def s3 : ℝ := q 268367709 100000000
def s4 : ℝ := q 279017717 100000000

/-! ## Swept intervals -/

def I0 : Set ℝ := Icc (-M) (-T)
def I1 : Set ℝ := Icc (s1 - M) (s1 - T)
def I2 : Set ℝ := Icc (s2 - M) (s2 - T)
def I3 : Set ℝ := Icc (s3 - M) (s3 - T)
def I4 : Set ℝ := Icc (s4 - M) (s4 - T)
def LongInterval : Set ℝ := Ioo (-T) 0

def TailParameter : Set ℝ := I0

def swept0 (a : ℝ) : ℝ := a
def swept1 (a : ℝ) : ℝ := a + s1
def swept2 (a : ℝ) : ℝ := a + s2
def swept3 (a : ℝ) : ℝ := a + s3
def swept4 (a : ℝ) : ℝ := a + s4

/--
The selector conclusion supplied by the five-atom dual certificate: for every
moving parameter `a`, at least one of the five swept points lies in the positive
set `E`.
-/
def TailSelector (E : Set ℝ) : Prop :=
  ∀ a : ℝ, a ∈ TailParameter →
    swept0 a ∈ E ∨ swept1 a ∈ E ∨ swept2 a ∈ E ∨ swept3 a ∈ E ∨ swept4 a ∈ E

/-! ## Measure-theoretic sweep contribution -/

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
    a + s ∈ Icc (s - M) (s - T) ↔ a ∈ I0 := by
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
      simpa [I1] using ((mem_shifted_tail_interval_iff (s := s1)).2 h.1)⟩
  · intro h
    exact ⟨(mem_shifted_tail_interval_iff (s := s1)).1 (by
      simpa [I1] using h.2), h.1⟩

lemma tailPreimage2_eq_shift_preimage_piece (E : Set ℝ) :
    TailPreimage2 E = swept2 ⁻¹' TailPiece2 E := by
  ext a
  simp only [TailPreimage2, TailPiece2, swept2, mem_inter_iff, mem_preimage]
  constructor
  · intro h
    exact ⟨h.2, by
      simpa [I2] using ((mem_shifted_tail_interval_iff (s := s2)).2 h.1)⟩
  · intro h
    exact ⟨(mem_shifted_tail_interval_iff (s := s2)).1 (by
      simpa [I2] using h.2), h.1⟩

lemma tailPreimage3_eq_shift_preimage_piece (E : Set ℝ) :
    TailPreimage3 E = swept3 ⁻¹' TailPiece3 E := by
  ext a
  simp only [TailPreimage3, TailPiece3, swept3, mem_inter_iff, mem_preimage]
  constructor
  · intro h
    exact ⟨h.2, by
      simpa [I3] using ((mem_shifted_tail_interval_iff (s := s3)).2 h.1)⟩
  · intro h
    exact ⟨(mem_shifted_tail_interval_iff (s := s3)).1 (by
      simpa [I3] using h.2), h.1⟩

lemma tailPreimage4_eq_shift_preimage_piece (E : Set ℝ) :
    TailPreimage4 E = swept4 ⁻¹' TailPiece4 E := by
  ext a
  simp only [TailPreimage4, TailPiece4, swept4, mem_inter_iff, mem_preimage]
  constructor
  · intro h
    exact ⟨h.2, by
      simpa [I4] using ((mem_shifted_tail_interval_iff (s := s4)).2 h.1)⟩
  · intro h
    exact ⟨(mem_shifted_tail_interval_iff (s := s4)).1 (by
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
  exact volume_preimage_add_const_eq s1 (TailPiece1 E)
    (hE.inter measurableSet_Icc)

lemma volume_tailPreimage2_eq_piece (E : Set ℝ) (hE : MeasurableSet E) :
    volume (TailPreimage2 E) = volume (TailPiece2 E) := by
  rw [tailPreimage2_eq_shift_preimage_piece]
  exact volume_preimage_add_const_eq s2 (TailPiece2 E)
    (hE.inter measurableSet_Icc)

lemma volume_tailPreimage3_eq_piece (E : Set ℝ) (hE : MeasurableSet E) :
    volume (TailPreimage3 E) = volume (TailPiece3 E) := by
  rw [tailPreimage3_eq_shift_preimage_piece]
  exact volume_preimage_add_const_eq s3 (TailPiece3 E)
    (hE.inter measurableSet_Icc)

lemma volume_tailPreimage4_eq_piece (E : Set ℝ) (hE : MeasurableSet E) :
    volume (TailPreimage4 E) = volume (TailPiece4 E) := by
  rw [tailPreimage4_eq_shift_preimage_piece]
  exact volume_preimage_add_const_eq s4 (TailPiece4 E)
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
    ENNReal.ofReal (M - T) ≤
      volume (TailPiece0 E) + volume (TailPiece1 E) + volume (TailPiece2 E) +
        volume (TailPiece3 E) + volume (TailPiece4 E) := by
  have h := tailSelector_measure_sum_lower_bound hE selector
  have hMT : -T + M = M - T := by ring
  simpa [TailParameter, I0, Real.volume_Icc, hMT] using h

/-! ## Exact arithmetic -/

theorem tail_length : M - T = q 98304 1000000 := by
  norm_num [M, T, q]

theorem target_length_arithmetic : T + (M - T) = M := by
  norm_num [M, T, q]

theorem target_lt_forcing_threshold : M < q 1836 1000 := by
  norm_num [M, q]

theorem first_shift_after_M : M < s1 := by
  norm_num [M, s1, q]

theorem gap12 : M - T < s2 - s1 := by
  norm_num [M, T, s1, s2, q]

theorem gap23 : M - T < s3 - s2 := by
  norm_num [M, T, s2, s3, q]

theorem gap34 : M - T < s4 - s3 := by
  norm_num [M, T, s3, s4, q]

/-! ## Disjointness of the long interval and swept tail intervals -/

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

/-! ## Route-level assumptions and final theorem -/

/-- The previous forcing branch gives the long interval contribution. -/
def LongForcingContribution (LengthAtLeast : ℝ → Prop) : Prop :=
  LengthAtLeast T

/--
The measure-theoretic sweep lemma applied to the five disjoint swept intervals.
-/
def TailSweepContribution (LengthAtLeast : ℝ → Prop) (E : Set ℝ) : Prop :=
  TailSelector E →
    Disjoint I0 LongInterval ∧
    Disjoint I1 LongInterval ∧
    Disjoint I2 LongInterval ∧
    Disjoint I3 LongInterval ∧
    Disjoint I4 LongInterval ∧
    Disjoint I0 I1 ∧
    Disjoint I1 I2 ∧
    Disjoint I2 I3 ∧
    Disjoint I3 I4 →
  LengthAtLeast (M - T)

/-- Addition rule for two disjoint length contributions. -/
def AddDisjointLengthRule (LengthAtLeast : ℝ → Prop) : Prop :=
  LengthAtLeast T → LengthAtLeast (M - T) → LengthAtLeast M

/--
Conditional route theorem for the finite-atom update to `M = 1.806304`.
-/
theorem finite_atom_route_1806304
    {E : Set ℝ} {LengthAtLeast : ℝ → Prop}
    (long : LongForcingContribution LengthAtLeast)
    (selector : TailSelector E)
    (tailSweep : TailSweepContribution LengthAtLeast E)
    (addRule : AddDisjointLengthRule LengthAtLeast) :
    LengthAtLeast M := by
  have htail : LengthAtLeast (M - T) :=
    tailSweep selector sweep_disjointness_certificate
  exact addRule long htail

/-- Same theorem with the target decimal unfolded. -/
theorem finite_atom_route_target_decimal
    {E : Set ℝ} {LengthAtLeast : ℝ → Prop}
    (long : LongForcingContribution LengthAtLeast)
    (selector : TailSelector E)
    (tailSweep : TailSweepContribution LengthAtLeast E)
    (addRule : AddDisjointLengthRule LengthAtLeast) :
    LengthAtLeast (q 1806304 1000000) := by
  simpa [M] using
    (finite_atom_route_1806304 (E := E) (LengthAtLeast := LengthAtLeast)
      long selector tailSweep addRule)

/-- Bundle of internal arithmetic and disjointness facts proved in this file. -/
theorem route_spine_internal_certificate :
    (M - T = q 98304 1000000) ∧
    (T + (M - T) = M) ∧
    (M < q 1836 1000) ∧
    (Disjoint I0 LongInterval ∧
      Disjoint I1 LongInterval ∧
      Disjoint I2 LongInterval ∧
      Disjoint I3 LongInterval ∧
      Disjoint I4 LongInterval ∧
      Disjoint I0 I1 ∧
      Disjoint I1 I2 ∧
      Disjoint I2 I3 ∧
      Disjoint I3 I4) := by
  exact ⟨tail_length, target_length_arithmetic,
    target_lt_forcing_threshold, sweep_disjointness_certificate⟩

end

end FiveAtom1806304Route
end Erdos1038
