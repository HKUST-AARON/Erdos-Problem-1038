import Mathlib
import finite_atoms.common.lean.StandardReduction
import PiecewiseFiveAtom181460Formal

/-!
# Route closure for the `M = 1.814600` five-atom piecewise tail candidate

This file records the route arithmetic and selector bridge needed for the tail
part of the candidate.  It imports the 560-block piecewise tail certificate and
uses it to produce the tail selector under the named tail-mass finiteness
hypothesis below.

The route remains conditional on the separate long-forcing branch that supplies
`(-1.708, 0)`, or equivalently the `hforcing1836` handoff theorem near the end
of this file.
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

def B1700 : ℝ := q 17 10

def Tail : ℝ := M - B

def M1700Tail : ℝ := B1700 + Tail

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
def LongInterval1700 : Set ℝ := Ioo (-B1700) 0

def TailParameter : Set ℝ := I0

def swept0 (a : ℝ) : ℝ := a
def swept1 (a : ℝ) : ℝ := a + shift1
def swept2 (a : ℝ) : ℝ := a + shift2
def swept3 (a : ℝ) : ℝ := a + shift3
def swept4 (a : ℝ) : ℝ := a + shift4

def sweptAtom (a : ℝ) : Fin 5 → ℝ
  | ⟨0, _⟩ => swept0 a
  | ⟨1, _⟩ => swept1 a
  | ⟨2, _⟩ => swept2 a
  | ⟨3, _⟩ => swept3 a
  | ⟨4, _⟩ => swept4 a

def TailSelector (E : Set ℝ) : Prop :=
  ∀ a : ℝ, a ∈ TailParameter →
    swept0 a ∈ E ∨ swept1 a ∈ E ∨ swept2 a ∈ E ∨ swept3 a ∈ E ∨ swept4 a ∈ E

def TailFiniteSelection (E : Set ℝ) : Prop :=
  ∀ a : ℝ, a ∈ TailParameter → ∃ i : Fin 5, sweptAtom a i ∈ E

def TailMassFiniteHypothesis
    (μ : MeasureTheory.ProbabilityMeasure StandardReduction.UnitInterval1038) : Prop :=
  ∀ a : ℝ, a ∈ TailParameter → ∀ i : Fin 5,
    sweptAtom a i ∈ Icc (-1 : ℝ) 1 →
    sweptAtom a i ∉ StandardReduction.diagonalAtomSet μ →
    ∃ ε : ℝ, 0 < ε ∧
      StandardReduction.singularTailMass ε μ (sweptAtom a i) < ∞

def UnitIntervalTailMassFiniteOffDiagonal
    (μ : MeasureTheory.ProbabilityMeasure StandardReduction.UnitInterval1038) : Prop :=
  ∀ x : ℝ, x ∈ Icc (-1 : ℝ) 1 →
    x ∉ StandardReduction.diagonalAtomSet μ →
    ∃ ε : ℝ, 0 < ε ∧
      StandardReduction.singularTailMass ε μ x < ∞

theorem TailMassFiniteHypothesis.of_unitInterval_offDiagonal
    {μ : MeasureTheory.ProbabilityMeasure StandardReduction.UnitInterval1038}
    (hfinite : UnitIntervalTailMassFiniteOffDiagonal μ) :
    TailMassFiniteHypothesis μ := by
  intro a ha i hunit hoff
  exact hfinite (sweptAtom a i) hunit hoff

theorem TailFiniteSelection.toTailSelector
    {E : Set ℝ} (h : TailFiniteSelection E) :
    TailSelector E := by
  intro a ha
  rcases h a ha with ⟨i, hi⟩
  fin_cases i <;> simp [sweptAtom] at hi
  · exact Or.inl hi
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr (Or.inl hi))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hi)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hi)))

theorem tailFiniteSelection_from_augmented_duality
    (μ : MeasureTheory.ProbabilityMeasure StandardReduction.UnitInterval1038)
    (w : ℝ → Fin 5 → ℝ)
    (hduality : ∀ a : ℝ, a ∈ TailParameter →
      StandardReduction.FiniteAtomicUnitIntervalDualityIdentity
        μ Finset.univ (w a) (sweptAtom a))
    (hw_nonneg : ∀ a : ℝ, a ∈ TailParameter → ∀ i : Fin 5, 0 ≤ w a i)
    (hintegral_pos : ∀ a : ℝ, a ∈ TailParameter →
      0 < ∫ x : StandardReduction.UnitInterval1038,
        StandardReduction.finiteWeightedPotential
          Finset.univ (w a) (sweptAtom a) (x : ℝ)
          ∂(μ : MeasureTheory.Measure StandardReduction.UnitInterval1038)) :
    TailFiniteSelection (StandardReduction.unitIntervalAugmentedPositiveSet μ) := by
  intro a ha
  rcases (hduality a ha).selects_augmented_atom
      (by
        intro i _hi
        exact hw_nonneg a ha i)
      (hintegral_pos a ha) with
    ⟨i, _hi, hmem⟩
  exact ⟨i, hmem⟩

theorem tailSelector_from_augmented_duality
    (μ : MeasureTheory.ProbabilityMeasure StandardReduction.UnitInterval1038)
    (w : ℝ → Fin 5 → ℝ)
    (hduality : ∀ a : ℝ, a ∈ TailParameter →
      StandardReduction.FiniteAtomicUnitIntervalDualityIdentity
        μ Finset.univ (w a) (sweptAtom a))
    (hw_nonneg : ∀ a : ℝ, a ∈ TailParameter → ∀ i : Fin 5, 0 ≤ w a i)
    (hintegral_pos : ∀ a : ℝ, a ∈ TailParameter →
      0 < ∫ x : StandardReduction.UnitInterval1038,
        StandardReduction.finiteWeightedPotential
          Finset.univ (w a) (sweptAtom a) (x : ℝ)
          ∂(μ : MeasureTheory.Measure StandardReduction.UnitInterval1038)) :
    TailSelector (StandardReduction.unitIntervalAugmentedPositiveSet μ) :=
  (tailFiniteSelection_from_augmented_duality μ w hduality hw_nonneg
    hintegral_pos).toTailSelector

theorem integral_pos_of_integrable_ae_pos_probability
    {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.ProbabilityMeasure α) {f : α → ℝ}
    (hf_int : Integrable f (μ : Measure α))
    (hf_pos : ∀ᵐ x ∂(μ : Measure α), 0 < f x) :
    0 < ∫ x, f x ∂(μ : Measure α) := by
  have hf_nonneg : 0 ≤ᵐ[(μ : Measure α)] f :=
    hf_pos.mono (fun _ hx => le_of_lt hx)
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae hf_nonneg hf_int]
  have hsupport_ae :
      Function.support f =ᵐ[(μ : Measure α)] Set.univ := by
    filter_upwards [hf_pos] with x hx
    exact propext ⟨fun _h => trivial, fun _h => ne_of_gt hx⟩
  have hsupport_measure :
      (μ : Measure α) (Function.support f) =
        (μ : Measure α) Set.univ :=
    measure_congr hsupport_ae
  rw [hsupport_measure]
  simp

def UnitIntervalNormalizedSupportAE
    (μ : MeasureTheory.ProbabilityMeasure StandardReduction.UnitInterval1038) : Prop :=
  ∀ᵐ (x : StandardReduction.UnitInterval1038)
    ∂(μ : MeasureTheory.Measure StandardReduction.UnitInterval1038),
    (x : ℝ) = -1 ∨ (x : ℝ) ∈ Icc (0 : ℝ) 1

theorem finiteWeightedPotential_integral_pos_of_normalized_pointwise
    (μ : MeasureTheory.ProbabilityMeasure StandardReduction.UnitInterval1038)
    (hNorm : UnitIntervalNormalizedSupportAE μ)
    (w : Fin 5 → ℝ) (atom : Fin 5 → ℝ)
    (hint : Integrable
      (fun x : StandardReduction.UnitInterval1038 =>
        StandardReduction.finiteWeightedPotential
          Finset.univ w atom (x : ℝ))
      (μ : MeasureTheory.Measure StandardReduction.UnitInterval1038))
    (hpoint :
      ∀ x : StandardReduction.UnitInterval1038,
        ((x : ℝ) = -1 ∨ (x : ℝ) ∈ Icc (0 : ℝ) 1) →
        0 <
          StandardReduction.finiteWeightedPotential
            Finset.univ w atom (x : ℝ)) :
    0 < ∫ x : StandardReduction.UnitInterval1038,
      StandardReduction.finiteWeightedPotential
        Finset.univ w atom (x : ℝ)
        ∂(μ : MeasureTheory.Measure StandardReduction.UnitInterval1038) :=
  integral_pos_of_integrable_ae_pos_probability μ hint
    (hNorm.mono (fun x hx => hpoint x hx))

theorem tailSelector_from_augmented_duality_of_normalized_pointwise
    (μ : MeasureTheory.ProbabilityMeasure StandardReduction.UnitInterval1038)
    (w : ℝ → Fin 5 → ℝ)
    (hNorm : UnitIntervalNormalizedSupportAE μ)
    (hduality : ∀ a : ℝ, a ∈ TailParameter →
      StandardReduction.FiniteAtomicUnitIntervalDualityIdentity
        μ Finset.univ (w a) (sweptAtom a))
    (hw_nonneg : ∀ a : ℝ, a ∈ TailParameter → ∀ i : Fin 5, 0 ≤ w a i)
    (hint : ∀ a : ℝ, a ∈ TailParameter →
      Integrable
        (fun x : StandardReduction.UnitInterval1038 =>
          StandardReduction.finiteWeightedPotential
            Finset.univ (w a) (sweptAtom a) (x : ℝ))
        (μ : MeasureTheory.Measure StandardReduction.UnitInterval1038))
    (hpoint : ∀ a : ℝ, a ∈ TailParameter →
      ∀ x : StandardReduction.UnitInterval1038,
        ((x : ℝ) = -1 ∨ (x : ℝ) ∈ Icc (0 : ℝ) 1) →
        0 <
          StandardReduction.finiteWeightedPotential
            Finset.univ (w a) (sweptAtom a) (x : ℝ)) :
    TailSelector (StandardReduction.unitIntervalAugmentedPositiveSet μ) :=
  tailSelector_from_augmented_duality μ w hduality hw_nonneg
    (fun a ha =>
      finiteWeightedPotential_integral_pos_of_normalized_pointwise
        μ hNorm (w a) (sweptAtom a) (hint a ha) (hpoint a ha))

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

/-! ## Concrete volume closure for the `1.814600` route -/

theorem I0_disjoint_Long : Disjoint I0 LongInterval := by
  rw [Set.disjoint_left]
  intro x hx0 hxLong
  simp [I0, LongInterval] at hx0 hxLong
  linarith

theorem I1_disjoint_Long : Disjoint I1 LongInterval := by
  rw [Set.disjoint_left]
  intro x hx1 hxLong
  simp [I1, LongInterval] at hx1 hxLong
  have hpos : 0 < shift1 - M := by
    norm_num [shift1, M, q]
  linarith

theorem I2_disjoint_Long : Disjoint I2 LongInterval := by
  rw [Set.disjoint_left]
  intro x hx2 hxLong
  simp [I2, LongInterval] at hx2 hxLong
  have hpos : 0 < shift2 - M := by
    norm_num [shift2, M, q]
  linarith

theorem I3_disjoint_Long : Disjoint I3 LongInterval := by
  rw [Set.disjoint_left]
  intro x hx3 hxLong
  simp [I3, LongInterval] at hx3 hxLong
  have hpos : 0 < shift3 - M := by
    norm_num [shift3, M, q]
  linarith

theorem I4_disjoint_Long : Disjoint I4 LongInterval := by
  rw [Set.disjoint_left]
  intro x hx4 hxLong
  simp [I4, LongInterval] at hx4 hxLong
  have hpos : 0 < shift4 - M := by
    norm_num [shift4, M, q]
  linarith

theorem I0_I1_disjoint : Disjoint I0 I1 := by
  rw [Set.disjoint_left]
  intro x hx0 hx1
  simp [I0, I1] at hx0 hx1
  have h : -B < shift1 - M := by
    norm_num [B, shift1, M, q]
  linarith

theorem I0_I2_disjoint : Disjoint I0 I2 := by
  rw [Set.disjoint_left]
  intro x hx0 hx2
  simp [I0, I2] at hx0 hx2
  have h : -B < shift2 - M := by
    norm_num [B, shift2, M, q]
  linarith

theorem I0_I3_disjoint : Disjoint I0 I3 := by
  rw [Set.disjoint_left]
  intro x hx0 hx3
  simp [I0, I3] at hx0 hx3
  have h : -B < shift3 - M := by
    norm_num [B, shift3, M, q]
  linarith

theorem I0_I4_disjoint : Disjoint I0 I4 := by
  rw [Set.disjoint_left]
  intro x hx0 hx4
  simp [I0, I4] at hx0 hx4
  have h : -B < shift4 - M := by
    norm_num [B, shift4, M, q]
  linarith

theorem I1_I2_disjoint : Disjoint I1 I2 := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  simp [I1, I2] at hx1 hx2
  have h : shift1 - B < shift2 - M := by
    norm_num [B, shift1, shift2, M, q]
  linarith

theorem I1_I3_disjoint : Disjoint I1 I3 := by
  rw [Set.disjoint_left]
  intro x hx1 hx3
  simp [I1, I3] at hx1 hx3
  have h : shift1 - B < shift3 - M := by
    norm_num [B, shift1, shift3, M, q]
  linarith

theorem I1_I4_disjoint : Disjoint I1 I4 := by
  rw [Set.disjoint_left]
  intro x hx1 hx4
  simp [I1, I4] at hx1 hx4
  have h : shift1 - B < shift4 - M := by
    norm_num [B, shift1, shift4, M, q]
  linarith

theorem I2_I3_disjoint : Disjoint I2 I3 := by
  rw [Set.disjoint_left]
  intro x hx2 hx3
  simp [I2, I3] at hx2 hx3
  have h : shift2 - B < shift3 - M := by
    norm_num [B, shift2, shift3, M, q]
  linarith

theorem I2_I4_disjoint : Disjoint I2 I4 := by
  rw [Set.disjoint_left]
  intro x hx2 hx4
  simp [I2, I4] at hx2 hx4
  have h : shift2 - B < shift4 - M := by
    norm_num [B, shift2, shift4, M, q]
  linarith

theorem I3_I4_disjoint : Disjoint I3 I4 := by
  rw [Set.disjoint_left]
  intro x hx3 hx4
  simp [I3, I4] at hx3 hx4
  have h : shift3 - B < shift4 - M := by
    norm_num [B, shift3, shift4, M, q]
  linarith

lemma longInterval_volume :
    volume LongInterval = ENNReal.ofReal B := by
  have hB : 0 - (-B) = B := by ring
  simp [LongInterval, Real.volume_Ioo, hB]

lemma measurable_tailPiece0 {E : Set ℝ} (hE : MeasurableSet E) :
    MeasurableSet (TailPiece0 E) :=
  hE.inter measurableSet_Icc

lemma measurable_tailPiece1 {E : Set ℝ} (hE : MeasurableSet E) :
    MeasurableSet (TailPiece1 E) :=
  hE.inter measurableSet_Icc

lemma measurable_tailPiece2 {E : Set ℝ} (hE : MeasurableSet E) :
    MeasurableSet (TailPiece2 E) :=
  hE.inter measurableSet_Icc

lemma measurable_tailPiece3 {E : Set ℝ} (hE : MeasurableSet E) :
    MeasurableSet (TailPiece3 E) :=
  hE.inter measurableSet_Icc

lemma measurable_tailPiece4 {E : Set ℝ} (hE : MeasurableSet E) :
    MeasurableSet (TailPiece4 E) :=
  hE.inter measurableSet_Icc

lemma tailPiece_disjoint_of_interval_disjoint
    {E A C : Set ℝ} (hAC : Disjoint A C) :
    Disjoint (E ∩ A) (E ∩ C) := by
  rw [Set.disjoint_left] at hAC ⊢
  intro x hxA hxC
  exact hAC hxA.2 hxC.2

lemma tailPiece0_tailPiece1_disjoint {E : Set ℝ} :
    Disjoint (TailPiece0 E) (TailPiece1 E) :=
  tailPiece_disjoint_of_interval_disjoint I0_I1_disjoint

lemma tailPiece0_tailPiece2_disjoint {E : Set ℝ} :
    Disjoint (TailPiece0 E) (TailPiece2 E) :=
  tailPiece_disjoint_of_interval_disjoint I0_I2_disjoint

lemma tailPiece0_tailPiece3_disjoint {E : Set ℝ} :
    Disjoint (TailPiece0 E) (TailPiece3 E) :=
  tailPiece_disjoint_of_interval_disjoint I0_I3_disjoint

lemma tailPiece0_tailPiece4_disjoint {E : Set ℝ} :
    Disjoint (TailPiece0 E) (TailPiece4 E) :=
  tailPiece_disjoint_of_interval_disjoint I0_I4_disjoint

lemma tailPiece1_tailPiece2_disjoint {E : Set ℝ} :
    Disjoint (TailPiece1 E) (TailPiece2 E) :=
  tailPiece_disjoint_of_interval_disjoint I1_I2_disjoint

lemma tailPiece1_tailPiece3_disjoint {E : Set ℝ} :
    Disjoint (TailPiece1 E) (TailPiece3 E) :=
  tailPiece_disjoint_of_interval_disjoint I1_I3_disjoint

lemma tailPiece1_tailPiece4_disjoint {E : Set ℝ} :
    Disjoint (TailPiece1 E) (TailPiece4 E) :=
  tailPiece_disjoint_of_interval_disjoint I1_I4_disjoint

lemma tailPiece2_tailPiece3_disjoint {E : Set ℝ} :
    Disjoint (TailPiece2 E) (TailPiece3 E) :=
  tailPiece_disjoint_of_interval_disjoint I2_I3_disjoint

lemma tailPiece2_tailPiece4_disjoint {E : Set ℝ} :
    Disjoint (TailPiece2 E) (TailPiece4 E) :=
  tailPiece_disjoint_of_interval_disjoint I2_I4_disjoint

lemma tailPiece3_tailPiece4_disjoint {E : Set ℝ} :
    Disjoint (TailPiece3 E) (TailPiece4 E) :=
  tailPiece_disjoint_of_interval_disjoint I3_I4_disjoint

lemma tailUnion01_disjoint_2 {E : Set ℝ} :
    Disjoint (TailPiece0 E ∪ TailPiece1 E) (TailPiece2 E) := by
  rw [Set.disjoint_union_left]
  exact ⟨tailPiece0_tailPiece2_disjoint, tailPiece1_tailPiece2_disjoint⟩

lemma tailUnion012_disjoint_3 {E : Set ℝ} :
    Disjoint (TailPiece0 E ∪ TailPiece1 E ∪ TailPiece2 E)
      (TailPiece3 E) := by
  rw [Set.disjoint_union_left]
  exact ⟨by
    rw [Set.disjoint_union_left]
    exact ⟨tailPiece0_tailPiece3_disjoint, tailPiece1_tailPiece3_disjoint⟩,
    tailPiece2_tailPiece3_disjoint⟩

lemma tailUnion0123_disjoint_4 {E : Set ℝ} :
    Disjoint (TailPiece0 E ∪ TailPiece1 E ∪ TailPiece2 E ∪
      TailPiece3 E) (TailPiece4 E) := by
  rw [Set.disjoint_union_left]
  exact ⟨by
    rw [Set.disjoint_union_left]
    exact ⟨by
      rw [Set.disjoint_union_left]
      exact ⟨tailPiece0_tailPiece4_disjoint, tailPiece1_tailPiece4_disjoint⟩,
      tailPiece2_tailPiece4_disjoint⟩,
    tailPiece3_tailPiece4_disjoint⟩

theorem tailPieces_union_volume_eq_sum {E : Set ℝ}
    (hE : MeasurableSet E) :
    volume (TailPiece0 E ∪ TailPiece1 E ∪ TailPiece2 E ∪
      TailPiece3 E ∪ TailPiece4 E) =
      volume (TailPiece0 E) + volume (TailPiece1 E) +
        volume (TailPiece2 E) + volume (TailPiece3 E) +
        volume (TailPiece4 E) := by
  have hP1 := measurable_tailPiece1 hE
  have hP2 := measurable_tailPiece2 hE
  have hP3 := measurable_tailPiece3 hE
  have hP4 := measurable_tailPiece4 hE
  calc
    volume (TailPiece0 E ∪ TailPiece1 E ∪ TailPiece2 E ∪
        TailPiece3 E ∪ TailPiece4 E)
        = volume (TailPiece0 E ∪ TailPiece1 E ∪ TailPiece2 E ∪
            TailPiece3 E) + volume (TailPiece4 E) := by
          rw [measure_union tailUnion0123_disjoint_4 hP4]
    _ = (volume (TailPiece0 E ∪ TailPiece1 E ∪ TailPiece2 E) +
            volume (TailPiece3 E)) + volume (TailPiece4 E) := by
          rw [measure_union tailUnion012_disjoint_3 hP3]
    _ = ((volume (TailPiece0 E ∪ TailPiece1 E) +
            volume (TailPiece2 E)) + volume (TailPiece3 E)) +
            volume (TailPiece4 E) := by
          rw [measure_union tailUnion01_disjoint_2 hP2]
    _ = (((volume (TailPiece0 E) + volume (TailPiece1 E)) +
            volume (TailPiece2 E)) + volume (TailPiece3 E)) +
            volume (TailPiece4 E) := by
          rw [measure_union tailPiece0_tailPiece1_disjoint hP1]
    _ = volume (TailPiece0 E) + volume (TailPiece1 E) +
        volume (TailPiece2 E) + volume (TailPiece3 E) +
        volume (TailPiece4 E) := by
          ac_rfl

lemma tailPieces_union_subset (E : Set ℝ) :
    TailPiece0 E ∪ TailPiece1 E ∪ TailPiece2 E ∪ TailPiece3 E ∪
      TailPiece4 E ⊆ E := by
  intro x hx
  rcases hx with hx0123 | hx4
  · rcases hx0123 with hx012 | hx3
    · rcases hx012 with hx01 | hx2
      · rcases hx01 with hx0 | hx1
        · exact hx0.1
        · exact hx1.1
      · exact hx2.1
    · exact hx3.1
  · exact hx4.1

theorem tailSelector_volume_lower_bound
    {E : Set ℝ}
    (hE : MeasurableSet E)
    (selector : TailSelector E) :
    ENNReal.ofReal (M - B) ≤ volume E := by
  have hsum := tailSelector_length_sum_lower_bound hE selector
  have hsum_eq := tailPieces_union_volume_eq_sum hE
  have hsub : TailPiece0 E ∪ TailPiece1 E ∪ TailPiece2 E ∪
      TailPiece3 E ∪ TailPiece4 E ⊆ E :=
    tailPieces_union_subset E
  calc
    ENNReal.ofReal (M - B)
        ≤ volume (TailPiece0 E) + volume (TailPiece1 E) +
          volume (TailPiece2 E) + volume (TailPiece3 E) +
          volume (TailPiece4 E) := hsum
    _ = volume (TailPiece0 E ∪ TailPiece1 E ∪ TailPiece2 E ∪
          TailPiece3 E ∪ TailPiece4 E) := hsum_eq.symm
    _ ≤ volume E := measure_mono (μ := volume) hsub

lemma swept0_not_mem_long_of_tail {a : ℝ} (ha : a ∈ TailParameter) :
    swept0 a ∉ LongInterval := by
  have hdisj := I0_disjoint_Long
  rw [Set.disjoint_left] at hdisj
  exact fun hlong => hdisj (a := swept0 a)
    (by simpa [TailParameter, swept0] using ha) hlong

lemma swept_mem_shifted_tail_interval {a s : ℝ}
    (ha : a ∈ TailParameter) :
    a + s ∈ Icc (s - M) (s - B) :=
  (mem_shifted_tail_interval_iff (s := s)).2
    (by simpa [TailParameter] using ha)

lemma swept1_mem_I1_of_tail {a : ℝ} (ha : a ∈ TailParameter) :
    swept1 a ∈ I1 := by
  simpa [swept1, I1] using swept_mem_shifted_tail_interval (s := shift1) ha

lemma swept2_mem_I2_of_tail {a : ℝ} (ha : a ∈ TailParameter) :
    swept2 a ∈ I2 := by
  simpa [swept2, I2] using swept_mem_shifted_tail_interval (s := shift2) ha

lemma swept3_mem_I3_of_tail {a : ℝ} (ha : a ∈ TailParameter) :
    swept3 a ∈ I3 := by
  simpa [swept3, I3] using swept_mem_shifted_tail_interval (s := shift3) ha

lemma swept4_mem_I4_of_tail {a : ℝ} (ha : a ∈ TailParameter) :
    swept4 a ∈ I4 := by
  simpa [swept4, I4] using swept_mem_shifted_tail_interval (s := shift4) ha

lemma swept1_not_mem_long_of_tail {a : ℝ} (ha : a ∈ TailParameter) :
    swept1 a ∉ LongInterval := by
  have hdisj := I1_disjoint_Long
  rw [Set.disjoint_left] at hdisj
  exact fun hlong => hdisj (a := swept1 a) (swept1_mem_I1_of_tail ha) hlong

lemma swept2_not_mem_long_of_tail {a : ℝ} (ha : a ∈ TailParameter) :
    swept2 a ∉ LongInterval := by
  have hdisj := I2_disjoint_Long
  rw [Set.disjoint_left] at hdisj
  exact fun hlong => hdisj (a := swept2 a) (swept2_mem_I2_of_tail ha) hlong

lemma swept3_not_mem_long_of_tail {a : ℝ} (ha : a ∈ TailParameter) :
    swept3 a ∉ LongInterval := by
  have hdisj := I3_disjoint_Long
  rw [Set.disjoint_left] at hdisj
  exact fun hlong => hdisj (a := swept3 a) (swept3_mem_I3_of_tail ha) hlong

lemma swept4_not_mem_long_of_tail {a : ℝ} (ha : a ∈ TailParameter) :
    swept4 a ∉ LongInterval := by
  have hdisj := I4_disjoint_Long
  rw [Set.disjoint_left] at hdisj
  exact fun hlong => hdisj (a := swept4 a) (swept4_mem_I4_of_tail ha) hlong

theorem tailSelector_diff_long {E : Set ℝ}
    (selector : TailSelector E) :
    TailSelector (E \ LongInterval) := by
  intro a ha
  rcases selector a ha with h0 | h1 | h2 | h3 | h4
  · exact Or.inl ⟨h0, swept0_not_mem_long_of_tail ha⟩
  · exact Or.inr (Or.inl ⟨h1, swept1_not_mem_long_of_tail ha⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h2, swept2_not_mem_long_of_tail ha⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h3, swept3_not_mem_long_of_tail ha⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h4, swept4_not_mem_long_of_tail ha⟩)))

lemma long_disjoint_diff (E : Set ℝ) :
    Disjoint LongInterval (E \ LongInterval) := by
  rw [Set.disjoint_left]
  intro x hxLong hxDiff
  exact hxDiff.2 hxLong

lemma long_union_diff_subset_of_long_subset {E : Set ℝ}
    (hLong : LongInterval ⊆ E) :
    LongInterval ∪ (E \ LongInterval) ⊆ E := by
  intro x hx
  rcases hx with hxLong | hxDiff
  · exact hLong hxLong
  · exact hxDiff.1

theorem long_and_tail_selector_volume_lower_bound
    {E : Set ℝ}
    (hE : MeasurableSet E)
    (hLong : LongInterval ⊆ E)
    (selector : TailSelector E) :
    ENNReal.ofReal M ≤ volume E := by
  have htail :
      ENNReal.ofReal (M - B) ≤ volume (E \ LongInterval) :=
    tailSelector_volume_lower_bound (hE.diff measurableSet_Ioo)
      (tailSelector_diff_long selector)
  have hsplit :
      ENNReal.ofReal M =
        ENNReal.ofReal B + ENNReal.ofReal (M - B) := by
    have hB_nonneg : 0 ≤ B := by
      norm_num [B, q]
    have hTail_nonneg : 0 ≤ M - B := by
      norm_num [M, B, q]
    have hreal : M = B + (M - B) := by ring
    calc
      ENNReal.ofReal M
          = ENNReal.ofReal (B + (M - B)) := congrArg ENNReal.ofReal hreal
      _ = ENNReal.ofReal B + ENNReal.ofReal (M - B) :=
          ENNReal.ofReal_add hB_nonneg hTail_nonneg
  have hmeasure :
      volume (LongInterval ∪ (E \ LongInterval)) =
        volume LongInterval + volume (E \ LongInterval) := by
    rw [measure_union (long_disjoint_diff E) (hE.diff measurableSet_Ioo)]
  calc
    ENNReal.ofReal M
        = ENNReal.ofReal B + ENNReal.ofReal (M - B) := hsplit
    _ ≤ volume LongInterval + volume (E \ LongInterval) := by
          exact add_le_add (by rw [longInterval_volume]) htail
    _ = volume (LongInterval ∪ (E \ LongInterval)) := hmeasure.symm
    _ ≤ volume E :=
          measure_mono (μ := volume) (long_union_diff_subset_of_long_subset hLong)

theorem augmented_positiveSet_long_and_tail_selector_volume_lower_bound
    (μ : MeasureTheory.ProbabilityMeasure StandardReduction.UnitInterval1038)
    (hLong : LongInterval ⊆ StandardReduction.unitIntervalAugmentedPositiveSet μ)
    (selector : TailSelector (StandardReduction.unitIntervalAugmentedPositiveSet μ)) :
    ENNReal.ofReal M ≤
      volume (StandardReduction.PositiveSet
        (StandardReduction.unitIntervalLogPotential μ)) := by
  have hposMeas :
      MeasurableSet
        (StandardReduction.PositiveSet
          (StandardReduction.unitIntervalLogPotential μ)) := by
    simpa [StandardReduction.PositiveSet] using
      (StandardReduction.unitIntervalLogPotential_measurableSet_threshold μ 0)
  have hAugMeas :
      MeasurableSet (StandardReduction.unitIntervalAugmentedPositiveSet μ) :=
    hposMeas.union (StandardReduction.diagonalAtomSet_measurableSet μ)
  have hAugLower :
      ENNReal.ofReal M ≤
        volume (StandardReduction.unitIntervalAugmentedPositiveSet μ) :=
    long_and_tail_selector_volume_lower_bound hAugMeas hLong selector
  exact StandardReduction.unitIntervalAugmentedPositiveSet_lower_bound_transfers μ hAugLower

/-! ## Weaker closure matching the current `forcing_1708` certificate -/

lemma longInterval1700_volume :
    volume LongInterval1700 = ENNReal.ofReal B1700 := by
  simp [LongInterval1700, Real.volume_Ioo, B1700, q]

lemma swept0_not_mem_long1700_of_tail {a : ℝ} (ha : a ∈ TailParameter) :
    swept0 a ∉ LongInterval1700 := by
  intro hlong
  simp [TailParameter, I0, swept0, LongInterval1700, M, B, B1700, q] at ha hlong
  linarith

lemma swept1_not_mem_long1700_of_tail {a : ℝ} (ha : a ∈ TailParameter) :
    swept1 a ∉ LongInterval1700 := by
  intro hlong
  have hmem := swept1_mem_I1_of_tail ha
  simp [I1, swept1, LongInterval1700, M, B, B1700, shift1, q] at hmem hlong
  linarith

lemma swept2_not_mem_long1700_of_tail {a : ℝ} (ha : a ∈ TailParameter) :
    swept2 a ∉ LongInterval1700 := by
  intro hlong
  have hmem := swept2_mem_I2_of_tail ha
  simp [I2, swept2, LongInterval1700, M, B, B1700, shift2, q] at hmem hlong
  linarith

lemma swept3_not_mem_long1700_of_tail {a : ℝ} (ha : a ∈ TailParameter) :
    swept3 a ∉ LongInterval1700 := by
  intro hlong
  have hmem := swept3_mem_I3_of_tail ha
  simp [I3, swept3, LongInterval1700, M, B, B1700, shift3, q] at hmem hlong
  linarith

lemma swept4_not_mem_long1700_of_tail {a : ℝ} (ha : a ∈ TailParameter) :
    swept4 a ∉ LongInterval1700 := by
  intro hlong
  have hmem := swept4_mem_I4_of_tail ha
  simp [I4, swept4, LongInterval1700, M, B, B1700, shift4, q] at hmem hlong
  linarith

theorem tailSelector_diff_long1700 {E : Set ℝ}
    (selector : TailSelector E) :
    TailSelector (E \ LongInterval1700) := by
  intro a ha
  rcases selector a ha with h0 | h1 | h2 | h3 | h4
  · exact Or.inl ⟨h0, swept0_not_mem_long1700_of_tail ha⟩
  · exact Or.inr (Or.inl ⟨h1, swept1_not_mem_long1700_of_tail ha⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h2, swept2_not_mem_long1700_of_tail ha⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h3, swept3_not_mem_long1700_of_tail ha⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h4, swept4_not_mem_long1700_of_tail ha⟩)))

lemma long1700_disjoint_diff (E : Set ℝ) :
    Disjoint LongInterval1700 (E \ LongInterval1700) := by
  rw [Set.disjoint_left]
  intro x hxLong hxDiff
  exact hxDiff.2 hxLong

lemma long1700_union_diff_subset_of_long_subset {E : Set ℝ}
    (hLong : LongInterval1700 ⊆ E) :
    LongInterval1700 ∪ (E \ LongInterval1700) ⊆ E := by
  intro x hx
  rcases hx with hxLong | hxDiff
  · exact hLong hxLong
  · exact hxDiff.1

theorem long1700_and_tail_selector_volume_lower_bound
    {E : Set ℝ}
    (hE : MeasurableSet E)
    (hLong : LongInterval1700 ⊆ E)
    (selector : TailSelector E) :
    ENNReal.ofReal M1700Tail ≤ volume E := by
  have htail :
      ENNReal.ofReal (M - B) ≤ volume (E \ LongInterval1700) :=
    tailSelector_volume_lower_bound (hE.diff measurableSet_Ioo)
      (tailSelector_diff_long1700 selector)
  have hsplit :
      ENNReal.ofReal M1700Tail =
        ENNReal.ofReal B1700 + ENNReal.ofReal (M - B) := by
    have hB_nonneg : 0 ≤ B1700 := by
      norm_num [B1700, q]
    have hTail_nonneg : 0 ≤ M - B := by
      norm_num [M, B, q]
    calc
      ENNReal.ofReal M1700Tail
          = ENNReal.ofReal (B1700 + (M - B)) := by
              rfl
      _ = ENNReal.ofReal B1700 + ENNReal.ofReal (M - B) :=
          ENNReal.ofReal_add hB_nonneg hTail_nonneg
  have hmeasure :
      volume (LongInterval1700 ∪ (E \ LongInterval1700)) =
        volume LongInterval1700 + volume (E \ LongInterval1700) := by
    rw [measure_union (long1700_disjoint_diff E) (hE.diff measurableSet_Ioo)]
  calc
    ENNReal.ofReal M1700Tail
        = ENNReal.ofReal B1700 + ENNReal.ofReal (M - B) := hsplit
    _ ≤ volume LongInterval1700 + volume (E \ LongInterval1700) := by
          exact add_le_add (by rw [longInterval1700_volume]) htail
    _ = volume (LongInterval1700 ∪ (E \ LongInterval1700)) := hmeasure.symm
    _ ≤ volume E :=
          measure_mono (μ := volume) (long1700_union_diff_subset_of_long_subset hLong)

theorem augmented_positiveSet_long1700_and_tail_selector_volume_lower_bound
    (μ : MeasureTheory.ProbabilityMeasure StandardReduction.UnitInterval1038)
    (hLong : LongInterval1700 ⊆ StandardReduction.unitIntervalAugmentedPositiveSet μ)
    (selector : TailSelector (StandardReduction.unitIntervalAugmentedPositiveSet μ)) :
    ENNReal.ofReal M1700Tail ≤
      volume (StandardReduction.PositiveSet
        (StandardReduction.unitIntervalLogPotential μ)) := by
  have hposMeas :
      MeasurableSet
        (StandardReduction.PositiveSet
          (StandardReduction.unitIntervalLogPotential μ)) := by
    simpa [StandardReduction.PositiveSet] using
      (StandardReduction.unitIntervalLogPotential_measurableSet_threshold μ 0)
  have hAugMeas :
      MeasurableSet (StandardReduction.unitIntervalAugmentedPositiveSet μ) :=
    hposMeas.union (StandardReduction.diagonalAtomSet_measurableSet μ)
  have hAugLower :
      ENNReal.ofReal M1700Tail ≤
        volume (StandardReduction.unitIntervalAugmentedPositiveSet μ) :=
    long1700_and_tail_selector_volume_lower_bound hAugMeas hLong selector
  exact StandardReduction.unitIntervalAugmentedPositiveSet_lower_bound_transfers μ hAugLower

theorem augmented_positiveSet_volume_lower_bound_from_duality
    (μ : MeasureTheory.ProbabilityMeasure StandardReduction.UnitInterval1038)
    (w : ℝ → Fin 5 → ℝ)
    (hLong : LongInterval ⊆ StandardReduction.unitIntervalAugmentedPositiveSet μ)
    (hduality : ∀ a : ℝ, a ∈ TailParameter →
      StandardReduction.FiniteAtomicUnitIntervalDualityIdentity
        μ Finset.univ (w a) (sweptAtom a))
    (hw_nonneg : ∀ a : ℝ, a ∈ TailParameter → ∀ i : Fin 5, 0 ≤ w a i)
    (hintegral_pos : ∀ a : ℝ, a ∈ TailParameter →
      0 < ∫ x : StandardReduction.UnitInterval1038,
        StandardReduction.finiteWeightedPotential
          Finset.univ (w a) (sweptAtom a) (x : ℝ)
          ∂(μ : MeasureTheory.Measure StandardReduction.UnitInterval1038)) :
    ENNReal.ofReal M ≤
      volume (StandardReduction.PositiveSet
        (StandardReduction.unitIntervalLogPotential μ)) :=
  augmented_positiveSet_long_and_tail_selector_volume_lower_bound μ hLong
    (tailSelector_from_augmented_duality μ w hduality hw_nonneg hintegral_pos)

theorem augmented_positiveSet_volume_lower_bound_from_normalized_pointwise
    (μ : MeasureTheory.ProbabilityMeasure StandardReduction.UnitInterval1038)
    (w : ℝ → Fin 5 → ℝ)
    (hNorm : UnitIntervalNormalizedSupportAE μ)
    (hLong : LongInterval ⊆ StandardReduction.unitIntervalAugmentedPositiveSet μ)
    (hduality : ∀ a : ℝ, a ∈ TailParameter →
      StandardReduction.FiniteAtomicUnitIntervalDualityIdentity
        μ Finset.univ (w a) (sweptAtom a))
    (hw_nonneg : ∀ a : ℝ, a ∈ TailParameter → ∀ i : Fin 5, 0 ≤ w a i)
    (hint : ∀ a : ℝ, a ∈ TailParameter →
      Integrable
        (fun x : StandardReduction.UnitInterval1038 =>
          StandardReduction.finiteWeightedPotential
            Finset.univ (w a) (sweptAtom a) (x : ℝ))
        (μ : MeasureTheory.Measure StandardReduction.UnitInterval1038))
    (hpoint : ∀ a : ℝ, a ∈ TailParameter →
      ∀ x : StandardReduction.UnitInterval1038,
        ((x : ℝ) = -1 ∨ (x : ℝ) ∈ Icc (0 : ℝ) 1) →
        0 <
          StandardReduction.finiteWeightedPotential
            Finset.univ (w a) (sweptAtom a) (x : ℝ)) :
    ENNReal.ofReal M ≤
      volume (StandardReduction.PositiveSet
        (StandardReduction.unitIntervalLogPotential μ)) :=
  augmented_positiveSet_long_and_tail_selector_volume_lower_bound μ hLong
    (tailSelector_from_augmented_duality_of_normalized_pointwise
      μ w hNorm hduality hw_nonneg hint hpoint)

/-! ## Concrete 560-block piecewise tail certificate bridge -/

def piecewiseTailRouteWeights (a : ℝ) : Fin 5 → ℝ :=
  PiecewiseFiveAtom181460Mathlib.piecewiseTailWeights a

theorem piecewiseTailRouteWeights_nonneg
    {a : ℝ} (ha : a ∈ TailParameter) :
    ∀ i : Fin 5, 0 ≤ piecewiseTailRouteWeights a i := by
  simpa [piecewiseTailRouteWeights, TailParameter, M, B, q]
    using PiecewiseFiveAtom181460Mathlib.piecewiseTailWeights_nonneg
      (a := a) (by simpa [PiecewiseFiveAtom181460Mathlib.M,
        PiecewiseFiveAtom181460Mathlib.B, PiecewiseFiveAtom181460Mathlib.q,
        M, B, q] using ha)

set_option maxHeartbeats 4000000 in
lemma finiteWeightedPotential_piecewiseTailRouteWeights_eq_V
    (a x : ℝ) :
    StandardReduction.finiteWeightedPotential
        Finset.univ (piecewiseTailRouteWeights a) (sweptAtom a) x =
      PiecewiseFiveAtom181460Mathlib.V
        (piecewiseTailRouteWeights a ⟨1, by norm_num⟩)
        (piecewiseTailRouteWeights a ⟨2, by norm_num⟩)
        (piecewiseTailRouteWeights a ⟨3, by norm_num⟩)
        (piecewiseTailRouteWeights a ⟨4, by norm_num⟩) (x - a) := by
  unfold StandardReduction.finiteWeightedPotential
    PiecewiseFiveAtom181460Mathlib.V sweptAtom
    swept0 swept1 swept2 swept3 swept4 shift1 shift2 shift3 shift4
    PiecewiseFiveAtom181460Mathlib.d1 PiecewiseFiveAtom181460Mathlib.d2
    PiecewiseFiveAtom181460Mathlib.d3 PiecewiseFiveAtom181460Mathlib.d4
    PiecewiseFiveAtom181460Mathlib.q q
  simp [Fin.sum_univ_five, one_div, sub_eq_add_neg, add_comm, add_assoc,
    mul_comm, piecewiseTailRouteWeights,
    PiecewiseFiveAtom181460Mathlib.piecewiseTailWeights,
    PiecewiseFiveAtom181460Mathlib.piecewiseBlockWeights]

theorem tailSelector_from_piecewise_tail_duality
    (μ : MeasureTheory.ProbabilityMeasure StandardReduction.UnitInterval1038)
    (hNorm : UnitIntervalNormalizedSupportAE μ)
    (hduality : ∀ a : ℝ, a ∈ TailParameter →
      StandardReduction.FiniteAtomicUnitIntervalDualityIdentity
        μ Finset.univ (piecewiseTailRouteWeights a) (sweptAtom a))
    (hint : ∀ a : ℝ, a ∈ TailParameter →
      Integrable
        (fun x : StandardReduction.UnitInterval1038 =>
          StandardReduction.finiteWeightedPotential
            Finset.univ (piecewiseTailRouteWeights a) (sweptAtom a) (x : ℝ))
        (μ : MeasureTheory.Measure StandardReduction.UnitInterval1038)) :
    TailSelector (StandardReduction.unitIntervalAugmentedPositiveSet μ) := by
  intro a ha
  by_cases h0 : swept0 a ∈ StandardReduction.unitIntervalAugmentedPositiveSet μ
  · exact Or.inl h0
  by_cases h1 : swept1 a ∈ StandardReduction.unitIntervalAugmentedPositiveSet μ
  · exact Or.inr (Or.inl h1)
  by_cases h2 : swept2 a ∈ StandardReduction.unitIntervalAugmentedPositiveSet μ
  · exact Or.inr (Or.inr (Or.inl h2))
  by_cases h3 : swept3 a ∈ StandardReduction.unitIntervalAugmentedPositiveSet μ
  · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
  by_cases h4 : swept4 a ∈ StandardReduction.unitIntervalAugmentedPositiveSet μ
  · exact Or.inr (Or.inr (Or.inr (Or.inr h4)))
  have h0diag : swept0 a ∉ StandardReduction.diagonalAtomSet μ := by
    intro hd
    exact h0 (Or.inr hd)
  have h1diag : swept1 a ∉ StandardReduction.diagonalAtomSet μ := by
    intro hd
    exact h1 (Or.inr hd)
  have h2diag : swept2 a ∉ StandardReduction.diagonalAtomSet μ := by
    intro hd
    exact h2 (Or.inr hd)
  have h3diag : swept3 a ∉ StandardReduction.diagonalAtomSet μ := by
    intro hd
    exact h3 (Or.inr hd)
  have h4diag : swept4 a ∉ StandardReduction.diagonalAtomSet μ := by
    intro hd
    exact h4 (Or.inr hd)
  have hae0 := StandardReduction.ae_ne_of_notMem_diagonalAtomSet
    (μ := μ) (x := swept0 a) h0diag
  have hae1 := StandardReduction.ae_ne_of_notMem_diagonalAtomSet
    (μ := μ) (x := swept1 a) h1diag
  have hae2 := StandardReduction.ae_ne_of_notMem_diagonalAtomSet
    (μ := μ) (x := swept2 a) h2diag
  have hae3 := StandardReduction.ae_ne_of_notMem_diagonalAtomSet
    (μ := μ) (x := swept3 a) h3diag
  have hae4 := StandardReduction.ae_ne_of_notMem_diagonalAtomSet
    (μ := μ) (x := swept4 a) h4diag
  have hpos_ae :
      ∀ᵐ x : StandardReduction.UnitInterval1038
        ∂(μ : MeasureTheory.Measure StandardReduction.UnitInterval1038),
        0 <
          StandardReduction.finiteWeightedPotential
            Finset.univ (piecewiseTailRouteWeights a) (sweptAtom a) (x : ℝ) := by
    filter_upwards [hNorm, hae0, hae1, hae2, hae3, hae4] with x hxNorm hx0 hx1 hx2 hx3 hx4
    have haPiece :
        a ∈ Icc
          (-PiecewiseFiveAtom181460Mathlib.M)
          (-PiecewiseFiveAtom181460Mathlib.B) := by
      simpa [TailParameter, M, B, q,
        PiecewiseFiveAtom181460Mathlib.M,
        PiecewiseFiveAtom181460Mathlib.B,
        PiecewiseFiveAtom181460Mathlib.q] using ha
    have hV := PiecewiseFiveAtom181460Mathlib.piecewiseTail_required_pos
      (a := a) (x := (x : ℝ)) haPiece hxNorm
      (by
        intro hxa
        apply hx0
        dsimp [swept0]
        linarith)
      (by
        intro hxa
        apply hx1
        dsimp [swept1, shift1]
        norm_num [PiecewiseFiveAtom181460Mathlib.d1,
          PiecewiseFiveAtom181460Mathlib.q, q] at hxa ⊢
        linarith)
      (by
        intro hxa
        apply hx2
        dsimp [swept2, shift2]
        norm_num [PiecewiseFiveAtom181460Mathlib.d2,
          PiecewiseFiveAtom181460Mathlib.q, q] at hxa ⊢
        linarith)
      (by
        intro hxa
        apply hx3
        dsimp [swept3, shift3]
        norm_num [PiecewiseFiveAtom181460Mathlib.d3,
          PiecewiseFiveAtom181460Mathlib.q, q] at hxa ⊢
        linarith)
      (by
        intro hxa
        apply hx4
        dsimp [swept4, shift4]
        norm_num [PiecewiseFiveAtom181460Mathlib.d4,
          PiecewiseFiveAtom181460Mathlib.q, q] at hxa ⊢
        linarith)
    simpa [finiteWeightedPotential_piecewiseTailRouteWeights_eq_V] using hV
  have hintegral_pos :
      0 < ∫ x : StandardReduction.UnitInterval1038,
        StandardReduction.finiteWeightedPotential
          Finset.univ (piecewiseTailRouteWeights a) (sweptAtom a) (x : ℝ)
          ∂(μ : MeasureTheory.Measure StandardReduction.UnitInterval1038) :=
    integral_pos_of_integrable_ae_pos_probability μ (hint a ha) hpos_ae
  rcases (hduality a ha).selects_augmented_atom
      (by
        intro i _hi
        exact piecewiseTailRouteWeights_nonneg ha i)
      hintegral_pos with
    ⟨i, _hi, hmem⟩
  fin_cases i <;> simp [sweptAtom] at hmem
  · exact Or.inl hmem
  · exact Or.inr (Or.inl hmem)
  · exact Or.inr (Or.inr (Or.inl hmem))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hmem)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hmem)))

lemma finiteWeightedPotential_integrable_of_atom_kernels
    (μ : MeasureTheory.ProbabilityMeasure StandardReduction.UnitInterval1038)
    (w atom : Fin 5 → ℝ)
    (hlog_int : ∀ i : Fin 5, i ∈ Finset.univ →
      Integrable
        (fun x : StandardReduction.UnitInterval1038 =>
          Real.log (1 / |(x : ℝ) - atom i|))
        (μ : MeasureTheory.Measure StandardReduction.UnitInterval1038)) :
    Integrable
      (fun x : StandardReduction.UnitInterval1038 =>
        StandardReduction.finiteWeightedPotential Finset.univ w atom (x : ℝ))
      (μ : MeasureTheory.Measure StandardReduction.UnitInterval1038) := by
  unfold StandardReduction.finiteWeightedPotential
  exact integrable_finset_sum Finset.univ (fun i hi =>
    (hlog_int i hi).const_mul (w i))

theorem tailSelector_from_piecewise_tail_tailMass
    (μ : MeasureTheory.ProbabilityMeasure StandardReduction.UnitInterval1038)
    (hNorm : UnitIntervalNormalizedSupportAE μ)
    (htailFinite : TailMassFiniteHypothesis μ) :
    TailSelector (StandardReduction.unitIntervalAugmentedPositiveSet μ) := by
  intro a ha
  by_cases h0 : swept0 a ∈ StandardReduction.unitIntervalAugmentedPositiveSet μ
  · exact Or.inl h0
  by_cases h1 : swept1 a ∈ StandardReduction.unitIntervalAugmentedPositiveSet μ
  · exact Or.inr (Or.inl h1)
  by_cases h2 : swept2 a ∈ StandardReduction.unitIntervalAugmentedPositiveSet μ
  · exact Or.inr (Or.inr (Or.inl h2))
  by_cases h3 : swept3 a ∈ StandardReduction.unitIntervalAugmentedPositiveSet μ
  · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
  by_cases h4 : swept4 a ∈ StandardReduction.unitIntervalAugmentedPositiveSet μ
  · exact Or.inr (Or.inr (Or.inr (Or.inr h4)))
  have hnotAug : ∀ i : Fin 5,
      sweptAtom a i ∉ StandardReduction.unitIntervalAugmentedPositiveSet μ := by
    intro i
    fin_cases i
    · simpa [sweptAtom] using h0
    · simpa [sweptAtom] using h1
    · simpa [sweptAtom] using h2
    · simpa [sweptAtom] using h3
    · simpa [sweptAtom] using h4
  have hoffdiag : ∀ i : Fin 5, sweptAtom a i ∉ StandardReduction.diagonalAtomSet μ := by
    intro i hd
    exact hnotAug i (Or.inr hd)
  have hatom :
      ∀ i : Fin 5, i ∈ Finset.univ →
        (sweptAtom a i < -1 ∨ 1 < sweptAtom a i) ∨
          (sweptAtom a i ∈ Icc (-1 : ℝ) 1 ∧
            sweptAtom a i ∉ StandardReduction.diagonalAtomSet μ ∧
            ∃ ε : ℝ, 0 < ε ∧
              StandardReduction.singularTailMass ε μ (sweptAtom a i) < ∞) := by
    intro i _hi
    by_cases hunit : sweptAtom a i ∈ Icc (-1 : ℝ) 1
    · exact Or.inr ⟨hunit, hoffdiag i, htailFinite a ha i hunit (hoffdiag i)⟩
    · have hout : sweptAtom a i < -1 ∨ 1 < sweptAtom a i := by
        have hlt_or_gt : sweptAtom a i < -1 ∨ 1 < sweptAtom a i := by
          by_contra hbad
          push Not at hbad
          exact hunit ⟨hbad.1, hbad.2⟩
        exact hlt_or_gt
      exact Or.inl hout
  have hduality :
      StandardReduction.FiniteAtomicUnitIntervalDualityIdentity
        μ Finset.univ (piecewiseTailRouteWeights a) (sweptAtom a) :=
    StandardReduction.FiniteAtomicUnitIntervalDualityIdentity.of_atoms_outside_or_offDiagonal_tailMass
      μ Finset.univ (piecewiseTailRouteWeights a) (sweptAtom a) hatom
  have hlog_int : ∀ i : Fin 5, i ∈ Finset.univ →
      Integrable
        (fun x : StandardReduction.UnitInterval1038 =>
          Real.log (1 / |(x : ℝ) - sweptAtom a i|))
        (μ : MeasureTheory.Measure StandardReduction.UnitInterval1038) := by
    intro i hi
    rcases hatom i hi with houtside | hinside
    · rcases houtside with hleft | hright
      · have hbase := StandardReduction.unitInterval_logKernel_integrable_of_left_outside
          (μ := μ) (x := sweptAtom a i) hleft
        exact hbase.congr (Filter.Eventually.of_forall (fun x => by
          simp [abs_sub_comm]))
      · have hbase := StandardReduction.unitInterval_logKernel_integrable_of_right_outside
          (μ := μ) (x := sweptAtom a i) hright
        exact hbase.congr (Filter.Eventually.of_forall (fun x => by
          simp [abs_sub_comm]))
    · rcases hinside with ⟨_hunit, hoff, ε, hε, htail⟩
      exact StandardReduction.unitInterval_logKernel_integrable_of_notMem_diagonalAtomSet_tailMass
        hε hoff htail
  have hint :
      Integrable
        (fun x : StandardReduction.UnitInterval1038 =>
          StandardReduction.finiteWeightedPotential
            Finset.univ (piecewiseTailRouteWeights a) (sweptAtom a) (x : ℝ))
        (μ : MeasureTheory.Measure StandardReduction.UnitInterval1038) :=
    finiteWeightedPotential_integrable_of_atom_kernels μ
      (piecewiseTailRouteWeights a) (sweptAtom a) hlog_int
  have hpos_ae :
      ∀ᵐ x : StandardReduction.UnitInterval1038
        ∂(μ : MeasureTheory.Measure StandardReduction.UnitInterval1038),
        0 <
          StandardReduction.finiteWeightedPotential
            Finset.univ (piecewiseTailRouteWeights a) (sweptAtom a) (x : ℝ) := by
    filter_upwards [hNorm,
      StandardReduction.ae_ne_of_notMem_diagonalAtomSet (μ := μ) (x := swept0 a) (hoffdiag ⟨0, by norm_num⟩),
      StandardReduction.ae_ne_of_notMem_diagonalAtomSet (μ := μ) (x := swept1 a) (hoffdiag ⟨1, by norm_num⟩),
      StandardReduction.ae_ne_of_notMem_diagonalAtomSet (μ := μ) (x := swept2 a) (hoffdiag ⟨2, by norm_num⟩),
      StandardReduction.ae_ne_of_notMem_diagonalAtomSet (μ := μ) (x := swept3 a) (hoffdiag ⟨3, by norm_num⟩),
      StandardReduction.ae_ne_of_notMem_diagonalAtomSet (μ := μ) (x := swept4 a) (hoffdiag ⟨4, by norm_num⟩)] with x hxNorm hx0 hx1 hx2 hx3 hx4
    have haPiece :
        a ∈ Icc
          (-PiecewiseFiveAtom181460Mathlib.M)
          (-PiecewiseFiveAtom181460Mathlib.B) := by
      simpa [TailParameter, M, B, q,
        PiecewiseFiveAtom181460Mathlib.M,
        PiecewiseFiveAtom181460Mathlib.B,
        PiecewiseFiveAtom181460Mathlib.q] using ha
    have hV := PiecewiseFiveAtom181460Mathlib.piecewiseTail_required_pos
      (a := a) (x := (x : ℝ)) haPiece hxNorm
      (by intro hxa; apply hx0; dsimp [swept0]; linarith)
      (by
        intro hxa; apply hx1; dsimp [swept1, shift1]
        norm_num [PiecewiseFiveAtom181460Mathlib.d1, PiecewiseFiveAtom181460Mathlib.q, q] at hxa ⊢
        linarith)
      (by
        intro hxa; apply hx2; dsimp [swept2, shift2]
        norm_num [PiecewiseFiveAtom181460Mathlib.d2, PiecewiseFiveAtom181460Mathlib.q, q] at hxa ⊢
        linarith)
      (by
        intro hxa; apply hx3; dsimp [swept3, shift3]
        norm_num [PiecewiseFiveAtom181460Mathlib.d3, PiecewiseFiveAtom181460Mathlib.q, q] at hxa ⊢
        linarith)
      (by
        intro hxa; apply hx4; dsimp [swept4, shift4]
        norm_num [PiecewiseFiveAtom181460Mathlib.d4, PiecewiseFiveAtom181460Mathlib.q, q] at hxa ⊢
        linarith)
    simpa [finiteWeightedPotential_piecewiseTailRouteWeights_eq_V] using hV
  have hintegral_pos :
      0 < ∫ x : StandardReduction.UnitInterval1038,
        StandardReduction.finiteWeightedPotential
          Finset.univ (piecewiseTailRouteWeights a) (sweptAtom a) (x : ℝ)
          ∂(μ : MeasureTheory.Measure StandardReduction.UnitInterval1038) :=
    integral_pos_of_integrable_ae_pos_probability μ hint hpos_ae
  rcases hduality.selects_augmented_atom
      (by intro i _hi; exact piecewiseTailRouteWeights_nonneg ha i)
      hintegral_pos with
    ⟨i, _hi, hmem⟩
  fin_cases i <;> simp [sweptAtom] at hmem
  · exact Or.inl hmem
  · exact Or.inr (Or.inl hmem)
  · exact Or.inr (Or.inr (Or.inl hmem))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hmem)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hmem)))

theorem augmented_positiveSet_volume_lower_bound_from_piecewise_tail_tailMass
    (μ : MeasureTheory.ProbabilityMeasure StandardReduction.UnitInterval1038)
    (hNorm : UnitIntervalNormalizedSupportAE μ)
    (hLong : LongInterval ⊆ StandardReduction.unitIntervalAugmentedPositiveSet μ)
    (htailFinite : TailMassFiniteHypothesis μ) :
    ENNReal.ofReal M ≤
      volume (StandardReduction.PositiveSet
        (StandardReduction.unitIntervalLogPotential μ)) :=
  augmented_positiveSet_long_and_tail_selector_volume_lower_bound μ hLong
    (tailSelector_from_piecewise_tail_tailMass μ hNorm htailFinite)

/--
Route closure with the forcing branch exposed as an alternative.

The forcing package is expected to prove the left branch: either the long
interval is already contained in the augmented positive set, or the positive set
has a stronger lower bound.  This theorem records the exact handoff needed by
the `M = 1.814600` tail certificate.
-/
theorem augmented_positiveSet_volume_lower_bound_from_forcing_or_tailMass
    (μ : MeasureTheory.ProbabilityMeasure StandardReduction.UnitInterval1038)
    (hNorm : UnitIntervalNormalizedSupportAE μ)
    (hforcing :
      ENNReal.ofReal M ≤
          volume (StandardReduction.PositiveSet
            (StandardReduction.unitIntervalLogPotential μ)) ∨
        LongInterval ⊆ StandardReduction.unitIntervalAugmentedPositiveSet μ)
    (htailFinite : TailMassFiniteHypothesis μ) :
    ENNReal.ofReal M ≤
      volume (StandardReduction.PositiveSet
        (StandardReduction.unitIntervalLogPotential μ)) := by
  rcases hforcing with hdone | hLong
  · exact hdone
  · exact augmented_positiveSet_volume_lower_bound_from_piecewise_tail_tailMass
      μ hNorm hLong htailFinite

/--
Handoff theorem for the earlier `1.708` forcing branch.

It is enough for the forcing branch to prove that failure of the long interval
already gives the stronger `1.836` lower bound.  Since `M = 1.814600 < 1.836`,
the piecewise tail route handles the complementary long-interval case.
-/
theorem augmented_positiveSet_volume_lower_bound_from_forcing1836_or_tailMass
    (μ : MeasureTheory.ProbabilityMeasure StandardReduction.UnitInterval1038)
    (hNorm : UnitIntervalNormalizedSupportAE μ)
    (hforcing1836 :
      ¬ LongInterval ⊆ StandardReduction.unitIntervalAugmentedPositiveSet μ →
        ENNReal.ofReal (q 1836 1000) ≤
          volume (StandardReduction.PositiveSet
            (StandardReduction.unitIntervalLogPotential μ)))
    (htailFinite : TailMassFiniteHypothesis μ) :
    ENNReal.ofReal M ≤
      volume (StandardReduction.PositiveSet
        (StandardReduction.unitIntervalLogPotential μ)) := by
  by_cases hLong : LongInterval ⊆ StandardReduction.unitIntervalAugmentedPositiveSet μ
  · exact augmented_positiveSet_volume_lower_bound_from_piecewise_tail_tailMass
      μ hNorm hLong htailFinite
  · have h1836 := hforcing1836 hLong
    exact le_trans (by norm_num [M, q]) h1836

/--
Route closure matching the currently formalized `forcing_1708` constants.

The current forcing certificate has base interval `(-1.7, 0)` and an `1.82`
fallback, so together with the same 1.814600 tail selector it closes the weaker
bound `M1700Tail = 1.8066`.  This theorem prevents that certificate from being
mistaken for the stronger `hforcing1836` handoff needed above.
-/
theorem augmented_positiveSet_volume_lower_bound_from_forcing1700_or_tailMass
    (μ : MeasureTheory.ProbabilityMeasure StandardReduction.UnitInterval1038)
    (hNorm : UnitIntervalNormalizedSupportAE μ)
    (hforcing1820 :
      ¬ LongInterval1700 ⊆ StandardReduction.unitIntervalAugmentedPositiveSet μ →
        ENNReal.ofReal (q 182 100) ≤
          volume (StandardReduction.PositiveSet
            (StandardReduction.unitIntervalLogPotential μ)))
    (htailFinite : TailMassFiniteHypothesis μ) :
    ENNReal.ofReal M1700Tail ≤
      volume (StandardReduction.PositiveSet
        (StandardReduction.unitIntervalLogPotential μ)) := by
  by_cases hLong : LongInterval1700 ⊆ StandardReduction.unitIntervalAugmentedPositiveSet μ
  · exact augmented_positiveSet_long1700_and_tail_selector_volume_lower_bound μ hLong
      (tailSelector_from_piecewise_tail_tailMass μ hNorm htailFinite)
  · have h1820 := hforcing1820 hLong
    exact le_trans (by norm_num [M1700Tail, B1700, Tail, M, B, q]) h1820

theorem augmented_positiveSet_volume_lower_bound_from_piecewise_tail_duality
    (μ : MeasureTheory.ProbabilityMeasure StandardReduction.UnitInterval1038)
    (hNorm : UnitIntervalNormalizedSupportAE μ)
    (hLong : LongInterval ⊆ StandardReduction.unitIntervalAugmentedPositiveSet μ)
    (hduality : ∀ a : ℝ, a ∈ TailParameter →
      StandardReduction.FiniteAtomicUnitIntervalDualityIdentity
        μ Finset.univ (piecewiseTailRouteWeights a) (sweptAtom a))
    (hint : ∀ a : ℝ, a ∈ TailParameter →
      Integrable
        (fun x : StandardReduction.UnitInterval1038 =>
          StandardReduction.finiteWeightedPotential
            Finset.univ (piecewiseTailRouteWeights a) (sweptAtom a) (x : ℝ))
        (μ : MeasureTheory.Measure StandardReduction.UnitInterval1038)) :
    ENNReal.ofReal M ≤
      volume (StandardReduction.PositiveSet
        (StandardReduction.unitIntervalLogPotential μ)) :=
  augmented_positiveSet_long_and_tail_selector_volume_lower_bound μ hLong
    (tailSelector_from_piecewise_tail_duality μ hNorm hduality hint)

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

end

end Route181460Closure
end Erdos1038
