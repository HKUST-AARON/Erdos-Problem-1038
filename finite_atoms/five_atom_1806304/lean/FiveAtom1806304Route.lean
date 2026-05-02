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
