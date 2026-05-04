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
