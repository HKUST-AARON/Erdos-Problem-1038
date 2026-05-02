import Mathlib

/-!
# Route closure for the `M = 1.806304` finite-atom update

This file is the top-level bookkeeping theorem for the conditional finite-atom
route.  The heavy finite checks live in the sibling folders:

* `finite_atoms/forcing_1708/`
* `finite_atoms/five_atom_1806304/`
* `finite_atoms/common/`

The purpose of this file is to make the final route arithmetic and implication
explicit in Lean.
-/

namespace Erdos1038
namespace Route1806304Closure

noncomputable section

open Set

def q (n d : ℕ) : ℝ := (n : ℝ) / (d : ℝ)

def M : ℝ := q 1806304 1000000
def T : ℝ := q 1708 1000
def Tail : ℝ := M - T

theorem tail_value : Tail = q 98304 1000000 := by
  norm_num [Tail, M, T, q]

theorem final_sum : T + Tail = M := by
  norm_num [Tail, M, T, q]

theorem target_below_forcing_threshold : M < q 1836 1000 := by
  norm_num [M, q]

/-- A deliberately abstract length-contribution predicate.  The finite Lean
certificates prove the local positivity/selector blocks; the measure-theoretic
sweep framework supplies concrete instances of this predicate. -/
def HasLengthAtLeast (_E : Set ℝ) (_L : ℝ) : Prop := True

/-- Long forcing branch contribution: the previous branch gives length `T`. -/
def LongContribution (LengthAtLeast : ℝ → Prop) : Prop :=
  LengthAtLeast T

/-- Tail block contribution: the five-atom tail gives length `Tail = M - T`. -/
def TailContribution (LengthAtLeast : ℝ → Prop) : Prop :=
  LengthAtLeast Tail

/-- Abstract additivity rule for the disjoint long and tail contributions. -/
def AddContributionRule (LengthAtLeast : ℝ → Prop) : Prop :=
  LengthAtLeast T → LengthAtLeast Tail → LengthAtLeast M

/-- Conditional closure theorem for the finite-atom route at `M = 1.806304`. -/
theorem route_closure
    {LengthAtLeast : ℝ → Prop}
    (hLong : LongContribution LengthAtLeast)
    (hTail : TailContribution LengthAtLeast)
    (hAdd : AddContributionRule LengthAtLeast) :
    LengthAtLeast M := by
  exact hAdd hLong hTail

/-- Same closure theorem with the target decimal unfolded. -/
theorem route_closure_decimal
    {LengthAtLeast : ℝ → Prop}
    (hLong : LongContribution LengthAtLeast)
    (hTail : TailContribution LengthAtLeast)
    (hAdd : AddContributionRule LengthAtLeast) :
    LengthAtLeast (q 1806304 1000000) := by
  simpa [M] using route_closure hLong hTail hAdd

/-- Bundle of internal route arithmetic facts. -/
theorem route_arithmetic_certificate :
    Tail = q 98304 1000000 ∧ T + Tail = M ∧ M < q 1836 1000 := by
  exact ⟨tail_value, final_sum, target_below_forcing_threshold⟩

end

end Route1806304Closure
end Erdos1038
