import finite_atoms.standard_reduction.lean.LowerSemicontinuity

/-!
# Minimizer-existence layer for the standard reduction

This module turns lower-semicontinuity of the relaxed objective into a named
minimizer package that later variational arguments can consume.
-/

namespace Erdos1038
namespace StandardReduction
namespace MinimizerExistence

noncomputable section

open Set
open MeasureTheory
open scoped ENNReal BigOperators

/-- A relaxed minimizer for the unit-interval positive-set objective. -/
structure RelaxedMinimizer where
  μ : ProbabilityMeasure UnitInterval1038
  minimizes : ∀ ν : ProbabilityMeasure UnitInterval1038,
    unitIntervalPositiveSetObjective μ ≤ unitIntervalPositiveSetObjective ν

/-- The value attained by a relaxed minimizer. -/
def RelaxedMinimizer.value (M : RelaxedMinimizer) : ℝ≥0∞ :=
  unitIntervalPositiveSetObjective M.μ

/-- Construct a relaxed minimizer from compact off-diagonal tail-mass stability. -/
theorem exists_relaxed_minimizer
    (H : LowerSemicontinuity.CompactTailMassStability) :
    Nonempty RelaxedMinimizer := by
  rcases LowerSemicontinuity.exists_minimizer H with ⟨μ, hμ⟩
  exact ⟨⟨μ, hμ⟩⟩

/-- Extract the usual minimizer inequality from the packaged object. -/
theorem RelaxedMinimizer.objective_le
    (M : RelaxedMinimizer) (ν : ProbabilityMeasure UnitInterval1038) :
    unitIntervalPositiveSetObjective M.μ ≤ unitIntervalPositiveSetObjective ν :=
  M.minimizes ν

/-- Any two relaxed minimizers have the same objective value. -/
theorem RelaxedMinimizer.value_eq
    (M N : RelaxedMinimizer) : M.value = N.value := by
  apply le_antisymm
  · exact M.minimizes N.μ
  · exact N.minimizes M.μ

end
end MinimizerExistence
end StandardReduction
end Erdos1038
