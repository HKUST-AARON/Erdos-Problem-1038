import finite_atoms.standard_reduction.lean.LogPotentialTruncation

/-!
# Lower semicontinuity layer for the standard reduction

This module packages the already-formalized lower-semicontinuity machinery for
Erdos 1038 into a small public interface.  The remaining analytic input is made
explicit as compact off-diagonal singular-tail stability.
-/

namespace Erdos1038
namespace StandardReduction
namespace LowerSemicontinuity

noncomputable section

open Set
open MeasureTheory
open scoped ENNReal BigOperators

/-- The length objective for the relaxed unit-interval potential problem. -/
abbrev Objective : ProbabilityMeasure UnitInterval1038 → ℝ≥0∞ :=
  unitIntervalPositiveSetObjective

/--
The remaining compact-tail stability estimate needed by the existing
lower-semicontinuity proof.

For every base measure, level, positive external error budget, positive
truncation scale, and compact subset of the fixed off-diagonal core, nearby
probability measures have uniformly small singular tail mass on that compact
set.
-/
structure CompactTailMassStability : Prop where
  stable : ∀ μ : ProbabilityMeasure UnitInterval1038,
    ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
      ∀ truncε : ℝ, 0 < truncε →
        ∀ K : Set ℝ,
          K ⊆ unitIntervalThresholdTailCoreOffDiagonal μ n truncε
            ((1 / ((n : ℝ) + 1)) / 3) (diagonalAtomSet μ) →
          IsCompact K →
          ∀ᶠ ν in nhds μ, ∀ x ∈ K,
            singularTailMass truncε ν x <
              ENNReal.ofReal ((1 / ((n : ℝ) + 1)) / 3)

/--
Lower semicontinuity of the true positive-set length objective from compact
off-diagonal tail-mass stability.
-/
theorem objective_lowerSemicontinuous
    (H : CompactTailMassStability) :
    LowerSemicontinuous Objective := by
  exact unitIntervalPositiveSetObjective_lowerSemicontinuous_of_tailMass_stability
    H.stable

/--
Existence of a relaxed minimizer for the true positive-set length objective
from compact off-diagonal tail-mass stability.
-/
theorem exists_minimizer
    (H : CompactTailMassStability) :
    ∃ μ : ProbabilityMeasure UnitInterval1038,
      ∀ ν : ProbabilityMeasure UnitInterval1038,
        Objective μ ≤ Objective ν := by
  exact unitIntervalPositiveSetObjective_exists_minimizer_of_tailMass_stability
    H.stable

/-- The predicate that a measure minimizes the relaxed objective. -/
def IsObjectiveMinimizer (μ : ProbabilityMeasure UnitInterval1038) : Prop :=
  ∀ ν : ProbabilityMeasure UnitInterval1038, Objective μ ≤ Objective ν

/-- Predicate-form minimizer existence. -/
theorem exists_objective_minimizer
    (H : CompactTailMassStability) :
    ∃ μ : ProbabilityMeasure UnitInterval1038, IsObjectiveMinimizer μ := by
  simpa [IsObjectiveMinimizer] using exists_minimizer H

end
end LowerSemicontinuity
end StandardReduction
end Erdos1038
