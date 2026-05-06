import finite_atoms.standard_reduction.lean.LogPotentialTruncation

/-!
# Truncated-sup objective layer

This module packages the countable truncated-potential surrogate objective.  It
is useful because its lower-semicontinuity avoids the logarithmic singularity
issues of the real-valued untruncated potential; the remaining input is only the
compact-threshold-core regularity statement already used by
`StandardReduction.lean`.
-/

namespace Erdos1038
namespace StandardReduction
namespace TruncatedObjective

noncomputable section

open Set
open MeasureTheory
open scoped ENNReal BigOperators

/-- The countable truncated-sup positive set. -/
abbrev PositiveSetTruncatedSup (μ : ProbabilityMeasure UnitInterval1038) : Set ℝ :=
  unitIntervalTruncatedPositiveSet μ

/-- The countable truncated-sup length objective. -/
abbrev Objective (μ : ProbabilityMeasure UnitInterval1038) : ℝ≥0∞ :=
  unitIntervalTruncatedPositiveSetObjective μ

/-- Compact threshold-core input for the truncated-sup objective. -/
structure CompactThresholdCore : Prop where
  core : ∀ μ : ProbabilityMeasure UnitInterval1038,
    ∀ η : NNReal, 0 < η →
      ∃ truncN thresholdN : ℕ, ∃ K : Set ℝ,
        volume (unitIntervalTruncatedPositiveSet μ) ≤
          volume K + (η : ℝ≥0∞) ∧
        K ⊆ {x : ℝ |
          unitIntervalPositiveTruncationScale thresholdN <
            unitIntervalTruncatedPotential
              (unitIntervalPositiveTruncationScale truncN) μ x} ∧
        IsCompact K

/-- Measurability of the truncated-sup positive set. -/
theorem measurableSet_positiveSet
    (μ : ProbabilityMeasure UnitInterval1038) :
    MeasurableSet (PositiveSetTruncatedSup μ) := by
  exact unitIntervalTruncatedPositiveSet_measurableSet_of_measurable μ
    (fun n =>
      LogPotentialTruncation.measurable_potential
        (unitIntervalPositiveTruncationScale_pos n) μ)

/-- Lower semicontinuity of the truncated-sup objective from compact threshold cores. -/
theorem objective_lowerSemicontinuous
    (H : CompactThresholdCore) :
    LowerSemicontinuous Objective := by
  exact unitIntervalTruncatedPositiveSetObjective_lowerSemicontinuous_of_compact_threshold_core
    H.core

/-- Existence of a minimizer for the truncated-sup objective. -/
theorem exists_minimizer
    (H : CompactThresholdCore) :
    ∃ μ : ProbabilityMeasure UnitInterval1038,
      ∀ ν : ProbabilityMeasure UnitInterval1038,
        Objective μ ≤ Objective ν := by
  exact unitIntervalTruncatedPositiveSetObjective_exists_minimizer_of_compact_threshold_core
    H.core

/-- A packaged minimizer for the truncated-sup objective. -/
structure TruncatedMinimizer where
  μ : ProbabilityMeasure UnitInterval1038
  minimizes : ∀ ν : ProbabilityMeasure UnitInterval1038,
    Objective μ ≤ Objective ν

/-- Construct a packaged minimizer for the truncated-sup objective. -/
theorem exists_truncated_minimizer
    (H : CompactThresholdCore) :
    Nonempty TruncatedMinimizer := by
  rcases exists_minimizer H with ⟨μ, hμ⟩
  exact ⟨⟨μ, hμ⟩⟩

/-- Any two truncated-sup minimizers have the same objective value. -/
theorem TruncatedMinimizer.value_eq
    (M N : TruncatedMinimizer) : Objective M.μ = Objective N.μ := by
  apply le_antisymm
  · exact M.minimizes N.μ
  · exact N.minimizes M.μ

end
end TruncatedObjective
end StandardReduction
end Erdos1038
