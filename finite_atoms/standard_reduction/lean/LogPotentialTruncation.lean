import finite_atoms.common.lean.StandardReduction

/-!
# Truncated logarithmic potentials for the standard reduction

This module is the first reusable layer of the standard-reduction
formalization.  It does not introduce a second potential theory; it packages
existing definitions from `StandardReduction.lean` into the precise measurable
objects needed by the lower-semicontinuity and minimizer-existence steps.
-/

namespace Erdos1038
namespace StandardReduction
namespace LogPotentialTruncation

noncomputable section

open Set
open MeasureTheory
open scoped ENNReal BigOperators

/-- Re-exported name for the truncated logarithmic kernel. -/
abbrev Kernel (ε x t : ℝ) : ℝ := truncatedLogKernel ε x t

/-- Re-exported name for the truncated unit-interval potential. -/
abbrev Potential (ε : ℝ) (μ : ProbabilityMeasure UnitInterval1038) (x : ℝ) : ℝ :=
  unitIntervalTruncatedPotential ε μ x

/-- Positive set of the truncated potential. -/
def TruncatedPositiveSet
    (ε : ℝ) (μ : ProbabilityMeasure UnitInterval1038) : Set ℝ :=
  PositiveSet (unitIntervalTruncatedPotential ε μ)

/-- Positive threshold set of the truncated potential. -/
def TruncatedThresholdSet
    (ε τ : ℝ) (μ : ProbabilityMeasure UnitInterval1038) : Set ℝ :=
  {x : ℝ | τ < unitIntervalTruncatedPotential ε μ x}

/-- Joint measurability of the truncated kernel on `ℝ × [-1,1]`. -/
theorem measurable_kernel_uncurry {ε : ℝ} (hε : 0 < ε) :
    Measurable
      (fun p : ℝ × UnitInterval1038 =>
        truncatedLogKernel ε p.1 (p.2 : ℝ)) :=
  (continuous_truncatedLogKernel_uncurry hε).measurable

/-- Measurability of the truncated potential as a function of the external point. -/
theorem measurable_potential {ε : ℝ} (hε : 0 < ε)
    (μ : ProbabilityMeasure UnitInterval1038) :
    Measurable (unitIntervalTruncatedPotential ε μ) := by
  unfold unitIntervalTruncatedPotential
  have hstrong :
      StronglyMeasurable
        (fun p : ℝ × UnitInterval1038 =>
          truncatedLogKernel ε p.1 (p.2 : ℝ)) :=
    (measurable_kernel_uncurry hε).stronglyMeasurable
  exact (hstrong.integral_prod_right'
    (ν := (μ : Measure UnitInterval1038))).measurable

/-- Every positive threshold set of a truncated potential is measurable. -/
theorem measurableSet_threshold {ε τ : ℝ} (hε : 0 < ε)
    (μ : ProbabilityMeasure UnitInterval1038) :
    MeasurableSet (TruncatedThresholdSet ε τ μ) := by
  unfold TruncatedThresholdSet
  exact measurableSet_lt measurable_const (measurable_potential hε μ)

/-- The positive set of a truncated potential is measurable. -/
theorem measurableSet_positive {ε : ℝ} (hε : 0 < ε)
    (μ : ProbabilityMeasure UnitInterval1038) :
    MeasurableSet (TruncatedPositiveSet ε μ) := by
  simpa [TruncatedPositiveSet, PositiveSet, TruncatedThresholdSet]
    using measurableSet_threshold (ε := ε) (τ := 0) hε μ

end
end LogPotentialTruncation
end StandardReduction
end Erdos1038
