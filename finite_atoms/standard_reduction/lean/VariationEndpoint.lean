import finite_atoms.standard_reduction.lean.MinimizerExistence

/-!
# Variation-to-endpoint interface for the standard reduction

This module isolates the hard endpoint-normalization input.  Earlier layers
construct a relaxed minimizer.  This layer states the exact endpoint data that
must be available for the potential presented to the finite-atom route, and
proves the immediate normalized endpoint consequence once that data is
available.
-/

namespace Erdos1038
namespace StandardReduction
namespace VariationEndpoint

noncomputable section

open Set
open MeasureTheory
open scoped ENNReal BigOperators

/-- The actual potential attached to a packaged relaxed minimizer. -/
abbrev RelaxedPotential
    (M : MinimizerExistence.RelaxedMinimizer) : ℝ → ℝ :=
  unitIntervalLogPotential M.μ

/--
The hard endpoint input for this layer: endpoint-normalized data is available
for the relaxed minimizer potential as it is presented here.

This structure does not formalize the reflection/translation operation or its
objective invariance.  If the upstream Tao variation proof normalizes by
reflection or translation, that work must be completed before supplying this
field.
-/
structure EndpointFromVariation where
  endpointData : ∀ M : MinimizerExistence.RelaxedMinimizer,
    TaoEndpointNormalizationData (RelaxedPotential M)

/-- Endpoint data immediately gives the normalized endpoint-potential interface. -/
def normalizedEndpointPotential
    (H : EndpointFromVariation)
    (M : MinimizerExistence.RelaxedMinimizer) :
    NormalizedEndpointPotential (RelaxedPotential M) :=
  (H.endpointData M).toNormalizedEndpointPotential

/-- Endpoint data immediately gives the baseline positive-set length lower bound. -/
theorem baseline_length
    (H : EndpointFromVariation)
    (M : MinimizerExistence.RelaxedMinimizer) :
    ENNReal.ofReal (Real.sqrt 2) ≤
      volume (PositiveSet (RelaxedPotential M)) :=
  (H.endpointData M).baseline_length_le_positiveSet

/-- Endpoint data gives the baseline interval inclusion. -/
theorem baseline_subset_positive
    (H : EndpointFromVariation)
    (M : MinimizerExistence.RelaxedMinimizer) :
    BaselinePunctured ⊆ PositiveSet (RelaxedPotential M) :=
  (H.endpointData M).baseline_subset_positive

/--
Combined minimizer plus endpoint package from the two preceding layers:
compact tail-mass stability supplies a relaxed minimizer, and the endpoint
input supplies data for its presented potential.
-/
theorem exists_relaxed_minimizer_with_endpoint_data
    (Hstab : LowerSemicontinuity.CompactTailMassStability)
    (Hvar : EndpointFromVariation) :
    Nonempty (Σ M : MinimizerExistence.RelaxedMinimizer,
      TaoEndpointNormalizationData (RelaxedPotential M)) := by
  rcases MinimizerExistence.exists_relaxed_minimizer Hstab with ⟨M⟩
  exact ⟨⟨M, Hvar.endpointData M⟩⟩

/-- Baseline-length existence form after the variation endpoint input. -/
theorem exists_baseline_length
    (Hstab : LowerSemicontinuity.CompactTailMassStability)
    (Hvar : EndpointFromVariation) :
    ∃ M : MinimizerExistence.RelaxedMinimizer,
      ENNReal.ofReal (Real.sqrt 2) ≤
        volume (PositiveSet (RelaxedPotential M)) := by
  rcases exists_relaxed_minimizer_with_endpoint_data Hstab Hvar with ⟨⟨M, D⟩⟩
  exact ⟨M, D.baseline_length_le_positiveSet⟩

end
end VariationEndpoint
end StandardReduction
end Erdos1038
