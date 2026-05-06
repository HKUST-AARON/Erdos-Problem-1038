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

/--
Concrete component-package form of the endpoint input.

This is narrower than `EndpointFromVariation`: instead of directly supplying
endpoint-normalized data, it supplies Tao's component/remainder package for
each relaxed minimizer.  The conversion to endpoint data is then performed by
the already-formal component and remainder packagers in `StandardReduction`.
-/
structure ComponentPackageFromVariation where
  componentPackage : ∀ M : MinimizerExistence.RelaxedMinimizer,
    TaoVariationComponentPackage (RelaxedPotential M)

/-- Concrete component-package variation data supplies endpoint data. -/
def ComponentPackageFromVariation.toEndpointFromVariation
    (H : ComponentPackageFromVariation) : EndpointFromVariation where
  endpointData := fun M =>
    (H.componentPackage M).toTaoEndpointNormalizationData

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

/-- Component-package variation data immediately gives the endpoint interface. -/
def normalizedEndpointPotential_from_componentPackage
    (H : ComponentPackageFromVariation)
    (M : MinimizerExistence.RelaxedMinimizer) :
    NormalizedEndpointPotential (RelaxedPotential M) :=
  normalizedEndpointPotential H.toEndpointFromVariation M

/-- Component-package variation data gives the baseline positive-set length lower bound. -/
theorem baseline_length_from_componentPackage
    (H : ComponentPackageFromVariation)
    (M : MinimizerExistence.RelaxedMinimizer) :
    ENNReal.ofReal (Real.sqrt 2) ≤
      volume (PositiveSet (RelaxedPotential M)) :=
  baseline_length H.toEndpointFromVariation M

/-- Component-package variation data gives the baseline interval inclusion. -/
theorem baseline_subset_positive_from_componentPackage
    (H : ComponentPackageFromVariation)
    (M : MinimizerExistence.RelaxedMinimizer) :
    BaselinePunctured ⊆ PositiveSet (RelaxedPotential M) :=
  baseline_subset_positive H.toEndpointFromVariation M

/--
Preferred diagonal-safe constructor using concrete Tao component packages
rather than a generic endpoint-data provider.
-/
theorem exists_relaxed_minimizer_with_component_package_of_oneSidedCompactCore
    (Hcore : LowerSemicontinuity.OneSidedCompactCore)
    (Hvar : ComponentPackageFromVariation) :
    Nonempty (Σ M : MinimizerExistence.RelaxedMinimizer,
      TaoVariationComponentPackage (RelaxedPotential M)) := by
  rcases MinimizerExistence.exists_relaxed_minimizer_of_oneSidedCompactCore
      Hcore with ⟨M⟩
  exact ⟨⟨M, Hvar.componentPackage M⟩⟩

/--
Baseline-length existence form using the preferred diagonal-safe core and
concrete component/remainder packages.
-/
theorem exists_baseline_length_from_componentPackage_of_oneSidedCompactCore
    (Hcore : LowerSemicontinuity.OneSidedCompactCore)
    (Hvar : ComponentPackageFromVariation) :
    ∃ M : MinimizerExistence.RelaxedMinimizer,
      ENNReal.ofReal (Real.sqrt 2) ≤
        volume (PositiveSet (RelaxedPotential M)) := by
  rcases MinimizerExistence.exists_relaxed_minimizer_of_oneSidedCompactCore
      Hcore with ⟨M⟩
  exact ⟨M, baseline_length_from_componentPackage Hvar M⟩

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

/--
Preferred diagonal-safe variant: construct a relaxed minimizer from the
one-sided compact-core input, then attach endpoint data.
-/
theorem exists_relaxed_minimizer_with_endpoint_data_of_oneSidedCompactCore
    (Hcore : LowerSemicontinuity.OneSidedCompactCore)
    (Hvar : EndpointFromVariation) :
    Nonempty (Σ M : MinimizerExistence.RelaxedMinimizer,
      TaoEndpointNormalizationData (RelaxedPotential M)) := by
  rcases MinimizerExistence.exists_relaxed_minimizer_of_oneSidedCompactCore
      Hcore with ⟨M⟩
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

/-- Baseline-length existence form using the preferred diagonal-safe core. -/
theorem exists_baseline_length_of_oneSidedCompactCore
    (Hcore : LowerSemicontinuity.OneSidedCompactCore)
    (Hvar : EndpointFromVariation) :
    ∃ M : MinimizerExistence.RelaxedMinimizer,
      ENNReal.ofReal (Real.sqrt 2) ≤
        volume (PositiveSet (RelaxedPotential M)) := by
  rcases exists_relaxed_minimizer_with_endpoint_data_of_oneSidedCompactCore
      Hcore Hvar with ⟨⟨M, D⟩⟩
  exact ⟨M, D.baseline_length_le_positiveSet⟩

end
end VariationEndpoint
end StandardReduction
end Erdos1038
