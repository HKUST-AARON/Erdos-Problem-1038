import finite_atoms.standard_reduction.lean.VariationEndpoint

/-!
# Component atomization layer

This module packages the barycenter-replacement part of the standard reduction.
It exposes the two reusable conclusions needed by the later endpoint-normalizing
variation proof:

* under the already-formalized Jensen/support-hit hypotheses, replacing a
  positive component by its barycenter atom does not increase the positive-set
  objective;
* for a secondary-minimizing primary minimizer, such a replacement forces the
  caller-supplied tested probability block to be a Dirac mass.

The tested block is an explicit field in the rigidity data.  This module does
not prove that the tested block is the actual component block unless the caller
supplies that identification through the secondary-objective equality field.
-/

namespace Erdos1038
namespace StandardReduction
namespace ComponentAtomization

noncomputable section

open Set
open MeasureTheory
open scoped ENNReal BigOperators

/--
A component whose barycenter replacement is known not to increase objective by
countability of the singular strict-outside support-hit branch.
-/
structure CountableSupportHitReplacement
    (μ : ProbabilityMeasure UnitInterval1038) where
  component : PositiveComponent μ
  componentMass_pos : 0 < componentMass component
  supportHit_countable : (strictOutsideSupportHitSet component).Countable

/-- Objective non-increase for countable-support-hit component replacement. -/
theorem CountableSupportHitReplacement.objective_le
    {μ : ProbabilityMeasure UnitInterval1038}
    (D : CountableSupportHitReplacement μ) :
    volume (PositiveSet (componentReplacementPotential D.component)) ≤
      volume (PositiveSet (unitIntervalLogPotential μ)) := by
  exact componentReplacement_objective_le_of_supportHit_countable
    D.component D.componentMass_pos D.supportHit_countable

/--
A component whose singular strict-outside support-hit branch is covered by a
concrete finite set.
-/
structure FiniteSupportHitReplacement
    (μ : ProbabilityMeasure UnitInterval1038) where
  component : PositiveComponent μ
  componentMass_pos : 0 < componentMass component
  carrier : Finset ℝ
  supportHit_subset : strictOutsideSupportHitSet component ⊆ (carrier : Set ℝ)

/-- Objective non-increase for finite-support-hit component replacement. -/
theorem FiniteSupportHitReplacement.objective_le
    {μ : ProbabilityMeasure UnitInterval1038}
    (D : FiniteSupportHitReplacement μ) :
    volume (PositiveSet (componentReplacementPotential D.component)) ≤
      volume (PositiveSet (unitIntervalLogPotential μ)) := by
  exact componentReplacement_objective_le_of_supportHit_subset_finset
    D.component D.componentMass_pos D.carrier D.supportHit_subset

/--
Data needed to apply the ENNReal secondary-minimizer rigidity theorem to one
component replacement.
-/
structure SecondaryReplacementRigidityData
    {α : Type*} [TopologicalSpace α]
    (P : SecondarySelectorProblemENNReal α)
    (a b : α)
    (μ : ProbabilityMeasure UnitInterval1038) where
  component : PositiveComponent μ
  secondary_minimizer : IsSecondaryMinimizingPrimaryMinimizerENNReal P a
  replacement_admissible : P.Primary.Admissible b
  objective_original :
    P.Primary.objective a = volume (PositiveSet (unitIntervalLogPotential μ))
  objective_replacement :
    P.Primary.objective b = volume (PositiveSet (componentReplacementPotential component))
  strictOutside_potential_le : ∀ x : ℝ, StrictOutsideComponent component x →
    componentReplacementPotential component x ≤ unitIntervalLogPotential μ x
  secondary_le : P.secondaryObjective b ≤ P.secondaryObjective a
  block : Measure ℝ
  block_probability : IsProbabilityMeasure block
  block_first_integrable : Integrable (fun t : ℝ => t) block
  block_second_integrable : Integrable (fun t : ℝ => t ^ 2) block
  secondary_eq_to_second_moment_eq :
    P.secondaryObjective b = P.secondaryObjective a →
      (∫ t : ℝ, t ^ 2 ∂block) = (∫ t : ℝ, t ∂block) ^ 2

/-- The tested component block is forced to be a Dirac mass. -/
theorem SecondaryReplacementRigidityData.block_eq_dirac
    {α : Type*} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {a b : α} {μ : ProbabilityMeasure UnitInterval1038}
    (D : SecondaryReplacementRigidityData P a b μ) :
    D.block = Measure.dirac (∫ t : ℝ, t ∂D.block) := by
  letI : IsProbabilityMeasure D.block := D.block_probability
  exact secondary_minimizer_componentReplacement_forces_block_dirac_ennreal_strictOutside
    D.secondary_minimizer D.replacement_admissible D.component
    D.objective_original D.objective_replacement D.strictOutside_potential_le
    D.secondary_le D.block D.block_first_integrable D.block_second_integrable
    D.secondary_eq_to_second_moment_eq

/--
Specialized rigidity data when objective non-increase is supplied by a
countable singular support-hit certificate.  This structure records the
countable certificate and derives the `strictOutside_potential_le` input through
existing StandardReduction machinery.
-/
structure CountableSupportHitRigidityData
    {α : Type*} [TopologicalSpace α]
    (P : SecondarySelectorProblemENNReal α)
    (a b : α)
    (μ : ProbabilityMeasure UnitInterval1038) where
  replacement : CountableSupportHitReplacement μ
  secondary_minimizer : IsSecondaryMinimizingPrimaryMinimizerENNReal P a
  replacement_admissible : P.Primary.Admissible b
  objective_original :
    P.Primary.objective a = volume (PositiveSet (unitIntervalLogPotential μ))
  objective_replacement :
    P.Primary.objective b = volume (PositiveSet (componentReplacementPotential replacement.component))
  secondary_le : P.secondaryObjective b ≤ P.secondaryObjective a
  block : Measure ℝ
  block_probability : IsProbabilityMeasure block
  block_first_integrable : Integrable (fun t : ℝ => t) block
  block_second_integrable : Integrable (fun t : ℝ => t ^ 2) block
  secondary_eq_to_second_moment_eq :
    P.secondaryObjective b = P.secondaryObjective a →
      (∫ t : ℝ, t ^ 2 ∂block) = (∫ t : ℝ, t ∂block) ^ 2

/-- Countable-support-hit replacement gives the primary objective comparison. -/
theorem CountableSupportHitRigidityData.primary_objective_le
    {α : Type*} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {a b : α} {μ : ProbabilityMeasure UnitInterval1038}
    (D : CountableSupportHitRigidityData P a b μ) :
    P.Primary.objective b ≤ P.Primary.objective a := by
  rw [D.objective_original, D.objective_replacement]
  exact D.replacement.objective_le

/-- Countable-support-hit replacement forces the tested block to be Dirac. -/
theorem CountableSupportHitRigidityData.block_eq_dirac
    {α : Type*} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {a b : α} {μ : ProbabilityMeasure UnitInterval1038}
    (D : CountableSupportHitRigidityData P a b μ) :
    D.block = Measure.dirac (∫ t : ℝ, t ∂D.block) := by
  letI : IsProbabilityMeasure D.block := D.block_probability
  exact secondary_minimizer_replacement_forces_block_dirac_ennreal
    D.secondary_minimizer D.replacement_admissible
    D.primary_objective_le D.secondary_le D.block
    D.block_first_integrable D.block_second_integrable
    D.secondary_eq_to_second_moment_eq

/--
Specialized rigidity data when objective non-increase is supplied by a finite
carrier for the singular support-hit branch.
-/
structure FiniteSupportHitRigidityData
    {α : Type*} [TopologicalSpace α]
    (P : SecondarySelectorProblemENNReal α)
    (a b : α)
    (μ : ProbabilityMeasure UnitInterval1038) where
  replacement : FiniteSupportHitReplacement μ
  secondary_minimizer : IsSecondaryMinimizingPrimaryMinimizerENNReal P a
  replacement_admissible : P.Primary.Admissible b
  objective_original :
    P.Primary.objective a = volume (PositiveSet (unitIntervalLogPotential μ))
  objective_replacement :
    P.Primary.objective b =
      volume (PositiveSet (componentReplacementPotential replacement.component))
  secondary_le : P.secondaryObjective b ≤ P.secondaryObjective a
  block : Measure ℝ
  block_probability : IsProbabilityMeasure block
  block_first_integrable : Integrable (fun t : ℝ => t) block
  block_second_integrable : Integrable (fun t : ℝ => t ^ 2) block
  secondary_eq_to_second_moment_eq :
    P.secondaryObjective b = P.secondaryObjective a →
      (∫ t : ℝ, t ^ 2 ∂block) = (∫ t : ℝ, t ∂block) ^ 2

/-- Finite-support-hit replacement gives the primary objective comparison. -/
theorem FiniteSupportHitRigidityData.primary_objective_le
    {α : Type*} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {a b : α} {μ : ProbabilityMeasure UnitInterval1038}
    (D : FiniteSupportHitRigidityData P a b μ) :
    P.Primary.objective b ≤ P.Primary.objective a := by
  rw [D.objective_original, D.objective_replacement]
  exact D.replacement.objective_le

/-- Finite-support-hit replacement forces the tested block to be Dirac. -/
theorem FiniteSupportHitRigidityData.block_eq_dirac
    {α : Type*} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {a b : α} {μ : ProbabilityMeasure UnitInterval1038}
    (D : FiniteSupportHitRigidityData P a b μ) :
    D.block = Measure.dirac (∫ t : ℝ, t ∂D.block) := by
  letI : IsProbabilityMeasure D.block := D.block_probability
  exact secondary_minimizer_replacement_forces_block_dirac_ennreal
    D.secondary_minimizer D.replacement_admissible
    D.primary_objective_le D.secondary_le D.block
    D.block_first_integrable D.block_second_integrable
    D.secondary_eq_to_second_moment_eq

end
end ComponentAtomization
end StandardReduction
end Erdos1038
