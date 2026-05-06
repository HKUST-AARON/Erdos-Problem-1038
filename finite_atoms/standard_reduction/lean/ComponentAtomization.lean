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
The normalized component block has an integrable second moment.  This is the
missing local bridge needed to use the canonical normalized component block as
the tested probability block in the variance-rigidity theorem.
-/
lemma normalized_componentBlock_second_moment_integrable
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    (hmass_pos : 0 < componentMass C) :
    Integrable (fun t : ℝ => t ^ 2)
      ((componentBlockFiniteMeasure C).normalize : Measure ℝ) := by
  refine ⟨(continuous_id.pow 2).aestronglyMeasurable, ?_⟩
  refine HasFiniteIntegral.of_bounded
    (C := (max |C.left| |C.right|) ^ 2) ?_
  filter_upwards [normalized_componentBlock_ae_mem_interval C hmass_pos] with t ht
  rw [PositiveComponent.interval_eq, Set.mem_Ioo] at ht
  have hleft_abs : |C.left| ≤ max |C.left| |C.right| := le_max_left _ _
  have hright_abs : |C.right| ≤ max |C.left| |C.right| := le_max_right _ _
  have ht_abs : |t| ≤ max |C.left| |C.right| := by
    by_cases ht_nonneg : 0 ≤ t
    · rw [abs_of_nonneg ht_nonneg]
      have ht_le_right : t ≤ C.right := le_of_lt ht.2
      have hright_le_abs : C.right ≤ |C.right| := le_abs_self C.right
      exact le_trans ht_le_right (le_trans hright_le_abs hright_abs)
    · have ht_nonpos : t ≤ 0 := le_of_not_ge ht_nonneg
      rw [abs_of_nonpos ht_nonpos]
      have hleft_le_t : C.left ≤ t := le_of_lt ht.1
      have hneg_t_le : -t ≤ -C.left := neg_le_neg hleft_le_t
      have hneg_left_le_abs : -C.left ≤ |C.left| := neg_le_abs C.left
      exact le_trans hneg_t_le (le_trans hneg_left_le_abs hleft_abs)
  have hmax_nonneg : 0 ≤ max |C.left| |C.right| :=
    le_trans (abs_nonneg C.left) hleft_abs
  have hsq : t ^ 2 ≤ (max |C.left| |C.right|) ^ 2 :=
    sq_le_sq.mpr (by simpa [abs_of_nonneg hmax_nonneg] using ht_abs)
  calc
    ‖t ^ 2‖ = |t ^ 2| := rfl
    _ = t ^ 2 := abs_of_nonneg (sq_nonneg t)
    _ ≤ (max |C.left| |C.right|) ^ 2 := hsq

/--
If the canonical normalized component block is Dirac at its first moment, then
the actual component block is the component mass times the barycenter Dirac.

This is the measure-level form of the atomization conclusion used later in the
normalization step.
-/
theorem componentBlock_eq_componentMass_smul_dirac_of_normalized_block_eq_dirac
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    (hmass_pos : 0 < componentMass C)
    (hdirac :
      ((componentBlockFiniteMeasure C).normalize : Measure ℝ) =
        Measure.dirac
          (∫ t : ℝ, t
            ∂((componentBlockFiniteMeasure C).normalize : Measure ℝ))) :
    componentBlock C = componentMass C • Measure.dirac (componentBarycenter C) := by
  have hbary :
      componentBarycenter C =
        ∫ t : ℝ, t
          ∂((componentBlockFiniteMeasure C).normalize : Measure ℝ) :=
    componentBarycenter_eq_normalized_componentBlock_integral C hmass_pos
  calc
    componentBlock C = (componentBlockFiniteMeasure C : Measure ℝ) := rfl
    _ = ((componentBlockFiniteMeasure C).mass : ℝ≥0∞) •
          ((componentBlockFiniteMeasure C).normalize : Measure ℝ) := by
          conv_lhs =>
            rw [(componentBlockFiniteMeasure C).self_eq_mass_smul_normalize]
          rfl
    _ = ((componentBlockFiniteMeasure C).mass : ℝ≥0∞) •
          Measure.dirac
            (∫ t : ℝ, t
              ∂((componentBlockFiniteMeasure C).normalize : Measure ℝ)) := by
          exact congrArg
            (fun ν : Measure ℝ =>
              ((componentBlockFiniteMeasure C).mass : ℝ≥0∞) • ν) hdirac
    _ = ((componentBlockFiniteMeasure C).mass : ℝ≥0∞) •
          Measure.dirac (componentBarycenter C) := by
          rw [← hbary]
    _ = componentMass C • Measure.dirac (componentBarycenter C) := by
          rw [componentBlockFiniteMeasure_mass C,
            ENNReal.coe_toNNReal (componentMass_ne_top C)]

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

/--
Rigidity data specialized to the canonical normalized component block, with a
countable support-hit certificate for objective non-increase.

The remaining caller-supplied bridge is the secondary-objective identity:
if the abstract secondary values are equal, then equality of the second moment
holds for this normalized component block.
-/
structure CountableSupportHitNormalizedBlockRigidityData
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
    P.Primary.objective b =
      volume (PositiveSet (componentReplacementPotential replacement.component))
  secondary_le : P.secondaryObjective b ≤ P.secondaryObjective a
  secondary_eq_to_second_moment_eq :
    P.secondaryObjective b = P.secondaryObjective a →
      (∫ t : ℝ, t ^ 2
          ∂((componentBlockFiniteMeasure replacement.component).normalize : Measure ℝ)) =
        (∫ t : ℝ, t
          ∂((componentBlockFiniteMeasure replacement.component).normalize : Measure ℝ)) ^ 2

/-- Countable-support-hit normalized component block is forced to be Dirac. -/
theorem CountableSupportHitNormalizedBlockRigidityData.normalized_block_eq_dirac
    {α : Type*} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {a b : α} {μ : ProbabilityMeasure UnitInterval1038}
    (D : CountableSupportHitNormalizedBlockRigidityData P a b μ) :
    ((componentBlockFiniteMeasure D.replacement.component).normalize : Measure ℝ) =
      Measure.dirac
        (∫ t : ℝ, t
          ∂((componentBlockFiniteMeasure D.replacement.component).normalize : Measure ℝ)) := by
  let block : Measure ℝ :=
    ((componentBlockFiniteMeasure D.replacement.component).normalize : Measure ℝ)
  have hblock_probability : IsProbabilityMeasure block := by
    dsimp [block]
    exact (componentBlockFiniteMeasure D.replacement.component).normalize.property
  have hprimary : P.Primary.objective b ≤ P.Primary.objective a := by
    rw [D.objective_original, D.objective_replacement]
    exact D.replacement.objective_le
  letI : IsProbabilityMeasure block := hblock_probability
  have hdirac :
      block = Measure.dirac (∫ t : ℝ, t ∂block) := by
    exact secondary_minimizer_replacement_forces_block_dirac_ennreal
      D.secondary_minimizer D.replacement_admissible
      hprimary D.secondary_le block
      (normalized_componentBlock_first_moment_integrable
        D.replacement.component D.replacement.componentMass_pos)
      (normalized_componentBlock_second_moment_integrable
        D.replacement.component D.replacement.componentMass_pos)
      (by
        intro h
        exact D.secondary_eq_to_second_moment_eq h)
  simpa [block] using hdirac

/--
Finite-carrier variant of normalized component-block rigidity.
-/
structure FiniteSupportHitNormalizedBlockRigidityData
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
  secondary_eq_to_second_moment_eq :
    P.secondaryObjective b = P.secondaryObjective a →
      (∫ t : ℝ, t ^ 2
          ∂((componentBlockFiniteMeasure replacement.component).normalize : Measure ℝ)) =
        (∫ t : ℝ, t
          ∂((componentBlockFiniteMeasure replacement.component).normalize : Measure ℝ)) ^ 2

/-- Finite-support-hit normalized component block is forced to be Dirac. -/
theorem FiniteSupportHitNormalizedBlockRigidityData.normalized_block_eq_dirac
    {α : Type*} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {a b : α} {μ : ProbabilityMeasure UnitInterval1038}
    (D : FiniteSupportHitNormalizedBlockRigidityData P a b μ) :
    ((componentBlockFiniteMeasure D.replacement.component).normalize : Measure ℝ) =
      Measure.dirac
        (∫ t : ℝ, t
          ∂((componentBlockFiniteMeasure D.replacement.component).normalize : Measure ℝ)) := by
  let block : Measure ℝ :=
    ((componentBlockFiniteMeasure D.replacement.component).normalize : Measure ℝ)
  have hblock_probability : IsProbabilityMeasure block := by
    dsimp [block]
    exact (componentBlockFiniteMeasure D.replacement.component).normalize.property
  have hprimary : P.Primary.objective b ≤ P.Primary.objective a := by
    rw [D.objective_original, D.objective_replacement]
    exact D.replacement.objective_le
  letI : IsProbabilityMeasure block := hblock_probability
  have hdirac :
      block = Measure.dirac (∫ t : ℝ, t ∂block) := by
    exact secondary_minimizer_replacement_forces_block_dirac_ennreal
      D.secondary_minimizer D.replacement_admissible
      hprimary D.secondary_le block
      (normalized_componentBlock_first_moment_integrable
        D.replacement.component D.replacement.componentMass_pos)
      (normalized_componentBlock_second_moment_integrable
        D.replacement.component D.replacement.componentMass_pos)
      (by
        intro h
        exact D.secondary_eq_to_second_moment_eq h)
  simpa [block] using hdirac

end
end ComponentAtomization
end StandardReduction
end Erdos1038
