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
open scoped ENNReal BigOperators Topology

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

/-- The support of a scaled Dirac measure is contained in its atom. -/
lemma support_smul_dirac_subset_singleton (c : ℝ≥0∞) (a : ℝ) :
    (c • Measure.dirac a : Measure ℝ).support ⊆ ({a} : Set ℝ) := by
  intro t ht
  by_contra hta
  have hU_mem : ({a}ᶜ : Set ℝ) ∈ 𝓝 t := by
    exact IsOpen.mem_nhds isClosed_singleton.isOpen_compl hta
  have hzero : (c • Measure.dirac a : Measure ℝ) ({a}ᶜ : Set ℝ) = 0 := by
    simp
  have hpos : 0 < (c • Measure.dirac a : Measure ℝ) ({a}ᶜ : Set ℝ) := by
    rw [Measure.mem_support_iff_forall] at ht
    exact ht ({a}ᶜ : Set ℝ) hU_mem
  simp [hzero] at hpos

/--
If the selected support is contained in the topological support of the actual
measure, then component-block atomization forces every selected support point
inside the positive component to be the barycenter.
-/
theorem unique_support_in_component_of_componentBlock_eq_dirac
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    {Support : Set ℝ}
    (hSupport_subset : Support ⊆ (realMeasure μ).support)
    (hblock :
      componentBlock C =
        componentMass C • Measure.dirac (componentBarycenter C)) :
    ∀ t : ℝ, t ∈ Support → t ∈ C.interval →
      t = componentBarycenter C := by
  intro t htSupport htComp
  have htInterior : t ∈ interior C.interval := by
    simpa [PositiveComponent.interval_eq] using htComp
  have htBlock : t ∈ (componentBlock C).support := by
    exact Measure.interior_inter_support
      (μ := realMeasure μ) (s := C.interval)
      ⟨htInterior, hSupport_subset htSupport⟩
  have htDirac :
      t ∈ (componentMass C • Measure.dirac (componentBarycenter C) :
        Measure ℝ).support := by
    simpa [hblock] using htBlock
  have htSingleton :
      t ∈ ({componentBarycenter C} : Set ℝ) :=
    support_smul_dirac_subset_singleton
      (componentMass C) (componentBarycenter C) htDirac
  simpa using htSingleton

/--
Endpoint-specialized support uniqueness: if the barycenter has been normalized
to `-1`, atomization gives the exact `unique_support_in_component` field used
by `TaoVariationComponentPackage`.
-/
theorem unique_support_in_component_endpoint_of_componentBlock_eq_dirac
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    {Support : Set ℝ}
    (hSupport_subset : Support ⊆ (realMeasure μ).support)
    (hblock :
      componentBlock C =
        componentMass C • Measure.dirac (componentBarycenter C))
    (hbary : componentBarycenter C = -1) :
    ∀ t : ℝ, t ∈ Support → t ∈ C.interval → t = -1 := by
  intro t htSupport htComp
  rw [← hbary]
  exact unique_support_in_component_of_componentBlock_eq_dirac
    C hSupport_subset hblock t htSupport htComp

/-! ### Endpoint support shape and boundary average -/

/--
The full component-order information gives the sharper normalized support
shape used in Tao's endpoint-mass boundary estimate: after normalization, every
selected support point is either the endpoint atom `-1` or lies to the right of
the component's right endpoint.
-/
private lemma support_subset_endpoint_union_rightEndpoint_of_order
    {Support : Set ℝ} {xMinus xPlus : ℝ}
    (hBounded : Support ⊆ Icc (-1 : ℝ) 1)
    (hInterval : Ioo (-1 : ℝ) 0 ⊆ Ioo xMinus xPlus)
    (hUniqueInComponent :
      ∀ t : ℝ, t ∈ Support → t ∈ Ioo xMinus xPlus → t = -1) :
    Support ⊆ ({-1} : Set ℝ) ∪ Icc xPlus 1 := by
  intro t ht
  have htBound := hBounded ht
  by_cases htEndpoint : t = -1
  · exact Or.inl (by simp [htEndpoint])
  · right
    constructor
    · by_contra hnot
      have hlt : t < xPlus := lt_of_not_ge hnot
      have ht_lower : -1 < t := lt_of_le_of_ne htBound.1 (Ne.symm htEndpoint)
      by_cases htneg : t < 0
      · let y : ℝ := (t - 1) / 2
        have hybase : y ∈ Ioo (-1 : ℝ) 0 := by
          constructor <;> dsimp [y] <;> linarith [ht_lower, htneg]
        have hxMinus_lt_y : xMinus < y := (hInterval hybase).1
        have hy_lt_t : y < t := by
          dsimp [y]
          linarith [ht_lower]
        have htComp : t ∈ Ioo xMinus xPlus :=
          ⟨lt_trans hxMinus_lt_y hy_lt_t, hlt⟩
        exact htEndpoint (hUniqueInComponent t ht htComp)
      · have ht_nonneg : 0 ≤ t := le_of_not_gt htneg
        have hminus_lt_neg_half : xMinus < (-1 / 2 : ℝ) := by
          have hbase : (-1 / 2 : ℝ) ∈ Ioo (-1 : ℝ) 0 := by norm_num
          exact (hInterval hbase).1
        have htComp : t ∈ Ioo xMinus xPlus :=
          ⟨lt_of_lt_of_le hminus_lt_neg_half (by linarith [ht_nonneg]), hlt⟩
        exact htEndpoint (hUniqueInComponent t ht htComp)
    · exact htBound.2

/-! ### Canonical endpoint remainder -/

/--
The canonical endpoint remainder after normalization: remove the endpoint atom
at `-1` from the pushed-forward unit-interval measure.
-/
def endpointRemainder (μ : ProbabilityMeasure UnitInterval1038) : Measure ℝ :=
  (realMeasure μ).restrict (({-1} : Set ℝ)ᶜ)

/--
The canonical endpoint remainder is a.e. supported on any selected support set
which contains the topological support of the original pushed-forward measure.
-/
theorem endpointRemainder_ae_mem_support
    (μ : ProbabilityMeasure UnitInterval1038) {Support : Set ℝ}
    (hSupport_subset : (realMeasure μ).support ⊆ Support) :
    ∀ᵐ t : ℝ ∂endpointRemainder μ, t ∈ Support := by
  have hsupport_ae :
      ∀ᵐ t : ℝ ∂realMeasure μ, t ∈ (realMeasure μ).support :=
    Measure.support_mem_ae
  exact (ae_restrict_of_ae hsupport_ae).mono fun t ht =>
    hSupport_subset ht

/-- The canonical endpoint remainder excludes the endpoint atom a.e. -/
theorem endpointRemainder_ae_ne_endpoint
    (μ : ProbabilityMeasure UnitInterval1038) :
    ∀ᵐ t : ℝ ∂endpointRemainder μ, t ≠ -1 := by
  have hmem :
      ∀ᵐ t : ℝ ∂endpointRemainder μ, t ∈ (({-1} : Set ℝ)ᶜ) :=
    ae_restrict_mem (measurableSet_singleton (-1 : ℝ)).compl
  exact hmem.mono fun t ht hEq => ht (by simp [hEq])

/--
Mass of the canonical endpoint remainder in real-valued endpoint-mass
coordinates.
-/
theorem endpointRemainder_mass
    (μ : ProbabilityMeasure UnitInterval1038) :
    endpointRemainder μ Set.univ =
      ENNReal.ofReal (1 - ((realMeasure μ) (({-1} : Set ℝ))).toReal) := by
  have hprob :
      (realMeasure μ).real (({-1} : Set ℝ)) +
          (realMeasure μ).real (({-1} : Set ℝ)ᶜ) = 1 :=
    probReal_add_probReal_compl (μ := realMeasure μ)
      (measurableSet_singleton (-1 : ℝ))
  have hcompl_real :
      (realMeasure μ).real (({-1} : Set ℝ)ᶜ) =
        1 - ((realMeasure μ) (({-1} : Set ℝ))).toReal := by
    dsimp [Measure.real] at hprob ⊢
    linarith
  calc
    endpointRemainder μ Set.univ =
        (realMeasure μ) (({-1} : Set ℝ)ᶜ) := by
          simp [endpointRemainder]
    _ = ENNReal.ofReal ((realMeasure μ).real (({-1} : Set ℝ)ᶜ)) := by
          exact (ENNReal.ofReal_toReal
            (measure_ne_top (realMeasure μ) (({-1} : Set ℝ)ᶜ))).symm
    _ = ENNReal.ofReal
          (1 - ((realMeasure μ) (({-1} : Set ℝ))).toReal) := by
          rw [hcompl_real]

/-- The canonical endpoint mass coordinate has nonnegative complement mass. -/
theorem endpointRemainder_mass_nonneg
    (μ : ProbabilityMeasure UnitInterval1038) :
    0 ≤ 1 - ((realMeasure μ) (({-1} : Set ℝ))).toReal := by
  have hprob :
      (realMeasure μ).real (({-1} : Set ℝ)) +
          (realMeasure μ).real (({-1} : Set ℝ)ᶜ) = 1 :=
    probReal_add_probReal_compl (μ := realMeasure μ)
      (measurableSet_singleton (-1 : ℝ))
  dsimp [Measure.real] at hprob ⊢
  have hnonneg : 0 ≤ ((realMeasure μ) (({-1} : Set ℝ)ᶜ)).toReal :=
    ENNReal.toReal_nonneg
  linarith

/--
If the original pushed-forward support is contained in `{-1} ∪ [0,1]`, then
the canonical endpoint remainder is a.e. supported in `[0,1]`.
-/
theorem endpointRemainder_ae_mem_Icc_zero_one
    (μ : ProbabilityMeasure UnitInterval1038)
    (hsupport :
      (realMeasure μ).support ⊆ ({-1} : Set ℝ) ∪ Icc (0 : ℝ) 1) :
    ∀ᵐ t : ℝ ∂endpointRemainder μ, t ∈ Icc (0 : ℝ) 1 := by
  filter_upwards
    [endpointRemainder_ae_mem_support μ hsupport,
      endpointRemainder_ae_ne_endpoint μ] with t htSupport htNe
  rcases htSupport with htEndpoint | htNonnegative
  · have htEq : t = -1 := by simpa using htEndpoint
    exact False.elim (htNe htEq)
  · exact htNonnegative

/--
The canonical endpoint remainder lies to the right of the selected positive
component's right endpoint.  This is the support-order part of the boundary
average argument: after removing the endpoint atom, no remaining support point
can lie inside the component, and the normalized support is bounded by `1`.
-/
theorem endpointRemainder_ae_mem_Icc_xPlus_one_of_support_order
    (μ : ProbabilityMeasure UnitInterval1038)
    {Support : Set ℝ} {xMinus xPlus : ℝ}
    (hSupport : (realMeasure μ).support ⊆ Support)
    (hBounded : Support ⊆ Icc (-1 : ℝ) 1)
    (hInterval : Ioo (-1 : ℝ) 0 ⊆ Ioo xMinus xPlus)
    (hUnique :
      ∀ t : ℝ, t ∈ Support → t ∈ Ioo xMinus xPlus → t = -1) :
    ∀ᵐ t : ℝ ∂endpointRemainder μ, t ∈ Icc xPlus 1 := by
  have hright :
      Support ⊆ ({-1} : Set ℝ) ∪ Icc xPlus 1 :=
    support_subset_endpoint_union_rightEndpoint_of_order
      hBounded hInterval hUnique
  filter_upwards
    [endpointRemainder_ae_mem_support μ hSupport,
      endpointRemainder_ae_ne_endpoint μ] with t htSupport htNe
  have htRight := hright htSupport
  rcases htRight with htEndpoint | htIcc
  · have htEq : t = -1 := by simpa using htEndpoint
    exact False.elim (htNe htEq)
  · exact htIcc

/--
Distance-integral upper bound for the canonical endpoint remainder once its
support is known to lie in `[xPlus, 1]`.
-/
theorem endpointRemainder_distance_integral_le_boundary_remainder
    (μ : ProbabilityMeasure UnitInterval1038) {xPlus : ℝ}
    (hrem_support :
      ∀ᵐ t : ℝ ∂endpointRemainder μ, t ∈ Icc xPlus 1)
    (hdist_int :
      Integrable (fun t : ℝ => |xPlus - t|) (endpointRemainder μ)) :
    (∫ t : ℝ, |xPlus - t| ∂endpointRemainder μ) ≤
      (1 - xPlus) *
        (1 - ((realMeasure μ) (({-1} : Set ℝ))).toReal) := by
  haveI : IsFiniteMeasure (endpointRemainder μ) := by
    refine ⟨?_⟩
    rw [endpointRemainder_mass μ]
    exact ENNReal.ofReal_lt_top
  have hupper_ae :
      (fun t : ℝ => |xPlus - t|) ≤ᵐ[endpointRemainder μ]
        fun _ : ℝ => 1 - xPlus := by
    filter_upwards [hrem_support] with t ht
    have hnonpos : xPlus - t ≤ 0 := by linarith [ht.1]
    rw [abs_of_nonpos hnonpos]
    linarith [ht.2]
  have hconst_int : Integrable (fun _ : ℝ => 1 - xPlus) (endpointRemainder μ) :=
    integrable_const (1 - xPlus)
  have hle :
      (∫ t : ℝ, |xPlus - t| ∂endpointRemainder μ) ≤
        ∫ _ : ℝ, (1 - xPlus) ∂endpointRemainder μ :=
    integral_mono_ae hdist_int hconst_int hupper_ae
  have hconst :
      (∫ _ : ℝ, (1 - xPlus) ∂endpointRemainder μ) =
        (endpointRemainder μ Set.univ).toReal * (1 - xPlus) := by
    rw [integral_const]
    simp [Measure.real, smul_eq_mul]
  calc
    (∫ t : ℝ, |xPlus - t| ∂endpointRemainder μ)
        ≤ (endpointRemainder μ Set.univ).toReal * (1 - xPlus) := by
          simpa [hconst] using hle
    _ = (1 - ((realMeasure μ) (({-1} : Set ℝ))).toReal) *
          (1 - xPlus) := by
          rw [endpointRemainder_mass μ]
          simp [ENNReal.toReal_ofReal (endpointRemainder_mass_nonneg μ)]
    _ = (1 - xPlus) *
          (1 - ((realMeasure μ) (({-1} : Set ℝ))).toReal) := by
          ring

/--
Boundary-average constructor from the analytic boundary-distance input.

The analytic input is the lower bound for the endpoint atom plus canonical
remainder distance at `xPlus`.  The support input above turns the remainder
distance integral into the algebraic `(1 - xPlus) * (1 - endpointMass)` term
required by `CanonicalEndpointVariationPackageData.boundary_average` and
`TaoComponentReductionData.boundary_average`.
-/
theorem boundary_average_of_endpointRemainder_boundary_distance
    (μ : ProbabilityMeasure UnitInterval1038) {xPlus : ℝ}
    (hrem_support :
      ∀ᵐ t : ℝ ∂endpointRemainder μ, t ∈ Icc xPlus 1)
    (hdist_int :
      Integrable (fun t : ℝ => |xPlus - t|) (endpointRemainder μ))
    (hboundary_distance :
      1 ≤
        ((realMeasure μ) (({-1} : Set ℝ))).toReal * (xPlus + 1) +
          (∫ t : ℝ, |xPlus - t| ∂endpointRemainder μ)) :
    1 ≤
      (xPlus + 1) * ((realMeasure μ) (({-1} : Set ℝ))).toReal +
        (1 - xPlus) *
          (1 - ((realMeasure μ) (({-1} : Set ℝ))).toReal) := by
  have hrem_le :
      (∫ t : ℝ, |xPlus - t| ∂endpointRemainder μ) ≤
        (1 - xPlus) *
          (1 - ((realMeasure μ) (({-1} : Set ℝ))).toReal) :=
    endpointRemainder_distance_integral_le_boundary_remainder μ
      hrem_support hdist_int
  nlinarith

/--
Boundary-distance lower bound from a nonpositive boundary potential.

This is the Jensen/log step in the right-endpoint argument.  If the boundary
point has nonpositive logarithmic potential, then the average distance from
that point to the measure is at least `1`.  Splitting the measure into the
endpoint atom at `-1` plus the canonical endpoint remainder gives the displayed
endpoint-plus-remainder lower bound.
-/
theorem endpointRemainder_boundary_distance_of_potential_nonpos
    (μ : ProbabilityMeasure UnitInterval1038) {xPlus ε : ℝ}
    (hxPlus_nonneg : 0 ≤ xPlus)
    (hpotential_nonpos : unitIntervalLogPotential μ xPlus ≤ 0)
    (hε : 0 < ε)
    (hdist_lower :
      ∀ᵐ t : ℝ ∂realMeasure μ, ε ≤ |xPlus - t|)
    (hdist_int :
      Integrable (fun t : ℝ => |xPlus - t|) (realMeasure μ))
    (hlog_int :
      Integrable (fun t : ℝ => Real.log |xPlus - t|) (realMeasure μ))
    (hrem_dist_int :
      Integrable (fun t : ℝ => |xPlus - t|) (endpointRemainder μ)) :
    1 ≤
      ((realMeasure μ) (({-1} : Set ℝ))).toReal * (xPlus + 1) +
        (∫ t : ℝ, |xPlus - t| ∂endpointRemainder μ) := by
  have hdist_avg :
      1 ≤ ∫ t : ℝ, |xPlus - t| ∂realMeasure μ := by
    by_contra hnot
    have hlt : (∫ t : ℝ, |xPlus - t| ∂realMeasure μ) < 1 :=
      lt_of_not_ge hnot
    have hpos :
        0 < measureLogPotential (realMeasure μ) xPlus :=
      measureLogPotential_pos_of_abs_integral_lt_one
        (realMeasure μ) hε hdist_lower hdist_int hlog_int hlt
    rw [← unitIntervalLogPotential_eq_realMeasure μ xPlus] at hpos
    linarith
  let f : ℝ → ℝ := fun t : ℝ => |xPlus - t|
  have hatom_int :
      Integrable f
        (((realMeasure μ) (({-1} : Set ℝ))) •
          Measure.dirac (-1 : ℝ)) := by
    exact (integrable_dirac
      (a := (-1 : ℝ))
      (f := f)
      (by simp [f])).smul_measure
        (measure_ne_top (realMeasure μ) (({-1} : Set ℝ)))
  have hsum :
      endpointRemainder μ +
          ((realMeasure μ) (({-1} : Set ℝ))) • Measure.dirac (-1 : ℝ) =
        realMeasure μ := by
    calc
      endpointRemainder μ +
          ((realMeasure μ) (({-1} : Set ℝ))) • Measure.dirac (-1 : ℝ)
          = (realMeasure μ).restrict (({-1} : Set ℝ)ᶜ) +
              (realMeasure μ).restrict ({-1} : Set ℝ) := by
              rw [endpointRemainder, Measure.restrict_singleton]
      _ = realMeasure μ := by
              exact Measure.restrict_compl_add_restrict
                (μ := realMeasure μ) (s := ({-1} : Set ℝ))
                (measurableSet_singleton (-1 : ℝ))
  have hsplit :
      (∫ t : ℝ, f t ∂realMeasure μ) =
        (∫ t : ℝ, f t ∂endpointRemainder μ) +
          (∫ t : ℝ, f t
            ∂(((realMeasure μ) (({-1} : Set ℝ))) •
              Measure.dirac (-1 : ℝ))) := by
    calc
      (∫ t : ℝ, f t ∂realMeasure μ)
          = ∫ t : ℝ, f t ∂(endpointRemainder μ +
              ((realMeasure μ) (({-1} : Set ℝ))) •
                Measure.dirac (-1 : ℝ)) := by
              rw [hsum]
      _ = (∫ t : ℝ, f t ∂endpointRemainder μ) +
          (∫ t : ℝ, f t
            ∂(((realMeasure μ) (({-1} : Set ℝ))) •
              Measure.dirac (-1 : ℝ))) := by
              exact integral_add_measure hrem_dist_int hatom_int
  have hatom_eval :
      (∫ t : ℝ, f t
          ∂(((realMeasure μ) (({-1} : Set ℝ))) •
            Measure.dirac (-1 : ℝ))) =
        ((realMeasure μ) (({-1} : Set ℝ))).toReal * (xPlus + 1) := by
    rw [integral_smul_measure]
    rw [integral_dirac]
    have hnonneg : 0 ≤ xPlus + 1 := by linarith
    simp [f, sub_eq_add_neg, abs_of_nonneg hnonneg, smul_eq_mul]
  rw [hsplit, hatom_eval] at hdist_avg
  simpa [f, add_comm] using hdist_avg

/--
Boundary-average constructor directly from nonpositive boundary potential.
-/
theorem boundary_average_of_boundary_potential_nonpos
    (μ : ProbabilityMeasure UnitInterval1038) {xPlus ε : ℝ}
    (hxPlus_nonneg : 0 ≤ xPlus)
    (hrem_support :
      ∀ᵐ t : ℝ ∂endpointRemainder μ, t ∈ Icc xPlus 1)
    (hpotential_nonpos : unitIntervalLogPotential μ xPlus ≤ 0)
    (hε : 0 < ε)
    (hdist_lower :
      ∀ᵐ t : ℝ ∂realMeasure μ, ε ≤ |xPlus - t|)
    (hdist_int :
      Integrable (fun t : ℝ => |xPlus - t|) (realMeasure μ))
    (hlog_int :
      Integrable (fun t : ℝ => Real.log |xPlus - t|) (realMeasure μ))
    (hrem_dist_int :
      Integrable (fun t : ℝ => |xPlus - t|) (endpointRemainder μ)) :
    1 ≤
      (xPlus + 1) * ((realMeasure μ) (({-1} : Set ℝ))).toReal +
        (1 - xPlus) *
          (1 - ((realMeasure μ) (({-1} : Set ℝ))).toReal) := by
  refine boundary_average_of_endpointRemainder_boundary_distance
    μ hrem_support hrem_dist_int ?_
  exact endpointRemainder_boundary_distance_of_potential_nonpos
    μ hxPlus_nonneg hpotential_nonpos hε hdist_lower hdist_int hlog_int
    hrem_dist_int

/--
Boundary-average constructor from the natural right-endpoint bookkeeping:
the endpoint is not in the positive set.

For an actual maximal positive component, the remaining topological step is to
prove `xPlus ∉ PositiveSet (unitIntervalLogPotential μ)`.  Once that is
available, this theorem supplies the boundary-average field through the
Jensen/log bridge above.
-/
theorem boundary_average_of_right_endpoint_not_positive
    (μ : ProbabilityMeasure UnitInterval1038) {xPlus ε : ℝ}
    (hxPlus_nonneg : 0 ≤ xPlus)
    (hrem_support :
      ∀ᵐ t : ℝ ∂endpointRemainder μ, t ∈ Icc xPlus 1)
    (hnot_positive :
      xPlus ∉ PositiveSet (unitIntervalLogPotential μ))
    (hε : 0 < ε)
    (hdist_lower :
      ∀ᵐ t : ℝ ∂realMeasure μ, ε ≤ |xPlus - t|)
    (hdist_int :
      Integrable (fun t : ℝ => |xPlus - t|) (realMeasure μ))
    (hlog_int :
      Integrable (fun t : ℝ => Real.log |xPlus - t|) (realMeasure μ))
    (hrem_dist_int :
      Integrable (fun t : ℝ => |xPlus - t|) (endpointRemainder μ)) :
    1 ≤
      (xPlus + 1) * ((realMeasure μ) (({-1} : Set ℝ))).toReal +
        (1 - xPlus) *
          (1 - ((realMeasure μ) (({-1} : Set ℝ))).toReal) := by
  refine boundary_average_of_boundary_potential_nonpos
    μ hxPlus_nonneg hrem_support ?_ hε hdist_lower hdist_int hlog_int
    hrem_dist_int
  exact le_of_not_gt hnot_positive

/--
On the baseline punctured interval, the log kernel is integrable against the
canonical endpoint remainder once the normalized support shape
`support ⊆ {-1} ∪ [0,1]` is known.
-/
theorem endpointRemainder_kernel_integrable_of_normalized_support
    (μ : ProbabilityMeasure UnitInterval1038)
    (hsupport :
      (realMeasure μ).support ⊆ ({-1} : Set ℝ) ∪ Icc (0 : ℝ) 1) :
    ∀ x : ℝ, x ∈ BaselinePunctured →
      Integrable (fun t : ℝ => Real.log (1 / |x - t|))
        (endpointRemainder μ) := by
  intro x hx
  have hxBase : x ∈ BaselineInterval := hx.1
  have hxneg : x < 0 := hxBase.2
  let K : Set ℝ := Icc (0 : ℝ) 1
  have hmemK : ∀ᵐ t : ℝ ∂endpointRemainder μ, t ∈ K :=
    endpointRemainder_ae_mem_Icc_zero_one μ hsupport
  have hcompact : IsCompact K := isCompact_Icc
  have hsep : K ⊆ {t : ℝ | -x ≤ |x - t|} := by
    intro t ht
    change -x ≤ |x - t|
    have ht0 : 0 ≤ t := ht.1
    have hnonpos : x - t ≤ 0 := by linarith
    rw [abs_of_nonpos hnonpos]
    linarith
  have hcont :
      ContinuousOn (fun t : ℝ => Real.log (1 / |x - t|)) K := by
    exact logKernel_continuousOn_of_dist_ge (by linarith : 0 < -x) hsep
  haveI : IsFiniteMeasure (endpointRemainder μ) := by
    refine ⟨?_⟩
    rw [endpointRemainder_mass μ]
    exact ENNReal.ofReal_lt_top
  exact integrable_of_ae_mem_compact_of_continuousOn
    (endpointRemainder μ) K
    (fun t : ℝ => Real.log (1 / |x - t|))
    hmemK hcompact hcont

/-- The endpoint atom log-kernel is integrable for every test point. -/
lemma endpointAtom_logKernel_integrable
    (μ : ProbabilityMeasure UnitInterval1038) (x : ℝ) :
    Integrable (fun t : ℝ => Real.log (1 / |x - t|))
      (((realMeasure μ) (({-1} : Set ℝ))) •
        Measure.dirac (-1 : ℝ)) := by
  exact (integrable_dirac
    (a := (-1 : ℝ))
    (f := fun t : ℝ => Real.log (1 / |x - t|))
    (by simp)).smul_measure (measure_ne_top (realMeasure μ) (({-1} : Set ℝ)))

/--
Exact potential decomposition into the endpoint atom at `-1` plus the canonical
endpoint remainder.
-/
theorem unitIntervalLogPotential_eq_endpointAtom_add_endpointRemainder
    (μ : ProbabilityMeasure UnitInterval1038) (x : ℝ)
    (hrem :
      Integrable (fun t : ℝ => Real.log (1 / |x - t|))
        (endpointRemainder μ)) :
    unitIntervalLogPotential μ x =
      ((realMeasure μ) (({-1} : Set ℝ))).toReal *
          Real.log (1 / |x + 1|) +
        (∫ t : ℝ, Real.log (1 / |x - t|) ∂endpointRemainder μ) := by
  let f : ℝ → ℝ := fun t : ℝ => Real.log (1 / |x - t|)
  have hatom :
      Integrable f
        (((realMeasure μ) (({-1} : Set ℝ))) •
          Measure.dirac (-1 : ℝ)) :=
    endpointAtom_logKernel_integrable μ x
  have hsum :
      endpointRemainder μ +
          ((realMeasure μ) (({-1} : Set ℝ))) • Measure.dirac (-1 : ℝ) =
        realMeasure μ := by
    calc
      endpointRemainder μ +
          ((realMeasure μ) (({-1} : Set ℝ))) • Measure.dirac (-1 : ℝ)
          = (realMeasure μ).restrict (({-1} : Set ℝ)ᶜ) +
              (realMeasure μ).restrict ({-1} : Set ℝ) := by
              rw [endpointRemainder, Measure.restrict_singleton]
      _ = realMeasure μ := by
              exact Measure.restrict_compl_add_restrict
                (μ := realMeasure μ) (s := ({-1} : Set ℝ))
                (measurableSet_singleton (-1 : ℝ))
  calc
    unitIntervalLogPotential μ x = measureLogPotential (realMeasure μ) x := by
      rw [unitIntervalLogPotential_eq_realMeasure]
    _ = ∫ t : ℝ, f t ∂realMeasure μ := rfl
    _ = ∫ t : ℝ, f t ∂(endpointRemainder μ +
          ((realMeasure μ) (({-1} : Set ℝ))) • Measure.dirac (-1 : ℝ)) := by
          rw [hsum]
    _ = (∫ t : ℝ, f t ∂endpointRemainder μ) +
          (∫ t : ℝ, f t
            ∂(((realMeasure μ) (({-1} : Set ℝ))) • Measure.dirac (-1 : ℝ))) := by
          exact integral_add_measure hrem hatom
    _ = (∫ t : ℝ, f t ∂endpointRemainder μ) +
          ((realMeasure μ) (({-1} : Set ℝ))).toReal *
            Real.log (1 / |x + 1|) := by
          rw [integral_smul_measure]
          rw [integral_dirac]
          simp [f, sub_eq_add_neg, smul_eq_mul, mul_comm]
    _ = ((realMeasure μ) (({-1} : Set ℝ))).toReal *
          Real.log (1 / |x + 1|) +
        (∫ t : ℝ, Real.log (1 / |x - t|) ∂endpointRemainder μ) := by
          ring

/--
Data needed to use the canonical endpoint remainder in
`TaoVariationComponentPackage`.

This removes the need to supply the remainder measure, its support in the
selected support, endpoint exclusion, mass, and mass nonnegativity separately.
The analytic log-integrability and endpoint-plus-remainder lower bound remain
explicit because they depend on the chosen normalized potential presentation.
-/
structure CanonicalEndpointRemainderData
    (μ : ProbabilityMeasure UnitInterval1038) (Support : Set ℝ)
    (U : ℝ → ℝ) where
  support_contains_real_support : (realMeasure μ).support ⊆ Support
  kernel_integrable : ∀ x : ℝ, x ∈ BaselinePunctured →
    Integrable (fun t : ℝ => Real.log (1 / |x - t|)) (endpointRemainder μ)
  potential_decomposition_lower : ∀ x : ℝ, x ∈ BaselinePunctured →
    ((realMeasure μ) (({-1} : Set ℝ))).toReal * Real.log (1 / |x + 1|) +
      (∫ t : ℝ, Real.log (1 / |x - t|) ∂endpointRemainder μ) ≤ U x

/--
For the unmodified unit-interval potential, canonical endpoint-remainder data
only needs support containment and log-kernel integrability; the potential
decomposition is an equality.
-/
def CanonicalEndpointRemainderData.of_unitIntervalLogPotential
    (μ : ProbabilityMeasure UnitInterval1038) (Support : Set ℝ)
    (hSupport : (realMeasure μ).support ⊆ Support)
    (hkernel : ∀ x : ℝ, x ∈ BaselinePunctured →
      Integrable (fun t : ℝ => Real.log (1 / |x - t|)) (endpointRemainder μ)) :
    CanonicalEndpointRemainderData μ Support (unitIntervalLogPotential μ) where
  support_contains_real_support := hSupport
  kernel_integrable := hkernel
  potential_decomposition_lower := by
    intro x hx
    rw [unitIntervalLogPotential_eq_endpointAtom_add_endpointRemainder
      μ x (hkernel x hx)]

/--
Build endpoint-normalization data from component data and the canonical
endpoint remainder.
-/
def TaoComponentReductionData.toTaoEndpointNormalizationData_of_endpointRemainder
    {μ : ProbabilityMeasure UnitInterval1038} {U : ℝ → ℝ}
    (D : TaoComponentReductionData)
    (hendpointMass :
      D.endpointMass = ((realMeasure μ) (({-1} : Set ℝ))).toReal)
    (Hrem : CanonicalEndpointRemainderData μ D.Support U) :
    TaoEndpointNormalizationData U :=
  D.toTaoEndpointNormalizationData_of_remainder_ae_support
    (endpointRemainder μ)
    (endpointRemainder_ae_mem_support μ Hrem.support_contains_real_support)
    (endpointRemainder_ae_ne_endpoint μ)
    (by
      rw [endpointRemainder_mass μ, hendpointMass])
    (by
      rw [hendpointMass]
      exact endpointRemainder_mass_nonneg μ)
    Hrem.kernel_integrable
    (by
      intro x hx
      simpa [hendpointMass] using Hrem.potential_decomposition_lower x hx)

/-! ### Canonical endpoint variation package -/

/--
Canonical endpoint version of `TaoVariationComponentPackage`.

Compared with `TaoVariationComponentPackage`, this structure no longer asks
the caller to provide an arbitrary endpoint mass or arbitrary remainder
measure.  The endpoint mass is fixed to the pushed-forward measure of `{-1}`,
and the remainder is fixed to `endpointRemainder μ`.  Thus the remaining
fields are the component/variation fields plus the genuine analytic
endpoint-remainder inputs packaged in `CanonicalEndpointRemainderData`.
-/
structure CanonicalEndpointVariationPackageData
    (μ : ProbabilityMeasure UnitInterval1038) (U : ℝ → ℝ) where
  mean_choice : TaoVariationMeanChoice
  reflected : Bool
  translation : ℝ
  component : Set ℝ
  Support : Set ℝ
  xMinus : ℝ
  xPlus : ℝ
  component_positive : component ⊆ PositiveSet U
  component_interval : component = Ioo xMinus xPlus
  baseline_inside_component : Ioo (-1 : ℝ) 0 ⊆ component
  support_bounded : Support ⊆ Icc (-1 : ℝ) 1
  unique_support_in_component :
    ∀ t : ℝ, t ∈ Support → t ∈ component → t = -1
  right_endpoint_positive : 0 < xPlus
  boundary_average :
    1 ≤
      (xPlus + 1) * ((realMeasure μ) (({-1} : Set ℝ))).toReal +
        (1 - xPlus) *
          (1 - ((realMeasure μ) (({-1} : Set ℝ))).toReal)
  remainder_data :
    CanonicalEndpointRemainderData μ Support U

/--
Convert canonical endpoint variation data into the existing concrete
`TaoVariationComponentPackage`.

This removes repeated endpoint-remainder bookkeeping from the standard
reduction interface: a.e. support, endpoint exclusion, mass identity, mass
nonnegativity, kernel integrability, and potential decomposition are all
provided by the canonical endpoint-remainder lemmas.
-/
def CanonicalEndpointVariationPackageData.toTaoVariationComponentPackage
    {μ : ProbabilityMeasure UnitInterval1038} {U : ℝ → ℝ}
    (D : CanonicalEndpointVariationPackageData μ U) :
    TaoVariationComponentPackage U where
  mean_choice := D.mean_choice
  reflected := D.reflected
  translation := D.translation
  component := D.component
  Support := D.Support
  endpointMass := ((realMeasure μ) (({-1} : Set ℝ))).toReal
  xMinus := D.xMinus
  xPlus := D.xPlus
  component_positive := D.component_positive
  component_interval := D.component_interval
  baseline_inside_component := D.baseline_inside_component
  support_bounded := D.support_bounded
  unique_support_in_component := D.unique_support_in_component
  right_endpoint_positive := D.right_endpoint_positive
  boundary_average := D.boundary_average
  remainder := endpointRemainder μ
  remainder_support_in_support :=
    endpointRemainder_ae_mem_support μ
      D.remainder_data.support_contains_real_support
  remainder_no_endpoint := endpointRemainder_ae_ne_endpoint μ
  remainder_mass := endpointRemainder_mass μ
  remainder_mass_nonneg := endpointRemainder_mass_nonneg μ
  kernel_integrable := D.remainder_data.kernel_integrable
  potential_decomposition_lower :=
    D.remainder_data.potential_decomposition_lower

/-- Build endpoint-normalized data directly from canonical endpoint data. -/
def CanonicalEndpointVariationPackageData.toTaoEndpointNormalizationData
    {μ : ProbabilityMeasure UnitInterval1038} {U : ℝ → ℝ}
    (D : CanonicalEndpointVariationPackageData μ U) :
    TaoEndpointNormalizationData U :=
  D.toTaoVariationComponentPackage.toTaoEndpointNormalizationData

/-- Build reduced-potential data directly from canonical endpoint data. -/
def CanonicalEndpointVariationPackageData.toTaoReducedPotentialData
    {μ : ProbabilityMeasure UnitInterval1038} {U : ℝ → ℝ}
    (D : CanonicalEndpointVariationPackageData μ U) :
    TaoReducedPotentialData U :=
  D.toTaoVariationComponentPackage.toTaoReducedPotentialData

/-- Build the finite-route endpoint potential directly from canonical data. -/
def CanonicalEndpointVariationPackageData.toNormalizedEndpointPotential
    {μ : ProbabilityMeasure UnitInterval1038} {U : ℝ → ℝ}
    (D : CanonicalEndpointVariationPackageData μ U) :
    NormalizedEndpointPotential U :=
  D.toTaoVariationComponentPackage.toNormalizedEndpointPotential

/--
Specialization to the unmodified unit-interval logarithmic potential.  The
endpoint-plus-remainder decomposition is already proved as an equality, so this
constructor only asks for support containment and endpoint-remainder kernel
integrability.
-/
def CanonicalEndpointVariationPackageData.of_unitIntervalLogPotential
    (μ : ProbabilityMeasure UnitInterval1038)
    (mean_choice : TaoVariationMeanChoice)
    (reflected : Bool)
    (translation : ℝ)
    (component : Set ℝ)
    (Support : Set ℝ)
    (xMinus xPlus : ℝ)
    (component_positive :
      component ⊆ PositiveSet (unitIntervalLogPotential μ))
    (component_interval : component = Ioo xMinus xPlus)
    (baseline_inside_component : Ioo (-1 : ℝ) 0 ⊆ component)
    (support_bounded : Support ⊆ Icc (-1 : ℝ) 1)
    (unique_support_in_component :
      ∀ t : ℝ, t ∈ Support → t ∈ component → t = -1)
    (right_endpoint_positive : 0 < xPlus)
    (boundary_average :
      1 ≤
        (xPlus + 1) * ((realMeasure μ) (({-1} : Set ℝ))).toReal +
          (1 - xPlus) *
            (1 - ((realMeasure μ) (({-1} : Set ℝ))).toReal))
    (support_contains_real_support :
      (realMeasure μ).support ⊆ Support)
    (kernel_integrable :
      ∀ x : ℝ, x ∈ BaselinePunctured →
        Integrable (fun t : ℝ => Real.log (1 / |x - t|))
          (endpointRemainder μ)) :
    CanonicalEndpointVariationPackageData μ (unitIntervalLogPotential μ) where
  mean_choice := mean_choice
  reflected := reflected
  translation := translation
  component := component
  Support := Support
  xMinus := xMinus
  xPlus := xPlus
  component_positive := component_positive
  component_interval := component_interval
  baseline_inside_component := baseline_inside_component
  support_bounded := support_bounded
  unique_support_in_component := unique_support_in_component
  right_endpoint_positive := right_endpoint_positive
  boundary_average := boundary_average
  remainder_data :=
    CanonicalEndpointRemainderData.of_unitIntervalLogPotential μ Support
      support_contains_real_support kernel_integrable

/--
Canonical component-package form of the variation input for relaxed
minimizers.  This is narrower than
`VariationEndpoint.ComponentPackageFromVariation`: it requires the upstream
variation argument to produce the canonical endpoint package for the actual
relaxed minimizer measure, with endpoint mass and remainder already fixed to
the canonical choices.
-/
structure CanonicalComponentPackageFromVariation where
  canonicalPackage : ∀ M : MinimizerExistence.RelaxedMinimizer,
    CanonicalEndpointVariationPackageData M.μ
      (VariationEndpoint.RelaxedPotential M)

/--
A canonical component-package provider supplies the existing component-package
variation interface.
-/
def CanonicalComponentPackageFromVariation.toComponentPackageFromVariation
    (H : CanonicalComponentPackageFromVariation) :
    VariationEndpoint.ComponentPackageFromVariation where
  componentPackage := fun M =>
    (H.canonicalPackage M).toTaoVariationComponentPackage

/--
Diagonal-safe minimizer plus canonical component package.
-/
theorem exists_relaxed_minimizer_with_canonical_component_package
    (Hcore : LowerSemicontinuity.OneSidedCompactCore)
    (Hvar : CanonicalComponentPackageFromVariation) :
    Nonempty (Σ M : MinimizerExistence.RelaxedMinimizer,
      CanonicalEndpointVariationPackageData M.μ
        (VariationEndpoint.RelaxedPotential M)) := by
  rcases MinimizerExistence.exists_relaxed_minimizer_of_oneSidedCompactCore
      Hcore with ⟨M⟩
  exact ⟨⟨M, Hvar.canonicalPackage M⟩⟩

/--
Canonical variation packages imply the baseline interval length consequence.
-/
theorem exists_baseline_length_from_canonical_componentPackage
    (Hcore : LowerSemicontinuity.OneSidedCompactCore)
    (Hvar : CanonicalComponentPackageFromVariation) :
    ∃ M : MinimizerExistence.RelaxedMinimizer,
      ENNReal.ofReal (Real.sqrt 2) ≤
        volume (PositiveSet (VariationEndpoint.RelaxedPotential M)) :=
  VariationEndpoint.exists_baseline_length_from_componentPackage_of_oneSidedCompactCore
    Hcore Hvar.toComponentPackageFromVariation

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
Countable-support-hit normalized rigidity gives the actual component-block
atomization statement.
-/
theorem CountableSupportHitNormalizedBlockRigidityData.componentBlock_eq_dirac
    {α : Type*} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {a b : α} {μ : ProbabilityMeasure UnitInterval1038}
    (D : CountableSupportHitNormalizedBlockRigidityData P a b μ) :
    componentBlock D.replacement.component =
      componentMass D.replacement.component •
        Measure.dirac (componentBarycenter D.replacement.component) := by
  exact componentBlock_eq_componentMass_smul_dirac_of_normalized_block_eq_dirac
    D.replacement.component D.replacement.componentMass_pos
    D.normalized_block_eq_dirac

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

/--
Finite-support-hit normalized rigidity gives the actual component-block
atomization statement.
-/
theorem FiniteSupportHitNormalizedBlockRigidityData.componentBlock_eq_dirac
    {α : Type*} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {a b : α} {μ : ProbabilityMeasure UnitInterval1038}
    (D : FiniteSupportHitNormalizedBlockRigidityData P a b μ) :
    componentBlock D.replacement.component =
      componentMass D.replacement.component •
        Measure.dirac (componentBarycenter D.replacement.component) := by
  exact componentBlock_eq_componentMass_smul_dirac_of_normalized_block_eq_dirac
    D.replacement.component D.replacement.componentMass_pos
    D.normalized_block_eq_dirac

end
end ComponentAtomization
end StandardReduction
end Erdos1038
