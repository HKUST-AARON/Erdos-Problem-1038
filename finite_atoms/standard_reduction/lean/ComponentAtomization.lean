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

/-- A point carrying positive singleton mass lies in the topological support. -/
private theorem mem_support_of_singleton_mass_pos
    (μ : Measure ℝ) {a : ℝ}
    (hmass : 0 < μ ({a} : Set ℝ)) :
    a ∈ μ.support := by
  rw [Measure.mem_support_iff_forall]
  intro U hU
  have haU : a ∈ U := mem_of_mem_nhds hU
  have hsingleton_subset : ({a} : Set ℝ) ⊆ U := by
    intro x hx
    simpa using hx ▸ haU
  exact lt_of_lt_of_le hmass (measure_mono hsingleton_subset)

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

/--
If component-block atomization has been proved and the normalized endpoint
`-1` is a support point inside the component, then the component barycenter is
the normalized endpoint.
-/
theorem componentBarycenter_eq_endpoint_of_componentBlock_eq_dirac
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    (hblock :
      componentBlock C =
        componentMass C • Measure.dirac (componentBarycenter C))
    (hendpoint_support : (-1 : ℝ) ∈ (realMeasure μ).support)
    (hendpoint_component : (-1 : ℝ) ∈ C.interval) :
    componentBarycenter C = -1 := by
  have hendpoint_eq :
      (-1 : ℝ) = componentBarycenter C :=
    unique_support_in_component_of_componentBlock_eq_dirac
      C (fun _ ht => ht) hblock (-1) hendpoint_support
      hendpoint_component
  exact hendpoint_eq.symm

/--
Endpoint-mass version of the barycenter endpoint bridge.  Positive mass at the
normalized endpoint makes `-1` a topological support point, so the atomized
component block has barycenter `-1` as soon as the selected component contains
that endpoint.
-/
theorem componentBarycenter_eq_endpoint_of_componentBlock_eq_dirac_of_endpoint_mass_pos
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    (hblock :
      componentBlock C =
        componentMass C • Measure.dirac (componentBarycenter C))
    (hmass : 0 < (realMeasure μ) ({-1} : Set ℝ))
    (hendpoint_component : (-1 : ℝ) ∈ C.interval) :
    componentBarycenter C = -1 := by
  exact componentBarycenter_eq_endpoint_of_componentBlock_eq_dirac C hblock
    (mem_support_of_singleton_mass_pos (realMeasure μ) hmass)
    hendpoint_component

/--
If the selected component contains the whole baseline interval `(-1,0)`, then
its left endpoint is at or to the left of `-1`, and its right endpoint is at or
to the right of `0`.
-/
theorem component_endpoint_order_of_baseline_inside
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    (hbaseline : Ioo (-1 : ℝ) 0 ⊆ C.interval) :
    C.left ≤ (-1 : ℝ) ∧ (0 : ℝ) ≤ C.right := by
  constructor
  · by_contra hnot
    have hleft_gt : (-1 : ℝ) < C.left := lt_of_not_ge hnot
    have hleft_lt_zero : C.left < 0 := by
      have hhalf_mem : ((-1 / 2 : ℝ)) ∈ C.interval := by
        exact hbaseline (by norm_num)
      rw [PositiveComponent.interval_eq] at hhalf_mem
      exact lt_trans hhalf_mem.1 (by norm_num)
    let y : ℝ := ((-1 : ℝ) + C.left) / 2
    have hy_base : y ∈ Ioo (-1 : ℝ) 0 := by
      constructor
      · dsimp [y]
        linarith
      · dsimp [y]
        linarith
    have hy_comp : y ∈ C.interval := hbaseline hy_base
    rw [PositiveComponent.interval_eq] at hy_comp
    have hy_lt_left : y < C.left := by
      dsimp [y]
      linarith
    linarith [hy_comp.1, hy_lt_left]
  · by_contra hnot
    have hright_lt : C.right < 0 := lt_of_not_ge hnot
    have hright_gt_neg_half : (-1 / 2 : ℝ) < C.right := by
      have hhalf_mem : ((-1 / 2 : ℝ)) ∈ C.interval := by
        exact hbaseline (by norm_num)
      rw [PositiveComponent.interval_eq] at hhalf_mem
      exact hhalf_mem.2
    let y : ℝ := C.right / 2
    have hy_base : y ∈ Ioo (-1 : ℝ) 0 := by
      constructor
      · dsimp [y]
        linarith
      · dsimp [y]
        linarith
    have hy_comp : y ∈ C.interval := hbaseline hy_base
    rw [PositiveComponent.interval_eq] at hy_comp
    have hright_lt_y : C.right < y := by
      dsimp [y]
      linarith
    linarith [hy_comp.2, hright_lt_y]

/--
If the selected component contains the baseline interval and its left endpoint
is strictly to the left of `-1`, then the normalized endpoint lies in the
selected component.
-/
theorem endpoint_mem_component_of_baseline_inside_left_lt
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    (hbaseline : Ioo (-1 : ℝ) 0 ⊆ C.interval)
    (hleft : C.left < (-1 : ℝ)) :
    (-1 : ℝ) ∈ C.interval := by
  rw [PositiveComponent.interval_eq]
  constructor
  · exact hleft
  · have hright_nonneg : (0 : ℝ) ≤ C.right :=
      (component_endpoint_order_of_baseline_inside C hbaseline).2
    linarith

/--
Nondegenerate-left-endpoint form of endpoint membership.  Baseline containment
already gives `C.left ≤ -1`; excluding equality upgrades this to the strict
left-endpoint condition needed for `-1 ∈ C.interval`.
-/
theorem endpoint_mem_component_of_baseline_inside_left_ne
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    (hbaseline : Ioo (-1 : ℝ) 0 ⊆ C.interval)
    (hleft_ne : C.left ≠ (-1 : ℝ)) :
    (-1 : ℝ) ∈ C.interval := by
  have hleft_le : C.left ≤ (-1 : ℝ) :=
    (component_endpoint_order_of_baseline_inside C hbaseline).1
  exact endpoint_mem_component_of_baseline_inside_left_lt C hbaseline
    (lt_of_le_of_ne hleft_le hleft_ne)

/--
Endpoint-mass and endpoint-order form of the barycenter bridge.  Once
atomization has been proved, positive mass at `-1`, baseline containment, and a
strictly left normalized component endpoint imply that the barycenter is `-1`.
-/
theorem componentBarycenter_eq_endpoint_of_componentBlock_eq_dirac_of_endpoint_mass_pos_left_lt
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    (hblock :
      componentBlock C =
        componentMass C • Measure.dirac (componentBarycenter C))
    (hmass : 0 < (realMeasure μ) ({-1} : Set ℝ))
    (hbaseline : Ioo (-1 : ℝ) 0 ⊆ C.interval)
    (hleft : C.left < (-1 : ℝ)) :
    componentBarycenter C = -1 := by
  exact componentBarycenter_eq_endpoint_of_componentBlock_eq_dirac_of_endpoint_mass_pos
    C hblock hmass
    (endpoint_mem_component_of_baseline_inside_left_lt C hbaseline hleft)

/--
Endpoint-mass and nondegenerate-left-endpoint form of the barycenter bridge.
This replaces the strict order input by the weaker equality-exclusion input
`C.left ≠ -1`.
-/
theorem componentBarycenter_eq_endpoint_of_componentBlock_eq_dirac_of_endpoint_mass_pos_left_ne
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    (hblock :
      componentBlock C =
        componentMass C • Measure.dirac (componentBarycenter C))
    (hmass : 0 < (realMeasure μ) ({-1} : Set ℝ))
    (hbaseline : Ioo (-1 : ℝ) 0 ⊆ C.interval)
    (hleft_ne : C.left ≠ (-1 : ℝ)) :
    componentBarycenter C = -1 := by
  exact componentBarycenter_eq_endpoint_of_componentBlock_eq_dirac_of_endpoint_mass_pos
    C hblock hmass
    (endpoint_mem_component_of_baseline_inside_left_ne C hbaseline hleft_ne)

/-! ### Endpoint support shape and boundary average -/

/-- Neighborhood form of the one-sided boundary exclusion argument. -/
private theorem not_mem_of_mem_nhds_no_right_points
    {S : Set ℝ} {r : ℝ}
    (hnhds : S ∈ 𝓝 r)
    (hNoRight : ∀ y : ℝ, r < y → y ∉ S) :
    r ∉ S := by
  intro hr
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε, hε, hball⟩
  let y : ℝ := r + ε / 2
  have hry : r < y := by
    dsimp [y]
    linarith
  have hydist : dist y r < ε := by
    dsimp [y]
    rw [Real.dist_eq]
    have hsub : r + ε / 2 - r = ε / 2 := by ring
    rw [hsub]
    have hhalf_nonneg : 0 ≤ ε / 2 := by linarith
    rw [abs_of_nonneg hhalf_nonneg]
    linarith
  exact hNoRight y hry (hball hydist)

/--
Open-set right-boundary lemma.

If an open set has no points strictly to the right of `r`, then `r` itself
cannot lie in the open set.  This is the topology core needed later for a
maximal positive component: once `xPlus` is known to be the right boundary of
the selected component, this lemma supplies
`xPlus ∉ PositiveSet (unitIntervalLogPotential μ)`.
-/
theorem not_mem_of_isOpen_no_right_points
    {S : Set ℝ} {r : ℝ}
    (hOpen : IsOpen S)
    (hNoRight : ∀ y : ℝ, r < y → y ∉ S) :
    r ∉ S := by
  intro hr
  exact not_mem_of_mem_nhds_no_right_points
    (hOpen.mem_nhds hr) hNoRight hr

/--
Continuous right-boundary lemma for a strict positivity set.

This local version avoids requiring global openness of the real-valued
logarithmic positive set.  It is enough to know continuity at the selected
right endpoint and that no strictly right point is positive.
-/
theorem not_mem_positiveSet_of_continuousAt_no_right_points
    {U : ℝ → ℝ} {r : ℝ}
    (hcont : ContinuousAt U r)
    (hNoRight : ∀ y : ℝ, r < y → y ∉ PositiveSet U) :
    r ∉ PositiveSet U := by
  intro hr
  have hpre : PositiveSet U ∈ 𝓝 r := by
    simpa [PositiveSet] using hcont (isOpen_Ioi.mem_nhds hr)
  exact not_mem_of_mem_nhds_no_right_points hpre hNoRight hr

/--
Right-side maximality of a component interval excludes positive points to the
right endpoint.

The hypothesis says that every positive point to the right of `xMinus` belongs
to the selected interval `(xMinus,xPlus)`.  This is the exact coverage property
that a maximal positive component will later supply.
-/
theorem no_right_positive_of_component_right_cover
    {U : ℝ → ℝ} {xMinus xPlus : ℝ}
    (hxMinus_lt_xPlus : xMinus < xPlus)
    (hcover :
      ∀ y : ℝ, xMinus < y → y ∈ PositiveSet U → y ∈ Ioo xMinus xPlus) :
    ∀ y : ℝ, xPlus < y → y ∉ PositiveSet U := by
  intro y hy hpos
  have hxMinus_lt_y : xMinus < y :=
    lt_trans hxMinus_lt_xPlus hy
  have hycomp := hcover y hxMinus_lt_y hpos
  exact not_lt_of_ge (le_of_lt hy) hycomp.2

/--
Right-region component equality supplies the right-cover property.

This is the minimal topological interface for the later maximal-component
selection step: once the chosen component is identified with all positive
points to the right of `xMinus`, the right-cover hypothesis used by the
endpoint package is automatic.
-/
private theorem right_cover_of_component_eq_positiveSet_inter_Ioi
    {U : ℝ → ℝ} {component : Set ℝ} {xMinus xPlus : ℝ}
    (right_region_eq :
      component = PositiveSet U ∩ Ioi xMinus)
    (component_interval : component = Ioo xMinus xPlus) :
    ∀ y : ℝ, xMinus < y → y ∈ PositiveSet U → y ∈ Ioo xMinus xPlus := by
  intro y hy hpos
  have hycomponent : y ∈ component := by
    rw [right_region_eq]
    exact ⟨hpos, hy⟩
  simpa [component_interval] using hycomponent

/--
Right-region component equality also supplies positivity on the chosen
component.
-/
private theorem component_positive_of_component_eq_positiveSet_inter_Ioi
    {U : ℝ → ℝ} {component : Set ℝ} {xMinus : ℝ}
    (right_region_eq :
      component = PositiveSet U ∩ Ioi xMinus) :
    component ⊆ PositiveSet U := by
  intro y hy
  rw [right_region_eq] at hy
  exact hy.1

/-- Normalized support shape from component order and selected-support containment. -/
private theorem realMeasure_support_subset_normalized_of_component_order
    (μ : ProbabilityMeasure UnitInterval1038)
    (component : Set ℝ)
    (Support : Set ℝ)
    (xMinus xPlus : ℝ)
    (component_interval : component = Ioo xMinus xPlus)
    (baseline_inside_component : Ioo (-1 : ℝ) 0 ⊆ component)
    (support_bounded : Support ⊆ Icc (-1 : ℝ) 1)
    (unique_support_in_component :
      ∀ t : ℝ, t ∈ Support → t ∈ component → t = -1)
    (support_contains_real_support :
      (realMeasure μ).support ⊆ Support) :
    (realMeasure μ).support ⊆ ({-1} : Set ℝ) ∪ Icc (0 : ℝ) 1 := by
  refine support_subset_endpoint_union_nonnegative
    (xMinus := xMinus) (xPlus := xPlus)
    (fun t ht => support_bounded (support_contains_real_support ht)) ?_ ?_
  · intro y hy
    have hycomp : y ∈ component := baseline_inside_component hy
    simpa [component_interval] using hycomp
  · intro t htSupport htComp
    exact unique_support_in_component t (support_contains_real_support htSupport)
      (by simpa [component_interval] using htComp)

/--
Right-region equality puts the right endpoint outside the positive set, without
any continuity assumption.  If `xPlus` were positive, then since
`xMinus < xPlus` it would belong to the right-region component, contradicting
the interval representation `(xMinus,xPlus)`.
-/
private theorem not_mem_positiveSet_of_component_eq_positiveSet_inter_Ioi
    {U : ℝ → ℝ} {component : Set ℝ} {xMinus xPlus : ℝ}
    (hxMinus_lt_xPlus : xMinus < xPlus)
    (right_region_eq :
      component = PositiveSet U ∩ Ioi xMinus)
    (component_interval : component = Ioo xMinus xPlus) :
    xPlus ∉ PositiveSet U := by
  intro hpos
  have hx_component : xPlus ∈ component := by
    rw [right_region_eq]
    exact ⟨hpos, hxMinus_lt_xPlus⟩
  have hx_interval : xPlus ∈ Ioo xMinus xPlus := by
    rw [component_interval] at hx_component
    exact hx_component
  exact (lt_irrefl xPlus) hx_interval.2

/--
If a point is outside the topological support of the real measure, then it is
separated by a positive distance from almost every point of the measure.
-/
private theorem exists_ae_dist_ge_of_not_mem_realMeasure_support
    (μ : ProbabilityMeasure UnitInterval1038) {x : ℝ}
    (hx : x ∉ (realMeasure μ).support) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᵐ t : ℝ ∂realMeasure μ, ε ≤ |x - t| := by
  rcases Measure.notMem_support_iff_exists.mp hx with ⟨U, hU_nhds, hU_zero⟩
  rcases Metric.mem_nhds_iff.mp hU_nhds with ⟨δ, hδ, hball_sub⟩
  refine ⟨δ, hδ, ?_⟩
  have hball_zero :
      (realMeasure μ) (Metric.ball x δ) = 0 :=
    measure_mono_null hball_sub hU_zero
  have h_ae_not_ball :
      ∀ᵐ t : ℝ ∂realMeasure μ, t ∉ Metric.ball x δ := by
    exact ae_iff.mpr (by simpa using hball_zero)
  filter_upwards [h_ae_not_ball] with t ht
  rw [Metric.mem_ball, dist_comm, Real.dist_eq] at ht
  exact le_of_not_gt ht

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

/-- Endpoint-remainder right support from component order and selected-support containment. -/
private theorem endpointRemainder_ae_mem_Icc_xPlus_one_of_component_order
    (μ : ProbabilityMeasure UnitInterval1038)
    (component : Set ℝ)
    (Support : Set ℝ)
    (xMinus xPlus : ℝ)
    (component_interval : component = Ioo xMinus xPlus)
    (baseline_inside_component : Ioo (-1 : ℝ) 0 ⊆ component)
    (support_bounded : Support ⊆ Icc (-1 : ℝ) 1)
    (unique_support_in_component :
      ∀ t : ℝ, t ∈ Support → t ∈ component → t = -1)
    (support_contains_real_support :
      (realMeasure μ).support ⊆ Support) :
    ∀ᵐ t : ℝ ∂endpointRemainder μ, t ∈ Icc xPlus 1 :=
  endpointRemainder_ae_mem_Icc_xPlus_one_of_support_order μ
    support_contains_real_support support_bounded
    (by
      intro y hy
      have hycomp : y ∈ component := baseline_inside_component hy
      simpa [component_interval] using hycomp)
    (by
      intro t htSupport htComp
      exact unique_support_in_component t htSupport
        (by simpa [component_interval] using htComp))

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

/-! ### Automatic integrability bridges for the boundary Jensen step -/

/-- The distance from a fixed point is integrable against the real unit-interval
probability measure. -/
private theorem realMeasure_distance_integrable
    (μ : ProbabilityMeasure UnitInterval1038) (x : ℝ) :
    Integrable (fun t : ℝ => |x - t|) (realMeasure μ) := by
  haveI : IsFiniteMeasure (realMeasure μ) := inferInstance
  exact integrable_of_ae_mem_compact_of_continuousOn
    (realMeasure μ) (Icc (-1 : ℝ) 1)
    (fun t : ℝ => |x - t|)
    (realMeasure_ae_mem_unitInterval μ)
    isCompact_Icc
    ((continuousOn_const.sub continuousOn_id).abs)

/-- The endpoint remainder distance is integrable once the remainder is a.e.
supported in a compact right-side interval. -/
private theorem endpointRemainder_distance_integrable_of_ae_mem_Icc
    (μ : ProbabilityMeasure UnitInterval1038) {xPlus : ℝ}
    (hrem_support :
      ∀ᵐ t : ℝ ∂endpointRemainder μ, t ∈ Icc xPlus 1) :
    Integrable (fun t : ℝ => |xPlus - t|) (endpointRemainder μ) := by
  haveI : IsFiniteMeasure (endpointRemainder μ) := by
    refine ⟨?_⟩
    rw [endpointRemainder_mass μ]
    exact ENNReal.ofReal_lt_top
  exact integrable_of_ae_mem_compact_of_continuousOn
    (endpointRemainder μ) (Icc xPlus 1)
    (fun t : ℝ => |xPlus - t|)
    hrem_support
    isCompact_Icc
    ((continuousOn_const.sub continuousOn_id).abs)

/-- `log |x - t|` is continuous on any set separated from `x`. -/
private lemma logAbsKernel_continuousOn_of_dist_ge
    {x ε : ℝ} {K : Set ℝ} (hε : 0 < ε)
    (hK : K ⊆ {t : ℝ | ε ≤ |x - t|}) :
    ContinuousOn (fun t : ℝ => Real.log |x - t|) K := by
  apply ContinuousOn.log
  · exact (continuousOn_const.sub continuousOn_id).abs
  · intro t ht
    have hdist : ε ≤ |x - t| := hK ht
    exact ne_of_gt (lt_of_lt_of_le hε hdist)

/--
If a fixed point is a.e. separated from the real unit-interval measure, then
the boundary logarithmic kernel is integrable.
-/
private theorem realMeasure_logAbs_integrable_of_dist_ge
    (μ : ProbabilityMeasure UnitInterval1038) {x ε : ℝ}
    (hε : 0 < ε)
    (hdist_lower : ∀ᵐ t : ℝ ∂realMeasure μ, ε ≤ |x - t|) :
    Integrable (fun t : ℝ => Real.log |x - t|) (realMeasure μ) := by
  haveI : IsFiniteMeasure (realMeasure μ) := inferInstance
  let K : Set ℝ := Icc (-1 : ℝ) 1 ∩ {t : ℝ | ε ≤ |x - t|}
  have hmemK : ∀ᵐ t : ℝ ∂realMeasure μ, t ∈ K := by
    filter_upwards [realMeasure_ae_mem_unitInterval μ, hdist_lower] with t htI hdist
    exact ⟨htI, hdist⟩
  have hclosed_sep : IsClosed ({t : ℝ | ε ≤ |x - t|} : Set ℝ) := by
    exact isClosed_Ici.preimage ((continuous_const.sub continuous_id).abs)
  have hcompact : IsCompact K := isCompact_Icc.inter_right hclosed_sep
  have hcont :
      ContinuousOn (fun t : ℝ => Real.log |x - t|) K := by
    exact logAbsKernel_continuousOn_of_dist_ge hε (by
      intro t ht
      exact ht.2)
  exact integrable_of_ae_mem_compact_of_continuousOn
    (realMeasure μ) K (fun t : ℝ => Real.log |x - t|)
    hmemK hcompact hcont

/-! ### Boundary-average constructors with automatic integrability -/

/--
Boundary-average constructor from nonpositive boundary potential, deriving all
distance/log integrability inputs from the standard compact support and the
separation hypothesis.
-/
theorem boundary_average_of_boundary_potential_nonpos_auto_integrable
    (μ : ProbabilityMeasure UnitInterval1038) {xPlus ε : ℝ}
    (hxPlus_nonneg : 0 ≤ xPlus)
    (hrem_support :
      ∀ᵐ t : ℝ ∂endpointRemainder μ, t ∈ Icc xPlus 1)
    (hpotential_nonpos : unitIntervalLogPotential μ xPlus ≤ 0)
    (hε : 0 < ε)
    (hdist_lower :
      ∀ᵐ t : ℝ ∂realMeasure μ, ε ≤ |xPlus - t|) :
    1 ≤
      (xPlus + 1) * ((realMeasure μ) (({-1} : Set ℝ))).toReal +
        (1 - xPlus) *
          (1 - ((realMeasure μ) (({-1} : Set ℝ))).toReal) := by
  exact boundary_average_of_boundary_potential_nonpos μ hxPlus_nonneg
    hrem_support hpotential_nonpos hε hdist_lower
    (realMeasure_distance_integrable μ xPlus)
    (realMeasure_logAbs_integrable_of_dist_ge μ hε hdist_lower)
    (endpointRemainder_distance_integrable_of_ae_mem_Icc μ hrem_support)

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
Boundary-average constructor from component-order data and right-endpoint
topology.

This is the narrow bridge needed by the canonical endpoint package: it derives
only the algebraic `boundary_average` field, leaving construction of the full
package to `of_unitIntervalLogPotential`.
-/
theorem boundary_average_of_component_right_endpoint_not_positive
    (μ : ProbabilityMeasure UnitInterval1038)
    (component : Set ℝ)
    (Support : Set ℝ)
    (xMinus xPlus ε : ℝ)
    (component_interval : component = Ioo xMinus xPlus)
    (baseline_inside_component : Ioo (-1 : ℝ) 0 ⊆ component)
    (support_bounded : Support ⊆ Icc (-1 : ℝ) 1)
    (unique_support_in_component :
      ∀ t : ℝ, t ∈ Support → t ∈ component → t = -1)
    (right_endpoint_positive : 0 < xPlus)
    (right_endpoint_not_positive :
      xPlus ∉ PositiveSet (unitIntervalLogPotential μ))
    (support_contains_real_support :
      (realMeasure μ).support ⊆ Support)
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
          (1 - ((realMeasure μ) (({-1} : Set ℝ))).toReal) :=
  boundary_average_of_right_endpoint_not_positive μ
    (le_of_lt right_endpoint_positive)
    (endpointRemainder_ae_mem_Icc_xPlus_one_of_support_order μ
      support_contains_real_support support_bounded
      (by
        intro y hy
        have hycomp : y ∈ component := baseline_inside_component hy
        simpa [component_interval] using hycomp)
      (by
        intro t htSupport htComp
        exact unique_support_in_component t htSupport
          (by simpa [component_interval] using htComp)))
    right_endpoint_not_positive hε hdist_lower hdist_int hlog_int
    hrem_dist_int

/--
Boundary-average constructor from local endpoint continuity and one-sided
maximality.

This is the form consumed by the future maximal-component argument: endpoint
separation supplies `ContinuousAt`, maximality supplies no strictly-right
positive points, and the theorem above supplies the algebraic boundary average.
-/
theorem boundary_average_of_component_continuousAt_no_right_positive
    (μ : ProbabilityMeasure UnitInterval1038)
    (component : Set ℝ)
    (Support : Set ℝ)
    (xMinus xPlus ε : ℝ)
    (component_interval : component = Ioo xMinus xPlus)
    (baseline_inside_component : Ioo (-1 : ℝ) 0 ⊆ component)
    (support_bounded : Support ⊆ Icc (-1 : ℝ) 1)
    (unique_support_in_component :
      ∀ t : ℝ, t ∈ Support → t ∈ component → t = -1)
    (right_endpoint_positive : 0 < xPlus)
    (hcont : ContinuousAt (unitIntervalLogPotential μ) xPlus)
    (hNoRight :
      ∀ y : ℝ, xPlus < y →
        y ∉ PositiveSet (unitIntervalLogPotential μ))
    (support_contains_real_support :
      (realMeasure μ).support ⊆ Support)
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
          (1 - ((realMeasure μ) (({-1} : Set ℝ))).toReal) :=
  boundary_average_of_component_right_endpoint_not_positive μ
    component Support xMinus xPlus ε component_interval
    baseline_inside_component support_bounded unique_support_in_component
    right_endpoint_positive
    (not_mem_positiveSet_of_continuousAt_no_right_points hcont hNoRight)
    support_contains_real_support hε hdist_lower hdist_int hlog_int
    hrem_dist_int

/--
Boundary-average constructor from local endpoint continuity and right-side
component coverage.

This replaces the raw `no-right-positive` input by the coverage statement that
every positive point to the right of `xMinus` belongs to the selected component
interval.  That is the maximal-component property needed in the Tao reduction.
-/
theorem boundary_average_of_component_right_cover
    (μ : ProbabilityMeasure UnitInterval1038)
    (component : Set ℝ)
    (Support : Set ℝ)
    (xMinus xPlus ε : ℝ)
    (component_interval : component = Ioo xMinus xPlus)
    (baseline_inside_component : Ioo (-1 : ℝ) 0 ⊆ component)
    (support_bounded : Support ⊆ Icc (-1 : ℝ) 1)
    (unique_support_in_component :
      ∀ t : ℝ, t ∈ Support → t ∈ component → t = -1)
    (right_endpoint_positive : 0 < xPlus)
    (hcont : ContinuousAt (unitIntervalLogPotential μ) xPlus)
    (hcover :
      ∀ y : ℝ, xMinus < y →
        y ∈ PositiveSet (unitIntervalLogPotential μ) →
          y ∈ Ioo xMinus xPlus)
    (support_contains_real_support :
      (realMeasure μ).support ⊆ Support)
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
          (1 - ((realMeasure μ) (({-1} : Set ℝ))).toReal) :=
  boundary_average_of_component_continuousAt_no_right_positive μ
    component Support xMinus xPlus ε component_interval
    baseline_inside_component support_bounded unique_support_in_component
    right_endpoint_positive hcont
    (no_right_positive_of_component_right_cover
      (by
        have hbase : (-1 / 2 : ℝ) ∈ Ioo (-1 : ℝ) 0 := by norm_num
        have hcomp : (-1 / 2 : ℝ) ∈ component :=
          baseline_inside_component hbase
        have hIoo : (-1 / 2 : ℝ) ∈ Ioo xMinus xPlus := by
          simpa [component_interval] using hcomp
        exact lt_trans hIoo.1 hIoo.2)
      hcover)
    support_contains_real_support hε hdist_lower hdist_int hlog_int
    hrem_dist_int

/--
Right-cover component bridge with the standard distance/log integrability
obligations discharged automatically.
-/
theorem boundary_average_of_component_right_cover_auto_integrable
    (μ : ProbabilityMeasure UnitInterval1038)
    (component : Set ℝ)
    (Support : Set ℝ)
    (xMinus xPlus ε : ℝ)
    (component_interval : component = Ioo xMinus xPlus)
    (baseline_inside_component : Ioo (-1 : ℝ) 0 ⊆ component)
    (support_bounded : Support ⊆ Icc (-1 : ℝ) 1)
    (unique_support_in_component :
      ∀ t : ℝ, t ∈ Support → t ∈ component → t = -1)
    (right_endpoint_positive : 0 < xPlus)
    (hcont : ContinuousAt (unitIntervalLogPotential μ) xPlus)
    (hcover :
      ∀ y : ℝ, xMinus < y →
        y ∈ PositiveSet (unitIntervalLogPotential μ) →
          y ∈ Ioo xMinus xPlus)
    (support_contains_real_support :
      (realMeasure μ).support ⊆ Support)
    (hε : 0 < ε)
    (hdist_lower :
      ∀ᵐ t : ℝ ∂realMeasure μ, ε ≤ |xPlus - t|) :
    1 ≤
      (xPlus + 1) * ((realMeasure μ) (({-1} : Set ℝ))).toReal +
        (1 - xPlus) *
          (1 - ((realMeasure μ) (({-1} : Set ℝ))).toReal) := by
  exact boundary_average_of_component_right_cover μ component Support
    xMinus xPlus ε component_interval baseline_inside_component support_bounded
    unique_support_in_component right_endpoint_positive hcont hcover
    support_contains_real_support hε hdist_lower
    (realMeasure_distance_integrable μ xPlus)
    (realMeasure_logAbs_integrable_of_dist_ge μ hε hdist_lower)
    (endpointRemainder_distance_integrable_of_ae_mem_Icc μ
      (endpointRemainder_ae_mem_Icc_xPlus_one_of_component_order μ
        component Support xMinus xPlus component_interval
        baseline_inside_component support_bounded unique_support_in_component
        support_contains_real_support))

/--
Right-region component bridge with the standard distance/log integrability
obligations discharged automatically.

Compared with the right-cover bridge, this version does not require endpoint
continuity: the right-region identity itself proves that `xPlus` is not in the
positive set.
-/
private theorem boundary_average_of_component_right_region_auto_integrable
    (μ : ProbabilityMeasure UnitInterval1038)
    (component : Set ℝ)
    (Support : Set ℝ)
    (xMinus xPlus ε : ℝ)
    (right_region_eq :
      component = PositiveSet (unitIntervalLogPotential μ) ∩ Ioi xMinus)
    (component_interval : component = Ioo xMinus xPlus)
    (baseline_inside_component : Ioo (-1 : ℝ) 0 ⊆ component)
    (support_bounded : Support ⊆ Icc (-1 : ℝ) 1)
    (unique_support_in_component :
      ∀ t : ℝ, t ∈ Support → t ∈ component → t = -1)
    (right_endpoint_positive : 0 < xPlus)
    (support_contains_real_support :
      (realMeasure μ).support ⊆ Support)
    (hε : 0 < ε)
    (hdist_lower :
      ∀ᵐ t : ℝ ∂realMeasure μ, ε ≤ |xPlus - t|) :
    1 ≤
      (xPlus + 1) * ((realMeasure μ) (({-1} : Set ℝ))).toReal +
        (1 - xPlus) *
          (1 - ((realMeasure μ) (({-1} : Set ℝ))).toReal) := by
  have hxMinus_lt_xPlus : xMinus < xPlus := by
    have hbase : (-1 / 2 : ℝ) ∈ Ioo (-1 : ℝ) 0 := by norm_num
    have hcomp : (-1 / 2 : ℝ) ∈ component :=
      baseline_inside_component hbase
    have hIoo : (-1 / 2 : ℝ) ∈ Ioo xMinus xPlus := by
      simpa [component_interval] using hcomp
    exact lt_trans hIoo.1 hIoo.2
  exact boundary_average_of_right_endpoint_not_positive μ
    (le_of_lt right_endpoint_positive)
    (endpointRemainder_ae_mem_Icc_xPlus_one_of_component_order μ
      component Support xMinus xPlus component_interval
      baseline_inside_component support_bounded unique_support_in_component
      support_contains_real_support)
    (not_mem_positiveSet_of_component_eq_positiveSet_inter_Ioi
      hxMinus_lt_xPlus right_region_eq component_interval)
    hε hdist_lower
    (realMeasure_distance_integrable μ xPlus)
    (realMeasure_logAbs_integrable_of_dist_ge μ hε hdist_lower)
    (endpointRemainder_distance_integrable_of_ae_mem_Icc μ
      (endpointRemainder_ae_mem_Icc_xPlus_one_of_component_order μ
        component Support xMinus xPlus component_interval
        baseline_inside_component support_bounded unique_support_in_component
        support_contains_real_support))

/--
Canonical unit-potential package from the right-cover maximal-component
interface.

This is the first endpoint-package constructor on the actual main path that
does not ask callers to separately provide the boundary-average integrability
bookkeeping.  The remaining analytic hypotheses are the genuine ones:
continuity at the right endpoint, maximal-component right coverage, and
a positive a.e. separation from the boundary point.
-/
def CanonicalEndpointVariationPackageData.of_unitIntervalLogPotential_right_cover
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
    (hcont : ContinuousAt (unitIntervalLogPotential μ) xPlus)
    (hcover :
      ∀ y : ℝ, xMinus < y →
        y ∈ PositiveSet (unitIntervalLogPotential μ) →
          y ∈ Ioo xMinus xPlus)
    (support_contains_real_support :
      (realMeasure μ).support ⊆ Support)
    (hε : 0 < ε)
    (hdist_lower :
      ∀ᵐ t : ℝ ∂realMeasure μ, ε ≤ |xPlus - t|) :
    CanonicalEndpointVariationPackageData μ (unitIntervalLogPotential μ) := by
  have hboundary :
      1 ≤
        (xPlus + 1) * ((realMeasure μ) (({-1} : Set ℝ))).toReal +
          (1 - xPlus) *
            (1 - ((realMeasure μ) (({-1} : Set ℝ))).toReal) :=
    boundary_average_of_component_right_cover_auto_integrable μ
      component Support xMinus xPlus ε component_interval
      baseline_inside_component support_bounded unique_support_in_component
      right_endpoint_positive hcont hcover support_contains_real_support
      hε hdist_lower
  have hsupport_norm :
      (realMeasure μ).support ⊆ ({-1} : Set ℝ) ∪ Icc (0 : ℝ) 1 :=
    realMeasure_support_subset_normalized_of_component_order μ
      component Support xMinus xPlus component_interval
      baseline_inside_component support_bounded unique_support_in_component
      support_contains_real_support
  exact CanonicalEndpointVariationPackageData.of_unitIntervalLogPotential μ
    mean_choice reflected translation component Support xMinus xPlus
    component_positive component_interval baseline_inside_component
    support_bounded unique_support_in_component right_endpoint_positive
    hboundary support_contains_real_support
    (endpointRemainder_kernel_integrable_of_normalized_support μ hsupport_norm)

/--
Canonical unit-potential package from a right-region component equality.

This is the preferred maximal-component-facing constructor.  Instead of asking
separately for component positivity and right-cover, it consumes the sharper
statement that the selected component is exactly the positive set to the right
of `xMinus`.
-/
def CanonicalEndpointVariationPackageData.of_unitIntervalLogPotential_right_region
    (μ : ProbabilityMeasure UnitInterval1038)
    (mean_choice : TaoVariationMeanChoice)
    (reflected : Bool)
    (translation : ℝ)
    (component : Set ℝ)
    (Support : Set ℝ)
    (xMinus xPlus : ℝ)
    (right_region_eq :
      component = PositiveSet (unitIntervalLogPotential μ) ∩ Ioi xMinus)
    (component_interval : component = Ioo xMinus xPlus)
    (baseline_inside_component : Ioo (-1 : ℝ) 0 ⊆ component)
    (support_bounded : Support ⊆ Icc (-1 : ℝ) 1)
    (unique_support_in_component :
      ∀ t : ℝ, t ∈ Support → t ∈ component → t = -1)
    (right_endpoint_positive : 0 < xPlus)
    (support_contains_real_support :
      (realMeasure μ).support ⊆ Support)
    (right_endpoint_not_mem_support :
      xPlus ∉ (realMeasure μ).support) :
    CanonicalEndpointVariationPackageData μ (unitIntervalLogPotential μ) := by
  let hsep : ∃ ε : ℝ, 0 < ε ∧
      ∀ᵐ t : ℝ ∂realMeasure μ, ε ≤ |xPlus - t| :=
    exists_ae_dist_ge_of_not_mem_realMeasure_support μ
      right_endpoint_not_mem_support
  let ε : ℝ := Classical.choose hsep
  have hε : 0 < ε := (Classical.choose_spec hsep).1
  have hdist_lower : ∀ᵐ t : ℝ ∂realMeasure μ, ε ≤ |xPlus - t| :=
    (Classical.choose_spec hsep).2
  have hboundary :
      1 ≤
        (xPlus + 1) * ((realMeasure μ) (({-1} : Set ℝ))).toReal +
          (1 - xPlus) *
            (1 - ((realMeasure μ) (({-1} : Set ℝ))).toReal) :=
    boundary_average_of_component_right_region_auto_integrable μ
      component Support xMinus xPlus ε right_region_eq component_interval
      baseline_inside_component support_bounded unique_support_in_component
      right_endpoint_positive support_contains_real_support hε hdist_lower
  have hsupport_norm :
      (realMeasure μ).support ⊆ ({-1} : Set ℝ) ∪ Icc (0 : ℝ) 1 :=
    realMeasure_support_subset_normalized_of_component_order μ
      component Support xMinus xPlus component_interval
      baseline_inside_component support_bounded unique_support_in_component
      support_contains_real_support
  exact CanonicalEndpointVariationPackageData.of_unitIntervalLogPotential μ
    mean_choice reflected translation component Support xMinus xPlus
    (component_positive_of_component_eq_positiveSet_inter_Ioi right_region_eq)
    component_interval baseline_inside_component support_bounded
    unique_support_in_component right_endpoint_positive hboundary
    support_contains_real_support
    (endpointRemainder_kernel_integrable_of_normalized_support μ hsupport_norm)

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
Right-region form of the canonical variation data for one relaxed minimizer.

This is the concrete maximal-component-facing data consumed by
`of_unitIntervalLogPotential_right_region`.
-/
structure CanonicalRightRegionPackageData
    (M : MinimizerExistence.RelaxedMinimizer) where
  mean_choice : TaoVariationMeanChoice
  reflected : Bool
  translation : ℝ
  component : Set ℝ
  Support : Set ℝ
  xMinus : ℝ
  xPlus : ℝ
  right_region_eq :
    component = PositiveSet (VariationEndpoint.RelaxedPotential M) ∩ Ioi xMinus
  component_interval : component = Ioo xMinus xPlus
  baseline_inside_component : Ioo (-1 : ℝ) 0 ⊆ component
  support_bounded : Support ⊆ Icc (-1 : ℝ) 1
  unique_support_in_component :
    ∀ t : ℝ, t ∈ Support → t ∈ component → t = -1
  right_endpoint_positive : 0 < xPlus
  support_contains_real_support :
    (realMeasure M.μ).support ⊆ Support
  right_endpoint_not_mem_support :
    xPlus ∉ (realMeasure M.μ).support

/-- Right-region data produces the canonical endpoint package. -/
def CanonicalRightRegionPackageData.toCanonicalEndpointVariationPackageData
    {M : MinimizerExistence.RelaxedMinimizer}
    (D : CanonicalRightRegionPackageData M) :
    CanonicalEndpointVariationPackageData M.μ
      (VariationEndpoint.RelaxedPotential M) :=
  CanonicalEndpointVariationPackageData.of_unitIntervalLogPotential_right_region
    M.μ D.mean_choice D.reflected D.translation D.component D.Support
    D.xMinus D.xPlus D.right_region_eq D.component_interval
    D.baseline_inside_component D.support_bounded
    D.unique_support_in_component D.right_endpoint_positive
    D.support_contains_real_support D.right_endpoint_not_mem_support

/--
Right-region variation input for every relaxed minimizer.  This is narrower
than `CanonicalComponentPackageFromVariation`: it asks for the maximal
right-region data, then constructs the canonical package internally.
-/
structure CanonicalRightRegionPackageFromVariation where
  right_region_data : ∀ M : MinimizerExistence.RelaxedMinimizer,
    CanonicalRightRegionPackageData M

/-- Right-region variation data supplies canonical component packages. -/
def CanonicalRightRegionPackageFromVariation.toCanonicalComponentPackageFromVariation
    (H : CanonicalRightRegionPackageFromVariation) :
    CanonicalComponentPackageFromVariation where
  canonicalPackage := fun M =>
    (H.right_region_data M).toCanonicalEndpointVariationPackageData

/--
Atomized right-region data for one relaxed minimizer.

Compared with `CanonicalRightRegionPackageData`, this no longer asks for
`unique_support_in_component` directly.  Instead it asks for the component-block
atomization conclusion and the endpoint barycenter normalization, then derives
support uniqueness internally.
-/
structure CanonicalAtomizedRightRegionPackageData
    (M : MinimizerExistence.RelaxedMinimizer) where
  mean_choice : TaoVariationMeanChoice
  reflected : Bool
  translation : ℝ
  component : PositiveComponent M.μ
  right_region_eq :
    component.interval =
      PositiveSet (VariationEndpoint.RelaxedPotential M) ∩ Ioi component.left
  baseline_inside_component : Ioo (-1 : ℝ) 0 ⊆ component.interval
  real_support_bounded : (realMeasure M.μ).support ⊆ Icc (-1 : ℝ) 1
  component_block_atomized :
    componentBlock component =
      componentMass component • Measure.dirac (componentBarycenter component)
  barycenter_eq_endpoint : componentBarycenter component = -1
  right_endpoint_positive : 0 < component.right
  right_endpoint_not_mem_support :
    component.right ∉ (realMeasure M.μ).support

/-- Atomized right-region data produces ordinary right-region data. -/
def CanonicalAtomizedRightRegionPackageData.toCanonicalRightRegionPackageData
    {M : MinimizerExistence.RelaxedMinimizer}
    (D : CanonicalAtomizedRightRegionPackageData M) :
    CanonicalRightRegionPackageData M where
  mean_choice := D.mean_choice
  reflected := D.reflected
  translation := D.translation
  component := D.component.interval
  Support := (realMeasure M.μ).support
  xMinus := D.component.left
  xPlus := D.component.right
  right_region_eq := D.right_region_eq
  component_interval := PositiveComponent.interval_eq D.component
  baseline_inside_component := D.baseline_inside_component
  support_bounded := D.real_support_bounded
  unique_support_in_component :=
    unique_support_in_component_endpoint_of_componentBlock_eq_dirac
      D.component (fun _ ht => ht) D.component_block_atomized
      D.barycenter_eq_endpoint
  right_endpoint_positive := D.right_endpoint_positive
  support_contains_real_support := fun _ ht => ht
  right_endpoint_not_mem_support := D.right_endpoint_not_mem_support

/--
Build atomized right-region data from component-block atomization plus the
endpoint-mass/nondegenerate-left-endpoint inputs.  This is the direct
constructor for the current normalized route: callers no longer provide
`componentBarycenter = -1` itself.
-/
def CanonicalAtomizedRightRegionPackageData.of_endpoint_mass_left_ne
    {M : MinimizerExistence.RelaxedMinimizer}
    (mean_choice : TaoVariationMeanChoice)
    (reflected : Bool)
    (translation : ℝ)
    (component : PositiveComponent M.μ)
    (right_region_eq :
      component.interval =
        PositiveSet (VariationEndpoint.RelaxedPotential M) ∩ Ioi component.left)
    (baseline_inside_component : Ioo (-1 : ℝ) 0 ⊆ component.interval)
    (real_support_bounded : (realMeasure M.μ).support ⊆ Icc (-1 : ℝ) 1)
    (component_block_atomized :
      componentBlock component =
        componentMass component • Measure.dirac (componentBarycenter component))
    (endpoint_mass_pos : 0 < (realMeasure M.μ) ({-1} : Set ℝ))
    (left_endpoint_ne : component.left ≠ (-1 : ℝ))
    (right_endpoint_positive : 0 < component.right)
    (right_endpoint_not_mem_support :
      component.right ∉ (realMeasure M.μ).support) :
    CanonicalAtomizedRightRegionPackageData M where
  mean_choice := mean_choice
  reflected := reflected
  translation := translation
  component := component
  right_region_eq := right_region_eq
  baseline_inside_component := baseline_inside_component
  real_support_bounded := real_support_bounded
  component_block_atomized := component_block_atomized
  barycenter_eq_endpoint :=
    componentBarycenter_eq_endpoint_of_componentBlock_eq_dirac_of_endpoint_mass_pos_left_ne
      component component_block_atomized endpoint_mass_pos
      baseline_inside_component left_endpoint_ne
  right_endpoint_positive := right_endpoint_positive
  right_endpoint_not_mem_support := right_endpoint_not_mem_support

/--
Canonical component-package variation data directly gives the normalized
endpoint-potential interface for each relaxed minimizer.
-/
def normalizedEndpointPotential_from_canonical_componentPackage
    (H : CanonicalComponentPackageFromVariation)
    (M : MinimizerExistence.RelaxedMinimizer) :
    NormalizedEndpointPotential (VariationEndpoint.RelaxedPotential M) :=
  (H.canonicalPackage M).toTaoReducedPotentialData
    |>.toNormalizedEndpointPotential

/--
Canonical component-package variation data gives the baseline positive-set
inclusion for each relaxed minimizer.
-/
theorem baseline_subset_positive_from_canonical_componentPackage
    (H : CanonicalComponentPackageFromVariation)
    (M : MinimizerExistence.RelaxedMinimizer) :
    BaselinePunctured ⊆ PositiveSet (VariationEndpoint.RelaxedPotential M) :=
  (H.canonicalPackage M).toTaoReducedPotentialData
    |>.baseline_subset_positive

/--
Canonical component-package variation data gives the baseline positive-set
length lower bound for each relaxed minimizer.
-/
theorem baseline_length_from_canonical_componentPackage
    (H : CanonicalComponentPackageFromVariation)
    (M : MinimizerExistence.RelaxedMinimizer) :
    ENNReal.ofReal (Real.sqrt 2) ≤
      volume (PositiveSet (VariationEndpoint.RelaxedPotential M)) :=
  (H.canonicalPackage M).toTaoReducedPotentialData
    |>.baseline_length_le_positiveSet

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
Diagonal-safe minimizer plus the normalized endpoint-potential interface,
using the canonical component-package provider directly.
-/
theorem exists_relaxed_minimizer_with_normalizedEndpointPotential_from_canonical
    (Hcore : LowerSemicontinuity.OneSidedCompactCore)
    (Hvar : CanonicalComponentPackageFromVariation) :
    Nonempty (Σ M : MinimizerExistence.RelaxedMinimizer,
      NormalizedEndpointPotential (VariationEndpoint.RelaxedPotential M)) := by
  rcases MinimizerExistence.exists_relaxed_minimizer_of_oneSidedCompactCore
      Hcore with ⟨M⟩
  exact ⟨⟨M, normalizedEndpointPotential_from_canonical_componentPackage Hvar M⟩⟩

/--
Canonical variation packages imply the baseline interval length consequence.
-/
theorem exists_baseline_length_from_canonical_componentPackage
    (Hcore : LowerSemicontinuity.OneSidedCompactCore)
    (Hvar : CanonicalComponentPackageFromVariation) :
    ∃ M : MinimizerExistence.RelaxedMinimizer,
      ENNReal.ofReal (Real.sqrt 2) ≤
        volume (PositiveSet (VariationEndpoint.RelaxedPotential M)) :=
  by
    rcases MinimizerExistence.exists_relaxed_minimizer_of_oneSidedCompactCore
        Hcore with ⟨M⟩
    exact ⟨M, baseline_length_from_canonical_componentPackage Hvar M⟩

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

/-! ### Atomized right-region constructors from rigidity data -/

/--
Build atomized right-region data from countable-support-hit normalized
rigidity.  This discharges the `component_block_atomized` field through the
existing secondary-minimizer rigidity theorem.
-/
def CanonicalAtomizedRightRegionPackageData.of_countable_rigidity
    {α : Type*} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {a b : α}
    {M : MinimizerExistence.RelaxedMinimizer}
    (D : CountableSupportHitNormalizedBlockRigidityData P a b M.μ)
    (mean_choice : TaoVariationMeanChoice)
    (reflected : Bool)
    (translation : ℝ)
    (right_region_eq :
      D.replacement.component.interval =
        PositiveSet (VariationEndpoint.RelaxedPotential M) ∩
          Ioi D.replacement.component.left)
    (baseline_inside_component :
      Ioo (-1 : ℝ) 0 ⊆ D.replacement.component.interval)
    (real_support_bounded : (realMeasure M.μ).support ⊆ Icc (-1 : ℝ) 1)
    (barycenter_eq_endpoint :
      componentBarycenter D.replacement.component = -1)
    (right_endpoint_positive : 0 < D.replacement.component.right)
    (right_endpoint_not_mem_support :
      D.replacement.component.right ∉ (realMeasure M.μ).support) :
    CanonicalAtomizedRightRegionPackageData M where
  mean_choice := mean_choice
  reflected := reflected
  translation := translation
  component := D.replacement.component
  right_region_eq := right_region_eq
  baseline_inside_component := baseline_inside_component
  real_support_bounded := real_support_bounded
  component_block_atomized := D.componentBlock_eq_dirac
  barycenter_eq_endpoint := barycenter_eq_endpoint
  right_endpoint_positive := right_endpoint_positive
  right_endpoint_not_mem_support := right_endpoint_not_mem_support

/--
Endpoint-mass/endpoint-order variant of the countable-rigidity constructor.
It removes the direct `componentBarycenter = -1` input by deriving it from
component-block atomization, positive mass at the normalized endpoint, baseline
containment, and the strict left-endpoint order.
-/
def CanonicalAtomizedRightRegionPackageData.of_countable_rigidity_endpoint_mass_left_lt
    {α : Type*} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {a b : α}
    {M : MinimizerExistence.RelaxedMinimizer}
    (D : CountableSupportHitNormalizedBlockRigidityData P a b M.μ)
    (mean_choice : TaoVariationMeanChoice)
    (reflected : Bool)
    (translation : ℝ)
    (right_region_eq :
      D.replacement.component.interval =
        PositiveSet (VariationEndpoint.RelaxedPotential M) ∩
          Ioi D.replacement.component.left)
    (baseline_inside_component :
      Ioo (-1 : ℝ) 0 ⊆ D.replacement.component.interval)
    (real_support_bounded : (realMeasure M.μ).support ⊆ Icc (-1 : ℝ) 1)
    (endpoint_mass_pos : 0 < (realMeasure M.μ) ({-1} : Set ℝ))
    (left_endpoint_lt : D.replacement.component.left < (-1 : ℝ))
    (right_endpoint_positive : 0 < D.replacement.component.right)
    (right_endpoint_not_mem_support :
      D.replacement.component.right ∉ (realMeasure M.μ).support) :
    CanonicalAtomizedRightRegionPackageData M :=
  CanonicalAtomizedRightRegionPackageData.of_countable_rigidity
    D mean_choice reflected translation right_region_eq
    baseline_inside_component real_support_bounded
    (componentBarycenter_eq_endpoint_of_componentBlock_eq_dirac_of_endpoint_mass_pos_left_lt
      D.replacement.component D.componentBlock_eq_dirac endpoint_mass_pos
      baseline_inside_component left_endpoint_lt)
    right_endpoint_positive right_endpoint_not_mem_support

/--
Nondegenerate-left-endpoint variant of the countable-rigidity constructor.
It replaces the strict left-endpoint order input by `component.left ≠ -1`;
baseline containment supplies the weak order, so equality exclusion is enough.
-/
def CanonicalAtomizedRightRegionPackageData.of_countable_rigidity_endpoint_mass_left_ne
    {α : Type*} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {a b : α}
    {M : MinimizerExistence.RelaxedMinimizer}
    (D : CountableSupportHitNormalizedBlockRigidityData P a b M.μ)
    (mean_choice : TaoVariationMeanChoice)
    (reflected : Bool)
    (translation : ℝ)
    (right_region_eq :
      D.replacement.component.interval =
        PositiveSet (VariationEndpoint.RelaxedPotential M) ∩
          Ioi D.replacement.component.left)
    (baseline_inside_component :
      Ioo (-1 : ℝ) 0 ⊆ D.replacement.component.interval)
    (real_support_bounded : (realMeasure M.μ).support ⊆ Icc (-1 : ℝ) 1)
    (endpoint_mass_pos : 0 < (realMeasure M.μ) ({-1} : Set ℝ))
    (left_endpoint_ne : D.replacement.component.left ≠ (-1 : ℝ))
    (right_endpoint_positive : 0 < D.replacement.component.right)
    (right_endpoint_not_mem_support :
      D.replacement.component.right ∉ (realMeasure M.μ).support) :
    CanonicalAtomizedRightRegionPackageData M :=
  CanonicalAtomizedRightRegionPackageData.of_endpoint_mass_left_ne
    mean_choice reflected translation D.replacement.component right_region_eq
    baseline_inside_component real_support_bounded D.componentBlock_eq_dirac
    endpoint_mass_pos left_endpoint_ne right_endpoint_positive
    right_endpoint_not_mem_support

end
end ComponentAtomization
end StandardReduction
end Erdos1038
