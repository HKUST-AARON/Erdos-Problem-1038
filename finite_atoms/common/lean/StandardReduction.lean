import Mathlib.Tactic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Normalized-support consequence used in the standard reduction

This file formalizes the elementary analytic consequence of the standard
normalization used in the finite-atom route.  If the reduced potential has at
least half of the mass at `-1`, and the remaining support lies to the right in
`[0,1]`, then the interval `(-sqrt 2, 0)` is forced into the positive set,
up to the atom point `-1` where a real-valued logarithmic potential would be
infinite rather than a finite `Real.log` value.

The theorem here does not prove the external variational statement that every
minimizer can be normalized in this way.  It proves the part of that reduction
which is actually used by the finite-atom certificate once the normalized
support/mass lower bound is available.
-/

namespace Erdos1038
namespace StandardReduction

noncomputable section

open Set
open MeasureTheory
open scoped ENNReal BigOperators

/-- Positive set of a real-valued potential. -/
def PositiveSet (U : ℝ → ℝ) : Set ℝ := {x : ℝ | 0 < U x}

/-- The baseline interval forced by the normalized endpoint mass. -/
def BaselineInterval : Set ℝ := Ioo (-(Real.sqrt 2)) 0

/-- The real-valued formalization removes the atom point where the potential is infinite. -/
def BaselinePunctured : Set ℝ := BaselineInterval \ ({-1} : Set ℝ)

/-- Endpoint lower bound coming from mass `p` at `-1` and the rest bounded below by evaluation at `1`. -/
def endpointMassLowerBound (p x : ℝ) : ℝ :=
  p * Real.log (1 / |x + 1|) + (1 - p) * Real.log (1 / |x - 1|)

/-- Abstract reduced-potential interface supplied by the normalized support/mass condition. -/
def HasNormalizedEndpointLowerBound (U : ℝ → ℝ) (p : ℝ) : Prop :=
  ∀ x : ℝ, x ∈ BaselinePunctured → endpointMassLowerBound p x ≤ U x

lemma sq_lt_two_of_mem_baseline {x : ℝ} (hx : x ∈ BaselineInterval) :
    x ^ 2 < 2 := by
  rcases hx with ⟨hxlo, hxhi⟩
  have hxabs : |x| < Real.sqrt 2 := by
    rw [abs_of_neg hxhi]
    linarith
  have hxabs' : |(|x|)| < |Real.sqrt 2| := by
    rwa [abs_of_nonneg (abs_nonneg x), abs_of_nonneg (Real.sqrt_nonneg 2)]
  have hsq : |x| ^ 2 < (Real.sqrt 2) ^ 2 := by
    exact sq_lt_sq.mpr hxabs'
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
    rw [Real.sq_sqrt]
    norm_num
  rwa [sq_abs, hsqrt] at hsq

lemma abs_sq_sub_one_lt_one_of_mem_baseline {x : ℝ}
    (hx : x ∈ BaselineInterval) :
    |x ^ 2 - 1| < 1 := by
  rcases hx with ⟨hxlo, hxhi⟩
  have hx2lt : x ^ 2 < 2 := sq_lt_two_of_mem_baseline ⟨hxlo, hxhi⟩
  have hxne0 : x ≠ 0 := by linarith
  have hx2pos : 0 < x ^ 2 := sq_pos_of_ne_zero hxne0
  rw [abs_lt]
  constructor <;> linarith

lemma half_log_inverse_abs_sq_sub_one_pos {x : ℝ}
    (hx : x ∈ BaselineInterval) (hne : x ≠ -1) :
    0 < (1 / 2 : ℝ) * Real.log (1 / |x ^ 2 - 1|) := by
  rcases hx with ⟨hxlo, hxhi⟩
  have habslt : |x ^ 2 - 1| < 1 :=
    abs_sq_sub_one_lt_one_of_mem_baseline ⟨hxlo, hxhi⟩
  have hsqne : x ^ 2 - 1 ≠ 0 := by
    intro hzero
    have hs : x ^ 2 = 1 := by linarith
    have hxpm : x = 1 ∨ x = -1 := by
      exact sq_eq_one_iff.mp hs
    rcases hxpm with hxone | hxminus
    · linarith
    · exact hne hxminus
  have habspos : 0 < |x ^ 2 - 1| := abs_pos.mpr hsqne
  have hloginv : 0 < Real.log (1 / |x ^ 2 - 1|) := by
    have hgt : 1 < 1 / |x ^ 2 - 1| := by
      rw [lt_div_iff₀ habspos]
      linarith
    exact Real.log_pos hgt
  nlinarith

lemma endpoint_log_order {x : ℝ} (hx : x < 0) (hne : x ≠ -1) :
    Real.log (1 / |x - 1|) ≤ Real.log (1 / |x + 1|) := by
  have hx1ne : x + 1 ≠ 0 := by
    intro h
    apply hne
    linarith
  have hx2ne : x - 1 ≠ 0 := by linarith
  have hposL : 0 < 1 / |x - 1| := one_div_pos.mpr (abs_pos.mpr hx2ne)
  have hle_abs : |x + 1| ≤ |x - 1| := by
    rw [← sq_le_sq]
    nlinarith
  have hle_inv : 1 / |x - 1| ≤ 1 / |x + 1| := by
    exact one_div_le_one_div_of_le (abs_pos.mpr hx1ne) hle_abs
  exact Real.log_le_log hposL hle_inv

lemma normalized_support_logKernel_lower_bound {x t : ℝ}
    (hx : x < 0) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.log (1 / |x - 1|) ≤ Real.log (1 / |x - t|) := by
  have hx1ne : x - 1 ≠ 0 := by linarith
  have hxtne : x - t ≠ 0 := by linarith
  have hposL : 0 < 1 / |x - 1| := one_div_pos.mpr (abs_pos.mpr hx1ne)
  have hle_abs : |x - t| ≤ |x - 1| := by
    have hxt_nonpos : x - t ≤ 0 := by linarith
    have hx1_nonpos : x - 1 ≤ 0 := by linarith
    rw [abs_of_nonpos hxt_nonpos, abs_of_nonpos hx1_nonpos]
    linarith
  have hle_inv : 1 / |x - 1| ≤ 1 / |x - t| := by
    exact one_div_le_one_div_of_le (abs_pos.mpr hxtne) hle_abs
  exact Real.log_le_log hposL hle_inv

lemma normalized_support_integral_lower_bound
    (ν : Measure ℝ) {x mass : ℝ}
    (hx : x < 0)
    (hsupp : ∀ᵐ t ∂ν, 0 ≤ t ∧ t ≤ 1)
    (hmass : ν Set.univ = ENNReal.ofReal mass)
    (hmass_nonneg : 0 ≤ mass)
    (hkernel_int : Integrable (fun t : ℝ => Real.log (1 / |x - t|)) ν) :
    mass * Real.log (1 / |x - 1|) ≤
      ∫ t : ℝ, Real.log (1 / |x - t|) ∂ν := by
  haveI : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [hmass]
    exact ENNReal.ofReal_lt_top
  have hlower_ae :
      (fun _ : ℝ => Real.log (1 / |x - 1|)) ≤ᵐ[ν]
        fun t : ℝ => Real.log (1 / |x - t|) := by
    filter_upwards [hsupp] with t ht
    exact normalized_support_logKernel_lower_bound hx ht.1 ht.2
  have hconst_int : Integrable (fun _ : ℝ => Real.log (1 / |x - 1|)) ν := by
    exact integrable_const (Real.log (1 / |x - 1|))
  have hle :
      (∫ _ : ℝ, Real.log (1 / |x - 1|) ∂ν) ≤
        ∫ t : ℝ, Real.log (1 / |x - t|) ∂ν :=
    integral_mono_ae hconst_int hkernel_int hlower_ae
  have hconst :
      (∫ _ : ℝ, Real.log (1 / |x - 1|) ∂ν) =
        (ν Set.univ).toReal * Real.log (1 / |x - 1|) := by
    rw [integral_const]
    simp [Measure.real, smul_eq_mul]
  rw [hconst, hmass] at hle
  simpa [ENNReal.toReal_ofReal hmass_nonneg] using hle

lemma endpoint_plus_normalized_remainder_lower_bound {U : ℝ → ℝ} {p : ℝ}
    (hU : ∀ x : ℝ, x ∈ BaselinePunctured →
      p * Real.log (1 / |x + 1|) +
        (1 - p) * Real.log (1 / |x - 1|) ≤ U x) :
    HasNormalizedEndpointLowerBound U p := by
  intro x hx
  exact hU x hx

/--
The endpoint lower-bound interface follows from an actual normalized support
decomposition: a mass `p` at `-1`, a remainder measure of mass `1-p` supported
on `[0,1]`, and a potential `U` bounded below by the sum of the endpoint
kernel and the remainder potential.
-/
theorem endpoint_lower_bound_from_normalized_remainder_measure
    {U : ℝ → ℝ} {ν : Measure ℝ} {p : ℝ}
    (hrem_supp : ∀ᵐ t ∂ν, 0 ≤ t ∧ t ≤ 1)
    (hrem_mass : ν Set.univ = ENNReal.ofReal (1 - p))
    (hrem_mass_nonneg : 0 ≤ 1 - p)
    (hkernel_int : ∀ x : ℝ, x ∈ BaselinePunctured →
      Integrable (fun t : ℝ => Real.log (1 / |x - t|)) ν)
    (hU_decomp : ∀ x : ℝ, x ∈ BaselinePunctured →
      p * Real.log (1 / |x + 1|) +
        (∫ t : ℝ, Real.log (1 / |x - t|) ∂ν) ≤ U x) :
    HasNormalizedEndpointLowerBound U p := by
  refine endpoint_plus_normalized_remainder_lower_bound ?_
  intro x hx
  have hxneg : x < 0 := hx.1.2
  have hrem_lower :
      (1 - p) * Real.log (1 / |x - 1|) ≤
        ∫ t : ℝ, Real.log (1 / |x - t|) ∂ν :=
    normalized_support_integral_lower_bound ν hxneg hrem_supp
      hrem_mass hrem_mass_nonneg (hkernel_int x hx)
  have hdecomp := hU_decomp x hx
  nlinarith

lemma half_endpoint_average_eq_half_product {x : ℝ}
    (hx : x ∈ BaselineInterval) (hne : x ≠ -1) :
    (1 / 2 : ℝ) * Real.log (1 / |x + 1|) +
      (1 / 2 : ℝ) * Real.log (1 / |x - 1|) =
    (1 / 2 : ℝ) * Real.log (1 / |x ^ 2 - 1|) := by
  rcases hx with ⟨_, hxhi⟩
  have hx1ne : x + 1 ≠ 0 := by
    intro h
    apply hne
    linarith
  have hx2ne : x - 1 ≠ 0 := by linarith
  have hpos1 : 0 < 1 / |x + 1| := one_div_pos.mpr (abs_pos.mpr hx1ne)
  have hpos2 : 0 < 1 / |x - 1| := one_div_pos.mpr (abs_pos.mpr hx2ne)
  have hmul : (1 / |x + 1|) * (1 / |x - 1|) = 1 / |x ^ 2 - 1| := by
    have habs : |x + 1| * |x - 1| = |x ^ 2 - 1| := by
      rw [← abs_mul]
      congr 1
      ring
    rw [← habs]
    field_simp [abs_pos.mpr hx1ne, abs_pos.mpr hx2ne]
  have hlogsum : Real.log (1 / |x + 1|) + Real.log (1 / |x - 1|) =
      Real.log (1 / |x ^ 2 - 1|) := by
    rw [← Real.log_mul hpos1.ne' hpos2.ne']
    rw [hmul]
  linarith

lemma half_endpoint_average_pos {x : ℝ}
    (hx : x ∈ BaselineInterval) (hne : x ≠ -1) :
    0 < (1 / 2 : ℝ) * Real.log (1 / |x + 1|) +
      (1 / 2 : ℝ) * Real.log (1 / |x - 1|) := by
  rw [half_endpoint_average_eq_half_product hx hne]
  exact half_log_inverse_abs_sq_sub_one_pos hx hne

lemma half_endpoint_average_le_endpointMassLowerBound {p x : ℝ}
    (hp : (1 / 2 : ℝ) ≤ p)
    (hx : x ∈ BaselineInterval) (hne : x ≠ -1) :
    (1 / 2 : ℝ) * Real.log (1 / |x + 1|) +
      (1 / 2 : ℝ) * Real.log (1 / |x - 1|) ≤ endpointMassLowerBound p x := by
  rcases hx with ⟨_, hxhi⟩
  have hBA : Real.log (1 / |x - 1|) ≤ Real.log (1 / |x + 1|) :=
    endpoint_log_order hxhi hne
  have hnonneg : 0 ≤
      (p - (1 / 2 : ℝ)) *
        (Real.log (1 / |x + 1|) - Real.log (1 / |x - 1|)) := by
    exact mul_nonneg (by linarith) (by linarith)
  unfold endpointMassLowerBound
  nlinarith

lemma endpointMassLowerBound_pos {p x : ℝ}
    (hp : (1 / 2 : ℝ) ≤ p)
    (hx : x ∈ BaselineInterval) (hne : x ≠ -1) :
    0 < endpointMassLowerBound p x := by
  have hpos := half_endpoint_average_pos hx hne
  have hle := half_endpoint_average_le_endpointMassLowerBound hp hx hne
  exact lt_of_lt_of_le hpos hle

/-- The normalized endpoint lower bound forces the punctured baseline interval into the positive set. -/
theorem normalized_endpoint_lower_bound_positive_set
    {U : ℝ → ℝ} {p : ℝ}
    (hp : (1 / 2 : ℝ) ≤ p)
    (hU : HasNormalizedEndpointLowerBound U p) :
    BaselinePunctured ⊆ PositiveSet U := by
  intro x hx
  rcases hx with ⟨hxBase, hxNotAtom⟩
  have hne : x ≠ -1 := by
    intro h
    exact hxNotAtom (by simp [h])
  have hposLower : 0 < endpointMassLowerBound p x :=
    endpointMassLowerBound_pos hp hxBase hne
  have hleU : endpointMassLowerBound p x ≤ U x := hU x ⟨hxBase, hxNotAtom⟩
  exact lt_of_lt_of_le hposLower hleU

/-- Same consequence written pointwise for downstream finite-atom route files. -/
theorem normalized_endpoint_lower_bound_pointwise_positive
    {U : ℝ → ℝ} {p x : ℝ}
    (hp : (1 / 2 : ℝ) ≤ p)
    (hU : HasNormalizedEndpointLowerBound U p)
    (hx : x ∈ BaselineInterval) (hne : x ≠ -1) :
    0 < U x := by
  exact normalized_endpoint_lower_bound_positive_set hp hU ⟨hx, by simpa using hne⟩

/--
Packed normalized endpoint consequence.  This is the precise formal object
needed by the finite-atom lower-bound route after the external variational
normalization has put a minimizer into endpoint-mass form.
-/
structure NormalizedEndpointPotential (U : ℝ → ℝ) where
  p : ℝ
  halfMass : (1 / 2 : ℝ) ≤ p
  endpointLowerBound : HasNormalizedEndpointLowerBound U p

theorem NormalizedEndpointPotential.baseline_subset_positive
    {U : ℝ → ℝ} (h : NormalizedEndpointPotential U) :
    BaselinePunctured ⊆ PositiveSet U := by
  exact normalized_endpoint_lower_bound_positive_set h.halfMass h.endpointLowerBound

theorem NormalizedEndpointPotential.pointwise_positive
    {U : ℝ → ℝ} (h : NormalizedEndpointPotential U)
    {x : ℝ} (hx : x ∈ BaselineInterval) (hne : x ≠ -1) :
    0 < U x := by
  exact normalized_endpoint_lower_bound_pointwise_positive h.halfMass
    h.endpointLowerBound hx hne

theorem baselineInterval_volume :
    volume BaselineInterval = ENNReal.ofReal (Real.sqrt 2) := by
  simp [BaselineInterval, Real.volume_Ioo]

theorem baselinePunctured_volume :
    volume BaselinePunctured = ENNReal.ofReal (Real.sqrt 2) := by
  have hnull : volume ({-1} : Set ℝ) = 0 := by simp
  rw [BaselinePunctured, measure_diff_null hnull]
  simp [baselineInterval_volume]

/--
Length form of the normalized endpoint consequence.  If the positive set is
measurable, the baseline interval contributes `sqrt 2` of Lebesgue length.
-/
theorem NormalizedEndpointPotential.baseline_length_le_positiveSet
    {U : ℝ → ℝ}
    (h : NormalizedEndpointPotential U) :
    ENNReal.ofReal (Real.sqrt 2) ≤ volume (PositiveSet U) := by
  rw [← baselinePunctured_volume]
  exact measure_mono (μ := volume) h.baseline_subset_positive

/--
Abstract statement of the remaining external variational theorem: a minimizer
can be normalized so that its potential satisfies `NormalizedEndpointPotential`.

This structure records the remaining external variational input. Downstream Lean files
can state exactly where the Tao variational reduction is used.
-/
structure StandardMinimizerReduction
    (Config : Type) (IsMinimizer : Config → Prop) (Potential : Config → ℝ → ℝ) where
  normalize :
    ∀ c : Config, IsMinimizer c → NormalizedEndpointPotential (Potential c)

theorem standard_minimizer_reduction_baseline_length
    {Config : Type} {IsMinimizer : Config → Prop} {Potential : Config → ℝ → ℝ}
    (hReduction : StandardMinimizerReduction Config IsMinimizer Potential)
    {c : Config} (hc : IsMinimizer c) :
    ENNReal.ofReal (Real.sqrt 2) ≤ volume (PositiveSet (Potential c)) := by
  exact (hReduction.normalize c hc).baseline_length_le_positiveSet

/--
Explicit normalization-map form of the variational reduction.

`Config` is the original minimizer configuration type, `Normalized` is the
normalized configuration type, and `normalize` is the reflection/translation
normalization map.  The mathematical content is the field `endpointForm`: after
normalization, every minimizer has the endpoint-mass lower-bound form needed by
the finite-atom route.
-/
structure VariationalNormalizationTheorem
    (Config Normalized : Type)
    (IsMinimizer : Config → Prop)
    (normalize : Config → Normalized)
    (Potential : Normalized → ℝ → ℝ) where
  endpointForm :
    ∀ c : Config, IsMinimizer c →
      NormalizedEndpointPotential (Potential (normalize c))

/--
The explicit normalization theorem gives the abstract standard-reduction
interface used by the finite-atom route.
-/
def variational_normalization_implies_standard_reduction
    {Config Normalized : Type}
    {IsMinimizer : Config → Prop}
    {normalize : Config → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (h : VariationalNormalizationTheorem Config Normalized IsMinimizer
      normalize Potential) :
    StandardMinimizerReduction Config IsMinimizer
      (fun c : Config => Potential (normalize c)) where
  normalize := h.endpointForm

/--
Compiled endpoint consequence of the variational normalization theorem:
after normalization, every minimizer has at least the baseline `sqrt 2`
positive-set contribution.
-/
theorem variational_normalization_baseline_length
    {Config Normalized : Type}
    {IsMinimizer : Config → Prop}
    {normalize : Config → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (h : VariationalNormalizationTheorem Config Normalized IsMinimizer
      normalize Potential)
    {c : Config} (hc : IsMinimizer c) :
    ENNReal.ofReal (Real.sqrt 2) ≤
      volume (PositiveSet (Potential (normalize c))) := by
  exact (h.endpointForm c hc).baseline_length_le_positiveSet

/-! ## Order and algebra pieces from the Tao component reduction -/

/--
The algebraic endpoint-mass step in Tao's reduction.  If the right endpoint
`x` of the component is positive and the boundary-distance estimate gives

`1 ≤ (x + 1) p + (1 - x) (1 - p)`,

then the endpoint mass satisfies `p ≥ 1/2`.
-/
lemma endpoint_mass_ge_half_from_boundary_average {x p : ℝ}
    (hx : 0 < x)
    (havg : 1 ≤ (x + 1) * p + (1 - x) * (1 - p)) :
    (1 / 2 : ℝ) ≤ p := by
  nlinarith

/--
The order-theoretic support conclusion from the component reduction.  If the
normalized support is contained in `[-1,1]`, the positive component contains
`(-1,0)`, and the only support point inside that component is the endpoint atom
`-1`, then the support is contained in `{-1} ∪ [0,1]`.
-/
lemma support_subset_endpoint_union_nonnegative
    {Support : Set ℝ} {xMinus xPlus : ℝ}
    (hBounded : Support ⊆ Icc (-1 : ℝ) 1)
    (hInterval : Ioo (-1 : ℝ) 0 ⊆ Ioo xMinus xPlus)
    (hUniqueInComponent : ∀ t : ℝ, t ∈ Support → t ∈ Ioo xMinus xPlus → t = -1) :
    Support ⊆ ({-1} : Set ℝ) ∪ Icc (0 : ℝ) 1 := by
  intro t ht
  have htBound := hBounded ht
  by_cases htneg : t < 0
  · have htle : -1 ≤ t := by simpa using htBound.1
    by_cases htm : t = -1
    · exact Or.inl (by simp [htm])
    · have hgt : -1 < t := lt_of_le_of_ne htle (Ne.symm htm)
      have htBase : t ∈ Ioo (-1 : ℝ) 0 := ⟨hgt, htneg⟩
      have htComp : t ∈ Ioo xMinus xPlus := hInterval htBase
      have : t = -1 := hUniqueInComponent t ht htComp
      exact False.elim (htm this)
  · have ht0 : 0 ≤ t := le_of_not_gt htneg
    exact Or.inr ⟨ht0, htBound.2⟩

/--
Data extracted from the component step of Tao's minimizer reduction after
reflection and translation have selected the component containing `(-1,0)`.
This is still an interface for the variational part, but the two conclusions
below are now proved from its order and algebra fields.
-/
structure TaoComponentReductionData where
  Support : Set ℝ
  endpointMass : ℝ
  xMinus : ℝ
  xPlus : ℝ
  support_bounded : Support ⊆ Icc (-1 : ℝ) 1
  baseline_inside_component : Ioo (-1 : ℝ) 0 ⊆ Ioo xMinus xPlus
  unique_support_in_component :
    ∀ t : ℝ, t ∈ Support → t ∈ Ioo xMinus xPlus → t = -1
  right_endpoint_positive : 0 < xPlus
  boundary_average :
    1 ≤ (xPlus + 1) * endpointMass + (1 - xPlus) * (1 - endpointMass)

theorem TaoComponentReductionData.support_subset_normalized
    (D : TaoComponentReductionData) :
    D.Support ⊆ ({-1} : Set ℝ) ∪ Icc (0 : ℝ) 1 :=
  support_subset_endpoint_union_nonnegative D.support_bounded
    D.baseline_inside_component D.unique_support_in_component

theorem TaoComponentReductionData.endpointMass_ge_half
    (D : TaoComponentReductionData) :
    (1 / 2 : ℝ) ≤ D.endpointMass :=
  endpoint_mass_ge_half_from_boundary_average D.right_endpoint_positive
    D.boundary_average

/--
Concrete endpoint-normalization data before packaging as
`TaoReducedPotentialData`: Tao's order/component reduction plus an actual
remainder measure supported on `[0,1]` whose decomposition gives the potential
lower bound.
-/
structure TaoEndpointNormalizationData (U : ℝ → ℝ)
    extends TaoComponentReductionData where
  remainder : Measure ℝ
  remainder_support : ∀ᵐ t ∂remainder, 0 ≤ t ∧ t ≤ 1
  remainder_mass : remainder Set.univ = ENNReal.ofReal (1 - endpointMass)
  remainder_mass_nonneg : 0 ≤ 1 - endpointMass
  kernel_integrable : ∀ x : ℝ, x ∈ BaselinePunctured →
    Integrable (fun t : ℝ => Real.log (1 / |x - t|)) remainder
  potential_decomposition_lower : ∀ x : ℝ, x ∈ BaselinePunctured →
    endpointMass * Real.log (1 / |x + 1|) +
      (∫ t : ℝ, Real.log (1 / |x - t|) ∂remainder) ≤ U x

/--
Bridge from Tao's component-reduction data to the normalized endpoint-potential
interface used by the finite-atom route.  The field `endpointLowerBound` is the
analytic support-to-potential lower bound obtained from the normalized support
configuration.
-/
structure TaoReducedPotentialData (U : ℝ → ℝ) extends TaoComponentReductionData where
  endpointLowerBound : HasNormalizedEndpointLowerBound U endpointMass

/-- Build `TaoReducedPotentialData` from concrete endpoint-normalization data. -/
def TaoEndpointNormalizationData.toTaoReducedPotentialData
    {U : ℝ → ℝ} (D : TaoEndpointNormalizationData U) :
    TaoReducedPotentialData U where
  toTaoComponentReductionData := D.toTaoComponentReductionData
  endpointLowerBound :=
    endpoint_lower_bound_from_normalized_remainder_measure
      D.remainder_support D.remainder_mass D.remainder_mass_nonneg
      D.kernel_integrable D.potential_decomposition_lower

def TaoEndpointNormalizationData.toNormalizedEndpointPotential
    {U : ℝ → ℝ} (D : TaoEndpointNormalizationData U) :
    NormalizedEndpointPotential U where
  p := D.endpointMass
  halfMass := D.toTaoComponentReductionData.endpointMass_ge_half
  endpointLowerBound := D.toTaoReducedPotentialData.endpointLowerBound

theorem TaoEndpointNormalizationData.baseline_subset_positive
    {U : ℝ → ℝ} (D : TaoEndpointNormalizationData U) :
    BaselinePunctured ⊆ PositiveSet U :=
  D.toNormalizedEndpointPotential.baseline_subset_positive

theorem TaoEndpointNormalizationData.baseline_length_le_positiveSet
    {U : ℝ → ℝ} (D : TaoEndpointNormalizationData U) :
    ENNReal.ofReal (Real.sqrt 2) ≤ volume (PositiveSet U) :=
  D.toNormalizedEndpointPotential.baseline_length_le_positiveSet

def TaoReducedPotentialData.toNormalizedEndpointPotential
    {U : ℝ → ℝ} (D : TaoReducedPotentialData U) :
    NormalizedEndpointPotential U where
  p := D.endpointMass
  halfMass := D.toTaoComponentReductionData.endpointMass_ge_half
  endpointLowerBound := D.endpointLowerBound

theorem TaoReducedPotentialData.baseline_subset_positive
    {U : ℝ → ℝ} (D : TaoReducedPotentialData U) :
    BaselinePunctured ⊆ PositiveSet U :=
  D.toNormalizedEndpointPotential.baseline_subset_positive

theorem TaoReducedPotentialData.baseline_length_le_positiveSet
    {U : ℝ → ℝ} (D : TaoReducedPotentialData U) :
    ENNReal.ofReal (Real.sqrt 2) ≤ volume (PositiveSet U) :=
  D.toNormalizedEndpointPotential.baseline_length_le_positiveSet

/--
The component package already proves the normalized support conclusion for the
non-endpoint remainder measure.  Remaining inputs are deliberately explicit:
the supplied remainder measure must be a.e. supported on the selected component
support after reflection/translation, and it must exclude the endpoint atom
`-1`.  Under those two assumptions its support is a.e. contained in `[0,1]`.
-/
theorem TaoComponentReductionData.remainder_support_normalized_of_ae_support
    (D : TaoComponentReductionData) {ν : Measure ℝ}
    (hν_support : ∀ᵐ t ∂ν, t ∈ D.Support)
    (hν_no_endpoint : ∀ᵐ t ∂ν, t ≠ -1) :
    ∀ᵐ t ∂ν, 0 ≤ t ∧ t ≤ 1 := by
  filter_upwards [hν_support, hν_no_endpoint] with t htSupport htNoEndpoint
  have htNorm : t ∈ ({-1} : Set ℝ) ∪ Icc (0 : ℝ) 1 :=
    D.support_subset_normalized htSupport
  rcases htNorm with htEndpoint | htUnit
  · have htEq : t = -1 := by
      simpa using htEndpoint
    exact False.elim (htNoEndpoint htEq)
  · exact htUnit

/--
Package component-normalization data plus an endpoint lower-bound proof as
`TaoReducedPotentialData`.

Remaining inputs: the caller must still supply the endpoint lower-bound theorem
for the reflected/translated potential.  The component data itself supplies the
endpoint half-mass inequality, so downstream users no longer assemble the
`TaoReducedPotentialData` fields manually.
-/
def TaoComponentReductionData.toTaoReducedPotentialData_of_endpoint_lower_bound
    {U : ℝ → ℝ} (D : TaoComponentReductionData)
    (hEndpointLowerBound : HasNormalizedEndpointLowerBound U D.endpointMass) :
    TaoReducedPotentialData U where
  toTaoComponentReductionData := D
  endpointLowerBound := hEndpointLowerBound

/--
Package component-normalization data plus an endpoint lower-bound proof directly
as `NormalizedEndpointPotential`.

Remaining inputs: the caller must still supply the endpoint lower-bound theorem
for the reflected/translated potential.  The component package supplies the
endpoint mass `p` and the proof `1/2 ≤ p`.
-/
def TaoComponentReductionData.toNormalizedEndpointPotential_of_endpoint_lower_bound
    {U : ℝ → ℝ} (D : TaoComponentReductionData)
    (hEndpointLowerBound : HasNormalizedEndpointLowerBound U D.endpointMass) :
    NormalizedEndpointPotential U :=
  (D.toTaoReducedPotentialData_of_endpoint_lower_bound
    hEndpointLowerBound).toNormalizedEndpointPotential

/--
Build the full endpoint-normalization package from component data and an already
normalized remainder decomposition.

Remaining inputs: the caller must still provide the reflected/translated
remainder measure, its `[0,1]` a.e. support, its mass `1 - endpointMass`,
nonnegativity of that mass, kernel integrability on `BaselinePunctured`, and the
endpoint-plus-remainder lower bound for the potential.  The component fields are
copied automatically.
-/
def TaoComponentReductionData.toTaoEndpointNormalizationData_of_normalized_remainder
    {U : ℝ → ℝ} (D : TaoComponentReductionData)
    (remainder : Measure ℝ)
    (hrem_support : ∀ᵐ t ∂remainder, 0 ≤ t ∧ t ≤ 1)
    (hrem_mass : remainder Set.univ = ENNReal.ofReal (1 - D.endpointMass))
    (hrem_mass_nonneg : 0 ≤ 1 - D.endpointMass)
    (hkernel_int : ∀ x : ℝ, x ∈ BaselinePunctured →
      Integrable (fun t : ℝ => Real.log (1 / |x - t|)) remainder)
    (hU_decomp : ∀ x : ℝ, x ∈ BaselinePunctured →
      D.endpointMass * Real.log (1 / |x + 1|) +
        (∫ t : ℝ, Real.log (1 / |x - t|) ∂remainder) ≤ U x) :
    TaoEndpointNormalizationData U where
  toTaoComponentReductionData := D
  remainder := remainder
  remainder_support := hrem_support
  remainder_mass := hrem_mass
  remainder_mass_nonneg := hrem_mass_nonneg
  kernel_integrable := hkernel_int
  potential_decomposition_lower := hU_decomp

/--
Build the full endpoint-normalization package from component data and a
remainder decomposition whose support is stated relative to the selected
component support.

Remaining inputs: after reflection/translation, the caller must still provide
the remainder measure, a.e. support in `D.Support`, a.e. exclusion of the
endpoint atom `-1`, mass `1 - endpointMass`, nonnegativity of that mass, kernel
integrability on `BaselinePunctured`, and the endpoint-plus-remainder lower
bound.  This theorem eliminates the separate manual proof that the remainder is
a.e. supported on `[0,1]`.
-/
def TaoComponentReductionData.toTaoEndpointNormalizationData_of_remainder_ae_support
    {U : ℝ → ℝ} (D : TaoComponentReductionData)
    (remainder : Measure ℝ)
    (hrem_support_in_component : ∀ᵐ t ∂remainder, t ∈ D.Support)
    (hrem_no_endpoint : ∀ᵐ t ∂remainder, t ≠ -1)
    (hrem_mass : remainder Set.univ = ENNReal.ofReal (1 - D.endpointMass))
    (hrem_mass_nonneg : 0 ≤ 1 - D.endpointMass)
    (hkernel_int : ∀ x : ℝ, x ∈ BaselinePunctured →
      Integrable (fun t : ℝ => Real.log (1 / |x - t|)) remainder)
    (hU_decomp : ∀ x : ℝ, x ∈ BaselinePunctured →
      D.endpointMass * Real.log (1 / |x + 1|) +
        (∫ t : ℝ, Real.log (1 / |x - t|) ∂remainder) ≤ U x) :
    TaoEndpointNormalizationData U :=
  D.toTaoEndpointNormalizationData_of_normalized_remainder remainder
    (D.remainder_support_normalized_of_ae_support
      hrem_support_in_component hrem_no_endpoint)
    hrem_mass hrem_mass_nonneg hkernel_int hU_decomp

/--
Direct reduced-potential package from component data and a remainder
decomposition stated relative to the selected component support.

Remaining inputs: after reflection/translation, the caller must still supply
the remainder measure, a.e. component-support evidence, a.e. endpoint exclusion,
mass/nonnegativity, kernel integrability, and the endpoint-plus-remainder lower
bound.  The support normalization and endpoint-lower-bound packaging are now
performed by this bridge.
-/
def TaoComponentReductionData.toTaoReducedPotentialData_of_remainder_ae_support
    {U : ℝ → ℝ} (D : TaoComponentReductionData)
    (remainder : Measure ℝ)
    (hrem_support_in_component : ∀ᵐ t ∂remainder, t ∈ D.Support)
    (hrem_no_endpoint : ∀ᵐ t ∂remainder, t ≠ -1)
    (hrem_mass : remainder Set.univ = ENNReal.ofReal (1 - D.endpointMass))
    (hrem_mass_nonneg : 0 ≤ 1 - D.endpointMass)
    (hkernel_int : ∀ x : ℝ, x ∈ BaselinePunctured →
      Integrable (fun t : ℝ => Real.log (1 / |x - t|)) remainder)
    (hU_decomp : ∀ x : ℝ, x ∈ BaselinePunctured →
      D.endpointMass * Real.log (1 / |x + 1|) +
        (∫ t : ℝ, Real.log (1 / |x - t|) ∂remainder) ≤ U x) :
    TaoReducedPotentialData U :=
  (D.toTaoEndpointNormalizationData_of_remainder_ae_support remainder
    hrem_support_in_component hrem_no_endpoint hrem_mass hrem_mass_nonneg
    hkernel_int hU_decomp).toTaoReducedPotentialData

/-! ## Concrete variation package feeding endpoint normalization -/

/--
Bookkeeping for the sign/reflection choice in Tao's variation argument.

`nonnegativeMean` means the chosen normalization uses the nonnegative-mean side
directly.  `reflectedNonpositiveMean` means the nonpositive-mean side has been
reflected before the component package below is stated.  This type carries no
mathematical assertion by itself; it records which branch supplied the
component data.
-/
inductive TaoVariationMeanChoice where
  | nonnegativeMean
  | reflectedNonpositiveMean

/--
Concrete component-and-remainder package extracted from Tao's variation
argument after the sign/reflection/translation choice has already been made.

Remaining variation inputs deliberately kept explicit:
* the mean-side/reflection/translation choice recorded by `mean_choice`,
  `reflected`, and `translation`;
* existence of a positive component `component` containing the baseline
  interval `(-1,0)`;
* identification of that component with the endpoint interval
  `Ioo xMinus xPlus`;
* the component atom/Dirac conclusion that every support point in the component
  is the endpoint atom `-1`;
* global support boundedness/order inside `[-1,1]`;
* the boundary-average estimate producing endpoint mass at least `1/2`;
* construction of the remainder measure, its support in the selected support,
  exclusion of the endpoint atom, mass, integrability, and the
  endpoint-plus-remainder lower bound for the normalized potential.

This structure does not assert that an arbitrary minimizer can be translated,
reflected, or decomposed this way; those are exactly the upstream variation
inputs recorded as fields.
-/
structure TaoVariationComponentPackage (U : ℝ → ℝ) where
  mean_choice : TaoVariationMeanChoice
  reflected : Bool
  translation : ℝ
  component : Set ℝ
  Support : Set ℝ
  endpointMass : ℝ
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
    1 ≤ (xPlus + 1) * endpointMass + (1 - xPlus) * (1 - endpointMass)
  remainder : Measure ℝ
  remainder_support_in_support : ∀ᵐ t ∂remainder, t ∈ Support
  remainder_no_endpoint : ∀ᵐ t ∂remainder, t ≠ -1
  remainder_mass : remainder Set.univ = ENNReal.ofReal (1 - endpointMass)
  remainder_mass_nonneg : 0 ≤ 1 - endpointMass
  kernel_integrable : ∀ x : ℝ, x ∈ BaselinePunctured →
    Integrable (fun t : ℝ => Real.log (1 / |x - t|)) remainder
  potential_decomposition_lower : ∀ x : ℝ, x ∈ BaselinePunctured →
    endpointMass * Real.log (1 / |x + 1|) +
      (∫ t : ℝ, Real.log (1 / |x - t|) ∂remainder) ≤ U x

/--
Extract the already-formal `TaoComponentReductionData` from the concrete
variation package.

Remaining inputs are exactly the fields of `TaoVariationComponentPackage`:
component existence, reflection/translation choice, boundary average,
support/order, component atom conclusion, and remainder construction are not
proved here.  This theorem only normalizes their shape so downstream endpoint
packagers no longer manually assemble `TaoComponentReductionData`.
-/
def TaoVariationComponentPackage.toTaoComponentReductionData
    {U : ℝ → ℝ} (D : TaoVariationComponentPackage U) :
    TaoComponentReductionData where
  Support := D.Support
  endpointMass := D.endpointMass
  xMinus := D.xMinus
  xPlus := D.xPlus
  support_bounded := D.support_bounded
  baseline_inside_component := by
    intro x hx
    have hxComp : x ∈ D.component := D.baseline_inside_component hx
    simpa [D.component_interval] using hxComp
  unique_support_in_component := by
    intro t htSupport htInterval
    exact D.unique_support_in_component t htSupport
      (by simpa [D.component_interval] using htInterval)
  right_endpoint_positive := D.right_endpoint_positive
  boundary_average := D.boundary_average

/--
Build the endpoint-normalization package directly from concrete variation data.

This eliminates downstream manual assembly of the component fields and the
separate proof that the non-endpoint remainder is supported in `[0,1]`.
Remaining variation inputs are still explicit in
`TaoVariationComponentPackage`: component existence, reflection/translation
choice, component atom conclusion, support/order, boundary average, endpoint
exclusion for the remainder, mass/integrability, and the decomposition lower
bound.
-/
def TaoVariationComponentPackage.toTaoEndpointNormalizationData
    {U : ℝ → ℝ} (D : TaoVariationComponentPackage U) :
    TaoEndpointNormalizationData U :=
  D.toTaoComponentReductionData.toTaoEndpointNormalizationData_of_remainder_ae_support
    D.remainder D.remainder_support_in_support D.remainder_no_endpoint
    D.remainder_mass D.remainder_mass_nonneg D.kernel_integrable
    D.potential_decomposition_lower

/--
Build the reduced-potential package directly from concrete variation data.

The downstream endpoint lower bound is now produced through the component and
remainder packagers.  What remains upstream is not hidden: the concrete package
must still provide the sign/reflection/translation choice, a positive component
containing the baseline interval, the component atom/Dirac conclusion,
support/order data, boundary-average evidence, and the normalized remainder
construction.
-/
def TaoVariationComponentPackage.toTaoReducedPotentialData
    {U : ℝ → ℝ} (D : TaoVariationComponentPackage U) :
    TaoReducedPotentialData U :=
  D.toTaoEndpointNormalizationData.toTaoReducedPotentialData

/--
Concrete variation package as the normalized endpoint potential consumed by
the finite-atom route.

This is the intended replacement for a generic `hEndpointFromVariation`
provider when the variation argument has supplied the concrete component and
remainder fields.  It still does not claim extraction from every minimizer.
-/
def TaoVariationComponentPackage.toNormalizedEndpointPotential
    {U : ℝ → ℝ} (D : TaoVariationComponentPackage U) :
    NormalizedEndpointPotential U :=
  D.toTaoReducedPotentialData.toNormalizedEndpointPotential

theorem TaoVariationComponentPackage.baseline_subset_positive
    {U : ℝ → ℝ} (D : TaoVariationComponentPackage U) :
    BaselinePunctured ⊆ PositiveSet U :=
  D.toNormalizedEndpointPotential.baseline_subset_positive

theorem TaoVariationComponentPackage.baseline_length_le_positiveSet
    {U : ℝ → ℝ} (D : TaoVariationComponentPackage U) :
    ENNReal.ofReal (Real.sqrt 2) ≤ volume (PositiveSet U) :=
  D.toNormalizedEndpointPotential.baseline_length_le_positiveSet

/--
If the strict Lemma 3.2 positivity conclusion has already placed the whole
baseline interval inside a selected positive component, then the concrete
variation package supplies the baseline component field required by
`TaoComponentReductionData`.

Remaining inputs: this theorem does not prove the strict Lemma 3.2 analytic
positivity itself, nor component maximality.  It packages the resulting
baseline-in-component evidence once the variation argument has supplied the
positive component and the baseline inclusion.
-/
theorem baseline_positive_from_strict_variation_component
    {U : ℝ → ℝ} {component : Set ℝ}
    (hcomponent_positive : component ⊆ PositiveSet U)
    (hstrict_baseline : Ioo (-1 : ℝ) 0 ⊆ component) :
    Ioo (-1 : ℝ) 0 ⊆ PositiveSet U := by
  intro x hx
  exact hcomponent_positive (hstrict_baseline hx)

/-! ## Algebraic kernel behind Tao's Lemma 3.2 -/

/--
Pointwise kernel inequality used in Tao's proof of Lemma 3.2.  For
`0 ≤ x ≤ 1` and `-1 ≤ t ≤ 1`, one has

`|x - t| + x * t ≤ 1`.

After integration, this is the real-variable input behind the estimate that
the sign of the mean forces one of `(0,1)` or `(-1,0)` into the positive set.
-/
lemma abs_sub_add_mul_le_one {x t : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (htlo : -1 ≤ t) (hthi : t ≤ 1) :
    |x - t| + x * t ≤ 1 := by
  by_cases htx : t ≤ x
  · rw [abs_of_nonneg (sub_nonneg.mpr htx)]
    have hx1nonpos : x - 1 ≤ 0 := by linarith
    nlinarith
  · have hxt : x ≤ t := le_of_lt (lt_of_not_ge htx)
    rw [abs_of_nonpos (sub_nonpos.mpr hxt)]
    nlinarith

/--
Equality case in the pointwise kernel inequality.  In the open range
`0 < x < 1`, equality in `|x-t| + x*t ≤ 1` forces the support point to be an
endpoint, `t = -1` or `t = 1`.
-/
lemma abs_sub_add_mul_eq_one_imp_endpoint {x t : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1)
    (h : |x - t| + x * t = 1) :
    t = -1 ∨ t = 1 := by
  by_cases htx : t ≤ x
  · rw [abs_of_nonneg (sub_nonneg.mpr htx)] at h
    left
    have hpos : 0 < 1 - x := by linarith
    nlinarith
  · have hxt : x ≤ t := le_of_lt (lt_of_not_ge htx)
    rw [abs_of_nonpos (sub_nonpos.mpr hxt)] at h
    right
    have hpos : 0 < 1 + x := by linarith
    nlinarith

/-!
## Finite weighted form of the Lemma 3.2 kernel estimate

The measure-theoretic version in Tao's notes integrates the pointwise kernel
inequality against a probability measure.  The following lemmas formalize the
finite weighted version.  This is the exact algebraic layer needed before one
replaces finite sums by measure integrals.
-/

lemma finite_weighted_kernel_sum_le_one
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w t : ι → ℝ) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1)
    (ht_bound : ∀ i ∈ s, -1 ≤ t i ∧ t i ≤ 1) :
    ∑ i ∈ s, w i * (|x - t i| + x * t i) ≤ 1 := by
  calc
    ∑ i ∈ s, w i * (|x - t i| + x * t i)
        ≤ ∑ i ∈ s, w i * 1 := by
          exact Finset.sum_le_sum (fun i hi =>
            mul_le_mul_of_nonneg_left
              (abs_sub_add_mul_le_one hx0 hx1
                (ht_bound i hi).1 (ht_bound i hi).2)
              (hw_nonneg i hi))
    _ = 1 := by
      simp [hw_sum]

lemma finite_weighted_kernel_sum_split
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w t : ι → ℝ) {x : ℝ} :
    ∑ i ∈ s, w i * (|x - t i| + x * t i) =
      ∑ i ∈ s, w i * |x - t i| + x * ∑ i ∈ s, w i * t i := by
  calc
    ∑ i ∈ s, w i * (|x - t i| + x * t i)
        = ∑ i ∈ s, (w i * |x - t i| + x * (w i * t i)) := by
          apply Finset.sum_congr rfl
          intro i _hi
          ring_nf
    _ = ∑ i ∈ s, w i * |x - t i| +
        ∑ i ∈ s, x * (w i * t i) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ i ∈ s, w i * |x - t i| +
        x * ∑ i ∈ s, w i * t i := by
          rw [Finset.mul_sum]

lemma finite_weighted_abs_sum_le_one_of_nonnegative_mean
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w t : ι → ℝ) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1)
    (ht_bound : ∀ i ∈ s, -1 ≤ t i ∧ t i ≤ 1)
    (hmean_nonneg : 0 ≤ ∑ i ∈ s, w i * t i) :
    ∑ i ∈ s, w i * |x - t i| ≤ 1 := by
  have hkernel : ∑ i ∈ s, w i * (|x - t i| + x * t i) ≤ 1 :=
    finite_weighted_kernel_sum_le_one s w t hx0 hx1 hw_nonneg hw_sum ht_bound
  have hsplit := finite_weighted_kernel_sum_split s w t (x := x)
  rw [hsplit] at hkernel
  have hxmean : 0 ≤ x * ∑ i ∈ s, w i * t i :=
    mul_nonneg hx0 hmean_nonneg
  nlinarith

lemma finite_weighted_abs_sum_le_one_of_nonpositive_mean
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w t : ι → ℝ) {x : ℝ}
    (hx0 : -1 ≤ x) (hx1 : x ≤ 0)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1)
    (ht_bound : ∀ i ∈ s, -1 ≤ t i ∧ t i ≤ 1)
    (hmean_nonpos : ∑ i ∈ s, w i * t i ≤ 0) :
    ∑ i ∈ s, w i * |x - t i| ≤ 1 := by
  let t' : ι → ℝ := fun i => -t i
  have hx0' : 0 ≤ -x := by linarith
  have hx1' : -x ≤ 1 := by linarith
  have ht_bound' : ∀ i ∈ s, -1 ≤ t' i ∧ t' i ≤ 1 := by
    intro i hi
    have hti := ht_bound i hi
    constructor <;> simp [t'] <;> linarith
  have hmean_nonneg' : 0 ≤ ∑ i ∈ s, w i * t' i := by
    have hneg :
        ∑ i ∈ s, w i * t' i = -∑ i ∈ s, w i * t i := by
      calc
        ∑ i ∈ s, w i * t' i
            = ∑ i ∈ s, -(w i * t i) := by
              apply Finset.sum_congr rfl
              intro i _hi
              simp [t']
        _ = -∑ i ∈ s, w i * t i := by
          rw [Finset.sum_neg_distrib]
    rw [hneg]
    linarith
  have hpos :=
    finite_weighted_abs_sum_le_one_of_nonnegative_mean
      s w t' hx0' hx1' hw_nonneg hw_sum ht_bound' hmean_nonneg'
  have hsum_eq :
      ∑ i ∈ s, w i * |x - t i| = ∑ i ∈ s, w i * |-x - t' i| := by
    apply Finset.sum_congr rfl
    intro i _hi
    congr 1
    rw [show -x - t' i = t i - x by
      simp [t']
      ring]
    exact abs_sub_comm x (t i)
  rw [hsum_eq]
  exact hpos

/-! ## Finite Jensen/logarithmic-potential layer of Tao's Lemma 3.2 -/

lemma finite_weighted_log_abs_sum_le_log_abs_average
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w t : ι → ℝ) {x : ℝ}
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1)
    (hdist_pos : ∀ i ∈ s, 0 < |x - t i|) :
    ∑ i ∈ s, w i * Real.log |x - t i| ≤
      Real.log (∑ i ∈ s, w i * |x - t i|) := by
  have hj := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (t := s) (w := w) (p := fun i => |x - t i|)
    hw_nonneg hw_sum (fun i hi => hdist_pos i hi)
  simpa [smul_eq_mul] using hj

lemma finite_weighted_log_abs_sum_nonpos_of_abs_average_le_one
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w t : ι → ℝ) {x : ℝ}
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1)
    (hdist_pos : ∀ i ∈ s, 0 < |x - t i|)
    (havg_le_one : ∑ i ∈ s, w i * |x - t i| ≤ 1) :
    ∑ i ∈ s, w i * Real.log |x - t i| ≤ 0 := by
  have hj :=
    finite_weighted_log_abs_sum_le_log_abs_average s w t
      hw_nonneg hw_sum hdist_pos
  have havg_nonneg : 0 ≤ ∑ i ∈ s, w i * |x - t i| := by
    exact Finset.sum_nonneg (fun i hi =>
      mul_nonneg (hw_nonneg i hi) (le_of_lt (hdist_pos i hi)))
  have hlog_nonpos :
      Real.log (∑ i ∈ s, w i * |x - t i|) ≤ 0 :=
    Real.log_nonpos havg_nonneg havg_le_one
  exact le_trans hj hlog_nonpos

lemma finite_weighted_log_abs_sum_nonpos_of_nonnegative_mean
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w t : ι → ℝ) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1)
    (ht_bound : ∀ i ∈ s, -1 ≤ t i ∧ t i ≤ 1)
    (hmean_nonneg : 0 ≤ ∑ i ∈ s, w i * t i)
    (hdist_pos : ∀ i ∈ s, 0 < |x - t i|) :
    ∑ i ∈ s, w i * Real.log |x - t i| ≤ 0 := by
  have havg_le_one :=
    finite_weighted_abs_sum_le_one_of_nonnegative_mean
      s w t hx0 hx1 hw_nonneg hw_sum ht_bound hmean_nonneg
  exact finite_weighted_log_abs_sum_nonpos_of_abs_average_le_one
    s w t hw_nonneg hw_sum hdist_pos havg_le_one

lemma finite_weighted_log_abs_sum_nonpos_of_nonpositive_mean
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w t : ι → ℝ) {x : ℝ}
    (hx0 : -1 ≤ x) (hx1 : x ≤ 0)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1)
    (ht_bound : ∀ i ∈ s, -1 ≤ t i ∧ t i ≤ 1)
    (hmean_nonpos : ∑ i ∈ s, w i * t i ≤ 0)
    (hdist_pos : ∀ i ∈ s, 0 < |x - t i|) :
    ∑ i ∈ s, w i * Real.log |x - t i| ≤ 0 := by
  have havg_le_one :=
    finite_weighted_abs_sum_le_one_of_nonpositive_mean
      s w t hx0 hx1 hw_nonneg hw_sum ht_bound hmean_nonpos
  exact finite_weighted_log_abs_sum_nonpos_of_abs_average_le_one
    s w t hw_nonneg hw_sum hdist_pos havg_le_one

/-- Finite weighted logarithmic potential associated to weighted atoms. -/
def finiteWeightedPotential
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w t : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ s, w i * Real.log (1 / |x - t i|)

lemma finiteWeightedPotential_eq_neg_log_abs_sum
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w t : ι → ℝ) {x : ℝ}
    (hdist_pos : ∀ i ∈ s, 0 < |x - t i|) :
    finiteWeightedPotential s w t x =
      -∑ i ∈ s, w i * Real.log |x - t i| := by
  unfold finiteWeightedPotential
  calc
    ∑ i ∈ s, w i * Real.log (1 / |x - t i|)
        = ∑ i ∈ s, -(w i * Real.log |x - t i|) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hdist_ne : |x - t i| ≠ 0 := ne_of_gt (hdist_pos i hi)
          rw [one_div, Real.log_inv]
          ring
    _ = -∑ i ∈ s, w i * Real.log |x - t i| := by
      rw [Finset.sum_neg_distrib]

theorem finiteWeightedPotential_nonneg_of_nonnegative_mean
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w t : ι → ℝ) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1)
    (ht_bound : ∀ i ∈ s, -1 ≤ t i ∧ t i ≤ 1)
    (hmean_nonneg : 0 ≤ ∑ i ∈ s, w i * t i)
    (hdist_pos : ∀ i ∈ s, 0 < |x - t i|) :
    0 ≤ finiteWeightedPotential s w t x := by
  have hlog_nonpos :=
    finite_weighted_log_abs_sum_nonpos_of_nonnegative_mean
      s w t hx0 hx1 hw_nonneg hw_sum ht_bound hmean_nonneg hdist_pos
  rw [finiteWeightedPotential_eq_neg_log_abs_sum s w t hdist_pos]
  linarith

theorem finiteWeightedPotential_nonneg_of_nonpositive_mean
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w t : ι → ℝ) {x : ℝ}
    (hx0 : -1 ≤ x) (hx1 : x ≤ 0)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1)
    (ht_bound : ∀ i ∈ s, -1 ≤ t i ∧ t i ≤ 1)
    (hmean_nonpos : ∑ i ∈ s, w i * t i ≤ 0)
    (hdist_pos : ∀ i ∈ s, 0 < |x - t i|) :
    0 ≤ finiteWeightedPotential s w t x := by
  have hlog_nonpos :=
    finite_weighted_log_abs_sum_nonpos_of_nonpositive_mean
      s w t hx0 hx1 hw_nonneg hw_sum ht_bound hmean_nonpos hdist_pos
  rw [finiteWeightedPotential_eq_neg_log_abs_sum s w t hdist_pos]
  linarith

/-! Finite reflection/translation symmetries for the logarithmic potential. -/

lemma finiteWeightedPotential_reflect
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w t : ι → ℝ) (x : ℝ) :
    finiteWeightedPotential s w (fun i => -t i) (-x) =
      finiteWeightedPotential s w t x := by
  unfold finiteWeightedPotential
  apply Finset.sum_congr rfl
  intro i _hi
  have habs : |-x - -t i| = |x - t i| := by
    rw [show -x - -t i = -(x - t i) by ring]
    exact abs_neg (x - t i)
  rw [habs]

lemma finiteWeightedPotential_translate
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w t : ι → ℝ) (x shift : ℝ) :
    finiteWeightedPotential s w (fun i => t i + shift) (x + shift) =
      finiteWeightedPotential s w t x := by
  unfold finiteWeightedPotential
  apply Finset.sum_congr rfl
  intro i _hi
  congr 2
  congr 1
  congr 1
  ring_nf

lemma finite_weighted_mean_reflect
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w t : ι → ℝ) :
    ∑ i ∈ s, w i * (-t i) = -∑ i ∈ s, w i * t i := by
  calc
    ∑ i ∈ s, w i * (-t i) = ∑ i ∈ s, -(w i * t i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = -∑ i ∈ s, w i * t i := by
      rw [Finset.sum_neg_distrib]

lemma finite_weighted_mean_translate
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w t : ι → ℝ) (shift : ℝ)
    (hw_sum : ∑ i ∈ s, w i = 1) :
    ∑ i ∈ s, w i * (t i + shift) =
      (∑ i ∈ s, w i * t i) + shift := by
  calc
    ∑ i ∈ s, w i * (t i + shift)
        = ∑ i ∈ s, (w i * t i + shift * w i) := by
          apply Finset.sum_congr rfl
          intro i _hi
          ring
    _ = (∑ i ∈ s, w i * t i) + shift * (∑ i ∈ s, w i) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (∑ i ∈ s, w i * t i) + shift := by
          rw [hw_sum]
          ring

/-!
## Continuous probability-measure version of the Lemma 3.2 estimate

The next lemmas replace finite weighted sums by Bochner integrals against an
arbitrary probability measure.  They formalize the Jensen/logarithmic-potential
part of Tao's Lemma 3.2 under the usual real-valued hypotheses needed to avoid
the logarithmic singularity at `x = t`.
-/

lemma measure_kernel_integral_le_one_of_nonnegative_x
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hsupp : ∀ᵐ t ∂μ, -1 ≤ t ∧ t ≤ 1)
    (hkernel_int : Integrable (fun t : ℝ => |x - t| + x * t) μ) :
    (∫ t, |x - t| + x * t ∂μ) ≤ 1 := by
  have hle_ae :
      (fun t : ℝ => |x - t| + x * t) ≤ᵐ[μ] fun _ : ℝ => (1 : ℝ) :=
    hsupp.mono (fun t ht =>
      abs_sub_add_mul_le_one hx0 hx1 ht.1 ht.2)
  have hle_int :
      (∫ t, |x - t| + x * t ∂μ) ≤ ∫ _ : ℝ, (1 : ℝ) ∂μ :=
    integral_mono_ae hkernel_int (integrable_const (1 : ℝ)) hle_ae
  simpa using hle_int

lemma measure_kernel_integral_le_one_of_nonpositive_x
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {x : ℝ}
    (hx0 : -1 ≤ x) (hx1 : x ≤ 0)
    (hsupp : ∀ᵐ t ∂μ, -1 ≤ t ∧ t ≤ 1)
    (hkernel_int : Integrable (fun t : ℝ => |x - t| + x * t) μ) :
    (∫ t, |x - t| + x * t ∂μ) ≤ 1 := by
  have hle_ae :
      (fun t : ℝ => |x - t| + x * t) ≤ᵐ[μ] fun _ : ℝ => (1 : ℝ) := by
    filter_upwards [hsupp] with t ht
    have h :=
      abs_sub_add_mul_le_one
        (x := -x) (t := -t) (by linarith) (by linarith)
        (by linarith [ht.2]) (by linarith [ht.1])
    have habs : |-x - -t| = |x - t| := by
      rw [show -x - -t = t - x by ring]
      exact abs_sub_comm t x
    have hmul : (-x) * (-t) = x * t := by ring
    rwa [habs, hmul] at h
  have hle_int :
      (∫ t, |x - t| + x * t ∂μ) ≤ ∫ _ : ℝ, (1 : ℝ) ∂μ :=
    integral_mono_ae hkernel_int (integrable_const (1 : ℝ)) hle_ae
  simpa using hle_int

lemma measure_kernel_integral_split
    (μ : Measure ℝ) {x : ℝ}
    (hdist_int : Integrable (fun t : ℝ => |x - t|) μ)
    (hlinear_int : Integrable (fun t : ℝ => x * t) μ) :
    (∫ t, |x - t| + x * t ∂μ) =
      (∫ t, |x - t| ∂μ) + x * (∫ t, t ∂μ) := by
  rw [integral_add hdist_int hlinear_int]
  rw [integral_const_mul]

lemma measure_abs_integral_le_one_of_nonnegative_mean
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hsupp : ∀ᵐ t ∂μ, -1 ≤ t ∧ t ≤ 1)
    (hdist_int : Integrable (fun t : ℝ => |x - t|) μ)
    (hlinear_int : Integrable (fun t : ℝ => x * t) μ)
    (hmean_nonneg : 0 ≤ ∫ t : ℝ, t ∂μ) :
    (∫ t, |x - t| ∂μ) ≤ 1 := by
  have hkernel_int : Integrable (fun t : ℝ => |x - t| + x * t) μ :=
    hdist_int.add hlinear_int
  have hkernel :=
    measure_kernel_integral_le_one_of_nonnegative_x μ hx0 hx1 hsupp hkernel_int
  rw [measure_kernel_integral_split μ hdist_int hlinear_int] at hkernel
  have hxmean : 0 ≤ x * (∫ t : ℝ, t ∂μ) :=
    mul_nonneg hx0 hmean_nonneg
  nlinarith

lemma measure_abs_integral_le_one_of_nonpositive_mean
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {x : ℝ}
    (hx0 : -1 ≤ x) (hx1 : x ≤ 0)
    (hsupp : ∀ᵐ t ∂μ, -1 ≤ t ∧ t ≤ 1)
    (hdist_int : Integrable (fun t : ℝ => |x - t|) μ)
    (hlinear_int : Integrable (fun t : ℝ => x * t) μ)
    (hmean_nonpos : (∫ t : ℝ, t ∂μ) ≤ 0) :
    (∫ t, |x - t| ∂μ) ≤ 1 := by
  have hkernel_int : Integrable (fun t : ℝ => |x - t| + x * t) μ :=
    hdist_int.add hlinear_int
  have hkernel :=
    measure_kernel_integral_le_one_of_nonpositive_x μ hx0 hx1 hsupp hkernel_int
  rw [measure_kernel_integral_split μ hdist_int hlinear_int] at hkernel
  have hxmean : 0 ≤ x * (∫ t : ℝ, t ∂μ) :=
    mul_nonneg_of_nonpos_of_nonpos hx1 hmean_nonpos
  nlinarith

lemma measure_log_abs_integral_le_log_abs_integral
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {x ε : ℝ}
    (hε : 0 < ε)
    (hdist_lower : ∀ᵐ t ∂μ, ε ≤ |x - t|)
    (hdist_int : Integrable (fun t : ℝ => |x - t|) μ)
    (hlog_int : Integrable (fun t : ℝ => Real.log |x - t|) μ) :
    (∫ t, Real.log |x - t| ∂μ) ≤
      Real.log (∫ t, |x - t| ∂μ) := by
  have hconc : ConcaveOn ℝ (Ici ε) Real.log :=
    strictConcaveOn_log_Ioi.concaveOn.subset
      (fun y hy => lt_of_lt_of_le hε hy) (convex_Ici ε)
  have hcont : ContinuousOn Real.log (Ici ε) :=
    Real.continuousOn_log.mono (fun y hy => ne_of_gt (lt_of_lt_of_le hε hy))
  exact hconc.le_map_integral hcont isClosed_Ici hdist_lower hdist_int hlog_int

lemma measure_log_abs_integral_nonpos_of_abs_integral_le_one
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {x ε : ℝ}
    (hε : 0 < ε)
    (hdist_lower : ∀ᵐ t ∂μ, ε ≤ |x - t|)
    (hdist_int : Integrable (fun t : ℝ => |x - t|) μ)
    (hlog_int : Integrable (fun t : ℝ => Real.log |x - t|) μ)
    (havg_le_one : (∫ t, |x - t| ∂μ) ≤ 1) :
    (∫ t, Real.log |x - t| ∂μ) ≤ 0 := by
  have hj :=
    measure_log_abs_integral_le_log_abs_integral μ
      hε hdist_lower hdist_int hlog_int
  have havg_nonneg : 0 ≤ ∫ t, |x - t| ∂μ :=
    integral_nonneg (fun t => abs_nonneg (x - t))
  have hlog_nonpos : Real.log (∫ t, |x - t| ∂μ) ≤ 0 :=
    Real.log_nonpos havg_nonneg havg_le_one
  exact le_trans hj hlog_nonpos

/-- Real-valued logarithmic potential of a probability measure. -/
def measureLogPotential (μ : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ t, Real.log (1 / |x - t|) ∂μ

lemma measureLogPotential_eq_neg_log_abs_integral
    (μ : Measure ℝ) {x : ℝ}
    (hdist_pos : ∀ᵐ t ∂μ, 0 < |x - t|) :
    measureLogPotential μ x =
      -∫ t, Real.log |x - t| ∂μ := by
  unfold measureLogPotential
  have hcongr :
    (fun t : ℝ => Real.log (1 / |x - t|))
        =ᵐ[μ] fun t : ℝ => -Real.log |x - t| :=
    hdist_pos.mono (fun t ht => by
      simp [one_div, Real.log_inv])
  rw [integral_congr_ae hcongr]
  rw [integral_neg]

/--
Boundary form of Jensen's logarithmic step.  If the logarithmic potential at a
test point is nonpositive, then the average distance from that point is at
least one.
-/
lemma one_le_abs_integral_of_measureLogPotential_nonpos
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {x ε : ℝ}
    (hε : 0 < ε)
    (hdist_lower : ∀ᵐ t ∂μ, ε ≤ |x - t|)
    (hdist_int : Integrable (fun t : ℝ => |x - t|) μ)
    (hlog_int : Integrable (fun t : ℝ => Real.log |x - t|) μ)
    (hpotential_nonpos : measureLogPotential μ x ≤ 0) :
    1 ≤ ∫ t, |x - t| ∂μ := by
  have hdist_pos : ∀ᵐ t ∂μ, 0 < |x - t| :=
    hdist_lower.mono (fun _ ht => lt_of_lt_of_le hε ht)
  have hlog_nonneg : 0 ≤ ∫ t, Real.log |x - t| ∂μ := by
    rw [measureLogPotential_eq_neg_log_abs_integral μ hdist_pos] at hpotential_nonpos
    linarith
  have hlog_le :
      (∫ t, Real.log |x - t| ∂μ) ≤
        Real.log (∫ t, |x - t| ∂μ) :=
    measure_log_abs_integral_le_log_abs_integral μ
      hε hdist_lower hdist_int hlog_int
  have hlog_avg_nonneg : 0 ≤ Real.log (∫ t, |x - t| ∂μ) :=
    le_trans hlog_nonneg hlog_le
  have hε_le_avg : ε ≤ ∫ t, |x - t| ∂μ := by
    have hle :
        (∫ _ : ℝ, ε ∂μ) ≤ ∫ t, |x - t| ∂μ :=
      integral_mono_ae (integrable_const ε) hdist_int hdist_lower
    simpa using hle
  have havg_pos : 0 < ∫ t, |x - t| ∂μ :=
    lt_of_lt_of_le hε hε_le_avg
  exact (Real.log_nonneg_iff havg_pos).1 hlog_avg_nonneg

theorem measureLogPotential_nonneg_of_nonnegative_mean
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {x ε : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hε : 0 < ε)
    (hsupp : ∀ᵐ t ∂μ, -1 ≤ t ∧ t ≤ 1)
    (hdist_lower : ∀ᵐ t ∂μ, ε ≤ |x - t|)
    (hdist_int : Integrable (fun t : ℝ => |x - t|) μ)
    (hlinear_int : Integrable (fun t : ℝ => x * t) μ)
    (hlog_int : Integrable (fun t : ℝ => Real.log |x - t|) μ)
    (hmean_nonneg : 0 ≤ ∫ t : ℝ, t ∂μ) :
    0 ≤ measureLogPotential μ x := by
  have havg_le_one :=
    measure_abs_integral_le_one_of_nonnegative_mean μ hx0 hx1 hsupp
      hdist_int hlinear_int hmean_nonneg
  have hlog_nonpos :=
    measure_log_abs_integral_nonpos_of_abs_integral_le_one μ
      hε hdist_lower hdist_int hlog_int havg_le_one
  have hdist_pos : ∀ᵐ t ∂μ, 0 < |x - t| :=
    hdist_lower.mono (fun _ ht => lt_of_lt_of_le hε ht)
  rw [measureLogPotential_eq_neg_log_abs_integral μ hdist_pos]
  linarith

theorem measureLogPotential_nonneg_of_nonpositive_mean
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {x ε : ℝ}
    (hx0 : -1 ≤ x) (hx1 : x ≤ 0)
    (hε : 0 < ε)
    (hsupp : ∀ᵐ t ∂μ, -1 ≤ t ∧ t ≤ 1)
    (hdist_lower : ∀ᵐ t ∂μ, ε ≤ |x - t|)
    (hdist_int : Integrable (fun t : ℝ => |x - t|) μ)
    (hlinear_int : Integrable (fun t : ℝ => x * t) μ)
    (hlog_int : Integrable (fun t : ℝ => Real.log |x - t|) μ)
    (hmean_nonpos : (∫ t : ℝ, t ∂μ) ≤ 0) :
    0 ≤ measureLogPotential μ x := by
  have havg_le_one :=
    measure_abs_integral_le_one_of_nonpositive_mean μ hx0 hx1 hsupp
      hdist_int hlinear_int hmean_nonpos
  have hlog_nonpos :=
    measure_log_abs_integral_nonpos_of_abs_integral_le_one μ
      hε hdist_lower hdist_int hlog_int havg_le_one
  have hdist_pos : ∀ᵐ t ∂μ, 0 < |x - t| :=
    hdist_lower.mono (fun _ ht => lt_of_lt_of_le hε ht)
  rw [measureLogPotential_eq_neg_log_abs_integral μ hdist_pos]
  linarith

/-! Continuous reflection/translation symmetries for the logarithmic potential. -/

lemma measureLogPotential_reflect (μ : Measure ℝ) (x : ℝ) :
    measureLogPotential (Measure.map (fun t : ℝ => -t) μ) (-x) =
      measureLogPotential μ x := by
  unfold measureLogPotential
  rw [integral_map]
  · apply integral_congr_ae
    filter_upwards with t
    have habs : |-x - -t| = |x - t| := by
      rw [show -x - -t = -(x - t) by ring]
      exact abs_neg (x - t)
    rw [habs]
  · fun_prop
  · exact (Real.measurable_log.comp (measurable_const.div
      (continuous_abs.measurable.comp
        (measurable_const.sub measurable_id)))).aestronglyMeasurable

lemma measureLogPotential_translate (μ : Measure ℝ) (x shift : ℝ) :
    measureLogPotential (Measure.map (fun t : ℝ => t + shift) μ)
      (x + shift) =
    measureLogPotential μ x := by
  unfold measureLogPotential
  rw [integral_map]
  · apply integral_congr_ae
    filter_upwards with t
    have habs : |x + shift - (t + shift)| = |x - t| := by
      congr 1
      ring
    rw [habs]
  · fun_prop
  · exact (Real.measurable_log.comp (measurable_const.div
      (continuous_abs.measurable.comp
        (measurable_const.sub measurable_id)))).aestronglyMeasurable

lemma measure_mean_reflect (μ : Measure ℝ) :
    (∫ t : ℝ, t ∂Measure.map (fun t : ℝ => -t) μ) =
      -(∫ t : ℝ, t ∂μ) := by
  rw [integral_map]
  · rw [integral_neg]
  · fun_prop
  · fun_prop

lemma measure_mean_translate (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (shift : ℝ)
    (hfirst : Integrable (fun t : ℝ => t) μ) :
    (∫ t : ℝ, t ∂Measure.map (fun t : ℝ => t + shift) μ) =
      (∫ t : ℝ, t ∂μ) + shift := by
  rw [integral_map]
  · rw [integral_add hfirst (integrable_const shift)]
    rw [integral_const]
    simp
  · fun_prop
  · fun_prop

/-!
## Compactness layer for Tao's Lemma 3.1

Tao's existence step uses the direct method: compactness of the admissible
class and lower semicontinuity of the objective imply existence of a minimizer.
The theorem below is the exact general topological statement, with no
problem-specific extra assumption.
-/

theorem compact_nonempty_lsc_exists_minimizer
    {α : Type*} [TopologicalSpace α]
    (s : Set α) (objective : α → ℝ)
    (hne : s.Nonempty)
    (hcompact : IsCompact s)
    (hlsc : LowerSemicontinuousOn objective s) :
    ∃ a : α, a ∈ s ∧ ∀ b : α, b ∈ s → objective a ≤ objective b := by
  rcases hlsc.exists_isMinOn hne hcompact with ⟨a, ha, hmin⟩
  exact ⟨a, ha, fun b hb => hmin hb⟩

/--
The same compact direct-method statement for an extended nonnegative real
objective.  This is the form needed by the true length objective
`μ ↦ volume {x | 0 < U_μ x}`.
-/
theorem compact_nonempty_lsc_exists_minimizer_ennreal
    {α : Type*} [TopologicalSpace α]
    (s : Set α) (objective : α → ℝ≥0∞)
    (hne : s.Nonempty)
    (hcompact : IsCompact s)
    (hlsc : LowerSemicontinuousOn objective s) :
    ∃ a : α, a ∈ s ∧ ∀ b : α, b ∈ s → objective a ≤ objective b := by
  rcases hlsc.exists_isMinOn hne hcompact with ⟨a, ha, hmin⟩
  exact ⟨a, ha, fun b hb => hmin hb⟩

/-- Predicate form of `compact_nonempty_lsc_exists_minimizer`. -/
theorem compact_predicate_lsc_exists_minimizer
    {α : Type*} [TopologicalSpace α]
    (Admissible : α → Prop) (objective : α → ℝ)
    (hne : ∃ a : α, Admissible a)
    (hcompact : IsCompact {a : α | Admissible a})
    (hlsc : LowerSemicontinuousOn objective {a : α | Admissible a}) :
    ∃ a : α, Admissible a ∧ ∀ b : α, Admissible b → objective a ≤ objective b := by
  rcases compact_nonempty_lsc_exists_minimizer
      {a : α | Admissible a} objective hne hcompact hlsc with
    ⟨a, ha, hmin⟩
  exact ⟨a, ha, fun b hb => hmin b hb⟩

/-!
## Concrete compact admissible class

For the relaxed continuous formulation, the admissible measures are probability
measures on the compact interval `[-1,1]`.  Mathlib's Prokhorov theorem gives
compactness of `ProbabilityMeasure E` when `E` is compact; this makes the
direct-method existence step completely concrete once the objective is known
to be lower semicontinuous.
-/

abbrev UnitInterval1038 := {x : ℝ // x ∈ Icc (-1 : ℝ) 1}

instance : CompactSpace UnitInterval1038 := by
  exact isCompact_iff_compactSpace.mp CompactIccSpace.isCompact_Icc

instance : Inhabited UnitInterval1038 := ⟨⟨0, by norm_num⟩⟩

abbrev AdmissibleProbability1038 := ProbabilityMeasure UnitInterval1038

instance : CompactSpace AdmissibleProbability1038 := by
  infer_instance

theorem admissible_probability_compact :
    IsCompact (Set.univ : Set AdmissibleProbability1038) := by
  exact isCompact_univ

theorem admissible_probability_lsc_exists_minimizer
    (objective : AdmissibleProbability1038 → ℝ)
    (hlsc : LowerSemicontinuous objective) :
    ∃ μ : AdmissibleProbability1038,
      ∀ ν : AdmissibleProbability1038, objective μ ≤ objective ν := by
  have hne : (Set.univ : Set AdmissibleProbability1038).Nonempty :=
    Set.univ_nonempty
  have hlscOn :
      LowerSemicontinuousOn objective
        (Set.univ : Set AdmissibleProbability1038) :=
    hlsc.lowerSemicontinuousOn (Set.univ : Set AdmissibleProbability1038)
  rcases hlscOn.exists_isMinOn hne admissible_probability_compact with
    ⟨μ, _hμ, hmin⟩
  exact ⟨μ, fun ν => hmin trivial⟩

/--
Concrete direct-method existence for the actual extended-valued length
objective on probability measures over `[-1,1]`.
-/
theorem admissible_probability_lsc_exists_minimizer_ennreal
    (objective : AdmissibleProbability1038 → ℝ≥0∞)
    (hlsc : LowerSemicontinuous objective) :
    ∃ μ : AdmissibleProbability1038,
      ∀ ν : AdmissibleProbability1038, objective μ ≤ objective ν := by
  have hne : (Set.univ : Set AdmissibleProbability1038).Nonempty :=
    Set.univ_nonempty
  have hlscOn :
      LowerSemicontinuousOn objective
        (Set.univ : Set AdmissibleProbability1038) :=
    hlsc.lowerSemicontinuousOn (Set.univ : Set AdmissibleProbability1038)
  rcases compact_nonempty_lsc_exists_minimizer_ennreal
      (Set.univ : Set AdmissibleProbability1038) objective hne
      admissible_probability_compact hlscOn with
    ⟨μ, _hμ, hmin⟩
  exact ⟨μ, fun ν => hmin ν trivial⟩

lemma argmin_set_eq_sublevel_at_min
    {α : Type*} [TopologicalSpace α] (objective : α → ℝ) (a0 : α)
    (hmin : ∀ b : α, objective a0 ≤ objective b) :
    {a : α | ∀ b : α, objective a ≤ objective b} =
      objective ⁻¹' Iic (objective a0) := by
  ext a
  constructor
  · intro ha
    exact ha a0
  · intro ha b
    exact le_trans ha (hmin b)

lemma compact_argmin_set_of_lsc
    {α : Type*} [TopologicalSpace α] [CompactSpace α]
    (objective : α → ℝ) (a0 : α)
    (hlsc : LowerSemicontinuous objective)
    (hmin : ∀ b : α, objective a0 ≤ objective b) :
    IsCompact {a : α | ∀ b : α, objective a ≤ objective b} := by
  rw [argmin_set_eq_sublevel_at_min objective a0 hmin]
  exact (hlsc.isClosed_preimage (objective a0)).isCompact

lemma argmin_set_eq_sublevel_at_min_ennreal
    {α : Type*} [TopologicalSpace α] (objective : α → ℝ≥0∞) (a0 : α)
    (hmin : ∀ b : α, objective a0 ≤ objective b) :
    {a : α | ∀ b : α, objective a ≤ objective b} =
      objective ⁻¹' Iic (objective a0) := by
  ext a
  constructor
  · intro ha
    exact ha a0
  · intro ha b
    exact le_trans ha (hmin b)

lemma compact_argmin_set_of_lsc_ennreal
    {α : Type*} [TopologicalSpace α] [CompactSpace α]
    (objective : α → ℝ≥0∞) (a0 : α)
    (hlsc : LowerSemicontinuous objective)
    (hmin : ∀ b : α, objective a0 ≤ objective b) :
    IsCompact {a : α | ∀ b : α, objective a ≤ objective b} := by
  rw [argmin_set_eq_sublevel_at_min_ennreal objective a0 hmin]
  exact (hlsc.isClosed_preimage (objective a0)).isCompact

theorem admissible_probability_lsc_exists_secondary_minimizer
    (primary secondary : AdmissibleProbability1038 → ℝ)
    (hprimary_lsc : LowerSemicontinuous primary)
    (hsecondary_lsc : LowerSemicontinuous secondary) :
    ∃ μ : AdmissibleProbability1038,
      (∀ ν : AdmissibleProbability1038, primary μ ≤ primary ν) ∧
      ∀ ν : AdmissibleProbability1038,
        (∀ η : AdmissibleProbability1038, primary ν ≤ primary η) →
          secondary μ ≤ secondary ν := by
  rcases admissible_probability_lsc_exists_minimizer primary
      hprimary_lsc with ⟨μ0, hμ0⟩
  let Argmin : AdmissibleProbability1038 → Prop :=
    fun μ => ∀ ν : AdmissibleProbability1038, primary μ ≤ primary ν
  have hne : ∃ μ : AdmissibleProbability1038, Argmin μ := ⟨μ0, hμ0⟩
  have hcompact : IsCompact {μ : AdmissibleProbability1038 | Argmin μ} := by
    simpa [Argmin] using
      compact_argmin_set_of_lsc primary μ0 hprimary_lsc hμ0
  have hsecOn :
      LowerSemicontinuousOn secondary
        {μ : AdmissibleProbability1038 | Argmin μ} :=
    hsecondary_lsc.lowerSemicontinuousOn
      {μ : AdmissibleProbability1038 | Argmin μ}
  rcases hsecOn.exists_isMinOn hne hcompact with ⟨μ, hμ, hminsec⟩
  exact ⟨μ, hμ, fun ν hν => hminsec hν⟩

theorem admissible_probability_lsc_exists_secondary_minimizer_ennreal_primary
    (primary : AdmissibleProbability1038 → ℝ≥0∞)
    (secondary : AdmissibleProbability1038 → ℝ)
    (hprimary_lsc : LowerSemicontinuous primary)
    (hsecondary_lsc : LowerSemicontinuous secondary) :
    ∃ μ : AdmissibleProbability1038,
      (∀ ν : AdmissibleProbability1038, primary μ ≤ primary ν) ∧
      ∀ ν : AdmissibleProbability1038,
        (∀ η : AdmissibleProbability1038, primary ν ≤ primary η) →
          secondary μ ≤ secondary ν := by
  rcases admissible_probability_lsc_exists_minimizer_ennreal primary
      hprimary_lsc with ⟨μ0, hμ0⟩
  let Argmin : AdmissibleProbability1038 → Prop :=
    fun μ => ∀ ν : AdmissibleProbability1038, primary μ ≤ primary ν
  have hne : ∃ μ : AdmissibleProbability1038, Argmin μ := ⟨μ0, hμ0⟩
  have hcompact : IsCompact {μ : AdmissibleProbability1038 | Argmin μ} := by
    simpa [Argmin] using
      compact_argmin_set_of_lsc_ennreal primary μ0 hprimary_lsc hμ0
  have hsecOn :
      LowerSemicontinuousOn secondary
        {μ : AdmissibleProbability1038 | Argmin μ} :=
    hsecondary_lsc.lowerSemicontinuousOn
      {μ : AdmissibleProbability1038 | Argmin μ}
  rcases hsecOn.exists_isMinOn hne hcompact with ⟨μ, hμ, hminsec⟩
  exact ⟨μ, hμ, fun ν hν => hminsec hν⟩

/-!
## Positive-set objective inner approximation

The length objective in the relaxed problem is the Lebesgue measure of
`{x | 0 < U x}`.  The next lemmas formalize the inner approximation used in
the lower-semicontinuity argument: the positive set is the increasing union of
strict threshold sets `{x | 1/(n+1) < U x}`.
-/

lemma positiveSet_eq_iUnion_thresholds (U : ℝ → ℝ) :
    {x : ℝ | 0 < U x} =
      ⋃ n : ℕ, {x : ℝ | 1 / ((n : ℝ) + 1) < U x} := by
  ext x
  constructor
  · intro hx
    rcases exists_nat_one_div_lt (show 0 < U x from hx) with ⟨n, hn⟩
    exact mem_iUnion.mpr ⟨n, hn⟩
  · intro hx
    rcases mem_iUnion.mp hx with ⟨n, hn⟩
    have hpos : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    exact lt_trans hpos hn

lemma monotone_thresholds (U : ℝ → ℝ) :
    Monotone (fun n : ℕ =>
      {x : ℝ | 1 / ((n : ℝ) + 1) < U x}) := by
  intro n m hnm x hx
  have hden : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ hnm
  have hpos : 0 < (n : ℝ) + 1 := by positivity
  have hle : (1 : ℝ) / ((m : ℝ) + 1) ≤
      1 / ((n : ℝ) + 1) := by
    exact one_div_le_one_div_of_le hpos hden
  exact lt_of_le_of_lt hle hx

lemma positiveSet_measure_eq_iSup_thresholds (U : ℝ → ℝ) :
    volume {x : ℝ | 0 < U x} =
      ⨆ n : ℕ, volume {x : ℝ | 1 / ((n : ℝ) + 1) < U x} := by
  rw [positiveSet_eq_iUnion_thresholds U]
  exact (monotone_thresholds U).measure_iUnion

lemma positiveSet_measure_le_of_thresholds_le
    (U : ℝ → ℝ) {B : ℝ≥0∞}
    (hB : ∀ n : ℕ,
      volume {x : ℝ | 1 / ((n : ℝ) + 1) < U x} ≤ B) :
    volume {x : ℝ | 0 < U x} ≤ B := by
  rw [positiveSet_measure_eq_iSup_thresholds U]
  exact iSup_le hB

lemma exists_iSup_nat_le_add_of_ne_top
    (f : ℕ → ℝ≥0∞) {η : NNReal}
    (hη : 0 < η) (hfinite : (⨆ n : ℕ, f n) ≠ ∞) :
    ∃ n : ℕ, (⨆ n : ℕ, f n) ≤ f n + (η : ℝ≥0∞) := by
  let S : ℝ≥0∞ := ⨆ n : ℕ, f n
  by_cases hSzero : S = 0
  · exact ⟨0, by simp [S, hSzero]⟩
  · have hη_ne : (η : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (ne_of_gt hη)
    have hsub_lt : S - (η : ℝ≥0∞) < S := by
      exact ENNReal.sub_lt_self (by simpa [S] using hfinite) hSzero hη_ne
    have hexists : ∃ n : ℕ, S - (η : ℝ≥0∞) < f n := by
      simpa [S] using (lt_iSup_iff.mp hsub_lt)
    rcases hexists with ⟨n, hn⟩
    refine ⟨n, le_of_lt ?_⟩
    have hlt : S < (η : ℝ≥0∞) + f n :=
      ENNReal.lt_add_of_sub_lt_left (Or.inl (by simpa [S] using hfinite)) hn
    simpa [add_comm] using hlt

lemma probability_measure_open_liminf_of_tendsto
    {Ω ι : Type*} {L : Filter ι}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    [HasOuterApproxClosed Ω]
    {μ : ProbabilityMeasure Ω} {μs : ι → ProbabilityMeasure Ω}
    (hμs : Filter.Tendsto μs L (nhds μ)) {G : Set Ω} (hG : IsOpen G) :
    (μ : Measure Ω) G ≤ L.liminf fun i => (μs i : Measure Ω) G := by
  exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμs hG

theorem positiveSet_measure_le_liminf_of_thresholds_le_liminf
    {ι : Type*} {L : Filter ι}
    (U : ℝ → ℝ) (objectives : ι → ℝ≥0∞)
    (hthreshold :
      ∀ n : ℕ,
        volume {x : ℝ | 1 / ((n : ℝ) + 1) < U x} ≤
          L.liminf objectives) :
    volume {x : ℝ | 0 < U x} ≤ L.liminf objectives := by
  exact positiveSet_measure_le_of_thresholds_le U hthreshold

lemma threshold_measure_le_liminf_of_eventually_subset
    {ι : Type*} {L : Filter ι} (A : Set ℝ) (E : ι → Set ℝ)
    (hsub : ∀ᶠ i in L, A ⊆ E i) :
    volume A ≤ L.liminf (fun i => volume (E i)) := by
  exact Filter.le_liminf_of_le
    (h := hsub.mono (fun _i hi => measure_mono hi))

theorem variable_positiveSet_measure_le_liminf_of_eventually_threshold_subset
    {ι : Type*} {L : Filter ι} (U : ℝ → ℝ) (Us : ι → ℝ → ℝ)
    (hsub : ∀ n : ℕ, ∀ᶠ i in L,
      {x : ℝ | 1 / ((n : ℝ) + 1) < U x} ⊆
        {x : ℝ | 0 < Us i x}) :
    volume {x : ℝ | 0 < U x} ≤
      L.liminf (fun i => volume {x : ℝ | 0 < Us i x}) := by
  refine positiveSet_measure_le_of_thresholds_le U ?_
  intro n
  exact Filter.le_liminf_of_le
    (h := (hsub n).mono (fun _i hi => measure_mono hi))

theorem positiveSet_measure_le_liminf_of_eventually_subset_up_to_error
    {ι : Type*} {L : Filter ι} (U : ℝ → ℝ) (Us : ι → ℝ → ℝ)
    (happrox : ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
      ∃ A : Set ℝ,
        volume {x : ℝ | 1 / ((n : ℝ) + 1) < U x} ≤
          volume A + (ε : ℝ≥0∞) ∧
        ∀ᶠ i in L, A ⊆ {x : ℝ | 0 < Us i x}) :
    volume {x : ℝ | 0 < U x} ≤
      L.liminf (fun i => volume {x : ℝ | 0 < Us i x}) := by
  refine positiveSet_measure_le_of_thresholds_le U ?_
  intro n
  let B : ℝ≥0∞ :=
    L.liminf (fun i => volume {x : ℝ | 0 < Us i x})
  by_cases htop : B = ∞
  · simp [B, htop]
  · have hle :
        volume {x : ℝ | 1 / ((n : ℝ) + 1) < U x} ≤ B := by
      refine ENNReal.le_of_forall_pos_le_add ?_
      intro ε hε _hB
      rcases happrox n ε hε with ⟨A, hAmeasure, hAsub⟩
      have hAle : volume A ≤ B := by
        exact threshold_measure_le_liminf_of_eventually_subset A
          (fun i => {x : ℝ | 0 < Us i x}) hAsub
      have hsum : volume A + (ε : ℝ≥0∞) ≤ B + (ε : ℝ≥0∞) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right hAle (ε : ℝ≥0∞)
      exact le_trans hAmeasure hsum
    simpa [B] using hle

lemma threshold_measure_le_liminf_of_eventually_subset_union_null
    {ι : Type*} {L : Filter ι} (A : Set ℝ)
    (E N : ι → Set ℝ)
    (hsub : ∀ᶠ i in L, A ⊆ E i ∪ N i)
    (hnull : ∀ᶠ i in L, volume (N i) = 0) :
    volume A ≤ L.liminf (fun i => volume (E i)) := by
  exact Filter.le_liminf_of_le
    (h := by
      filter_upwards [hsub, hnull] with i hsubi hnulli
      have hmono : volume A ≤ volume (E i ∪ N i) :=
        measure_mono hsubi
      have hunion : volume (E i ∪ N i) ≤ volume (E i) + volume (N i) :=
        measure_union_le _ _
      calc
        volume A ≤ volume (E i ∪ N i) := hmono
        _ ≤ volume (E i) + volume (N i) := hunion
        _ = volume (E i) := by simp [hnulli])

theorem positiveSet_measure_le_liminf_of_eventually_subset_union_null_up_to_error
    {ι : Type*} {L : Filter ι} (U : ℝ → ℝ) (Us : ι → ℝ → ℝ)
    (N : ι → Set ℝ)
    (hnull : ∀ᶠ i in L, volume (N i) = 0)
    (happrox : ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
      ∃ A : Set ℝ,
        volume {x : ℝ | 1 / ((n : ℝ) + 1) < U x} ≤
          volume A + (ε : ℝ≥0∞) ∧
        ∀ᶠ i in L, A ⊆ {x : ℝ | 0 < Us i x} ∪ N i) :
    volume {x : ℝ | 0 < U x} ≤
      L.liminf (fun i => volume {x : ℝ | 0 < Us i x}) := by
  refine positiveSet_measure_le_of_thresholds_le U ?_
  intro n
  let B : ℝ≥0∞ :=
    L.liminf (fun i => volume {x : ℝ | 0 < Us i x})
  by_cases htop : B = ∞
  · simp [B, htop]
  · have hle :
        volume {x : ℝ | 1 / ((n : ℝ) + 1) < U x} ≤ B := by
      refine ENNReal.le_of_forall_pos_le_add ?_
      intro ε hε _hB
      rcases happrox n ε hε with ⟨A, hAmeasure, hAsub⟩
      have hAle : volume A ≤ B := by
        exact threshold_measure_le_liminf_of_eventually_subset_union_null
          A (fun i => {x : ℝ | 0 < Us i x}) N hAsub hnull
      have hsum : volume A + (ε : ℝ≥0∞) ≤ B + (ε : ℝ≥0∞) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right hAle (ε : ℝ≥0∞)
      exact le_trans hAmeasure hsum
    simpa [B] using hle

lemma lintegral_markov_bound
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℝ≥0∞) {η C : ℝ≥0∞}
    (hη0 : η ≠ 0) (hηtop : η ≠ ∞)
    (hS : MeasurableSet {x : α | η < f x})
    (hint : ∫⁻ x, f x ∂μ ≤ C) :
    μ {x : α | η < f x} ≤ C / η := by
  have hpoint :
      Set.indicator {x : α | η < f x} (fun _ : α => η) ≤ f := by
    intro x
    by_cases hx : x ∈ {x : α | η < f x}
    · have hxlt : η < f x := hx
      simp [Set.indicator_of_mem hx, le_of_lt hxlt]
    · simp [Set.indicator_of_notMem hx]
  have hint_lower :
      η * μ {x : α | η < f x} ≤ ∫⁻ x, f x ∂μ := by
    calc
      η * μ {x : α | η < f x}
          = ∫⁻ x,
              Set.indicator {x : α | η < f x}
                (fun _ : α => η) x ∂μ := by
            rw [lintegral_indicator_const hS]
      _ ≤ ∫⁻ x, f x ∂μ := lintegral_mono hpoint
  have hmul : μ {x : α | η < f x} * η ≤ C := by
    calc
      μ {x : α | η < f x} * η =
          η * μ {x : α | η < f x} := by
            rw [mul_comm]
      _ ≤ ∫⁻ x, f x ∂μ := hint_lower
      _ ≤ C := hint
  exact (ENNReal.le_div_iff_mul_le (Or.inl hη0) (Or.inl hηtop)).2 hmul

lemma eventually_threshold_subset_of_eventually_pointwise_error
    {ι : Type*} {L : Filter ι} (U : ℝ → ℝ) (Us : ι → ℝ → ℝ)
    (n : ℕ)
    (herr : ∀ᶠ i in L, ∀ x : ℝ,
      |Us i x - U x| < 1 / ((n : ℝ) + 1)) :
    ∀ᶠ i in L,
      {x : ℝ | 1 / ((n : ℝ) + 1) < U x} ⊆
        {x : ℝ | 0 < Us i x} := by
  refine herr.mono ?_
  intro i hi x hx
  change 0 < Us i x
  have hx' : 1 / ((n : ℝ) + 1) < U x := hx
  have hneg : -(1 / ((n : ℝ) + 1)) < Us i x - U x :=
    (abs_lt.mp (hi x)).1
  linarith

theorem variable_positiveSet_measure_le_liminf_of_eventually_pointwise_error
    {ι : Type*} {L : Filter ι} (U : ℝ → ℝ) (Us : ι → ℝ → ℝ)
    (herr : ∀ n : ℕ, ∀ᶠ i in L, ∀ x : ℝ,
      |Us i x - U x| < 1 / ((n : ℝ) + 1)) :
    volume {x : ℝ | 0 < U x} ≤
      L.liminf (fun i => volume {x : ℝ | 0 < Us i x}) := by
  exact variable_positiveSet_measure_le_liminf_of_eventually_threshold_subset
    U Us
    (fun n =>
      eventually_threshold_subset_of_eventually_pointwise_error U Us n
        (herr n))

theorem measureLogPotential_positiveSet_measure_le_liminf
    {ι : Type*} {L : Filter ι}
    (μ : Measure ℝ) (μs : ι → Measure ℝ)
    (herr : ∀ n : ℕ, ∀ᶠ i in L, ∀ x : ℝ,
      |measureLogPotential (μs i) x - measureLogPotential μ x| <
        1 / ((n : ℝ) + 1)) :
    volume {x : ℝ | 0 < measureLogPotential μ x} ≤
      L.liminf
        (fun i => volume {x : ℝ | 0 < measureLogPotential (μs i) x}) := by
  exact variable_positiveSet_measure_le_liminf_of_eventually_pointwise_error
    (measureLogPotential μ)
    (fun i => measureLogPotential (μs i))
    herr

def unitIntervalLogPotential
    (μ : ProbabilityMeasure UnitInterval1038) (x : ℝ) : ℝ :=
  ∫ t : UnitInterval1038,
    Real.log (1 / |x - (t : ℝ)|) ∂(μ : Measure UnitInterval1038)

/--
Concrete secondary objective for the Tao selector: the second moment of the
probability measure on the normalized interval `[-1,1]`.
-/
def unitIntervalSecondMomentObjective
    (μ : ProbabilityMeasure UnitInterval1038) : ℝ :=
  ∫ t : UnitInterval1038, (t : ℝ) ^ 2 ∂(μ : Measure UnitInterval1038)

/-- The bounded-continuous-function form of the second-moment integrand. -/
noncomputable def unitIntervalSecondMomentBCF :
    BoundedContinuousFunction UnitInterval1038 ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun t : UnitInterval1038 => (t : ℝ) ^ 2, by continuity⟩

/-- Weak continuity of the concrete second-moment objective. -/
theorem unitIntervalSecondMomentObjective_tendsto
    {ι : Type*} {L : Filter ι}
    {μ : ProbabilityMeasure UnitInterval1038}
    {μs : ι → ProbabilityMeasure UnitInterval1038}
    (hμs : Filter.Tendsto μs L (nhds μ)) :
    Filter.Tendsto
      (fun i => unitIntervalSecondMomentObjective (μs i)) L
      (nhds (unitIntervalSecondMomentObjective μ)) := by
  simpa [unitIntervalSecondMomentObjective, unitIntervalSecondMomentBCF] using
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμs)
      unitIntervalSecondMomentBCF

/-- Continuity of the concrete second-moment objective. -/
theorem unitIntervalSecondMomentObjective_continuous :
    Continuous unitIntervalSecondMomentObjective := by
  rw [continuous_iff_continuousAt]
  intro μ
  exact unitIntervalSecondMomentObjective_tendsto
    (μs := fun ν : ProbabilityMeasure UnitInterval1038 => ν)
    (L := nhds μ) Filter.tendsto_id

/-- Lower semicontinuity of the concrete second-moment secondary objective. -/
theorem unitIntervalSecondMomentObjective_lowerSemicontinuous :
    LowerSemicontinuous unitIntervalSecondMomentObjective :=
  unitIntervalSecondMomentObjective_continuous.lowerSemicontinuous

/-- Joint measurability of the logarithmic kernel on `ℝ × [-1,1]`. -/
lemma measurable_unitIntervalLogKernel_uncurry :
    Measurable
      (fun p : ℝ × UnitInterval1038 =>
        Real.log (1 / |p.1 - (p.2 : ℝ)|)) := by
  exact Real.measurable_log.comp
    (measurable_const.div
      ((continuous_fst.sub (continuous_subtype_val.comp continuous_snd)).abs.measurable))

/-- Measurability of the real-valued unit-interval logarithmic potential. -/
theorem unitIntervalLogPotential_measurable
    (μ : ProbabilityMeasure UnitInterval1038) :
    Measurable (unitIntervalLogPotential μ) := by
  unfold unitIntervalLogPotential
  have hstrong :
      StronglyMeasurable
        (fun p : ℝ × UnitInterval1038 =>
          Real.log (1 / |p.1 - (p.2 : ℝ)|)) :=
    measurable_unitIntervalLogKernel_uncurry.stronglyMeasurable
  exact (hstrong.integral_prod_right'
    (ν := (μ : Measure UnitInterval1038))).measurable

/-- Every positive threshold set of the unit-interval potential is measurable. -/
theorem unitIntervalLogPotential_measurableSet_threshold
    (μ : ProbabilityMeasure UnitInterval1038) (τ : ℝ) :
    MeasurableSet {x : ℝ | τ < unitIntervalLogPotential μ x} := by
  exact measurableSet_lt measurable_const (unitIntervalLogPotential_measurable μ)

def realMeasure (μ : ProbabilityMeasure UnitInterval1038) : Measure ℝ :=
  Measure.map (fun t : UnitInterval1038 => (t : ℝ)) (μ : Measure UnitInterval1038)

/-- The second-moment objective is the second moment of the pushed-forward real
measure. -/
theorem unitIntervalSecondMomentObjective_eq_realMeasure
    (μ : ProbabilityMeasure UnitInterval1038) :
    unitIntervalSecondMomentObjective μ =
      ∫ t : ℝ, t ^ 2 ∂realMeasure μ := by
  unfold unitIntervalSecondMomentObjective realMeasure
  rw [integral_map]
  · exact continuous_subtype_val.measurable.aemeasurable
  · exact (continuous_pow 2).measurable.aestronglyMeasurable

instance realMeasure.isProbabilityMeasure
    (μ : ProbabilityMeasure UnitInterval1038) :
    IsProbabilityMeasure (realMeasure μ) := by
  dsimp [realMeasure]
  exact Measure.isProbabilityMeasure_map continuous_subtype_val.measurable.aemeasurable

lemma realMeasure_ae_mem_unitInterval
    (μ : ProbabilityMeasure UnitInterval1038) :
    ∀ᵐ t ∂realMeasure μ, t ∈ Icc (-1 : ℝ) 1 := by
  dsimp [realMeasure]
  exact (ae_map_iff
    continuous_subtype_val.measurable.aemeasurable measurableSet_Icc).2
    (Filter.Eventually.of_forall (fun t : UnitInterval1038 => t.2))

theorem realMeasure_ae_mem_support
    (μ : ProbabilityMeasure UnitInterval1038) :
    ∀ᵐ t ∂realMeasure μ, t ∈ (realMeasure μ).support := by
  exact Measure.support_mem_ae

theorem realMeasure_support_open_neighborhood_pos
    (μ : ProbabilityMeasure UnitInterval1038) :
    ∀ t : ℝ, t ∈ (realMeasure μ).support → ∀ U : Set ℝ,
      IsOpen U → t ∈ U → realMeasure μ U ≠ 0 := by
  intro t ht U hU htU hzero
  have hsubset :
      U ⊆ (realMeasure μ).supportᶜ :=
    Measure.subset_compl_support_of_isOpen (μ := realMeasure μ) hU hzero
  exact hsubset htU ht

theorem realMeasure_support_subset_unitInterval
    (μ : ProbabilityMeasure UnitInterval1038) :
    (realMeasure μ).support ⊆ Icc (-1 : ℝ) 1 :=
  Measure.support_subset_of_isClosed isClosed_Icc
    (realMeasure_ae_mem_unitInterval μ)

theorem realMeasure_endpointRemainder_support_in_support
    (μ : ProbabilityMeasure UnitInterval1038) (Support : Set ℝ)
    (hSupport : ∀ᵐ t ∂realMeasure μ, t ∈ Support) :
    ∀ᵐ t ∂(realMeasure μ).restrict ({-1} : Set ℝ)ᶜ, t ∈ Support := by
  exact hSupport.filter_mono (ae_restrict_le)

theorem realMeasure_endpointRemainder_no_endpoint
    (μ : ProbabilityMeasure UnitInterval1038) :
    ∀ᵐ t ∂(realMeasure μ).restrict ({-1} : Set ℝ)ᶜ, t ≠ -1 := by
  have hmem :
      ∀ᵐ t ∂(realMeasure μ).restrict ({-1} : Set ℝ)ᶜ,
        t ∈ ({-1} : Set ℝ)ᶜ :=
    ae_restrict_mem₀ (measurableSet_singleton (-1 : ℝ)).compl.nullMeasurableSet
  filter_upwards [hmem] with t ht
  simpa using ht

theorem realMeasure_endpointRemainder_univ_add_endpoint
    (μ : ProbabilityMeasure UnitInterval1038) :
    (realMeasure μ).restrict ({-1} : Set ℝ)ᶜ Set.univ +
        realMeasure μ ({-1} : Set ℝ) = 1 := by
  have h :=
    measure_add_measure_compl₀
      (μ := realMeasure μ)
      ((measurableSet_singleton (-1 : ℝ)).nullMeasurableSet)
  simpa [add_comm] using h

theorem realMeasure_endpointRemainder_mass
    (μ : ProbabilityMeasure UnitInterval1038) {p : ℝ}
    (hp : realMeasure μ ({-1} : Set ℝ) = ENNReal.ofReal p)
    (hp_nonneg_left : 0 ≤ p) :
    (realMeasure μ).restrict ({-1} : Set ℝ)ᶜ Set.univ =
      ENNReal.ofReal (1 - p) := by
  have hadd :
      (realMeasure μ).restrict ({-1} : Set ℝ)ᶜ Set.univ +
        ENNReal.ofReal p = 1 := by
    simpa [hp] using realMeasure_endpointRemainder_univ_add_endpoint μ
  have hsub :
      (realMeasure μ).restrict ({-1} : Set ℝ)ᶜ Set.univ =
        (1 : ℝ≥0∞) - ENNReal.ofReal p :=
    ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top hadd
  have hofReal :
      ENNReal.ofReal (1 - p) = (1 : ℝ≥0∞) - ENNReal.ofReal p := by
    simpa using (ENNReal.ofReal_sub (1 : ℝ) hp_nonneg_left)
  rw [hsub, ← hofReal]

theorem realMeasure_endpoint_atom_eq_of_unitInterval_endpoint_atom_eq
    (μ : ProbabilityMeasure UnitInterval1038) {p : ℝ}
    (hp :
      (μ : Measure UnitInterval1038)
        {t : UnitInterval1038 | (t : ℝ) = -1} = ENNReal.ofReal p) :
    realMeasure μ ({-1} : Set ℝ) = ENNReal.ofReal p := by
  rw [realMeasure]
  rw [Measure.map_apply continuous_subtype_val.measurable
    (measurableSet_singleton (-1 : ℝ))]
  simpa [Set.preimage, Set.mem_singleton_iff] using hp

theorem unitInterval_endpoint_atom_eq_of_realMeasure_endpoint_atom_eq
    (μ : ProbabilityMeasure UnitInterval1038) {p : ℝ}
    (hp : realMeasure μ ({-1} : Set ℝ) = ENNReal.ofReal p) :
    (μ : Measure UnitInterval1038)
      {t : UnitInterval1038 | (t : ℝ) = -1} = ENNReal.ofReal p := by
  have hmap :
      realMeasure μ ({-1} : Set ℝ) =
        (μ : Measure UnitInterval1038)
          {t : UnitInterval1038 | (t : ℝ) = -1} := by
    rw [realMeasure]
    rw [Measure.map_apply continuous_subtype_val.measurable
      (measurableSet_singleton (-1 : ℝ))]
    rfl
  exact hmap.symm.trans hp

theorem unitInterval_endpoint_atom_ne_top
    (μ : ProbabilityMeasure UnitInterval1038) :
    (μ : Measure UnitInterval1038)
      {t : UnitInterval1038 | (t : ℝ) = -1} ≠ ⊤ := by
  have hle :
      (μ : Measure UnitInterval1038)
        {t : UnitInterval1038 | (t : ℝ) = -1} ≤
        (μ : Measure UnitInterval1038) Set.univ :=
    measure_mono (Set.subset_univ _)
  have hlt :
      (μ : Measure UnitInterval1038)
        {t : UnitInterval1038 | (t : ℝ) = -1} < ⊤ := by
    refine lt_of_le_of_lt hle ?_
    simp
  exact ne_of_lt hlt

theorem unitInterval_endpoint_atom_eq_ofReal_toReal
    (μ : ProbabilityMeasure UnitInterval1038) :
    (μ : Measure UnitInterval1038)
      {t : UnitInterval1038 | (t : ℝ) = -1} =
        ENNReal.ofReal
          (((μ : Measure UnitInterval1038)
            {t : UnitInterval1038 | (t : ℝ) = -1}).toReal) := by
  rw [ENNReal.ofReal_toReal (unitInterval_endpoint_atom_ne_top μ)]

theorem unitInterval_endpoint_atom_toReal_nonneg
    (μ : ProbabilityMeasure UnitInterval1038) :
    0 ≤
      (((μ : Measure UnitInterval1038)
        {t : UnitInterval1038 | (t : ℝ) = -1}).toReal) :=
  ENNReal.toReal_nonneg

theorem unitInterval_endpoint_atom_toReal_le_one
    (μ : ProbabilityMeasure UnitInterval1038) :
    (((μ : Measure UnitInterval1038)
      {t : UnitInterval1038 | (t : ℝ) = -1}).toReal) ≤ 1 := by
  have hle :
      (μ : Measure UnitInterval1038)
        {t : UnitInterval1038 | (t : ℝ) = -1} ≤
        (1 : ℝ≥0∞) := by
    have hle_univ :
        (μ : Measure UnitInterval1038)
          {t : UnitInterval1038 | (t : ℝ) = -1} ≤
          (μ : Measure UnitInterval1038) Set.univ :=
      measure_mono (Set.subset_univ _)
    simpa using hle_univ
  simpa using (ENNReal.toReal_mono ENNReal.one_ne_top hle)

theorem unitInterval_endpoint_atom_remainderMass_nonneg
    (μ : ProbabilityMeasure UnitInterval1038) :
    0 ≤ 1 -
      (((μ : Measure UnitInterval1038)
        {t : UnitInterval1038 | (t : ℝ) = -1}).toReal) := by
  have hle := unitInterval_endpoint_atom_toReal_le_one μ
  linarith

/-- Real points carrying positive mass for the pushed-forward unit-interval measure. -/
def diagonalAtomSet (μ : ProbabilityMeasure UnitInterval1038) : Set ℝ :=
  {x : ℝ | 0 < (μ : Measure UnitInterval1038) {t : UnitInterval1038 | (t : ℝ) = x}}

lemma diagonalAtomSet_countable (μ : ProbabilityMeasure UnitInterval1038) :
    (diagonalAtomSet μ).Countable := by
  simpa [diagonalAtomSet] using
    (Measure.countable_meas_level_set_pos
      (μ := (μ : Measure UnitInterval1038))
      (g := fun t : UnitInterval1038 => (t : ℝ))
      continuous_subtype_val.measurable)

lemma diagonalAtomSet_measurableSet (μ : ProbabilityMeasure UnitInterval1038) :
    MeasurableSet (diagonalAtomSet μ) :=
  (diagonalAtomSet_countable μ).measurableSet

lemma diagonalAtomSet_volume_zero (μ : ProbabilityMeasure UnitInterval1038) :
    volume (diagonalAtomSet μ) = 0 := by
  exact Set.Countable.measure_zero (diagonalAtomSet_countable μ) volume

/--
Positive set enlarged by the diagonal atom set.

The real-valued potential `unitIntervalLogPotential` uses `Real.log`, so a
diagonal logarithmic singularity is not represented as `+∞`.  The finite-atom
selector therefore carries diagonal candidate atoms through this null exceptional
set instead of pretending they lie in the real-valued positive set.
-/
def unitIntervalAugmentedPositiveSet
    (μ : ProbabilityMeasure UnitInterval1038) : Set ℝ :=
  PositiveSet (unitIntervalLogPotential μ) ∪ diagonalAtomSet μ

theorem unitInterval_positiveSet_subset_augmented
    (μ : ProbabilityMeasure UnitInterval1038) :
    PositiveSet (unitIntervalLogPotential μ) ⊆
      unitIntervalAugmentedPositiveSet μ := by
  intro x hx
  exact Or.inl hx

theorem unitInterval_diagonalAtomSet_subset_augmented
    (μ : ProbabilityMeasure UnitInterval1038) :
    diagonalAtomSet μ ⊆ unitIntervalAugmentedPositiveSet μ := by
  intro x hx
  exact Or.inr hx

/--
Adding diagonal atom locations does not change Lebesgue length, since the
diagonal atom set is countable.
-/
theorem unitIntervalAugmentedPositiveSet_volume_eq_positiveSet
    (μ : ProbabilityMeasure UnitInterval1038) :
    volume (unitIntervalAugmentedPositiveSet μ) =
      volume (PositiveSet (unitIntervalLogPotential μ)) := by
  apply le_antisymm
  · calc
      volume (unitIntervalAugmentedPositiveSet μ)
          ≤ volume (PositiveSet (unitIntervalLogPotential μ)) +
              volume (diagonalAtomSet μ) := by
            unfold unitIntervalAugmentedPositiveSet
            exact measure_union_le _ _
      _ = volume (PositiveSet (unitIntervalLogPotential μ)) := by
            simp [diagonalAtomSet_volume_zero μ]
  · exact measure_mono (unitInterval_positiveSet_subset_augmented μ)

theorem unitIntervalAugmentedPositiveSet_lower_bound_transfers
    (μ : ProbabilityMeasure UnitInterval1038) {L : ℝ≥0∞}
    (hL : L ≤ volume (unitIntervalAugmentedPositiveSet μ)) :
    L ≤ volume (PositiveSet (unitIntervalLogPotential μ)) := by
  simpa [unitIntervalAugmentedPositiveSet_volume_eq_positiveSet μ] using hL

lemma ae_ne_of_notMem_diagonalAtomSet
    {μ : ProbabilityMeasure UnitInterval1038} {x : ℝ}
    (hx : x ∉ diagonalAtomSet μ) :
    ∀ᵐ t : UnitInterval1038 ∂(μ : Measure UnitInterval1038), x ≠ (t : ℝ) := by
  have hzero :
      (μ : Measure UnitInterval1038) {t : UnitInterval1038 | (t : ℝ) = x} = 0 := by
    have hnotpos :
        ¬ 0 < (μ : Measure UnitInterval1038)
          {t : UnitInterval1038 | (t : ℝ) = x} := by
      simpa [diagonalAtomSet] using hx
    exact le_antisymm (not_lt.mp hnotpos) bot_le
  rw [ae_iff]
  simpa [Set.compl_setOf, eq_comm] using hzero

lemma unitIntervalLogPotential_eq_map_subtypeVal
    (μ : ProbabilityMeasure UnitInterval1038) (x : ℝ) :
    unitIntervalLogPotential μ x =
      measureLogPotential
        (Measure.map (fun t : UnitInterval1038 => (t : ℝ))
          (μ : Measure UnitInterval1038)) x := by
  unfold unitIntervalLogPotential measureLogPotential
  rw [integral_map]
  · exact continuous_subtype_val.measurable.aemeasurable
  · exact (Real.measurable_log.comp (measurable_const.div
      (continuous_abs.measurable.comp
        (measurable_const.sub measurable_id)))).aestronglyMeasurable

lemma unitIntervalLogPotential_eq_realMeasure
    (μ : ProbabilityMeasure UnitInterval1038) (x : ℝ) :
    unitIntervalLogPotential μ x = measureLogPotential (realMeasure μ) x := by
  simpa [realMeasure] using unitIntervalLogPotential_eq_map_subtypeVal μ x

/-! ## Concrete reflection/translation normalization map -/

/-- Point map used by the concrete Tao normalization: optional reflection,
followed by translation. -/
def taoNormalizePoint (reflected : Bool) (translation x : ℝ) : ℝ :=
  (if reflected then -x else x) + translation

/-- Real push-forward measure under the concrete Tao normalization map. -/
def taoNormalizeRealMeasure
    (μ : ProbabilityMeasure UnitInterval1038) (reflected : Bool) (translation : ℝ) :
    Measure ℝ :=
  Measure.map (taoNormalizePoint reflected translation) (realMeasure μ)

/-- Potential of the concrete normalized real measure. -/
def taoNormalizedPotential
    (μ : ProbabilityMeasure UnitInterval1038) (reflected : Bool) (translation : ℝ) :
    ℝ → ℝ :=
  measureLogPotential (taoNormalizeRealMeasure μ reflected translation)

lemma taoNormalizePoint_false (translation x : ℝ) :
    taoNormalizePoint false translation x = x + translation := by
  rfl

lemma taoNormalizePoint_true (translation x : ℝ) :
    taoNormalizePoint true translation x = -x + translation := by
  rfl

lemma taoNormalizeRealMeasure_false
    (μ : ProbabilityMeasure UnitInterval1038) (translation : ℝ) :
    taoNormalizeRealMeasure μ false translation =
      Measure.map (fun t : ℝ => t + translation) (realMeasure μ) := by
  rfl

lemma taoNormalizeRealMeasure_true
    (μ : ProbabilityMeasure UnitInterval1038) (translation : ℝ) :
    taoNormalizeRealMeasure μ true translation =
      Measure.map (fun t : ℝ => -t + translation) (realMeasure μ) := by
  rfl

lemma measureLogPotential_reflect_translate (μ : Measure ℝ) (x shift : ℝ) :
    measureLogPotential (Measure.map (fun t : ℝ => -t + shift) μ)
      (-x + shift) =
    measureLogPotential μ x := by
  unfold measureLogPotential
  rw [integral_map]
  · apply integral_congr_ae
    filter_upwards with t
    have habs : |-x + shift - (-t + shift)| = |x - t| := by
      rw [show -x + shift - (-t + shift) = -(x - t) by ring]
      exact abs_neg (x - t)
    rw [habs]
  · fun_prop
  · exact (Real.measurable_log.comp (measurable_const.div
      (continuous_abs.measurable.comp
        (measurable_const.sub measurable_id)))).aestronglyMeasurable

theorem taoNormalizedPotential_false_apply
    (μ : ProbabilityMeasure UnitInterval1038) (translation x : ℝ) :
    taoNormalizedPotential μ false translation (x + translation) =
      unitIntervalLogPotential μ x := by
  change measureLogPotential
      (Measure.map (fun t : ℝ => t + translation) (realMeasure μ))
      (x + translation) = unitIntervalLogPotential μ x
  rw [measureLogPotential_translate]
  exact (unitIntervalLogPotential_eq_realMeasure μ x).symm

theorem taoNormalizedPotential_true_apply
    (μ : ProbabilityMeasure UnitInterval1038) (translation x : ℝ) :
    taoNormalizedPotential μ true translation (-x + translation) =
      unitIntervalLogPotential μ x := by
  change measureLogPotential
      (Measure.map (fun t : ℝ => -t + translation) (realMeasure μ))
      (-x + translation) = unitIntervalLogPotential μ x
  rw [measureLogPotential_reflect_translate]
  exact (unitIntervalLogPotential_eq_realMeasure μ x).symm

theorem positiveSet_taoNormalizedPotential_false_eq_preimage
    (μ : ProbabilityMeasure UnitInterval1038) (translation : ℝ) :
    PositiveSet (taoNormalizedPotential μ false translation) =
      (fun y : ℝ => y - translation) ⁻¹'
        PositiveSet (unitIntervalLogPotential μ) := by
  ext y
  constructor
  · intro hy
    have happly := taoNormalizedPotential_false_apply μ translation (y - translation)
    have hy_eq : y - translation + translation = y := by ring
    rw [hy_eq] at happly
    simpa [PositiveSet, happly] using hy
  · intro hy
    have happly := taoNormalizedPotential_false_apply μ translation (y - translation)
    have hy_eq : y - translation + translation = y := by ring
    rw [hy_eq] at happly
    simpa [PositiveSet, happly] using hy

theorem positiveSet_taoNormalizedPotential_true_eq_preimage
    (μ : ProbabilityMeasure UnitInterval1038) (translation : ℝ) :
    PositiveSet (taoNormalizedPotential μ true translation) =
      (fun y : ℝ => -y + translation) ⁻¹'
        PositiveSet (unitIntervalLogPotential μ) := by
  ext y
  constructor
  · intro hy
    have happly := taoNormalizedPotential_true_apply μ translation (-y + translation)
    have hy_eq : -(-y + translation) + translation = y := by ring
    rw [hy_eq] at happly
    simpa [PositiveSet, happly] using hy
  · intro hy
    have happly := taoNormalizedPotential_true_apply μ translation (-y + translation)
    have hy_eq : -(-y + translation) + translation = y := by ring
    rw [hy_eq] at happly
    simpa [PositiveSet, happly] using hy

theorem volume_positiveSet_taoNormalizedPotential_false
    (μ : ProbabilityMeasure UnitInterval1038) (translation : ℝ) :
    volume (PositiveSet (taoNormalizedPotential μ false translation)) =
      volume (PositiveSet (unitIntervalLogPotential μ)) := by
  have hset := positiveSet_taoNormalizedPotential_false_eq_preimage μ translation
  have hmap : Measure.map (fun y : ℝ => y - translation) volume = volume := by
    simpa [sub_eq_add_neg] using
      (map_add_right_eq_self (μ := volume) (-translation))
  have hmeas : NullMeasurableSet (PositiveSet (unitIntervalLogPotential μ)) volume := by
    exact (unitIntervalLogPotential_measurableSet_threshold μ (0 : ℝ)).nullMeasurableSet
  rw [hset]
  exact Measure.measure_preimage_of_map_eq_self hmap hmeas

theorem volume_positiveSet_taoNormalizedPotential_true
    (μ : ProbabilityMeasure UnitInterval1038) (translation : ℝ) :
    volume (PositiveSet (taoNormalizedPotential μ true translation)) =
      volume (PositiveSet (unitIntervalLogPotential μ)) := by
  have hset := positiveSet_taoNormalizedPotential_true_eq_preimage μ translation
  have hmeas : NullMeasurableSet (PositiveSet (unitIntervalLogPotential μ)) volume := by
    exact (unitIntervalLogPotential_measurableSet_threshold μ (0 : ℝ)).nullMeasurableSet
  rw [hset]
  have htranslate :
      volume ((fun y : ℝ => y + translation) ⁻¹'
          PositiveSet (unitIntervalLogPotential μ)) =
        volume (PositiveSet (unitIntervalLogPotential μ)) := by
    exact Measure.measure_preimage_of_map_eq_self
      (map_add_right_eq_self (μ := volume) translation) hmeas
  have hneg :
      volume ((fun y : ℝ => -y + translation) ⁻¹'
          PositiveSet (unitIntervalLogPotential μ)) =
        volume ((fun y : ℝ => y + translation) ⁻¹'
          PositiveSet (unitIntervalLogPotential μ)) := by
    have hpre :
        ((fun y : ℝ => -y + translation) ⁻¹'
          PositiveSet (unitIntervalLogPotential μ)) =
          (fun y : ℝ => (-1 : ℝ) * y) ⁻¹'
            ((fun y : ℝ => y + translation) ⁻¹'
              PositiveSet (unitIntervalLogPotential μ)) := by
      ext y
      simp
    rw [hpre, Real.volume_preimage_mul_left (by norm_num : (-1 : ℝ) ≠ 0)]
    simp
  exact hneg.trans htranslate

theorem volume_positiveSet_taoNormalizedPotential
    (μ : ProbabilityMeasure UnitInterval1038) (reflected : Bool) (translation : ℝ) :
    volume (PositiveSet (taoNormalizedPotential μ reflected translation)) =
      volume (PositiveSet (unitIntervalLogPotential μ)) := by
  cases reflected
  · exact volume_positiveSet_taoNormalizedPotential_false μ translation
  · exact volume_positiveSet_taoNormalizedPotential_true μ translation

/-- Unit-interval version of the boundary Jensen step. -/
theorem one_le_unitInterval_boundary_abs_integral_of_potential_nonpos
    (μ : ProbabilityMeasure UnitInterval1038) {x ε : ℝ}
    (hε : 0 < ε)
    (hdist_lower : ∀ᵐ t ∂realMeasure μ, ε ≤ |x - t|)
    (hdist_int : Integrable (fun t : ℝ => |x - t|) (realMeasure μ))
    (hlog_int : Integrable (fun t : ℝ => Real.log |x - t|) (realMeasure μ))
    (hpotential_nonpos : unitIntervalLogPotential μ x ≤ 0) :
    1 ≤ ∫ t, |x - t| ∂realMeasure μ := by
  rw [unitIntervalLogPotential_eq_realMeasure] at hpotential_nonpos
  exact one_le_abs_integral_of_measureLogPotential_nonpos
    (realMeasure μ) hε hdist_lower hdist_int hlog_int hpotential_nonpos

/--
Tao boundary-average inequality once the boundary Jensen lower bound and the
endpoint/remainder distance upper bound have been supplied.
-/
theorem tao_boundary_average_of_boundary_distance_upper
    (μ : ProbabilityMeasure UnitInterval1038) {xPlus endpointMass ε : ℝ}
    (hε : 0 < ε)
    (hdist_lower : ∀ᵐ t ∂realMeasure μ, ε ≤ |xPlus - t|)
    (hdist_int : Integrable (fun t : ℝ => |xPlus - t|) (realMeasure μ))
    (hlog_int : Integrable (fun t : ℝ => Real.log |xPlus - t|) (realMeasure μ))
    (hpotential_nonpos : unitIntervalLogPotential μ xPlus ≤ 0)
    (hdistance_upper :
      (∫ t, |xPlus - t| ∂realMeasure μ) ≤
        (xPlus + 1) * endpointMass + (1 - xPlus) * (1 - endpointMass)) :
    1 ≤ (xPlus + 1) * endpointMass + (1 - xPlus) * (1 - endpointMass) := by
  exact le_trans
    (one_le_unitInterval_boundary_abs_integral_of_potential_nonpos
      μ hε hdist_lower hdist_int hlog_int hpotential_nonpos)
    hdistance_upper

/--
Endpoint half-mass consequence of the boundary-distance form of Tao's boundary
average inequality.
-/
theorem endpoint_mass_ge_half_of_boundary_distance_upper
    (μ : ProbabilityMeasure UnitInterval1038) {xPlus endpointMass ε : ℝ}
    (hright_endpoint_positive : 0 < xPlus)
    (hε : 0 < ε)
    (hdist_lower : ∀ᵐ t ∂realMeasure μ, ε ≤ |xPlus - t|)
    (hdist_int : Integrable (fun t : ℝ => |xPlus - t|) (realMeasure μ))
    (hlog_int : Integrable (fun t : ℝ => Real.log |xPlus - t|) (realMeasure μ))
    (hpotential_nonpos : unitIntervalLogPotential μ xPlus ≤ 0)
    (hdistance_upper :
      (∫ t, |xPlus - t| ∂realMeasure μ) ≤
        (xPlus + 1) * endpointMass + (1 - xPlus) * (1 - endpointMass)) :
    (1 / 2 : ℝ) ≤ endpointMass := by
  exact endpoint_mass_ge_half_from_boundary_average hright_endpoint_positive
    (tao_boundary_average_of_boundary_distance_upper μ hε hdist_lower
      hdist_int hlog_int hpotential_nonpos hdistance_upper)

/-!
## Finite atomic dual-potential selector

The finite-atom lower-bound route often proves positivity of a finite weighted
dual expression before it has an explicit atom selected inside the actual
positive set of `unitIntervalLogPotential μ`.  The next definitions and
theorems package that last finite selector step.

No Fubini/Tonelli logarithmic duality is asserted here.  The named predicate
`FiniteAtomicUnitIntervalDualityIdentity` records the remaining identity between
the integral of the finite atomic potential and the finite sum of actual
unit-interval log potentials.  Once that identity, or directly the finite dual
sum positivity, is supplied, nonnegative weights force at least one candidate
atom to lie in `PositiveSet (unitIntervalLogPotential μ)`.
-/

/--
Finite weighted dual potential obtained by testing the actual unit-interval
log potential against finitely many candidate atom locations.
-/
def finiteAtomicUnitIntervalDualPotential
    {ι : Type*} [DecidableEq ι]
    (μ : ProbabilityMeasure UnitInterval1038)
    (s : Finset ι) (w atom : ι → ℝ) : ℝ :=
  ∑ i ∈ s, w i * unitIntervalLogPotential μ (atom i)

/--
Named remaining finite duality identity.

This is the finite-atom version of the logarithmic duality still needed by the
route: the integral of the finite weighted atomic potential over the actual
probability measure equals the finite weighted sum of actual potentials at the
candidate atom locations.  This predicate deliberately does not prove that
identity; proving it from integrability/Fubini or a checked finite atomic
package is left outside this selector theorem.
-/
def FiniteAtomicUnitIntervalDualityIdentity
    {ι : Type*} [DecidableEq ι]
    (μ : ProbabilityMeasure UnitInterval1038)
    (s : Finset ι) (w atom : ι → ℝ) : Prop :=
  (∫ x : UnitInterval1038,
      finiteWeightedPotential s w atom (x : ℝ) ∂(μ : Measure UnitInterval1038)) =
    finiteAtomicUnitIntervalDualPotential μ s w atom

/--
Finite atomic duality identity from finite integral linearity.

This closes the purely finite part of the log-potential duality: under explicit
per-atom integrability of the logarithmic kernels on the unit interval, the
integral of the finite weighted atomic potential is exactly the finite weighted
sum of the actual `unitIntervalLogPotential` values.  No global Fubini/Tonelli
identity is assumed here; the remaining analytic hypothesis is the stated
integrability of each atom kernel.
-/
theorem FiniteAtomicUnitIntervalDualityIdentity.of_integrable_atom_kernels
    {ι : Type*} [DecidableEq ι]
    (μ : ProbabilityMeasure UnitInterval1038)
    (s : Finset ι) (w atom : ι → ℝ)
    (hlog_int : ∀ i ∈ s, Integrable
      (fun x : UnitInterval1038 =>
        Real.log (1 / |(x : ℝ) - atom i|))
      (μ : Measure UnitInterval1038)) :
    FiniteAtomicUnitIntervalDualityIdentity μ s w atom := by
  unfold FiniteAtomicUnitIntervalDualityIdentity
  unfold finiteAtomicUnitIntervalDualPotential
  unfold finiteWeightedPotential
  unfold unitIntervalLogPotential
  calc
    (∫ x : UnitInterval1038,
        (∑ i ∈ s, w i * Real.log (1 / |(x : ℝ) - atom i|))
          ∂(μ : Measure UnitInterval1038))
        = ∑ i ∈ s,
            ∫ x : UnitInterval1038,
              w i * Real.log (1 / |(x : ℝ) - atom i|)
                ∂(μ : Measure UnitInterval1038) := by
          exact integral_finset_sum s (fun i _hi => by
            exact (hlog_int i ‹i ∈ s›).const_mul (w i))
    _ = ∑ i ∈ s,
          w i *
            ∫ x : UnitInterval1038,
              Real.log (1 / |(x : ℝ) - atom i|)
                ∂(μ : Measure UnitInterval1038) := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [integral_const_mul]
    _ = ∑ i ∈ s,
          w i *
            ∫ x : UnitInterval1038,
              Real.log (1 / |atom i - (x : ℝ)|)
                ∂(μ : Measure UnitInterval1038) := by
          apply Finset.sum_congr rfl
          intro i _hi
          congr 1
          rw [show
            (fun x : UnitInterval1038 =>
              Real.log (1 / |(x : ℝ) - atom i|)) =
            (fun x : UnitInterval1038 =>
              Real.log (1 / |atom i - (x : ℝ)|)) by
              funext x
              rw [abs_sub_comm]]

/--
Contradiction form of the finite atomic selector.

Remaining assumptions are finite and explicit: the candidate family is a
`Finset`, all weights are nonnegative, and the finite weighted sum of actual
unit-interval potentials is positive.  If every candidate atom is outside the
actual positive set, then every summand is nonpositive, contradicting the
positive finite dual sum.
-/
theorem finiteAtomicUnitIntervalDualPotential_positive_contradicts_no_positive_atom
    {ι : Type*} [DecidableEq ι]
    (μ : ProbabilityMeasure UnitInterval1038)
    (s : Finset ι) (w atom : ι → ℝ)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hdual_pos : 0 < finiteAtomicUnitIntervalDualPotential μ s w atom)
    (hno_positive : ∀ i ∈ s,
      atom i ∉ PositiveSet (unitIntervalLogPotential μ)) :
    False := by
  have hsum_nonpos :
      finiteAtomicUnitIntervalDualPotential μ s w atom ≤ 0 := by
    unfold finiteAtomicUnitIntervalDualPotential
    calc
      ∑ i ∈ s, w i * unitIntervalLogPotential μ (atom i)
          ≤ ∑ i ∈ s, 0 := by
            exact Finset.sum_le_sum (fun i hi => by
              have hpotential_nonpos :
                  unitIntervalLogPotential μ (atom i) ≤ 0 := by
                have hnot_pos :
                    ¬ 0 < unitIntervalLogPotential μ (atom i) := by
                  simpa [PositiveSet] using hno_positive i hi
                exact le_of_not_gt hnot_pos
              exact mul_nonpos_of_nonneg_of_nonpos
                (hw_nonneg i hi) hpotential_nonpos)
      _ = 0 := by simp
  exact not_lt_of_ge hsum_nonpos hdual_pos

/--
Selector form of the finite atomic dual theorem.

From nonnegative finite weights and positivity of the finite weighted sum of
actual `unitIntervalLogPotential μ` values, one candidate atom is selected in
the actual positive set.  This eliminates the separate manual selector
hypothesis `∃ i ∈ s, atom i ∈ PositiveSet ...` from downstream finite-atom
arguments.
-/
theorem finiteAtomicUnitIntervalDualPotential_positive_selects_atom
    {ι : Type*} [DecidableEq ι]
    (μ : ProbabilityMeasure UnitInterval1038)
    (s : Finset ι) (w atom : ι → ℝ)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hdual_pos : 0 < finiteAtomicUnitIntervalDualPotential μ s w atom) :
    ∃ i : ι, i ∈ s ∧
      atom i ∈ PositiveSet (unitIntervalLogPotential μ) := by
  by_contra hnone
  exact finiteAtomicUnitIntervalDualPotential_positive_contradicts_no_positive_atom
    μ s w atom hw_nonneg hdual_pos
    (fun i hi hpos => hnone ⟨i, hi, hpos⟩)

/--
Domain-aware selector form for normalized-support finite atom packages.

If every candidate atom lies in a required domain, for example the normalized
support or sweep domain used by a finite certificate, then the selected atom is
returned together with that domain membership.  The theorem still assumes only
nonnegative finite weights and positivity of the finite actual dual sum; it
does not assume a preselected positive atom.
-/
theorem finiteAtomicUnitIntervalDualPotential_positive_selects_atom_in_domain
    {ι : Type*} [DecidableEq ι]
    (μ : ProbabilityMeasure UnitInterval1038)
    (s : Finset ι) (w atom : ι → ℝ) (Domain : Set ℝ)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hatom_domain : ∀ i ∈ s, atom i ∈ Domain)
    (hdual_pos : 0 < finiteAtomicUnitIntervalDualPotential μ s w atom) :
    ∃ i : ι, i ∈ s ∧ atom i ∈ Domain ∧
      atom i ∈ PositiveSet (unitIntervalLogPotential μ) := by
  rcases finiteAtomicUnitIntervalDualPotential_positive_selects_atom
      μ s w atom hw_nonneg hdual_pos with
    ⟨i, hi, hpos⟩
  exact ⟨i, hi, hatom_domain i hi, hpos⟩

/--
Selector from the named finite duality identity.

This is the intended bridge from finite atomic positivity blocks to the actual
positive-set selector.  The remaining assumptions are exactly stated:
nonnegative weights, the finite duality identity above, and positivity of the
integral of the finite weighted atomic potential over the actual measure.  The
theorem does not claim that the logarithmic duality identity or the integral
positivity has been proved here.
-/
theorem FiniteAtomicUnitIntervalDualityIdentity.selects_atom
    {ι : Type*} [DecidableEq ι]
    {μ : ProbabilityMeasure UnitInterval1038}
    {s : Finset ι} {w atom : ι → ℝ}
    (hduality : FiniteAtomicUnitIntervalDualityIdentity μ s w atom)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hintegral_pos :
      0 < ∫ x : UnitInterval1038,
        finiteWeightedPotential s w atom (x : ℝ)
          ∂(μ : Measure UnitInterval1038)) :
    ∃ i : ι, i ∈ s ∧
      atom i ∈ PositiveSet (unitIntervalLogPotential μ) := by
  refine finiteAtomicUnitIntervalDualPotential_positive_selects_atom
    μ s w atom hw_nonneg ?_
  rwa [← hduality]

/--
Direct selected-atom theorem from finite integral linearity.

This is the assumption-reduced bridge for finite certificates: per-atom
integrability proves the finite atomic duality identity, and positivity of the
integral of the finite weighted atomic potential then selects an atom where the
actual `unitIntervalLogPotential μ` is positive.
-/
theorem finiteAtomicUnitIntervalDuality_integrable_selects_atom
    {ι : Type*} [DecidableEq ι]
    (μ : ProbabilityMeasure UnitInterval1038)
    (s : Finset ι) (w atom : ι → ℝ)
    (hlog_int : ∀ i ∈ s, Integrable
      (fun x : UnitInterval1038 =>
        Real.log (1 / |(x : ℝ) - atom i|))
      (μ : Measure UnitInterval1038))
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hintegral_pos :
      0 < ∫ x : UnitInterval1038,
        finiteWeightedPotential s w atom (x : ℝ)
          ∂(μ : Measure UnitInterval1038)) :
    ∃ i : ι, i ∈ s ∧
      atom i ∈ PositiveSet (unitIntervalLogPotential μ) := by
  exact (FiniteAtomicUnitIntervalDualityIdentity.of_integrable_atom_kernels
    μ s w atom hlog_int).selects_atom hw_nonneg hintegral_pos

/--
Domain-aware selector from the named finite duality identity.

Use this when the finite certificate already proves that all candidate atom
locations lie in the normalized support or sweep domain.  It packages the
duality identity plus finite positivity into a selected candidate atom in the
actual positive set, while carrying the domain membership forward.
-/
theorem FiniteAtomicUnitIntervalDualityIdentity.selects_atom_in_domain
    {ι : Type*} [DecidableEq ι]
    {μ : ProbabilityMeasure UnitInterval1038}
    {s : Finset ι} {w atom : ι → ℝ} {Domain : Set ℝ}
    (hduality : FiniteAtomicUnitIntervalDualityIdentity μ s w atom)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hatom_domain : ∀ i ∈ s, atom i ∈ Domain)
    (hintegral_pos :
      0 < ∫ x : UnitInterval1038,
        finiteWeightedPotential s w atom (x : ℝ)
          ∂(μ : Measure UnitInterval1038)) :
    ∃ i : ι, i ∈ s ∧ atom i ∈ Domain ∧
      atom i ∈ PositiveSet (unitIntervalLogPotential μ) := by
  refine finiteAtomicUnitIntervalDualPotential_positive_selects_atom_in_domain
    μ s w atom Domain hw_nonneg hatom_domain ?_
  rwa [← hduality]

/-- If `x` is outside `[-2,2]` and `t ∈ [-1,1]`, then `|x-t| ≥ 1`. -/
lemma one_le_abs_sub_of_two_le_abs_of_mem_unitInterval
    {x t : ℝ} (hx : (2 : ℝ) ≤ |x|) (ht : t ∈ Icc (-1 : ℝ) 1) :
    (1 : ℝ) ≤ |x - t| := by
  by_cases hxnonneg : 0 ≤ x
  · have hxge : (2 : ℝ) ≤ x := by
      simpa [abs_of_nonneg hxnonneg] using hx
    have hdist : (1 : ℝ) ≤ x - t := by
      linarith [ht.2]
    exact le_trans hdist (le_abs_self (x - t))
  · have hxlt : x < 0 := lt_of_not_ge hxnonneg
    have hxle : x ≤ (-2 : ℝ) := by
      have h : (2 : ℝ) ≤ -x := by
        simpa [abs_of_neg hxlt] using hx
      linarith
    have hdist : (1 : ℝ) ≤ t - x := by
      linarith [ht.1]
    have habs : |x - t| = t - x := by
      have : x - t ≤ -1 := by linarith
      rw [abs_of_neg (lt_of_le_of_lt this (by norm_num))]
      ring
    rw [habs]
    exact hdist

/-- The logarithmic kernel is nonpositive outside the fixed window `[-2,2]`. -/
lemma unitInterval_logKernel_nonpos_of_two_le_abs
    {x : ℝ} (hx : (2 : ℝ) ≤ |x|) (t : UnitInterval1038) :
    Real.log (1 / |x - (t : ℝ)|) ≤ 0 := by
  have hdist : (1 : ℝ) ≤ |x - (t : ℝ)| :=
    one_le_abs_sub_of_two_le_abs_of_mem_unitInterval hx t.2
  have hpos : 0 < |x - (t : ℝ)| := lt_of_lt_of_le zero_lt_one hdist
  have hinv : 1 / |x - (t : ℝ)| ≤ 1 := by
    rw [div_le_iff₀ hpos]
    linarith
  have hlog := Real.log_le_log (one_div_pos.mpr hpos) hinv
  simpa using hlog

/-- The unit-interval potential is nonpositive outside `[-2,2]`. -/
theorem unitIntervalLogPotential_nonpos_of_two_le_abs
    (μ : ProbabilityMeasure UnitInterval1038) {x : ℝ}
    (hx : (2 : ℝ) ≤ |x|) :
    unitIntervalLogPotential μ x ≤ 0 := by
  unfold unitIntervalLogPotential
  have hkernel_cont :
      Continuous (fun t : UnitInterval1038 =>
        Real.log (1 / |x - (t : ℝ)|)) := by
    apply Continuous.log
    · exact continuous_const.div
        ((continuous_const.sub continuous_subtype_val).abs)
        (fun t => by
          have hdist : (1 : ℝ) ≤ |x - (t : ℝ)| :=
            one_le_abs_sub_of_two_le_abs_of_mem_unitInterval hx t.2
          exact ne_of_gt (lt_of_lt_of_le zero_lt_one hdist))
    · intro t hzero
      have hdist : (1 : ℝ) ≤ |x - (t : ℝ)| :=
        one_le_abs_sub_of_two_le_abs_of_mem_unitInterval hx t.2
      have hpos : 0 < |x - (t : ℝ)| := lt_of_lt_of_le zero_lt_one hdist
      exact (div_ne_zero one_ne_zero (ne_of_gt hpos)) hzero
  have hkernel_int :
      Integrable (fun t : UnitInterval1038 =>
        Real.log (1 / |x - (t : ℝ)|)) (μ : Measure UnitInterval1038) := by
    exact hkernel_cont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_univ
        (fun _t _ht => trivial))
  have hzero_int :
      Integrable (fun _t : UnitInterval1038 => (0 : ℝ))
        (μ : Measure UnitInterval1038) := by
    exact integrable_const 0
  have hle_ae :
      (fun t : UnitInterval1038 => Real.log (1 / |x - (t : ℝ)|))
        ≤ᵐ[(μ : Measure UnitInterval1038)]
      (fun _t : UnitInterval1038 => (0 : ℝ)) := by
    filter_upwards with t
    exact unitInterval_logKernel_nonpos_of_two_le_abs hx t
  have hle :
      (∫ t : UnitInterval1038,
        Real.log (1 / |x - (t : ℝ)|) ∂(μ : Measure UnitInterval1038)) ≤
        ∫ _t : UnitInterval1038, (0 : ℝ) ∂(μ : Measure UnitInterval1038) :=
    integral_mono_ae hkernel_int hzero_int hle_ae
  simpa using hle

/-- Every positive threshold set is contained in the fixed finite window `(-2,2)`. -/
theorem unitIntervalLogPotential_threshold_subset_Ioo_neg_two_two
    (μ : ProbabilityMeasure UnitInterval1038) {τ : ℝ} (hτ : 0 ≤ τ) :
    {x : ℝ | τ < unitIntervalLogPotential μ x} ⊆ Ioo (-2 : ℝ) 2 := by
  intro x hx
  have hnot : ¬ (2 : ℝ) ≤ |x| := by
    intro h2
    have hnonpos := unitIntervalLogPotential_nonpos_of_two_le_abs μ h2
    have hgt : τ < unitIntervalLogPotential μ x := hx
    linarith
  have hlt_abs : |x| < 2 := lt_of_not_ge hnot
  rw [abs_lt] at hlt_abs
  exact ⟨hlt_abs.1, hlt_abs.2⟩

/-- In particular, the positive set itself is contained in `(-2,2)`. -/
theorem unitIntervalLogPotential_positiveSet_subset_Ioo_neg_two_two
    (μ : ProbabilityMeasure UnitInterval1038) :
    PositiveSet (unitIntervalLogPotential μ) ⊆ Ioo (-2 : ℝ) 2 := by
  intro x hx
  exact unitIntervalLogPotential_threshold_subset_Ioo_neg_two_two μ
    (show (0 : ℝ) ≤ 0 by rfl) hx

/-- Positive threshold sets have finite Lebesgue measure because they lie in `(-2,2)`. -/
theorem unitIntervalLogPotential_threshold_measure_ne_top
    (μ : ProbabilityMeasure UnitInterval1038) {τ : ℝ} (hτ : 0 ≤ τ) :
    volume {x : ℝ | τ < unitIntervalLogPotential μ x} ≠ ∞ := by
  have hsub :
      {x : ℝ | τ < unitIntervalLogPotential μ x} ⊆ Ioo (-2 : ℝ) 2 :=
    unitIntervalLogPotential_threshold_subset_Ioo_neg_two_two μ hτ
  have hle :
      volume {x : ℝ | τ < unitIntervalLogPotential μ x} ≤
        volume (Ioo (-2 : ℝ) 2) :=
    measure_mono (μ := volume) hsub
  have hfinite_window : volume (Ioo (-2 : ℝ) 2) ≠ ∞ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  exact ne_top_of_le_ne_top hfinite_window hle

/--
Inner-regular compact core for a positive threshold set.  This is the correct
replacement for the impossible `Finset`-core target: finite sets cannot cover a
positive-length threshold set up to arbitrarily small Lebesgue error, but compact
subsets can.
-/
theorem unitIntervalLogPotential_threshold_exists_compact_core
    (μ : ProbabilityMeasure UnitInterval1038) {τ : ℝ} (hτ : 0 ≤ τ)
    (hS : MeasurableSet {x : ℝ | τ < unitIntervalLogPotential μ x})
    (η : NNReal) (hη : 0 < η) :
    ∃ K : Set ℝ,
      K ⊆ {x : ℝ | τ < unitIntervalLogPotential μ x} ∧
      IsCompact K ∧
      volume ({x : ℝ | τ < unitIntervalLogPotential μ x} \ K) ≤
        (η : ℝ≥0∞) := by
  have hfinite :
      volume {x : ℝ | τ < unitIntervalLogPotential μ x} ≠ ∞ :=
    unitIntervalLogPotential_threshold_measure_ne_top μ hτ
  have hη_ne : (η : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (ne_of_gt hη)
  rcases hS.exists_isCompact_diff_lt hfinite hη_ne with
    ⟨K, hKsub, hKcompact, hdiff_lt⟩
  exact ⟨K, hKsub, hKcompact, le_of_lt hdiff_lt⟩

/-- Unconditional compact core for a positive threshold set. -/
theorem unitIntervalLogPotential_threshold_exists_compact_core'
    (μ : ProbabilityMeasure UnitInterval1038) {τ : ℝ} (hτ : 0 ≤ τ)
    (η : NNReal) (hη : 0 < η) :
    ∃ K : Set ℝ,
      K ⊆ {x : ℝ | τ < unitIntervalLogPotential μ x} ∧
      IsCompact K ∧
      volume ({x : ℝ | τ < unitIntervalLogPotential μ x} \ K) ≤
        (η : ℝ≥0∞) := by
  exact unitIntervalLogPotential_threshold_exists_compact_core μ hτ
    (unitIntervalLogPotential_measurableSet_threshold μ τ) η hη

/--
Off-diagonal compact core for a positive threshold set.  The removed diagonal
atom set has Lebesgue measure zero, so the compact core still approximates the
full threshold set in Lebesgue measure while avoiding the only obstruction to
real logarithmic integrability.
-/
theorem unitIntervalLogPotential_threshold_exists_compact_core_offDiagonal
    (μ : ProbabilityMeasure UnitInterval1038) {τ : ℝ} (hτ : 0 ≤ τ)
    (η : NNReal) (hη : 0 < η) :
    ∃ K : Set ℝ,
      K ⊆ {x : ℝ | τ < unitIntervalLogPotential μ x} \ diagonalAtomSet μ ∧
      IsCompact K ∧
      volume ({x : ℝ | τ < unitIntervalLogPotential μ x} \ K) ≤
        (η : ℝ≥0∞) := by
  let S : Set ℝ := {x : ℝ | τ < unitIntervalLogPotential μ x}
  let A : Set ℝ := S \ diagonalAtomSet μ
  have hSmeas : MeasurableSet S :=
    unitIntervalLogPotential_measurableSet_threshold μ τ
  have hAmeas : MeasurableSet A := by
    dsimp [A]
    exact hSmeas.diff (diagonalAtomSet_measurableSet μ)
  have hSfinite : volume S ≠ ∞ :=
    unitIntervalLogPotential_threshold_measure_ne_top μ hτ
  have hAfinite : volume A ≠ ∞ := by
    exact ne_top_of_le_ne_top hSfinite (measure_mono (by
      intro x hx
      exact hx.1))
  have hη_ne : (η : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (ne_of_gt hη)
  rcases hAmeas.exists_isCompact_diff_lt hAfinite hη_ne with
    ⟨K, hKsubA, hKcompact, hdiff_lt⟩
  have hsubset :
      S \ K ⊆ (A \ K) ∪ diagonalAtomSet μ := by
    intro x hx
    by_cases hxdiag : x ∈ diagonalAtomSet μ
    · exact Or.inr hxdiag
    · exact Or.inl ⟨⟨hx.1, hxdiag⟩, hx.2⟩
  have hmeasure :
      volume (S \ K) ≤ volume ((A \ K) ∪ diagonalAtomSet μ) :=
    measure_mono (μ := volume) hsubset
  have hunion :
      volume ((A \ K) ∪ diagonalAtomSet μ) ≤
        volume (A \ K) + volume (diagonalAtomSet μ) :=
    measure_union_le _ _
  have hdiff_le : volume (A \ K) ≤ (η : ℝ≥0∞) := le_of_lt hdiff_lt
  refine ⟨K, ?_, hKcompact, ?_⟩
  · simpa [A, S] using hKsubA
  · calc
      volume ({x : ℝ | τ < unitIntervalLogPotential μ x} \ K)
          = volume (S \ K) := rfl
      _ ≤ volume ((A \ K) ∪ diagonalAtomSet μ) := hmeasure
      _ ≤ volume (A \ K) + volume (diagonalAtomSet μ) := hunion
      _ = volume (A \ K) := by simp [diagonalAtomSet_volume_zero μ]
      _ ≤ (η : ℝ≥0∞) := hdiff_le

structure PositiveComponent (μ : ProbabilityMeasure UnitInterval1038) where
  left : ℝ
  right : ℝ
  left_lt_right : left < right
  interval_pos : Ioo left right ⊆ PositiveSet (unitIntervalLogPotential μ)

/-- Build a positive component package from an open interval contained in the
positive set.  This is the first component-selection bridge: the genuinely hard
part is producing the interval witness from the variation argument. -/
def PositiveComponent.of_interval_subset_positiveSet
    {μ : ProbabilityMeasure UnitInterval1038} {l r : ℝ}
    (hlr : l < r)
    (hpos : Ioo l r ⊆ PositiveSet (unitIntervalLogPotential μ)) :
    PositiveComponent μ where
  left := l
  right := r
  left_lt_right := hlr
  interval_pos := hpos

/-- Existence form of `PositiveComponent.of_interval_subset_positiveSet`. -/
theorem exists_positiveComponent_of_interval_subset_positiveSet
    {μ : ProbabilityMeasure UnitInterval1038} {l r : ℝ}
    (hlr : l < r)
    (hpos : Ioo l r ⊆ PositiveSet (unitIntervalLogPotential μ)) :
    ∃ C : PositiveComponent μ, C.left = l ∧ C.right = r := by
  refine ⟨PositiveComponent.of_interval_subset_positiveSet hlr hpos, rfl, rfl⟩

def PositiveComponent.interval
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ) : Set ℝ :=
  Ioo C.left C.right

lemma PositiveComponent.interval_eq
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ) :
    C.interval = Ioo C.left C.right := rfl

/-- Every packaged positive component already supplies interval endpoints. -/
theorem PositiveComponent.exists_interval_endpoints
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ) :
    ∃ xMinus xPlus : ℝ, C.interval = Ioo xMinus xPlus ∧ xMinus < xPlus := by
  exact ⟨C.left, C.right, rfl, C.left_lt_right⟩

lemma PositiveComponent.measurableSet_interval
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ) :
    MeasurableSet C.interval := by
  rw [C.interval_eq]
  exact isOpen_Ioo.measurableSet

lemma PositiveComponent.pointwise_positive
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    {x : ℝ} (hx : x ∈ C.interval) :
    0 < unitIntervalLogPotential μ x := by
  exact C.interval_pos hx

lemma PositiveComponent.interval_subset_positiveSet
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ) :
    C.interval ⊆ PositiveSet (unitIntervalLogPotential μ) :=
  C.interval_pos

/--
Endpoint criterion for the baseline placement field.  Once the selected
component is known to start strictly left of `-1` and reach at least `0`, it
contains the whole Tao baseline interval `(-1,0)`.
-/
theorem PositiveComponent.baseline_subset_interval_of_left_lt_endpoint_right_nonneg
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    (hleft : C.left < -1)
    (hright : 0 ≤ C.right) :
    Ioo (-1 : ℝ) 0 ⊆ C.interval := by
  intro x hx
  rw [C.interval_eq]
  exact ⟨lt_trans hleft hx.1, lt_of_lt_of_le hx.2 hright⟩

/--
The baseline placement alone forces the right endpoint to be nonnegative.  It
does not force strict positivity: the component could end exactly at `0`.
-/
theorem PositiveComponent.right_nonneg_of_baseline_subset_interval
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    (hbaseline : Ioo (-1 : ℝ) 0 ⊆ C.interval) :
    0 ≤ C.right := by
  by_contra hnot
  have hright_neg : C.right < 0 := lt_of_not_ge hnot
  let x : ℝ := C.right / 2
  have hx_base : x ∈ Ioo (-1 : ℝ) 0 := by
    constructor
    · have hleft_lt_right : -1 < C.right := by
        have hmid : (-(1 : ℝ) / 2) ∈ Ioo (-1 : ℝ) 0 := by norm_num
        have hmem := hbaseline hmid
        rw [C.interval_eq] at hmem
        exact lt_trans (by norm_num : (-1 : ℝ) < -(1 : ℝ) / 2) hmem.2
      dsimp [x]
      linarith
    · dsimp [x]
      linarith
  have hx_interval := hbaseline hx_base
  rw [C.interval_eq] at hx_interval
  have hx_ge_right : C.right ≤ x := by
    dsimp [x]
    linarith
  exact not_lt_of_ge hx_ge_right hx_interval.2

/--
Strict right-endpoint positivity from an actual positive point in the selected
component.  This is the exact extra witness needed beyond baseline placement.
-/
theorem PositiveComponent.right_pos_of_pos_mem_interval
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    {x : ℝ} (hxpos : 0 < x) (hx : x ∈ C.interval) :
    0 < C.right := by
  rw [C.interval_eq] at hx
  exact lt_trans hxpos hx.2

/--
Maximal-open-interval formulation for the selected positive component.

This is the topological interface needed by the Tao reduction: any open
interval contained in the positive set and intersecting the selected component
is already part of the selected component.  It is deliberately a predicate,
not a new component structure.
-/
def PositiveComponent.IntervalMaximal
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ) : Prop :=
  ∀ l r : ℝ, l < r →
    Ioo l r ⊆ PositiveSet (unitIntervalLogPotential μ) →
    (Ioo l r ∩ C.interval).Nonempty →
      Ioo l r ⊆ C.interval

/--
The local component-selection bridge for the endpoint `-1`.

If the selected positive component contains the right baseline `(-1,0)`, the
endpoint `-1` is positive, and a left neighbourhood of `-1` is positive, then
maximality of the selected component forces the whole left neighbourhood
`(-1-ε,-1)` into the same component.  This is the formal open-left-cover step
needed before feeding the component into the atomized right-region package.

The theorem does not prove endpoint positivity or component maximality; it
isolates the exact topological step once those analytic inputs are available.
-/
theorem PositiveComponent.left_open_cover_of_intervalMaximal
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    {ε : ℝ}
    (hε : 0 < ε)
    (hmax : C.IntervalMaximal)
    (hbaseline : Ioo (-1 : ℝ) 0 ⊆ C.interval)
    (hleft_pos : Ioo (-(1 : ℝ) - ε) (-1) ⊆
      PositiveSet (unitIntervalLogPotential μ))
    (hendpoint_pos : (-1 : ℝ) ∈ PositiveSet (unitIntervalLogPotential μ)) :
    Ioo (-(1 : ℝ) - ε) (-1) ⊆ C.interval := by
  intro y hy
  have hleft_endpoint_lt : -(1 : ℝ) - ε < -1 := by
    linarith
  let l : ℝ := ((-(1 : ℝ) - ε) + y) / 2
  have hl_lower : -(1 : ℝ) - ε < l := by
    dsimp [l]
    linarith [hy.1]
  have hl_y : l < y := by
    dsimp [l]
    linarith [hy.1]
  have hy_mhalf : y < (-(1 : ℝ) / 2) := by
    linarith [hy.2]
  have hl_mthreequarter : l < (-(3 : ℝ) / 4) := by
    have hl_lt_neg_one : l < -1 := by
      dsimp [l]
      linarith [hy.2, hleft_endpoint_lt]
    linarith
  have hJ_pos :
      Ioo l (-(1 : ℝ) / 2) ⊆ PositiveSet (unitIntervalLogPotential μ) := by
    intro q hq
    by_cases hq_left : q < -1
    · exact hleft_pos ⟨lt_trans hl_lower hq.1, hq_left⟩
    · have hq_ge : -1 ≤ q := le_of_not_gt hq_left
      by_cases hq_endpoint : q = -1
      · simpa [hq_endpoint] using hendpoint_pos
      · have hq_base_left : -1 < q := lt_of_le_of_ne hq_ge (Ne.symm hq_endpoint)
        have hq_base_right : q < 0 := by linarith [hq.2]
        exact C.interval_subset_positiveSet
          (hbaseline ⟨hq_base_left, hq_base_right⟩)
  have hJ_inter : (Ioo l (-(1 : ℝ) / 2) ∩ C.interval).Nonempty := by
    refine ⟨-(3 : ℝ) / 4, ?_⟩
    constructor
    · exact ⟨hl_mthreequarter, by norm_num⟩
    · exact hbaseline (by norm_num)
  have hJ_subset :
      Ioo l (-(1 : ℝ) / 2) ⊆ C.interval :=
    hmax l (-(1 : ℝ) / 2) (by linarith [hl_y, hy_mhalf]) hJ_pos hJ_inter
  exact hJ_subset ⟨hl_y, hy_mhalf⟩

/--
Augmented maximal-open-interval formulation for the selected component.

This is the version that matches the real-valued logarithmic potential used in
this file.  Diagonal atoms are carried by `unitIntervalAugmentedPositiveSet`,
because `Real.log` does not model the endpoint singularity as `+∞`.
-/
def PositiveComponent.AugmentedIntervalMaximal
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ) : Prop :=
  ∀ l r : ℝ, l < r →
    Ioo l r ⊆ unitIntervalAugmentedPositiveSet μ →
    (Ioo l r ∩ C.interval).Nonempty →
      Ioo l r ⊆ C.interval

/--
An augmented-maximal selected component is maximal for ordinary positive
intervals.  This is the bridge from the pole-as-win component selection used in
the real-valued formalization back to the ordinary positive-component API.
-/
theorem PositiveComponent.intervalMaximal_of_augmentedIntervalMaximal
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    (hmax : C.AugmentedIntervalMaximal) :
    C.IntervalMaximal := by
  intro l r hlr hpos hinter
  exact hmax l r hlr
    (fun x hx => unitInterval_positiveSet_subset_augmented μ (hpos hx))
    hinter

/--
Augmented open-left-cover bridge.

This is the usable component-selection bridge when the endpoint `-1` is carried
as a diagonal atom rather than as a real-valued positive-potential point.  If a
maximal augmented interval containing the right baseline also has an augmented
left neighbourhood of `-1`, then that left neighbourhood belongs to the same
selected component.
-/
theorem PositiveComponent.left_open_cover_of_augmentedIntervalMaximal
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    {ε : ℝ}
    (hε : 0 < ε)
    (hmax : C.AugmentedIntervalMaximal)
    (hbaseline : Ioo (-1 : ℝ) 0 ⊆ C.interval)
    (hleft_aug : Ioo (-(1 : ℝ) - ε) (-1) ⊆
      unitIntervalAugmentedPositiveSet μ)
    (hendpoint_aug : (-1 : ℝ) ∈ unitIntervalAugmentedPositiveSet μ) :
    Ioo (-(1 : ℝ) - ε) (-1) ⊆ C.interval := by
  intro y hy
  have hleft_endpoint_lt : -(1 : ℝ) - ε < -1 := by
    linarith
  let l : ℝ := ((-(1 : ℝ) - ε) + y) / 2
  have hl_lower : -(1 : ℝ) - ε < l := by
    dsimp [l]
    linarith [hy.1]
  have hl_y : l < y := by
    dsimp [l]
    linarith [hy.1]
  have hy_mhalf : y < (-(1 : ℝ) / 2) := by
    linarith [hy.2]
  have hl_mthreequarter : l < (-(3 : ℝ) / 4) := by
    have hl_lt_neg_one : l < -1 := by
      dsimp [l]
      linarith [hy.2, hleft_endpoint_lt]
    linarith
  have hJ_aug :
      Ioo l (-(1 : ℝ) / 2) ⊆ unitIntervalAugmentedPositiveSet μ := by
    intro q hq
    by_cases hq_left : q < -1
    · exact hleft_aug ⟨lt_trans hl_lower hq.1, hq_left⟩
    · have hq_ge : -1 ≤ q := le_of_not_gt hq_left
      by_cases hq_endpoint : q = -1
      · simpa [hq_endpoint] using hendpoint_aug
      · have hq_base_left : -1 < q := lt_of_le_of_ne hq_ge (Ne.symm hq_endpoint)
        have hq_base_right : q < 0 := by linarith [hq.2]
        exact unitInterval_positiveSet_subset_augmented μ
          (C.interval_subset_positiveSet
            (hbaseline ⟨hq_base_left, hq_base_right⟩))
  have hJ_inter : (Ioo l (-(1 : ℝ) / 2) ∩ C.interval).Nonempty := by
    refine ⟨-(3 : ℝ) / 4, ?_⟩
    constructor
    · exact ⟨hl_mthreequarter, by norm_num⟩
    · exact hbaseline (by norm_num)
  have hJ_subset :
      Ioo l (-(1 : ℝ) / 2) ⊆ C.interval :=
    hmax l (-(1 : ℝ) / 2) (by linarith [hl_y, hy_mhalf]) hJ_aug hJ_inter
  exact hJ_subset ⟨hl_y, hy_mhalf⟩

/--
Endpoint-atom version of the augmented open-left-cover bridge.

This is the form closest to the normalized endpoint reduction: if `-1` has
positive mass, then it is in `diagonalAtomSet μ`, hence in the augmented
positive set.  A real-valued positive left neighbourhood is also an augmented
left neighbourhood, so augmented maximality selects the same component.
-/
theorem PositiveComponent.left_open_cover_of_augmentedIntervalMaximal_endpointAtom
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    {ε : ℝ}
    (hε : 0 < ε)
    (hmax : C.AugmentedIntervalMaximal)
    (hbaseline : Ioo (-1 : ℝ) 0 ⊆ C.interval)
    (hleft_pos : Ioo (-(1 : ℝ) - ε) (-1) ⊆
      PositiveSet (unitIntervalLogPotential μ))
    (hendpoint_atom :
      0 < (μ : Measure UnitInterval1038)
        {t : UnitInterval1038 | (t : ℝ) = -1}) :
    Ioo (-(1 : ℝ) - ε) (-1) ⊆ C.interval := by
  refine C.left_open_cover_of_augmentedIntervalMaximal hε hmax hbaseline ?_ ?_
  · intro x hx
    exact unitInterval_positiveSet_subset_augmented μ (hleft_pos hx)
  · exact unitInterval_diagonalAtomSet_subset_augmented μ
      (by simpa [diagonalAtomSet] using hendpoint_atom)

/--
Endpoint membership from augmented maximality.

The endpoint `-1` is not usually a point of the real-valued positive set, but if
it is a diagonal atom and the selected component is maximal for the augmented
positive set, then the same interval-gluing argument places `-1` inside the
selected component.
-/
theorem PositiveComponent.endpoint_mem_of_augmentedIntervalMaximal_endpointAtom
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    {ε : ℝ}
    (hε : 0 < ε)
    (hmax : C.AugmentedIntervalMaximal)
    (hbaseline : Ioo (-1 : ℝ) 0 ⊆ C.interval)
    (hleft_pos : Ioo (-(1 : ℝ) - ε) (-1) ⊆
      PositiveSet (unitIntervalLogPotential μ))
    (hendpoint_atom :
      0 < (μ : Measure UnitInterval1038)
        {t : UnitInterval1038 | (t : ℝ) = -1}) :
    (-1 : ℝ) ∈ C.interval := by
  have hleft_aug : Ioo (-(1 : ℝ) - ε) (-1) ⊆
      unitIntervalAugmentedPositiveSet μ := by
    intro x hx
    exact unitInterval_positiveSet_subset_augmented μ (hleft_pos hx)
  have hendpoint_aug : (-1 : ℝ) ∈ unitIntervalAugmentedPositiveSet μ :=
    unitInterval_diagonalAtomSet_subset_augmented μ
      (by simpa [diagonalAtomSet] using hendpoint_atom)
  have hJ_aug :
      Ioo (-(1 : ℝ) - ε) (-(1 : ℝ) / 2) ⊆
        unitIntervalAugmentedPositiveSet μ := by
    intro q hq
    by_cases hq_left : q < -1
    · exact hleft_aug ⟨hq.1, hq_left⟩
    · have hq_ge : -1 ≤ q := le_of_not_gt hq_left
      by_cases hq_endpoint : q = -1
      · simpa [hq_endpoint] using hendpoint_aug
      · have hq_base_left : -1 < q := lt_of_le_of_ne hq_ge (Ne.symm hq_endpoint)
        have hq_base_right : q < 0 := by linarith [hq.2]
        exact unitInterval_positiveSet_subset_augmented μ
          (C.interval_subset_positiveSet
            (hbaseline ⟨hq_base_left, hq_base_right⟩))
  have hJ_inter :
      (Ioo (-(1 : ℝ) - ε) (-(1 : ℝ) / 2) ∩ C.interval).Nonempty := by
    refine ⟨-(3 : ℝ) / 4, ?_⟩
    constructor
    · constructor
      · linarith [hε]
      · norm_num
    · exact hbaseline (by norm_num)
  have hJ_subset :
      Ioo (-(1 : ℝ) - ε) (-(1 : ℝ) / 2) ⊆ C.interval :=
    hmax (-(1 : ℝ) - ε) (-(1 : ℝ) / 2)
      (by linarith [hε]) hJ_aug hJ_inter
  exact hJ_subset (by constructor <;> norm_num [hε])

/--
Combined component-selection conclusion around the endpoint.

Under augmented maximality, endpoint atom mass, right-baseline membership, and a
positive left neighbourhood, the whole open interval `(-1-ε,0)` lies in the
selected component.  This is the most convenient local component-selection
form for the later endpoint-normalization package.
-/
theorem PositiveComponent.endpoint_neighborhood_subset_of_augmentedIntervalMaximal_endpointAtom
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    {ε : ℝ}
    (hε : 0 < ε)
    (hmax : C.AugmentedIntervalMaximal)
    (hbaseline : Ioo (-1 : ℝ) 0 ⊆ C.interval)
    (hleft_pos : Ioo (-(1 : ℝ) - ε) (-1) ⊆
      PositiveSet (unitIntervalLogPotential μ))
    (hendpoint_atom :
      0 < (μ : Measure UnitInterval1038)
        {t : UnitInterval1038 | (t : ℝ) = -1}) :
    Ioo (-(1 : ℝ) - ε) 0 ⊆ C.interval := by
  intro x hx
  by_cases hx_left : x < -1
  · exact C.left_open_cover_of_augmentedIntervalMaximal_endpointAtom
      hε hmax hbaseline hleft_pos hendpoint_atom ⟨hx.1, hx_left⟩
  · have hx_ge : -1 ≤ x := le_of_not_gt hx_left
    by_cases hx_endpoint : x = -1
    · simpa [hx_endpoint] using
        C.endpoint_mem_of_augmentedIntervalMaximal_endpointAtom
          hε hmax hbaseline hleft_pos hendpoint_atom
    · have hx_base_left : -1 < x := lt_of_le_of_ne hx_ge (Ne.symm hx_endpoint)
      exact hbaseline ⟨hx_base_left, hx.2⟩

theorem PositiveComponent.endpoint_neighborhood_subset_component_of_augmentedIntervalMaximal_endpointAtom
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    {component : Set ℝ} {ε : ℝ}
    (hcomponent : component = C.interval)
    (hε : 0 < ε)
    (hmax : C.AugmentedIntervalMaximal)
    (hbaseline : Ioo (-1 : ℝ) 0 ⊆ C.interval)
    (hleft_pos : Ioo (-(1 : ℝ) - ε) (-1) ⊆
      PositiveSet (unitIntervalLogPotential μ))
    (hendpoint_atom :
      0 < (μ : Measure UnitInterval1038)
        {t : UnitInterval1038 | (t : ℝ) = -1}) :
    Ioo (-(1 : ℝ) - ε) 0 ⊆ component := by
  intro x hx
  rw [hcomponent]
  exact C.endpoint_neighborhood_subset_of_augmentedIntervalMaximal_endpointAtom
    hε hmax hbaseline hleft_pos hendpoint_atom hx

def componentBlock
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ) : Measure ℝ :=
  (realMeasure μ).restrict C.interval

def componentMass
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ) : ℝ≥0∞ :=
  realMeasure μ C.interval

def componentBarycenter
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ) : ℝ :=
  (∫ t : ℝ, t ∂componentBlock C) / (componentMass C).toReal

def componentReplacementMeasure
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ) : Measure ℝ :=
  (realMeasure μ).restrict C.intervalᶜ +
    componentMass C • Measure.dirac (componentBarycenter C)

/--
Subtype probability measure obtained from the real replacement measure once its
mass on the normalized interval is known to be one.

This is the measure-construction part of the barycenter replacement.  The
remaining analytic obligations are exactly the hypotheses that the replacement
measure stays on `[-1,1]` with total mass one.
-/
noncomputable def componentReplacementProbability
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    (hmass_unit :
      componentReplacementMeasure C (Icc (-1 : ℝ) 1) = 1) :
    ProbabilityMeasure UnitInterval1038 :=
  ⟨Measure.comap (fun t : UnitInterval1038 => (t : ℝ))
      (componentReplacementMeasure C), by
    refine ⟨?_⟩
    rw [Measure.comap_apply (fun t : UnitInterval1038 => (t : ℝ))
      Subtype.coe_injective
      (fun s hs => MeasurableSet.subtype_image measurableSet_Icc hs)
      (componentReplacementMeasure C) MeasurableSet.univ]
    simpa [UnitInterval1038] using hmass_unit⟩

/-- The underlying measure of `componentReplacementProbability` is the subtype
comap of the real replacement measure. -/
theorem componentReplacementProbability_toMeasure
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    (hmass_unit :
      componentReplacementMeasure C (Icc (-1 : ℝ) 1) = 1) :
    (componentReplacementProbability C hmass_unit : Measure UnitInterval1038) =
      Measure.comap (fun t : UnitInterval1038 => (t : ℝ))
        (componentReplacementMeasure C) := rfl

/--
The replacement probability is admissible for the concrete compact admissible
class used in this file, namely all probability measures on `[-1,1]`.
-/
theorem componentReplacementProbability_admissibleProbability
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    (hmass_unit :
      componentReplacementMeasure C (Icc (-1 : ℝ) 1) = 1) :
    (componentReplacementProbability C hmass_unit : AdmissibleProbability1038) =
      componentReplacementProbability C hmass_unit := rfl

/--
If the real replacement measure is supported on the normalized interval, then
the real pushforward of its subtype probability representative is exactly the
real replacement measure.
-/
theorem realMeasure_componentReplacementProbability_eq_of_ae_mem_unitInterval
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    (hmass_unit :
      componentReplacementMeasure C (Icc (-1 : ℝ) 1) = 1)
    (hsupport :
      ∀ᵐ x ∂componentReplacementMeasure C, x ∈ Icc (-1 : ℝ) 1) :
    realMeasure (componentReplacementProbability C hmass_unit) =
      componentReplacementMeasure C := by
  unfold realMeasure
  rw [componentReplacementProbability_toMeasure]
  rw [map_comap_subtype_coe measurableSet_Icc]
  exact Measure.restrict_eq_self_of_ae_mem hsupport

structure ComponentReplacement
    (μ : ProbabilityMeasure UnitInterval1038) (C : PositiveComponent μ) where
  mass_pos : 0 < componentMass C
  mass_ne_top : componentMass C ≠ ⊤

/--
The component block normalized to total mass one.

This is the measure to which the existing measure-level Jensen theorem applies.
The normalization is only useful under `ComponentReplacement.mass_pos` and
`ComponentReplacement.mass_ne_top`.
-/
def normalizedComponentBlock
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ) : Measure ℝ :=
  (componentMass C)⁻¹ • componentBlock C

lemma componentBlock_univ
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ) :
    componentBlock C Set.univ = componentMass C := by
  simp [componentBlock, componentMass]

lemma normalizedComponentBlock_univ
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C) :
    normalizedComponentBlock C Set.univ = 1 := by
  have hmass_ne_zero : componentMass C ≠ 0 := ne_of_gt R.mass_pos
  simp [normalizedComponentBlock, componentBlock_univ,
    ENNReal.inv_mul_cancel hmass_ne_zero R.mass_ne_top]

theorem ComponentReplacement.normalizedComponentBlock_isProbabilityMeasure
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C) :
    IsProbabilityMeasure (normalizedComponentBlock C) :=
  ⟨normalizedComponentBlock_univ R⟩

lemma normalizedComponentBlock_integral_eq_barycenter
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C) :
    (∫ t : ℝ, t ∂normalizedComponentBlock C) = componentBarycenter C := by
  have hmass_ne_zero : componentMass C ≠ 0 := ne_of_gt R.mass_pos
  have hmass_toReal_pos : 0 < (componentMass C).toReal :=
    ENNReal.toReal_pos hmass_ne_zero R.mass_ne_top
  unfold normalizedComponentBlock componentBarycenter
  rw [integral_smul_measure]
  rw [ENNReal.toReal_inv]
  rw [smul_eq_mul]
  field_simp [hmass_toReal_pos.ne']

lemma componentBlock_ae_mem_interval
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ) :
    ∀ᵐ t : ℝ ∂componentBlock C, t ∈ C.interval := by
  unfold componentBlock
  exact ae_restrict_mem₀ C.measurableSet_interval.nullMeasurableSet

/--
The component block has finite first moment automatically.  It is the
restriction of the pushed-forward unit-interval probability measure, whose
support is a.e. contained in `[-1,1]`, so the identity is bounded by `1` on the
block.
-/
theorem componentBlock_firstMoment_integrable
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ) :
    Integrable (fun t : ℝ => t) (componentBlock C) := by
  have hsupp : ∀ᵐ t : ℝ ∂componentBlock C, t ∈ Icc (-1 : ℝ) 1 := by
    unfold componentBlock
    refine (ae_restrict_iff' C.measurableSet_interval).2 ?_
    filter_upwards [realMeasure_ae_mem_unitInterval μ] with t ht _htC
    exact ht
  haveI : IsFiniteMeasure (componentBlock C) := by
    unfold componentBlock
    infer_instance
  have hconst : Integrable (fun _ : ℝ => (1 : ℝ)) (componentBlock C) :=
    integrable_const (1 : ℝ)
  refine hconst.mono' measurable_id.aestronglyMeasurable ?_
  filter_upwards [hsupp] with t ht
  have ht_abs : |t| ≤ 1 := abs_le.mpr ht
  simpa [Real.norm_eq_abs] using ht_abs

/-- The component block has finite second moment, again by unit-interval
support. -/
theorem componentBlock_secondMoment_integrable
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ) :
    Integrable (fun t : ℝ => t ^ 2) (componentBlock C) := by
  have hsupp : ∀ᵐ t : ℝ ∂componentBlock C, t ∈ Icc (-1 : ℝ) 1 := by
    unfold componentBlock
    refine (ae_restrict_iff' C.measurableSet_interval).2 ?_
    filter_upwards [realMeasure_ae_mem_unitInterval μ] with t ht _htC
    exact ht
  haveI : IsFiniteMeasure (componentBlock C) := by
    unfold componentBlock
    infer_instance
  have hconst : Integrable (fun _ : ℝ => (1 : ℝ)) (componentBlock C) :=
    integrable_const (1 : ℝ)
  refine hconst.mono' (by fun_prop : AEStronglyMeasurable (fun t : ℝ => t ^ 2) (componentBlock C)) ?_
  filter_upwards [hsupp] with t ht
  have hsq_nonneg : 0 ≤ t ^ 2 := sq_nonneg t
  have hsq_le : t ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (t - 1), sq_nonneg (t + 1), ht.1, ht.2]
  have hsq : |t ^ 2| ≤ 1 := by
    simpa [abs_of_nonneg hsq_nonneg] using hsq_le
  simpa [Real.norm_eq_abs] using hsq

/-- The outside part also has finite second moment by unit-interval support. -/
theorem outsideComponent_secondMoment_integrable
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ) :
    Integrable (fun t : ℝ => t ^ 2)
      ((realMeasure μ).restrict C.intervalᶜ) := by
  have hsupp :
      ∀ᵐ t : ℝ ∂(realMeasure μ).restrict C.intervalᶜ,
        t ∈ Icc (-1 : ℝ) 1 := by
    refine (ae_restrict_iff' C.measurableSet_interval.compl).2 ?_
    filter_upwards [realMeasure_ae_mem_unitInterval μ] with t ht _htC
    exact ht
  haveI : IsFiniteMeasure ((realMeasure μ).restrict C.intervalᶜ) := by
    infer_instance
  have hconst :
      Integrable (fun _ : ℝ => (1 : ℝ))
        ((realMeasure μ).restrict C.intervalᶜ) :=
    integrable_const (1 : ℝ)
  refine hconst.mono' (by fun_prop : AEStronglyMeasurable (fun t : ℝ => t ^ 2)
    ((realMeasure μ).restrict C.intervalᶜ)) ?_
  filter_upwards [hsupp] with t ht
  have hsq_nonneg : 0 ≤ t ^ 2 := sq_nonneg t
  have hsq_le : t ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (t - 1), sq_nonneg (t + 1), ht.1, ht.2]
  have hsq : |t ^ 2| ≤ 1 := by
    simpa [abs_of_nonneg hsq_nonneg] using hsq_le
  simpa [Real.norm_eq_abs] using hsq

lemma normalizedComponentBlock_ae_mem_interval
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (_R : ComponentReplacement μ C) :
    ∀ᵐ t : ℝ ∂normalizedComponentBlock C, t ∈ C.interval := by
  exact (componentBlock_ae_mem_interval C).filter_mono
    (Measure.ae_mono' Measure.smul_absolutelyContinuous)

lemma componentMass_ne_top
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ) :
    componentMass C ≠ ⊤ := by
  haveI : IsFiniteMeasure (realMeasure μ) := by infer_instance
  exact ne_of_lt (measure_lt_top (realMeasure μ) C.interval)

/-- Construct component-replacement data from the only nontrivial mass input:
the selected component has positive `realMeasure` mass.  Finiteness is automatic
because `realMeasure μ` is a finite probability measure. -/
def ComponentReplacement.of_mass_pos
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    (hmass_pos : 0 < componentMass C) :
    ComponentReplacement μ C where
  mass_pos := hmass_pos
  mass_ne_top := componentMass_ne_top C

lemma componentReplacementMeasure_def
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ) :
    componentReplacementMeasure C =
      (realMeasure μ).restrict C.intervalᶜ +
        componentMass C • Measure.dirac (componentBarycenter C) := rfl

def componentReplacementPotential
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ) : ℝ → ℝ :=
  measureLogPotential (componentReplacementMeasure C)

/--
Potential equality for the subtype replacement probability.  The only remaining
side condition is the natural support statement that the real replacement
measure stays inside `[-1,1]`.
-/
theorem unitIntervalLogPotential_componentReplacementProbability_eq
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    (hmass_unit :
      componentReplacementMeasure C (Icc (-1 : ℝ) 1) = 1)
    (hsupport :
      ∀ᵐ x ∂componentReplacementMeasure C, x ∈ Icc (-1 : ℝ) 1) :
    unitIntervalLogPotential (componentReplacementProbability C hmass_unit) =
      componentReplacementPotential C := by
  funext x
  rw [unitIntervalLogPotential_eq_realMeasure]
  rw [realMeasure_componentReplacementProbability_eq_of_ae_mem_unitInterval
    C hmass_unit hsupport]
  rfl

theorem componentReplacement_potential_eq_outside_add_replacementAtom
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    (x : ℝ)
    (houtside_integrable : Integrable
      (fun t : ℝ => Real.log (1 / |x - t|))
      ((realMeasure μ).restrict C.intervalᶜ)) :
    componentReplacementPotential C x =
      measureLogPotential ((realMeasure μ).restrict C.intervalᶜ) x +
        (componentMass C).toReal *
          Real.log (1 / |x - componentBarycenter C|) := by
  have hdirac_integrable : Integrable
      (fun t : ℝ => Real.log (1 / |x - t|))
      (componentMass C • Measure.dirac (componentBarycenter C)) := by
    exact (integrable_dirac (by simp)).smul_measure (componentMass_ne_top C)
  unfold componentReplacementPotential measureLogPotential
  rw [componentReplacementMeasure_def]
  rw [integral_add_measure houtside_integrable hdirac_integrable]
  · rw [integral_smul_measure]
    simp [smul_eq_mul]

/--
Original-potential decomposition into the unchanged outside contribution and
the selected component block.

This is the original-side analogue of
`componentReplacement_potential_eq_outside_add_replacementAtom`: the real
measure splits as its restriction to `C.intervalᶜ` plus its restriction to
`C.interval`, namely `componentBlock C`.
-/
theorem unitIntervalLogPotential_eq_outside_add_componentBlock
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    (x : ℝ)
    (houtside_integrable : Integrable
      (fun t : ℝ => Real.log (1 / |x - t|))
      ((realMeasure μ).restrict C.intervalᶜ))
    (hblock_integrable : Integrable
      (fun t : ℝ => Real.log (1 / |x - t|)) (componentBlock C)) :
    unitIntervalLogPotential μ x =
      measureLogPotential ((realMeasure μ).restrict C.intervalᶜ) x +
        ∫ t : ℝ, Real.log (1 / |x - t|) ∂componentBlock C := by
  have hsplit :
      (realMeasure μ).restrict C.intervalᶜ + componentBlock C = realMeasure μ := by
    unfold componentBlock
    exact Measure.restrict_compl_add_restrict C.measurableSet_interval
  calc
    unitIntervalLogPotential μ x = measureLogPotential (realMeasure μ) x := by
      exact unitIntervalLogPotential_eq_realMeasure μ x
    _ = measureLogPotential
        ((realMeasure μ).restrict C.intervalᶜ + componentBlock C) x := by
      rw [hsplit]
    _ = measureLogPotential ((realMeasure μ).restrict C.intervalᶜ) x +
        ∫ t : ℝ, Real.log (1 / |x - t|) ∂componentBlock C := by
      unfold measureLogPotential
      rw [integral_add_measure houtside_integrable hblock_integrable]

lemma replacement_positiveSet_subset_original_of_outside_le
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    {U' : ℝ → ℝ}
    (houtside : ∀ x : ℝ, x ∉ C.interval →
      U' x ≤ unitIntervalLogPotential μ x) :
    PositiveSet U' ⊆ PositiveSet (unitIntervalLogPotential μ) := by
  intro x hx
  by_cases hxC : x ∈ C.interval
  · exact C.interval_subset_positiveSet hxC
  · exact lt_of_lt_of_le hx (houtside x hxC)

def StrictOutsideComponent
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ) (x : ℝ) : Prop :=
  x < C.left ∨ C.right < x

/--
Function-level original-side decomposition lower bound for the
decomposition-plus-Jensen objective bridge.

If `outsidePart` is bounded by the concrete outside restricted potential and
`originalBlock` is bounded by the concrete component-block integral, then their
sum is bounded by the actual original potential.  This packages the
`hdecomp_original` input expected by
`componentReplacement_objective_le_of_decomposition_jensen`.
-/
theorem unitIntervalLogPotential_original_potential_decomposition_lower
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    (outsidePart originalBlock : ℝ → ℝ)
    (houtside_le : ∀ x : ℝ, StrictOutsideComponent C x →
      outsidePart x ≤
        measureLogPotential ((realMeasure μ).restrict C.intervalᶜ) x)
    (hblock_le : ∀ x : ℝ, StrictOutsideComponent C x →
      originalBlock x ≤
        ∫ t : ℝ, Real.log (1 / |x - t|) ∂componentBlock C)
    (houtside_integrable : ∀ x : ℝ, StrictOutsideComponent C x →
      Integrable (fun t : ℝ => Real.log (1 / |x - t|))
        ((realMeasure μ).restrict C.intervalᶜ))
    (hblock_integrable : ∀ x : ℝ, StrictOutsideComponent C x →
      Integrable (fun t : ℝ => Real.log (1 / |x - t|)) (componentBlock C)) :
    ∀ x : ℝ, StrictOutsideComponent C x →
      outsidePart x + originalBlock x ≤ unitIntervalLogPotential μ x := by
  intro x hx
  rw [unitIntervalLogPotential_eq_outside_add_componentBlock C x
    (houtside_integrable x hx) (hblock_integrable x hx)]
  exact add_le_add (houtside_le x hx) (hblock_le x hx)

theorem unitIntervalLogPotential_endpointRemainder_potential_decomposition_lower
    (μ : ProbabilityMeasure UnitInterval1038) {p : ℝ}
    (hp : realMeasure μ ({-1} : Set ℝ) = ENNReal.ofReal p)
    (hp_nonneg : 0 ≤ p)
    (hrem_integrable : ∀ x : ℝ, x ∈ BaselinePunctured →
      Integrable (fun t : ℝ => Real.log (1 / |x - t|))
        ((realMeasure μ).restrict ({-1} : Set ℝ)ᶜ)) :
    ∀ x : ℝ, x ∈ BaselinePunctured →
      p * Real.log (1 / |x + 1|) +
        (∫ t : ℝ, Real.log (1 / |x - t|)
          ∂(realMeasure μ).restrict ({-1} : Set ℝ)ᶜ) ≤
        unitIntervalLogPotential μ x := by
  intro x hx
  let f : ℝ → ℝ := fun t => Real.log (1 / |x - t|)
  have hsplit :
      (realMeasure μ).restrict ({-1} : Set ℝ)ᶜ +
          (realMeasure μ).restrict ({-1} : Set ℝ) =
        realMeasure μ := by
    exact Measure.restrict_compl_add_restrict (measurableSet_singleton (-1 : ℝ))
  have hendpoint_integrable :
      Integrable f ((realMeasure μ).restrict ({-1} : Set ℝ)) := by
    rw [Measure.restrict_singleton]
    exact (integrable_dirac (by simp [f])).smul_measure (measure_ne_top _ _)
  have hendpoint_eq :
      (∫ t : ℝ, f t ∂(realMeasure μ).restrict ({-1} : Set ℝ)) =
        p * Real.log (1 / |x + 1|) := by
    rw [Measure.restrict_singleton]
    rw [integral_smul_measure]
    rw [integral_dirac]
    rw [hp]
    simp [f, smul_eq_mul, ENNReal.toReal_ofReal hp_nonneg]
  have hEq :
      unitIntervalLogPotential μ x =
        (∫ t : ℝ, f t ∂(realMeasure μ).restrict ({-1} : Set ℝ)ᶜ) +
          p * Real.log (1 / |x + 1|) := by
    calc
      unitIntervalLogPotential μ x = measureLogPotential (realMeasure μ) x := by
        exact unitIntervalLogPotential_eq_realMeasure μ x
      _ = measureLogPotential
          ((realMeasure μ).restrict ({-1} : Set ℝ)ᶜ +
            (realMeasure μ).restrict ({-1} : Set ℝ)) x := by
        rw [hsplit]
      _ = (∫ t : ℝ, f t ∂(realMeasure μ).restrict ({-1} : Set ℝ)ᶜ) +
            (∫ t : ℝ, f t ∂(realMeasure μ).restrict ({-1} : Set ℝ)) := by
        unfold measureLogPotential
        exact integral_add_measure (hrem_integrable x hx) hendpoint_integrable
      _ = (∫ t : ℝ, f t ∂(realMeasure μ).restrict ({-1} : Set ℝ)ᶜ) +
            p * Real.log (1 / |x + 1|) := by
        rw [hendpoint_eq]
  rw [hEq]
  linarith

theorem componentReplacement_potential_le_outside_add_replacementAtom
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    (outsidePart : ℝ → ℝ)
    (houtside_decomp : ∀ x : ℝ, StrictOutsideComponent C x →
      measureLogPotential ((realMeasure μ).restrict C.intervalᶜ) x ≤ outsidePart x)
    (houtside_integrable : ∀ x : ℝ, StrictOutsideComponent C x →
      Integrable (fun t : ℝ => Real.log (1 / |x - t|))
        ((realMeasure μ).restrict C.intervalᶜ)) :
    ∀ x : ℝ, StrictOutsideComponent C x →
      componentReplacementPotential C x ≤
        outsidePart x + (componentMass C).toReal *
          Real.log (1 / |x - componentBarycenter C|) := by
  intro x hx
  rw [componentReplacement_potential_eq_outside_add_replacementAtom C x
    (houtside_integrable x hx)]
  exact add_le_add (houtside_decomp x hx) le_rfl

lemma PositiveComponent.not_interval_imp_strictOutside_or_endpoint
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    {x : ℝ} (hx : x ∉ C.interval) :
    StrictOutsideComponent C x ∨ x = C.left ∨ x = C.right := by
  rw [PositiveComponent.interval_eq, Set.mem_Ioo] at hx
  by_cases hxl : x < C.left
  · exact Or.inl (Or.inl hxl)
  · by_cases hrx : C.right < x
    · exact Or.inl (Or.inr hrx)
    · have hle_left : C.left ≤ x := le_of_not_gt hxl
      have hle_right : x ≤ C.right := le_of_not_gt hrx
      have hnot : ¬ (C.left < x ∧ x < C.right) := hx
      by_cases hxeqleft : x = C.left
      · exact Or.inr (Or.inl hxeqleft)
      · have hleftlt : C.left < x := lt_of_le_of_ne hle_left (Ne.symm hxeqleft)
        by_cases hxeqright : x = C.right
        · exact Or.inr (Or.inr hxeqright)
        · have hxltRight : x < C.right := lt_of_le_of_ne hle_right hxeqright
          exact False.elim (hnot ⟨hleftlt, hxltRight⟩)

lemma replacement_positiveSet_subset_original_union_endpoints_of_strictOutside_le
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    {U' : ℝ → ℝ}
    (houtside : ∀ x : ℝ, StrictOutsideComponent C x →
      U' x ≤ unitIntervalLogPotential μ x) :
    PositiveSet U' ⊆
      PositiveSet (unitIntervalLogPotential μ) ∪ ({C.left, C.right} : Set ℝ) := by
  intro x hx
  by_cases hxC : x ∈ C.interval
  · exact Or.inl (C.interval_subset_positiveSet hxC)
  · rcases C.not_interval_imp_strictOutside_or_endpoint hxC with hstrict | hendpoint
    · exact Or.inl (lt_of_lt_of_le hx (houtside x hstrict))
    · exact Or.inr (by simpa [Set.mem_insert_iff] using hendpoint)

theorem replacement_objective_le_of_strictOutside_potential_le
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    {U' : ℝ → ℝ}
    (houtside : ∀ x : ℝ, StrictOutsideComponent C x →
      U' x ≤ unitIntervalLogPotential μ x) :
    volume (PositiveSet U') ≤
      volume (PositiveSet (unitIntervalLogPotential μ)) := by
  have hsub :=
    replacement_positiveSet_subset_original_union_endpoints_of_strictOutside_le
      C houtside
  have hmono :
      volume (PositiveSet U') ≤
        volume (PositiveSet (unitIntervalLogPotential μ) ∪
          ({C.left, C.right} : Set ℝ)) :=
    measure_mono (μ := volume) hsub
  have hunion :
      volume (PositiveSet (unitIntervalLogPotential μ) ∪
          ({C.left, C.right} : Set ℝ)) ≤
        volume (PositiveSet (unitIntervalLogPotential μ)) +
          volume ({C.left, C.right} : Set ℝ) :=
    measure_union_le _ _
  have hfinite : volume ({C.left, C.right} : Set ℝ) = 0 := by
    apply le_antisymm
    · calc
        volume ({C.left, C.right} : Set ℝ) ≤
            volume (({C.left} : Set ℝ) ∪ ({C.right} : Set ℝ)) := by
              exact measure_mono (by
                intro x hx
                simp at hx ⊢
                rcases hx with hx | hx
                · exact Or.inr hx
                · exact Or.inl hx)
        _ ≤ volume ({C.left} : Set ℝ) + volume ({C.right} : Set ℝ) :=
              measure_union_le _ _
        _ = 0 := by simp
    · exact bot_le
  calc
    volume (PositiveSet U') ≤
        volume (PositiveSet (unitIntervalLogPotential μ) ∪
          ({C.left, C.right} : Set ℝ)) := hmono
    _ ≤ volume (PositiveSet (unitIntervalLogPotential μ)) +
          volume ({C.left, C.right} : Set ℝ) := hunion
    _ = volume (PositiveSet (unitIntervalLogPotential μ)) := by
          simp [hfinite]

lemma replacement_positiveSet_subset_original_union_endpoints_diagonal_of_strictOutside_le_offdiag
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    {U' : ℝ → ℝ}
    (houtside : ∀ x : ℝ, StrictOutsideComponent C x →
      x ∉ diagonalAtomSet μ → U' x ≤ unitIntervalLogPotential μ x) :
    PositiveSet U' ⊆
      PositiveSet (unitIntervalLogPotential μ) ∪
        (({C.left, C.right} : Set ℝ) ∪ diagonalAtomSet μ) := by
  intro x hx
  by_cases hxC : x ∈ C.interval
  · exact Or.inl (C.interval_subset_positiveSet hxC)
  · rcases C.not_interval_imp_strictOutside_or_endpoint hxC with hstrict | hendpoint
    · by_cases hxdiag : x ∈ diagonalAtomSet μ
      · exact Or.inr (Or.inr hxdiag)
      · exact Or.inl (lt_of_lt_of_le hx (houtside x hstrict hxdiag))
    · exact Or.inr (Or.inl (by simpa [Set.mem_insert_iff] using hendpoint))

lemma replacement_positiveSet_subset_original_union_endpoints_diagonal_null_of_strictOutside_le_offdiag
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    {U' : ℝ → ℝ} {N : Set ℝ}
    (houtside : ∀ x : ℝ, StrictOutsideComponent C x →
      x ∉ diagonalAtomSet μ → x ∉ N → U' x ≤ unitIntervalLogPotential μ x) :
    PositiveSet U' ⊆
      PositiveSet (unitIntervalLogPotential μ) ∪
        (({C.left, C.right} : Set ℝ) ∪ (diagonalAtomSet μ ∪ N)) := by
  intro x hx
  by_cases hxC : x ∈ C.interval
  · exact Or.inl (C.interval_subset_positiveSet hxC)
  · rcases C.not_interval_imp_strictOutside_or_endpoint hxC with hstrict | hendpoint
    · by_cases hxdiag : x ∈ diagonalAtomSet μ
      · exact Or.inr (Or.inr (Or.inl hxdiag))
      · by_cases hxN : x ∈ N
        · exact Or.inr (Or.inr (Or.inr hxN))
        · exact Or.inl (lt_of_lt_of_le hx (houtside x hstrict hxdiag hxN))
    · exact Or.inr (Or.inl (by simpa [Set.mem_insert_iff] using hendpoint))

theorem replacement_objective_le_of_strictOutside_potential_le_offdiag_null
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    {U' : ℝ → ℝ} {N : Set ℝ}
    (hN : volume N = 0)
    (houtside : ∀ x : ℝ, StrictOutsideComponent C x →
      x ∉ diagonalAtomSet μ → x ∉ N → U' x ≤ unitIntervalLogPotential μ x) :
    volume (PositiveSet U') ≤
      volume (PositiveSet (unitIntervalLogPotential μ)) := by
  have hsub :=
    replacement_positiveSet_subset_original_union_endpoints_diagonal_null_of_strictOutside_le_offdiag
      C houtside
  have hmono :
      volume (PositiveSet U') ≤
        volume (PositiveSet (unitIntervalLogPotential μ) ∪
          (({C.left, C.right} : Set ℝ) ∪ (diagonalAtomSet μ ∪ N))) :=
    measure_mono (μ := volume) hsub
  have hendpoint_zero : volume ({C.left, C.right} : Set ℝ) = 0 := by
    exact Set.Countable.measure_zero (by simp : ({C.left, C.right} : Set ℝ).Countable) volume
  have hexception_zero :
      volume (({C.left, C.right} : Set ℝ) ∪ (diagonalAtomSet μ ∪ N)) = 0 := by
    apply le_antisymm
    · calc
        volume (({C.left, C.right} : Set ℝ) ∪ (diagonalAtomSet μ ∪ N)) ≤
            volume ({C.left, C.right} : Set ℝ) +
              volume (diagonalAtomSet μ ∪ N) := measure_union_le (μ := volume) _ _
        _ ≤ volume ({C.left, C.right} : Set ℝ) +
              (volume (diagonalAtomSet μ) + volume N) := by
                exact add_le_add_right
                  (measure_union_le (μ := volume) (diagonalAtomSet μ) N) _
        _ = 0 := by simp [hendpoint_zero, diagonalAtomSet_volume_zero μ, hN]
    · exact bot_le
  have hunion :
      volume (PositiveSet (unitIntervalLogPotential μ) ∪
          (({C.left, C.right} : Set ℝ) ∪ (diagonalAtomSet μ ∪ N))) ≤
        volume (PositiveSet (unitIntervalLogPotential μ)) +
          volume (({C.left, C.right} : Set ℝ) ∪ (diagonalAtomSet μ ∪ N)) :=
    measure_union_le (μ := volume) _ _
  calc
    volume (PositiveSet U') ≤
        volume (PositiveSet (unitIntervalLogPotential μ) ∪
          (({C.left, C.right} : Set ℝ) ∪ (diagonalAtomSet μ ∪ N))) := hmono
    _ ≤ volume (PositiveSet (unitIntervalLogPotential μ)) +
          volume (({C.left, C.right} : Set ℝ) ∪ (diagonalAtomSet μ ∪ N)) := hunion
    _ = volume (PositiveSet (unitIntervalLogPotential μ)) := by
          simp [hexception_zero]

theorem replacement_objective_le_add_of_strictOutside_potential_le_offdiag_exception
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    {U' : ℝ → ℝ} {N : Set ℝ} {η : ℝ≥0∞}
    (hN : volume N ≤ η)
    (houtside : ∀ x : ℝ, StrictOutsideComponent C x →
      x ∉ diagonalAtomSet μ → x ∉ N → U' x ≤ unitIntervalLogPotential μ x) :
    volume (PositiveSet U') ≤
      volume (PositiveSet (unitIntervalLogPotential μ)) + η := by
  have hsub :=
    replacement_positiveSet_subset_original_union_endpoints_diagonal_null_of_strictOutside_le_offdiag
      C houtside
  have hmono :
      volume (PositiveSet U') ≤
        volume (PositiveSet (unitIntervalLogPotential μ) ∪
          (({C.left, C.right} : Set ℝ) ∪ (diagonalAtomSet μ ∪ N))) :=
    measure_mono (μ := volume) hsub
  have hendpoint_zero : volume ({C.left, C.right} : Set ℝ) = 0 := by
    exact Set.Countable.measure_zero (by simp : ({C.left, C.right} : Set ℝ).Countable) volume
  have hexception_le :
      volume (({C.left, C.right} : Set ℝ) ∪ (diagonalAtomSet μ ∪ N)) ≤ η := by
    calc
      volume (({C.left, C.right} : Set ℝ) ∪ (diagonalAtomSet μ ∪ N)) ≤
          volume ({C.left, C.right} : Set ℝ) +
            volume (diagonalAtomSet μ ∪ N) := measure_union_le (μ := volume) _ _
      _ ≤ volume ({C.left, C.right} : Set ℝ) +
            (volume (diagonalAtomSet μ) + volume N) := by
              exact add_le_add_right
                (measure_union_le (μ := volume) (diagonalAtomSet μ) N) _
      _ = volume N := by
            simp [hendpoint_zero, diagonalAtomSet_volume_zero μ]
      _ ≤ η := hN
  have hunion :
      volume (PositiveSet (unitIntervalLogPotential μ) ∪
          (({C.left, C.right} : Set ℝ) ∪ (diagonalAtomSet μ ∪ N))) ≤
        volume (PositiveSet (unitIntervalLogPotential μ)) +
          volume (({C.left, C.right} : Set ℝ) ∪ (diagonalAtomSet μ ∪ N)) :=
    measure_union_le (μ := volume) _ _
  calc
    volume (PositiveSet U') ≤
        volume (PositiveSet (unitIntervalLogPotential μ) ∪
          (({C.left, C.right} : Set ℝ) ∪ (diagonalAtomSet μ ∪ N))) := hmono
    _ ≤ volume (PositiveSet (unitIntervalLogPotential μ)) +
          volume (({C.left, C.right} : Set ℝ) ∪ (diagonalAtomSet μ ∪ N)) := hunion
    _ ≤ volume (PositiveSet (unitIntervalLogPotential μ)) + η := by
          exact add_le_add_right hexception_le _

theorem replacement_objective_le_of_strictOutside_potential_le_offdiag
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    {U' : ℝ → ℝ}
    (houtside : ∀ x : ℝ, StrictOutsideComponent C x →
      x ∉ diagonalAtomSet μ → U' x ≤ unitIntervalLogPotential μ x) :
    volume (PositiveSet U') ≤
      volume (PositiveSet (unitIntervalLogPotential μ)) := by
  have hsub :=
    replacement_positiveSet_subset_original_union_endpoints_diagonal_of_strictOutside_le_offdiag
      C houtside
  have hmono :
      volume (PositiveSet U') ≤
        volume (PositiveSet (unitIntervalLogPotential μ) ∪
          (({C.left, C.right} : Set ℝ) ∪ diagonalAtomSet μ)) :=
    measure_mono (μ := volume) hsub
  have hendpoint_zero : volume ({C.left, C.right} : Set ℝ) = 0 := by
    exact Set.Countable.measure_zero (by simp : ({C.left, C.right} : Set ℝ).Countable) volume
  have hexception_zero :
      volume (({C.left, C.right} : Set ℝ) ∪ diagonalAtomSet μ) = 0 := by
    apply le_antisymm
    · calc
        volume (({C.left, C.right} : Set ℝ) ∪ diagonalAtomSet μ) ≤
            volume ({C.left, C.right} : Set ℝ) +
              volume (diagonalAtomSet μ) := measure_union_le _ _
        _ = 0 := by simp [hendpoint_zero, diagonalAtomSet_volume_zero μ]
    · exact bot_le
  have hunion :
      volume (PositiveSet (unitIntervalLogPotential μ) ∪
          (({C.left, C.right} : Set ℝ) ∪ diagonalAtomSet μ)) ≤
        volume (PositiveSet (unitIntervalLogPotential μ)) +
          volume (({C.left, C.right} : Set ℝ) ∪ diagonalAtomSet μ) :=
    measure_union_le _ _
  calc
    volume (PositiveSet U') ≤
        volume (PositiveSet (unitIntervalLogPotential μ) ∪
          (({C.left, C.right} : Set ℝ) ∪ diagonalAtomSet μ)) := hmono
    _ ≤ volume (PositiveSet (unitIntervalLogPotential μ)) +
          volume (({C.left, C.right} : Set ℝ) ∪ diagonalAtomSet μ) := hunion
    _ = volume (PositiveSet (unitIntervalLogPotential μ)) := by
          simp [hexception_zero]

theorem replacement_objective_le_of_outside_potential_le
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    {U' : ℝ → ℝ}
    (houtside : ∀ x : ℝ, x ∉ C.interval →
      U' x ≤ unitIntervalLogPotential μ x) :
    volume (PositiveSet U') ≤
      volume (PositiveSet (unitIntervalLogPotential μ)) := by
  exact measure_mono (μ := volume)
    (replacement_positiveSet_subset_original_of_outside_le C houtside)

theorem componentReplacement_objective_le_of_outside_potential_le
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    (houtside : ∀ x : ℝ, x ∉ C.interval →
      componentReplacementPotential C x ≤ unitIntervalLogPotential μ x) :
    volume (PositiveSet (componentReplacementPotential C)) ≤
      volume (PositiveSet (unitIntervalLogPotential μ)) := by
  exact replacement_objective_le_of_outside_potential_le C houtside

theorem componentReplacement_objective_le_of_strictOutside_potential_le
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    (houtside : ∀ x : ℝ, StrictOutsideComponent C x →
      componentReplacementPotential C x ≤ unitIntervalLogPotential μ x) :
    volume (PositiveSet (componentReplacementPotential C)) ≤
      volume (PositiveSet (unitIntervalLogPotential μ)) := by
  exact replacement_objective_le_of_strictOutside_potential_le C houtside

/--
Component-replacement objective bridge from local potential decompositions.

For a strict outside point `x`, the replacement proof naturally splits both
potentials into the unchanged outside-component contribution and the component
block contribution.  If the unchanged contributions are ordered and the
barycenter block contribution is bounded by the original block contribution
by Jensen, then the replacement potential is no larger at `x`.

This theorem is deliberately stated at the decomposition level.  The analytic
work left after this bridge is exactly to prove the two decomposition formulas
for the concrete restricted measures and to discharge the block Jensen
inequality by `measure_barycenter_logKernel_replacement_le_of_strictOutside_Ioo`.
-/
theorem componentReplacement_strictOutside_potential_le_of_decomposition_jensen
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    (outsidePart replacementBlock originalBlock : ℝ → ℝ)
    (hdecomp_replacement : ∀ x : ℝ, StrictOutsideComponent C x →
      componentReplacementPotential C x ≤ outsidePart x + replacementBlock x)
    (hdecomp_original : ∀ x : ℝ, StrictOutsideComponent C x →
      outsidePart x + originalBlock x ≤ unitIntervalLogPotential μ x)
    (hblock_jensen : ∀ x : ℝ, StrictOutsideComponent C x →
      replacementBlock x ≤ originalBlock x) :
    ∀ x : ℝ, StrictOutsideComponent C x →
      componentReplacementPotential C x ≤ unitIntervalLogPotential μ x := by
  intro x hx
  exact le_trans (hdecomp_replacement x hx)
    (le_trans (add_le_add_right (hblock_jensen x hx) (outsidePart x))
      (hdecomp_original x hx))

/--
Objective consequence of the decomposition-plus-Jensen replacement bridge.

This is the route used in the Tao variation argument: once the strict-outside
potential decomposition and the component-block Jensen estimate are proved,
the barycenter replacement cannot increase the positive-set objective.
-/
theorem componentReplacement_objective_le_of_decomposition_jensen
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    (outsidePart replacementBlock originalBlock : ℝ → ℝ)
    (hdecomp_replacement : ∀ x : ℝ, StrictOutsideComponent C x →
      componentReplacementPotential C x ≤ outsidePart x + replacementBlock x)
    (hdecomp_original : ∀ x : ℝ, StrictOutsideComponent C x →
      outsidePart x + originalBlock x ≤ unitIntervalLogPotential μ x)
    (hblock_jensen : ∀ x : ℝ, StrictOutsideComponent C x →
      replacementBlock x ≤ originalBlock x) :
    volume (PositiveSet (componentReplacementPotential C)) ≤
      volume (PositiveSet (unitIntervalLogPotential μ)) := by
  exact componentReplacement_objective_le_of_strictOutside_potential_le C
    (componentReplacement_strictOutside_potential_le_of_decomposition_jensen
      C outsidePart replacementBlock originalBlock hdecomp_replacement
      hdecomp_original hblock_jensen)

lemma eventual_pointwise_error_of_three_errors
    {ι : Type*} {L : Filter ι} (U : ℝ → ℝ) (Us : ι → ℝ → ℝ)
    (T : ℕ → ℝ → ℝ) (Ts : ℕ → ι → ℝ → ℝ)
    (hlimit : ∀ n x,
      |T n x - U x| < (1 / ((n : ℝ) + 1)) / 3)
    (hseq : ∀ n, ∀ᶠ i in L, ∀ x,
      |Ts n i x - Us i x| < (1 / ((n : ℝ) + 1)) / 3)
    (htrunc : ∀ n, ∀ᶠ i in L, ∀ x,
      |Ts n i x - T n x| < (1 / ((n : ℝ) + 1)) / 3) :
    ∀ n : ℕ, ∀ᶠ i in L, ∀ x : ℝ,
      |Us i x - U x| < 1 / ((n : ℝ) + 1) := by
  intro n
  filter_upwards [hseq n, htrunc n] with i hseqi htrunci x
  have h1 := hseqi x
  have h2 := htrunci x
  have h3 := hlimit n x
  have htriangle : |Us i x - U x| ≤
      |Us i x - Ts n i x| + |Ts n i x - T n x| +
        |T n x - U x| := by
    calc
      |Us i x - U x| =
          |(Us i x - Ts n i x) + (Ts n i x - T n x) +
            (T n x - U x)| := by
            congr 1
            ring
      _ ≤ |Us i x - Ts n i x| + |Ts n i x - T n x| +
          |T n x - U x| := by
        calc
          |(Us i x - Ts n i x) + (Ts n i x - T n x) +
              (T n x - U x)|
              ≤ |(Us i x - Ts n i x) + (Ts n i x - T n x)| +
                |T n x - U x| :=
            abs_add_le
              ((Us i x - Ts n i x) + (Ts n i x - T n x))
              (T n x - U x)
          _ ≤ |Us i x - Ts n i x| + |Ts n i x - T n x| +
              |T n x - U x| := by
            have h :=
              abs_add_le (Us i x - Ts n i x) (Ts n i x - T n x)
            linarith
  have h1' : |Us i x - Ts n i x| <
      (1 / ((n : ℝ) + 1)) / 3 := by
    rwa [abs_sub_comm]
  linarith

theorem variable_positiveSet_measure_le_liminf_of_three_error_scheme
    {ι : Type*} {L : Filter ι} (U : ℝ → ℝ) (Us : ι → ℝ → ℝ)
    (T : ℕ → ℝ → ℝ) (Ts : ℕ → ι → ℝ → ℝ)
    (hlimit : ∀ n x,
      |T n x - U x| < (1 / ((n : ℝ) + 1)) / 3)
    (hseq : ∀ n, ∀ᶠ i in L, ∀ x,
      |Ts n i x - Us i x| < (1 / ((n : ℝ) + 1)) / 3)
    (htrunc : ∀ n, ∀ᶠ i in L, ∀ x,
      |Ts n i x - T n x| < (1 / ((n : ℝ) + 1)) / 3) :
    volume {x : ℝ | 0 < U x} ≤
      L.liminf (fun i => volume {x : ℝ | 0 < Us i x}) := by
  exact variable_positiveSet_measure_le_liminf_of_eventually_pointwise_error
    U Us
    (eventual_pointwise_error_of_three_errors U Us T Ts
      hlimit hseq htrunc)

/--
Core-set form of the three-error argument.  If a set `A` sits inside the
`τ`-superlevel set of `U`, and the limit truncation, sequence truncation, and
truncated convergence errors are all less than `τ/3` on `A`, then eventually
`A` is contained in the positive set of the perturbed potentials.
-/
lemma eventually_subset_positiveSet_of_three_errors_on_core
    {ι : Type*} {L : Filter ι}
    (U : ℝ → ℝ) (Us : ι → ℝ → ℝ)
    (T : ℝ → ℝ) (Ts : ι → ℝ → ℝ)
    {A : Set ℝ} {τ : ℝ} (_hτ : 0 < τ)
    (hA : A ⊆ {x : ℝ | τ < U x})
    (hlimit : ∀ x ∈ A, |T x - U x| < τ / 3)
    (hseq : ∀ᶠ i in L, ∀ x ∈ A, |Ts i x - Us i x| < τ / 3)
    (htrunc : ∀ᶠ i in L, ∀ x ∈ A, |Ts i x - T x| < τ / 3) :
    ∀ᶠ i in L, A ⊆ {x : ℝ | 0 < Us i x} := by
  filter_upwards [hseq, htrunc] with i hseqi htrunci x hxA
  have hUx : τ < U x := hA hxA
  have h1 := hlimit x hxA
  have h2 := hseqi x hxA
  have h3 := htrunci x hxA
  have hseq_lower : -(τ / 3) < Us i x - Ts i x := by
    have h2' : |Us i x - Ts i x| < τ / 3 := by
      simpa [abs_sub_comm] using h2
    exact (abs_lt.mp h2').1
  have htrunc_lower : -(τ / 3) < Ts i x - T x := (abs_lt.mp h3).1
  have hlimit_lower : -(τ / 3) < T x - U x := (abs_lt.mp h1).1
  change 0 < Us i x
  linarith

lemma eventually_subset_positiveSet_union_exception_of_three_errors_on_core
    {ι : Type*} {L : Filter ι}
    (U : ℝ → ℝ) (Us : ι → ℝ → ℝ)
    (T : ℝ → ℝ) (Ts : ι → ℝ → ℝ)
    (N : ι → Set ℝ)
    {A : Set ℝ} {τ : ℝ} (_hτ : 0 < τ)
    (hA : A ⊆ {x : ℝ | τ < U x})
    (hlimit : ∀ x ∈ A, |T x - U x| < τ / 3)
    (hseq : ∀ᶠ i in L, ∀ x ∈ A,
      x ∈ N i ∨ |Ts i x - Us i x| < τ / 3)
    (htrunc : ∀ᶠ i in L, ∀ x ∈ A, |Ts i x - T x| < τ / 3) :
    ∀ᶠ i in L, A ⊆ {x : ℝ | 0 < Us i x} ∪ N i := by
  filter_upwards [hseq, htrunc] with i hseqi htrunci x hxA
  rcases hseqi x hxA with hxN | h2
  · exact Or.inr hxN
  · have hUx : τ < U x := hA hxA
    have h1 := hlimit x hxA
    have h3 := htrunci x hxA
    have hseq_lower : -(τ / 3) < Us i x - Ts i x := by
      have h2' : |Us i x - Ts i x| < τ / 3 := by
        simpa [abs_sub_comm] using h2
      exact (abs_lt.mp h2').1
    have htrunc_lower : -(τ / 3) < Ts i x - T x := (abs_lt.mp h3).1
    have hlimit_lower : -(τ / 3) < T x - U x := (abs_lt.mp h1).1
    exact Or.inl (by
      change 0 < Us i x
      linarith)

/--
Threshold approximation follows once one can choose a core `A` that covers a
threshold set up to `ε` measure and satisfies the three local error controls.
This theorem is the formal assembly point for `happrox`.
-/
theorem threshold_approx_of_three_error_core
    {ι : Type*} {L : Filter ι}
    (U : ℝ → ℝ) (Us : ι → ℝ → ℝ)
    (T : ℝ → ℝ) (Ts : ι → ℝ → ℝ)
    {τ : ℝ} (hτ : 0 < τ) {ε : ℝ≥0∞}
    (A : Set ℝ)
    (hAmeasure : volume {x : ℝ | τ < U x} ≤ volume A + ε)
    (hA : A ⊆ {x : ℝ | τ < U x})
    (hlimit : ∀ x ∈ A, |T x - U x| < τ / 3)
    (hseq : ∀ᶠ i in L, ∀ x ∈ A, |Ts i x - Us i x| < τ / 3)
    (htrunc : ∀ᶠ i in L, ∀ x ∈ A, |Ts i x - T x| < τ / 3) :
    volume {x : ℝ | τ < U x} ≤ volume A + ε ∧
      ∀ᶠ i in L, A ⊆ {x : ℝ | 0 < Us i x} := by
  exact ⟨hAmeasure,
    eventually_subset_positiveSet_of_three_errors_on_core
      U Us T Ts hτ hA hlimit hseq htrunc⟩

theorem threshold_approx_of_three_error_core_with_exception
    {ι : Type*} {L : Filter ι}
    (U : ℝ → ℝ) (Us : ι → ℝ → ℝ)
    (T : ℝ → ℝ) (Ts : ι → ℝ → ℝ)
    (N : ι → Set ℝ)
    {τ : ℝ} (hτ : 0 < τ) {ε : ℝ≥0∞}
    (A : Set ℝ)
    (hAmeasure : volume {x : ℝ | τ < U x} ≤ volume A + ε)
    (hA : A ⊆ {x : ℝ | τ < U x})
    (hlimit : ∀ x ∈ A, |T x - U x| < τ / 3)
    (hseq : ∀ᶠ i in L, ∀ x ∈ A,
      x ∈ N i ∨ |Ts i x - Us i x| < τ / 3)
    (htrunc : ∀ᶠ i in L, ∀ x ∈ A, |Ts i x - T x| < τ / 3) :
    volume {x : ℝ | τ < U x} ≤ volume A + ε ∧
      ∀ᶠ i in L, A ⊆ {x : ℝ | 0 < Us i x} ∪ N i := by
  exact ⟨hAmeasure,
    eventually_subset_positiveSet_union_exception_of_three_errors_on_core
      U Us T Ts N hτ hA hlimit hseq htrunc⟩

lemma eventually_subset_positiveSet_union_exception_of_limit_trunc_and_seq_lower_on_core
    {ι : Type*} {L : Filter ι}
    (U : ℝ → ℝ) (Us : ι → ℝ → ℝ)
    (T : ℝ → ℝ) (Ts : ι → ℝ → ℝ)
    (N : ι → Set ℝ)
    {A : Set ℝ} {τ : ℝ} (_hτ : 0 < τ)
    (hA : A ⊆ {x : ℝ | τ < U x})
    (hlimit : ∀ x ∈ A, |T x - U x| < τ / 3)
    (hseqLower : ∀ᶠ i in L, ∀ x ∈ A, x ∈ N i ∨ Ts i x ≤ Us i x)
    (htrunc : ∀ᶠ i in L, ∀ x ∈ A, |Ts i x - T x| < τ / 3) :
    ∀ᶠ i in L, A ⊆ {x : ℝ | 0 < Us i x} ∪ N i := by
  filter_upwards [hseqLower, htrunc] with i hseqi htrunci x hxA
  rcases hseqi x hxA with hxN | hle
  · exact Or.inr hxN
  · have hUx : τ < U x := hA hxA
    have h1 := hlimit x hxA
    have h3 := htrunci x hxA
    have htrunc_lower : -(τ / 3) < Ts i x - T x := (abs_lt.mp h3).1
    have hlimit_lower : -(τ / 3) < T x - U x := (abs_lt.mp h1).1
    exact Or.inl (by
      change 0 < Us i x
      linarith)

theorem threshold_approx_of_limit_trunc_and_seq_lower_core_with_exception
    {ι : Type*} {L : Filter ι}
    (U : ℝ → ℝ) (Us : ι → ℝ → ℝ)
    (T : ℝ → ℝ) (Ts : ι → ℝ → ℝ)
    (N : ι → Set ℝ)
    {τ : ℝ} (hτ : 0 < τ) {ε : ℝ≥0∞}
    (A : Set ℝ)
    (hAmeasure : volume {x : ℝ | τ < U x} ≤ volume A + ε)
    (hA : A ⊆ {x : ℝ | τ < U x})
    (hlimit : ∀ x ∈ A, |T x - U x| < τ / 3)
    (hseqLower : ∀ᶠ i in L, ∀ x ∈ A, x ∈ N i ∨ Ts i x ≤ Us i x)
    (htrunc : ∀ᶠ i in L, ∀ x ∈ A, |Ts i x - T x| < τ / 3) :
    volume {x : ℝ | τ < U x} ≤ volume A + ε ∧
      ∀ᶠ i in L, A ⊆ {x : ℝ | 0 < Us i x} ∪ N i := by
  exact ⟨hAmeasure,
    eventually_subset_positiveSet_union_exception_of_limit_trunc_and_seq_lower_on_core
      U Us T Ts N hτ hA hlimit hseqLower htrunc⟩

def truncatedLogKernel (ε x : ℝ) (t : ℝ) : ℝ :=
  Real.log (1 / max ε |x - t|)

def unitIntervalTruncatedPotential
    (ε : ℝ) (μ : ProbabilityMeasure UnitInterval1038) (x : ℝ) : ℝ :=
  ∫ t : UnitInterval1038,
    truncatedLogKernel ε x (t : ℝ) ∂(μ : Measure UnitInterval1038)

/--
Structured version of the `happrox` input for the unit-interval logarithmic
potential.  The remaining analytic task is now exactly to construct these
truncated cores `A`; once they are available, this theorem returns the original
threshold-approximation statement used by lower semicontinuity.
-/
theorem unitInterval_threshold_approx_of_truncated_cores
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ truncε : ℝ, ∃ A : Set ℝ,
          volume {x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} ≤
            volume A + (ε : ℝ≥0∞) ∧
          A ⊆ {x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} ∧
          (∀ x ∈ A,
            |unitIntervalTruncatedPotential truncε μ x -
              unitIntervalLogPotential μ x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ A,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalLogPotential ν x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ A,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalTruncatedPotential truncε μ x| <
              (1 / ((n : ℝ) + 1)) / 3)) :
    ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ A : Set ℝ,
          volume {x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} ≤
            volume A + (ε : ℝ≥0∞) ∧
          ∀ᶠ ν in nhds μ,
            A ⊆ {x : ℝ | 0 < unitIntervalLogPotential ν x} := by
  intro μ n ε hε
  rcases hcore μ n ε hε with
    ⟨truncε, A, hAmeasure, hA, hlimit, hseq, htrunc⟩
  refine ⟨A, ?_⟩
  have hτ : 0 < 1 / ((n : ℝ) + 1) := by positivity
  exact threshold_approx_of_three_error_core
    (unitIntervalLogPotential μ)
    (fun ν : ProbabilityMeasure UnitInterval1038 =>
      unitIntervalLogPotential ν)
    (unitIntervalTruncatedPotential truncε μ)
    (fun ν : ProbabilityMeasure UnitInterval1038 =>
      unitIntervalTruncatedPotential truncε ν)
    hτ A hAmeasure hA hlimit hseq htrunc

theorem unitInterval_threshold_approx_of_truncated_cores_with_diagonal_exception
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ truncε : ℝ, ∃ A : Set ℝ,
          volume {x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} ≤
            volume A + (ε : ℝ≥0∞) ∧
          A ⊆ {x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} ∧
          (∀ x ∈ A,
            |unitIntervalTruncatedPotential truncε μ x -
              unitIntervalLogPotential μ x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ A,
            x ∈ diagonalAtomSet ν ∨
              |unitIntervalTruncatedPotential truncε ν x -
                unitIntervalLogPotential ν x| <
                (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ A,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalTruncatedPotential truncε μ x| <
              (1 / ((n : ℝ) + 1)) / 3)) :
    ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ A : Set ℝ,
          volume {x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} ≤
            volume A + (ε : ℝ≥0∞) ∧
          ∀ᶠ ν in nhds μ,
            A ⊆ {x : ℝ | 0 < unitIntervalLogPotential ν x} ∪
              diagonalAtomSet ν := by
  intro μ n ε hε
  rcases hcore μ n ε hε with
    ⟨truncε, A, hAmeasure, hA, hlimit, hseq, htrunc⟩
  refine ⟨A, ?_⟩
  have hτ : 0 < 1 / ((n : ℝ) + 1) := by positivity
  exact threshold_approx_of_three_error_core_with_exception
    (unitIntervalLogPotential μ)
    (fun ν : ProbabilityMeasure UnitInterval1038 =>
      unitIntervalLogPotential ν)
    (unitIntervalTruncatedPotential truncε μ)
    (fun ν : ProbabilityMeasure UnitInterval1038 =>
      unitIntervalTruncatedPotential truncε ν)
      (fun ν : ProbabilityMeasure UnitInterval1038 => diagonalAtomSet ν)
    hτ A hAmeasure hA hlimit hseq htrunc

theorem unitInterval_threshold_approx_of_truncated_cores_with_diagonal_exception_oneSided
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ truncε : ℝ, ∃ A : Set ℝ,
          volume {x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} ≤
            volume A + (ε : ℝ≥0∞) ∧
          A ⊆ {x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} ∧
          (∀ x ∈ A,
            |unitIntervalTruncatedPotential truncε μ x -
              unitIntervalLogPotential μ x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ A,
            x ∈ diagonalAtomSet ν ∨
              unitIntervalTruncatedPotential truncε ν x ≤
                unitIntervalLogPotential ν x) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ A,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalTruncatedPotential truncε μ x| <
              (1 / ((n : ℝ) + 1)) / 3)) :
    ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ A : Set ℝ,
          volume {x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} ≤
            volume A + (ε : ℝ≥0∞) ∧
          ∀ᶠ ν in nhds μ,
            A ⊆ {x : ℝ | 0 < unitIntervalLogPotential ν x} ∪
              diagonalAtomSet ν := by
  intro μ n ε hε
  rcases hcore μ n ε hε with
    ⟨truncε, A, hAmeasure, hA, hlimit, hseqLower, htrunc⟩
  refine ⟨A, ?_⟩
  have hτ : 0 < 1 / ((n : ℝ) + 1) := by positivity
  exact threshold_approx_of_limit_trunc_and_seq_lower_core_with_exception
    (unitIntervalLogPotential μ)
    (fun ν : ProbabilityMeasure UnitInterval1038 =>
      unitIntervalLogPotential ν)
    (unitIntervalTruncatedPotential truncε μ)
    (fun ν : ProbabilityMeasure UnitInterval1038 =>
      unitIntervalTruncatedPotential truncε ν)
    (fun ν : ProbabilityMeasure UnitInterval1038 => diagonalAtomSet ν)
    hτ A hAmeasure hA hlimit hseqLower htrunc

/--
Bad-set form of the truncated-core construction.  If the threshold set outside
the core has measure at most `ε`, and the three error estimates hold on the
core, then the original threshold-approximation statement follows.
-/
theorem unitInterval_threshold_approx_of_badSet_core
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ truncε : ℝ, ∃ A : Set ℝ,
          A ⊆ {x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} ∧
          volume ({x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} \ A) ≤ (ε : ℝ≥0∞) ∧
          (∀ x ∈ A,
            |unitIntervalTruncatedPotential truncε μ x -
              unitIntervalLogPotential μ x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ A,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalLogPotential ν x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ A,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalTruncatedPotential truncε μ x| <
              (1 / ((n : ℝ) + 1)) / 3)) :
    ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ A : Set ℝ,
          volume {x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} ≤
            volume A + (ε : ℝ≥0∞) ∧
          ∀ᶠ ν in nhds μ,
            A ⊆ {x : ℝ | 0 < unitIntervalLogPotential ν x} := by
  refine unitInterval_threshold_approx_of_truncated_cores ?_
  intro μ n ε hε
  rcases hcore μ n ε hε with
    ⟨truncε, A, hA, hbad, hlimit, hseq, htrunc⟩
  refine ⟨truncε, A, ?_, hA, hlimit, hseq, htrunc⟩
  let S : Set ℝ :=
    {x : ℝ | 1 / ((n : ℝ) + 1) < unitIntervalLogPotential μ x}
  have hSsubset : S ⊆ A ∪ (S \ A) := by
    intro x hx
    by_cases hxA : x ∈ A
    · exact Or.inl hxA
    · exact Or.inr ⟨hx, hxA⟩
  have hmeasure :
      volume S ≤ volume (A ∪ (S \ A)) :=
    measure_mono (μ := volume) hSsubset
  have hunion :
      volume (A ∪ (S \ A)) ≤ volume A + volume (S \ A) :=
    measure_union_le _ _
  calc
    volume {x : ℝ | 1 / ((n : ℝ) + 1) <
        unitIntervalLogPotential μ x}
        = volume S := rfl
    _ ≤ volume (A ∪ (S \ A)) := hmeasure
    _ ≤ volume A + volume (S \ A) := hunion
    _ ≤ volume A + (ε : ℝ≥0∞) := by
          calc
            volume A + volume (S \ A) =
                volume (S \ A) + volume A := by ac_rfl
            _ ≤ (ε : ℝ≥0∞) + volume A := by
                  exact add_le_add_left (by simpa [S] using hbad) (volume A)
            _ = volume A + (ε : ℝ≥0∞) := by ac_rfl

/--
Compact-core form of the threshold approximation.  This is the usable version of
the regularity step: approximate the positive threshold set by a compact subset,
then verify the three analytic estimates on that compact core.
-/
theorem unitInterval_threshold_approx_of_compact_core
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ truncε : ℝ, ∃ K : Set ℝ,
          K ⊆ {x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} ∧
          IsCompact K ∧
          volume ({x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} \ K) ≤ (ε : ℝ≥0∞) ∧
          (∀ x ∈ K,
            |unitIntervalTruncatedPotential truncε μ x -
              unitIntervalLogPotential μ x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ K,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalLogPotential ν x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ K,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalTruncatedPotential truncε μ x| <
              (1 / ((n : ℝ) + 1)) / 3)) :
    ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ A : Set ℝ,
          volume {x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} ≤
            volume A + (ε : ℝ≥0∞) ∧
          ∀ᶠ ν in nhds μ,
            A ⊆ {x : ℝ | 0 < unitIntervalLogPotential ν x} := by
  refine unitInterval_threshold_approx_of_badSet_core ?_
  intro μ n ε hε
  rcases hcore μ n ε hε with
    ⟨truncε, K, hKsub, _hKcompact, hbad, hlimit, hseq, htrunc⟩
  exact ⟨truncε, K, hKsub, hbad, hlimit, hseq, htrunc⟩

def singularTailKernel (ε : ℝ) (x : ℝ) (t : UnitInterval1038) :
    ℝ≥0∞ :=
  if |x - (t : ℝ)| < ε then
    ENNReal.ofReal (Real.log (ε / |x - (t : ℝ)|))
  else
    0

def singularTailMass
    (ε : ℝ) (μ : ProbabilityMeasure UnitInterval1038) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ t : UnitInterval1038,
    singularTailKernel ε x t ∂(μ : Measure UnitInterval1038)

lemma measurable_singularTailKernel_uncurry (ε : ℝ) :
    Measurable
      (fun p : ℝ × UnitInterval1038 => singularTailKernel ε p.1 p.2) := by
  unfold singularTailKernel
  have hs :
      MeasurableSet
        {p : ℝ × UnitInterval1038 | |p.1 - (p.2 : ℝ)| < ε} := by
    measurability
  have hf :
      Measurable
        (fun p : ℝ × UnitInterval1038 =>
          ENNReal.ofReal (Real.log (ε / |p.1 - (p.2 : ℝ)|))) := by
    measurability
  exact Measurable.ite hs hf measurable_const

lemma aemeasurable_singularTailKernel_uncurry
    (ε : ℝ) (μ : ProbabilityMeasure UnitInterval1038) :
    AEMeasurable
      (Function.uncurry (fun x t => singularTailKernel ε x t))
      (volume.prod (μ : Measure UnitInterval1038)) := by
  exact (measurable_singularTailKernel_uncurry ε).aemeasurable

lemma measurable_singularTailMass
    (ε : ℝ) (μ : ProbabilityMeasure UnitInterval1038) :
    Measurable (singularTailMass ε μ) := by
  unfold singularTailMass
  simpa using
    (Measurable.lintegral_prod_right'
      (ν := (μ : Measure UnitInterval1038))
      (measurable_singularTailKernel_uncurry ε))

lemma measurableSet_singularTailMass_strict
    (ε : ℝ) (μ : ProbabilityMeasure UnitInterval1038) (δ : ℝ≥0∞) :
    MeasurableSet {x : ℝ | δ < singularTailMass ε μ x} := by
  exact measurableSet_lt measurable_const (measurable_singularTailMass ε μ)

lemma measurableSet_singularTailMass_closed
    (ε : ℝ) (μ : ProbabilityMeasure UnitInterval1038) (δ : ℝ≥0∞) :
    MeasurableSet {x : ℝ | δ ≤ singularTailMass ε μ x} := by
  exact measurableSet_le measurable_const (measurable_singularTailMass ε μ)

lemma real_error_lt_of_ofReal_error_le_tail_lt
    {err δ : ℝ} {tail : ℝ≥0∞}
    (hδ : 0 < δ)
    (herror : ENNReal.ofReal err ≤ tail)
    (htail : tail < ENNReal.ofReal δ) :
    err < δ := by
  have hlt : ENNReal.ofReal err < ENNReal.ofReal δ :=
    lt_of_le_of_lt herror htail
  exact (ENNReal.ofReal_lt_ofReal_iff hδ).mp hlt

lemma truncated_potential_error_lt_of_tail_bound
    {ε δ : ℝ} {μ : ProbabilityMeasure UnitInterval1038} {x : ℝ}
    (hδ : 0 < δ)
    (herror :
      ENNReal.ofReal
        |unitIntervalTruncatedPotential ε μ x -
          unitIntervalLogPotential μ x| ≤ singularTailMass ε μ x)
    (htail : singularTailMass ε μ x < ENNReal.ofReal δ) :
    |unitIntervalTruncatedPotential ε μ x -
      unitIntervalLogPotential μ x| < δ :=
  real_error_lt_of_ofReal_error_le_tail_lt hδ herror htail

lemma core_limit_error_from_tail_bound
    {ε δ : ℝ} {μ : ProbabilityMeasure UnitInterval1038} {A : Set ℝ}
    (hδ : 0 < δ)
    (herror : ∀ x ∈ A,
      ENNReal.ofReal
        |unitIntervalTruncatedPotential ε μ x -
          unitIntervalLogPotential μ x| ≤ singularTailMass ε μ x)
    (htail : ∀ x ∈ A, singularTailMass ε μ x < ENNReal.ofReal δ) :
    ∀ x ∈ A,
      |unitIntervalTruncatedPotential ε μ x -
        unitIntervalLogPotential μ x| < δ := by
  intro x hx
  exact truncated_potential_error_lt_of_tail_bound hδ
    (herror x hx) (htail x hx)

def unitIntervalThresholdTailCore
    (μ : ProbabilityMeasure UnitInterval1038) (n : ℕ)
    (truncε δ : ℝ) : Set ℝ :=
  {x : ℝ | 1 / ((n : ℝ) + 1) < unitIntervalLogPotential μ x} ∩
    {x : ℝ | singularTailMass truncε μ x < ENNReal.ofReal δ}

theorem unitInterval_tailCore_subset_threshold
    (μ : ProbabilityMeasure UnitInterval1038) (n : ℕ)
    (truncε δ : ℝ) :
    unitIntervalThresholdTailCore μ n truncε δ ⊆
      {x : ℝ | 1 / ((n : ℝ) + 1) < unitIntervalLogPotential μ x} := by
  intro x hx
  exact hx.1

theorem singularTailMass_lt_top_of_mem_unitIntervalThresholdTailCore
    (μ : ProbabilityMeasure UnitInterval1038) (n : ℕ)
    (truncε δ : ℝ) {x : ℝ}
    (hx : x ∈ unitIntervalThresholdTailCore μ n truncε δ) :
    singularTailMass truncε μ x < ∞ := by
  exact lt_of_lt_of_le hx.2 le_top

theorem unitInterval_threshold_diff_tailCore_subset_badSet
    (μ : ProbabilityMeasure UnitInterval1038) (n : ℕ)
    (truncε δ : ℝ) :
    ({x : ℝ | 1 / ((n : ℝ) + 1) < unitIntervalLogPotential μ x} \
      unitIntervalThresholdTailCore μ n truncε δ) ⊆
        {x : ℝ | ENNReal.ofReal δ ≤ singularTailMass truncε μ x} := by
  intro x hx
  have hxS := hx.1
  have hxnot := hx.2
  have hnot_tail :
      ¬ singularTailMass truncε μ x < ENNReal.ofReal δ := by
    intro htail
    exact hxnot ⟨hxS, htail⟩
  exact le_of_not_gt hnot_tail

theorem unitInterval_threshold_diff_tailCore_measure_le
    (μ : ProbabilityMeasure UnitInterval1038) (n : ℕ)
    (truncε δ : ℝ) {η : ℝ≥0∞}
    (hbad :
      volume {x : ℝ | ENNReal.ofReal δ ≤ singularTailMass truncε μ x} ≤ η) :
    volume ({x : ℝ | 1 / ((n : ℝ) + 1) < unitIntervalLogPotential μ x} \
      unitIntervalThresholdTailCore μ n truncε δ) ≤ η := by
  exact le_trans
    (measure_mono (μ := volume)
      (unitInterval_threshold_diff_tailCore_subset_badSet μ n truncε δ))
    hbad

/--
Tail core with an explicit null exceptional set removed.  This is the form
needed to separate the diagonal-atom obstruction from the tail-control
argument: all analytic estimates are only required on `A \ N`, while `N`
costs no Lebesgue measure.
-/
def unitIntervalThresholdTailCoreOffDiagonal
    (μ : ProbabilityMeasure UnitInterval1038) (n : ℕ)
    (truncε δ : ℝ) (N : Set ℝ) : Set ℝ :=
  unitIntervalThresholdTailCore μ n truncε δ \ N

theorem unitIntervalThresholdTailCore_measurableSet
    (μ : ProbabilityMeasure UnitInterval1038) (n : ℕ)
    (truncε δ : ℝ) :
    MeasurableSet (unitIntervalThresholdTailCore μ n truncε δ) := by
  unfold unitIntervalThresholdTailCore
  exact
    (unitIntervalLogPotential_measurableSet_threshold μ
      (1 / ((n : ℝ) + 1))).inter
      (measurableSet_lt (measurable_singularTailMass truncε μ) measurable_const)

theorem unitIntervalThresholdTailCoreOffDiagonal_measurableSet
    (μ : ProbabilityMeasure UnitInterval1038) (n : ℕ)
    (truncε δ : ℝ) :
    MeasurableSet
      (unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ
        (diagonalAtomSet μ)) := by
  unfold unitIntervalThresholdTailCoreOffDiagonal
  exact (unitIntervalThresholdTailCore_measurableSet μ n truncε δ).diff
    (diagonalAtomSet_measurableSet μ)

theorem unitInterval_tailCoreOffDiagonal_subset_tailCore
    (μ : ProbabilityMeasure UnitInterval1038) (n : ℕ)
    (truncε δ : ℝ) (N : Set ℝ) :
    unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ N ⊆
      unitIntervalThresholdTailCore μ n truncε δ := by
  intro x hx
  exact hx.1

theorem singularTailMass_lt_top_of_mem_unitIntervalThresholdTailCoreOffDiagonal
    (μ : ProbabilityMeasure UnitInterval1038) (n : ℕ)
    (truncε δ : ℝ) (N : Set ℝ) {x : ℝ}
    (hx : x ∈ unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ N) :
    singularTailMass truncε μ x < ∞ := by
  exact singularTailMass_lt_top_of_mem_unitIntervalThresholdTailCore μ n truncε δ hx.1

theorem unitInterval_tailCoreOffDiagonal_subset_threshold
    (μ : ProbabilityMeasure UnitInterval1038) (n : ℕ)
    (truncε δ : ℝ) (N : Set ℝ) :
    unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ N ⊆
      {x : ℝ | 1 / ((n : ℝ) + 1) < unitIntervalLogPotential μ x} := by
  intro x hx
  exact unitInterval_tailCore_subset_threshold μ n truncε δ hx.1

theorem unitInterval_threshold_diff_tailCoreOffDiagonal_subset_badSet_union_null
    (μ : ProbabilityMeasure UnitInterval1038) (n : ℕ)
    (truncε δ : ℝ) (N : Set ℝ) :
    ({x : ℝ | 1 / ((n : ℝ) + 1) < unitIntervalLogPotential μ x} \
      unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ N) ⊆
        {x : ℝ | ENNReal.ofReal δ ≤ singularTailMass truncε μ x} ∪ N := by
  intro x hx
  by_cases hxN : x ∈ N
  · exact Or.inr hxN
  · have hxnotTail : x ∉ unitIntervalThresholdTailCore μ n truncε δ := by
      intro hxTail
      exact hx.2 ⟨hxTail, hxN⟩
    have hxTailDiff :
        x ∈ ({x : ℝ | 1 / ((n : ℝ) + 1) <
              unitIntervalLogPotential μ x} \
            unitIntervalThresholdTailCore μ n truncε δ) :=
      ⟨hx.1, hxnotTail⟩
    exact Or.inl
      (unitInterval_threshold_diff_tailCore_subset_badSet
        μ n truncε δ hxTailDiff)

theorem unitInterval_threshold_diff_tailCoreOffDiagonal_measure_le
    (μ : ProbabilityMeasure UnitInterval1038) (n : ℕ)
    (truncε δ : ℝ) (N : Set ℝ) {η : ℝ≥0∞}
    (hbad :
      volume {x : ℝ | ENNReal.ofReal δ ≤ singularTailMass truncε μ x} ≤ η)
    (hN : volume N = 0) :
    volume ({x : ℝ | 1 / ((n : ℝ) + 1) < unitIntervalLogPotential μ x} \
      unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ N) ≤ η := by
  have hmono :
      volume ({x : ℝ | 1 / ((n : ℝ) + 1) < unitIntervalLogPotential μ x} \
          unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ N) ≤
        volume ({x : ℝ | ENNReal.ofReal δ ≤ singularTailMass truncε μ x} ∪ N) :=
    measure_mono (μ := volume)
      (unitInterval_threshold_diff_tailCoreOffDiagonal_subset_badSet_union_null
        μ n truncε δ N)
  have hunion :
      volume ({x : ℝ | ENNReal.ofReal δ ≤ singularTailMass truncε μ x} ∪ N) ≤
        volume {x : ℝ | ENNReal.ofReal δ ≤ singularTailMass truncε μ x} +
          volume N :=
    measure_union_le _ _
  calc
    volume ({x : ℝ | 1 / ((n : ℝ) + 1) < unitIntervalLogPotential μ x} \
        unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ N)
        ≤ volume ({x : ℝ | ENNReal.ofReal δ ≤ singularTailMass truncε μ x} ∪ N) :=
          hmono
    _ ≤ volume {x : ℝ | ENNReal.ofReal δ ≤ singularTailMass truncε μ x} +
          volume N := hunion
    _ = volume {x : ℝ | ENNReal.ofReal δ ≤ singularTailMass truncε μ x} := by
          simp [hN]
    _ ≤ η := hbad

/--
Compact off-diagonal tail core with explicit measure budget.  If the bad
tail-mass set costs at most `ηBad`, and compact regularity spends `ηCore`, then
the positive threshold set is covered up to `ηBad + ηCore` by a compact subset of
the off-diagonal tail core.
-/
theorem unitIntervalThresholdTailCoreOffDiagonal_exists_compact_core
    (μ : ProbabilityMeasure UnitInterval1038) (n : ℕ)
    (truncε δ : ℝ) {ηBad ηCore η : ℝ≥0∞}
    (hηCore : ηCore ≠ 0)
    (hbad :
      volume {x : ℝ | ENNReal.ofReal δ ≤ singularTailMass truncε μ x} ≤
        ηBad)
    (hbudget : ηBad + ηCore ≤ η) :
    ∃ K : Set ℝ,
      K ⊆ unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ
        (diagonalAtomSet μ) ∧
      IsCompact K ∧
      volume ({x : ℝ | 1 / ((n : ℝ) + 1) <
        unitIntervalLogPotential μ x} \ K) ≤ η := by
  let S : Set ℝ :=
    {x : ℝ | 1 / ((n : ℝ) + 1) < unitIntervalLogPotential μ x}
  let A : Set ℝ :=
    unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ
      (diagonalAtomSet μ)
  have hAmeas : MeasurableSet A := by
    dsimp [A]
    exact unitIntervalThresholdTailCoreOffDiagonal_measurableSet μ n truncε δ
  have hSfinite : volume S ≠ ∞ := by
    exact unitIntervalLogPotential_threshold_measure_ne_top μ
      (by positivity : 0 ≤ 1 / ((n : ℝ) + 1))
  have hAfinite : volume A ≠ ∞ := by
    exact ne_top_of_le_ne_top hSfinite (measure_mono (by
      intro x hx
      dsimp [A] at hx
      exact unitInterval_tailCoreOffDiagonal_subset_threshold μ n truncε δ
        (diagonalAtomSet μ) hx))
  rcases hAmeas.exists_isCompact_diff_lt hAfinite hηCore with
    ⟨K, hKsubA, hKcompact, hA_diff_lt⟩
  have hSdiffA :
      volume (S \ A) ≤ ηBad := by
    dsimp [S, A]
    exact unitInterval_threshold_diff_tailCoreOffDiagonal_measure_le
      μ n truncε δ (diagonalAtomSet μ) hbad (diagonalAtomSet_volume_zero μ)
  have hsubset :
      S \ K ⊆ (S \ A) ∪ (A \ K) := by
    intro x hx
    by_cases hxA : x ∈ A
    · exact Or.inr ⟨hxA, hx.2⟩
    · exact Or.inl ⟨hx.1, hxA⟩
  have hmono :
      volume (S \ K) ≤ volume ((S \ A) ∪ (A \ K)) :=
    measure_mono (μ := volume) hsubset
  have hunion :
      volume ((S \ A) ∪ (A \ K)) ≤ volume (S \ A) + volume (A \ K) :=
    measure_union_le _ _
  refine ⟨K, ?_, hKcompact, ?_⟩
  · simpa [A] using hKsubA
  · calc
      volume ({x : ℝ | 1 / ((n : ℝ) + 1) <
          unitIntervalLogPotential μ x} \ K)
          = volume (S \ K) := rfl
      _ ≤ volume ((S \ A) ∪ (A \ K)) := hmono
      _ ≤ volume (S \ A) + volume (A \ K) := hunion
      _ ≤ ηBad + ηCore := by
            exact add_le_add hSdiffA (le_of_lt hA_diff_lt)
      _ ≤ η := hbudget

theorem unitInterval_tailCore_limit_error
    {μ : ProbabilityMeasure UnitInterval1038} {n : ℕ} {truncε δ : ℝ}
    (hδ : 0 < δ)
    (herror : ∀ x ∈ unitIntervalThresholdTailCore μ n truncε δ,
      ENNReal.ofReal
        |unitIntervalTruncatedPotential truncε μ x -
          unitIntervalLogPotential μ x| ≤ singularTailMass truncε μ x) :
    ∀ x ∈ unitIntervalThresholdTailCore μ n truncε δ,
      |unitIntervalTruncatedPotential truncε μ x -
        unitIntervalLogPotential μ x| < δ := by
  refine core_limit_error_from_tail_bound hδ herror ?_
  intro x hx
  exact hx.2

theorem unitInterval_badSet_core_from_tailCore
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ truncε δ : ℝ,
          0 < δ ∧
          volume {x : ℝ | ENNReal.ofReal δ ≤ singularTailMass truncε μ x} ≤
            (ε : ℝ≥0∞) ∧
          (∀ x ∈ unitIntervalThresholdTailCore μ n truncε δ,
            ENNReal.ofReal
              |unitIntervalTruncatedPotential truncε μ x -
                unitIntervalLogPotential μ x| ≤ singularTailMass truncε μ x) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ unitIntervalThresholdTailCore μ n truncε δ,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalLogPotential ν x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ unitIntervalThresholdTailCore μ n truncε δ,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalTruncatedPotential truncε μ x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          δ ≤ (1 / ((n : ℝ) + 1)) / 3) :
    ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ truncε : ℝ, ∃ A : Set ℝ,
          A ⊆ {x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} ∧
          volume ({x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} \ A) ≤ (ε : ℝ≥0∞) ∧
          (∀ x ∈ A,
            |unitIntervalTruncatedPotential truncε μ x -
              unitIntervalLogPotential μ x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ A,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalLogPotential ν x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ A,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalTruncatedPotential truncε μ x| <
              (1 / ((n : ℝ) + 1)) / 3) := by
  intro μ n ε hε
  rcases hcore μ n ε hε with
    ⟨truncε, δ, hδ, hbad, herror, hseq, htrunc, hδ_le⟩
  let A := unitIntervalThresholdTailCore μ n truncε δ
  refine ⟨truncε, A, ?_, ?_, ?_, hseq, htrunc⟩
  · exact unitInterval_tailCore_subset_threshold μ n truncε δ
  · exact unitInterval_threshold_diff_tailCore_measure_le μ n truncε δ hbad
  · intro x hx
    have hlt :=
      unitInterval_tailCore_limit_error (μ := μ) (n := n)
        (truncε := truncε) (δ := δ) hδ herror x hx
    exact lt_of_lt_of_le hlt hδ_le

/--
Off-diagonal version of the tail-core assembly.  The input may remove a
Lebesgue-null exceptional set `N` from the core before asking for the logarithmic
integrability/error estimates.  This isolates the only place where atoms of
`μ` can obstruct the real-valued logarithmic potential.
-/
theorem unitInterval_badSet_core_from_tailCore_offDiagonal
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ truncε δ : ℝ, ∃ N : Set ℝ,
          0 < δ ∧
          volume N = 0 ∧
          volume {x : ℝ | ENNReal.ofReal δ ≤ singularTailMass truncε μ x} ≤
            (ε : ℝ≥0∞) ∧
          (∀ x ∈ unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ N,
            ENNReal.ofReal
              |unitIntervalTruncatedPotential truncε μ x -
                unitIntervalLogPotential μ x| ≤ singularTailMass truncε μ x) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈
              unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ N,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalLogPotential ν x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈
              unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ N,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalTruncatedPotential truncε μ x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          δ ≤ (1 / ((n : ℝ) + 1)) / 3) :
    ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ truncε : ℝ, ∃ A : Set ℝ,
          A ⊆ {x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} ∧
          volume ({x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} \ A) ≤ (ε : ℝ≥0∞) ∧
          (∀ x ∈ A,
            |unitIntervalTruncatedPotential truncε μ x -
              unitIntervalLogPotential μ x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ A,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalLogPotential ν x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ A,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalTruncatedPotential truncε μ x| <
              (1 / ((n : ℝ) + 1)) / 3) := by
  intro μ n ε hε
  rcases hcore μ n ε hε with
    ⟨truncε, δ, N, hδ, hN, hbad, herror, hseq, htrunc, hδ_le⟩
  let A := unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ N
  refine ⟨truncε, A, ?_, ?_, ?_, hseq, htrunc⟩
  · exact unitInterval_tailCoreOffDiagonal_subset_threshold μ n truncε δ N
  · exact unitInterval_threshold_diff_tailCoreOffDiagonal_measure_le
      μ n truncε δ N hbad hN
  · intro x hx
    have htail : singularTailMass truncε μ x < ENNReal.ofReal δ := hx.1.2
    have hlt :=
      truncated_potential_error_lt_of_tail_bound hδ
        (herror x hx) htail
    exact lt_of_lt_of_le hlt hδ_le

theorem unitInterval_threshold_approx_of_tailCore
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ truncε δ : ℝ,
          0 < δ ∧
          volume {x : ℝ | ENNReal.ofReal δ ≤ singularTailMass truncε μ x} ≤
            (ε : ℝ≥0∞) ∧
          (∀ x ∈ unitIntervalThresholdTailCore μ n truncε δ,
            ENNReal.ofReal
              |unitIntervalTruncatedPotential truncε μ x -
                unitIntervalLogPotential μ x| ≤ singularTailMass truncε μ x) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ unitIntervalThresholdTailCore μ n truncε δ,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalLogPotential ν x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ unitIntervalThresholdTailCore μ n truncε δ,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalTruncatedPotential truncε μ x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          δ ≤ (1 / ((n : ℝ) + 1)) / 3) :
    ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ A : Set ℝ,
          volume {x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} ≤
            volume A + (ε : ℝ≥0∞) ∧
          ∀ᶠ ν in nhds μ,
            A ⊆ {x : ℝ | 0 < unitIntervalLogPotential ν x} := by
  exact unitInterval_threshold_approx_of_badSet_core
    (unitInterval_badSet_core_from_tailCore hcore)

theorem unitInterval_threshold_approx_of_tailCore_offDiagonal
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ truncε δ : ℝ, ∃ N : Set ℝ,
          0 < δ ∧
          volume N = 0 ∧
          volume {x : ℝ | ENNReal.ofReal δ ≤ singularTailMass truncε μ x} ≤
            (ε : ℝ≥0∞) ∧
          (∀ x ∈ unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ N,
            ENNReal.ofReal
              |unitIntervalTruncatedPotential truncε μ x -
                unitIntervalLogPotential μ x| ≤ singularTailMass truncε μ x) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈
              unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ N,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalLogPotential ν x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈
              unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ N,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalTruncatedPotential truncε μ x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          δ ≤ (1 / ((n : ℝ) + 1)) / 3) :
    ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ A : Set ℝ,
          volume {x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} ≤
            volume A + (ε : ℝ≥0∞) ∧
          ∀ᶠ ν in nhds μ,
            A ⊆ {x : ℝ | 0 < unitIntervalLogPotential ν x} := by
  exact unitInterval_threshold_approx_of_badSet_core
    (unitInterval_badSet_core_from_tailCore_offDiagonal hcore)

lemma singularTailKernel_lintegral_le_ofReal_two_mul
    (ε : ℝ) (t : UnitInterval1038) :
    (∫⁻ x : ℝ, singularTailKernel ε x t ∂volume) ≤ ENNReal.ofReal (2 * ε) := by
  by_cases hεpos : 0 < ε
  ·
    let g : ℝ → ℝ≥0∞ :=
      Set.indicator (Set.Ioo (-ε) ε) (fun x => ENNReal.ofReal (Real.log (ε / |x|)))
    let f : ℝ → ℝ := fun x => Real.log (ε / |x|)
    have hmeas : MeasurableSet (Set.Ioo (-ε) ε) := isOpen_Ioo.measurableSet
    have htranslate :
        (fun x : ℝ => singularTailKernel ε x t) =ᵐ[volume] fun x : ℝ => g (x - (t : ℝ)) := by
      filter_upwards with x
      by_cases hx : |x - (t : ℝ)| < ε
      · have hxmem : x - (t : ℝ) ∈ Set.Ioo (-ε) ε := by
          simpa [Set.mem_Ioo] using (abs_lt.mp hx)
        simp [singularTailKernel, g, hxmem, hx]
      · have hxmem : x - (t : ℝ) ∉ Set.Ioo (-ε) ε := by
          intro hxm
          exact hx (abs_lt.2 (by simpa [Set.mem_Ioo] using hxm))
        simp [singularTailKernel, g, hxmem, hx]
    have hshift :
        (∫⁻ x : ℝ, singularTailKernel ε x t ∂volume) =
          ∫⁻ x : ℝ, g (x - (t : ℝ)) ∂volume := by
      exact MeasureTheory.lintegral_congr_ae htranslate
    have hshift' :
        (∫⁻ x : ℝ, g (x - (t : ℝ)) ∂volume) =
          ∫⁻ x : ℝ, g x ∂volume := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (MeasureTheory.lintegral_add_right_eq_self (μ := volume) (f := g) (-(t : ℝ)))
    have href :
        (∫⁻ x : ℝ, g x ∂volume) =
          ∫⁻ x : ℝ in Set.Ioo (-ε) ε, ENNReal.ofReal (Real.log (ε / |x|)) ∂volume := by
      simp [g]
    have hint :
        (∫⁻ x : ℝ, g x ∂volume) = ENNReal.ofReal (2 * ε) := by
      have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (-ε) ε)] f := by
        refine (ae_restrict_iff' isOpen_Ioo.measurableSet).2 ?_
        refine Filter.Eventually.of_forall ?_
        intro x hx
        by_cases hx0 : x = 0
        · simp [f, hx0]
        · have hxa : |x| < ε := by
            exact (abs_lt).2 (by simpa [Set.mem_Ioo] using hx)
          have h1 : 1 ≤ ε / |x| := (one_le_div (abs_pos.2 hx0)).2 (le_of_lt hxa)
          have hlog : 0 ≤ Real.log (ε / |x|) := Real.log_nonneg h1
          simpa [f] using hlog
      have hfm : AEStronglyMeasurable f (volume.restrict (Set.Ioo (-ε) ε)) := by
        have hmf : Measurable f := by
          measurability
        exact hmf.aestronglyMeasurable
      have hEq_toReal :
          (∫ x : ℝ, f x ∂(volume.restrict (Set.Ioo (-ε) ε))) =
            (∫⁻ x : ℝ, ENNReal.ofReal (f x) ∂(volume.restrict (Set.Ioo (-ε) ε))).toReal := by
        exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnn hfm
      have hIoo_to_Int :
          (∫ x : ℝ, f x ∂(volume.restrict (Set.Ioo (-ε) ε))) =
            ∫ (x : ℝ) in (-ε)..ε, f x ∂volume := by
        calc
          (∫ x : ℝ, f x ∂(volume.restrict (Set.Ioo (-ε) ε)))
              = ∫ (x : ℝ) in Set.Ioo (-ε) ε, f x ∂volume := by simp
          _ = ∫ (x : ℝ) in Set.Ioc (-ε) ε, f x ∂volume := by
            simpa using (MeasureTheory.integral_Ioc_eq_integral_Ioo (μ := volume) (f := f)).symm
          _ = ∫ (x : ℝ) in (-ε)..ε, f x ∂volume := by
            simpa [Set.uIcc_of_le (show -ε ≤ ε by nlinarith)] using
              (intervalIntegral.integral_of_le (μ := volume) (f := f)
                (a := -ε) (b := ε) (by nlinarith)).symm
      have hnegEq :
          (∫ (x : ℝ) in (-ε)..0, f x ∂volume) = (∫ (x : ℝ) in 0..ε, f x ∂volume) := by
        calc
          (∫ (x : ℝ) in (-ε)..0, f x ∂volume)
              = ∫ (x : ℝ) in 0..ε, f (-x) ∂volume := by
                  simp
          _ = ∫ (x : ℝ) in 0..ε, f x ∂volume := by
                simp [f]
      have hEqOn : Set.EqOn f (fun x => Real.log ε - Real.log x) (Set.uIoc 0 ε) := by
        intro x hx
        have hx' : x ∈ Set.Ioc 0 ε := by
          simpa [Set.uIoc_of_le hεpos.le] using hx
        have hxpos : 0 < x := hx'.1
        have hxabs : |x| = x := abs_of_pos hxpos
        have hxne : x ≠ 0 := ne_of_gt hxpos
        simp [f, hxabs, Real.log_div hεpos.ne' hxne]
      have h0_eq : ∀ᵐ x ∂volume, x ∈ Set.uIoc 0 ε →
          f x = Real.log ε - Real.log x := by
        exact Filter.Eventually.of_forall hEqOn
      have hconst : IntervalIntegrable (fun _ : ℝ => Real.log ε) volume 0 ε :=
        intervalIntegral.intervalIntegrable_const
      have hlog : IntervalIntegrable (fun x : ℝ => Real.log x) volume 0 ε :=
        intervalIntegral.intervalIntegrable_log'
      have hsub : IntervalIntegrable (fun x : ℝ => Real.log ε - Real.log x) volume 0 ε :=
        hconst.sub hlog
      have h_int : IntervalIntegrable f volume 0 ε :=
        (intervalIntegrable_congr hEqOn).2 hsub
      have hposInt : (∫ (x : ℝ) in 0..ε, f x ∂volume) = ε := by
        have hconstInt : (∫ (x : ℝ) in 0..ε, (fun _ : ℝ => Real.log ε) x ∂volume) = (ε - 0) * Real.log ε := by
          rw [intervalIntegral.integral_const]
          simp [smul_eq_mul]
        calc
          (∫ (x : ℝ) in 0..ε, f x ∂volume)
              = ∫ (x : ℝ) in 0..ε, (fun x => Real.log ε - Real.log x) x ∂volume := by
                  exact intervalIntegral.integral_congr_ae h0_eq
          _ = ∫ (x : ℝ) in 0..ε, (fun _ : ℝ => Real.log ε) x ∂volume
                - ∫ (x : ℝ) in 0..ε, (fun x => Real.log x) x ∂volume := by
                  simpa [sub_eq_add_neg] using (intervalIntegral.integral_sub hconst hlog)
          _ = (ε - 0) * Real.log ε - (ε * Real.log ε - ε) := by
                rw [hconstInt, integral_log_from_zero_of_pos hεpos]
          _ = ε := by
                ring
      have hnegInt : IntervalIntegrable f volume (-ε) 0 := by
        have haux : IntervalIntegrable (fun x : ℝ => f (x * (-1 : ℝ)))
            volume (0 / -1) (ε / -1) :=
          h_int.comp_mul_right (c := (-1 : ℝ))
        have haux' : IntervalIntegrable (fun x : ℝ => f (x * (-1 : ℝ))) volume (-ε) 0 := by
          simpa [div_eq_mul_inv] using haux.symm
        exact (intervalIntegrable_congr (by
          intro x hx
          simp [f])).2 haux'
      have hhalf :
          (∫ (x : ℝ) in (-ε)..ε, f x ∂volume) =
            2 * ∫ (x : ℝ) in 0..ε, f x ∂volume := by
        calc
          (∫ (x : ℝ) in (-ε)..ε, f x ∂volume)
              = (∫ (x : ℝ) in (-ε)..0, f x ∂volume)
                  + ∫ (x : ℝ) in 0..ε, f x ∂volume := by
                exact (intervalIntegral.integral_add_adjacent_intervals hnegInt h_int).symm
          _ = (∫ (x : ℝ) in 0..ε, f x ∂volume)
                + ∫ (x : ℝ) in 0..ε, f x ∂volume := by
                rw [hnegEq]
          _ = 2 * ∫ (x : ℝ) in 0..ε, f x ∂volume := by ring
      have hIntIoo :
          (∫ x : ℝ, f x ∂(volume.restrict (Set.Ioo (-ε) ε))) = 2 * ε := by
        calc
          (∫ x : ℝ, f x ∂(volume.restrict (Set.Ioo (-ε) ε)))
              = ∫ (x : ℝ) in (-ε)..ε, f x ∂volume := hIoo_to_Int
          _ = 2 * ∫ (x : ℝ) in 0..ε, f x ∂volume := hhalf
          _ = 2 * ε := by rw [hposInt]
      have htoReal :
          (∫⁻ x : ℝ, ENNReal.ofReal (f x) ∂(volume.restrict (Set.Ioo (-ε) ε))).toReal = 2 * ε := by
        calc
          (∫⁻ x : ℝ, ENNReal.ofReal (f x) ∂(volume.restrict (Set.Ioo (-ε) ε))).toReal
              = (∫ x : ℝ, f x ∂(volume.restrict (Set.Ioo (-ε) ε))) := hEq_toReal.symm
          _ = 2 * ε := hIntIoo
      have htoTop :
          (∫⁻ x : ℝ, ENNReal.ofReal (f x) ∂(volume.restrict (Set.Ioo (-ε) ε)) ) ≠ ⊤ := by
        intro htop
        rw [htop, ENNReal.toReal_top] at htoReal
        nlinarith [hεpos]
      have htoReal' : (∫⁻ x : ℝ, ENNReal.ofReal (f x) ∂(volume.restrict (Set.Ioo (-ε) ε))).toReal = 2 * (ENNReal.ofReal ε).toReal := by
        simpa [ENNReal.toReal_ofReal hεpos.le] using htoReal
      have htarget :
          (∫⁻ x : ℝ, ENNReal.ofReal (f x) ∂(volume.restrict (Set.Ioo (-ε) ε)) ) = ENNReal.ofReal (2 * ε) := by
        apply
          (ENNReal.toReal_eq_toReal_iff'
            (x := ∫⁻ x : ℝ, ENNReal.ofReal (f x) ∂(volume.restrict (Set.Ioo (-ε) ε)))
            (y := ENNReal.ofReal (2 * ε)) htoTop ENNReal.ofReal_ne_top).1
        simpa [ENNReal.toReal_ofReal (show 0 ≤ 2 * ε by positivity)] using htoReal'
      calc
        (∫⁻ x : ℝ, g x ∂volume) =
            ∫⁻ x : ℝ in Set.Ioo (-ε) ε, ENNReal.ofReal (f x) ∂volume := href
        _ = ENNReal.ofReal (2 * ε) := by
              simpa [f] using htarget
    exact le_of_eq (by
      calc
        (∫⁻ x : ℝ, singularTailKernel ε x t ∂volume)
            = ∫⁻ x : ℝ, g (x - (t : ℝ)) ∂volume := hshift
        _ = ∫⁻ x : ℝ, g x ∂volume := hshift'
        _ = ENNReal.ofReal (2 * ε) := hint)
  ·
    have hε : ε ≤ 0 := le_of_not_gt hεpos
    have hε' : 2 * ε ≤ 0 := by
      nlinarith
    have hzero : ∀ x : ℝ, singularTailKernel ε x t = 0 := by
      intro x
      have hnot : ¬ |x - (t : ℝ)| < ε := by
        exact not_lt_of_ge (le_trans hε (abs_nonneg (x - (t : ℝ))))
      simp [singularTailKernel, hnot]
    have hzeroInt : (∫⁻ x : ℝ, singularTailKernel ε x t ∂volume) = 0 := by
      simp [hzero]
    simpa [hε', ENNReal.ofReal_of_nonpos hε'] using hzeroInt

lemma singularTail_badSet_volume_le_of_lintegral_bound
    (ε : ℝ) (μ : ProbabilityMeasure UnitInterval1038)
    {η C : ℝ≥0∞}
    (hη0 : η ≠ 0) (hηtop : η ≠ ∞)
    (hS : MeasurableSet {x : ℝ | η < singularTailMass ε μ x})
    (hint : ∫⁻ x : ℝ, singularTailMass ε μ x ∂volume ≤ C) :
    volume {x : ℝ | η < singularTailMass ε μ x} ≤ C / η := by
  exact lintegral_markov_bound volume (singularTailMass ε μ)
    hη0 hηtop hS hint

lemma singularTail_closed_badSet_volume_le_of_lintegral_bound
    (ε : ℝ) (μ : ProbabilityMeasure UnitInterval1038)
    {δ C η : ℝ≥0∞}
    (hδ0 : δ ≠ 0)
    (hδtop : δ ≠ ∞)
    (hδhalf0 : δ / 2 ≠ 0)
    (hδhalftop : δ / 2 ≠ ∞)
    (hstrictMeas : MeasurableSet {x : ℝ | δ / 2 < singularTailMass ε μ x})
    (hint : ∫⁻ x : ℝ, singularTailMass ε μ x ∂volume ≤ C)
    (hbound : C / (δ / 2) ≤ η) :
    volume {x : ℝ | δ ≤ singularTailMass ε μ x} ≤ η := by
  have hsub :
      {x : ℝ | δ ≤ singularTailMass ε μ x} ⊆
        {x : ℝ | δ / 2 < singularTailMass ε μ x} := by
    intro x hx
    exact lt_of_lt_of_le (b := δ)
      (ENNReal.half_lt_self hδ0 hδtop)
      (show δ ≤ singularTailMass ε μ x from hx)
  calc
    volume {x : ℝ | δ ≤ singularTailMass ε μ x}
        ≤ volume {x : ℝ | δ / 2 < singularTailMass ε μ x} :=
          measure_mono (μ := volume) hsub
    _ ≤ C / (δ / 2) :=
          singularTail_badSet_volume_le_of_lintegral_bound ε μ
            hδhalf0 hδhalftop hstrictMeas hint
    _ ≤ η := hbound

lemma singularTail_total_lintegral_le_of_pointwise_bound
    (ε : ℝ) (μ : ProbabilityMeasure UnitInterval1038) {C : ℝ≥0∞}
    (hmeas :
      AEMeasurable
        (Function.uncurry (fun x t => singularTailKernel ε x t))
        (volume.prod (μ : Measure UnitInterval1038)))
    (hbound : ∀ t : UnitInterval1038,
      (∫⁻ x : ℝ, singularTailKernel ε x t ∂volume) ≤ C) :
    (∫⁻ x : ℝ, singularTailMass ε μ x ∂volume) ≤ C := by
  unfold singularTailMass
  calc
    (∫⁻ x : ℝ, ∫⁻ t : UnitInterval1038,
        singularTailKernel ε x t ∂(μ : Measure UnitInterval1038) ∂volume)
        = ∫⁻ t : UnitInterval1038, ∫⁻ x : ℝ,
            singularTailKernel ε x t ∂volume ∂(μ : Measure UnitInterval1038) := by
          exact lintegral_lintegral_swap hmeas
    _ ≤ ∫⁻ _t : UnitInterval1038, C ∂(μ : Measure UnitInterval1038) := by
          exact lintegral_mono (fun t => hbound t)
    _ = C := by simp

lemma singularTail_badSet_volume_le_of_pointwise_lintegral_bound
    (ε : ℝ) (μ : ProbabilityMeasure UnitInterval1038)
    {η C : ℝ≥0∞}
    (hη0 : η ≠ 0) (hηtop : η ≠ ∞)
    (hS : MeasurableSet {x : ℝ | η < singularTailMass ε μ x})
    (hmeas :
      AEMeasurable
        (Function.uncurry (fun x t => singularTailKernel ε x t))
        (volume.prod (μ : Measure UnitInterval1038)))
    (hbound : ∀ t : UnitInterval1038,
      (∫⁻ x : ℝ, singularTailKernel ε x t ∂volume) ≤ C) :
    volume {x : ℝ | η < singularTailMass ε μ x} ≤ C / η := by
  exact singularTail_badSet_volume_le_of_lintegral_bound ε μ
    hη0 hηtop hS
    (singularTail_total_lintegral_le_of_pointwise_bound ε μ hmeas hbound)

lemma singularTail_closed_badSet_volume_le_of_pointwise_lintegral_bound
    (ε : ℝ) (μ : ProbabilityMeasure UnitInterval1038)
    {δ C η : ℝ≥0∞}
    (hδ0 : δ ≠ 0)
    (hδtop : δ ≠ ∞)
    (hδhalf0 : δ / 2 ≠ 0)
    (hδhalftop : δ / 2 ≠ ∞)
    (hstrictMeas : MeasurableSet {x : ℝ | δ / 2 < singularTailMass ε μ x})
    (hmeas :
      AEMeasurable
        (Function.uncurry (fun x t => singularTailKernel ε x t))
        (volume.prod (μ : Measure UnitInterval1038)))
    (hbound : ∀ t : UnitInterval1038,
      (∫⁻ x : ℝ, singularTailKernel ε x t ∂volume) ≤ C)
    (hfinal : C / (δ / 2) ≤ η) :
    volume {x : ℝ | δ ≤ singularTailMass ε μ x} ≤ η := by
  exact singularTail_closed_badSet_volume_le_of_lintegral_bound ε μ
    hδ0 hδtop hδhalf0 hδhalftop hstrictMeas
    (singularTail_total_lintegral_le_of_pointwise_bound ε μ hmeas hbound)
    hfinal

lemma singularTail_closed_badSet_volume_le_of_two_mul
    (ε : ℝ) (μ : ProbabilityMeasure UnitInterval1038)
    {δ η : ℝ≥0∞}
    (hδ0 : δ ≠ 0)
    (hδtop : δ ≠ ∞)
    (hδhalf0 : δ / 2 ≠ 0)
    (hδhalftop : δ / 2 ≠ ∞)
    (hstrictMeas : MeasurableSet {x : ℝ | δ / 2 < singularTailMass ε μ x})
    (hmeas :
      AEMeasurable
        (Function.uncurry (fun x t => singularTailKernel ε x t))
        (volume.prod (μ : Measure UnitInterval1038)))
    (hfinal : ENNReal.ofReal (2 * ε) / (δ / 2) ≤ η) :
    volume {x : ℝ | δ ≤ singularTailMass ε μ x} ≤ η := by
  exact singularTail_closed_badSet_volume_le_of_pointwise_lintegral_bound ε μ
    hδ0 hδtop hδhalf0 hδhalftop hstrictMeas hmeas
    (fun t => singularTailKernel_lintegral_le_ofReal_two_mul ε t)
    hfinal

lemma singularTail_closed_badSet_volume_le_of_two_mul'
    (ε : ℝ) (μ : ProbabilityMeasure UnitInterval1038)
    {δ η : ℝ≥0∞}
    (hδ0 : δ ≠ 0)
    (hδtop : δ ≠ ∞)
    (hδhalf0 : δ / 2 ≠ 0)
    (hδhalftop : δ / 2 ≠ ∞)
    (hfinal : ENNReal.ofReal (2 * ε) / (δ / 2) ≤ η) :
    volume {x : ℝ | δ ≤ singularTailMass ε μ x} ≤ η := by
  exact singularTail_closed_badSet_volume_le_of_two_mul ε μ
    hδ0 hδtop hδhalf0 hδhalftop
    (measurableSet_singularTailMass_strict ε μ (δ / 2))
    (aemeasurable_singularTailKernel_uncurry ε μ)
    hfinal

lemma singularTail_closed_badSet_volume_le_of_two_mul_real_threshold
    (ε : ℝ) (μ : ProbabilityMeasure UnitInterval1038)
    {δ : ℝ} {η : ℝ≥0∞}
    (hδ : 0 < δ)
    (hfinal : ENNReal.ofReal (2 * ε) / (ENNReal.ofReal δ / 2) ≤ η) :
    volume {x : ℝ | ENNReal.ofReal δ ≤ singularTailMass ε μ x} ≤ η := by
  have hδ0 : ENNReal.ofReal δ ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hδ)
  have hδtop : ENNReal.ofReal δ ≠ ∞ := ENNReal.ofReal_ne_top
  have hhalf0 : ENNReal.ofReal δ / 2 ≠ 0 := by
    rw [ENNReal.div_eq_inv_mul]
    exact mul_ne_zero (by simp) hδ0
  have hhalftop : ENNReal.ofReal δ / 2 ≠ ∞ := by
    rw [ENNReal.div_eq_inv_mul]
    exact ENNReal.mul_ne_top (by simp) hδtop
  exact singularTail_closed_badSet_volume_le_of_two_mul' ε μ
    hδ0 hδtop hhalf0 hhalftop hfinal

lemma exists_tailScale_for_target {δ : ℝ} {η : NNReal}
    (hδ : 0 < δ) (hη : 0 < η) :
    ∃ truncε : ℝ,
      0 < truncε ∧
      ENNReal.ofReal (2 * truncε) / (ENNReal.ofReal δ / 2) ≤
        (η : ℝ≥0∞) := by
  refine ⟨δ * (η : ℝ) / 8, ?_, ?_⟩
  · positivity
  · have hden_eq : ENNReal.ofReal δ / 2 = ENNReal.ofReal (δ / 2) := by
      simpa using
        (ENNReal.ofReal_div_of_pos (x := δ) (y := 2)
          (by norm_num : (0 : ℝ) < 2)).symm
    rw [hden_eq]
    have hden0 : ENNReal.ofReal (δ / 2) ≠ 0 := by
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity : 0 < δ / 2))
    have hdentop : ENNReal.ofReal (δ / 2) ≠ ∞ := ENNReal.ofReal_ne_top
    rw [ENNReal.div_le_iff hden0 hdentop]
    have hright :
        (η : ℝ≥0∞) * ENNReal.ofReal (δ / 2) =
          ENNReal.ofReal ((η : ℝ) * (δ / 2)) := by
      rw [ENNReal.coe_nnreal_eq]
      rw [← ENNReal.ofReal_mul (show 0 ≤ (η : ℝ) by exact η.2)]
    rw [hright]
    rw [ENNReal.ofReal_le_ofReal_iff]
    · nlinarith [η.2]
    · positivity

lemma exists_tailThreshold_for_target (ε : ℝ) {η : NNReal}
    (hη : 0 < η) :
    ∃ δ : ℝ,
      0 < δ ∧
      ENNReal.ofReal (2 * ε) / (ENNReal.ofReal δ / 2) ≤
        (η : ℝ≥0∞) := by
  let A : ℝ := max (2 * ε) 0 + 1
  have hApos : 0 < A := by
    dsimp [A]
    nlinarith [le_max_right (2 * ε) (0 : ℝ)]
  refine ⟨4 * A / (η : ℝ), ?_, ?_⟩
  · positivity
  · have hδpos : 0 < 4 * A / (η : ℝ) := by positivity
    have hden_eq :
        ENNReal.ofReal (4 * A / (η : ℝ)) / 2 =
          ENNReal.ofReal ((4 * A / (η : ℝ)) / 2) := by
      simpa using
        (ENNReal.ofReal_div_of_pos (x := 4 * A / (η : ℝ)) (y := 2)
          (by norm_num : (0 : ℝ) < 2)).symm
    rw [hden_eq]
    have hden0 : ENNReal.ofReal ((4 * A / (η : ℝ)) / 2) ≠ 0 := by
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
    have hdentop : ENNReal.ofReal ((4 * A / (η : ℝ)) / 2) ≠ ∞ :=
      ENNReal.ofReal_ne_top
    rw [ENNReal.div_le_iff hden0 hdentop]
    have hright :
        (η : ℝ≥0∞) * ENNReal.ofReal ((4 * A / (η : ℝ)) / 2) =
          ENNReal.ofReal ((η : ℝ) * ((4 * A / (η : ℝ)) / 2)) := by
      rw [ENNReal.coe_nnreal_eq]
      rw [← ENNReal.ofReal_mul (show 0 ≤ (η : ℝ) by exact η.2)]
    rw [hright]
    apply ENNReal.ofReal_le_ofReal
    have hleA : 2 * ε ≤ A := by
      dsimp [A]
      nlinarith [le_max_left (2 * ε) (0 : ℝ)]
    have heta_pos : 0 < (η : ℝ) := by exact_mod_cast hη
    field_simp [ne_of_gt heta_pos]
    nlinarith

/--
Arbitrarily small closed singular-tail exceptional set.  Outside this set, the
fixed-scale singular tail mass is finite.
-/
theorem singularTail_exists_small_finite_exception
    (ε : ℝ) (μ : ProbabilityMeasure UnitInterval1038)
    (η : NNReal) (hη : 0 < η) :
    ∃ N : Set ℝ,
      volume N ≤ (η : ℝ≥0∞) ∧
      ∀ x : ℝ, x ∉ N → singularTailMass ε μ x < ∞ := by
  rcases exists_tailThreshold_for_target ε hη with
    ⟨δ, hδ, hscale⟩
  refine ⟨{x : ℝ | ENNReal.ofReal δ ≤ singularTailMass ε μ x}, ?_, ?_⟩
  · exact singularTail_closed_badSet_volume_le_of_two_mul_real_threshold
      ε μ hδ hscale
  · intro x hxN
    have hlt : singularTailMass ε μ x < ENNReal.ofReal δ := by
      exact lt_of_not_ge hxN
    exact lt_trans hlt ENNReal.ofReal_lt_top

/--
Strict-outside/off-diagonal version of the small singular-tail exceptional-set
provider.  The exceptional set itself comes from the global tail estimate; the
extra strict-outside and off-diagonal hypotheses are preserved for the
replacement objective interface.
-/
theorem singularTail_exists_small_strictOutside_exception
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    (ε : ℝ)
    (η : NNReal) (hη : 0 < η) :
    ∃ N : Set ℝ,
      volume N ≤ (η : ℝ≥0∞) ∧
      ∀ x : ℝ, StrictOutsideComponent C x →
        x ∉ diagonalAtomSet μ → x ∉ N → singularTailMass ε μ x < ∞ := by
  rcases singularTail_exists_small_finite_exception ε μ η hη with
    ⟨N, hN, hfinite⟩
  refine ⟨N, hN, ?_⟩
  intro x _hxstrict _hxdiag hxN
  exact hfinite x hxN

/--
Adding diagonal atom locations to an arbitrary small exceptional set does not
increase its Lebesgue-volume budget, because the diagonal atom set is countable.
-/
theorem diagonalAtomSet_union_exception_volume_le
    (μ : ProbabilityMeasure UnitInterval1038) {N : Set ℝ} {η : ℝ≥0∞}
    (hN : volume N ≤ η) :
    volume (diagonalAtomSet μ ∪ N) ≤ η := by
  calc
    volume (diagonalAtomSet μ ∪ N)
        ≤ volume (diagonalAtomSet μ) + volume N :=
          measure_union_le (μ := volume) (diagonalAtomSet μ) N
    _ = volume N := by simp [diagonalAtomSet_volume_zero μ]
    _ ≤ η := hN

/--
Small exceptional set with the diagonal atom set already included.  Outside the
union, the point is automatically off diagonal and has finite singular tail
mass.
-/
theorem singularTail_exists_small_exception_with_diagonal
    (ε : ℝ) (μ : ProbabilityMeasure UnitInterval1038)
    (η : NNReal) (hη : 0 < η) :
    ∃ N : Set ℝ,
      volume N ≤ (η : ℝ≥0∞) ∧
      diagonalAtomSet μ ⊆ N ∧
      ∀ x : ℝ, x ∉ N → singularTailMass ε μ x < ∞ := by
  rcases singularTail_exists_small_finite_exception ε μ η hη with
    ⟨N0, hN0, hfinite⟩
  refine ⟨diagonalAtomSet μ ∪ N0, ?_, ?_, ?_⟩
  · exact diagonalAtomSet_union_exception_volume_le μ hN0
  · intro x hx
    exact Or.inl hx
  · intro x hx
    exact hfinite x (fun hxN0 => hx (Or.inr hxN0))

theorem unitIntervalLogPotential_objective_lsc_from_tail_control
    {ι : Type*} {L : Filter ι}
    (μ : ProbabilityMeasure UnitInterval1038)
    (μs : ι → ProbabilityMeasure UnitInterval1038)
    (εOf : ℕ → ℝ)
    (hlimitTail : ∀ n x,
      |unitIntervalTruncatedPotential (εOf n) μ x -
        unitIntervalLogPotential μ x| <
        (1 / ((n : ℝ) + 1)) / 3)
    (hseqTail : ∀ n, ∀ᶠ i in L, ∀ x,
      |unitIntervalTruncatedPotential (εOf n) (μs i) x -
        unitIntervalLogPotential (μs i) x| <
        (1 / ((n : ℝ) + 1)) / 3)
    (htruncConv : ∀ n, ∀ᶠ i in L, ∀ x,
      |unitIntervalTruncatedPotential (εOf n) (μs i) x -
        unitIntervalTruncatedPotential (εOf n) μ x| <
        (1 / ((n : ℝ) + 1)) / 3) :
    volume {x : ℝ | 0 < unitIntervalLogPotential μ x} ≤
      L.liminf
        (fun i => volume {x : ℝ | 0 < unitIntervalLogPotential (μs i) x}) := by
  exact variable_positiveSet_measure_le_liminf_of_three_error_scheme
    (unitIntervalLogPotential μ)
    (fun i => unitIntervalLogPotential (μs i))
    (fun n => unitIntervalTruncatedPotential (εOf n) μ)
    (fun n i => unitIntervalTruncatedPotential (εOf n) (μs i))
    hlimitTail hseqTail htruncConv

def unitIntervalPositiveSetObjective
    (μ : ProbabilityMeasure UnitInterval1038) : ℝ≥0∞ :=
  volume {x : ℝ | 0 < unitIntervalLogPotential μ x}

theorem unitIntervalPositiveSetObjective_le_liminf_from_tail_control
    {ι : Type*} {L : Filter ι}
    (μ : ProbabilityMeasure UnitInterval1038)
    (μs : ι → ProbabilityMeasure UnitInterval1038)
    (εOf : ℕ → ℝ)
    (hlimitTail : ∀ n x,
      |unitIntervalTruncatedPotential (εOf n) μ x -
        unitIntervalLogPotential μ x| <
        (1 / ((n : ℝ) + 1)) / 3)
    (hseqTail : ∀ n, ∀ᶠ i in L, ∀ x,
      |unitIntervalTruncatedPotential (εOf n) (μs i) x -
        unitIntervalLogPotential (μs i) x| <
        (1 / ((n : ℝ) + 1)) / 3)
    (htruncConv : ∀ n, ∀ᶠ i in L, ∀ x,
      |unitIntervalTruncatedPotential (εOf n) (μs i) x -
        unitIntervalTruncatedPotential (εOf n) μ x| <
        (1 / ((n : ℝ) + 1)) / 3) :
    unitIntervalPositiveSetObjective μ ≤
      L.liminf (fun i => unitIntervalPositiveSetObjective (μs i)) := by
  simpa [unitIntervalPositiveSetObjective] using
    unitIntervalLogPotential_objective_lsc_from_tail_control
      μ μs εOf hlimitTail hseqTail htruncConv

theorem unitIntervalPositiveSetObjective_lowerSemicontinuous_of_tail_control
    (hTail : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∃ εOf : ℕ → ℝ,
        (∀ n x,
          |unitIntervalTruncatedPotential (εOf n) μ x -
            unitIntervalLogPotential μ x| <
            (1 / ((n : ℝ) + 1)) / 3) ∧
        (∀ n, ∀ᶠ ν in nhds μ, ∀ x,
          |unitIntervalTruncatedPotential (εOf n) ν x -
            unitIntervalLogPotential ν x| <
            (1 / ((n : ℝ) + 1)) / 3) ∧
        (∀ n, ∀ᶠ ν in nhds μ, ∀ x,
          |unitIntervalTruncatedPotential (εOf n) ν x -
            unitIntervalTruncatedPotential (εOf n) μ x| <
            (1 / ((n : ℝ) + 1)) / 3)) :
    LowerSemicontinuous unitIntervalPositiveSetObjective := by
  rw [lowerSemicontinuous_iff]
  intro μ
  rw [lowerSemicontinuousAt_iff_le_liminf]
  rcases hTail μ with ⟨εOf, hlimitTail, hseqTail, htruncConv⟩
  exact unitIntervalPositiveSetObjective_le_liminf_from_tail_control
    μ (fun ν : ProbabilityMeasure UnitInterval1038 => ν) εOf
    hlimitTail hseqTail htruncConv

theorem unitIntervalPositiveSetObjective_lowerSemicontinuous_of_threshold_approx
    (happrox : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ A : Set ℝ,
          volume {x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} ≤
            volume A + (ε : ℝ≥0∞) ∧
          ∀ᶠ ν in nhds μ,
            A ⊆ {x : ℝ | 0 < unitIntervalLogPotential ν x}) :
    LowerSemicontinuous unitIntervalPositiveSetObjective := by
  rw [lowerSemicontinuous_iff]
  intro μ
  rw [lowerSemicontinuousAt_iff_le_liminf]
  simpa [unitIntervalPositiveSetObjective] using
    positiveSet_measure_le_liminf_of_eventually_subset_up_to_error
      (unitIntervalLogPotential μ)
      (fun ν : ProbabilityMeasure UnitInterval1038 =>
        unitIntervalLogPotential ν)
      (happrox μ)

theorem unitIntervalPositiveSetObjective_lowerSemicontinuous_of_threshold_approx_with_diagonal_exception
    (happrox : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ A : Set ℝ,
          volume {x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} ≤
            volume A + (ε : ℝ≥0∞) ∧
          ∀ᶠ ν in nhds μ,
            A ⊆ {x : ℝ | 0 < unitIntervalLogPotential ν x} ∪
              diagonalAtomSet ν) :
    LowerSemicontinuous unitIntervalPositiveSetObjective := by
  rw [lowerSemicontinuous_iff]
  intro μ
  rw [lowerSemicontinuousAt_iff_le_liminf]
  simpa [unitIntervalPositiveSetObjective] using
    positiveSet_measure_le_liminf_of_eventually_subset_union_null_up_to_error
      (unitIntervalLogPotential μ)
      (fun ν : ProbabilityMeasure UnitInterval1038 =>
        unitIntervalLogPotential ν)
      (fun ν : ProbabilityMeasure UnitInterval1038 => diagonalAtomSet ν)
      (Filter.Eventually.of_forall
        (fun ν : ProbabilityMeasure UnitInterval1038 =>
          diagonalAtomSet_volume_zero ν))
      (happrox μ)

theorem unitIntervalPositiveSetObjective_exists_minimizer_of_threshold_approx_with_diagonal_exception
    (happrox : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ A : Set ℝ,
          volume {x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} ≤
            volume A + (ε : ℝ≥0∞) ∧
          ∀ᶠ ν in nhds μ,
            A ⊆ {x : ℝ | 0 < unitIntervalLogPotential ν x} ∪
              diagonalAtomSet ν) :
    ∃ μ : ProbabilityMeasure UnitInterval1038,
      ∀ ν : ProbabilityMeasure UnitInterval1038,
        unitIntervalPositiveSetObjective μ ≤
          unitIntervalPositiveSetObjective ν := by
  exact admissible_probability_lsc_exists_minimizer_ennreal
    unitIntervalPositiveSetObjective
    (unitIntervalPositiveSetObjective_lowerSemicontinuous_of_threshold_approx_with_diagonal_exception
      happrox)

/--
Existence of a relaxed minimizer for the actual length objective, once the
threshold-approximation/lower-semicontinuity estimate has been established.
This closes the compactness part for the real objective rather than for an
abstract real-valued surrogate.
-/
theorem unitIntervalPositiveSetObjective_exists_minimizer_of_threshold_approx
    (happrox : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ A : Set ℝ,
          volume {x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} ≤
            volume A + (ε : ℝ≥0∞) ∧
          ∀ᶠ ν in nhds μ,
            A ⊆ {x : ℝ | 0 < unitIntervalLogPotential ν x}) :
    ∃ μ : ProbabilityMeasure UnitInterval1038,
      ∀ ν : ProbabilityMeasure UnitInterval1038,
        unitIntervalPositiveSetObjective μ ≤
          unitIntervalPositiveSetObjective ν := by
  exact admissible_probability_lsc_exists_minimizer_ennreal
    unitIntervalPositiveSetObjective
    (unitIntervalPositiveSetObjective_lowerSemicontinuous_of_threshold_approx
      happrox)

theorem unitIntervalPositiveSetObjective_lowerSemicontinuous_of_tailCore
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ truncε δ : ℝ,
          0 < δ ∧
          volume {x : ℝ | ENNReal.ofReal δ ≤ singularTailMass truncε μ x} ≤
            (ε : ℝ≥0∞) ∧
          (∀ x ∈ unitIntervalThresholdTailCore μ n truncε δ,
            ENNReal.ofReal
              |unitIntervalTruncatedPotential truncε μ x -
                unitIntervalLogPotential μ x| ≤ singularTailMass truncε μ x) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ unitIntervalThresholdTailCore μ n truncε δ,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalLogPotential ν x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ unitIntervalThresholdTailCore μ n truncε δ,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalTruncatedPotential truncε μ x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          δ ≤ (1 / ((n : ℝ) + 1)) / 3) :
    LowerSemicontinuous unitIntervalPositiveSetObjective := by
  exact unitIntervalPositiveSetObjective_lowerSemicontinuous_of_threshold_approx
    (unitInterval_threshold_approx_of_tailCore hcore)

theorem unitIntervalPositiveSetObjective_exists_minimizer_of_tailCore
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ truncε δ : ℝ,
          0 < δ ∧
          volume {x : ℝ | ENNReal.ofReal δ ≤ singularTailMass truncε μ x} ≤
            (ε : ℝ≥0∞) ∧
          (∀ x ∈ unitIntervalThresholdTailCore μ n truncε δ,
            ENNReal.ofReal
              |unitIntervalTruncatedPotential truncε μ x -
                unitIntervalLogPotential μ x| ≤ singularTailMass truncε μ x) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ unitIntervalThresholdTailCore μ n truncε δ,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalLogPotential ν x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ unitIntervalThresholdTailCore μ n truncε δ,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalTruncatedPotential truncε μ x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          δ ≤ (1 / ((n : ℝ) + 1)) / 3) :
    ∃ μ : ProbabilityMeasure UnitInterval1038,
      ∀ ν : ProbabilityMeasure UnitInterval1038,
        unitIntervalPositiveSetObjective μ ≤
          unitIntervalPositiveSetObjective ν := by
  exact admissible_probability_lsc_exists_minimizer_ennreal
    unitIntervalPositiveSetObjective
    (unitIntervalPositiveSetObjective_lowerSemicontinuous_of_tailCore hcore)

theorem unitIntervalPositiveSetObjective_lowerSemicontinuous_of_tailCore_offDiagonal
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ truncε δ : ℝ, ∃ N : Set ℝ,
          0 < δ ∧
          volume N = 0 ∧
          volume {x : ℝ | ENNReal.ofReal δ ≤ singularTailMass truncε μ x} ≤
            (ε : ℝ≥0∞) ∧
          (∀ x ∈ unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ N,
            ENNReal.ofReal
              |unitIntervalTruncatedPotential truncε μ x -
                unitIntervalLogPotential μ x| ≤ singularTailMass truncε μ x) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈
              unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ N,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalLogPotential ν x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈
              unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ N,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalTruncatedPotential truncε μ x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          δ ≤ (1 / ((n : ℝ) + 1)) / 3) :
    LowerSemicontinuous unitIntervalPositiveSetObjective := by
  exact unitIntervalPositiveSetObjective_lowerSemicontinuous_of_threshold_approx
    (unitInterval_threshold_approx_of_tailCore_offDiagonal hcore)

theorem unitIntervalPositiveSetObjective_exists_minimizer_of_tailCore_offDiagonal
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ truncε δ : ℝ, ∃ N : Set ℝ,
          0 < δ ∧
          volume N = 0 ∧
          volume {x : ℝ | ENNReal.ofReal δ ≤ singularTailMass truncε μ x} ≤
            (ε : ℝ≥0∞) ∧
          (∀ x ∈ unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ N,
            ENNReal.ofReal
              |unitIntervalTruncatedPotential truncε μ x -
                unitIntervalLogPotential μ x| ≤ singularTailMass truncε μ x) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈
              unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ N,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalLogPotential ν x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈
              unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ N,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalTruncatedPotential truncε μ x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          δ ≤ (1 / ((n : ℝ) + 1)) / 3) :
    ∃ μ : ProbabilityMeasure UnitInterval1038,
      ∀ ν : ProbabilityMeasure UnitInterval1038,
        unitIntervalPositiveSetObjective μ ≤
          unitIntervalPositiveSetObjective ν := by
  exact admissible_probability_lsc_exists_minimizer_ennreal
    unitIntervalPositiveSetObjective
    (unitIntervalPositiveSetObjective_lowerSemicontinuous_of_tailCore_offDiagonal hcore)

theorem unitIntervalPositiveSetObjective_lowerSemicontinuous_of_compact_core
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ truncε : ℝ, ∃ K : Set ℝ,
          K ⊆ {x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} ∧
          IsCompact K ∧
          volume ({x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} \ K) ≤ (ε : ℝ≥0∞) ∧
          (∀ x ∈ K,
            |unitIntervalTruncatedPotential truncε μ x -
              unitIntervalLogPotential μ x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ K,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalLogPotential ν x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ K,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalTruncatedPotential truncε μ x| <
              (1 / ((n : ℝ) + 1)) / 3)) :
    LowerSemicontinuous unitIntervalPositiveSetObjective := by
  exact unitIntervalPositiveSetObjective_lowerSemicontinuous_of_threshold_approx
    (unitInterval_threshold_approx_of_compact_core hcore)

theorem unitIntervalPositiveSetObjective_exists_minimizer_of_compact_core
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ truncε : ℝ, ∃ K : Set ℝ,
          K ⊆ {x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} ∧
          IsCompact K ∧
          volume ({x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} \ K) ≤ (ε : ℝ≥0∞) ∧
          (∀ x ∈ K,
            |unitIntervalTruncatedPotential truncε μ x -
              unitIntervalLogPotential μ x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ K,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalLogPotential ν x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ K,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalTruncatedPotential truncε μ x| <
              (1 / ((n : ℝ) + 1)) / 3)) :
    ∃ μ : ProbabilityMeasure UnitInterval1038,
      ∀ ν : ProbabilityMeasure UnitInterval1038,
        unitIntervalPositiveSetObjective μ ≤
          unitIntervalPositiveSetObjective ν := by
  exact admissible_probability_lsc_exists_minimizer_ennreal
    unitIntervalPositiveSetObjective
    (unitIntervalPositiveSetObjective_lowerSemicontinuous_of_compact_core hcore)

theorem unitIntervalPositiveSetObjective_exists_minimizer_of_tailCore_real_threshold
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ truncε δ : ℝ,
          0 < δ ∧
          ENNReal.ofReal (2 * truncε) / (ENNReal.ofReal δ / 2) ≤
            (ε : ℝ≥0∞) ∧
          (∀ x ∈ unitIntervalThresholdTailCore μ n truncε δ,
            ENNReal.ofReal
              |unitIntervalTruncatedPotential truncε μ x -
                unitIntervalLogPotential μ x| ≤ singularTailMass truncε μ x) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ unitIntervalThresholdTailCore μ n truncε δ,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalLogPotential ν x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ unitIntervalThresholdTailCore μ n truncε δ,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalTruncatedPotential truncε μ x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          δ ≤ (1 / ((n : ℝ) + 1)) / 3) :
    ∃ μ : ProbabilityMeasure UnitInterval1038,
      ∀ ν : ProbabilityMeasure UnitInterval1038,
        unitIntervalPositiveSetObjective μ ≤
          unitIntervalPositiveSetObjective ν := by
  refine unitIntervalPositiveSetObjective_exists_minimizer_of_tailCore ?_
  intro μ n ε hε
  rcases hcore μ n ε hε with
    ⟨truncε, δ, hδ, hscale, herror, hseq, htrunc, hδle⟩
  refine ⟨truncε, δ, hδ, ?_, herror, hseq, htrunc, hδle⟩
  exact singularTail_closed_badSet_volume_le_of_two_mul_real_threshold
    truncε μ hδ hscale

theorem unitIntervalPositiveSetObjective_exists_minimizer_of_tailCore_scale_choice
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ η : NNReal, 0 < η →
        ∀ truncε : ℝ,
          0 < truncε →
          ENNReal.ofReal (2 * truncε) /
              (ENNReal.ofReal ((1 / ((n : ℝ) + 1)) / 3) / 2) ≤
            (η : ℝ≥0∞) →
          (∀ x ∈ unitIntervalThresholdTailCore μ n truncε
              ((1 / ((n : ℝ) + 1)) / 3),
            ENNReal.ofReal
              |unitIntervalTruncatedPotential truncε μ x -
                unitIntervalLogPotential μ x| ≤ singularTailMass truncε μ x) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ unitIntervalThresholdTailCore μ n truncε
              ((1 / ((n : ℝ) + 1)) / 3),
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalLogPotential ν x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ unitIntervalThresholdTailCore μ n truncε
              ((1 / ((n : ℝ) + 1)) / 3),
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalTruncatedPotential truncε μ x| <
              (1 / ((n : ℝ) + 1)) / 3)) :
    ∃ μ : ProbabilityMeasure UnitInterval1038,
      ∀ ν : ProbabilityMeasure UnitInterval1038,
        unitIntervalPositiveSetObjective μ ≤
          unitIntervalPositiveSetObjective ν := by
  refine unitIntervalPositiveSetObjective_exists_minimizer_of_tailCore_real_threshold ?_
  intro μ n η hη
  let δ : ℝ := (1 / ((n : ℝ) + 1)) / 3
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  rcases exists_tailScale_for_target (δ := δ) (η := η) hδ hη with
    ⟨truncε, htruncε_pos, hscale⟩
  specialize hcore μ n η hη truncε htruncε_pos (by simpa [δ] using hscale)
  rcases hcore with ⟨herror, hseq, htrunc⟩
  refine ⟨truncε, δ, hδ, hscale, herror, hseq, htrunc, ?_⟩
  rfl

lemma continuous_truncatedLogKernel {ε x : ℝ} (hε : 0 < ε) :
    Continuous (fun t : ℝ => truncatedLogKernel ε x t) := by
  unfold truncatedLogKernel
  apply Continuous.log
  · exact continuous_const.div₀
      (continuous_const.max ((continuous_const.sub continuous_id).abs))
      (fun t => by
        have hmax : 0 < max ε |x - t| :=
          lt_of_lt_of_le hε (le_max_left ε |x - t|)
        exact ne_of_gt hmax)
  · intro t
    have hmax : 0 < max ε |x - t| :=
      lt_of_lt_of_le hε (le_max_left ε |x - t|)
    exact div_ne_zero one_ne_zero (ne_of_gt hmax)

lemma continuous_truncatedLogKernel_uncurry {ε : ℝ} (hε : 0 < ε) :
    Continuous
      (fun p : ℝ × UnitInterval1038 =>
        truncatedLogKernel ε p.1 (p.2 : ℝ)) := by
  unfold truncatedLogKernel
  apply Continuous.log
  · exact continuous_const.div₀
      (continuous_const.max
        ((continuous_fst.sub (continuous_subtype_val.comp continuous_snd)).abs))
      (fun p => by
        have hmax : 0 < max ε |p.1 - (p.2 : ℝ)| :=
          lt_of_lt_of_le hε (le_max_left ε |p.1 - (p.2 : ℝ)|)
        exact ne_of_gt hmax)
  · intro p
    have hmax : 0 < max ε |p.1 - (p.2 : ℝ)| :=
      lt_of_lt_of_le hε (le_max_left ε |p.1 - (p.2 : ℝ)|)
    exact div_ne_zero one_ne_zero (ne_of_gt hmax)

noncomputable def truncatedLogKernelBCF (ε x : ℝ) (hε : 0 < ε) :
    BoundedContinuousFunction UnitInterval1038 ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun t : UnitInterval1038 => truncatedLogKernel ε x t,
      (continuous_truncatedLogKernel (x := x) hε).comp
        continuous_subtype_val⟩

lemma truncatedLogKernel_integrable
    (μ : ProbabilityMeasure UnitInterval1038) {ε x : ℝ}
    (hε : 0 < ε) :
    Integrable
      (fun t : UnitInterval1038 => truncatedLogKernel ε x (t : ℝ))
      (μ : Measure UnitInterval1038) := by
  exact ((continuous_truncatedLogKernel (x := x) hε).comp
      continuous_subtype_val).integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_univ
      (fun _t _ht => trivial))

lemma unitIntervalTruncatedPotential_oscillation_le
    (μ : ProbabilityMeasure UnitInterval1038) {ε x y c : ℝ}
    (hε : 0 < ε)
    (hosc : ∀ t : UnitInterval1038,
      |truncatedLogKernel ε y (t : ℝ) -
        truncatedLogKernel ε x (t : ℝ)| ≤ c) :
    |unitIntervalTruncatedPotential ε μ y -
      unitIntervalTruncatedPotential ε μ x| ≤ c := by
  let f : UnitInterval1038 → ℝ :=
    fun t => truncatedLogKernel ε y (t : ℝ)
  let g : UnitInterval1038 → ℝ :=
    fun t => truncatedLogKernel ε x (t : ℝ)
  have hf : Integrable f (μ : Measure UnitInterval1038) :=
    truncatedLogKernel_integrable μ (x := y) hε
  have hg : Integrable g (μ : Measure UnitInterval1038) :=
    truncatedLogKernel_integrable μ (x := x) hε
  have hdiff_int : Integrable (fun t => f t - g t)
      (μ : Measure UnitInterval1038) := hf.sub hg
  have hsub :
      (∫ t : UnitInterval1038, f t - g t ∂(μ : Measure UnitInterval1038)) =
        (∫ t : UnitInterval1038, f t ∂(μ : Measure UnitInterval1038)) -
          ∫ t : UnitInterval1038, g t ∂(μ : Measure UnitInterval1038) := by
    exact integral_sub hf hg
  have hreal_le :
      |(∫ t : UnitInterval1038, f t ∂(μ : Measure UnitInterval1038)) -
          ∫ t : UnitInterval1038, g t ∂(μ : Measure UnitInterval1038)| ≤
        ∫ t : UnitInterval1038, |f t - g t| ∂(μ : Measure UnitInterval1038) := by
    calc
      |(∫ t : UnitInterval1038, f t ∂(μ : Measure UnitInterval1038)) -
          ∫ t : UnitInterval1038, g t ∂(μ : Measure UnitInterval1038)|
          = ‖∫ t : UnitInterval1038, f t - g t
              ∂(μ : Measure UnitInterval1038)‖ := by
              rw [hsub]
              simp [Real.norm_eq_abs]
      _ ≤ ∫ t : UnitInterval1038, ‖f t - g t‖
              ∂(μ : Measure UnitInterval1038) :=
              norm_integral_le_integral_norm
                (fun t : UnitInterval1038 => f t - g t)
      _ = ∫ t : UnitInterval1038, |f t - g t|
              ∂(μ : Measure UnitInterval1038) := by
              simp [Real.norm_eq_abs]
  have habs_int : Integrable (fun t : UnitInterval1038 => |f t - g t|)
      (μ : Measure UnitInterval1038) := hdiff_int.norm
  have hconst_int : Integrable (fun _ : UnitInterval1038 => c)
      (μ : Measure UnitInterval1038) := integrable_const c
  have hmono :
      (∫ t : UnitInterval1038, |f t - g t|
          ∂(μ : Measure UnitInterval1038)) ≤
        ∫ _t : UnitInterval1038, c ∂(μ : Measure UnitInterval1038) := by
    refine integral_mono habs_int hconst_int ?_
    intro t
    simpa [f, g] using hosc t
  have hconst :
      (∫ _t : UnitInterval1038, c ∂(μ : Measure UnitInterval1038)) = c := by
    simp
  unfold unitIntervalTruncatedPotential
  exact le_trans hreal_le (by simpa [hconst] using hmono)

lemma truncatedLogKernel_integral_tendsto
    {ι : Type*} {L : Filter ι}
    {μ : ProbabilityMeasure UnitInterval1038}
    {μs : ι → ProbabilityMeasure UnitInterval1038}
    (hμs : Filter.Tendsto μs L (nhds μ)) {ε x : ℝ}
    (hε : 0 < ε) :
    Filter.Tendsto
      (fun i => ∫ t : UnitInterval1038,
        truncatedLogKernel ε x t ∂(μs i : Measure UnitInterval1038)) L
      (nhds (∫ t : UnitInterval1038,
        truncatedLogKernel ε x t ∂(μ : Measure UnitInterval1038))) := by
  simpa [truncatedLogKernelBCF] using
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμs)
      (truncatedLogKernelBCF ε x hε)

/-- Weak continuity of the truncated unit-interval potential at fixed `ε,x`. -/
theorem unitIntervalTruncatedPotential_tendsto
    {ι : Type*} {L : Filter ι}
    {μ : ProbabilityMeasure UnitInterval1038}
    {μs : ι → ProbabilityMeasure UnitInterval1038}
    (hμs : Filter.Tendsto μs L (nhds μ)) {ε x : ℝ}
    (hε : 0 < ε) :
    Filter.Tendsto
      (fun i => unitIntervalTruncatedPotential ε (μs i) x) L
      (nhds (unitIntervalTruncatedPotential ε μ x)) := by
  simpa [unitIntervalTruncatedPotential] using
    truncatedLogKernel_integral_tendsto hμs (x := x) hε

/--
Neighborhood form of weak continuity for the truncated potential.  This is the
local building block used by the threshold-approximation argument.
-/
theorem unitIntervalTruncatedPotential_eventually_close
    (μ : ProbabilityMeasure UnitInterval1038) {ε x δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ ν in nhds μ,
      |unitIntervalTruncatedPotential ε ν x -
        unitIntervalTruncatedPotential ε μ x| < δ := by
  have htend :
      Filter.Tendsto
        (fun ν : ProbabilityMeasure UnitInterval1038 =>
          unitIntervalTruncatedPotential ε ν x) (nhds μ)
        (nhds (unitIntervalTruncatedPotential ε μ x)) :=
    unitIntervalTruncatedPotential_tendsto
      (μ := μ) (μs := fun ν : ProbabilityMeasure UnitInterval1038 => ν)
      Filter.tendsto_id (x := x) hε
  have hclose :=
    (Metric.tendsto_nhds.mp htend) δ hδ
  simpa [Real.dist_eq, abs_sub_comm] using hclose

lemma truncatedLogKernel_tendstoUniformly_in_x {ε x : ℝ}
    (hε : 0 < ε) :
    TendstoUniformly
      (fun y : ℝ => fun t : UnitInterval1038 =>
        truncatedLogKernel ε y (t : ℝ))
      (fun t : UnitInterval1038 => truncatedLogKernel ε x (t : ℝ))
      (nhds x) := by
  simpa using
    (Continuous.tendstoUniformly
      (fun y : ℝ => fun t : UnitInterval1038 =>
        truncatedLogKernel ε y (t : ℝ))
      (continuous_truncatedLogKernel_uncurry hε) x)

lemma truncatedLogKernel_local_uniform_oscillation {ε x η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) :
    ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ t : UnitInterval1038,
        |truncatedLogKernel ε y (t : ℝ) -
          truncatedLogKernel ε x (t : ℝ)| < η := by
  have htend := truncatedLogKernel_tendstoUniformly_in_x (x := x) hε
  have hevent :
      ∀ᶠ y in nhds x, ∀ t : UnitInterval1038,
        dist (truncatedLogKernel ε x (t : ℝ))
          (truncatedLogKernel ε y (t : ℝ)) < η :=
    (Metric.tendstoUniformly_iff.mp htend) η hη
  rcases mem_nhds_iff.mp hevent with ⟨U, hUsub, hUopen, hxU⟩
  refine ⟨U, hUopen, hxU, ?_⟩
  intro y hyU t
  have hdist := hUsub hyU t
  simpa [Real.dist_eq, abs_sub_comm] using hdist

/--
Local form of uniform weak continuity for the truncated potential.  The only
input is a neighborhood on which the truncated kernels oscillate by at most
`δ / 3`; the pointwise weak-continuity estimate at the center supplies the
middle third.
-/
theorem unitIntervalTruncatedPotential_local_eventually_close_of_kernel_osc
    (μ : ProbabilityMeasure UnitInterval1038) {ε x δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ)
    {U : Set ℝ} (hUopen : IsOpen U) (hxU : x ∈ U)
    (hosc : ∀ y ∈ U, ∀ ν : ProbabilityMeasure UnitInterval1038,
      |unitIntervalTruncatedPotential ε ν y -
        unitIntervalTruncatedPotential ε ν x| ≤ δ / 3) :
    ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧
      ∀ᶠ ν in nhds μ, ∀ y ∈ U,
        |unitIntervalTruncatedPotential ε ν y -
          unitIntervalTruncatedPotential ε μ y| < δ := by
  refine ⟨U, hUopen, hxU, ?_⟩
  have hthird : 0 < δ / 3 := by positivity
  have hpoint :
      ∀ᶠ ν in nhds μ,
        |unitIntervalTruncatedPotential ε ν x -
          unitIntervalTruncatedPotential ε μ x| < δ / 3 :=
    unitIntervalTruncatedPotential_eventually_close μ hε hthird
  filter_upwards [hpoint] with ν hν y hyU
  have hνosc := hosc y hyU ν
  have hμosc := hosc y hyU μ
  have hμosc' :
      |unitIntervalTruncatedPotential ε μ x -
        unitIntervalTruncatedPotential ε μ y| ≤ δ / 3 := by
    simpa [abs_sub_comm] using hμosc
  have htri :
      |unitIntervalTruncatedPotential ε ν y -
        unitIntervalTruncatedPotential ε μ y| ≤
        |unitIntervalTruncatedPotential ε ν y -
          unitIntervalTruncatedPotential ε ν x| +
        |unitIntervalTruncatedPotential ε ν x -
          unitIntervalTruncatedPotential ε μ x| +
        |unitIntervalTruncatedPotential ε μ x -
          unitIntervalTruncatedPotential ε μ y| := by
    have hsplit :
        unitIntervalTruncatedPotential ε ν y -
          unitIntervalTruncatedPotential ε μ y =
        (unitIntervalTruncatedPotential ε ν y -
          unitIntervalTruncatedPotential ε ν x) +
        (unitIntervalTruncatedPotential ε ν x -
          unitIntervalTruncatedPotential ε μ x) +
        (unitIntervalTruncatedPotential ε μ x -
          unitIntervalTruncatedPotential ε μ y) := by
      ring
    rw [hsplit]
    have h12 :
        |(unitIntervalTruncatedPotential ε ν y -
          unitIntervalTruncatedPotential ε ν x) +
        (unitIntervalTruncatedPotential ε ν x -
          unitIntervalTruncatedPotential ε μ x)| ≤
        |unitIntervalTruncatedPotential ε ν y -
          unitIntervalTruncatedPotential ε ν x| +
        |unitIntervalTruncatedPotential ε ν x -
          unitIntervalTruncatedPotential ε μ x| :=
      abs_add_le _ _
    have h123 :
        |(unitIntervalTruncatedPotential ε ν y -
          unitIntervalTruncatedPotential ε ν x) +
        (unitIntervalTruncatedPotential ε ν x -
          unitIntervalTruncatedPotential ε μ x) +
        (unitIntervalTruncatedPotential ε μ x -
          unitIntervalTruncatedPotential ε μ y)| ≤
        |(unitIntervalTruncatedPotential ε ν y -
          unitIntervalTruncatedPotential ε ν x) +
        (unitIntervalTruncatedPotential ε ν x -
          unitIntervalTruncatedPotential ε μ x)| +
        |unitIntervalTruncatedPotential ε μ x -
          unitIntervalTruncatedPotential ε μ y| :=
      abs_add_le _ _
    linarith
  nlinarith

theorem unitIntervalTruncatedPotential_local_eventually_close
    (μ : ProbabilityMeasure UnitInterval1038) {ε x δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧
      ∀ᶠ ν in nhds μ, ∀ y ∈ U,
        |unitIntervalTruncatedPotential ε ν y -
          unitIntervalTruncatedPotential ε μ y| < δ := by
  have hthird : 0 < δ / 3 := by positivity
  rcases truncatedLogKernel_local_uniform_oscillation
      (ε := ε) (x := x) (η := δ / 3) hε hthird with
    ⟨U, hUopen, hxU, hkernel⟩
  refine unitIntervalTruncatedPotential_local_eventually_close_of_kernel_osc
    μ hε hδ hUopen hxU ?_
  intro y hyU ν
  exact unitIntervalTruncatedPotential_oscillation_le ν hε
    (fun t => le_of_lt (hkernel y hyU t))

theorem unitIntervalTruncatedPotential_continuous
    (μ : ProbabilityMeasure UnitInterval1038) {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun x : ℝ => unitIntervalTruncatedPotential ε μ x) := by
  rw [Metric.continuous_iff]
  intro x δ hδ
  have hδhalf : 0 < δ / 2 := by positivity
  rcases truncatedLogKernel_local_uniform_oscillation
      (ε := ε) (x := x) (η := δ / 2) hε hδhalf with
    ⟨U, hUopen, hxU, hosc⟩
  rcases Metric.isOpen_iff.mp hUopen x hxU with ⟨r, hr_pos, hr_sub⟩
  refine ⟨r, hr_pos, ?_⟩
  intro y hy
  have hyU : y ∈ U := hr_sub hy
  have hle :
      |unitIntervalTruncatedPotential ε μ y -
        unitIntervalTruncatedPotential ε μ x| ≤ δ / 2 :=
    unitIntervalTruncatedPotential_oscillation_le μ hε
      (fun t => le_of_lt (hosc y hyU t))
  have hlt : |unitIntervalTruncatedPotential ε μ y -
        unitIntervalTruncatedPotential ε μ x| < δ := by
    linarith
  simpa [Real.dist_eq, abs_sub_comm] using hlt

lemma eventually_forall_mem_finset
    {ι β : Type*} {L : Filter ι} (s : Finset β) (P : ι → β → Prop)
    (h : ∀ b ∈ s, ∀ᶠ i in L, P i b) :
    ∀ᶠ i in L, ∀ b ∈ s, P i b := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert b s hbs ih =>
      have hb : ∀ᶠ i in L, P i b := h b (by simp)
      have hs : ∀ᶠ i in L, ∀ c ∈ s, P i c := by
        apply ih
        intro c hc
        exact h c (by simp [hc])
      filter_upwards [hb, hs] with i hbi hsi c hc
      simp at hc
      rcases hc with hcb | hcs
      · simpa [hcb] using hbi
      · exact hsi c hcs

/--
Compact finite-subcover upgrade for local eventually estimates.  This is the
topological core of the uniform-on-compact step: once every point has an open
neighborhood on which an estimate eventually holds, compactness upgrades it to
an estimate on all of `K`.
-/
theorem eventually_forall_mem_compact_of_eventually_nhds_cover
    {ι : Type*} {L : Filter ι} {K : Set ℝ} (hK : IsCompact K)
    {P : ι → ℝ → Prop}
    (hlocal : ∀ x ∈ K, ∃ U : Set ℝ,
      IsOpen U ∧ x ∈ U ∧
        ∀ᶠ i in L, ∀ y ∈ K, y ∈ U → P i y) :
    ∀ᶠ i in L, ∀ y ∈ K, P i y := by
  classical
  choose U hUopen hxU hUevent using hlocal
  let V : K → Set ℝ := fun x => U x x.2
  have hVopen : ∀ x : K, IsOpen (V x) := fun x => hUopen x x.2
  have hcover : K ⊆ ⋃ x : K, V x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxU x hx⟩
  rcases hK.elim_finite_subcover V hVopen hcover with ⟨s, hscover⟩
  have hevent :
      ∀ᶠ i in L, ∀ x ∈ s, ∀ y ∈ K, y ∈ V x → P i y :=
    eventually_forall_mem_finset s
      (fun i x => ∀ y ∈ K, y ∈ V x → P i y)
      (fun x _hx => hUevent x x.2)
  filter_upwards [hevent] with i hi y hy
  have hycover : y ∈ ⋃ x ∈ s, V x := hscover hy
  rcases mem_iUnion₂.mp hycover with ⟨x, hxs, hyUx⟩
  exact hi x hxs y hy hyUx

theorem unitIntervalTruncatedPotential_eventually_close_on_finset
    (μ : ProbabilityMeasure UnitInterval1038) {ε δ : ℝ}
    (s : Finset ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ ν in nhds μ, ∀ x ∈ s,
      |unitIntervalTruncatedPotential ε ν x -
        unitIntervalTruncatedPotential ε μ x| < δ := by
  exact eventually_forall_mem_finset s
    (fun ν x =>
      |unitIntervalTruncatedPotential ε ν x -
        unitIntervalTruncatedPotential ε μ x| < δ)
    (fun x _hx =>
      unitIntervalTruncatedPotential_eventually_close μ hε hδ)

/--
Compact-core version of weak continuity for the truncated potential, reduced to
local estimates.  This is the exact compactness wrapper needed by the
threshold-core argument.
-/
theorem unitIntervalTruncatedPotential_eventually_close_on_compact_of_local
    (μ : ProbabilityMeasure UnitInterval1038) {truncε δ : ℝ}
    {K : Set ℝ} (hK : IsCompact K)
    (hlocal : ∀ x ∈ K, ∃ U : Set ℝ,
      IsOpen U ∧ x ∈ U ∧
        ∀ᶠ ν in nhds μ, ∀ y ∈ K, y ∈ U →
          |unitIntervalTruncatedPotential truncε ν y -
            unitIntervalTruncatedPotential truncε μ y| < δ) :
    ∀ᶠ ν in nhds μ, ∀ y ∈ K,
      |unitIntervalTruncatedPotential truncε ν y -
        unitIntervalTruncatedPotential truncε μ y| < δ := by
  exact eventually_forall_mem_compact_of_eventually_nhds_cover hK hlocal

theorem unitIntervalTruncatedPotential_eventually_close_on_compact
    (μ : ProbabilityMeasure UnitInterval1038) {truncε δ : ℝ}
    (htruncε : 0 < truncε) (hδ : 0 < δ)
    {K : Set ℝ} (hK : IsCompact K) :
    ∀ᶠ ν in nhds μ, ∀ y ∈ K,
      |unitIntervalTruncatedPotential truncε ν y -
        unitIntervalTruncatedPotential truncε μ y| < δ := by
  refine unitIntervalTruncatedPotential_eventually_close_on_compact_of_local
    μ hK ?_
  intro x hxK
  rcases unitIntervalTruncatedPotential_local_eventually_close
      (μ := μ) (ε := truncε) (x := x) (δ := δ) htruncε hδ with
    ⟨U, hUopen, hxU, hevent⟩
  refine ⟨U, hUopen, hxU, ?_⟩
  filter_upwards [hevent] with ν hν y _hyK hyU
  exact hν y hyU

/-- Canonical positive truncation scale for the truncated-sup objective. -/
def unitIntervalPositiveTruncationScale (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

theorem unitIntervalPositiveTruncationScale_pos (n : ℕ) :
    0 < unitIntervalPositiveTruncationScale n := by
  unfold unitIntervalPositiveTruncationScale
  positivity

theorem unitIntervalPositiveTruncationScale_le_one (n : ℕ) :
    unitIntervalPositiveTruncationScale n ≤ 1 := by
  unfold unitIntervalPositiveTruncationScale
  have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    exact_mod_cast Nat.succ_pos n
  have hpos : 0 < (n : ℝ) + 1 := by positivity
  rw [div_le_iff₀ hpos]
  simpa using hden

lemma truncatedLogKernel_eq_logKernel_of_scale_le_one_of_two_le_abs
    {x : ℝ} (hx : (2 : ℝ) ≤ |x|)
    {ε : ℝ} (hε_le_one : ε ≤ 1) (t : UnitInterval1038) :
    truncatedLogKernel ε x (t : ℝ) =
      Real.log (1 / |x - (t : ℝ)|) := by
  unfold truncatedLogKernel
  have hdist : (1 : ℝ) ≤ |x - (t : ℝ)| :=
    one_le_abs_sub_of_two_le_abs_of_mem_unitInterval hx t.2
  have hε_le_dist : ε ≤ |x - (t : ℝ)| := le_trans hε_le_one hdist
  rw [max_eq_right hε_le_dist]

lemma unitIntervalTruncatedKernel_nonpos_of_two_le_abs
    {x : ℝ} (hx : (2 : ℝ) ≤ |x|) (n : ℕ) (t : UnitInterval1038) :
    truncatedLogKernel (unitIntervalPositiveTruncationScale n) x (t : ℝ) ≤ 0 := by
  rw [truncatedLogKernel_eq_logKernel_of_scale_le_one_of_two_le_abs
    hx (unitIntervalPositiveTruncationScale_le_one n) t]
  exact unitInterval_logKernel_nonpos_of_two_le_abs hx t

theorem unitIntervalTruncatedPotential_nonpos_of_two_le_abs
    (μ : ProbabilityMeasure UnitInterval1038) {x : ℝ}
    (hx : (2 : ℝ) ≤ |x|) (n : ℕ) :
    unitIntervalTruncatedPotential (unitIntervalPositiveTruncationScale n) μ x ≤ 0 := by
  unfold unitIntervalTruncatedPotential
  have hkernel_int :
      Integrable
        (fun t : UnitInterval1038 =>
          truncatedLogKernel (unitIntervalPositiveTruncationScale n) x (t : ℝ))
        (μ : Measure UnitInterval1038) :=
    truncatedLogKernel_integrable μ (unitIntervalPositiveTruncationScale_pos n)
  have hzero_int :
      Integrable (fun _t : UnitInterval1038 => (0 : ℝ))
        (μ : Measure UnitInterval1038) := integrable_const 0
  have hle_ae :
      (fun t : UnitInterval1038 =>
        truncatedLogKernel (unitIntervalPositiveTruncationScale n) x (t : ℝ))
        ≤ᵐ[(μ : Measure UnitInterval1038)]
      (fun _t : UnitInterval1038 => (0 : ℝ)) := by
    filter_upwards with t
    exact unitIntervalTruncatedKernel_nonpos_of_two_le_abs hx n t
  have hle :
      (∫ t : UnitInterval1038,
        truncatedLogKernel (unitIntervalPositiveTruncationScale n) x (t : ℝ)
          ∂(μ : Measure UnitInterval1038)) ≤
        ∫ _t : UnitInterval1038, (0 : ℝ) ∂(μ : Measure UnitInterval1038) :=
    integral_mono_ae hkernel_int hzero_int hle_ae
  simpa using hle

lemma truncatedLogKernel_mono_of_scale_le
    {ε₁ ε₂ x t : ℝ} (hε₂ : 0 < ε₂) (hε₂_le : ε₂ ≤ ε₁) :
    truncatedLogKernel ε₁ x t ≤ truncatedLogKernel ε₂ x t := by
  unfold truncatedLogKernel
  have hmax₂_pos : 0 < max ε₂ |x - t| :=
    lt_of_lt_of_le hε₂ (le_max_left ε₂ |x - t|)
  have hε₁_pos : 0 < ε₁ := lt_of_lt_of_le hε₂ hε₂_le
  have hmax₁_pos : 0 < max ε₁ |x - t| :=
    lt_of_lt_of_le hε₁_pos (le_max_left ε₁ |x - t|)
  have hmax_le : max ε₂ |x - t| ≤ max ε₁ |x - t| :=
    max_le_max_right |x - t| hε₂_le
  have hinv : 1 / max ε₁ |x - t| ≤ 1 / max ε₂ |x - t| :=
    one_div_le_one_div_of_le hmax₂_pos hmax_le
  exact Real.log_le_log (one_div_pos.mpr hmax₁_pos) hinv

theorem unitIntervalPositiveTruncationScale_antitone :
    Antitone unitIntervalPositiveTruncationScale := by
  intro n m hnm
  unfold unitIntervalPositiveTruncationScale
  have hden : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ hnm
  have hpos : 0 < (n : ℝ) + 1 := by positivity
  exact one_div_le_one_div_of_le hpos hden

theorem unitIntervalTruncatedPotential_mono_index
    (μ : ProbabilityMeasure UnitInterval1038) (x : ℝ) :
    Monotone (fun n : ℕ =>
      unitIntervalTruncatedPotential
        (unitIntervalPositiveTruncationScale n) μ x) := by
  intro n m hnm
  unfold unitIntervalTruncatedPotential
  have hfn_int :
      Integrable
        (fun t : UnitInterval1038 =>
          truncatedLogKernel (unitIntervalPositiveTruncationScale n) x (t : ℝ))
        (μ : Measure UnitInterval1038) :=
    truncatedLogKernel_integrable μ (unitIntervalPositiveTruncationScale_pos n)
  have hfm_int :
      Integrable
        (fun t : UnitInterval1038 =>
          truncatedLogKernel (unitIntervalPositiveTruncationScale m) x (t : ℝ))
        (μ : Measure UnitInterval1038) :=
    truncatedLogKernel_integrable μ (unitIntervalPositiveTruncationScale_pos m)
  have hle_ae :
      (fun t : UnitInterval1038 =>
        truncatedLogKernel (unitIntervalPositiveTruncationScale n) x (t : ℝ))
        ≤ᵐ[(μ : Measure UnitInterval1038)]
      (fun t : UnitInterval1038 =>
        truncatedLogKernel (unitIntervalPositiveTruncationScale m) x (t : ℝ)) := by
    filter_upwards with t
    exact truncatedLogKernel_mono_of_scale_le
      (unitIntervalPositiveTruncationScale_pos m)
      (unitIntervalPositiveTruncationScale_antitone hnm)
  exact integral_mono_ae hfn_int hfm_int hle_ae

theorem unitIntervalTruncatedPositiveSet_level_mono
    (μ : ProbabilityMeasure UnitInterval1038) :
    Monotone (fun n : ℕ =>
      {x : ℝ | 0 <
        unitIntervalTruncatedPotential
          (unitIntervalPositiveTruncationScale n) μ x}) := by
  intro n m hnm x hx
  exact lt_of_lt_of_le hx
    (unitIntervalTruncatedPotential_mono_index μ x hnm)

/--
Positive set generated by the countable family of positively truncated
potentials.  This is a truncated-sup surrogate only; no equivalence with the
original logarithmic positive set is asserted here.
-/
def unitIntervalTruncatedPositiveSet
    (μ : ProbabilityMeasure UnitInterval1038) : Set ℝ :=
  {x : ℝ | ∃ n : ℕ,
    0 < unitIntervalTruncatedPotential
      (unitIntervalPositiveTruncationScale n) μ x}

theorem unitIntervalTruncatedPositiveSet_subset_Ioo_neg_two_two
    (μ : ProbabilityMeasure UnitInterval1038) :
    unitIntervalTruncatedPositiveSet μ ⊆ Ioo (-2 : ℝ) 2 := by
  intro x hx
  rcases hx with ⟨n, hnpos⟩
  have hnot : ¬ (2 : ℝ) ≤ |x| := by
    intro h2
    have hnonpos := unitIntervalTruncatedPotential_nonpos_of_two_le_abs μ h2 n
    linarith
  have hlt_abs : |x| < 2 := lt_of_not_ge hnot
  rw [abs_lt] at hlt_abs
  exact ⟨hlt_abs.1, hlt_abs.2⟩

theorem unitIntervalTruncatedPositiveSet_volume_ne_top
    (μ : ProbabilityMeasure UnitInterval1038) :
    volume (unitIntervalTruncatedPositiveSet μ) ≠ ∞ := by
  have hle :
      volume (unitIntervalTruncatedPositiveSet μ) ≤
        volume (Ioo (-2 : ℝ) 2) :=
    measure_mono (μ := volume)
      (unitIntervalTruncatedPositiveSet_subset_Ioo_neg_two_two μ)
  have hfinite_window : volume (Ioo (-2 : ℝ) 2) ≠ ∞ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  exact ne_top_of_le_ne_top hfinite_window hle

theorem unitIntervalTruncatedPositiveSet_volume_eq_iSup_levels
    (μ : ProbabilityMeasure UnitInterval1038) :
    volume (unitIntervalTruncatedPositiveSet μ) =
      ⨆ n : ℕ, volume {x : ℝ | 0 <
        unitIntervalTruncatedPotential
          (unitIntervalPositiveTruncationScale n) μ x} := by
  rw [show unitIntervalTruncatedPositiveSet μ =
      ⋃ n : ℕ,
        {x : ℝ | 0 < unitIntervalTruncatedPotential
          (unitIntervalPositiveTruncationScale n) μ x} by
    ext x
    simp [unitIntervalTruncatedPositiveSet]]
  exact (unitIntervalTruncatedPositiveSet_level_mono μ).measure_iUnion

theorem unitIntervalTruncatedPositiveSet_exists_level_volume_le_add
    (μ : ProbabilityMeasure UnitInterval1038)
    (η : NNReal) (hη : 0 < η) :
    ∃ truncN : ℕ,
      volume (unitIntervalTruncatedPositiveSet μ) ≤
        volume {x : ℝ | 0 <
          unitIntervalTruncatedPotential
            (unitIntervalPositiveTruncationScale truncN) μ x} +
          (η : ℝ≥0∞) := by
  have hfinite :
      (⨆ n : ℕ, volume {x : ℝ | 0 <
        unitIntervalTruncatedPotential
          (unitIntervalPositiveTruncationScale n) μ x}) ≠ ∞ := by
    simpa [← unitIntervalTruncatedPositiveSet_volume_eq_iSup_levels μ]
      using unitIntervalTruncatedPositiveSet_volume_ne_top μ
  rcases exists_iSup_nat_le_add_of_ne_top
      (fun n : ℕ => volume {x : ℝ | 0 <
        unitIntervalTruncatedPotential
          (unitIntervalPositiveTruncationScale n) μ x})
      hη hfinite with
    ⟨truncN, htruncN⟩
  exact ⟨truncN, by
    simpa [unitIntervalTruncatedPositiveSet_volume_eq_iSup_levels μ]
      using htruncN⟩

theorem unitIntervalTruncatedPotential_threshold_subset_Ioo_neg_two_two
    (μ : ProbabilityMeasure UnitInterval1038) (truncN thresholdN : ℕ) :
    {x : ℝ |
      unitIntervalPositiveTruncationScale thresholdN <
        unitIntervalTruncatedPotential
          (unitIntervalPositiveTruncationScale truncN) μ x} ⊆
      Ioo (-2 : ℝ) 2 := by
  intro x hx
  exact unitIntervalTruncatedPositiveSet_subset_Ioo_neg_two_two μ
    ⟨truncN, lt_trans (unitIntervalPositiveTruncationScale_pos thresholdN) hx⟩

theorem unitIntervalTruncatedPotential_threshold_measure_ne_top
    (μ : ProbabilityMeasure UnitInterval1038) (truncN thresholdN : ℕ) :
    volume {x : ℝ |
      unitIntervalPositiveTruncationScale thresholdN <
        unitIntervalTruncatedPotential
          (unitIntervalPositiveTruncationScale truncN) μ x} ≠ ∞ := by
  have hle :
      volume {x : ℝ |
        unitIntervalPositiveTruncationScale thresholdN <
          unitIntervalTruncatedPotential
            (unitIntervalPositiveTruncationScale truncN) μ x} ≤
        volume (Ioo (-2 : ℝ) 2) :=
    measure_mono (μ := volume)
      (unitIntervalTruncatedPotential_threshold_subset_Ioo_neg_two_two
        μ truncN thresholdN)
  have hfinite_window : volume (Ioo (-2 : ℝ) 2) ≠ ∞ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  exact ne_top_of_le_ne_top hfinite_window hle

theorem unitIntervalTruncatedPotential_threshold_exists_compact_core
    (μ : ProbabilityMeasure UnitInterval1038) (truncN thresholdN : ℕ)
    (η : NNReal) (hη : 0 < η) :
    ∃ K : Set ℝ,
      K ⊆ {x : ℝ |
        unitIntervalPositiveTruncationScale thresholdN <
          unitIntervalTruncatedPotential
            (unitIntervalPositiveTruncationScale truncN) μ x} ∧
      IsCompact K ∧
      volume ({x : ℝ |
        unitIntervalPositiveTruncationScale thresholdN <
          unitIntervalTruncatedPotential
            (unitIntervalPositiveTruncationScale truncN) μ x} \ K) ≤
        (η : ℝ≥0∞) := by
  let S : Set ℝ := {x : ℝ |
    unitIntervalPositiveTruncationScale thresholdN <
      unitIntervalTruncatedPotential
        (unitIntervalPositiveTruncationScale truncN) μ x}
  have hSmeas : MeasurableSet S := by
    exact (isOpen_lt continuous_const
      (unitIntervalTruncatedPotential_continuous μ
        (unitIntervalPositiveTruncationScale_pos truncN))).measurableSet
  have hfinite : volume S ≠ ∞ := by
    simpa [S] using
      unitIntervalTruncatedPotential_threshold_measure_ne_top μ truncN thresholdN
  have hη_ne : (η : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (ne_of_gt hη)
  rcases hSmeas.exists_isCompact_diff_lt hfinite hη_ne with
    ⟨K, hKsub, hKcompact, hdiff_lt⟩
  exact ⟨K, hKsub, hKcompact, le_of_lt hdiff_lt⟩

theorem unitIntervalTruncatedPotential_positiveSet_exists_threshold_volume_le_add
    (μ : ProbabilityMeasure UnitInterval1038) (truncN : ℕ)
    (η : NNReal) (hη : 0 < η) :
    ∃ thresholdN : ℕ,
      volume {x : ℝ | 0 <
        unitIntervalTruncatedPotential
          (unitIntervalPositiveTruncationScale truncN) μ x} ≤
        volume {x : ℝ |
          unitIntervalPositiveTruncationScale thresholdN <
            unitIntervalTruncatedPotential
              (unitIntervalPositiveTruncationScale truncN) μ x} +
          (η : ℝ≥0∞) := by
  let U : ℝ → ℝ :=
    fun x => unitIntervalTruncatedPotential
      (unitIntervalPositiveTruncationScale truncN) μ x
  have hfinite :
      (⨆ thresholdN : ℕ,
        volume {x : ℝ | 1 / ((thresholdN : ℝ) + 1) < U x}) ≠ ∞ := by
    have hle :
        (⨆ thresholdN : ℕ,
          volume {x : ℝ | 1 / ((thresholdN : ℝ) + 1) < U x}) ≤
          volume (Ioo (-2 : ℝ) 2) := by
      refine iSup_le ?_
      intro thresholdN
      exact measure_mono (μ := volume)
        (by
          intro x hx
          exact unitIntervalTruncatedPotential_threshold_subset_Ioo_neg_two_two
            μ truncN thresholdN hx)
    have hfinite_window : volume (Ioo (-2 : ℝ) 2) ≠ ∞ := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top hfinite_window hle
  rcases exists_iSup_nat_le_add_of_ne_top
      (fun thresholdN : ℕ =>
        volume {x : ℝ | 1 / ((thresholdN : ℝ) + 1) < U x})
      hη hfinite with
    ⟨thresholdN, hthresholdN⟩
  refine ⟨thresholdN, ?_⟩
  simpa [U, unitIntervalPositiveTruncationScale,
    positiveSet_measure_eq_iSup_thresholds] using hthresholdN

theorem unitIntervalTruncatedPositiveSetObjective_compact_threshold_core :
    ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ η : NNReal, 0 < η →
        ∃ truncN thresholdN : ℕ, ∃ K : Set ℝ,
          volume (unitIntervalTruncatedPositiveSet μ) ≤
            volume K + (η : ℝ≥0∞) ∧
          K ⊆ {x : ℝ |
            unitIntervalPositiveTruncationScale thresholdN <
              unitIntervalTruncatedPotential
                (unitIntervalPositiveTruncationScale truncN) μ x} ∧
          IsCompact K := by
  intro μ η hη
  let ηPart : NNReal := η / 3
  have hηPart : 0 < ηPart := by
    positivity
  rcases unitIntervalTruncatedPositiveSet_exists_level_volume_le_add
      μ ηPart hηPart with
    ⟨truncN, hlevel⟩
  rcases unitIntervalTruncatedPotential_positiveSet_exists_threshold_volume_le_add
      μ truncN ηPart hηPart with
    ⟨thresholdN, hthreshold⟩
  rcases unitIntervalTruncatedPotential_threshold_exists_compact_core
      μ truncN thresholdN ηPart hηPart with
    ⟨K, hKsub, hKcompact, hKmeasure⟩
  refine ⟨truncN, thresholdN, K, ?_, hKsub, hKcompact⟩
  let S : Set ℝ := {x : ℝ |
    unitIntervalPositiveTruncationScale thresholdN <
      unitIntervalTruncatedPotential
        (unitIntervalPositiveTruncationScale truncN) μ x}
  have hSmeasure : volume S ≤ volume K + (ηPart : ℝ≥0∞) := by
    have hSsubset : S ⊆ K ∪ (S \ K) := by
      intro x hx
      by_cases hxK : x ∈ K
      · exact Or.inl hxK
      · exact Or.inr ⟨hx, hxK⟩
    have hmono : volume S ≤ volume (K ∪ (S \ K)) :=
      measure_mono hSsubset
    have hunion : volume (K ∪ (S \ K)) ≤ volume K + volume (S \ K) :=
      measure_union_le _ _
    calc
      volume S ≤ volume (K ∪ (S \ K)) := hmono
      _ ≤ volume K + volume (S \ K) := hunion
      _ ≤ volume K + (ηPart : ℝ≥0∞) := by
            simpa [S, add_comm, add_left_comm, add_assoc] using
              add_le_add_right hKmeasure (volume K)
  have hη_cast :
      (ηPart : ℝ≥0∞) + (ηPart : ℝ≥0∞) + (ηPart : ℝ≥0∞) = (η : ℝ≥0∞) := by
    simpa [ηPart] using ENNReal.add_thirds (η : ℝ≥0∞)
  calc
    volume (unitIntervalTruncatedPositiveSet μ)
        ≤ volume {x : ℝ | 0 <
            unitIntervalTruncatedPotential
              (unitIntervalPositiveTruncationScale truncN) μ x} +
          (ηPart : ℝ≥0∞) := hlevel
    _ ≤ (volume {x : ℝ |
            unitIntervalPositiveTruncationScale thresholdN <
              unitIntervalTruncatedPotential
                (unitIntervalPositiveTruncationScale truncN) μ x} +
          (ηPart : ℝ≥0∞)) + (ηPart : ℝ≥0∞) := by
            exact add_le_add hthreshold le_rfl
    _ ≤ ((volume K + (ηPart : ℝ≥0∞)) + (ηPart : ℝ≥0∞)) +
          (ηPart : ℝ≥0∞) := by
            simpa [S, add_assoc] using
              add_le_add_right (add_le_add hSmeasure le_rfl)
                (ηPart : ℝ≥0∞)
    _ = volume K + (η : ℝ≥0∞) := by
            calc
              ((volume K + (ηPart : ℝ≥0∞)) + (ηPart : ℝ≥0∞)) +
                    (ηPart : ℝ≥0∞)
                  = volume K + ((ηPart : ℝ≥0∞) + (ηPart : ℝ≥0∞) +
                    (ηPart : ℝ≥0∞)) := by ac_rfl
              _ = volume K + (η : ℝ≥0∞) := by rw [hη_cast]

/-- Truncated-sup positive-set length objective. -/
def unitIntervalTruncatedPositiveSetObjective
    (μ : ProbabilityMeasure UnitInterval1038) : ℝ≥0∞ :=
  volume (unitIntervalTruncatedPositiveSet μ)

theorem unitIntervalTruncatedPositiveSet_measurableSet_of_measurable
    (μ : ProbabilityMeasure UnitInterval1038)
    (htrunc : ∀ n : ℕ,
      Measurable
        (unitIntervalTruncatedPotential
          (unitIntervalPositiveTruncationScale n) μ)) :
    MeasurableSet (unitIntervalTruncatedPositiveSet μ) := by
  rw [show unitIntervalTruncatedPositiveSet μ =
      ⋃ n : ℕ,
        {x : ℝ | 0 < unitIntervalTruncatedPotential
          (unitIntervalPositiveTruncationScale n) μ x} by
    ext x
    simp [unitIntervalTruncatedPositiveSet]]
  exact MeasurableSet.iUnion fun n =>
    measurableSet_lt measurable_const (htrunc n)

/--
Lower-semicontinuity assembly for the truncated-sup objective.  The theorem
reduces LSC to compact threshold cores for the countable truncated-potential
family, and uses the existing weak continuity of truncated potentials on compact
sets to push each core into nearby truncated positive sets.
-/
theorem unitIntervalTruncatedPositiveSetObjective_lowerSemicontinuous_of_compact_threshold_core
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ η : NNReal, 0 < η →
        ∃ truncN thresholdN : ℕ, ∃ K : Set ℝ,
          volume (unitIntervalTruncatedPositiveSet μ) ≤
            volume K + (η : ℝ≥0∞) ∧
          K ⊆ {x : ℝ |
            unitIntervalPositiveTruncationScale thresholdN <
              unitIntervalTruncatedPotential
                (unitIntervalPositiveTruncationScale truncN) μ x} ∧
          IsCompact K) :
    LowerSemicontinuous unitIntervalTruncatedPositiveSetObjective := by
  rw [lowerSemicontinuous_iff]
  intro μ
  rw [lowerSemicontinuousAt_iff_le_liminf]
  let B : ℝ≥0∞ :=
    (nhds μ).liminf
      (fun ν : ProbabilityMeasure UnitInterval1038 =>
        unitIntervalTruncatedPositiveSetObjective ν)
  refine ENNReal.le_of_forall_pos_le_add ?_
  intro η hη _hB
  rcases hcore μ η hη with
    ⟨truncN, thresholdN, K, hKmeasure, hKsub, hKcompact⟩
  have hclose :
      ∀ᶠ ν in nhds μ, ∀ y ∈ K,
        |unitIntervalTruncatedPotential
            (unitIntervalPositiveTruncationScale truncN) ν y -
          unitIntervalTruncatedPotential
            (unitIntervalPositiveTruncationScale truncN) μ y| <
          unitIntervalPositiveTruncationScale thresholdN :=
    unitIntervalTruncatedPotential_eventually_close_on_compact μ
      (unitIntervalPositiveTruncationScale_pos truncN)
      (unitIntervalPositiveTruncationScale_pos thresholdN) hKcompact
  have hsub :
      ∀ᶠ ν in nhds μ, K ⊆ unitIntervalTruncatedPositiveSet ν := by
    filter_upwards [hclose] with ν hν y hyK
    have hyThreshold := hKsub hyK
    have hyThreshold' :
        unitIntervalPositiveTruncationScale thresholdN <
          unitIntervalTruncatedPotential
            (unitIntervalPositiveTruncationScale truncN) μ y :=
      hyThreshold
    have hyClose := hν y hyK
    have hyLower :
        -unitIntervalPositiveTruncationScale thresholdN <
          unitIntervalTruncatedPotential
              (unitIntervalPositiveTruncationScale truncN) ν y -
            unitIntervalTruncatedPotential
              (unitIntervalPositiveTruncationScale truncN) μ y :=
      (abs_lt.mp hyClose).1
    have hypos :
        0 <
          unitIntervalTruncatedPotential
            (unitIntervalPositiveTruncationScale truncN) ν y := by
      linarith
    exact ⟨truncN, hypos⟩
  have hKle :
      volume K ≤
        (nhds μ).liminf
          (fun ν : ProbabilityMeasure UnitInterval1038 =>
            unitIntervalTruncatedPositiveSetObjective ν) := by
    simpa [unitIntervalTruncatedPositiveSetObjective] using
      threshold_measure_le_liminf_of_eventually_subset K
        (fun ν : ProbabilityMeasure UnitInterval1038 =>
          unitIntervalTruncatedPositiveSet ν) hsub
  have hsum :
      volume K + (η : ℝ≥0∞) ≤ B + (η : ℝ≥0∞) := by
    simpa [B, add_comm, add_left_comm, add_assoc] using
      add_le_add_right hKle (η : ℝ≥0∞)
  exact le_trans hKmeasure hsum

/--
Lower semicontinuity of the truncated-sup objective with its compact
threshold-core provider generated internally.
-/
theorem unitIntervalTruncatedPositiveSetObjective_lowerSemicontinuous :
    LowerSemicontinuous unitIntervalTruncatedPositiveSetObjective := by
  exact unitIntervalTruncatedPositiveSetObjective_lowerSemicontinuous_of_compact_threshold_core
    unitIntervalTruncatedPositiveSetObjective_compact_threshold_core

/--
Compact-threshold-core minimizer existence for the truncated-sup surrogate.
This uses only the lower-semicontinuity assembled above from compact
threshold-core hypotheses.
-/
theorem unitIntervalTruncatedPositiveSetObjective_exists_minimizer_of_compact_threshold_core
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ η : NNReal, 0 < η →
        ∃ truncN thresholdN : ℕ, ∃ K : Set ℝ,
          volume (unitIntervalTruncatedPositiveSet μ) ≤
            volume K + (η : ℝ≥0∞) ∧
          K ⊆ {x : ℝ |
            unitIntervalPositiveTruncationScale thresholdN <
              unitIntervalTruncatedPotential
                (unitIntervalPositiveTruncationScale truncN) μ x} ∧
          IsCompact K) :
    ∃ μ : ProbabilityMeasure UnitInterval1038,
      ∀ ν : ProbabilityMeasure UnitInterval1038,
        unitIntervalTruncatedPositiveSetObjective μ ≤
          unitIntervalTruncatedPositiveSetObjective ν := by
  exact admissible_probability_lsc_exists_minimizer_ennreal
    unitIntervalTruncatedPositiveSetObjective
    (unitIntervalTruncatedPositiveSetObjective_lowerSemicontinuous_of_compact_threshold_core
      hcore)

/--
Primary minimizer existence for the truncated-sup surrogate, with the compact
threshold-core and lower-semicontinuity inputs generated internally.
-/
theorem unitIntervalTruncatedPositiveSetObjective_exists_minimizer :
    ∃ μ : ProbabilityMeasure UnitInterval1038,
      ∀ ν : ProbabilityMeasure UnitInterval1038,
        unitIntervalTruncatedPositiveSetObjective μ ≤
          unitIntervalTruncatedPositiveSetObjective ν := by
  exact admissible_probability_lsc_exists_minimizer_ennreal
    unitIntervalTruncatedPositiveSetObjective
    unitIntervalTruncatedPositiveSetObjective_lowerSemicontinuous

/--
Backward-compatible secondary minimizer selector for the truncated-sup
surrogate with an explicit lower-semicontinuous secondary parameter.  The
concrete Tao second-moment objective is `unitIntervalSecondMomentObjective`.
-/
theorem unitIntervalTruncatedPositiveSetObjective_exists_secondary_minimizer_of_compact_threshold_core
    (secondary : ProbabilityMeasure UnitInterval1038 → ℝ)
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ η : NNReal, 0 < η →
        ∃ truncN thresholdN : ℕ, ∃ K : Set ℝ,
          volume (unitIntervalTruncatedPositiveSet μ) ≤
            volume K + (η : ℝ≥0∞) ∧
          K ⊆ {x : ℝ |
            unitIntervalPositiveTruncationScale thresholdN <
              unitIntervalTruncatedPotential
                (unitIntervalPositiveTruncationScale truncN) μ x} ∧
          IsCompact K)
    (hsecondary_lsc : LowerSemicontinuous secondary) :
    ∃ μ : ProbabilityMeasure UnitInterval1038,
      (∀ ν : ProbabilityMeasure UnitInterval1038,
        unitIntervalTruncatedPositiveSetObjective μ ≤
          unitIntervalTruncatedPositiveSetObjective ν) ∧
      ∀ ν : ProbabilityMeasure UnitInterval1038,
        (∀ η : ProbabilityMeasure UnitInterval1038,
          unitIntervalTruncatedPositiveSetObjective ν ≤
            unitIntervalTruncatedPositiveSetObjective η) →
          secondary μ ≤ secondary ν := by
  exact admissible_probability_lsc_exists_secondary_minimizer_ennreal_primary
    unitIntervalTruncatedPositiveSetObjective secondary
    (unitIntervalTruncatedPositiveSetObjective_lowerSemicontinuous_of_compact_threshold_core
      hcore)
    hsecondary_lsc

/--
Concrete secondary minimizer selector for the truncated-sup surrogate: among
primary minimizers, choose one minimizing the second moment on `[-1,1]`.
-/
theorem unitIntervalTruncatedPositiveSetObjective_exists_secondMoment_secondary_minimizer :
    ∃ μ : ProbabilityMeasure UnitInterval1038,
      (∀ ν : ProbabilityMeasure UnitInterval1038,
        unitIntervalTruncatedPositiveSetObjective μ ≤
          unitIntervalTruncatedPositiveSetObjective ν) ∧
      ∀ ν : ProbabilityMeasure UnitInterval1038,
        (∀ η : ProbabilityMeasure UnitInterval1038,
          unitIntervalTruncatedPositiveSetObjective ν ≤
            unitIntervalTruncatedPositiveSetObjective η) →
          unitIntervalSecondMomentObjective μ ≤
            unitIntervalSecondMomentObjective ν := by
  exact admissible_probability_lsc_exists_secondary_minimizer_ennreal_primary
    unitIntervalTruncatedPositiveSetObjective unitIntervalSecondMomentObjective
    unitIntervalTruncatedPositiveSetObjective_lowerSemicontinuous
    unitIntervalSecondMomentObjective_lowerSemicontinuous

lemma truncatedLogKernel_le_logKernel {ε x t : ℝ}
    (hε : 0 < ε) (hne : x ≠ t) :
    truncatedLogKernel ε x t ≤ Real.log (1 / |x - t|) := by
  unfold truncatedLogKernel
  have hdist : 0 < |x - t| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hmaxpos : 0 < max ε |x - t| :=
    lt_of_lt_of_le hε (le_max_left ε |x - t|)
  have hden : |x - t| ≤ max ε |x - t| := le_max_right ε |x - t|
  have hinv : 1 / max ε |x - t| ≤ 1 / |x - t| := by
    exact one_div_le_one_div_of_le hdist hden
  exact Real.log_le_log (one_div_pos.mpr hmaxpos) hinv

theorem unitIntervalTruncatedPotential_le_logPotential_of_ae_ne
    {ε x : ℝ} {μ : ProbabilityMeasure UnitInterval1038}
    (hε : 0 < ε)
    (hae_ne : ∀ᵐ t : UnitInterval1038 ∂(μ : Measure UnitInterval1038),
      x ≠ (t : ℝ))
    (hlog_int : Integrable
      (fun t : UnitInterval1038 => Real.log (1 / |x - (t : ℝ)|))
      (μ : Measure UnitInterval1038)) :
    unitIntervalTruncatedPotential ε μ x ≤ unitIntervalLogPotential μ x := by
  have htrunc_int :
      Integrable
        (fun t : UnitInterval1038 => truncatedLogKernel ε x (t : ℝ))
        (μ : Measure UnitInterval1038) :=
    truncatedLogKernel_integrable μ hε
  have hle :
      (fun t : UnitInterval1038 => truncatedLogKernel ε x (t : ℝ))
        ≤ᵐ[(μ : Measure UnitInterval1038)]
          fun t : UnitInterval1038 => Real.log (1 / |x - (t : ℝ)|) := by
    filter_upwards [hae_ne] with t ht
    exact truncatedLogKernel_le_logKernel hε ht
  unfold unitIntervalTruncatedPotential unitIntervalLogPotential
  exact integral_mono_ae htrunc_int hlog_int hle

theorem unitInterval_diagonalAtom_or_truncatedPotential_le_logPotential
    {ε x : ℝ} {μ : ProbabilityMeasure UnitInterval1038}
    (hε : 0 < ε)
    (hlog_int : x ∉ diagonalAtomSet μ →
      Integrable
        (fun t : UnitInterval1038 => Real.log (1 / |x - (t : ℝ)|))
        (μ : Measure UnitInterval1038)) :
    x ∈ diagonalAtomSet μ ∨
      unitIntervalTruncatedPotential ε μ x ≤ unitIntervalLogPotential μ x := by
  by_cases hxdiag : x ∈ diagonalAtomSet μ
  · exact Or.inl hxdiag
  · exact Or.inr
      (unitIntervalTruncatedPotential_le_logPotential_of_ae_ne
        hε (ae_ne_of_notMem_diagonalAtomSet hxdiag) (hlog_int hxdiag))

theorem unitInterval_diagonalAtom_or_truncatedPotential_le_logPotential_eventually_on_compact
    (μ : ProbabilityMeasure UnitInterval1038) {ε : ℝ} {K : Set ℝ}
    (hε : 0 < ε)
    (hlog_int : ∀ᶠ ν in nhds μ, ∀ x ∈ K,
      x ∉ diagonalAtomSet ν →
        Integrable
          (fun t : UnitInterval1038 => Real.log (1 / |x - (t : ℝ)|))
          (ν : Measure UnitInterval1038)) :
    ∀ᶠ ν in nhds μ, ∀ x ∈ K,
      x ∈ diagonalAtomSet ν ∨
        unitIntervalTruncatedPotential ε ν x ≤
          unitIntervalLogPotential ν x := by
  filter_upwards [hlog_int] with ν hν x hxK
  exact unitInterval_diagonalAtom_or_truncatedPotential_le_logPotential
    hε (hν x hxK)

lemma truncatedLogKernel_eq_logKernel_of_eps_le_dist {ε x t : ℝ}
    (hε : ε ≤ |x - t|) :
    truncatedLogKernel ε x t = Real.log (1 / |x - t|) := by
  unfold truncatedLogKernel
  rw [max_eq_right hε]

lemma truncatedLogKernel_error_eq_zero_of_eps_le_dist {ε x t : ℝ}
    (hε : ε ≤ |x - t|) :
    |truncatedLogKernel ε x t - Real.log (1 / |x - t|)| = 0 := by
  rw [truncatedLogKernel_eq_logKernel_of_eps_le_dist hε]
  simp

lemma truncatedLogKernel_error_eq_log_ratio_of_dist_lt_eps
    {ε x t : ℝ} (hε : 0 < ε) (hxt : x ≠ t)
    (hdist : |x - t| < ε) :
    |truncatedLogKernel ε x t - Real.log (1 / |x - t|)| =
      Real.log (ε / |x - t|) := by
  have hdist_pos : 0 < |x - t| := abs_pos.mpr (sub_ne_zero.mpr hxt)
  have hratio_gt_one : 1 < ε / |x - t| := by
    rw [one_lt_div hdist_pos]
    exact hdist
  have hratio_nonneg : 0 ≤ Real.log (ε / |x - t|) :=
    le_of_lt (Real.log_pos hratio_gt_one)
  unfold truncatedLogKernel
  rw [max_eq_left (le_of_lt hdist)]
  have hlog_sub :
      Real.log (1 / ε) - Real.log (1 / |x - t|) =
        -Real.log (ε / |x - t|) := by
    have hpos_inv_eps : 0 < 1 / ε := one_div_pos.mpr hε
    have hpos_inv_dist : 0 < 1 / |x - t| := one_div_pos.mpr hdist_pos
    have hdiv_ne : |x - t| ≠ 0 := ne_of_gt hdist_pos
    calc
      Real.log (1 / ε) - Real.log (1 / |x - t|)
          = Real.log ((1 / ε) / (1 / |x - t|)) := by
              rw [Real.log_div hpos_inv_eps.ne' hpos_inv_dist.ne']
      _ = Real.log (|x - t| / ε) := by
              congr 1
              field_simp [hε.ne', hdiv_ne]
      _ = Real.log ((ε / |x - t|)⁻¹) := by
              congr 1
              field_simp [hε.ne', hdiv_ne]
      _ = -Real.log (ε / |x - t|) := by
              rw [Real.log_inv]
  rw [hlog_sub, abs_neg]
  exact abs_of_nonneg hratio_nonneg

lemma truncatedLogKernel_error_ofReal_le_singularTailKernel
    {ε x : ℝ} (hε : 0 < ε) (t : UnitInterval1038)
    (hxt : x ≠ (t : ℝ)) :
    ENNReal.ofReal
      |truncatedLogKernel ε x (t : ℝ) -
        Real.log (1 / |x - (t : ℝ)|)| ≤
      singularTailKernel ε x t := by
  by_cases hdist : |x - (t : ℝ)| < ε
  · rw [truncatedLogKernel_error_eq_log_ratio_of_dist_lt_eps hε hxt hdist]
    simp [singularTailKernel, hdist]
  · have hle : ε ≤ |x - (t : ℝ)| := le_of_not_gt hdist
    rw [truncatedLogKernel_error_eq_zero_of_eps_le_dist hle]
    simp [singularTailKernel, hdist]

lemma ae_ne_const_volume (c : ℝ) :
    ∀ᵐ x : ℝ ∂volume, x ≠ c := by
  rw [ae_iff]
  have hset : {x : ℝ | ¬x ≠ c} = ({c} : Set ℝ) := by
    ext x
    simp
  rw [hset]
  exact MeasureTheory.NoAtoms.measure_singleton c

lemma truncatedLogKernel_error_ofReal_le_singularTailKernel_ae
    {ε : ℝ} (hε : 0 < ε) (t : UnitInterval1038) :
    ∀ᵐ x : ℝ ∂volume,
      ENNReal.ofReal
        |truncatedLogKernel ε x (t : ℝ) -
          Real.log (1 / |x - (t : ℝ)|)| ≤
        singularTailKernel ε x t := by
  filter_upwards [ae_ne_const_volume (t : ℝ)] with x hxt
  exact truncatedLogKernel_error_ofReal_le_singularTailKernel hε t hxt

lemma unitIntervalTruncatedPotential_error_le_singularTailMass_of_ae_ne
    {ε x : ℝ} {μ : ProbabilityMeasure UnitInterval1038}
    (hε : 0 < ε)
    (hae_ne : ∀ᵐ t : UnitInterval1038 ∂(μ : Measure UnitInterval1038),
      x ≠ (t : ℝ))
    (htrunc_int : Integrable
      (fun t : UnitInterval1038 => truncatedLogKernel ε x (t : ℝ))
      (μ : Measure UnitInterval1038))
    (hlog_int : Integrable
      (fun t : UnitInterval1038 => Real.log (1 / |x - (t : ℝ)|))
      (μ : Measure UnitInterval1038)) :
    ENNReal.ofReal
      |unitIntervalTruncatedPotential ε μ x -
        unitIntervalLogPotential μ x| ≤ singularTailMass ε μ x := by
  let f : UnitInterval1038 → ℝ :=
    fun t => truncatedLogKernel ε x (t : ℝ)
  let g : UnitInterval1038 → ℝ :=
    fun t => Real.log (1 / |x - (t : ℝ)|)
  have hf : Integrable f (μ : Measure UnitInterval1038) := htrunc_int
  have hg : Integrable g (μ : Measure UnitInterval1038) := hlog_int
  have hdiff_int : Integrable (fun t => f t - g t)
      (μ : Measure UnitInterval1038) := hf.sub hg
  have hsub :
      (∫ t : UnitInterval1038, f t - g t ∂(μ : Measure UnitInterval1038)) =
        (∫ t : UnitInterval1038, f t ∂(μ : Measure UnitInterval1038)) -
          ∫ t : UnitInterval1038, g t ∂(μ : Measure UnitInterval1038) := by
    exact integral_sub hf hg
  have hreal_le :
      |(∫ t : UnitInterval1038, f t ∂(μ : Measure UnitInterval1038)) -
          ∫ t : UnitInterval1038, g t ∂(μ : Measure UnitInterval1038)| ≤
        ∫ t : UnitInterval1038, |f t - g t| ∂(μ : Measure UnitInterval1038) := by
    calc
      |(∫ t : UnitInterval1038, f t ∂(μ : Measure UnitInterval1038)) -
          ∫ t : UnitInterval1038, g t ∂(μ : Measure UnitInterval1038)|
          = ‖∫ t : UnitInterval1038, f t - g t ∂(μ : Measure UnitInterval1038)‖ := by
              rw [hsub]
              simp [Real.norm_eq_abs]
      _ ≤ ∫ t : UnitInterval1038, ‖f t - g t‖ ∂(μ : Measure UnitInterval1038) :=
              norm_integral_le_integral_norm (fun t : UnitInterval1038 => f t - g t)
      _ = ∫ t : UnitInterval1038, |f t - g t| ∂(μ : Measure UnitInterval1038) := by
              simp [Real.norm_eq_abs]
  have habs_nonneg :
      0 ≤ ∫ t : UnitInterval1038, |f t - g t| ∂(μ : Measure UnitInterval1038) :=
    integral_nonneg (fun t => abs_nonneg (f t - g t))
  have hlintegral_eq :
      (∫ t : UnitInterval1038, |f t - g t| ∂(μ : Measure UnitInterval1038)) =
        (∫⁻ t : UnitInterval1038, ENNReal.ofReal |f t - g t|
          ∂(μ : Measure UnitInterval1038)).toReal := by
    exact integral_eq_lintegral_of_nonneg_ae
      (show 0 ≤ᵐ[(μ : Measure UnitInterval1038)]
          fun t : UnitInterval1038 => |f t - g t| by
        filter_upwards with t
        exact abs_nonneg (f t - g t))
      hdiff_int.norm.aestronglyMeasurable
  have h_ofReal_real_le :
      ENNReal.ofReal
        |(∫ t : UnitInterval1038, f t ∂(μ : Measure UnitInterval1038)) -
          ∫ t : UnitInterval1038, g t ∂(μ : Measure UnitInterval1038)| ≤
        ∫⁻ t : UnitInterval1038, ENNReal.ofReal |f t - g t|
          ∂(μ : Measure UnitInterval1038) := by
    have hstep :
        ENNReal.ofReal
          |(∫ t : UnitInterval1038, f t ∂(μ : Measure UnitInterval1038)) -
            ∫ t : UnitInterval1038, g t ∂(μ : Measure UnitInterval1038)| ≤
          ENNReal.ofReal
            (∫ t : UnitInterval1038, |f t - g t|
              ∂(μ : Measure UnitInterval1038)) := by
      exact (ENNReal.ofReal_le_ofReal_iff habs_nonneg).2 hreal_le
    calc
      ENNReal.ofReal
          |(∫ t : UnitInterval1038, f t ∂(μ : Measure UnitInterval1038)) -
            ∫ t : UnitInterval1038, g t ∂(μ : Measure UnitInterval1038)|
          ≤ ENNReal.ofReal
            (∫ t : UnitInterval1038, |f t - g t|
              ∂(μ : Measure UnitInterval1038)) := hstep
      _ = ENNReal.ofReal
            ((∫⁻ t : UnitInterval1038, ENNReal.ofReal |f t - g t|
              ∂(μ : Measure UnitInterval1038)).toReal) := by rw [hlintegral_eq]
      _ ≤ ∫⁻ t : UnitInterval1038, ENNReal.ofReal |f t - g t|
              ∂(μ : Measure UnitInterval1038) := ENNReal.ofReal_toReal_le
  have hpoint :
      (fun t : UnitInterval1038 => ENNReal.ofReal |f t - g t|)
        ≤ᵐ[(μ : Measure UnitInterval1038)]
          fun t : UnitInterval1038 => singularTailKernel ε x t := by
    filter_upwards [hae_ne] with t ht
    exact truncatedLogKernel_error_ofReal_le_singularTailKernel hε t ht
  have hlintegral_le :
      (∫⁻ t : UnitInterval1038, ENNReal.ofReal |f t - g t|
          ∂(μ : Measure UnitInterval1038)) ≤ singularTailMass ε μ x := by
    unfold singularTailMass
    exact lintegral_mono_ae hpoint
  unfold unitIntervalTruncatedPotential unitIntervalLogPotential
  exact le_trans h_ofReal_real_le hlintegral_le

lemma integrable_of_lintegral_ofReal_abs_lt_top
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ)
    (hfinite : (∫⁻ a, ENNReal.ofReal |f a| ∂μ) < ∞) :
    Integrable f μ := by
  refine ⟨hf, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simpa [Real.norm_eq_abs] using hfinite

lemma logKernel_integrable_of_truncated_integrable_of_tailMass_lt_top
    {ε x : ℝ} {μ : ProbabilityMeasure UnitInterval1038}
    (hε : 0 < ε)
    (hae_ne : ∀ᵐ t : UnitInterval1038 ∂(μ : Measure UnitInterval1038),
      x ≠ (t : ℝ))
    (htrunc_int : Integrable
      (fun t : UnitInterval1038 => truncatedLogKernel ε x (t : ℝ))
      (μ : Measure UnitInterval1038))
    (htailFinite : singularTailMass ε μ x < ∞) :
    Integrable
      (fun t : UnitInterval1038 => Real.log (1 / |x - (t : ℝ)|))
      (μ : Measure UnitInterval1038) := by
  let f : UnitInterval1038 → ℝ :=
    fun t => truncatedLogKernel ε x (t : ℝ)
  let g : UnitInterval1038 → ℝ :=
    fun t => Real.log (1 / |x - (t : ℝ)|)
  let d : UnitInterval1038 → ℝ := fun t => f t - g t
  have hpoint :
      (fun t : UnitInterval1038 => ENNReal.ofReal |d t|)
        ≤ᵐ[(μ : Measure UnitInterval1038)]
          fun t : UnitInterval1038 => singularTailKernel ε x t := by
    filter_upwards [hae_ne] with t ht
    exact truncatedLogKernel_error_ofReal_le_singularTailKernel hε t ht
  have hlintegral_le :
      (∫⁻ t : UnitInterval1038, ENNReal.ofReal |d t|
          ∂(μ : Measure UnitInterval1038)) ≤ singularTailMass ε μ x := by
    unfold singularTailMass
    exact lintegral_mono_ae hpoint
  have hlintegral_lt :
      (∫⁻ t : UnitInterval1038, ENNReal.ofReal |d t|
          ∂(μ : Measure UnitInterval1038)) < ∞ :=
    lt_of_le_of_lt hlintegral_le htailFinite
  have hd_meas : AEStronglyMeasurable d (μ : Measure UnitInterval1038) := by
    have hf_meas : AEStronglyMeasurable f (μ : Measure UnitInterval1038) :=
      htrunc_int.aestronglyMeasurable
    have hg_meas : AEStronglyMeasurable g (μ : Measure UnitInterval1038) := by
      dsimp [g]
      exact (Real.measurable_log.comp
        (measurable_const.div
          ((continuous_const.sub continuous_subtype_val).abs.measurable))).aestronglyMeasurable
    exact hf_meas.sub hg_meas
  have hd_int : Integrable d (μ : Measure UnitInterval1038) :=
    integrable_of_lintegral_ofReal_abs_lt_top hd_meas hlintegral_lt
  have hf_int : Integrable f (μ : Measure UnitInterval1038) := htrunc_int
  have hmain : Integrable (fun t : UnitInterval1038 => f t - d t)
      (μ : Measure UnitInterval1038) := hf_int.sub hd_int
  exact hmain.congr (Filter.Eventually.of_forall (fun t => by
    dsimp [d, f, g]
    ring))

lemma unitInterval_logKernel_integrable_of_tailMass_lt_top
    {ε x : ℝ} {μ : ProbabilityMeasure UnitInterval1038}
    (hε : 0 < ε)
    (hae_ne : ∀ᵐ t : UnitInterval1038 ∂(μ : Measure UnitInterval1038),
      x ≠ (t : ℝ))
    (htailFinite : singularTailMass ε μ x < ∞) :
    Integrable
      (fun t : UnitInterval1038 => Real.log (1 / |x - (t : ℝ)|))
      (μ : Measure UnitInterval1038) := by
  exact logKernel_integrable_of_truncated_integrable_of_tailMass_lt_top
    hε hae_ne (truncatedLogKernel_integrable μ hε) htailFinite

/-- If an atom location is uniformly separated from `[-1,1]`, its log kernel is integrable. -/
lemma unitInterval_logKernel_integrable_of_uniform_separation
    {ε x : ℝ} {μ : ProbabilityMeasure UnitInterval1038}
    (hε : 0 < ε)
    (hsep : ∀ t : UnitInterval1038, ε ≤ |x - (t : ℝ)|) :
    Integrable
      (fun t : UnitInterval1038 => Real.log (1 / |x - (t : ℝ)|))
      (μ : Measure UnitInterval1038) := by
  have hae_ne : ∀ᵐ t : UnitInterval1038 ∂(μ : Measure UnitInterval1038),
      x ≠ (t : ℝ) := by
    exact Filter.Eventually.of_forall (fun t hxt => by
      have hzero : |x - (t : ℝ)| = 0 := by simp [hxt]
      have hε_nonpos : ε ≤ 0 := by simpa [hzero] using hsep t
      linarith)
  have htail_zero : singularTailMass ε μ x = 0 := by
    unfold singularTailMass
    have hkernel_zero :
        (fun t : UnitInterval1038 => singularTailKernel ε x t) =
          fun _ : UnitInterval1038 => 0 := by
      funext t
      unfold singularTailKernel
      simp [not_lt.mpr (hsep t)]
    simp [hkernel_zero]
  have htailFinite : singularTailMass ε μ x < ∞ := by
    rw [htail_zero]
    simp
  exact unitInterval_logKernel_integrable_of_tailMass_lt_top hε hae_ne htailFinite

/-- A point strictly to the left of `[-1,1]` is uniformly separated from the unit interval. -/
lemma unitInterval_left_separation {x : ℝ} (hx : x < -1)
    (t : UnitInterval1038) :
    -(x + 1) ≤ |x - (t : ℝ)| := by
  have ht_left : (-1 : ℝ) ≤ (t : ℝ) := t.2.1
  have hnonpos : x - (t : ℝ) ≤ 0 := by linarith
  rw [abs_of_nonpos hnonpos]
  linarith

/-- Log-kernel integrability for atom locations strictly to the left of `[-1,1]`. -/
lemma unitInterval_logKernel_integrable_of_left_outside
    {x : ℝ} {μ : ProbabilityMeasure UnitInterval1038}
    (hx : x < -1) :
    Integrable
      (fun t : UnitInterval1038 => Real.log (1 / |x - (t : ℝ)|))
      (μ : Measure UnitInterval1038) := by
  refine unitInterval_logKernel_integrable_of_uniform_separation
    (μ := μ) (ε := -(x + 1)) (x := x) ?_ ?_
  · linarith
  · exact unitInterval_left_separation hx

/-- A point strictly to the right of `[-1,1]` is uniformly separated from the unit interval. -/
lemma unitInterval_right_separation {x : ℝ} (hx : 1 < x)
    (t : UnitInterval1038) :
    x - 1 ≤ |x - (t : ℝ)| := by
  have ht_right : (t : ℝ) ≤ 1 := t.2.2
  have hnonneg : 0 ≤ x - (t : ℝ) := by linarith
  rw [abs_of_nonneg hnonneg]
  linarith

/-- Log-kernel integrability for atom locations strictly to the right of `[-1,1]`. -/
lemma unitInterval_logKernel_integrable_of_right_outside
    {x : ℝ} {μ : ProbabilityMeasure UnitInterval1038}
    (hx : 1 < x) :
    Integrable
      (fun t : UnitInterval1038 => Real.log (1 / |x - (t : ℝ)|))
      (μ : Measure UnitInterval1038) := by
  refine unitInterval_logKernel_integrable_of_uniform_separation
    (μ := μ) (ε := x - 1) (x := x) ?_ ?_
  · linarith
  · exact unitInterval_right_separation hx

/--
Finite atomic duality when every atom location lies strictly outside `[-1,1]`.
The separation from the unit interval supplies the per-atom integrability
needed by `FiniteAtomicUnitIntervalDualityIdentity.of_integrable_atom_kernels`.
-/
theorem FiniteAtomicUnitIntervalDualityIdentity.of_atoms_outside_unitInterval
    {ι : Type*} [DecidableEq ι]
    (μ : ProbabilityMeasure UnitInterval1038)
    (s : Finset ι) (w atom : ι → ℝ)
    (houtside : ∀ i ∈ s, atom i < -1 ∨ 1 < atom i) :
    FiniteAtomicUnitIntervalDualityIdentity μ s w atom := by
  refine FiniteAtomicUnitIntervalDualityIdentity.of_integrable_atom_kernels
    μ s w atom ?_
  intro i hi
  rcases houtside i hi with hleft | hright
  · have hbase :
        Integrable
          (fun x : UnitInterval1038 =>
            Real.log (1 / |atom i - (x : ℝ)|))
          (μ : Measure UnitInterval1038) :=
      unitInterval_logKernel_integrable_of_left_outside
        (μ := μ) (x := atom i) hleft
    exact hbase.congr (Filter.Eventually.of_forall (fun x => by
      simp [abs_sub_comm]))
  · have hbase :
        Integrable
          (fun x : UnitInterval1038 =>
            Real.log (1 / |atom i - (x : ℝ)|))
          (μ : Measure UnitInterval1038) :=
      unitInterval_logKernel_integrable_of_right_outside
        (μ := μ) (x := atom i) hright
    exact hbase.congr (Filter.Eventually.of_forall (fun x => by
      simp [abs_sub_comm]))

/--
Off-diagonal tail-mass integrability bridge for candidate atom locations.

The hypothesis `x ∉ diagonalAtomSet μ` is exactly the condition needed to turn
the diagonal singularity into an almost-everywhere off-diagonal statement via
`ae_ne_of_notMem_diagonalAtomSet`; the finite tail-mass bound then supplies
integrability of the real-valued logarithmic kernel.
-/
theorem unitInterval_logKernel_integrable_of_notMem_diagonalAtomSet_tailMass
    {ε x : ℝ} {μ : ProbabilityMeasure UnitInterval1038}
    (hε : 0 < ε)
    (hxdiag : x ∉ diagonalAtomSet μ)
    (htailFinite : singularTailMass ε μ x < ∞) :
    Integrable
      (fun t : UnitInterval1038 => Real.log (1 / |(t : ℝ) - x|))
      (μ : Measure UnitInterval1038) := by
  have hbase :
      Integrable
        (fun t : UnitInterval1038 => Real.log (1 / |x - (t : ℝ)|))
        (μ : Measure UnitInterval1038) :=
    unitInterval_logKernel_integrable_of_tailMass_lt_top
      hε (ae_ne_of_notMem_diagonalAtomSet hxdiag) htailFinite
  exact hbase.congr (Filter.Eventually.of_forall (fun t => by
    simp [abs_sub_comm]))

/--
Candidate-location dichotomy for the real-valued finite-atom selector.

If the candidate location is a true atom of `μ`, this theorem returns the
diagonal exceptional branch.  It deliberately does not assert membership in
`PositiveSet (unitIntervalLogPotential μ)`: with the current real-valued
definition, the pointwise diagonal kernel uses `Real.log 0`, not an extended
`+∞` singularity.  If the candidate is not a diagonal atom, finite tail mass
gives the per-candidate log-kernel integrability needed by the finite duality
identity.
-/
theorem unitInterval_candidateAtom_diagonal_or_logKernel_integrable_of_tailMass
    {ε x : ℝ} {μ : ProbabilityMeasure UnitInterval1038}
    (hε : 0 < ε)
    (htailFinite : singularTailMass ε μ x < ∞) :
    x ∈ diagonalAtomSet μ ∨
      Integrable
        (fun t : UnitInterval1038 => Real.log (1 / |(t : ℝ) - x|))
        (μ : Measure UnitInterval1038) := by
  by_cases hxdiag : x ∈ diagonalAtomSet μ
  · exact Or.inl hxdiag
  · exact Or.inr
      (unitInterval_logKernel_integrable_of_notMem_diagonalAtomSet_tailMass
        hε hxdiag htailFinite)

/--
Finite atomic duality identity for off-diagonal candidate atom locations with
finite singular tail mass.

This is the inside-interval replacement for the outside-interval separation
wrapper above: no separation from `[-1,1]` is needed, but every finite candidate
must either be handled by the diagonal exceptional branch or be explicitly
off-diagonal with finite tail mass.
-/
theorem FiniteAtomicUnitIntervalDualityIdentity.of_atoms_offDiagonal_tailMass
    {ι : Type*} [DecidableEq ι]
    {ε : ℝ} (hε : 0 < ε)
    (μ : ProbabilityMeasure UnitInterval1038)
    (s : Finset ι) (w atom : ι → ℝ)
    (hoffdiag : ∀ i ∈ s, atom i ∉ diagonalAtomSet μ)
    (htailFinite : ∀ i ∈ s, singularTailMass ε μ (atom i) < ∞) :
    FiniteAtomicUnitIntervalDualityIdentity μ s w atom := by
  refine FiniteAtomicUnitIntervalDualityIdentity.of_integrable_atom_kernels
    μ s w atom ?_
  intro i hi
  exact unitInterval_logKernel_integrable_of_notMem_diagonalAtomSet_tailMass
    hε (hoffdiag i hi) (htailFinite i hi)

/--
Finite selector wrapper for candidate atoms inside `[-1,1]`, after diagonal
candidate atoms have been removed into the exceptional/selector branch.

The theorem carries the inside-interval membership to the selected atom and
uses only off-diagonal plus finite tail-mass assumptions to prove the finite
duality identity internally.
-/
theorem finiteAtomicUnitIntervalDuality_offDiagonal_tailMass_selects_atom_in_unitInterval
    {ι : Type*} [DecidableEq ι]
    {ε : ℝ} (hε : 0 < ε)
    (μ : ProbabilityMeasure UnitInterval1038)
    (s : Finset ι) (w atom : ι → ℝ)
    (hatom_unit : ∀ i ∈ s, atom i ∈ Icc (-1 : ℝ) 1)
    (hoffdiag : ∀ i ∈ s, atom i ∉ diagonalAtomSet μ)
    (htailFinite : ∀ i ∈ s, singularTailMass ε μ (atom i) < ∞)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hintegral_pos :
      0 < ∫ x : UnitInterval1038,
        finiteWeightedPotential s w atom (x : ℝ)
          ∂(μ : Measure UnitInterval1038)) :
    ∃ i : ι, i ∈ s ∧ atom i ∈ Icc (-1 : ℝ) 1 ∧
      atom i ∈ PositiveSet (unitIntervalLogPotential μ) := by
  exact
    (FiniteAtomicUnitIntervalDualityIdentity.of_atoms_offDiagonal_tailMass
      hε μ s w atom hoffdiag htailFinite).selects_atom_in_domain
      hw_nonneg hatom_unit hintegral_pos

/--
Unified finite atomic duality identity for mixed finite certificates.

For each candidate atom, the branch assumption is explicit: either the atom is
strictly outside `[-1,1]`, where separation from the unit interval supplies
integrability, or it lies inside `[-1,1]` and is off the diagonal atom set of
`μ`, with some positive truncation scale at which its singular tail mass is
finite.  Diagonal atoms inside `[-1,1]` are not hidden by this theorem; they
must be handled by a separate exceptional branch.
-/
theorem FiniteAtomicUnitIntervalDualityIdentity.of_atoms_outside_or_offDiagonal_tailMass
    {ι : Type*} [DecidableEq ι]
    (μ : ProbabilityMeasure UnitInterval1038)
    (s : Finset ι) (w atom : ι → ℝ)
    (hatom :
      ∀ i ∈ s,
        (atom i < -1 ∨ 1 < atom i) ∨
          (atom i ∈ Icc (-1 : ℝ) 1 ∧
            atom i ∉ diagonalAtomSet μ ∧
            ∃ ε : ℝ, 0 < ε ∧ singularTailMass ε μ (atom i) < ∞)) :
    FiniteAtomicUnitIntervalDualityIdentity μ s w atom := by
  refine FiniteAtomicUnitIntervalDualityIdentity.of_integrable_atom_kernels
    μ s w atom ?_
  intro i hi
  rcases hatom i hi with houtside | hinside
  · rcases houtside with hleft | hright
    · have hbase :
          Integrable
            (fun x : UnitInterval1038 =>
              Real.log (1 / |atom i - (x : ℝ)|))
            (μ : Measure UnitInterval1038) :=
        unitInterval_logKernel_integrable_of_left_outside
          (μ := μ) (x := atom i) hleft
      exact hbase.congr (Filter.Eventually.of_forall (fun x => by
        simp [abs_sub_comm]))
    · have hbase :
          Integrable
            (fun x : UnitInterval1038 =>
              Real.log (1 / |atom i - (x : ℝ)|))
            (μ : Measure UnitInterval1038) :=
        unitInterval_logKernel_integrable_of_right_outside
          (μ := μ) (x := atom i) hright
      exact hbase.congr (Filter.Eventually.of_forall (fun x => by
        simp [abs_sub_comm]))
  · rcases hinside with ⟨_hunit, hoffdiag, ε, hε, htailFinite⟩
    exact unitInterval_logKernel_integrable_of_notMem_diagonalAtomSet_tailMass
      hε hoffdiag htailFinite

/--
Direct selector wrapper for mixed outside/off-diagonal finite certificates.

Assume every finite candidate atom is either strictly outside `[-1,1]`, or is
inside `[-1,1]`, off `diagonalAtomSet μ`, and has finite singular tail mass at
some positive truncation scale.  Together with nonnegative weights and
positivity of the finite weighted-potential integral, this selects an atom in
the actual positive set while preserving the same branch information.  Inside
diagonal atoms remain excluded and must be handled separately.
-/
theorem finiteAtomicUnitIntervalDuality_outside_or_offDiagonal_tailMass_selects_atom
    {ι : Type*} [DecidableEq ι]
    (μ : ProbabilityMeasure UnitInterval1038)
    (s : Finset ι) (w atom : ι → ℝ)
    (hatom :
      ∀ i ∈ s,
        (atom i < -1 ∨ 1 < atom i) ∨
          (atom i ∈ Icc (-1 : ℝ) 1 ∧
            atom i ∉ diagonalAtomSet μ ∧
            ∃ ε : ℝ, 0 < ε ∧ singularTailMass ε μ (atom i) < ∞))
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hintegral_pos :
      0 < ∫ x : UnitInterval1038,
        finiteWeightedPotential s w atom (x : ℝ)
          ∂(μ : Measure UnitInterval1038)) :
    ∃ i : ι, i ∈ s ∧
      ((atom i < -1 ∨ 1 < atom i) ∨
        (atom i ∈ Icc (-1 : ℝ) 1 ∧
          atom i ∉ diagonalAtomSet μ ∧
          ∃ ε : ℝ, 0 < ε ∧ singularTailMass ε μ (atom i) < ∞)) ∧
      atom i ∈ PositiveSet (unitIntervalLogPotential μ) := by
  exact
    (FiniteAtomicUnitIntervalDualityIdentity.of_atoms_outside_or_offDiagonal_tailMass
      μ s w atom hatom).selects_atom_in_domain
      (Domain := {x : ℝ |
        (x < -1 ∨ 1 < x) ∨
          (x ∈ Icc (-1 : ℝ) 1 ∧
            x ∉ diagonalAtomSet μ ∧
            ∃ ε : ℝ, 0 < ε ∧ singularTailMass ε μ x < ∞)})
      hw_nonneg (fun i hi => hatom i hi) hintegral_pos

theorem unitInterval_tailCore_error_bound_of_ae_ne
    {ε : ℝ} {μ : ProbabilityMeasure UnitInterval1038} {n : ℕ} {δ : ℝ}
    (hε : 0 < ε)
    (hae_ne : ∀ x ∈ unitIntervalThresholdTailCore μ n ε δ,
      ∀ᵐ t : UnitInterval1038 ∂(μ : Measure UnitInterval1038),
        x ≠ (t : ℝ))
    (htrunc_int : ∀ x ∈ unitIntervalThresholdTailCore μ n ε δ,
      Integrable
        (fun t : UnitInterval1038 => truncatedLogKernel ε x (t : ℝ))
        (μ : Measure UnitInterval1038))
    (hlog_int : ∀ x ∈ unitIntervalThresholdTailCore μ n ε δ,
      Integrable
        (fun t : UnitInterval1038 => Real.log (1 / |x - (t : ℝ)|))
        (μ : Measure UnitInterval1038)) :
    ∀ x ∈ unitIntervalThresholdTailCore μ n ε δ,
      ENNReal.ofReal
        |unitIntervalTruncatedPotential ε μ x -
          unitIntervalLogPotential μ x| ≤ singularTailMass ε μ x := by
  intro x hx
  exact unitIntervalTruncatedPotential_error_le_singularTailMass_of_ae_ne
    hε (hae_ne x hx) (htrunc_int x hx) (hlog_int x hx)

theorem unitInterval_tailCoreOffDiagonal_error_bound_of_integrable
    {ε : ℝ} {μ : ProbabilityMeasure UnitInterval1038} {n : ℕ} {δ : ℝ}
    (hε : 0 < ε)
    (htrunc_int : ∀ x ∈
        unitIntervalThresholdTailCoreOffDiagonal μ n ε δ (diagonalAtomSet μ),
      Integrable
        (fun t : UnitInterval1038 => truncatedLogKernel ε x (t : ℝ))
        (μ : Measure UnitInterval1038))
    (hlog_int : ∀ x ∈
        unitIntervalThresholdTailCoreOffDiagonal μ n ε δ (diagonalAtomSet μ),
      Integrable
        (fun t : UnitInterval1038 => Real.log (1 / |x - (t : ℝ)|))
        (μ : Measure UnitInterval1038)) :
    ∀ x ∈ unitIntervalThresholdTailCoreOffDiagonal μ n ε δ (diagonalAtomSet μ),
      ENNReal.ofReal
        |unitIntervalTruncatedPotential ε μ x -
          unitIntervalLogPotential μ x| ≤ singularTailMass ε μ x := by
  intro x hx
  exact unitIntervalTruncatedPotential_error_le_singularTailMass_of_ae_ne
    hε (ae_ne_of_notMem_diagonalAtomSet hx.2)
    (htrunc_int x hx) (hlog_int x hx)

/--
Uniform tail-error estimate on the off-diagonal tail core.  The same `δ` works
for every `x` in the core because the core definition includes the uniform tail
mass bound `singularTailMass ε μ x < ofReal δ`.
-/
theorem unitInterval_tailCoreOffDiagonal_error_lt
    {ε : ℝ} {μ : ProbabilityMeasure UnitInterval1038} {n : ℕ} {δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ x ∈ unitIntervalThresholdTailCoreOffDiagonal μ n ε δ (diagonalAtomSet μ),
      |unitIntervalTruncatedPotential ε μ x -
        unitIntervalLogPotential μ x| < δ := by
  intro x hx
  have htailFinite : singularTailMass ε μ x < ∞ :=
    lt_trans hx.1.2 ENNReal.ofReal_lt_top
  have hlog_int :
      Integrable
        (fun t : UnitInterval1038 => Real.log (1 / |x - (t : ℝ)|))
        (μ : Measure UnitInterval1038) :=
    unitInterval_logKernel_integrable_of_tailMass_lt_top
      hε (ae_ne_of_notMem_diagonalAtomSet hx.2) htailFinite
  have herror :
      ENNReal.ofReal
        |unitIntervalTruncatedPotential ε μ x -
          unitIntervalLogPotential μ x| ≤ singularTailMass ε μ x :=
    unitIntervalTruncatedPotential_error_le_singularTailMass_of_ae_ne
      hε (ae_ne_of_notMem_diagonalAtomSet hx.2)
      (truncatedLogKernel_integrable μ hε) hlog_int
  exact truncated_potential_error_lt_of_tail_bound hδ herror hx.1.2

theorem unitInterval_log_error_lt_of_tailMass_and_ae_ne
    {ε δ x : ℝ} {μ : ProbabilityMeasure UnitInterval1038}
    (hε : 0 < ε) (hδ : 0 < δ)
    (htail : singularTailMass ε μ x < ENNReal.ofReal δ)
    (hae_ne : ∀ᵐ t : UnitInterval1038 ∂(μ : Measure UnitInterval1038),
      x ≠ (t : ℝ)) :
    |unitIntervalTruncatedPotential ε μ x -
      unitIntervalLogPotential μ x| < δ := by
  have htailFinite : singularTailMass ε μ x < ∞ :=
    lt_trans htail ENNReal.ofReal_lt_top
  have hlog_int :
      Integrable
        (fun t : UnitInterval1038 => Real.log (1 / |x - (t : ℝ)|))
        (μ : Measure UnitInterval1038) :=
    unitInterval_logKernel_integrable_of_tailMass_lt_top
      hε hae_ne htailFinite
  have herror :
      ENNReal.ofReal
        |unitIntervalTruncatedPotential ε μ x -
          unitIntervalLogPotential μ x| ≤ singularTailMass ε μ x :=
    unitIntervalTruncatedPotential_error_le_singularTailMass_of_ae_ne
      hε hae_ne (truncatedLogKernel_integrable μ hε) hlog_int
  exact truncated_potential_error_lt_of_tail_bound hδ herror htail

theorem unitInterval_diagonalAtom_or_log_error_lt_of_tailMass
    {ε δ x : ℝ} {μ : ProbabilityMeasure UnitInterval1038}
    (hε : 0 < ε) (hδ : 0 < δ)
    (htail : singularTailMass ε μ x < ENNReal.ofReal δ) :
    x ∈ diagonalAtomSet μ ∨
      |unitIntervalTruncatedPotential ε μ x -
        unitIntervalLogPotential μ x| < δ := by
  by_cases hxdiag : x ∈ diagonalAtomSet μ
  · exact Or.inl hxdiag
  · exact Or.inr
      (unitInterval_log_error_lt_of_tailMass_and_ae_ne
        hε hδ htail (ae_ne_of_notMem_diagonalAtomSet hxdiag))

theorem unitInterval_log_error_eventually_on_compact_of_tailMass_and_ae_ne
    (μ : ProbabilityMeasure UnitInterval1038) {ε δ : ℝ} {K : Set ℝ}
    (hε : 0 < ε) (hδ : 0 < δ)
    (htail : ∀ᶠ ν in nhds μ, ∀ x ∈ K,
      singularTailMass ε ν x < ENNReal.ofReal δ)
    (hae_ne : ∀ᶠ (ν : ProbabilityMeasure UnitInterval1038) in nhds μ, ∀ x ∈ K,
      ∀ᵐ t : UnitInterval1038 ∂(ν : Measure UnitInterval1038),
        x ≠ (t : ℝ)) :
    ∀ᶠ ν in nhds μ, ∀ x ∈ K,
      |unitIntervalTruncatedPotential ε ν x -
        unitIntervalLogPotential ν x| < δ := by
  filter_upwards [htail, hae_ne] with ν htailν haeν x hxK
  exact unitInterval_log_error_lt_of_tailMass_and_ae_ne
    hε hδ (htailν x hxK) (haeν x hxK)

theorem unitInterval_log_error_eventually_on_compact_of_tailMass_and_ae_ne_limit
    (μ : ProbabilityMeasure UnitInterval1038) {ε δ τ : ℝ} {K : Set ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hδ_le : δ ≤ τ)
    (htail : ∀ᶠ ν in nhds μ, ∀ x ∈ K,
      singularTailMass ε ν x < ENNReal.ofReal δ)
    (hae_ne : ∀ᶠ (ν : ProbabilityMeasure UnitInterval1038) in nhds μ, ∀ x ∈ K,
      ∀ᵐ t : UnitInterval1038 ∂(ν : Measure UnitInterval1038),
        x ≠ (t : ℝ)) :
    ∀ᶠ ν in nhds μ, ∀ x ∈ K,
      |unitIntervalTruncatedPotential ε ν x -
        unitIntervalLogPotential ν x| < τ := by
  filter_upwards [
    unitInterval_log_error_eventually_on_compact_of_tailMass_and_ae_ne
      μ hε hδ htail hae_ne] with ν hν x hxK
  exact lt_of_lt_of_le (hν x hxK) hδ_le

theorem unitInterval_diagonalAtom_or_log_error_eventually_on_compact_of_tailMass
    (μ : ProbabilityMeasure UnitInterval1038) {ε δ : ℝ} {K : Set ℝ}
    (hε : 0 < ε) (hδ : 0 < δ)
    (htail : ∀ᶠ ν in nhds μ, ∀ x ∈ K,
      singularTailMass ε ν x < ENNReal.ofReal δ) :
    ∀ᶠ ν in nhds μ, ∀ x ∈ K,
      x ∈ diagonalAtomSet ν ∨
        |unitIntervalTruncatedPotential ε ν x -
          unitIntervalLogPotential ν x| < δ := by
  filter_upwards [htail] with ν htailν x hxK
  exact unitInterval_diagonalAtom_or_log_error_lt_of_tailMass
    hε hδ (htailν x hxK)

theorem unitInterval_diagonalAtom_or_log_error_eventually_on_compact_of_tailMass_limit
    (μ : ProbabilityMeasure UnitInterval1038) {ε δ τ : ℝ} {K : Set ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hδ_le : δ ≤ τ)
    (htail : ∀ᶠ ν in nhds μ, ∀ x ∈ K,
      singularTailMass ε ν x < ENNReal.ofReal δ) :
    ∀ᶠ ν in nhds μ, ∀ x ∈ K,
      x ∈ diagonalAtomSet ν ∨
        |unitIntervalTruncatedPotential ε ν x -
          unitIntervalLogPotential ν x| < τ := by
  filter_upwards [
    unitInterval_diagonalAtom_or_log_error_eventually_on_compact_of_tailMass
      μ hε hδ htail] with ν hν x hxK
  rcases hν x hxK with hxdiag | herr
  · exact Or.inl hxdiag
  · exact Or.inr (lt_of_lt_of_le herr hδ_le)

/-- Compact-core wrapper for the off-diagonal tail-error estimate. -/
theorem unitInterval_tailCoreOffDiagonal_error_lt_on_compact
    {ε : ℝ} {μ : ProbabilityMeasure UnitInterval1038} {n : ℕ} {δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ)
    {K : Set ℝ}
    (hKsub :
      K ⊆ unitIntervalThresholdTailCoreOffDiagonal μ n ε δ
        (diagonalAtomSet μ)) :
    ∀ x ∈ K,
      |unitIntervalTruncatedPotential ε μ x -
        unitIntervalLogPotential μ x| < δ := by
  intro x hx
  exact unitInterval_tailCoreOffDiagonal_error_lt hε hδ x (hKsub hx)

/--
Tail-error estimate in the exact `τ/3` form used by the threshold-core
argument.
-/
theorem unitInterval_tailCoreOffDiagonal_limit_error_on_compact
    {ε : ℝ} {μ : ProbabilityMeasure UnitInterval1038} {n : ℕ} {δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ)
    {K : Set ℝ}
    (hKsub :
      K ⊆ unitIntervalThresholdTailCoreOffDiagonal μ n ε δ
        (diagonalAtomSet μ))
    (hδ_le : δ ≤ (1 / ((n : ℝ) + 1)) / 3) :
    ∀ x ∈ K,
      |unitIntervalTruncatedPotential ε μ x -
        unitIntervalLogPotential μ x| <
          (1 / ((n : ℝ) + 1)) / 3 := by
  intro x hx
  exact lt_of_lt_of_le
    (unitInterval_tailCoreOffDiagonal_error_lt_on_compact hε hδ hKsub x hx)
    hδ_le

theorem unitIntervalPositiveSetObjective_lowerSemicontinuous_of_compact_tailCore
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ truncε δ : ℝ, ∃ K : Set ℝ,
          0 < truncε ∧
          0 < δ ∧
          δ ≤ (1 / ((n : ℝ) + 1)) / 3 ∧
          K ⊆ unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ
            (diagonalAtomSet μ) ∧
          IsCompact K ∧
          volume ({x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} \ K) ≤ (ε : ℝ≥0∞) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ K,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalLogPotential ν x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ K,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalTruncatedPotential truncε μ x| <
              (1 / ((n : ℝ) + 1)) / 3)) :
    LowerSemicontinuous unitIntervalPositiveSetObjective := by
  refine unitIntervalPositiveSetObjective_lowerSemicontinuous_of_compact_core ?_
  intro μ n ε hε
  rcases hcore μ n ε hε with
    ⟨truncε, δ, K, htruncε_pos, hδ_pos, hδ_le, hKsub, hKcompact,
      hmeasure, hseq, htrunc⟩
  refine ⟨truncε, K, ?_, hKcompact, hmeasure, ?_, hseq, htrunc⟩
  · intro x hx
    exact unitInterval_tailCoreOffDiagonal_subset_threshold μ n truncε δ
      (diagonalAtomSet μ) (hKsub hx)
  · exact unitInterval_tailCoreOffDiagonal_limit_error_on_compact
      htruncε_pos hδ_pos hKsub hδ_le

theorem unitIntervalPositiveSetObjective_exists_minimizer_of_compact_tailCore
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ truncε δ : ℝ, ∃ K : Set ℝ,
          0 < truncε ∧
          0 < δ ∧
          δ ≤ (1 / ((n : ℝ) + 1)) / 3 ∧
          K ⊆ unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ
            (diagonalAtomSet μ) ∧
          IsCompact K ∧
          volume ({x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} \ K) ≤ (ε : ℝ≥0∞) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ K,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalLogPotential ν x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ K,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalTruncatedPotential truncε μ x| <
              (1 / ((n : ℝ) + 1)) / 3)) :
    ∃ μ : ProbabilityMeasure UnitInterval1038,
      ∀ ν : ProbabilityMeasure UnitInterval1038,
        unitIntervalPositiveSetObjective μ ≤
          unitIntervalPositiveSetObjective ν := by
  exact admissible_probability_lsc_exists_minimizer_ennreal
    unitIntervalPositiveSetObjective
    (unitIntervalPositiveSetObjective_lowerSemicontinuous_of_compact_tailCore hcore)

/--
Compact-tail-core lower semicontinuity with the truncated-potential compact
continuity term provided by the preceding theorem.  After this theorem, the compact core
input only has to supply the two log-vs-truncated tail estimates; the
`truncated ν` versus `truncated μ` term follows from weak continuity plus
compactness.
-/
theorem unitIntervalPositiveSetObjective_lowerSemicontinuous_of_compact_tailCore_auto_truncated
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ truncε δ : ℝ, ∃ K : Set ℝ,
          0 < truncε ∧
          0 < δ ∧
          δ ≤ (1 / ((n : ℝ) + 1)) / 3 ∧
          K ⊆ unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ
            (diagonalAtomSet μ) ∧
          IsCompact K ∧
          volume ({x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} \ K) ≤ (ε : ℝ≥0∞) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ K,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalLogPotential ν x| <
              (1 / ((n : ℝ) + 1)) / 3)) :
    LowerSemicontinuous unitIntervalPositiveSetObjective := by
  refine unitIntervalPositiveSetObjective_lowerSemicontinuous_of_compact_tailCore ?_
  intro μ n ε hε
  rcases hcore μ n ε hε with
    ⟨truncε, δ, K, htruncε_pos, hδ_pos, hδ_le, hKsub, hKcompact,
      hmeasure, hseq⟩
  refine ⟨truncε, δ, K, htruncε_pos, hδ_pos, hδ_le, hKsub,
    hKcompact, hmeasure, hseq, ?_⟩
  exact unitIntervalTruncatedPotential_eventually_close_on_compact
    μ htruncε_pos (by positivity : 0 < (1 / ((n : ℝ) + 1)) / 3)
    hKcompact

theorem unitIntervalPositiveSetObjective_exists_minimizer_of_compact_tailCore_auto_truncated
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ truncε δ : ℝ, ∃ K : Set ℝ,
          0 < truncε ∧
          0 < δ ∧
          δ ≤ (1 / ((n : ℝ) + 1)) / 3 ∧
          K ⊆ unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ
            (diagonalAtomSet μ) ∧
          IsCompact K ∧
          volume ({x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} \ K) ≤ (ε : ℝ≥0∞) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ K,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalLogPotential ν x| <
              (1 / ((n : ℝ) + 1)) / 3)) :
    ∃ μ : ProbabilityMeasure UnitInterval1038,
      ∀ ν : ProbabilityMeasure UnitInterval1038,
        unitIntervalPositiveSetObjective μ ≤
          unitIntervalPositiveSetObjective ν := by
  exact admissible_probability_lsc_exists_minimizer_ennreal
    unitIntervalPositiveSetObjective
    (unitIntervalPositiveSetObjective_lowerSemicontinuous_of_compact_tailCore_auto_truncated
      hcore)

/--
Compact-tail-core lower semicontinuity with both analytic estimate bridges
made explicit.  The compact core now supplies only:

* a compact off-diagonal tail core for the base measure;
* an eventual uniform tail-mass bound for nearby measures;
* an eventual no-diagonal-atom condition on that compact core.

The log-vs-truncated estimate and the truncated weak-continuity estimate are
then generated inside Lean.
-/
theorem unitIntervalPositiveSetObjective_lowerSemicontinuous_of_compact_tailCore_tailMass
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ truncε δ : ℝ, ∃ K : Set ℝ,
          0 < truncε ∧
          0 < δ ∧
          δ ≤ (1 / ((n : ℝ) + 1)) / 3 ∧
          K ⊆ unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ
            (diagonalAtomSet μ) ∧
          IsCompact K ∧
          volume ({x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} \ K) ≤ (ε : ℝ≥0∞) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ K,
            singularTailMass truncε ν x < ENNReal.ofReal δ) ∧
          (∀ᶠ (ν : ProbabilityMeasure UnitInterval1038) in nhds μ, ∀ x ∈ K,
            ∀ᵐ t : UnitInterval1038 ∂(ν : Measure UnitInterval1038),
              x ≠ (t : ℝ))) :
    LowerSemicontinuous unitIntervalPositiveSetObjective := by
  refine unitIntervalPositiveSetObjective_lowerSemicontinuous_of_compact_tailCore_auto_truncated ?_
  intro μ n ε hε
  rcases hcore μ n ε hε with
    ⟨truncε, δ, K, htruncε_pos, hδ_pos, hδ_le, hKsub, hKcompact,
      hmeasure, htail, hae_ne⟩
  refine ⟨truncε, δ, K, htruncε_pos, hδ_pos, hδ_le, hKsub,
    hKcompact, hmeasure, ?_⟩
  exact unitInterval_log_error_eventually_on_compact_of_tailMass_and_ae_ne_limit
    μ htruncε_pos hδ_pos hδ_le htail hae_ne

theorem unitIntervalPositiveSetObjective_exists_minimizer_of_compact_tailCore_tailMass
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ truncε δ : ℝ, ∃ K : Set ℝ,
          0 < truncε ∧
          0 < δ ∧
          δ ≤ (1 / ((n : ℝ) + 1)) / 3 ∧
          K ⊆ unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ
            (diagonalAtomSet μ) ∧
          IsCompact K ∧
          volume ({x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} \ K) ≤ (ε : ℝ≥0∞) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ K,
            singularTailMass truncε ν x < ENNReal.ofReal δ) ∧
          (∀ᶠ (ν : ProbabilityMeasure UnitInterval1038) in nhds μ, ∀ x ∈ K,
            ∀ᵐ t : UnitInterval1038 ∂(ν : Measure UnitInterval1038),
              x ≠ (t : ℝ))) :
    ∃ μ : ProbabilityMeasure UnitInterval1038,
      ∀ ν : ProbabilityMeasure UnitInterval1038,
        unitIntervalPositiveSetObjective μ ≤
          unitIntervalPositiveSetObjective ν := by
  exact admissible_probability_lsc_exists_minimizer_ennreal
    unitIntervalPositiveSetObjective
    (unitIntervalPositiveSetObjective_lowerSemicontinuous_of_compact_tailCore_tailMass
      hcore)

/--
Diagonal-safe compact-tail-core lower semicontinuity.  This removes the false
requirement that nearby weak perturbations have no atoms on the compact core:
if a nearby measure has an atom at a core point, that point is placed into the
zero-volume diagonal exceptional set; otherwise the tail-mass estimate gives
the log-vs-truncated error bound.
-/
theorem unitIntervalPositiveSetObjective_lowerSemicontinuous_of_compact_tailCore_tailMass_diagonal
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ truncε δ : ℝ, ∃ K : Set ℝ,
          0 < truncε ∧
          0 < δ ∧
          δ ≤ (1 / ((n : ℝ) + 1)) / 3 ∧
          K ⊆ unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ
            (diagonalAtomSet μ) ∧
          IsCompact K ∧
          volume ({x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} \ K) ≤ (ε : ℝ≥0∞) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ K,
            singularTailMass truncε ν x < ENNReal.ofReal δ)) :
    LowerSemicontinuous unitIntervalPositiveSetObjective := by
  refine unitIntervalPositiveSetObjective_lowerSemicontinuous_of_threshold_approx_with_diagonal_exception ?_
  intro μ n ε hε
  rcases hcore μ n ε hε with
    ⟨truncε, δ, K, htruncε_pos, hδ_pos, hδ_le, hKsub, hKcompact,
      hmeasure, htail⟩
  let S : Set ℝ :=
    {x : ℝ | 1 / ((n : ℝ) + 1) <
      unitIntervalLogPotential μ x}
  have hKmeasure :
      volume {x : ℝ | 1 / ((n : ℝ) + 1) <
          unitIntervalLogPotential μ x} ≤
        volume K + (ε : ℝ≥0∞) := by
    have hSsubset : S ⊆ K ∪ (S \ K) := by
      intro x hx
      by_cases hxK : x ∈ K
      · exact Or.inl hxK
      · exact Or.inr ⟨hx, hxK⟩
    have hmeasure_mono :
        volume S ≤ volume (K ∪ (S \ K)) :=
      measure_mono hSsubset
    have hunion :
        volume (K ∪ (S \ K)) ≤ volume K + volume (S \ K) :=
      measure_union_le _ _
    calc
      volume {x : ℝ | 1 / ((n : ℝ) + 1) <
          unitIntervalLogPotential μ x}
          = volume S := rfl
      _ ≤ volume (K ∪ (S \ K)) := hmeasure_mono
      _ ≤ volume K + volume (S \ K) := hunion
      _ ≤ volume K + (ε : ℝ≥0∞) := by
            exact add_le_add_right (by simpa [S] using hmeasure) (volume K)
  refine ⟨K, hKmeasure, ?_⟩
  · have hτ : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hKthreshold :
        K ⊆ {x : ℝ | 1 / ((n : ℝ) + 1) <
          unitIntervalLogPotential μ x} := by
      intro x hx
      exact unitInterval_tailCoreOffDiagonal_subset_threshold μ n truncε δ
        (diagonalAtomSet μ) (hKsub hx)
    have hlimit :
        ∀ x ∈ K,
          |unitIntervalTruncatedPotential truncε μ x -
            unitIntervalLogPotential μ x| <
            (1 / ((n : ℝ) + 1)) / 3 :=
      unitInterval_tailCoreOffDiagonal_limit_error_on_compact
        htruncε_pos hδ_pos hKsub hδ_le
    have hseq :
        ∀ᶠ ν in nhds μ, ∀ x ∈ K,
          x ∈ diagonalAtomSet ν ∨
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalLogPotential ν x| <
              (1 / ((n : ℝ) + 1)) / 3 :=
      unitInterval_diagonalAtom_or_log_error_eventually_on_compact_of_tailMass_limit
        μ htruncε_pos hδ_pos hδ_le htail
    have htrunc :
        ∀ᶠ ν in nhds μ, ∀ x ∈ K,
          |unitIntervalTruncatedPotential truncε ν x -
            unitIntervalTruncatedPotential truncε μ x| <
            (1 / ((n : ℝ) + 1)) / 3 :=
      unitIntervalTruncatedPotential_eventually_close_on_compact
        μ htruncε_pos (by positivity : 0 < (1 / ((n : ℝ) + 1)) / 3)
        hKcompact
    exact (threshold_approx_of_three_error_core_with_exception
      (unitIntervalLogPotential μ)
      (fun ν : ProbabilityMeasure UnitInterval1038 =>
        unitIntervalLogPotential ν)
      (unitIntervalTruncatedPotential truncε μ)
      (fun ν : ProbabilityMeasure UnitInterval1038 =>
        unitIntervalTruncatedPotential truncε ν)
      (fun ν : ProbabilityMeasure UnitInterval1038 => diagonalAtomSet ν)
      hτ K hKmeasure hKthreshold hlimit hseq htrunc).2

theorem unitIntervalPositiveSetObjective_exists_minimizer_of_compact_tailCore_tailMass_diagonal
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ truncε δ : ℝ, ∃ K : Set ℝ,
          0 < truncε ∧
          0 < δ ∧
          δ ≤ (1 / ((n : ℝ) + 1)) / 3 ∧
          K ⊆ unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ
            (diagonalAtomSet μ) ∧
          IsCompact K ∧
          volume ({x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} \ K) ≤ (ε : ℝ≥0∞) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ K,
            singularTailMass truncε ν x < ENNReal.ofReal δ)) :
    ∃ μ : ProbabilityMeasure UnitInterval1038,
      ∀ ν : ProbabilityMeasure UnitInterval1038,
        unitIntervalPositiveSetObjective μ ≤
          unitIntervalPositiveSetObjective ν := by
  exact admissible_probability_lsc_exists_minimizer_ennreal
    unitIntervalPositiveSetObjective
    (unitIntervalPositiveSetObjective_lowerSemicontinuous_of_compact_tailCore_tailMass_diagonal
      hcore)

/--
Tail-mass bad-set bridge for objective lower semicontinuity.  The compact
off-diagonal core is constructed here from the existing finite-window,
measurability, null-diagonal, and inner-regularity lemmas; it is not an external
witness.  The remaining analytic input is eventual tail-mass stability on every
compact subset of the fixed off-diagonal tail core.
-/
theorem unitIntervalPositiveSetObjective_lowerSemicontinuous_of_tailMass_badSet_control
    (hregular : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ truncε : ℝ, ∃ ηBad ηCore : ℝ≥0∞,
          0 < truncε ∧
          ηCore ≠ 0 ∧
          volume {x : ℝ |
              ENNReal.ofReal ((1 / ((n : ℝ) + 1)) / 3) ≤
                singularTailMass truncε μ x} ≤ ηBad ∧
          ηBad + ηCore ≤ (ε : ℝ≥0∞) ∧
          (∀ K : Set ℝ,
            K ⊆ unitIntervalThresholdTailCoreOffDiagonal μ n truncε
              ((1 / ((n : ℝ) + 1)) / 3) (diagonalAtomSet μ) →
            IsCompact K →
            ∀ᶠ ν in nhds μ, ∀ x ∈ K,
              singularTailMass truncε ν x <
                ENNReal.ofReal ((1 / ((n : ℝ) + 1)) / 3))) :
    LowerSemicontinuous unitIntervalPositiveSetObjective := by
  refine unitIntervalPositiveSetObjective_lowerSemicontinuous_of_compact_tailCore_tailMass_diagonal ?_
  intro μ n ε hε
  let δ : ℝ := (1 / ((n : ℝ) + 1)) / 3
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  have hδ_le : δ ≤ (1 / ((n : ℝ) + 1)) / 3 := by
    simp [δ]
  rcases hregular μ n ε hε with
    ⟨truncε, ηBad, ηCore, htruncε_pos, hηCore, hbad, hbudget, htail⟩
  have hbadδ :
      volume {x : ℝ | ENNReal.ofReal δ ≤ singularTailMass truncε μ x} ≤
        ηBad := by
    simpa [δ] using hbad
  rcases unitIntervalThresholdTailCoreOffDiagonal_exists_compact_core
      μ n truncε δ hηCore hbadδ hbudget with
    ⟨K, hKsub, hKcompact, hmeasure⟩
  have htailK :
      ∀ᶠ ν in nhds μ, ∀ x ∈ K,
        singularTailMass truncε ν x < ENNReal.ofReal δ := by
    simpa [δ] using
      htail K (by simpa [δ] using hKsub) hKcompact
  exact ⟨truncε, δ, K, htruncε_pos, hδ_pos, hδ_le, hKsub,
    hKcompact, hmeasure, htailK⟩

/--
Minimizer-existence consequence of the tail-mass bad-set bridge.  This entry
point no longer asks callers to provide compact cores; it only consumes the
bad-set budget and compact-subcore tail-mass stability used by the preceding
lower-semicontinuity theorem.
-/
theorem unitIntervalPositiveSetObjective_exists_minimizer_of_tailMass_badSet_control
    (hregular : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ truncε : ℝ, ∃ ηBad ηCore : ℝ≥0∞,
          0 < truncε ∧
          ηCore ≠ 0 ∧
          volume {x : ℝ |
              ENNReal.ofReal ((1 / ((n : ℝ) + 1)) / 3) ≤
                singularTailMass truncε μ x} ≤ ηBad ∧
          ηBad + ηCore ≤ (ε : ℝ≥0∞) ∧
          (∀ K : Set ℝ,
            K ⊆ unitIntervalThresholdTailCoreOffDiagonal μ n truncε
              ((1 / ((n : ℝ) + 1)) / 3) (diagonalAtomSet μ) →
            IsCompact K →
            ∀ᶠ ν in nhds μ, ∀ x ∈ K,
              singularTailMass truncε ν x <
                ENNReal.ofReal ((1 / ((n : ℝ) + 1)) / 3))) :
    ∃ μ : ProbabilityMeasure UnitInterval1038,
      ∀ ν : ProbabilityMeasure UnitInterval1038,
        unitIntervalPositiveSetObjective μ ≤
          unitIntervalPositiveSetObjective ν := by
  exact admissible_probability_lsc_exists_minimizer_ennreal
    unitIntervalPositiveSetObjective
    (unitIntervalPositiveSetObjective_lowerSemicontinuous_of_tailMass_badSet_control
      hregular)

/--
Tail-mass-stability bridge for objective lower semicontinuity.

Compared with `unitIntervalPositiveSetObjective_lowerSemicontinuous_of_tailMass_badSet_control`,
this theorem proves the bad-tail-set budget internally from the already
formalized singular-tail estimate
`singularTail_closed_badSet_volume_le_of_two_mul_real_threshold` and the scale
choice lemma `exists_tailScale_for_target`.  Thus callers no longer supply the
bad-set estimate, the budget split, or a compact core.

The only remaining analytic input is the public-facing stability estimate:
for every base measure, level `n`, positive truncation scale, and compact
subset of the fixed off-diagonal tail core, nearby measures have uniformly
small singular tail mass on that compact set.
-/
theorem unitIntervalPositiveSetObjective_lowerSemicontinuous_of_tailMass_stability
    (hstability : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∀ truncε : ℝ, 0 < truncε →
          (∀ K : Set ℝ,
            K ⊆ unitIntervalThresholdTailCoreOffDiagonal μ n truncε
              ((1 / ((n : ℝ) + 1)) / 3) (diagonalAtomSet μ) →
            IsCompact K →
            ∀ᶠ ν in nhds μ, ∀ x ∈ K,
              singularTailMass truncε ν x <
                ENNReal.ofReal ((1 / ((n : ℝ) + 1)) / 3))) :
    LowerSemicontinuous unitIntervalPositiveSetObjective := by
  refine unitIntervalPositiveSetObjective_lowerSemicontinuous_of_tailMass_badSet_control ?_
  intro μ n ε hε
  let δ : ℝ := (1 / ((n : ℝ) + 1)) / 3
  let ηPart : NNReal := ε / 2
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  have hηPart_pos : 0 < ηPart := by
    dsimp [ηPart]
    positivity
  rcases exists_tailScale_for_target (δ := δ) (η := ηPart)
      hδ_pos hηPart_pos with
    ⟨truncε, htruncε_pos, hscale⟩
  refine ⟨truncε, (ηPart : ℝ≥0∞), (ηPart : ℝ≥0∞),
    htruncε_pos, ?_, ?_, ?_, ?_⟩
  · exact ne_of_gt (ENNReal.coe_pos.mpr hηPart_pos)
  · simpa [δ] using
      singularTail_closed_badSet_volume_le_of_two_mul_real_threshold
        truncε μ hδ_pos hscale
  · have hbudget_eq :
        (ηPart : ℝ≥0∞) + (ηPart : ℝ≥0∞) = (ε : ℝ≥0∞) := by
      rw [← ENNReal.coe_add]
      congr 1
      exact add_halves ε
    exact le_of_eq hbudget_eq
  · intro K hKsub hKcompact
    exact hstability μ n ε hε truncε htruncε_pos K hKsub hKcompact

/--
Minimizer-existence consequence of the tail-mass-stability bridge.

The singular-tail two-mul estimate now supplies the bad-tail-set budget and
budget split in Lean.  The remaining analytic estimate is exactly compact
off-diagonal tail-mass stability for nearby measures at any positive
truncation scale selected by the theorem.
-/
theorem unitIntervalPositiveSetObjective_exists_minimizer_of_tailMass_stability
    (hstability : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∀ truncε : ℝ, 0 < truncε →
          (∀ K : Set ℝ,
            K ⊆ unitIntervalThresholdTailCoreOffDiagonal μ n truncε
              ((1 / ((n : ℝ) + 1)) / 3) (diagonalAtomSet μ) →
            IsCompact K →
            ∀ᶠ ν in nhds μ, ∀ x ∈ K,
              singularTailMass truncε ν x <
                ENNReal.ofReal ((1 / ((n : ℝ) + 1)) / 3))) :
    ∃ μ : ProbabilityMeasure UnitInterval1038,
      ∀ ν : ProbabilityMeasure UnitInterval1038,
        unitIntervalPositiveSetObjective μ ≤
          unitIntervalPositiveSetObjective ν := by
  exact admissible_probability_lsc_exists_minimizer_ennreal
    unitIntervalPositiveSetObjective
    (unitIntervalPositiveSetObjective_lowerSemicontinuous_of_tailMass_stability
      hstability)

/--
One-sided compact-tail-core lower semicontinuity.  This is the sharper form of
the threshold argument: on the varying-measure side we do not need absolute
tail-error control.  It is enough that, away from diagonal atoms,
`truncated potential ≤ log potential`.
-/
theorem unitIntervalPositiveSetObjective_lowerSemicontinuous_of_compact_tailCore_oneSided
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ truncε δ : ℝ, ∃ K : Set ℝ,
          0 < truncε ∧
          0 < δ ∧
          δ ≤ (1 / ((n : ℝ) + 1)) / 3 ∧
          K ⊆ unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ
            (diagonalAtomSet μ) ∧
          IsCompact K ∧
          volume ({x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} \ K) ≤ (ε : ℝ≥0∞) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ K,
            x ∉ diagonalAtomSet ν →
              Integrable
                (fun t : UnitInterval1038 => Real.log (1 / |x - (t : ℝ)|))
                (ν : Measure UnitInterval1038))) :
    LowerSemicontinuous unitIntervalPositiveSetObjective := by
  refine unitIntervalPositiveSetObjective_lowerSemicontinuous_of_threshold_approx_with_diagonal_exception ?_
  intro μ n ε hε
  rcases hcore μ n ε hε with
    ⟨truncε, δ, K, htruncε_pos, hδ_pos, hδ_le, hKsub, hKcompact,
      hmeasure, hlog_int⟩
  let S : Set ℝ :=
    {x : ℝ | 1 / ((n : ℝ) + 1) <
      unitIntervalLogPotential μ x}
  have hKmeasure :
      volume {x : ℝ | 1 / ((n : ℝ) + 1) <
          unitIntervalLogPotential μ x} ≤
        volume K + (ε : ℝ≥0∞) := by
    have hSsubset : S ⊆ K ∪ (S \ K) := by
      intro x hx
      by_cases hxK : x ∈ K
      · exact Or.inl hxK
      · exact Or.inr ⟨hx, hxK⟩
    have hmeasure_mono :
        volume S ≤ volume (K ∪ (S \ K)) :=
      measure_mono hSsubset
    have hunion :
        volume (K ∪ (S \ K)) ≤ volume K + volume (S \ K) :=
      measure_union_le _ _
    calc
      volume {x : ℝ | 1 / ((n : ℝ) + 1) <
          unitIntervalLogPotential μ x}
          = volume S := rfl
      _ ≤ volume (K ∪ (S \ K)) := hmeasure_mono
      _ ≤ volume K + volume (S \ K) := hunion
      _ ≤ volume K + (ε : ℝ≥0∞) := by
            exact add_le_add_right (by simpa [S] using hmeasure) (volume K)
  refine ⟨K, hKmeasure, ?_⟩
  have hτ : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have hKthreshold :
      K ⊆ {x : ℝ | 1 / ((n : ℝ) + 1) <
        unitIntervalLogPotential μ x} := by
    intro x hx
    exact unitInterval_tailCoreOffDiagonal_subset_threshold μ n truncε δ
      (diagonalAtomSet μ) (hKsub hx)
  have hlimit :
      ∀ x ∈ K,
        |unitIntervalTruncatedPotential truncε μ x -
          unitIntervalLogPotential μ x| <
          (1 / ((n : ℝ) + 1)) / 3 :=
    unitInterval_tailCoreOffDiagonal_limit_error_on_compact
      htruncε_pos hδ_pos hKsub hδ_le
  have hseqLower :
      ∀ᶠ ν in nhds μ, ∀ x ∈ K,
        x ∈ diagonalAtomSet ν ∨
          unitIntervalTruncatedPotential truncε ν x ≤
            unitIntervalLogPotential ν x :=
    unitInterval_diagonalAtom_or_truncatedPotential_le_logPotential_eventually_on_compact
      μ htruncε_pos hlog_int
  have htrunc :
      ∀ᶠ ν in nhds μ, ∀ x ∈ K,
        |unitIntervalTruncatedPotential truncε ν x -
          unitIntervalTruncatedPotential truncε μ x| <
          (1 / ((n : ℝ) + 1)) / 3 :=
    unitIntervalTruncatedPotential_eventually_close_on_compact
      μ htruncε_pos (by positivity : 0 < (1 / ((n : ℝ) + 1)) / 3)
      hKcompact
  exact (threshold_approx_of_limit_trunc_and_seq_lower_core_with_exception
    (unitIntervalLogPotential μ)
    (fun ν : ProbabilityMeasure UnitInterval1038 =>
      unitIntervalLogPotential ν)
    (unitIntervalTruncatedPotential truncε μ)
    (fun ν : ProbabilityMeasure UnitInterval1038 =>
      unitIntervalTruncatedPotential truncε ν)
    (fun ν : ProbabilityMeasure UnitInterval1038 => diagonalAtomSet ν)
    hτ K hKmeasure hKthreshold hlimit hseqLower htrunc).2

theorem unitIntervalPositiveSetObjective_exists_minimizer_of_compact_tailCore_oneSided
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ truncε δ : ℝ, ∃ K : Set ℝ,
          0 < truncε ∧
          0 < δ ∧
          δ ≤ (1 / ((n : ℝ) + 1)) / 3 ∧
          K ⊆ unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ
            (diagonalAtomSet μ) ∧
          IsCompact K ∧
          volume ({x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} \ K) ≤ (ε : ℝ≥0∞) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ K,
            x ∉ diagonalAtomSet ν →
              Integrable
                (fun t : UnitInterval1038 => Real.log (1 / |x - (t : ℝ)|))
                (ν : Measure UnitInterval1038))) :
    ∃ μ : ProbabilityMeasure UnitInterval1038,
      ∀ ν : ProbabilityMeasure UnitInterval1038,
        unitIntervalPositiveSetObjective μ ≤
          unitIntervalPositiveSetObjective ν := by
  exact admissible_probability_lsc_exists_minimizer_ennreal
    unitIntervalPositiveSetObjective
    (unitIntervalPositiveSetObjective_lowerSemicontinuous_of_compact_tailCore_oneSided
      hcore)

theorem unitIntervalPositiveSetObjective_exists_minimizer_of_tailCore_ae_ne
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ η : NNReal, 0 < η →
        ∀ truncε : ℝ,
          0 < truncε →
          ENNReal.ofReal (2 * truncε) /
              (ENNReal.ofReal ((1 / ((n : ℝ) + 1)) / 3) / 2) ≤
            (η : ℝ≥0∞) →
          (∀ x ∈ unitIntervalThresholdTailCore μ n truncε
              ((1 / ((n : ℝ) + 1)) / 3),
            ∀ᵐ t : UnitInterval1038 ∂(μ : Measure UnitInterval1038),
              x ≠ (t : ℝ)) ∧
          (∀ x ∈ unitIntervalThresholdTailCore μ n truncε
              ((1 / ((n : ℝ) + 1)) / 3),
            Integrable
              (fun t : UnitInterval1038 => truncatedLogKernel truncε x (t : ℝ))
              (μ : Measure UnitInterval1038)) ∧
          (∀ x ∈ unitIntervalThresholdTailCore μ n truncε
              ((1 / ((n : ℝ) + 1)) / 3),
            Integrable
              (fun t : UnitInterval1038 => Real.log (1 / |x - (t : ℝ)|))
              (μ : Measure UnitInterval1038)) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ unitIntervalThresholdTailCore μ n truncε
              ((1 / ((n : ℝ) + 1)) / 3),
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalLogPotential ν x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ unitIntervalThresholdTailCore μ n truncε
              ((1 / ((n : ℝ) + 1)) / 3),
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalTruncatedPotential truncε μ x| <
              (1 / ((n : ℝ) + 1)) / 3)) :
    ∃ μ : ProbabilityMeasure UnitInterval1038,
      ∀ ν : ProbabilityMeasure UnitInterval1038,
        unitIntervalPositiveSetObjective μ ≤
          unitIntervalPositiveSetObjective ν := by
  refine unitIntervalPositiveSetObjective_exists_minimizer_of_tailCore_scale_choice ?_
  intro μ n η hη truncε htruncε_pos hscale
  rcases hcore μ n η hη truncε htruncε_pos hscale with
    ⟨hae_ne, htrunc_int, hlog_int, hseq, htrunc⟩
  refine ⟨?_, hseq, htrunc⟩
  exact unitInterval_tailCore_error_bound_of_ae_ne htruncε_pos
    hae_ne htrunc_int hlog_int

theorem unitIntervalPositiveSetObjective_exists_minimizer_of_tailCore_diagonalAtoms
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ η : NNReal, 0 < η →
        ∀ truncε : ℝ,
          0 < truncε →
          ENNReal.ofReal (2 * truncε) /
              (ENNReal.ofReal ((1 / ((n : ℝ) + 1)) / 3) / 2) ≤
            (η : ℝ≥0∞) →
          (∀ x ∈ unitIntervalThresholdTailCoreOffDiagonal μ n truncε
              ((1 / ((n : ℝ) + 1)) / 3) (diagonalAtomSet μ),
            Integrable
              (fun t : UnitInterval1038 => truncatedLogKernel truncε x (t : ℝ))
              (μ : Measure UnitInterval1038)) ∧
          (∀ x ∈ unitIntervalThresholdTailCoreOffDiagonal μ n truncε
              ((1 / ((n : ℝ) + 1)) / 3) (diagonalAtomSet μ),
            Integrable
              (fun t : UnitInterval1038 => Real.log (1 / |x - (t : ℝ)|))
              (μ : Measure UnitInterval1038)) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈
              unitIntervalThresholdTailCoreOffDiagonal μ n truncε
                ((1 / ((n : ℝ) + 1)) / 3) (diagonalAtomSet μ),
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalLogPotential ν x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈
              unitIntervalThresholdTailCoreOffDiagonal μ n truncε
                ((1 / ((n : ℝ) + 1)) / 3) (diagonalAtomSet μ),
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalTruncatedPotential truncε μ x| <
              (1 / ((n : ℝ) + 1)) / 3)) :
    ∃ μ : ProbabilityMeasure UnitInterval1038,
      ∀ ν : ProbabilityMeasure UnitInterval1038,
        unitIntervalPositiveSetObjective μ ≤
          unitIntervalPositiveSetObjective ν := by
  refine unitIntervalPositiveSetObjective_exists_minimizer_of_tailCore_offDiagonal ?_
  intro μ n η hη
  let δ : ℝ := (1 / ((n : ℝ) + 1)) / 3
  rcases exists_tailScale_for_target (δ := δ) (η := η)
      (by positivity : 0 < δ) hη with
    ⟨truncε, htruncε_pos, hscale⟩
  rcases hcore μ n η hη truncε htruncε_pos hscale with
    ⟨htrunc_int, hlog_int, hseq, htrunc⟩
  refine ⟨truncε, δ, diagonalAtomSet μ, ?_, ?_, ?_, ?_, hseq, htrunc, ?_⟩
  · positivity
  · exact diagonalAtomSet_volume_zero μ
  · exact singularTail_closed_badSet_volume_le_of_two_mul_real_threshold
      truncε μ (by positivity : 0 < δ) hscale
  · exact unitInterval_tailCoreOffDiagonal_error_bound_of_integrable
      htruncε_pos htrunc_int hlog_int
  · exact le_rfl

theorem unitIntervalPositiveSetObjective_exists_minimizer_of_tailCore_diagonalAtoms_logIntegrable
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ η : NNReal, 0 < η →
        ∀ truncε : ℝ,
          0 < truncε →
          ENNReal.ofReal (2 * truncε) /
              (ENNReal.ofReal ((1 / ((n : ℝ) + 1)) / 3) / 2) ≤
            (η : ℝ≥0∞) →
          (∀ x ∈ unitIntervalThresholdTailCoreOffDiagonal μ n truncε
              ((1 / ((n : ℝ) + 1)) / 3) (diagonalAtomSet μ),
            Integrable
              (fun t : UnitInterval1038 => Real.log (1 / |x - (t : ℝ)|))
              (μ : Measure UnitInterval1038)) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈
              unitIntervalThresholdTailCoreOffDiagonal μ n truncε
                ((1 / ((n : ℝ) + 1)) / 3) (diagonalAtomSet μ),
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalLogPotential ν x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈
              unitIntervalThresholdTailCoreOffDiagonal μ n truncε
                ((1 / ((n : ℝ) + 1)) / 3) (diagonalAtomSet μ),
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalTruncatedPotential truncε μ x| <
              (1 / ((n : ℝ) + 1)) / 3)) :
    ∃ μ : ProbabilityMeasure UnitInterval1038,
      ∀ ν : ProbabilityMeasure UnitInterval1038,
        unitIntervalPositiveSetObjective μ ≤
          unitIntervalPositiveSetObjective ν := by
  refine unitIntervalPositiveSetObjective_exists_minimizer_of_tailCore_diagonalAtoms ?_
  intro μ n η hη truncε htruncε_pos hscale
  rcases hcore μ n η hη truncε htruncε_pos hscale with
    ⟨hlog_int, hseq, htrunc⟩
  exact ⟨fun x _hx => truncatedLogKernel_integrable μ htruncε_pos,
    hlog_int, hseq, htrunc⟩

theorem unitIntervalPositiveSetObjective_exists_minimizer_of_tailCore_diagonalAtoms_autoIntegrable
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ η : NNReal, 0 < η →
        ∀ truncε : ℝ,
          0 < truncε →
          ENNReal.ofReal (2 * truncε) /
              (ENNReal.ofReal ((1 / ((n : ℝ) + 1)) / 3) / 2) ≤
            (η : ℝ≥0∞) →
          (∀ᶠ ν in nhds μ, ∀ x ∈
              unitIntervalThresholdTailCoreOffDiagonal μ n truncε
                ((1 / ((n : ℝ) + 1)) / 3) (diagonalAtomSet μ),
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalLogPotential ν x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈
              unitIntervalThresholdTailCoreOffDiagonal μ n truncε
                ((1 / ((n : ℝ) + 1)) / 3) (diagonalAtomSet μ),
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalTruncatedPotential truncε μ x| <
              (1 / ((n : ℝ) + 1)) / 3)) :
    ∃ μ : ProbabilityMeasure UnitInterval1038,
      ∀ ν : ProbabilityMeasure UnitInterval1038,
        unitIntervalPositiveSetObjective μ ≤
          unitIntervalPositiveSetObjective ν := by
  refine unitIntervalPositiveSetObjective_exists_minimizer_of_tailCore_diagonalAtoms_logIntegrable ?_
  intro μ n η hη truncε htruncε_pos hscale
  rcases hcore μ n η hη truncε htruncε_pos hscale with
    ⟨hseq, htrunc⟩
  refine ⟨?_, hseq, htrunc⟩
  intro x hx
  have htailFinite :
      singularTailMass truncε μ x < ∞ :=
    lt_trans hx.1.2 ENNReal.ofReal_lt_top
  exact unitInterval_logKernel_integrable_of_tailMass_lt_top
    htruncε_pos (ae_ne_of_notMem_diagonalAtomSet hx.2) htailFinite

theorem unitInterval_threshold_approx_of_finite_tailCore
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ η : NNReal, 0 < η →
        ∃ truncε δ : ℝ, ∃ s : Finset ℝ,
          0 < truncε ∧
          0 < δ ∧
          volume ({x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} \ (s : Set ℝ)) ≤
            (η : ℝ≥0∞) ∧
          (∀ x ∈ s,
            x ∈ unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ
              (diagonalAtomSet μ)) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ s,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalLogPotential ν x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          δ ≤ (1 / ((n : ℝ) + 1)) / 3) :
    ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ η : NNReal, 0 < η →
        ∃ A : Set ℝ,
          volume {x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} ≤
            volume A + (η : ℝ≥0∞) ∧
          ∀ᶠ ν in nhds μ,
            A ⊆ {x : ℝ | 0 < unitIntervalLogPotential ν x} := by
  refine unitInterval_threshold_approx_of_badSet_core ?_
  intro μ n η hη
  rcases hcore μ n η hη with
    ⟨truncε, δ, s, htruncε_pos, hδ, hbad, hs_core, hseq, hδ_le⟩
  refine ⟨truncε, (s : Set ℝ), ?_, hbad, ?_, hseq, ?_⟩
  · intro x hx
    exact unitInterval_tailCoreOffDiagonal_subset_threshold μ n truncε δ
      (diagonalAtomSet μ) (hs_core x hx)
  · intro x hx
    have hxcore :
        x ∈ unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ
          (diagonalAtomSet μ) := hs_core x hx
    have htail : singularTailMass truncε μ x < ENNReal.ofReal δ := hxcore.1.2
    have htailFinite : singularTailMass truncε μ x < ∞ :=
      lt_trans htail ENNReal.ofReal_lt_top
    have hlog_int :
        Integrable
          (fun t : UnitInterval1038 => Real.log (1 / |x - (t : ℝ)|))
          (μ : Measure UnitInterval1038) :=
      unitInterval_logKernel_integrable_of_tailMass_lt_top
        htruncε_pos (ae_ne_of_notMem_diagonalAtomSet hxcore.2) htailFinite
    have herror :
        ENNReal.ofReal
          |unitIntervalTruncatedPotential truncε μ x -
            unitIntervalLogPotential μ x| ≤ singularTailMass truncε μ x :=
      unitIntervalTruncatedPotential_error_le_singularTailMass_of_ae_ne
        htruncε_pos (ae_ne_of_notMem_diagonalAtomSet hxcore.2)
        (truncatedLogKernel_integrable μ htruncε_pos) hlog_int
    have hlt :=
      truncated_potential_error_lt_of_tail_bound hδ herror htail
    exact lt_of_lt_of_le hlt hδ_le
  · exact unitIntervalTruncatedPotential_eventually_close_on_finset
      μ s htruncε_pos (by positivity)

theorem unitIntervalPositiveSetObjective_lowerSemicontinuous_of_finite_tailCore
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ η : NNReal, 0 < η →
        ∃ truncε δ : ℝ, ∃ s : Finset ℝ,
          0 < truncε ∧
          0 < δ ∧
          volume ({x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} \ (s : Set ℝ)) ≤
            (η : ℝ≥0∞) ∧
          (∀ x ∈ s,
            x ∈ unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ
              (diagonalAtomSet μ)) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ s,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalLogPotential ν x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          δ ≤ (1 / ((n : ℝ) + 1)) / 3) :
    LowerSemicontinuous unitIntervalPositiveSetObjective := by
  exact unitIntervalPositiveSetObjective_lowerSemicontinuous_of_threshold_approx
    (unitInterval_threshold_approx_of_finite_tailCore hcore)

theorem unitIntervalPositiveSetObjective_exists_minimizer_of_finite_tailCore
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ η : NNReal, 0 < η →
        ∃ truncε δ : ℝ, ∃ s : Finset ℝ,
          0 < truncε ∧
          0 < δ ∧
          volume ({x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} \ (s : Set ℝ)) ≤
            (η : ℝ≥0∞) ∧
          (∀ x ∈ s,
            x ∈ unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ
              (diagonalAtomSet μ)) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ s,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalLogPotential ν x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          δ ≤ (1 / ((n : ℝ) + 1)) / 3) :
    ∃ μ : ProbabilityMeasure UnitInterval1038,
      ∀ ν : ProbabilityMeasure UnitInterval1038,
        unitIntervalPositiveSetObjective μ ≤
          unitIntervalPositiveSetObjective ν := by
  exact unitIntervalPositiveSetObjective_exists_minimizer_of_threshold_approx
    (unitInterval_threshold_approx_of_finite_tailCore hcore)

lemma probability_measure_integral_boundedContinuousFunction_tendsto
    {Ω ι : Type*} {L : Filter ι}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    {μ : ProbabilityMeasure Ω} {μs : ι → ProbabilityMeasure Ω}
    (hμs : Filter.Tendsto μs L (nhds μ))
    (f : BoundedContinuousFunction Ω ℝ) :
    Filter.Tendsto
      (fun i => ∫ x : Ω, f x ∂(μs i : Measure Ω)) L
      (nhds (∫ x : Ω, f x ∂(μ : Measure Ω))) := by
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμs) f

structure MinimizationProblem (α : Type*) [TopologicalSpace α] where
  Admissible : α → Prop
  objective : α → ℝ
  nonempty_admissible : ∃ a : α, Admissible a
  compact_admissible : IsCompact {a : α | Admissible a}
  lowerSemicontinuous_objective :
    LowerSemicontinuousOn objective {a : α | Admissible a}

theorem MinimizationProblem.exists_minimizer
    {α : Type*} [TopologicalSpace α] (P : MinimizationProblem α) :
    ∃ a : α, P.Admissible a ∧
      ∀ b : α, P.Admissible b → P.objective a ≤ P.objective b := by
  exact compact_predicate_lsc_exists_minimizer P.Admissible P.objective
    P.nonempty_admissible P.compact_admissible
    P.lowerSemicontinuous_objective

def IsMinimizer
    {α : Type*} [TopologicalSpace α] (P : MinimizationProblem α) (a : α) : Prop :=
  P.Admissible a ∧ ∀ b : α, P.Admissible b → P.objective a ≤ P.objective b

theorem MinimizationProblem.exists_isMinimizer
    {α : Type*} [TopologicalSpace α] (P : MinimizationProblem α) :
    ∃ a : α, IsMinimizer P a := by
  simpa [IsMinimizer] using P.exists_minimizer

structure MinimizationProblemENNReal (α : Type*) [TopologicalSpace α] where
  Admissible : α → Prop
  objective : α → ℝ≥0∞
  nonempty_admissible : ∃ a : α, Admissible a
  compact_admissible : IsCompact {a : α | Admissible a}
  lowerSemicontinuous_objective :
    LowerSemicontinuousOn objective {a : α | Admissible a}

def IsMinimizerENNReal
    {α : Type*} [TopologicalSpace α]
    (P : MinimizationProblemENNReal α) (a : α) : Prop :=
  P.Admissible a ∧ ∀ b : α, P.Admissible b → P.objective a ≤ P.objective b

theorem MinimizationProblemENNReal.exists_isMinimizer
    {α : Type*} [TopologicalSpace α] (P : MinimizationProblemENNReal α) :
    ∃ a : α, IsMinimizerENNReal P a := by
  rcases compact_nonempty_lsc_exists_minimizer_ennreal
      {a : α | P.Admissible a} P.objective
      P.nonempty_admissible P.compact_admissible
      P.lowerSemicontinuous_objective with
    ⟨a, ha, hmin⟩
  exact ⟨a, ha, hmin⟩

/-!
## Variance-selector layer

After Lemma 3.1 gives at least one minimizer, Tao chooses a minimizer with
minimal variance.  The next structure packages the exact hypotheses needed for
that second compactness step, and the theorem proves the selector.
-/

structure SecondarySelectorProblem
    (α : Type*) [TopologicalSpace α] where
  Primary : MinimizationProblem α
  secondaryObjective : α → ℝ
  minimizer_set_compact :
    IsCompact {a : α | IsMinimizer Primary a}
  secondary_lsc_on_minimizers :
    LowerSemicontinuousOn secondaryObjective {a : α | IsMinimizer Primary a}

def IsSecondaryMinimizingPrimaryMinimizer
    {α : Type*} [TopologicalSpace α]
    (P : SecondarySelectorProblem α) (a : α) : Prop :=
  IsMinimizer P.Primary a ∧
    ∀ b : α, IsMinimizer P.Primary b →
      P.secondaryObjective a ≤ P.secondaryObjective b

theorem SecondarySelectorProblem.exists_secondary_minimizer
    {α : Type*} [TopologicalSpace α] (P : SecondarySelectorProblem α) :
    ∃ a : α, IsSecondaryMinimizingPrimaryMinimizer P a := by
  have hne : ∃ a : α, IsMinimizer P.Primary a :=
    P.Primary.exists_isMinimizer
  rcases compact_predicate_lsc_exists_minimizer
      (fun a : α => IsMinimizer P.Primary a)
      P.secondaryObjective hne P.minimizer_set_compact
      P.secondary_lsc_on_minimizers with
    ⟨a, hmin, hsecondary⟩
  exact ⟨a, hmin, hsecondary⟩

structure SecondarySelectorProblemENNReal
    (α : Type*) [TopologicalSpace α] where
  Primary : MinimizationProblemENNReal α
  secondaryObjective : α → ℝ
  minimizer_set_compact :
    IsCompact {a : α | IsMinimizerENNReal Primary a}
  secondary_lsc_on_minimizers :
    LowerSemicontinuousOn secondaryObjective
      {a : α | IsMinimizerENNReal Primary a}

def IsSecondaryMinimizingPrimaryMinimizerENNReal
    {α : Type*} [TopologicalSpace α]
    (P : SecondarySelectorProblemENNReal α) (a : α) : Prop :=
  IsMinimizerENNReal P.Primary a ∧
    ∀ b : α, IsMinimizerENNReal P.Primary b →
      P.secondaryObjective a ≤ P.secondaryObjective b

theorem SecondarySelectorProblemENNReal.exists_secondary_minimizer
    {α : Type*} [TopologicalSpace α] (P : SecondarySelectorProblemENNReal α) :
    ∃ a : α, IsSecondaryMinimizingPrimaryMinimizerENNReal P a := by
  have hne : ∃ a : α, IsMinimizerENNReal P.Primary a :=
    P.Primary.exists_isMinimizer
  rcases compact_predicate_lsc_exists_minimizer
      (fun a : α => IsMinimizerENNReal P.Primary a)
      P.secondaryObjective hne P.minimizer_set_compact
      P.secondary_lsc_on_minimizers with
    ⟨a, hmin, hsecondary⟩
  exact ⟨a, hmin, hsecondary⟩

/--
Selector-problem admissibility bridge for the replacement probability when the
primary admissible class is the concrete full probability class.
-/
theorem componentReplacementProbability_primary_admissible_of_univ
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    (hmass_unit :
      componentReplacementMeasure C (Icc (-1 : ℝ) 1) = 1)
    {P : SecondarySelectorProblemENNReal (ProbabilityMeasure UnitInterval1038)}
    (hAdmissible : P.Primary.Admissible = fun _ => True) :
    P.Primary.Admissible (componentReplacementProbability C hmass_unit) := by
  simpa [hAdmissible]

/-!
## Replacement/variance contradiction layer

This abstracts Tao's barycenter-replacement move.  If a replacement stays
admissible, does not increase the primary objective, and strictly decreases the
secondary objective, then it contradicts the choice of a secondary-minimizing
primary minimizer.
-/

lemma replacement_is_primary_minimizer
    {α : Type*} [TopologicalSpace α]
    {P : MinimizationProblem α} {a b : α}
    (ha : IsMinimizer P a)
    (hb_adm : P.Admissible b)
    (hb_primary : P.objective b ≤ P.objective a) :
    IsMinimizer P b := by
  constructor
  · exact hb_adm
  · intro c hc
    exact le_trans hb_primary (ha.2 c hc)

lemma no_strict_secondary_decreasing_replacement
    {α : Type*} [TopologicalSpace α]
    {P : SecondarySelectorProblem α} {a b : α}
    (ha : IsSecondaryMinimizingPrimaryMinimizer P a)
    (hb_adm : P.Primary.Admissible b)
    (hb_primary : P.Primary.objective b ≤ P.Primary.objective a) :
    ¬ P.secondaryObjective b < P.secondaryObjective a := by
  intro hb_secondary
  have hb_min : IsMinimizer P.Primary b :=
    replacement_is_primary_minimizer ha.1 hb_adm hb_primary
  have hsec_le : P.secondaryObjective a ≤ P.secondaryObjective b :=
    ha.2 b hb_min
  exact not_lt_of_ge hsec_le hb_secondary

theorem secondary_minimizer_forces_replacement_rigidity
    {α : Type*} [TopologicalSpace α]
    {P : SecondarySelectorProblem α} {a b : α}
    (ha : IsSecondaryMinimizingPrimaryMinimizer P a)
    (hb_adm : P.Primary.Admissible b)
    (hb_primary : P.Primary.objective b ≤ P.Primary.objective a)
    (hb_secondary_le : P.secondaryObjective b ≤ P.secondaryObjective a) :
    P.secondaryObjective b = P.secondaryObjective a := by
  have hnot_lt :=
    no_strict_secondary_decreasing_replacement ha hb_adm hb_primary
  exact le_antisymm hb_secondary_le (le_of_not_gt hnot_lt)

lemma replacement_is_primary_minimizer_ennreal
    {α : Type*} [TopologicalSpace α]
    {P : MinimizationProblemENNReal α} {a b : α}
    (ha : IsMinimizerENNReal P a)
    (hb_adm : P.Admissible b)
    (hb_primary : P.objective b ≤ P.objective a) :
    IsMinimizerENNReal P b := by
  constructor
  · exact hb_adm
  · intro c hc
    exact le_trans hb_primary (ha.2 c hc)

lemma no_strict_secondary_decreasing_replacement_ennreal
    {α : Type*} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α} {a b : α}
    (ha : IsSecondaryMinimizingPrimaryMinimizerENNReal P a)
    (hb_adm : P.Primary.Admissible b)
    (hb_primary : P.Primary.objective b ≤ P.Primary.objective a) :
    ¬ P.secondaryObjective b < P.secondaryObjective a := by
  intro hb_secondary
  have hb_min : IsMinimizerENNReal P.Primary b :=
    replacement_is_primary_minimizer_ennreal ha.1 hb_adm hb_primary
  have hsec_le : P.secondaryObjective a ≤ P.secondaryObjective b :=
    ha.2 b hb_min
  exact not_lt_of_ge hsec_le hb_secondary

theorem secondary_minimizer_forces_replacement_rigidity_ennreal
    {α : Type*} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α} {a b : α}
    (ha : IsSecondaryMinimizingPrimaryMinimizerENNReal P a)
    (hb_adm : P.Primary.Admissible b)
    (hb_primary : P.Primary.objective b ≤ P.Primary.objective a)
    (hb_secondary_le : P.secondaryObjective b ≤ P.secondaryObjective a) :
    P.secondaryObjective b = P.secondaryObjective a := by
  have hnot_lt :=
    no_strict_secondary_decreasing_replacement_ennreal ha hb_adm hb_primary
  exact le_antisymm hb_secondary_le (le_of_not_gt hnot_lt)

/-!
## Barycenter replacement Jensen layer

This is the finite weighted Jensen statement behind the barycenter replacement
step in Tao Section 3.  In the measure proof, the function is the logarithmic
kernel `t ↦ log (1 / |x - t|)` restricted to a positive component `I`, and
`x` is outside `I`, so the kernel is convex on that interval.
-/

lemma finite_barycenter_replacement_jensen
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w y : ι → ℝ) (f : ℝ → ℝ) (C : Set ℝ)
    (hf : ConvexOn ℝ C f)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1)
    (hy_mem : ∀ i ∈ s, y i ∈ C) :
    f (∑ i ∈ s, w i * y i) ≤ ∑ i ∈ s, w i * f (y i) := by
  have h := hf.map_sum_le (t := s) (w := w) (p := y)
    hw_nonneg hw_sum hy_mem
  simpa [smul_eq_mul] using h

lemma finite_barycenter_replacement_potential_le
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w y : ι → ℝ) (kernel : ℝ → ℝ) (C : Set ℝ)
    (hkernel : ConvexOn ℝ C kernel)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1)
    (hy_mem : ∀ i ∈ s, y i ∈ C) :
    kernel (∑ i ∈ s, w i * y i) ≤
      ∑ i ∈ s, w i * kernel (y i) :=
  finite_barycenter_replacement_jensen s w y kernel C
    hkernel hw_nonneg hw_sum hy_mem

/-- The logarithmic kernel is convex on any interval lying strictly to the left of `x`. -/
lemma logKernel_convexOn_Iic_left {x c : ℝ} (hc : c < x) :
    ConvexOn ℝ (Iic c) (fun t : ℝ => Real.log (1 / |x - t|)) := by
  refine ⟨convex_Iic c, ?_⟩
  intro y hy z hz a b ha hb hab
  have hyle : y ≤ c := hy
  have hzle : z ≤ c := hz
  have hyx : 0 < x - y := by linarith
  have hzx : 0 < x - z := by linarith
  have hcombo_le : a * y + b * z ≤ c := by
    have hay : a * y ≤ a * c := mul_le_mul_of_nonneg_left hyle ha
    have hbz : b * z ≤ b * c := mul_le_mul_of_nonneg_left hzle hb
    have hcweighted : a * c + b * c = c := by
      calc
        a * c + b * c = (a + b) * c := by ring
        _ = c := by rw [hab]; ring
    linarith
  have hcombo : 0 < x - (a • y + b • z) := by
    simp [smul_eq_mul]
    linarith
  have hconc := strictConcaveOn_log_Ioi.concaveOn.2
      (show x - y ∈ Ioi (0 : ℝ) by exact hyx)
      (show x - z ∈ Ioi (0 : ℝ) by exact hzx)
      ha hb hab
  have harg : a • (x - y) + b • (x - z) = x - (a • y + b • z) := by
    simp [smul_eq_mul]
    calc
      a * (x - y) + b * (x - z) = (a + b) * x - (a * y + b * z) := by ring
      _ = x - (a * y + b * z) := by rw [hab]; ring
  have hlog :
      a • Real.log (x - y) + b • Real.log (x - z) ≤
        Real.log (x - (a • y + b • z)) := by
    rw [← harg]
    exact hconc
  have hyabs : |x - y| = x - y := abs_of_pos hyx
  have hzabs : |x - z| = x - z := abs_of_pos hzx
  have hcabs : |x - (a • y + b • z)| = x - (a • y + b • z) :=
    abs_of_pos hcombo
  change Real.log (1 / |x - (a • y + b • z)|) ≤
    a • Real.log (1 / |x - y|) + b • Real.log (1 / |x - z|)
  rw [hyabs, hzabs, hcabs]
  have htarget :
      -Real.log (x - (a • y + b • z)) ≤
        a * -Real.log (x - y) + b * -Real.log (x - z) := by
    calc
      -Real.log (x - (a • y + b • z))
          ≤ -(a * Real.log (x - y) + b * Real.log (x - z)) := neg_le_neg hlog
      _ = a * -Real.log (x - y) + b * -Real.log (x - z) := by ring
  simpa [one_div, Real.log_inv, smul_eq_mul] using htarget

/-- The logarithmic kernel is convex on any interval lying strictly to the right of `x`. -/
lemma logKernel_convexOn_Ici_right {x c : ℝ} (hc : x < c) :
    ConvexOn ℝ (Ici c) (fun t : ℝ => Real.log (1 / |x - t|)) := by
  refine ⟨convex_Ici c, ?_⟩
  intro y hy z hz a b ha hb hab
  have hyle : c ≤ y := hy
  have hzle : c ≤ z := hz
  have hyx : 0 < y - x := by linarith
  have hzx : 0 < z - x := by linarith
  have hcombo_ge : c ≤ a * y + b * z := by
    have hay : a * c ≤ a * y := mul_le_mul_of_nonneg_left hyle ha
    have hbz : b * c ≤ b * z := mul_le_mul_of_nonneg_left hzle hb
    have hcweighted : a * c + b * c = c := by
      calc
        a * c + b * c = (a + b) * c := by ring
        _ = c := by rw [hab]; ring
    linarith
  have hcombo : 0 < (a • y + b • z) - x := by
    simp [smul_eq_mul]
    linarith
  have hconc := strictConcaveOn_log_Ioi.concaveOn.2
      (show y - x ∈ Ioi (0 : ℝ) by exact hyx)
      (show z - x ∈ Ioi (0 : ℝ) by exact hzx)
      ha hb hab
  have harg : a • (y - x) + b • (z - x) = (a • y + b • z) - x := by
    simp [smul_eq_mul]
    calc
      a * (y - x) + b * (z - x) = (a * y + b * z) - (a + b) * x := by ring
      _ = (a * y + b * z) - x := by rw [hab]; ring
  have hlog :
      a • Real.log (y - x) + b • Real.log (z - x) ≤
        Real.log ((a • y + b • z) - x) := by
    rw [← harg]
    exact hconc
  have hyabs : |x - y| = y - x := by
    rw [abs_of_neg (by linarith : x - y < 0)]
    ring
  have hzabs : |x - z| = z - x := by
    rw [abs_of_neg (by linarith : x - z < 0)]
    ring
  have hcabs : |x - (a • y + b • z)| = (a • y + b • z) - x := by
    rw [abs_of_neg (by linarith : x - (a • y + b • z) < 0)]
    ring
  change Real.log (1 / |x - (a • y + b • z)|) ≤
    a • Real.log (1 / |x - y|) + b • Real.log (1 / |x - z|)
  rw [hyabs, hzabs, hcabs]
  have htarget :
      -Real.log ((a • y + b • z) - x) ≤
        a * -Real.log (y - x) + b * -Real.log (z - x) := by
    calc
      -Real.log ((a • y + b • z) - x)
          ≤ -(a * Real.log (y - x) + b * Real.log (z - x)) := neg_le_neg hlog
      _ = a * -Real.log (y - x) + b * -Real.log (z - x) := by ring
  simpa [one_div, Real.log_inv, smul_eq_mul] using htarget

lemma logKernel_continuousOn_Iic_left {x c : ℝ} (hc : c < x) :
    ContinuousOn (fun t : ℝ => Real.log (1 / |x - t|)) (Iic c) := by
  apply ContinuousOn.log
  · exact (continuousOn_const.div₀
      ((continuousOn_const.sub continuousOn_id).abs)
      (fun t ht hzero => by
        have htc : t ≤ c := ht
        have hxt : x - t ≠ 0 := by
          intro h
          linarith
        exact hxt (abs_eq_zero.mp hzero)))
  · intro t ht hzero
    have htc : t ≤ c := ht
    have hxt : x - t ≠ 0 := by
      intro h
      linarith
    have hpos : 0 < |x - t| := abs_pos.mpr hxt
    exact (div_ne_zero one_ne_zero (ne_of_gt hpos)) hzero

lemma logKernel_continuousOn_Ici_right {x c : ℝ} (hc : x < c) :
    ContinuousOn (fun t : ℝ => Real.log (1 / |x - t|)) (Ici c) := by
  apply ContinuousOn.log
  · exact (continuousOn_const.div₀
      ((continuousOn_const.sub continuousOn_id).abs)
      (fun t ht hzero => by
        have hct : c ≤ t := ht
        have hxt : x - t ≠ 0 := by
          intro h
          linarith
        exact hxt (abs_eq_zero.mp hzero)))
  · intro t ht hzero
    have hct : c ≤ t := ht
    have hxt : x - t ≠ 0 := by
      intro h
      linarith
    have hpos : 0 < |x - t| := abs_pos.mpr hxt
    exact (div_ne_zero one_ne_zero (ne_of_gt hpos)) hzero

lemma logKernel_continuousOn_away {x : ℝ} {K : Set ℝ}
    (haway : ∀ t : ℝ, t ∈ K → x ≠ t) :
    ContinuousOn (fun t : ℝ => Real.log (1 / |x - t|)) K := by
  apply ContinuousOn.log
  · exact (continuousOn_const.div₀
      ((continuousOn_const.sub continuousOn_id).abs)
      (fun t ht hzero => by
        exact (haway t ht) (sub_eq_zero.mp (abs_eq_zero.mp hzero))))
  · intro t ht hzero
    have hxt : x - t ≠ 0 := by
      intro h
      exact (haway t ht) (sub_eq_zero.mp h)
    have hpos : 0 < |x - t| := abs_pos.mpr hxt
    exact (div_ne_zero one_ne_zero (ne_of_gt hpos)) hzero

theorem finite_barycenter_logKernel_replacement_le_left
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w y : ι → ℝ) {x c : ℝ}
    (hc : c < x)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1)
    (hy_mem : ∀ i ∈ s, y i ∈ Iic c) :
    Real.log (1 / |x - ∑ i ∈ s, w i * y i|) ≤
      ∑ i ∈ s, w i * Real.log (1 / |x - y i|) :=
  finite_barycenter_replacement_potential_le s w y
    (fun t : ℝ => Real.log (1 / |x - t|)) (Iic c)
    (logKernel_convexOn_Iic_left hc) hw_nonneg hw_sum hy_mem

theorem finite_barycenter_logKernel_replacement_le_right
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w y : ι → ℝ) {x c : ℝ}
    (hc : x < c)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1)
    (hy_mem : ∀ i ∈ s, y i ∈ Ici c) :
    Real.log (1 / |x - ∑ i ∈ s, w i * y i|) ≤
      ∑ i ∈ s, w i * Real.log (1 / |x - y i|) :=
  finite_barycenter_replacement_potential_le s w y
    (fun t : ℝ => Real.log (1 / |x - t|)) (Ici c)
    (logKernel_convexOn_Ici_right hc) hw_nonneg hw_sum hy_mem

lemma measure_barycenter_replacement_jensen
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℝ → ℝ) (C : Set ℝ)
    (hf : ConvexOn ℝ C f)
    (hcont : ContinuousOn f C)
    (hclosed : IsClosed C)
    (hmem : ∀ᵐ t ∂μ, t ∈ C)
    (hid : Integrable (fun t : ℝ => t) μ)
    (hfint : Integrable f μ) :
    f (∫ t : ℝ, t ∂μ) ≤ ∫ t : ℝ, f t ∂μ := by
  exact hf.map_integral_le hcont hclosed hmem hid hfint

theorem measure_barycenter_logKernel_replacement_le_left
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {x c : ℝ}
    (hc : c < x)
    (hmem : ∀ᵐ t ∂μ, t ∈ Iic c)
    (hfirst : Integrable (fun t : ℝ => t) μ)
    (hkernel_int : Integrable
      (fun t : ℝ => Real.log (1 / |x - t|)) μ) :
    Real.log (1 / |x - ∫ t : ℝ, t ∂μ|) ≤
      ∫ t : ℝ, Real.log (1 / |x - t|) ∂μ := by
  exact measure_barycenter_replacement_jensen μ
    (fun t : ℝ => Real.log (1 / |x - t|)) (Iic c)
    (logKernel_convexOn_Iic_left hc)
    (logKernel_continuousOn_Iic_left hc)
    isClosed_Iic hmem hfirst hkernel_int

theorem measure_barycenter_logKernel_replacement_le_right
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {x c : ℝ}
    (hc : x < c)
    (hmem : ∀ᵐ t ∂μ, t ∈ Ici c)
    (hfirst : Integrable (fun t : ℝ => t) μ)
    (hkernel_int : Integrable
      (fun t : ℝ => Real.log (1 / |x - t|)) μ) :
    Real.log (1 / |x - ∫ t : ℝ, t ∂μ|) ≤
      ∫ t : ℝ, Real.log (1 / |x - t|) ∂μ := by
  exact measure_barycenter_replacement_jensen μ
    (fun t : ℝ => Real.log (1 / |x - t|)) (Ici c)
    (logKernel_convexOn_Ici_right hc)
    (logKernel_continuousOn_Ici_right hc)
    isClosed_Ici hmem hfirst hkernel_int

theorem measure_barycenter_logKernel_replacement_le_of_mem_Ioo_left
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {l r x : ℝ}
    (hrx : r < x)
    (hmem : ∀ᵐ t ∂μ, t ∈ Ioo l r)
    (hfirst : Integrable (fun t : ℝ => t) μ)
    (hkernel_int : Integrable
      (fun t : ℝ => Real.log (1 / |x - t|)) μ) :
    Real.log (1 / |x - ∫ t : ℝ, t ∂μ|) ≤
      ∫ t : ℝ, Real.log (1 / |x - t|) ∂μ := by
  exact measure_barycenter_logKernel_replacement_le_left μ hrx
    (hmem.mono (fun t ht => le_of_lt ht.2)) hfirst hkernel_int

theorem measure_barycenter_logKernel_replacement_le_of_mem_Ioo_right
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {l r x : ℝ}
    (hxl : x < l)
    (hmem : ∀ᵐ t ∂μ, t ∈ Ioo l r)
    (hfirst : Integrable (fun t : ℝ => t) μ)
    (hkernel_int : Integrable
      (fun t : ℝ => Real.log (1 / |x - t|)) μ) :
    Real.log (1 / |x - ∫ t : ℝ, t ∂μ|) ≤
      ∫ t : ℝ, Real.log (1 / |x - t|) ∂μ := by
  exact measure_barycenter_logKernel_replacement_le_right μ hxl
    (hmem.mono (fun t ht => le_of_lt ht.1)) hfirst hkernel_int

/--
Combined outside-component Jensen inequality.  If the block measure is
supported in an open component `(l,r)` and the test point `x` lies strictly
outside that component, replacing the block by its barycenter cannot increase
the logarithmic potential at `x`.
-/
theorem measure_barycenter_logKernel_replacement_le_of_strictOutside_Ioo
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {l r x : ℝ}
    (hstrict : x < l ∨ r < x)
    (hmem : ∀ᵐ t ∂μ, t ∈ Ioo l r)
    (hfirst : Integrable (fun t : ℝ => t) μ)
    (hkernel_int : Integrable
      (fun t : ℝ => Real.log (1 / |x - t|)) μ) :
    Real.log (1 / |x - ∫ t : ℝ, t ∂μ|) ≤
      ∫ t : ℝ, Real.log (1 / |x - t|) ∂μ := by
  rcases hstrict with hxl | hrx
  · exact measure_barycenter_logKernel_replacement_le_of_mem_Ioo_right μ
      hxl hmem hfirst hkernel_int
  · exact measure_barycenter_logKernel_replacement_le_of_mem_Ioo_left μ
      hrx hmem hfirst hkernel_int

/--
The component-block log kernel is integrable for test points strictly outside
the component.  The restricted block is a.e. supported on
`C.interval ∩ [-1,1]`; on this compact set it lies in the closed half-line away
from `x`, where the log kernel is continuous.
-/
theorem componentBlock_logKernel_integrable_of_strictOutside
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    {x : ℝ} (hx : StrictOutsideComponent C x) :
    Integrable (fun t : ℝ => Real.log (1 / |x - t|)) (componentBlock C) := by
  let f : ℝ → ℝ := fun t => Real.log (1 / |x - t|)
  have hrestrict :
      (realMeasure μ).restrict C.interval =
        (realMeasure μ).restrict (C.interval ∩ Icc (-1 : ℝ) 1) := by
    apply Measure.restrict_congr_set
    filter_upwards [realMeasure_ae_mem_unitInterval μ] with t ht
    exact propext ⟨fun htC => ⟨htC, ht⟩, fun htC => htC.1⟩
  have hs_meas : MeasurableSet (C.interval ∩ Icc (-1 : ℝ) 1) :=
    C.measurableSet_interval.inter measurableSet_Icc
  haveI : IsFiniteMeasure (realMeasure μ) := by infer_instance
  rcases hx with hx_left | hx_right
  · let K : Set ℝ := Icc (-1 : ℝ) 1 ∩ Ici C.left
    have hK : IsCompact K := by
      exact isCompact_Icc.inter_right isClosed_Ici
    have hsub : C.interval ∩ Icc (-1 : ℝ) 1 ⊆ K := by
      intro t ht
      have htC : t ∈ Ioo C.left C.right := by
        simpa [C.interval_eq] using ht.1
      exact ⟨ht.2, le_of_lt htC.1⟩
    have hcont : ContinuousOn f K := by
      exact (logKernel_continuousOn_Ici_right hx_left).mono
        (by intro t ht; exact ht.2)
    have hint : IntegrableOn f (C.interval ∩ Icc (-1 : ℝ) 1)
        (realMeasure μ) :=
      hcont.integrableOn_of_subset_isCompact hK hs_meas hsub
        (measure_ne_top (realMeasure μ) _)
    change Integrable f (componentBlock C)
    unfold componentBlock
    rw [hrestrict]
    simpa [IntegrableOn] using hint
  · let K : Set ℝ := Icc (-1 : ℝ) 1 ∩ Iic C.right
    have hK : IsCompact K := by
      exact isCompact_Icc.inter_right isClosed_Iic
    have hsub : C.interval ∩ Icc (-1 : ℝ) 1 ⊆ K := by
      intro t ht
      have htC : t ∈ Ioo C.left C.right := by
        simpa [C.interval_eq] using ht.1
      exact ⟨ht.2, le_of_lt htC.2⟩
    have hcont : ContinuousOn f K := by
      exact (logKernel_continuousOn_Iic_left hx_right).mono
        (by intro t ht; exact ht.2)
    have hint : IntegrableOn f (C.interval ∩ Icc (-1 : ℝ) 1)
        (realMeasure μ) :=
      hcont.integrableOn_of_subset_isCompact hK hs_meas hsub
        (measure_ne_top (realMeasure μ) _)
    change Integrable f (componentBlock C)
    unfold componentBlock
    rw [hrestrict]
    simpa [IntegrableOn] using hint

/--
Integrability transfers from the component block to its normalized probability
rescaling.  This is only the scalar-measure bridge; the caller still supplies
the original component-block integrability.
-/
theorem ComponentReplacement.normalizedComponentBlock_integrable_of_componentBlock
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C) {f : ℝ → ℝ}
    (hf : Integrable f (componentBlock C)) :
    Integrable f (normalizedComponentBlock C) := by
  unfold normalizedComponentBlock
  exact hf.smul_measure (ENNReal.inv_ne_top.mpr (ne_of_gt R.mass_pos))

theorem ComponentReplacement.normalizedComponentBlock_logKernel_integrable_of_componentBlock
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C) {x : ℝ}
    (hkernel_int : Integrable
      (fun t : ℝ => Real.log (1 / |x - t|)) (componentBlock C)) :
    Integrable
      (fun t : ℝ => Real.log (1 / |x - t|)) (normalizedComponentBlock C) := by
  exact R.normalizedComponentBlock_integrable_of_componentBlock hkernel_int

theorem ComponentReplacement.normalizedComponentBlock_firstMoment_integrable_of_componentBlock
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C)
    (hfirst : Integrable (fun t : ℝ => t) (componentBlock C)) :
    Integrable (fun t : ℝ => t) (normalizedComponentBlock C) := by
  exact R.normalizedComponentBlock_integrable_of_componentBlock hfirst

theorem ComponentReplacement.normalizedComponentBlock_secondMoment_integrable_of_componentBlock
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C)
    (hsecond : Integrable (fun t : ℝ => t ^ 2) (componentBlock C)) :
    Integrable (fun t : ℝ => t ^ 2) (normalizedComponentBlock C) := by
  exact R.normalizedComponentBlock_integrable_of_componentBlock hsecond

/--
Component-block Jensen inequality in normalized form.

After normalizing the restricted component block to a probability measure, the
existing measure-level Jensen theorem applies directly.  The conclusion is the
pointwise block inequality before multiplying back by the component mass.
-/
theorem normalizedComponentBlock_logKernel_replacement_le_of_strictOutside
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C) {x : ℝ}
    (hstrict : StrictOutsideComponent C x)
    (hfirst : Integrable (fun t : ℝ => t) (normalizedComponentBlock C))
    (hkernel_int : Integrable
      (fun t : ℝ => Real.log (1 / |x - t|)) (normalizedComponentBlock C)) :
    Real.log (1 / |x - componentBarycenter C|) ≤
      ∫ t : ℝ, Real.log (1 / |x - t|) ∂normalizedComponentBlock C := by
  letI : IsProbabilityMeasure (normalizedComponentBlock C) :=
    R.normalizedComponentBlock_isProbabilityMeasure
  rw [← normalizedComponentBlock_integral_eq_barycenter R]
  exact measure_barycenter_logKernel_replacement_le_of_strictOutside_Ioo
    (normalizedComponentBlock C) hstrict
    (normalizedComponentBlock_ae_mem_interval R) hfirst hkernel_int

/--
Component-block Jensen inequality scaled back to the original component mass.

This is the form used in the potential decomposition: the replacement block is
`componentMass C` times the kernel evaluated at the barycenter, and the
original block is the integral of the kernel over `componentBlock C`.
-/
theorem componentBlock_logKernel_replacement_le_of_strictOutside
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C) {x : ℝ}
    (hstrict : StrictOutsideComponent C x)
    (hfirst : Integrable (fun t : ℝ => t) (normalizedComponentBlock C))
    (hkernel_norm_int : Integrable
      (fun t : ℝ => Real.log (1 / |x - t|)) (normalizedComponentBlock C)) :
    (componentMass C).toReal *
        Real.log (1 / |x - componentBarycenter C|) ≤
      ∫ t : ℝ, Real.log (1 / |x - t|) ∂componentBlock C := by
  have hmass_ne_zero : componentMass C ≠ 0 := ne_of_gt R.mass_pos
  have hmass_toReal_pos : 0 < (componentMass C).toReal :=
    ENNReal.toReal_pos hmass_ne_zero R.mass_ne_top
  have hjen :=
    normalizedComponentBlock_logKernel_replacement_le_of_strictOutside
      R hstrict hfirst hkernel_norm_int
  have hnorm :
      (∫ t : ℝ, Real.log (1 / |x - t|) ∂normalizedComponentBlock C) =
        ((componentMass C)⁻¹).toReal *
          ∫ t : ℝ, Real.log (1 / |x - t|) ∂componentBlock C := by
    unfold normalizedComponentBlock
    rw [integral_smul_measure]
    rw [smul_eq_mul]
  rw [hnorm] at hjen
  calc
    (componentMass C).toReal *
        Real.log (1 / |x - componentBarycenter C|)
        ≤ (componentMass C).toReal *
            (((componentMass C)⁻¹).toReal *
              ∫ t : ℝ, Real.log (1 / |x - t|) ∂componentBlock C) := by
          exact mul_le_mul_of_nonneg_left hjen (le_of_lt hmass_toReal_pos)
    _ = ∫ t : ℝ, Real.log (1 / |x - t|) ∂componentBlock C := by
          rw [ENNReal.toReal_inv]
          field_simp [hmass_toReal_pos.ne']

/--
Function-level component-block Jensen wrapper.

This packages the scaled Jensen theorem as the `hblock_jensen` input expected by
`componentReplacement_objective_le_of_decomposition_jensen`.
-/
theorem componentReplacement_blockKernel_le_original_of_strictOutside
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C)
    (hfirst : Integrable (fun t : ℝ => t) (normalizedComponentBlock C))
    (hkernel_norm_int : ∀ x : ℝ, StrictOutsideComponent C x →
      Integrable (fun t : ℝ => Real.log (1 / |x - t|))
        (normalizedComponentBlock C)) :
    ∀ x : ℝ, StrictOutsideComponent C x →
      (componentMass C).toReal *
          Real.log (1 / |x - componentBarycenter C|) ≤
        ∫ t : ℝ, Real.log (1 / |x - t|) ∂componentBlock C := by
  intro x hx
  exact componentBlock_logKernel_replacement_le_of_strictOutside
    R hx hfirst (hkernel_norm_int x hx)

/--
Pointwise strict-outside Jensen inequality for the concrete barycenter
replacement.  The only remaining analytic input is integrability of the
unchanged outside part; component-block and normalized-block integrability are
automatic for strict outside test points.
-/
theorem componentReplacement_strictOutside_potential_le_of_outside_integrability_jensen
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C)
    (houtside_integrable : ∀ x : ℝ, StrictOutsideComponent C x →
      Integrable (fun t : ℝ => Real.log (1 / |x - t|))
        ((realMeasure μ).restrict C.intervalᶜ)) :
    ∀ x : ℝ, StrictOutsideComponent C x →
      componentReplacementPotential C x ≤ unitIntervalLogPotential μ x := by
  let outsidePart : ℝ → ℝ :=
    fun x => measureLogPotential ((realMeasure μ).restrict C.intervalᶜ) x
  let replacementBlock : ℝ → ℝ :=
    fun x => (componentMass C).toReal *
      Real.log (1 / |x - componentBarycenter C|)
  let originalBlock : ℝ → ℝ :=
    fun x => ∫ t : ℝ, Real.log (1 / |x - t|) ∂componentBlock C
  refine componentReplacement_strictOutside_potential_le_of_decomposition_jensen
    C outsidePart replacementBlock originalBlock ?_ ?_ ?_
  · simpa [outsidePart, replacementBlock] using
      componentReplacement_potential_le_outside_add_replacementAtom
        C outsidePart (fun x hx => le_rfl) houtside_integrable
  · refine unitIntervalLogPotential_original_potential_decomposition_lower
      C outsidePart originalBlock (fun x hx => le_rfl) ?_
      houtside_integrable
      (fun x hx => componentBlock_logKernel_integrable_of_strictOutside C hx)
    intro x hx
    simp [originalBlock]
  · simpa [replacementBlock, originalBlock] using
      componentReplacement_blockKernel_le_original_of_strictOutside
        R
        (R.normalizedComponentBlock_firstMoment_integrable_of_componentBlock
          (componentBlock_firstMoment_integrable C))
        (fun x hx =>
          R.normalizedComponentBlock_logKernel_integrable_of_componentBlock
            (componentBlock_logKernel_integrable_of_strictOutside C hx))

/--
Concrete component-replacement objective wrapper.

This combines the concrete outside/replacement decomposition, the concrete
original-side decomposition, and the normalized component-block Jensen theorem
into the abstract decomposition-plus-Jensen objective bridge.  The only
remaining analytic assumptions are the two outside comparisons, the component
replacement data, the first-moment integrability of the normalized block, and
the kernel integrability obligations needed by those concrete bridge theorems.
-/
theorem componentReplacement_objective_le_of_concrete_decomposition_jensen
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C)
    (outsidePart : ℝ → ℝ)
    (houtside_replacement : ∀ x : ℝ, StrictOutsideComponent C x →
      measureLogPotential ((realMeasure μ).restrict C.intervalᶜ) x ≤
        outsidePart x)
    (houtside_original : ∀ x : ℝ, StrictOutsideComponent C x →
      outsidePart x ≤
        measureLogPotential ((realMeasure μ).restrict C.intervalᶜ) x)
    (houtside_integrable : ∀ x : ℝ, StrictOutsideComponent C x →
      Integrable (fun t : ℝ => Real.log (1 / |x - t|))
        ((realMeasure μ).restrict C.intervalᶜ))
    (hcomponent_block_integrable : ∀ x : ℝ, StrictOutsideComponent C x →
      Integrable (fun t : ℝ => Real.log (1 / |x - t|)) (componentBlock C))
    (hnormalized_block_integrable : ∀ x : ℝ, StrictOutsideComponent C x →
      Integrable (fun t : ℝ => Real.log (1 / |x - t|))
        (normalizedComponentBlock C))
    (hfirst : Integrable (fun t : ℝ => t) (normalizedComponentBlock C)) :
    volume (PositiveSet (componentReplacementPotential C)) ≤
      volume (PositiveSet (unitIntervalLogPotential μ)) := by
  let replacementBlock : ℝ → ℝ :=
    fun x => (componentMass C).toReal *
      Real.log (1 / |x - componentBarycenter C|)
  let originalBlock : ℝ → ℝ :=
    fun x => ∫ t : ℝ, Real.log (1 / |x - t|) ∂componentBlock C
  refine componentReplacement_objective_le_of_decomposition_jensen
    C outsidePart replacementBlock originalBlock ?_ ?_ ?_
  · simpa [replacementBlock] using
      componentReplacement_potential_le_outside_add_replacementAtom
        C outsidePart houtside_replacement houtside_integrable
  · refine unitIntervalLogPotential_original_potential_decomposition_lower
      C outsidePart originalBlock houtside_original ?_
      houtside_integrable hcomponent_block_integrable
    intro x hx
    simp [originalBlock]
  · simpa [replacementBlock, originalBlock] using
      componentReplacement_blockKernel_le_original_of_strictOutside
        R hfirst hnormalized_block_integrable

/--
Concrete component-replacement objective wrapper with the outside part fixed to
the concrete outside restricted potential.

This removes the auxiliary `outsidePart` and its two comparison assumptions
from `componentReplacement_objective_le_of_concrete_decomposition_jensen`.
-/
theorem componentReplacement_objective_le_of_concrete_outside_jensen
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C)
    (houtside_integrable : ∀ x : ℝ, StrictOutsideComponent C x →
      Integrable (fun t : ℝ => Real.log (1 / |x - t|))
        ((realMeasure μ).restrict C.intervalᶜ))
    (hcomponent_block_integrable : ∀ x : ℝ, StrictOutsideComponent C x →
      Integrable (fun t : ℝ => Real.log (1 / |x - t|)) (componentBlock C))
    (hnormalized_block_integrable : ∀ x : ℝ, StrictOutsideComponent C x →
      Integrable (fun t : ℝ => Real.log (1 / |x - t|))
        (normalizedComponentBlock C))
    (hfirst : Integrable (fun t : ℝ => t) (normalizedComponentBlock C)) :
    volume (PositiveSet (componentReplacementPotential C)) ≤
      volume (PositiveSet (unitIntervalLogPotential μ)) := by
  refine componentReplacement_objective_le_of_concrete_decomposition_jensen
    R (fun x => measureLogPotential ((realMeasure μ).restrict C.intervalᶜ) x)
    ?_ ?_ houtside_integrable hcomponent_block_integrable
    hnormalized_block_integrable hfirst
  · intro x hx
    exact le_rfl
  · intro x hx
    exact le_rfl

/--
Concrete component-replacement objective wrapper with normalized-block
integrability discharged from component-block integrability.

Remaining assumptions are the component-replacement data, outside kernel
integrability, component-block kernel integrability, and component-block
first-moment integrability.
-/
theorem componentReplacement_objective_le_of_componentBlock_integrability_jensen
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C)
    (houtside_integrable : ∀ x : ℝ, StrictOutsideComponent C x →
      Integrable (fun t : ℝ => Real.log (1 / |x - t|))
        ((realMeasure μ).restrict C.intervalᶜ))
    (hcomponent_block_integrable : ∀ x : ℝ, StrictOutsideComponent C x →
      Integrable (fun t : ℝ => Real.log (1 / |x - t|)) (componentBlock C))
    (hcomponent_first : Integrable (fun t : ℝ => t) (componentBlock C)) :
    volume (PositiveSet (componentReplacementPotential C)) ≤
      volume (PositiveSet (unitIntervalLogPotential μ)) := by
  refine componentReplacement_objective_le_of_concrete_outside_jensen
    R houtside_integrable hcomponent_block_integrable ?_ ?_
  · intro x hx
    exact R.normalizedComponentBlock_logKernel_integrable_of_componentBlock
      (hcomponent_block_integrable x hx)
  · exact R.normalizedComponentBlock_firstMoment_integrable_of_componentBlock
      hcomponent_first

/--
Cleaner concrete component-replacement objective wrapper: first-moment
integrability of the component block is discharged from the unit-interval
support of `realMeasure μ`.
-/
theorem componentReplacement_objective_le_of_kernel_integrability_jensen
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C)
    (houtside_integrable : ∀ x : ℝ, StrictOutsideComponent C x →
      Integrable (fun t : ℝ => Real.log (1 / |x - t|))
        ((realMeasure μ).restrict C.intervalᶜ))
    (hcomponent_block_integrable : ∀ x : ℝ, StrictOutsideComponent C x →
      Integrable (fun t : ℝ => Real.log (1 / |x - t|)) (componentBlock C)) :
    volume (PositiveSet (componentReplacementPotential C)) ≤
      volume (PositiveSet (unitIntervalLogPotential μ)) := by
  exact componentReplacement_objective_le_of_componentBlock_integrability_jensen
    R houtside_integrable hcomponent_block_integrable
    (componentBlock_firstMoment_integrable C)

/--
Cleaner component-replacement objective wrapper: the only remaining analytic
input is outside log-kernel integrability; component-block integrability is
automatic for strict outside test points.
-/
theorem componentReplacement_objective_le_of_outside_integrability_jensen
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C)
    (houtside_integrable : ∀ x : ℝ, StrictOutsideComponent C x →
      Integrable (fun t : ℝ => Real.log (1 / |x - t|))
        ((realMeasure μ).restrict C.intervalᶜ)) :
    volume (PositiveSet (componentReplacementPotential C)) ≤
      volume (PositiveSet (unitIntervalLogPotential μ)) := by
  exact componentReplacement_objective_le_of_kernel_integrability_jensen
    R houtside_integrable
    (fun x hx => componentBlock_logKernel_integrable_of_strictOutside C hx)

/--
Primary objective nonincrease for the concrete barycenter replacement, obtained
by combining strict-outside Jensen with the positive-set objective bridge.
-/
theorem componentReplacement_primaryObjective_nonincrease_of_outside_integrability
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C)
    (houtside_integrable : ∀ x : ℝ, StrictOutsideComponent C x →
      Integrable (fun t : ℝ => Real.log (1 / |x - t|))
        ((realMeasure μ).restrict C.intervalᶜ)) :
    volume (PositiveSet (componentReplacementPotential C)) ≤
      volume (PositiveSet (unitIntervalLogPotential μ)) := by
  exact componentReplacement_objective_le_of_strictOutside_potential_le C
    (componentReplacement_strictOutside_potential_le_of_outside_integrability_jensen
      R houtside_integrable)

/--
Outside-restricted real-measure log-kernel integrability from finite singular
tail mass.

The existing tail-mass theorem gives full unit-interval integrability over the
subtype measure.  This bridge pushes it forward to `realMeasure μ` and then
restricts to the outside of the component interval.
-/
theorem outside_logKernel_integrable_of_notMem_diagonalAtomSet_tailMass
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    {ε x : ℝ} (hε : 0 < ε)
    (hxdiag : x ∉ diagonalAtomSet μ)
    (htailFinite : singularTailMass ε μ x < ∞) :
    Integrable (fun t : ℝ => Real.log (1 / |x - t|))
      ((realMeasure μ).restrict C.intervalᶜ) := by
  have hunit_raw :
      Integrable
        (fun t : UnitInterval1038 => Real.log (1 / |(t : ℝ) - x|))
        (μ : Measure UnitInterval1038) :=
    unitInterval_logKernel_integrable_of_notMem_diagonalAtomSet_tailMass
      (μ := μ) hε hxdiag htailFinite
  have hunit :
      Integrable
        ((fun t : ℝ => Real.log (1 / |x - t|)) ∘
          (fun t : UnitInterval1038 => (t : ℝ)))
        (μ : Measure UnitInterval1038) := by
    exact hunit_raw.congr (Filter.Eventually.of_forall (fun t => by
      simp [abs_sub_comm]))
  have hkernel_meas :
      AEStronglyMeasurable
        (fun t : ℝ => Real.log (1 / |x - t|))
        (Measure.map (fun t : UnitInterval1038 => (t : ℝ))
          (μ : Measure UnitInterval1038)) :=
    (Real.measurable_log.comp (measurable_const.div
      (continuous_abs.measurable.comp
        (measurable_const.sub measurable_id)))).aestronglyMeasurable
  have hreal :
      Integrable (fun t : ℝ => Real.log (1 / |x - t|)) (realMeasure μ) := by
    dsimp [realMeasure]
    exact (integrable_map_measure hkernel_meas
      continuous_subtype_val.measurable.aemeasurable).2 hunit
  exact hreal.restrict

theorem endpointRemainder_logKernel_integrable_of_left_outside
    {μ : ProbabilityMeasure UnitInterval1038} {x : ℝ} (hx : x < -1) :
    Integrable (fun t : ℝ => Real.log (1 / |x - t|))
      ((realMeasure μ).restrict ({-1} : Set ℝ)ᶜ) := by
  have hunit :
      Integrable
        ((fun t : ℝ => Real.log (1 / |x - t|)) ∘
          (fun t : UnitInterval1038 => (t : ℝ)))
        (μ : Measure UnitInterval1038) :=
    unitInterval_logKernel_integrable_of_left_outside (μ := μ) hx
  have hkernel_meas :
      AEStronglyMeasurable
        (fun t : ℝ => Real.log (1 / |x - t|))
        (Measure.map (fun t : UnitInterval1038 => (t : ℝ))
          (μ : Measure UnitInterval1038)) :=
    (Real.measurable_log.comp (measurable_const.div
      (continuous_abs.measurable.comp
        (measurable_const.sub measurable_id)))).aestronglyMeasurable
  have hreal :
      Integrable (fun t : ℝ => Real.log (1 / |x - t|)) (realMeasure μ) := by
    dsimp [realMeasure]
    exact (integrable_map_measure hkernel_meas
      continuous_subtype_val.measurable.aemeasurable).2 hunit
  exact hreal.restrict

/--
Off-diagonal component-replacement objective wrapper.

The outside restricted log-kernel only has to be integrable at strict-outside
test points away from `diagonalAtomSet μ`; diagonal strict-outside exceptions
are discarded by the null exceptional-set bridge in
`replacement_objective_le_of_strictOutside_potential_le_offdiag`.
-/
theorem componentReplacement_objective_le_of_outside_integrability_offdiag_jensen
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C)
    (houtside_integrable : ∀ x : ℝ, StrictOutsideComponent C x →
      x ∉ diagonalAtomSet μ →
      Integrable (fun t : ℝ => Real.log (1 / |x - t|))
        ((realMeasure μ).restrict C.intervalᶜ)) :
    volume (PositiveSet (componentReplacementPotential C)) ≤
      volume (PositiveSet (unitIntervalLogPotential μ)) := by
  refine replacement_objective_le_of_strictOutside_potential_le_offdiag C ?_
  intro x hxstrict hxdiag
  have houtside_int := houtside_integrable x hxstrict hxdiag
  have hcomponent_int :
      Integrable (fun t : ℝ => Real.log (1 / |x - t|)) (componentBlock C) :=
    componentBlock_logKernel_integrable_of_strictOutside C hxstrict
  have hnormalized_int :
      Integrable (fun t : ℝ => Real.log (1 / |x - t|))
        (normalizedComponentBlock C) :=
    R.normalizedComponentBlock_logKernel_integrable_of_componentBlock
      hcomponent_int
  have hfirst :
      Integrable (fun t : ℝ => t) (normalizedComponentBlock C) :=
    R.normalizedComponentBlock_firstMoment_integrable_of_componentBlock
      (componentBlock_firstMoment_integrable C)
  have hblock :
      (componentMass C).toReal *
          Real.log (1 / |x - componentBarycenter C|) ≤
        ∫ t : ℝ, Real.log (1 / |x - t|) ∂componentBlock C :=
    componentBlock_logKernel_replacement_le_of_strictOutside
      R hxstrict hfirst hnormalized_int
  rw [componentReplacement_potential_eq_outside_add_replacementAtom C x
    houtside_int]
  rw [unitIntervalLogPotential_eq_outside_add_componentBlock C x
    houtside_int hcomponent_int]
  exact add_le_add le_rfl hblock

/--
Tail-mass component-replacement objective wrapper.

Finite singular tail mass at every off-diagonal strict-outside test point
discharges the outside restricted log-kernel integrability assumption in
`componentReplacement_objective_le_of_outside_integrability_offdiag_jensen`.
-/
theorem componentReplacement_objective_le_of_outside_tailMass_offdiag_jensen
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C)
    {ε : ℝ} (hε : 0 < ε)
    (htailFinite : ∀ x : ℝ, StrictOutsideComponent C x →
      x ∉ diagonalAtomSet μ → singularTailMass ε μ x < ∞) :
    volume (PositiveSet (componentReplacementPotential C)) ≤
      volume (PositiveSet (unitIntervalLogPotential μ)) := by
  refine componentReplacement_objective_le_of_outside_integrability_offdiag_jensen
    R ?_
  intro x hxstrict hxdiag
  exact outside_logKernel_integrable_of_notMem_diagonalAtomSet_tailMass
    C hε hxdiag (htailFinite x hxstrict hxdiag)

/--
Null-exception tail-mass component-replacement objective wrapper.

Finite singular tail mass is only required at strict-outside off-diagonal test
points outside the supplied null set `N`; endpoints, diagonal atoms, and `N` are
discarded by
`replacement_objective_le_of_strictOutside_potential_le_offdiag_null`.
-/
theorem componentReplacement_objective_le_of_outside_tailMass_offdiag_ae_jensen
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C)
    {ε : ℝ} (hε : 0 < ε)
    (N : Set ℝ) (hN : volume N = 0)
    (htailFinite : ∀ x : ℝ, StrictOutsideComponent C x →
      x ∉ diagonalAtomSet μ → x ∉ N → singularTailMass ε μ x < ∞) :
    volume (PositiveSet (componentReplacementPotential C)) ≤
      volume (PositiveSet (unitIntervalLogPotential μ)) := by
  refine replacement_objective_le_of_strictOutside_potential_le_offdiag_null
    C hN ?_
  intro x hxstrict hxdiag hxN
  have houtside_int :
      Integrable (fun t : ℝ => Real.log (1 / |x - t|))
        ((realMeasure μ).restrict C.intervalᶜ) :=
    outside_logKernel_integrable_of_notMem_diagonalAtomSet_tailMass
      C hε hxdiag (htailFinite x hxstrict hxdiag hxN)
  have hcomponent_int :
      Integrable (fun t : ℝ => Real.log (1 / |x - t|)) (componentBlock C) :=
    componentBlock_logKernel_integrable_of_strictOutside C hxstrict
  have hnormalized_int :
      Integrable (fun t : ℝ => Real.log (1 / |x - t|))
        (normalizedComponentBlock C) :=
    R.normalizedComponentBlock_logKernel_integrable_of_componentBlock
      hcomponent_int
  have hfirst :
      Integrable (fun t : ℝ => t) (normalizedComponentBlock C) :=
    R.normalizedComponentBlock_firstMoment_integrable_of_componentBlock
      (componentBlock_firstMoment_integrable C)
  have hblock :
      (componentMass C).toReal *
          Real.log (1 / |x - componentBarycenter C|) ≤
        ∫ t : ℝ, Real.log (1 / |x - t|) ∂componentBlock C :=
    componentBlock_logKernel_replacement_le_of_strictOutside
      R hxstrict hfirst hnormalized_int
  rw [componentReplacement_potential_eq_outside_add_replacementAtom C x
    houtside_int]
  rw [unitIntervalLogPotential_eq_outside_add_componentBlock C x
    houtside_int hcomponent_int]
  exact add_le_add le_rfl hblock

/--
Stable public wrapper name for the null-exception tail-mass replacement
objective theorem.
-/
theorem componentReplacement_objective_le_of_tailMass_null_exception
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C)
    {ε : ℝ} (hε : 0 < ε)
    (N : Set ℝ) (hN : volume N = 0)
    (htailFinite : ∀ x : ℝ, StrictOutsideComponent C x →
      x ∉ diagonalAtomSet μ → x ∉ N → singularTailMass ε μ x < ∞) :
    volume (PositiveSet (componentReplacementPotential C)) ≤
      volume (PositiveSet (unitIntervalLogPotential μ)) := by
  exact componentReplacement_objective_le_of_outside_tailMass_offdiag_ae_jensen
    R hε N hN htailFinite

theorem componentReplacement_objective_le_add_of_tailMass_exception
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C)
    {ε : ℝ} (hε : 0 < ε)
    (N : Set ℝ) {η : ℝ≥0∞} (hN : volume N ≤ η)
    (htailFinite : ∀ x : ℝ, StrictOutsideComponent C x →
      x ∉ diagonalAtomSet μ → x ∉ N → singularTailMass ε μ x < ∞) :
    volume (PositiveSet (componentReplacementPotential C)) ≤
      volume (PositiveSet (unitIntervalLogPotential μ)) + η := by
  refine replacement_objective_le_add_of_strictOutside_potential_le_offdiag_exception
    C hN ?_
  intro x hxstrict hxdiag hxN
  have houtside_int :
      Integrable (fun t : ℝ => Real.log (1 / |x - t|))
        ((realMeasure μ).restrict C.intervalᶜ) :=
    outside_logKernel_integrable_of_notMem_diagonalAtomSet_tailMass
      C hε hxdiag (htailFinite x hxstrict hxdiag hxN)
  have hcomponent_int :
      Integrable (fun t : ℝ => Real.log (1 / |x - t|)) (componentBlock C) :=
    componentBlock_logKernel_integrable_of_strictOutside C hxstrict
  have hnormalized_int :
      Integrable (fun t : ℝ => Real.log (1 / |x - t|))
        (normalizedComponentBlock C) :=
    R.normalizedComponentBlock_logKernel_integrable_of_componentBlock
      hcomponent_int
  have hfirst :
      Integrable (fun t : ℝ => t) (normalizedComponentBlock C) :=
    R.normalizedComponentBlock_firstMoment_integrable_of_componentBlock
      (componentBlock_firstMoment_integrable C)
  have hblock :
      (componentMass C).toReal *
          Real.log (1 / |x - componentBarycenter C|) ≤
        ∫ t : ℝ, Real.log (1 / |x - t|) ∂componentBlock C :=
    componentBlock_logKernel_replacement_le_of_strictOutside
      R hxstrict hfirst hnormalized_int
  rw [componentReplacement_potential_eq_outside_add_replacementAtom C x
    houtside_int]
  rw [unitIntervalLogPotential_eq_outside_add_componentBlock C x
    houtside_int hcomponent_int]
  exact add_le_add le_rfl hblock

theorem componentReplacement_objective_le_of_forall_small_tailMass_exception
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C)
    {ε : ℝ} (hε : 0 < ε)
    (hsmall : ∀ η : NNReal, 0 < η →
      ∃ N : Set ℝ,
        volume N ≤ (η : ℝ≥0∞) ∧
        ∀ x : ℝ, StrictOutsideComponent C x →
          x ∉ diagonalAtomSet μ → x ∉ N → singularTailMass ε μ x < ∞) :
    volume (PositiveSet (componentReplacementPotential C)) ≤
      volume (PositiveSet (unitIntervalLogPotential μ)) := by
  refine ENNReal.le_of_forall_pos_le_add ?_
  intro η hη _
  rcases hsmall η hη with ⟨N, hN, htailFinite⟩
  exact componentReplacement_objective_le_add_of_tailMass_exception
    R hε N hN htailFinite

/--
Exact objective nonincrease with the small exceptional sets generated
internally from the singular-tail bad-set estimate.
-/
theorem componentReplacement_objective_le_of_singularTail_small_exceptions
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C)
    {ε : ℝ} (hε : 0 < ε) :
    volume (PositiveSet (componentReplacementPotential C)) ≤
      volume (PositiveSet (unitIntervalLogPotential μ)) := by
  refine componentReplacement_objective_le_of_forall_small_tailMass_exception
    R hε ?_
  intro η hη
  exact singularTail_exists_small_strictOutside_exception C ε η hη

/-!
## Finite variance drop under barycenter replacement

This is the finite weighted form of the variance statement used in Tao's
argument: replacing a weighted block by its barycenter does not increase the
second moment, and equality forces every positive-weight point in that block to
already be the barycenter.
-/

lemma finite_weighted_second_moment_sub_barycenter_sq_nonneg
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w y : ι → ℝ)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1) :
    0 ≤ (∑ i ∈ s, w i * y i ^ 2) -
      (∑ i ∈ s, w i * y i) ^ 2 := by
  let m : ℝ := ∑ i ∈ s, w i * y i
  have hsq_nonneg : 0 ≤ ∑ i ∈ s, w i * (y i - m) ^ 2 := by
    exact Finset.sum_nonneg (fun i hi =>
      mul_nonneg (hw_nonneg i hi) (sq_nonneg (y i - m)))
  have hidentity :
      ∑ i ∈ s, w i * (y i - m) ^ 2 =
        (∑ i ∈ s, w i * y i ^ 2) - m ^ 2 := by
    calc
      ∑ i ∈ s, w i * (y i - m) ^ 2
          = ∑ i ∈ s, (w i * y i ^ 2 -
              2 * m * (w i * y i) + m ^ 2 * w i) := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      _ = (∑ i ∈ s, w i * y i ^ 2) -
          2 * m * (∑ i ∈ s, w i * y i) +
          m ^ 2 * (∑ i ∈ s, w i) := by
            simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
      _ = (∑ i ∈ s, w i * y i ^ 2) - m ^ 2 := by
            rw [hw_sum]
            simp [m]
            ring
  rw [← hidentity]
  exact hsq_nonneg

theorem finite_barycenter_second_moment_le_original
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w y : ι → ℝ)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1) :
    (∑ i ∈ s, w i * y i) ^ 2 ≤ ∑ i ∈ s, w i * y i ^ 2 := by
  have h :=
    finite_weighted_second_moment_sub_barycenter_sq_nonneg
      s w y hw_nonneg hw_sum
  linarith

theorem finite_barycenter_second_moment_eq_imp_const_on_positive_weight
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w y : ι → ℝ)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1)
    (heq : (∑ i ∈ s, w i * y i ^ 2) =
      (∑ i ∈ s, w i * y i) ^ 2) :
    ∀ i ∈ s, 0 < w i → y i = ∑ j ∈ s, w j * y j := by
  let m : ℝ := ∑ i ∈ s, w i * y i
  have hidentity :
      ∑ i ∈ s, w i * (y i - m) ^ 2 =
        (∑ i ∈ s, w i * y i ^ 2) - m ^ 2 := by
    calc
      ∑ i ∈ s, w i * (y i - m) ^ 2
          = ∑ i ∈ s, (w i * y i ^ 2 -
              2 * m * (w i * y i) + m ^ 2 * w i) := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      _ = (∑ i ∈ s, w i * y i ^ 2) -
          2 * m * (∑ i ∈ s, w i * y i) +
          m ^ 2 * (∑ i ∈ s, w i) := by
            simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
      _ = (∑ i ∈ s, w i * y i ^ 2) - m ^ 2 := by
            rw [hw_sum]
            simp [m]
            ring
  have hsumzero : ∑ i ∈ s, w i * (y i - m) ^ 2 = 0 := by
    rw [hidentity]
    simp [m] at heq ⊢
    linarith
  have htermzero : ∀ i ∈ s, w i * (y i - m) ^ 2 = 0 := by
    rw [Finset.sum_eq_zero_iff_of_nonneg] at hsumzero
    · exact hsumzero
    · intro i hi
      exact mul_nonneg (hw_nonneg i hi) (sq_nonneg (y i - m))
  intro i hi hwi
  have hzero := htermzero i hi
  have hsquare : (y i - m) ^ 2 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hwi)
  have hdiff : y i - m = 0 := sq_eq_zero_iff.mp hsquare
  dsimp [m] at hdiff ⊢
  linarith

/-! Continuous second-moment form of the same variance drop. -/

lemma measure_second_moment_sub_mean_sq_nonneg
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hfirst : Integrable (fun t : ℝ => t) μ)
    (hsecond : Integrable (fun t : ℝ => t ^ 2) μ) :
    0 ≤ (∫ t : ℝ, t ^ 2 ∂μ) - (∫ t : ℝ, t ∂μ) ^ 2 := by
  let m : ℝ := ∫ t : ℝ, t ∂μ
  have hcenter_nonneg : 0 ≤ ∫ t : ℝ, (t - m) ^ 2 ∂μ := by
    exact integral_nonneg (fun t => sq_nonneg (t - m))
  have hlin : Integrable (fun t : ℝ => 2 * m * t) μ := hfirst.const_mul (2 * m)
  have hsub : Integrable (fun t : ℝ => t ^ 2 - 2 * m * t) μ := hsecond.sub hlin
  have hconst : Integrable (fun _ : ℝ => m ^ 2) μ := integrable_const (m ^ 2)
  have hidentity :
      (∫ t : ℝ, (t - m) ^ 2 ∂μ) = (∫ t : ℝ, t ^ 2 ∂μ) - m ^ 2 := by
    calc
      (∫ t : ℝ, (t - m) ^ 2 ∂μ)
          = ∫ t : ℝ, (t ^ 2 - 2 * m * t + m ^ 2) ∂μ := by
            apply integral_congr_ae
            filter_upwards with t
            ring
      _ = ∫ t : ℝ, (t ^ 2 - 2 * m * t) ∂μ + ∫ _ : ℝ, m ^ 2 ∂μ := by
            rw [integral_add hsub hconst]
      _ = ((∫ t : ℝ, t ^ 2 ∂μ) - ∫ t : ℝ, 2 * m * t ∂μ) +
          ∫ _ : ℝ, m ^ 2 ∂μ := by
            rw [integral_sub hsecond hlin]
      _ = (∫ t : ℝ, t ^ 2 ∂μ) - 2 * m * (∫ t : ℝ, t ∂μ) + m ^ 2 := by
            rw [integral_const_mul, integral_const]
            simp [m]
      _ = (∫ t : ℝ, t ^ 2 ∂μ) - m ^ 2 := by
            simp [m]
            ring
  rw [← hidentity]
  exact hcenter_nonneg

theorem measure_barycenter_second_moment_le_original
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hfirst : Integrable (fun t : ℝ => t) μ)
    (hsecond : Integrable (fun t : ℝ => t ^ 2) μ) :
    (∫ t : ℝ, t ∂μ) ^ 2 ≤ ∫ t : ℝ, t ^ 2 ∂μ := by
  have h := measure_second_moment_sub_mean_sq_nonneg μ hfirst hsecond
  linarith

/--
Component-block second-moment drop under barycenter replacement, scaled back to
the original component mass.
-/
theorem componentBlock_barycenter_secondMoment_le_original
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C)
    (hfirst : Integrable (fun t : ℝ => t) (normalizedComponentBlock C))
    (hsecond : Integrable (fun t : ℝ => t ^ 2) (normalizedComponentBlock C)) :
    (componentMass C).toReal * (componentBarycenter C) ^ 2 ≤
      ∫ t : ℝ, t ^ 2 ∂componentBlock C := by
  have hmass_ne_zero : componentMass C ≠ 0 := ne_of_gt R.mass_pos
  have hmass_toReal_pos : 0 < (componentMass C).toReal :=
    ENNReal.toReal_pos hmass_ne_zero R.mass_ne_top
  letI : IsProbabilityMeasure (normalizedComponentBlock C) :=
    R.normalizedComponentBlock_isProbabilityMeasure
  have hle :
      (∫ t : ℝ, t ∂normalizedComponentBlock C) ^ 2 ≤
        ∫ t : ℝ, t ^ 2 ∂normalizedComponentBlock C :=
    measure_barycenter_second_moment_le_original
      (normalizedComponentBlock C) hfirst hsecond
  rw [normalizedComponentBlock_integral_eq_barycenter R] at hle
  have hnorm :
      (∫ t : ℝ, t ^ 2 ∂normalizedComponentBlock C) =
        ((componentMass C)⁻¹).toReal *
          ∫ t : ℝ, t ^ 2 ∂componentBlock C := by
    unfold normalizedComponentBlock
    rw [integral_smul_measure]
    rw [smul_eq_mul]
  rw [hnorm] at hle
  calc
    (componentMass C).toReal * (componentBarycenter C) ^ 2
        ≤ (componentMass C).toReal *
            (((componentMass C)⁻¹).toReal *
              ∫ t : ℝ, t ^ 2 ∂componentBlock C) := by
          exact mul_le_mul_of_nonneg_left hle (le_of_lt hmass_toReal_pos)
    _ = ∫ t : ℝ, t ^ 2 ∂componentBlock C := by
          rw [ENNReal.toReal_inv]
          field_simp [hmass_toReal_pos.ne']

/-- Real-measure second-moment nonincrease for the component replacement. -/
theorem componentReplacementMeasure_secondMoment_le_realMeasure
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C) :
    (∫ t : ℝ, t ^ 2 ∂componentReplacementMeasure C) ≤
      ∫ t : ℝ, t ^ 2 ∂realMeasure μ := by
  let f : ℝ → ℝ := fun t => t ^ 2
  have houtside_int : Integrable f ((realMeasure μ).restrict C.intervalᶜ) :=
    outsideComponent_secondMoment_integrable C
  have hblock_int : Integrable f (componentBlock C) :=
    componentBlock_secondMoment_integrable C
  have hdirac_int :
      Integrable f (componentMass C • Measure.dirac (componentBarycenter C)) := by
    exact (integrable_dirac (by simp [f])).smul_measure (measure_ne_top _ _)
  have hreplacement :
      (∫ t : ℝ, f t ∂componentReplacementMeasure C) =
        (∫ t : ℝ, f t ∂(realMeasure μ).restrict C.intervalᶜ) +
          (componentMass C).toReal * (componentBarycenter C) ^ 2 := by
    rw [componentReplacementMeasure_def]
    rw [integral_add_measure houtside_int hdirac_int]
    rw [integral_smul_measure]
    rw [integral_dirac]
    simp [f, smul_eq_mul]
  have hsplit :
      (realMeasure μ).restrict C.intervalᶜ + componentBlock C =
        realMeasure μ := by
    unfold componentBlock
    exact Measure.restrict_compl_add_restrict C.measurableSet_interval
  have horiginal :
      (∫ t : ℝ, f t ∂realMeasure μ) =
        (∫ t : ℝ, f t ∂(realMeasure μ).restrict C.intervalᶜ) +
          ∫ t : ℝ, f t ∂componentBlock C := by
    calc
      (∫ t : ℝ, f t ∂realMeasure μ)
          = ∫ t : ℝ, f t ∂((realMeasure μ).restrict C.intervalᶜ +
              componentBlock C) := by rw [hsplit]
      _ = (∫ t : ℝ, f t ∂(realMeasure μ).restrict C.intervalᶜ) +
            ∫ t : ℝ, f t ∂componentBlock C := by
              rw [integral_add_measure houtside_int hblock_int]
  have hfirst :
      Integrable (fun t : ℝ => t) (normalizedComponentBlock C) :=
    R.normalizedComponentBlock_firstMoment_integrable_of_componentBlock
      (componentBlock_firstMoment_integrable C)
  have hsecond :
      Integrable (fun t : ℝ => t ^ 2) (normalizedComponentBlock C) :=
    R.normalizedComponentBlock_secondMoment_integrable_of_componentBlock
      (componentBlock_secondMoment_integrable C)
  have hblock_le :
      (componentMass C).toReal * (componentBarycenter C) ^ 2 ≤
        ∫ t : ℝ, t ^ 2 ∂componentBlock C :=
    componentBlock_barycenter_secondMoment_le_original R hfirst hsecond
  rw [hreplacement, horiginal]
  simpa [f, add_comm, add_left_comm, add_assoc] using
    add_le_add_left hblock_le
      (∫ t : ℝ, f t ∂(realMeasure μ).restrict C.intervalᶜ)

/--
If the real replacement has the same second moment as the original measure,
then the component-block barycenter inequality is an equality.
-/
theorem componentBlock_secondMoment_eq_of_replacement_secondMoment_eq
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (heq :
      (∫ t : ℝ, t ^ 2 ∂componentReplacementMeasure C) =
        ∫ t : ℝ, t ^ 2 ∂realMeasure μ) :
    (componentMass C).toReal * (componentBarycenter C) ^ 2 =
      ∫ t : ℝ, t ^ 2 ∂componentBlock C := by
  let f : ℝ → ℝ := fun t => t ^ 2
  have houtside_int : Integrable f ((realMeasure μ).restrict C.intervalᶜ) :=
    outsideComponent_secondMoment_integrable C
  have hblock_int : Integrable f (componentBlock C) :=
    componentBlock_secondMoment_integrable C
  have hdirac_int :
      Integrable f (componentMass C • Measure.dirac (componentBarycenter C)) := by
    exact (integrable_dirac (by simp [f])).smul_measure (measure_ne_top _ _)
  have hreplacement :
      (∫ t : ℝ, f t ∂componentReplacementMeasure C) =
        (∫ t : ℝ, f t ∂(realMeasure μ).restrict C.intervalᶜ) +
          (componentMass C).toReal * (componentBarycenter C) ^ 2 := by
    rw [componentReplacementMeasure_def]
    rw [integral_add_measure houtside_int hdirac_int]
    rw [integral_smul_measure]
    rw [integral_dirac]
    simp [f, smul_eq_mul]
  have hsplit :
      (realMeasure μ).restrict C.intervalᶜ + componentBlock C =
        realMeasure μ := by
    unfold componentBlock
    exact Measure.restrict_compl_add_restrict C.measurableSet_interval
  have horiginal :
      (∫ t : ℝ, f t ∂realMeasure μ) =
        (∫ t : ℝ, f t ∂(realMeasure μ).restrict C.intervalᶜ) +
          ∫ t : ℝ, f t ∂componentBlock C := by
    calc
      (∫ t : ℝ, f t ∂realMeasure μ)
          = ∫ t : ℝ, f t ∂((realMeasure μ).restrict C.intervalᶜ +
              componentBlock C) := by rw [hsplit]
      _ = (∫ t : ℝ, f t ∂(realMeasure μ).restrict C.intervalᶜ) +
            ∫ t : ℝ, f t ∂componentBlock C := by
              rw [integral_add_measure houtside_int hblock_int]
  have hsum :
      (∫ t : ℝ, f t ∂(realMeasure μ).restrict C.intervalᶜ) +
          (componentMass C).toReal * (componentBarycenter C) ^ 2 =
        (∫ t : ℝ, f t ∂(realMeasure μ).restrict C.intervalᶜ) +
          ∫ t : ℝ, f t ∂componentBlock C := by
    calc
      (∫ t : ℝ, f t ∂(realMeasure μ).restrict C.intervalᶜ) +
          (componentMass C).toReal * (componentBarycenter C) ^ 2
          = ∫ t : ℝ, f t ∂componentReplacementMeasure C := by
              rw [hreplacement]
      _ = ∫ t : ℝ, f t ∂realMeasure μ := heq
      _ = (∫ t : ℝ, f t ∂(realMeasure μ).restrict C.intervalᶜ) +
          ∫ t : ℝ, f t ∂componentBlock C := horiginal
  exact add_left_cancel hsum

/-- Concrete secondary objective nonincrease for the subtype replacement
probability. -/
theorem unitIntervalSecondMomentObjective_componentReplacement_nonincrease
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C)
    (hmass_unit :
      componentReplacementMeasure C (Icc (-1 : ℝ) 1) = 1)
    (hsupport :
      ∀ᵐ x ∂componentReplacementMeasure C, x ∈ Icc (-1 : ℝ) 1) :
    unitIntervalSecondMomentObjective (componentReplacementProbability C hmass_unit) ≤
      unitIntervalSecondMomentObjective μ := by
  rw [unitIntervalSecondMomentObjective_eq_realMeasure]
  rw [unitIntervalSecondMomentObjective_eq_realMeasure]
  rw [realMeasure_componentReplacementProbability_eq_of_ae_mem_unitInterval
    C hmass_unit hsupport]
  exact componentReplacementMeasure_secondMoment_le_realMeasure R

/--
Concrete secondary equality implies equality in the component-block
second-moment inequality.
-/
theorem componentBlock_secondMoment_eq_of_unitIntervalSecondMomentObjective_eq
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (hmass_unit :
      componentReplacementMeasure C (Icc (-1 : ℝ) 1) = 1)
    (hsupport :
      ∀ᵐ x ∂componentReplacementMeasure C, x ∈ Icc (-1 : ℝ) 1)
    (heq :
      unitIntervalSecondMomentObjective (componentReplacementProbability C hmass_unit) =
        unitIntervalSecondMomentObjective μ) :
    (componentMass C).toReal * (componentBarycenter C) ^ 2 =
      ∫ t : ℝ, t ^ 2 ∂componentBlock C := by
  have hreal :
      (∫ t : ℝ, t ^ 2 ∂componentReplacementMeasure C) =
        ∫ t : ℝ, t ^ 2 ∂realMeasure μ := by
    rw [← unitIntervalSecondMomentObjective_eq_realMeasure μ]
    rw [← heq]
    rw [unitIntervalSecondMomentObjective_eq_realMeasure]
    rw [realMeasure_componentReplacementProbability_eq_of_ae_mem_unitInterval
      C hmass_unit hsupport]
  exact componentBlock_secondMoment_eq_of_replacement_secondMoment_eq hreal

/--
Scaled component-block second-moment equality is equivalent to equality in the
normalized probability block's variance inequality.
-/
theorem normalizedComponentBlock_secondMoment_eq_barycenter_sq_of_componentBlock_eq
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C)
    (heq :
      (componentMass C).toReal * (componentBarycenter C) ^ 2 =
        ∫ t : ℝ, t ^ 2 ∂componentBlock C) :
    (∫ t : ℝ, t ^ 2 ∂normalizedComponentBlock C) =
      (componentBarycenter C) ^ 2 := by
  have hmass_ne_zero : componentMass C ≠ 0 := ne_of_gt R.mass_pos
  have hmass_toReal_pos : 0 < (componentMass C).toReal :=
    ENNReal.toReal_pos hmass_ne_zero R.mass_ne_top
  have hnorm :
      (∫ t : ℝ, t ^ 2 ∂normalizedComponentBlock C) =
        ((componentMass C)⁻¹).toReal *
          ∫ t : ℝ, t ^ 2 ∂componentBlock C := by
    unfold normalizedComponentBlock
    rw [integral_smul_measure]
    rw [smul_eq_mul]
  rw [hnorm, ← heq]
  rw [ENNReal.toReal_inv]
  field_simp [hmass_toReal_pos.ne']

theorem measure_barycenter_second_moment_eq_imp_ae_eq_mean
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hfirst : Integrable (fun t : ℝ => t) μ)
    (hsecond : Integrable (fun t : ℝ => t ^ 2) μ)
    (heq : (∫ t : ℝ, t ^ 2 ∂μ) = (∫ t : ℝ, t ∂μ) ^ 2) :
    (fun t : ℝ => t) =ᵐ[μ] fun _ : ℝ => ∫ t : ℝ, t ∂μ := by
  let m : ℝ := ∫ t : ℝ, t ∂μ
  have hlin : Integrable (fun t : ℝ => 2 * m * t) μ :=
    hfirst.const_mul (2 * m)
  have hsub : Integrable (fun t : ℝ => t ^ 2 - 2 * m * t) μ :=
    hsecond.sub hlin
  have hconst : Integrable (fun _ : ℝ => m ^ 2) μ :=
    integrable_const (m ^ 2)
  have hcenter_int : Integrable (fun t : ℝ => (t - m) ^ 2) μ := by
    refine (hsub.add hconst).congr ?_
    filter_upwards with t
    change (t ^ 2 - 2 * m * t) + m ^ 2 = (t - m) ^ 2
    ring
  have hidentity :
      (∫ t : ℝ, (t - m) ^ 2 ∂μ) =
        (∫ t : ℝ, t ^ 2 ∂μ) - m ^ 2 := by
    calc
      (∫ t : ℝ, (t - m) ^ 2 ∂μ)
          = ∫ t : ℝ, (t ^ 2 - 2 * m * t + m ^ 2) ∂μ := by
            apply integral_congr_ae
            filter_upwards with t
            ring
      _ = ∫ t : ℝ, (t ^ 2 - 2 * m * t) ∂μ +
          ∫ _ : ℝ, m ^ 2 ∂μ := by
            rw [integral_add hsub hconst]
      _ = ((∫ t : ℝ, t ^ 2 ∂μ) - ∫ t : ℝ, 2 * m * t ∂μ) +
          ∫ _ : ℝ, m ^ 2 ∂μ := by
            rw [integral_sub hsecond hlin]
      _ = (∫ t : ℝ, t ^ 2 ∂μ) -
          2 * m * (∫ t : ℝ, t ∂μ) + m ^ 2 := by
            rw [integral_const_mul, integral_const]
            simp [m]
      _ = (∫ t : ℝ, t ^ 2 ∂μ) - m ^ 2 := by
            simp [m]
            ring
  have hcenter_zero : ∫ t : ℝ, (t - m) ^ 2 ∂μ = 0 := by
    rw [hidentity]
    simp [m] at heq ⊢
    linarith
  have hsquare_zero : (fun t : ℝ => (t - m) ^ 2) =ᵐ[μ] 0 := by
    exact (integral_eq_zero_iff_of_nonneg_ae
      (show 0 ≤ᵐ[μ] fun t : ℝ => (t - m) ^ 2 by
        filter_upwards with t
        exact sq_nonneg (t - m)) hcenter_int).mp hcenter_zero
  filter_upwards [hsquare_zero] with t ht
  have hdiff : t - m = 0 := sq_eq_zero_iff.mp ht
  change t = m
  linarith

lemma measure_eq_dirac_of_ae_eq_const
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (m : ℝ)
    (h : (fun t : ℝ => t) =ᵐ[μ] fun _ : ℝ => m) :
    μ = Measure.dirac m := by
  calc
    μ = Measure.map id μ := by rw [Measure.map_id]
    _ = Measure.map (fun _ : ℝ => m) μ := by
      exact Measure.map_congr h
    _ = μ Set.univ • Measure.dirac m := by
      rw [Measure.map_const]
    _ = Measure.dirac m := by simp

lemma ae_eq_const_of_measure_eq_dirac
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {m : ℝ}
    (h : μ = Measure.dirac m) :
    (fun t : ℝ => t) =ᵐ[μ] fun _ : ℝ => m := by
  rw [h]
  rw [MeasureTheory.ae_dirac_eq]
  exact Filter.eventually_pure.2 rfl

theorem ComponentReplacement.normalizedComponentBlock_ae_eq_of_eq_dirac
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C) {m : ℝ}
    (hdirac : normalizedComponentBlock C = Measure.dirac m) :
    (fun t : ℝ => t) =ᵐ[normalizedComponentBlock C] fun _ : ℝ => m := by
  letI : IsProbabilityMeasure (normalizedComponentBlock C) :=
    R.normalizedComponentBlock_isProbabilityMeasure
  exact ae_eq_const_of_measure_eq_dirac (normalizedComponentBlock C) hdirac

theorem unique_support_in_component_of_support_neighborhood_zero
    {μ : ProbabilityMeasure UnitInterval1038}
    {Support component : Set ℝ}
    (hcomponent_open : IsOpen component)
    (hSupport_nhds :
      ∀ t : ℝ, t ∈ Support → ∀ U : Set ℝ,
        IsOpen U → t ∈ U → realMeasure μ U ≠ 0)
    (hzero :
      ∀ U : Set ℝ, IsOpen U → U ⊆ component → -1 ∉ U →
        realMeasure μ U = 0) :
    ∀ t : ℝ, t ∈ Support → t ∈ component → t = -1 := by
  intro t htSupport htComponent
  by_contra ht_ne
  let U : Set ℝ := component ∩ ({-1} : Set ℝ)ᶜ
  have hUopen : IsOpen U :=
    hcomponent_open.inter (isClosed_singleton.isOpen_compl)
  have htU : t ∈ U := by
    exact ⟨htComponent, by simpa using ht_ne⟩
  have hUsub : U ⊆ component := by
    intro y hy
    exact hy.1
  have hendpoint_not_mem : -1 ∉ U := by
    simp [U]
  exact (hSupport_nhds t htSupport U hUopen htU)
    (hzero U hUopen hUsub hendpoint_not_mem)

theorem component_neighborhood_zero_of_componentBlock_eq_smul_dirac_endpoint
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (hdirac : componentBlock C =
      componentMass C • Measure.dirac (-1 : ℝ)) :
    ∀ U : Set ℝ, IsOpen U → U ⊆ C.interval → -1 ∉ U →
      realMeasure μ U = 0 := by
  intro U hU hUsub hendpoint
  have hrestrict_eq :
      componentBlock C U = realMeasure μ U := by
    unfold componentBlock
    rw [Measure.restrict_apply]
    · have hinter : U ∩ C.interval = U := by
        ext x
        constructor
        · intro hx
          exact hx.1
        · intro hx
          exact ⟨hx, hUsub hx⟩
      rw [hinter]
    · exact hU.measurableSet
  have hdirac_zero : componentBlock C U = 0 := by
    rw [hdirac]
    simp [Measure.smul_apply, hendpoint]
  rw [← hrestrict_eq]
  exact hdirac_zero

/--
Concrete normalized-support form from a selected component whose non-endpoint
open sub-neighborhoods carry no realMeasure mass.
-/
theorem realMeasure_support_subset_endpoint_union_nonnegative_of_component_neighborhood_zero
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (hbaseline : Ioo (-1 : ℝ) 0 ⊆ C.interval)
    (hzero : ∀ U : Set ℝ, IsOpen U → U ⊆ C.interval → -1 ∉ U →
      realMeasure μ U = 0) :
    (realMeasure μ).support ⊆ ({-1} : Set ℝ) ∪ Icc (0 : ℝ) 1 := by
  have hunique :
      ∀ t : ℝ, t ∈ (realMeasure μ).support → t ∈ C.interval → t = -1 :=
    unique_support_in_component_of_support_neighborhood_zero
      (by simpa [PositiveComponent.interval_eq] using
        (isOpen_Ioo : IsOpen (Ioo C.left C.right)))
      (realMeasure_support_open_neighborhood_pos μ) hzero
  exact support_subset_endpoint_union_nonnegative
    (Support := (realMeasure μ).support)
    (xMinus := C.left) (xPlus := C.right)
    (realMeasure_support_subset_unitInterval μ)
    (by simpa [PositiveComponent.interval_eq] using hbaseline)
    (by
      intro t htSupport htInterval
      exact hunique t htSupport (by simpa [PositiveComponent.interval_eq] using htInterval))

/--
Concrete normalized-support form from endpoint atomization of the selected
component block.
-/
theorem realMeasure_support_subset_endpoint_union_nonnegative_of_componentBlock_eq_smul_dirac_endpoint
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (hbaseline : Ioo (-1 : ℝ) 0 ⊆ C.interval)
    (hdirac : componentBlock C = componentMass C • Measure.dirac (-1 : ℝ)) :
    (realMeasure μ).support ⊆ ({-1} : Set ℝ) ∪ Icc (0 : ℝ) 1 := by
  exact realMeasure_support_subset_endpoint_union_nonnegative_of_component_neighborhood_zero
    hbaseline
    (component_neighborhood_zero_of_componentBlock_eq_smul_dirac_endpoint hdirac)

/--
Endpoint atomization of the selected component produces a genuine endpoint atom
of the real push-forward measure.
-/
theorem realMeasure_endpoint_atom_pos_of_componentBlock_eq_smul_dirac_endpoint
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C)
    (hdirac : componentBlock C = componentMass C • Measure.dirac (-1 : ℝ)) :
    0 < realMeasure μ ({-1} : Set ℝ) := by
  have hblock_atom : componentBlock C ({-1} : Set ℝ) = componentMass C := by
    rw [hdirac]
    simp [Measure.smul_apply]
  have hle : componentBlock C ({-1} : Set ℝ) ≤ realMeasure μ ({-1} : Set ℝ) := by
    unfold componentBlock
    exact Measure.restrict_le_self ({-1} : Set ℝ)
  exact lt_of_lt_of_le (by simpa [hblock_atom] using R.mass_pos) hle

/--
Endpoint atomization of the selected component produces a genuine endpoint atom
of the original subtype probability measure.
-/
theorem unitInterval_endpoint_atom_pos_of_componentBlock_eq_smul_dirac_endpoint
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C)
    (hdirac : componentBlock C = componentMass C • Measure.dirac (-1 : ℝ)) :
    0 < (μ : Measure UnitInterval1038)
      {t : UnitInterval1038 | (t : ℝ) = -1} := by
  have hreal :=
    realMeasure_endpoint_atom_pos_of_componentBlock_eq_smul_dirac_endpoint
      R hdirac
  rw [realMeasure] at hreal
  rw [Measure.map_apply continuous_subtype_val.measurable
    (measurableSet_singleton (-1 : ℝ))] at hreal
  simpa [Set.preimage, Set.mem_singleton_iff] using hreal

theorem realMeasure_endpointRemainder_component_zero_of_componentBlock_eq_smul_dirac_endpoint
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (hdirac : componentBlock C =
      componentMass C • Measure.dirac (-1 : ℝ)) :
    (realMeasure μ).restrict ({-1} : Set ℝ)ᶜ C.interval = 0 := by
  have hzero :=
    component_neighborhood_zero_of_componentBlock_eq_smul_dirac_endpoint
      hdirac
  have hCopen : IsOpen C.interval := by
    rw [C.interval_eq]
    exact isOpen_Ioo
  have hopen : IsOpen (C.interval ∩ ({-1} : Set ℝ)ᶜ) :=
    hCopen.inter (isClosed_singleton.isOpen_compl)
  have hsub : C.interval ∩ ({-1} : Set ℝ)ᶜ ⊆ C.interval := by
    intro t ht
    exact ht.1
  have hnot : -1 ∉ C.interval ∩ ({-1} : Set ℝ)ᶜ := by
    simp
  have hzero_inter :
      realMeasure μ (C.interval ∩ ({-1} : Set ℝ)ᶜ) = 0 :=
    hzero (C.interval ∩ ({-1} : Set ℝ)ᶜ) hopen hsub hnot
  rw [Measure.restrict_apply C.measurableSet_interval]
  simpa [Set.inter_comm] using hzero_inter

theorem realMeasure_ae_endpointCompl_iff_endpointCompl_componentCompl_of_componentBlock_eq_smul_dirac_endpoint
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (hdirac : componentBlock C =
      componentMass C • Measure.dirac (-1 : ℝ)) :
    ∀ᵐ t ∂realMeasure μ,
      (t ∈ ({-1} : Set ℝ)ᶜ) ↔
        t ∈ ({-1} : Set ℝ)ᶜ ∩ C.intervalᶜ := by
  have hzero :=
    realMeasure_endpointRemainder_component_zero_of_componentBlock_eq_smul_dirac_endpoint
      hdirac
  rw [Measure.restrict_apply C.measurableSet_interval] at hzero
  rw [ae_iff]
  have hbad :
      {t : ℝ |
        ¬ (t ∈ ({-1} : Set ℝ)ᶜ ↔
          t ∈ ({-1} : Set ℝ)ᶜ ∩ C.intervalᶜ)} =
        C.interval ∩ ({-1} : Set ℝ)ᶜ := by
    ext t
    by_cases ht_endpoint : t = -1
    · simp [ht_endpoint]
    · by_cases ht_component : t ∈ C.interval
      · simp [ht_endpoint, ht_component]
      · simp [ht_endpoint, ht_component]
  simpa [hbad, Set.inter_comm] using hzero

theorem realMeasure_endpointRemainder_eq_restrict_endpointCompl_componentCompl_of_componentBlock_eq_smul_dirac_endpoint
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (hdirac : componentBlock C =
      componentMass C • Measure.dirac (-1 : ℝ)) :
    (realMeasure μ).restrict ({-1} : Set ℝ)ᶜ =
      (realMeasure μ).restrict (({-1} : Set ℝ)ᶜ ∩ C.intervalᶜ) := by
  apply Measure.restrict_congr_set
  filter_upwards [
    realMeasure_ae_endpointCompl_iff_endpointCompl_componentCompl_of_componentBlock_eq_smul_dirac_endpoint
      hdirac
  ] with t ht
  exact propext ht

theorem endpointRemainder_logKernel_integrable_of_mem_atomized_component
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    {x : ℝ}
    (hdirac : componentBlock C =
      componentMass C • Measure.dirac (-1 : ℝ))
    (hxC : x ∈ C.interval) :
    Integrable (fun t : ℝ => Real.log (1 / |x - t|))
      ((realMeasure μ).restrict ({-1} : Set ℝ)ᶜ) := by
  let f : ℝ → ℝ := fun t => Real.log (1 / |x - t|)
  let A : Set ℝ := ({-1} : Set ℝ)ᶜ ∩ C.intervalᶜ
  let S : Set ℝ := A ∩ Icc (-1 : ℝ) 1
  have hendpoint :
      (realMeasure μ).restrict ({-1} : Set ℝ)ᶜ =
        (realMeasure μ).restrict A := by
    simpa [A] using
      realMeasure_endpointRemainder_eq_restrict_endpointCompl_componentCompl_of_componentBlock_eq_smul_dirac_endpoint
        hdirac
  have hrestrict_unit :
      (realMeasure μ).restrict A = (realMeasure μ).restrict S := by
    apply Measure.restrict_congr_set
    filter_upwards [realMeasure_ae_mem_unitInterval μ] with t ht
    exact propext ⟨fun hA => ⟨hA, ht⟩, fun hS => hS.1⟩
  have hCopen : IsOpen C.interval := by
    rw [C.interval_eq]
    exact isOpen_Ioo
  let K : Set ℝ := Icc (-1 : ℝ) 1 ∩ C.intervalᶜ
  have hK : IsCompact K := by
    exact isCompact_Icc.inter_right hCopen.isClosed_compl
  have hS_meas : MeasurableSet S := by
    exact ((measurableSet_singleton (-1 : ℝ)).compl.inter
      C.measurableSet_interval.compl).inter measurableSet_Icc
  have hS_sub_K : S ⊆ K := by
    intro t ht
    exact ⟨ht.2, ht.1.2⟩
  have haway : ∀ t : ℝ, t ∈ K → x ≠ t := by
    intro t ht hxt
    have htC : t ∈ C.interval := by
      simpa [hxt] using hxC
    exact ht.2 htC
  have hcont : ContinuousOn f K :=
    logKernel_continuousOn_away haway
  have hint : IntegrableOn f S (realMeasure μ) :=
    hcont.integrableOn_of_subset_isCompact hK hS_meas hS_sub_K
      (measure_ne_top (realMeasure μ) _)
  change Integrable f ((realMeasure μ).restrict ({-1} : Set ℝ)ᶜ)
  rw [hendpoint, hrestrict_unit]
  simpa [IntegrableOn] using hint

theorem endpointRemainder_logKernel_integrable_of_baseline_punctured_atomized_component
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (hdirac : componentBlock C =
      componentMass C • Measure.dirac (-1 : ℝ))
    (hbaseline : Ioo (-1 : ℝ) 0 ⊆ C.interval) :
    ∀ x : ℝ, x ∈ BaselinePunctured →
      Integrable (fun t : ℝ => Real.log (1 / |x - t|))
        ((realMeasure μ).restrict ({-1} : Set ℝ)ᶜ) := by
  intro x hx
  rcases hx with ⟨hxBase, hxNotEndpointSet⟩
  by_cases hx_left : x < -1
  · exact endpointRemainder_logKernel_integrable_of_left_outside hx_left
  · have hx_ne_endpoint : x ≠ -1 := by
      simpa using hxNotEndpointSet
    have hx_ge_endpoint : (-1 : ℝ) ≤ x := le_of_not_gt hx_left
    have hx_gt_endpoint : (-1 : ℝ) < x :=
      lt_of_le_of_ne hx_ge_endpoint (Ne.symm hx_ne_endpoint)
    have hx_component : x ∈ C.interval :=
      hbaseline ⟨hx_gt_endpoint, hxBase.2⟩
    exact endpointRemainder_logKernel_integrable_of_mem_atomized_component
      hdirac hx_component

theorem componentBlock_eq_smul_dirac_of_normalizedComponentBlock_eq_dirac
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C)
    (hdirac : normalizedComponentBlock C = Measure.dirac (-1 : ℝ)) :
    componentBlock C = componentMass C • Measure.dirac (-1 : ℝ) := by
  have hmass_ne_zero : componentMass C ≠ 0 := ne_of_gt R.mass_pos
  have hmass_ne_top : componentMass C ≠ ⊤ := R.mass_ne_top
  ext s
  calc
    componentBlock C s =
        (componentMass C * (componentMass C)⁻¹) * componentBlock C s := by
      rw [ENNReal.mul_inv_cancel hmass_ne_zero hmass_ne_top]
      simp
    _ = componentMass C * ((componentMass C)⁻¹ * componentBlock C s) := by
      rw [mul_assoc]
    _ = componentMass C * normalizedComponentBlock C s := by
      rfl
    _ = componentMass C * Measure.dirac (-1 : ℝ) s := by
      rw [hdirac]
    _ = (componentMass C • Measure.dirac (-1 : ℝ)) s := by
      rfl

def taoVariationComponentPackage_of_component_replacement_data
    (μ : ProbabilityMeasure UnitInterval1038)
    (mean_choice : TaoVariationMeanChoice)
    (reflected : Bool)
    (translation : ℝ)
    (C : PositiveComponent μ)
    (Support : Set ℝ)
    (endpointMass xMinus xPlus : ℝ)
    (hcomponent_interval : C.interval = Ioo xMinus xPlus)
    (hbaseline : Ioo (-1 : ℝ) 0 ⊆ C.interval)
    (hsupport_bounded : Support ⊆ Icc (-1 : ℝ) 1)
    (hSupport_ae : ∀ᵐ t ∂realMeasure μ, t ∈ Support)
    (hSupport_nhds :
      ∀ t : ℝ, t ∈ Support → ∀ U : Set ℝ,
        IsOpen U → t ∈ U → realMeasure μ U ≠ 0)
    (hzero_component_neighborhood :
      ∀ U : Set ℝ, IsOpen U → U ⊆ C.interval → -1 ∉ U →
        realMeasure μ U = 0)
    (hright_endpoint_positive : 0 < xPlus)
    (hboundary_average :
      1 ≤ (xPlus + 1) * endpointMass +
        (1 - xPlus) * (1 - endpointMass))
    (hendpoint_mass :
      realMeasure μ ({-1} : Set ℝ) = ENNReal.ofReal endpointMass)
    (hendpoint_mass_nonneg : 0 ≤ endpointMass)
    (hremainder_mass_nonneg : 0 ≤ 1 - endpointMass)
    (hkernel_integrable : ∀ x : ℝ, x ∈ BaselinePunctured →
      Integrable (fun t : ℝ => Real.log (1 / |x - t|))
        ((realMeasure μ).restrict ({-1} : Set ℝ)ᶜ)) :
    TaoVariationComponentPackage (unitIntervalLogPotential μ) where
  mean_choice := mean_choice
  reflected := reflected
  translation := translation
  component := C.interval
  Support := Support
  endpointMass := endpointMass
  xMinus := xMinus
  xPlus := xPlus
  component_positive := C.interval_subset_positiveSet
  component_interval := hcomponent_interval
  baseline_inside_component := hbaseline
  support_bounded := hsupport_bounded
  unique_support_in_component := by
    have hcomponent_open : IsOpen C.interval := by
      simpa [hcomponent_interval] using (isOpen_Ioo : IsOpen (Ioo xMinus xPlus))
    exact unique_support_in_component_of_support_neighborhood_zero
      hcomponent_open hSupport_nhds hzero_component_neighborhood
  right_endpoint_positive := hright_endpoint_positive
  boundary_average := hboundary_average
  remainder := (realMeasure μ).restrict ({-1} : Set ℝ)ᶜ
  remainder_support_in_support :=
    realMeasure_endpointRemainder_support_in_support μ Support hSupport_ae
  remainder_no_endpoint := realMeasure_endpointRemainder_no_endpoint μ
  remainder_mass :=
    realMeasure_endpointRemainder_mass μ hendpoint_mass hendpoint_mass_nonneg
  remainder_mass_nonneg := hremainder_mass_nonneg
  kernel_integrable := hkernel_integrable
  potential_decomposition_lower :=
    unitIntervalLogPotential_endpointRemainder_potential_decomposition_lower
      μ hendpoint_mass hendpoint_mass_nonneg hkernel_integrable

def taoVariationComponentPackage_of_realSupport_component_atomization_data
    (μ : ProbabilityMeasure UnitInterval1038)
    (mean_choice : TaoVariationMeanChoice)
    (reflected : Bool)
    (translation : ℝ)
    (C : PositiveComponent μ)
    (endpointMass xMinus xPlus : ℝ)
    (hcomponent_interval : C.interval = Ioo xMinus xPlus)
    (hbaseline : Ioo (-1 : ℝ) 0 ⊆ C.interval)
    (hsupport_bounded : (realMeasure μ).support ⊆ Icc (-1 : ℝ) 1)
    (hright_endpoint_positive : 0 < xPlus)
    (hboundary_average :
      1 ≤ (xPlus + 1) * endpointMass +
        (1 - xPlus) * (1 - endpointMass))
    (hunit_endpoint_mass :
      (μ : Measure UnitInterval1038)
        {t : UnitInterval1038 | (t : ℝ) = -1} =
          ENNReal.ofReal endpointMass)
    (hendpoint_mass_nonneg : 0 ≤ endpointMass)
    (hremainder_mass_nonneg : 0 ≤ 1 - endpointMass)
    (hkernel_integrable : ∀ x : ℝ, x ∈ BaselinePunctured →
      Integrable (fun t : ℝ => Real.log (1 / |x - t|))
        ((realMeasure μ).restrict ({-1} : Set ℝ)ᶜ))
    (hcomponent_atomized :
      componentBlock C = componentMass C • Measure.dirac (-1 : ℝ)) :
    TaoVariationComponentPackage (unitIntervalLogPotential μ) :=
  taoVariationComponentPackage_of_component_replacement_data
    μ mean_choice reflected translation C (realMeasure μ).support
    endpointMass xMinus xPlus hcomponent_interval hbaseline hsupport_bounded
    (realMeasure_ae_mem_support μ)
    (realMeasure_support_open_neighborhood_pos μ)
    (component_neighborhood_zero_of_componentBlock_eq_smul_dirac_endpoint
      hcomponent_atomized)
    hright_endpoint_positive hboundary_average
    (realMeasure_endpoint_atom_eq_of_unitInterval_endpoint_atom_eq
      μ hunit_endpoint_mass)
    hendpoint_mass_nonneg hremainder_mass_nonneg hkernel_integrable

/-- Variant of `taoVariationComponentPackage_of_realSupport_component_atomization_data`
where the support bound is filled automatically from the real pushforward of the
unit-interval measure.  The remaining explicit inputs are the genuinely
variational ones: component placement, boundary average, endpoint mass
normalization, kernel integrability, and component atomization. -/
def taoVariationComponentPackage_of_unitIntervalSupport_component_atomization_data
    (μ : ProbabilityMeasure UnitInterval1038)
    (mean_choice : TaoVariationMeanChoice)
    (reflected : Bool)
    (translation : ℝ)
    (C : PositiveComponent μ)
    (endpointMass xMinus xPlus : ℝ)
    (hcomponent_interval : C.interval = Ioo xMinus xPlus)
    (hbaseline : Ioo (-1 : ℝ) 0 ⊆ C.interval)
    (hright_endpoint_positive : 0 < xPlus)
    (hboundary_average :
      1 ≤ (xPlus + 1) * endpointMass +
        (1 - xPlus) * (1 - endpointMass))
    (hunit_endpoint_mass :
      (μ : Measure UnitInterval1038)
        {t : UnitInterval1038 | (t : ℝ) = -1} =
          ENNReal.ofReal endpointMass)
    (hendpoint_mass_nonneg : 0 ≤ endpointMass)
    (hremainder_mass_nonneg : 0 ≤ 1 - endpointMass)
    (hkernel_integrable : ∀ x : ℝ, x ∈ BaselinePunctured →
      Integrable (fun t : ℝ => Real.log (1 / |x - t|))
        ((realMeasure μ).restrict ({-1} : Set ℝ)ᶜ))
    (hcomponent_atomized :
      componentBlock C = componentMass C • Measure.dirac (-1 : ℝ)) :
    TaoVariationComponentPackage (unitIntervalLogPotential μ) :=
  taoVariationComponentPackage_of_realSupport_component_atomization_data
    μ mean_choice reflected translation C endpointMass xMinus xPlus
    hcomponent_interval hbaseline (realMeasure_support_subset_unitInterval μ)
    hright_endpoint_positive hboundary_average hunit_endpoint_mass
    hendpoint_mass_nonneg hremainder_mass_nonneg hkernel_integrable
    hcomponent_atomized

/-- Variant where component atomization is supplied in normalized form.  This is
the natural output of the barycenter/secondary-minimizer rigidity argument, and
the scaled component-block statement is derived internally. -/
def taoVariationComponentPackage_of_unitIntervalSupport_normalized_atomization_data
    (μ : ProbabilityMeasure UnitInterval1038)
    (mean_choice : TaoVariationMeanChoice)
    (reflected : Bool)
    (translation : ℝ)
    (C : PositiveComponent μ)
    (R : ComponentReplacement μ C)
    (endpointMass xMinus xPlus : ℝ)
    (hcomponent_interval : C.interval = Ioo xMinus xPlus)
    (hbaseline : Ioo (-1 : ℝ) 0 ⊆ C.interval)
    (hright_endpoint_positive : 0 < xPlus)
    (hboundary_average :
      1 ≤ (xPlus + 1) * endpointMass +
        (1 - xPlus) * (1 - endpointMass))
    (hunit_endpoint_mass :
      (μ : Measure UnitInterval1038)
        {t : UnitInterval1038 | (t : ℝ) = -1} =
          ENNReal.ofReal endpointMass)
    (hendpoint_mass_nonneg : 0 ≤ endpointMass)
    (hremainder_mass_nonneg : 0 ≤ 1 - endpointMass)
    (hkernel_integrable : ∀ x : ℝ, x ∈ BaselinePunctured →
      Integrable (fun t : ℝ => Real.log (1 / |x - t|))
        ((realMeasure μ).restrict ({-1} : Set ℝ)ᶜ))
    (hnormalized_atomized :
      normalizedComponentBlock C = Measure.dirac (-1 : ℝ)) :
    TaoVariationComponentPackage (unitIntervalLogPotential μ) :=
  taoVariationComponentPackage_of_unitIntervalSupport_component_atomization_data
    μ mean_choice reflected translation C endpointMass xMinus xPlus
    hcomponent_interval hbaseline hright_endpoint_positive hboundary_average
    hunit_endpoint_mass hendpoint_mass_nonneg hremainder_mass_nonneg
    hkernel_integrable
    (componentBlock_eq_smul_dirac_of_normalizedComponentBlock_eq_dirac
      R hnormalized_atomized)

/-- Canonical-endpoint-mass version of the package constructor.  The endpoint
mass is no longer an arbitrary real parameter: it is the real value of the
endpoint atom of the subtype measure, so its endpoint equality, nonnegativity,
and remainder nonnegativity are filled automatically. -/
def taoVariationComponentPackage_of_canonicalEndpointMass_normalized_atomization_data
    (μ : ProbabilityMeasure UnitInterval1038)
    (mean_choice : TaoVariationMeanChoice)
    (reflected : Bool)
    (translation : ℝ)
    (C : PositiveComponent μ)
    (R : ComponentReplacement μ C)
    (xMinus xPlus : ℝ)
    (hcomponent_interval : C.interval = Ioo xMinus xPlus)
    (hbaseline : Ioo (-1 : ℝ) 0 ⊆ C.interval)
    (hright_endpoint_positive : 0 < xPlus)
    (hboundary_average :
      1 ≤ (xPlus + 1) *
          (((μ : Measure UnitInterval1038)
            {t : UnitInterval1038 | (t : ℝ) = -1}).toReal) +
        (1 - xPlus) *
          (1 -
            (((μ : Measure UnitInterval1038)
              {t : UnitInterval1038 | (t : ℝ) = -1}).toReal)))
    (hkernel_integrable : ∀ x : ℝ, x ∈ BaselinePunctured →
      Integrable (fun t : ℝ => Real.log (1 / |x - t|))
        ((realMeasure μ).restrict ({-1} : Set ℝ)ᶜ))
    (hnormalized_atomized :
      normalizedComponentBlock C = Measure.dirac (-1 : ℝ)) :
    TaoVariationComponentPackage (unitIntervalLogPotential μ) :=
  taoVariationComponentPackage_of_unitIntervalSupport_normalized_atomization_data
    μ mean_choice reflected translation C R
    (((μ : Measure UnitInterval1038)
      {t : UnitInterval1038 | (t : ℝ) = -1}).toReal)
    xMinus xPlus hcomponent_interval hbaseline hright_endpoint_positive
    hboundary_average
    (unitInterval_endpoint_atom_eq_ofReal_toReal μ)
    (unitInterval_endpoint_atom_toReal_nonneg μ)
    (unitInterval_endpoint_atom_remainderMass_nonneg μ)
    hkernel_integrable hnormalized_atomized

/-- Fully mechanical endpoint-remainder version of the canonical constructor:
once the component contains the baseline interval and normalized atomization has
identified the component block with the endpoint atom, kernel integrability on
`BaselinePunctured` is generated internally. -/
def taoVariationComponentPackage_of_canonicalEndpointMass_normalized_atomization_baseline_data
    (μ : ProbabilityMeasure UnitInterval1038)
    (mean_choice : TaoVariationMeanChoice)
    (reflected : Bool)
    (translation : ℝ)
    (C : PositiveComponent μ)
    (R : ComponentReplacement μ C)
    (xMinus xPlus : ℝ)
    (hcomponent_interval : C.interval = Ioo xMinus xPlus)
    (hbaseline : Ioo (-1 : ℝ) 0 ⊆ C.interval)
    (hright_endpoint_positive : 0 < xPlus)
    (hboundary_average :
      1 ≤ (xPlus + 1) *
          (((μ : Measure UnitInterval1038)
            {t : UnitInterval1038 | (t : ℝ) = -1}).toReal) +
        (1 - xPlus) *
          (1 -
            (((μ : Measure UnitInterval1038)
              {t : UnitInterval1038 | (t : ℝ) = -1}).toReal)))
    (hnormalized_atomized :
      normalizedComponentBlock C = Measure.dirac (-1 : ℝ)) :
    TaoVariationComponentPackage (unitIntervalLogPotential μ) :=
  taoVariationComponentPackage_of_canonicalEndpointMass_normalized_atomization_data
    μ mean_choice reflected translation C R xMinus xPlus hcomponent_interval
    hbaseline hright_endpoint_positive hboundary_average
    (endpointRemainder_logKernel_integrable_of_baseline_punctured_atomized_component
      (componentBlock_eq_smul_dirac_of_normalizedComponentBlock_eq_dirac
        R hnormalized_atomized)
      hbaseline)
    hnormalized_atomized

theorem measure_barycenter_second_moment_eq_imp_eq_dirac_at_mean
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hfirst : Integrable (fun t : ℝ => t) μ)
    (hsecond : Integrable (fun t : ℝ => t ^ 2) μ)
    (heq : (∫ t : ℝ, t ^ 2 ∂μ) = (∫ t : ℝ, t ∂μ) ^ 2) :
    μ = MeasureTheory.Measure.dirac (∫ t : ℝ, t ∂μ) := by
  exact measure_eq_dirac_of_ae_eq_const μ (∫ t : ℝ, t ∂μ)
    (measure_barycenter_second_moment_eq_imp_ae_eq_mean μ
      hfirst hsecond heq)

/--
Variance rigidity for the normalized component block: equality in the
second-moment drop forces the normalized block to be a Dirac mass at its
barycenter.
-/
theorem normalizedComponentBlock_eq_dirac_componentBarycenter_of_componentBlock_secondMoment_eq
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C)
    (heq :
      (componentMass C).toReal * (componentBarycenter C) ^ 2 =
        ∫ t : ℝ, t ^ 2 ∂componentBlock C) :
    normalizedComponentBlock C = Measure.dirac (componentBarycenter C) := by
  letI : IsProbabilityMeasure (normalizedComponentBlock C) :=
    R.normalizedComponentBlock_isProbabilityMeasure
  have hfirst :
      Integrable (fun t : ℝ => t) (normalizedComponentBlock C) :=
    R.normalizedComponentBlock_firstMoment_integrable_of_componentBlock
      (componentBlock_firstMoment_integrable C)
  have hsecond :
      Integrable (fun t : ℝ => t ^ 2) (normalizedComponentBlock C) :=
    R.normalizedComponentBlock_secondMoment_integrable_of_componentBlock
      (componentBlock_secondMoment_integrable C)
  have hmean :
      (∫ t : ℝ, t ∂normalizedComponentBlock C) = componentBarycenter C :=
    normalizedComponentBlock_integral_eq_barycenter R
  have hvar :
      (∫ t : ℝ, t ^ 2 ∂normalizedComponentBlock C) =
        (∫ t : ℝ, t ∂normalizedComponentBlock C) ^ 2 := by
    rw [hmean]
    exact normalizedComponentBlock_secondMoment_eq_barycenter_sq_of_componentBlock_eq
      R heq
  simpa [hmean] using
    measure_barycenter_second_moment_eq_imp_eq_dirac_at_mean
      (normalizedComponentBlock C) hfirst hsecond hvar

/--
If the normalized component block is the Dirac mass at its barycenter, then the
barycenter lies in the selected component interval.
-/
theorem componentBarycenter_mem_interval_of_normalizedComponentBlock_eq_dirac
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C)
    (hdirac : normalizedComponentBlock C = Measure.dirac (componentBarycenter C)) :
    componentBarycenter C ∈ C.interval := by
  have hmem : ∀ᵐ t : ℝ ∂normalizedComponentBlock C, t ∈ C.interval :=
    normalizedComponentBlock_ae_mem_interval R
  rw [hdirac] at hmem
  rw [MeasureTheory.ae_dirac_eq] at hmem
  exact hmem

/--
If the normalized component block is a Dirac mass at the component barycenter,
then that barycenter is a support point of the original real measure.
-/
theorem componentBarycenter_mem_realMeasure_support_of_normalizedComponentBlock_eq_dirac
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (hdirac : normalizedComponentBlock C = Measure.dirac (componentBarycenter C)) :
    componentBarycenter C ∈ (realMeasure μ).support := by
  rw [Measure.mem_support_iff_forall]
  intro U hU
  have hcenterU : componentBarycenter C ∈ U := mem_of_mem_nhds hU
  by_contra hnot_pos
  have hzero_real : realMeasure μ U = 0 := by
    exact le_antisymm (le_of_not_gt hnot_pos) bot_le
  have hzero_block : componentBlock C U = 0 := by
    exact le_antisymm
      (le_trans (Measure.restrict_le_self U) (le_of_eq hzero_real)) bot_le
  have hzero_norm : normalizedComponentBlock C U = 0 := by
    unfold normalizedComponentBlock
    rw [Measure.smul_apply, hzero_block]
    simp
  have hone_norm : normalizedComponentBlock C U = 1 := by
    rw [hdirac]
    simp [hcenterU]
  exact zero_ne_one (hzero_norm.symm.trans hone_norm)

/--
Endpoint identification after normalized atomization: once the Dirac barycenter
is known to be the only support point in the selected component, the barycenter
is the endpoint atom `-1`.
-/
theorem componentBarycenter_eq_endpoint_of_normalizedComponentBlock_eq_dirac
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C)
    (hdirac : normalizedComponentBlock C = Measure.dirac (componentBarycenter C))
    (hunique : ∀ t : ℝ, t ∈ (realMeasure μ).support → t ∈ C.interval → t = -1) :
    componentBarycenter C = -1 := by
  exact hunique (componentBarycenter C)
    (componentBarycenter_mem_realMeasure_support_of_normalizedComponentBlock_eq_dirac
      hdirac)
    (componentBarycenter_mem_interval_of_normalizedComponentBlock_eq_dirac R hdirac)

/--
Normalized atomization at the endpoint: moment equality gives a Dirac mass at
the component barycenter, and endpoint uniqueness identifies that barycenter
with `-1`.
-/
theorem normalizedComponentBlock_eq_dirac_endpoint_of_componentBlock_secondMoment_eq
    {μ : ProbabilityMeasure UnitInterval1038} {C : PositiveComponent μ}
    (R : ComponentReplacement μ C)
    (heq :
      (componentMass C).toReal * (componentBarycenter C) ^ 2 =
        ∫ t : ℝ, t ^ 2 ∂componentBlock C)
    (hunique : ∀ t : ℝ, t ∈ (realMeasure μ).support → t ∈ C.interval → t = -1) :
    normalizedComponentBlock C = Measure.dirac (-1 : ℝ) := by
  have hdirac_bary :
      normalizedComponentBlock C = Measure.dirac (componentBarycenter C) :=
    normalizedComponentBlock_eq_dirac_componentBarycenter_of_componentBlock_secondMoment_eq
      R heq
  have hbary_endpoint : componentBarycenter C = -1 :=
    componentBarycenter_eq_endpoint_of_normalizedComponentBlock_eq_dirac
      R hdirac_bary hunique
  simpa [hbary_endpoint] using hdirac_bary

/-!
## Coupling the variance selector to barycenter rigidity

The next theorem connects the abstract secondary-minimizer framework to the
continuous variance equality statement above.  This is the formal version of
the step: if barycenter replacement is admissible, does not increase the
primary objective, and cannot strictly reduce the selected variance, then the
replaced probability block must already be a Dirac mass at its barycenter.
-/

theorem secondary_minimizer_replacement_forces_block_dirac
    {α : Type*} [TopologicalSpace α]
    {P : SecondarySelectorProblem α} {a b : α}
    (ha : IsSecondaryMinimizingPrimaryMinimizer P a)
    (hb_adm : P.Primary.Admissible b)
    (hb_primary : P.Primary.objective b ≤ P.Primary.objective a)
    (hb_secondary_le : P.secondaryObjective b ≤ P.secondaryObjective a)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hfirst : Integrable (fun t : ℝ => t) μ)
    (hsecond : Integrable (fun t : ℝ => t ^ 2) μ)
    (hsecondary_eq_to_second_moment_eq :
      P.secondaryObjective b = P.secondaryObjective a →
        (∫ t : ℝ, t ^ 2 ∂μ) = (∫ t : ℝ, t ∂μ) ^ 2) :
    μ = Measure.dirac (∫ t : ℝ, t ∂μ) := by
  have hsecondary_eq :
      P.secondaryObjective b = P.secondaryObjective a :=
    secondary_minimizer_forces_replacement_rigidity ha
      hb_adm hb_primary hb_secondary_le
  exact measure_barycenter_second_moment_eq_imp_eq_dirac_at_mean μ
    hfirst hsecond (hsecondary_eq_to_second_moment_eq hsecondary_eq)

/--
Component-replacement contradiction packaged in the language of the positive
component objective.  Once a replacement object `b` represents the component
replacement potential and the outside-potential Jensen inequality is known,
a secondary-minimizing primary minimizer cannot have a strictly smaller
secondary value after replacement.
-/
theorem secondary_minimizer_no_strict_componentReplacement
    {α : Type*} [TopologicalSpace α]
    {P : SecondarySelectorProblem α} {a b : α}
    (ha : IsSecondaryMinimizingPrimaryMinimizer P a)
    (hb_adm : P.Primary.Admissible b)
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    (hobj_a :
      P.Primary.objective a =
        (volume (PositiveSet (unitIntervalLogPotential μ))).toReal)
    (hobj_b :
      P.Primary.objective b =
        (volume (PositiveSet (componentReplacementPotential C))).toReal)
    (hfinite_a : volume (PositiveSet (unitIntervalLogPotential μ)) ≠ ⊤)
    (houtside : ∀ x : ℝ, x ∉ C.interval →
      componentReplacementPotential C x ≤ unitIntervalLogPotential μ x) :
    ¬ P.secondaryObjective b < P.secondaryObjective a := by
  have hvol_le :
      volume (PositiveSet (componentReplacementPotential C)) ≤
        volume (PositiveSet (unitIntervalLogPotential μ)) :=
    componentReplacement_objective_le_of_outside_potential_le C houtside
  have hfinite_b : volume (PositiveSet (componentReplacementPotential C)) ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite_a hvol_le
  have hb_primary : P.Primary.objective b ≤ P.Primary.objective a := by
    rw [hobj_a, hobj_b]
    exact ENNReal.toReal_mono hfinite_a hvol_le
  exact no_strict_secondary_decreasing_replacement ha hb_adm hb_primary

theorem secondary_minimizer_no_strict_componentReplacement_strictOutside
    {α : Type*} [TopologicalSpace α]
    {P : SecondarySelectorProblem α} {a b : α}
    (ha : IsSecondaryMinimizingPrimaryMinimizer P a)
    (hb_adm : P.Primary.Admissible b)
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    (hobj_a :
      P.Primary.objective a =
        (volume (PositiveSet (unitIntervalLogPotential μ))).toReal)
    (hobj_b :
      P.Primary.objective b =
        (volume (PositiveSet (componentReplacementPotential C))).toReal)
    (hfinite_a : volume (PositiveSet (unitIntervalLogPotential μ)) ≠ ⊤)
    (houtside : ∀ x : ℝ, StrictOutsideComponent C x →
      componentReplacementPotential C x ≤ unitIntervalLogPotential μ x) :
    ¬ P.secondaryObjective b < P.secondaryObjective a := by
  have hvol_le :
      volume (PositiveSet (componentReplacementPotential C)) ≤
        volume (PositiveSet (unitIntervalLogPotential μ)) :=
    componentReplacement_objective_le_of_strictOutside_potential_le C houtside
  have hfinite_b : volume (PositiveSet (componentReplacementPotential C)) ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite_a hvol_le
  have hb_primary : P.Primary.objective b ≤ P.Primary.objective a := by
    rw [hobj_a, hobj_b]
    exact ENNReal.toReal_mono hfinite_a hvol_le
  exact no_strict_secondary_decreasing_replacement ha hb_adm hb_primary

theorem secondary_minimizer_no_strict_componentReplacement_ennreal_strictOutside
    {α : Type*} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α} {a b : α}
    (ha : IsSecondaryMinimizingPrimaryMinimizerENNReal P a)
    (hb_adm : P.Primary.Admissible b)
    {μ : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ)
    (hobj_a :
      P.Primary.objective a =
        volume (PositiveSet (unitIntervalLogPotential μ)))
    (hobj_b :
      P.Primary.objective b =
        volume (PositiveSet (componentReplacementPotential C)))
    (houtside : ∀ x : ℝ, StrictOutsideComponent C x →
      componentReplacementPotential C x ≤ unitIntervalLogPotential μ x) :
    ¬ P.secondaryObjective b < P.secondaryObjective a := by
  have hvol_le :
      volume (PositiveSet (componentReplacementPotential C)) ≤
        volume (PositiveSet (unitIntervalLogPotential μ)) :=
    componentReplacement_objective_le_of_strictOutside_potential_le C houtside
  have hb_primary : P.Primary.objective b ≤ P.Primary.objective a := by
    rw [hobj_a, hobj_b]
    exact hvol_le
  exact no_strict_secondary_decreasing_replacement_ennreal ha hb_adm hb_primary

/--
Full abstract component-replacement rigidity package.  If a component
replacement is admissible, has no larger positive-set objective, and its
secondary value is no larger, then the probability block whose variance is
being tested must already be a Dirac mass at its barycenter.
-/
theorem secondary_minimizer_componentReplacement_forces_block_dirac
    {α : Type*} [TopologicalSpace α]
    {P : SecondarySelectorProblem α} {a b : α}
    (ha : IsSecondaryMinimizingPrimaryMinimizer P a)
    (hb_adm : P.Primary.Admissible b)
    {μ0 : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ0)
    (hobj_a :
      P.Primary.objective a =
        (volume (PositiveSet (unitIntervalLogPotential μ0))).toReal)
    (hobj_b :
      P.Primary.objective b =
        (volume (PositiveSet (componentReplacementPotential C))).toReal)
    (hfinite_a : volume (PositiveSet (unitIntervalLogPotential μ0)) ≠ ⊤)
    (houtside : ∀ x : ℝ, x ∉ C.interval →
      componentReplacementPotential C x ≤ unitIntervalLogPotential μ0 x)
    (hb_secondary_le : P.secondaryObjective b ≤ P.secondaryObjective a)
    (block : Measure ℝ) [IsProbabilityMeasure block]
    (hfirst : Integrable (fun t : ℝ => t) block)
    (hsecond : Integrable (fun t : ℝ => t ^ 2) block)
    (hsecondary_eq_to_second_moment_eq :
      P.secondaryObjective b = P.secondaryObjective a →
        (∫ t : ℝ, t ^ 2 ∂block) = (∫ t : ℝ, t ∂block) ^ 2) :
    block = Measure.dirac (∫ t : ℝ, t ∂block) := by
  have hvol_le :
      volume (PositiveSet (componentReplacementPotential C)) ≤
        volume (PositiveSet (unitIntervalLogPotential μ0)) :=
    componentReplacement_objective_le_of_outside_potential_le C houtside
  have hfinite_b : volume (PositiveSet (componentReplacementPotential C)) ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite_a hvol_le
  have hb_primary : P.Primary.objective b ≤ P.Primary.objective a := by
    rw [hobj_a, hobj_b]
    exact ENNReal.toReal_mono hfinite_a hvol_le
  exact secondary_minimizer_replacement_forces_block_dirac ha hb_adm
    hb_primary hb_secondary_le block hfirst hsecond
    hsecondary_eq_to_second_moment_eq

theorem secondary_minimizer_replacement_forces_block_dirac_ennreal
    {α : Type*} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α} {a b : α}
    (ha : IsSecondaryMinimizingPrimaryMinimizerENNReal P a)
    (hb_adm : P.Primary.Admissible b)
    (hb_primary : P.Primary.objective b ≤ P.Primary.objective a)
    (hb_secondary_le : P.secondaryObjective b ≤ P.secondaryObjective a)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hfirst : Integrable (fun t : ℝ => t) μ)
    (hsecond : Integrable (fun t : ℝ => t ^ 2) μ)
    (hsecondary_eq_to_second_moment_eq :
      P.secondaryObjective b = P.secondaryObjective a →
        (∫ t : ℝ, t ^ 2 ∂μ) = (∫ t : ℝ, t ∂μ) ^ 2) :
    μ = Measure.dirac (∫ t : ℝ, t ∂μ) := by
  have hsecondary_eq :
      P.secondaryObjective b = P.secondaryObjective a :=
    secondary_minimizer_forces_replacement_rigidity_ennreal ha
      hb_adm hb_primary hb_secondary_le
  exact measure_barycenter_second_moment_eq_imp_eq_dirac_at_mean μ
    hfirst hsecond (hsecondary_eq_to_second_moment_eq hsecondary_eq)

theorem secondary_minimizer_componentReplacement_forces_block_dirac_strictOutside
    {α : Type*} [TopologicalSpace α]
    {P : SecondarySelectorProblem α} {a b : α}
    (ha : IsSecondaryMinimizingPrimaryMinimizer P a)
    (hb_adm : P.Primary.Admissible b)
    {μ0 : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ0)
    (hobj_a :
      P.Primary.objective a =
        (volume (PositiveSet (unitIntervalLogPotential μ0))).toReal)
    (hobj_b :
      P.Primary.objective b =
        (volume (PositiveSet (componentReplacementPotential C))).toReal)
    (hfinite_a : volume (PositiveSet (unitIntervalLogPotential μ0)) ≠ ⊤)
    (houtside : ∀ x : ℝ, StrictOutsideComponent C x →
      componentReplacementPotential C x ≤ unitIntervalLogPotential μ0 x)
    (hb_secondary_le : P.secondaryObjective b ≤ P.secondaryObjective a)
    (block : Measure ℝ) [IsProbabilityMeasure block]
    (hfirst : Integrable (fun t : ℝ => t) block)
    (hsecond : Integrable (fun t : ℝ => t ^ 2) block)
    (hsecondary_eq_to_second_moment_eq :
      P.secondaryObjective b = P.secondaryObjective a →
        (∫ t : ℝ, t ^ 2 ∂block) = (∫ t : ℝ, t ∂block) ^ 2) :
    block = Measure.dirac (∫ t : ℝ, t ∂block) := by
  have hvol_le :
      volume (PositiveSet (componentReplacementPotential C)) ≤
        volume (PositiveSet (unitIntervalLogPotential μ0)) :=
    componentReplacement_objective_le_of_strictOutside_potential_le C houtside
  have hfinite_b : volume (PositiveSet (componentReplacementPotential C)) ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite_a hvol_le
  have hb_primary : P.Primary.objective b ≤ P.Primary.objective a := by
    rw [hobj_a, hobj_b]
    exact ENNReal.toReal_mono hfinite_a hvol_le
  exact secondary_minimizer_replacement_forces_block_dirac ha hb_adm
    hb_primary hb_secondary_le block hfirst hsecond
    hsecondary_eq_to_second_moment_eq

theorem secondary_minimizer_componentReplacement_forces_block_dirac_ennreal_strictOutside
    {α : Type*} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α} {a b : α}
    (ha : IsSecondaryMinimizingPrimaryMinimizerENNReal P a)
    (hb_adm : P.Primary.Admissible b)
    {μ0 : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ0)
    (hobj_a :
      P.Primary.objective a =
        volume (PositiveSet (unitIntervalLogPotential μ0)))
    (hobj_b :
      P.Primary.objective b =
        volume (PositiveSet (componentReplacementPotential C)))
    (houtside : ∀ x : ℝ, StrictOutsideComponent C x →
      componentReplacementPotential C x ≤ unitIntervalLogPotential μ0 x)
    (hb_secondary_le : P.secondaryObjective b ≤ P.secondaryObjective a)
    (block : Measure ℝ) [IsProbabilityMeasure block]
    (hfirst : Integrable (fun t : ℝ => t) block)
    (hsecond : Integrable (fun t : ℝ => t ^ 2) block)
    (hsecondary_eq_to_second_moment_eq :
      P.secondaryObjective b = P.secondaryObjective a →
        (∫ t : ℝ, t ^ 2 ∂block) = (∫ t : ℝ, t ∂block) ^ 2) :
    block = Measure.dirac (∫ t : ℝ, t ∂block) := by
  have hvol_le :
      volume (PositiveSet (componentReplacementPotential C)) ≤
        volume (PositiveSet (unitIntervalLogPotential μ0)) :=
    componentReplacement_objective_le_of_strictOutside_potential_le C houtside
  have hb_primary : P.Primary.objective b ≤ P.Primary.objective a := by
    rw [hobj_a, hobj_b]
    exact hvol_le
  exact secondary_minimizer_replacement_forces_block_dirac_ennreal ha hb_adm
    hb_primary hb_secondary_le block hfirst hsecond
    hsecondary_eq_to_second_moment_eq

theorem secondary_minimizer_componentReplacement_forces_block_dirac_ennreal_smallException
    {α : Type*} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α} {a b : α}
    (ha : IsSecondaryMinimizingPrimaryMinimizerENNReal P a)
    (hb_adm : P.Primary.Admissible b)
    {μ0 : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ0)
    (R : ComponentReplacement μ0 C)
    {ε : ℝ} (hε : 0 < ε)
    (hobj_a :
      P.Primary.objective a =
        volume (PositiveSet (unitIntervalLogPotential μ0)))
    (hobj_b :
      P.Primary.objective b =
        volume (PositiveSet (componentReplacementPotential C)))
    (hsmall : ∀ η : NNReal, 0 < η →
      ∃ N : Set ℝ,
        volume N ≤ (η : ℝ≥0∞) ∧
        ∀ x : ℝ, StrictOutsideComponent C x →
          x ∉ diagonalAtomSet μ0 → x ∉ N →
            singularTailMass ε μ0 x < ∞)
    (hb_secondary_le : P.secondaryObjective b ≤ P.secondaryObjective a)
    (block : Measure ℝ) [IsProbabilityMeasure block]
    (hfirst : Integrable (fun t : ℝ => t) block)
    (hsecond : Integrable (fun t : ℝ => t ^ 2) block)
    (hsecondary_eq_to_second_moment_eq :
      P.secondaryObjective b = P.secondaryObjective a →
        (∫ t : ℝ, t ^ 2 ∂block) = (∫ t : ℝ, t ∂block) ^ 2) :
    block = Measure.dirac (∫ t : ℝ, t ∂block) := by
  have hvol_le :
      volume (PositiveSet (componentReplacementPotential C)) ≤
        volume (PositiveSet (unitIntervalLogPotential μ0)) :=
    componentReplacement_objective_le_of_forall_small_tailMass_exception
      R hε hsmall
  have hb_primary : P.Primary.objective b ≤ P.Primary.objective a := by
    rw [hobj_a, hobj_b]
    exact hvol_le
  exact secondary_minimizer_replacement_forces_block_dirac_ennreal ha hb_adm
    hb_primary hb_secondary_le block hfirst hsecond
    hsecondary_eq_to_second_moment_eq

/-!
## Translation/reflection normalization layer

Once the secondary-minimizing minimizer has the rigidity properties needed by
Tao's component argument, the reflection/translation normalization is encoded
as a map into a normalized configuration whose potential satisfies
`NormalizedEndpointPotential`.
-/

structure SecondaryMinimizerNormalization
    {α Normalized : Type} [TopologicalSpace α]
    (P : SecondarySelectorProblem α)
    (normalize : α → Normalized)
    (Potential : Normalized → ℝ → ℝ) where
  endpointForm :
    ∀ a : α, IsSecondaryMinimizingPrimaryMinimizer P a →
      NormalizedEndpointPotential (Potential (normalize a))

structure SecondaryMinimizerNormalizationENNReal
    {α Normalized : Type} [TopologicalSpace α]
    (P : SecondarySelectorProblemENNReal α)
    (normalize : α → Normalized)
    (Potential : Normalized → ℝ → ℝ) where
  endpointForm :
    ∀ a : α, IsSecondaryMinimizingPrimaryMinimizerENNReal P a →
      NormalizedEndpointPotential (Potential (normalize a))

structure TaoVariationalReductionInput
    {α Normalized : Type} [TopologicalSpace α]
    (P : SecondarySelectorProblem α)
    (normalize : α → Normalized)
    (Potential : Normalized → ℝ → ℝ) where
  reducedData :
    ∀ a : α, IsSecondaryMinimizingPrimaryMinimizer P a →
      TaoReducedPotentialData (Potential (normalize a))

structure TaoEndpointReductionInput
    {α Normalized : Type} [TopologicalSpace α]
    (P : SecondarySelectorProblem α)
    (normalize : α → Normalized)
    (Potential : Normalized → ℝ → ℝ) where
  endpointData :
    ∀ a : α, IsSecondaryMinimizingPrimaryMinimizer P a →
      TaoEndpointNormalizationData (Potential (normalize a))

def TaoEndpointReductionInput.toTaoVariationalReductionInput
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblem α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hTao : TaoEndpointReductionInput P normalize Potential) :
    TaoVariationalReductionInput P normalize Potential where
  reducedData := fun a ha =>
    (hTao.endpointData a ha).toTaoReducedPotentialData

def TaoVariationalReductionInput.toSecondaryMinimizerNormalization
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblem α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hTao : TaoVariationalReductionInput P normalize Potential) :
    SecondaryMinimizerNormalization P normalize Potential where
  endpointForm := fun a ha =>
    (hTao.reducedData a ha).toNormalizedEndpointPotential

structure TaoVariationalReductionInputENNReal
    {α Normalized : Type} [TopologicalSpace α]
    (P : SecondarySelectorProblemENNReal α)
    (normalize : α → Normalized)
    (Potential : Normalized → ℝ → ℝ) where
  reducedData :
    ∀ a : α, IsSecondaryMinimizingPrimaryMinimizerENNReal P a →
      TaoReducedPotentialData (Potential (normalize a))

structure TaoEndpointReductionInputENNReal
    {α Normalized : Type} [TopologicalSpace α]
    (P : SecondarySelectorProblemENNReal α)
    (normalize : α → Normalized)
    (Potential : Normalized → ℝ → ℝ) where
  endpointData :
    ∀ a : α, IsSecondaryMinimizingPrimaryMinimizerENNReal P a →
      TaoEndpointNormalizationData (Potential (normalize a))

def TaoEndpointReductionInputENNReal.toTaoVariationalReductionInput
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hTao : TaoEndpointReductionInputENNReal P normalize Potential) :
    TaoVariationalReductionInputENNReal P normalize Potential where
  reducedData := fun a ha =>
    (hTao.endpointData a ha).toTaoReducedPotentialData

def TaoVariationalReductionInputENNReal.toSecondaryMinimizerNormalization
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hTao : TaoVariationalReductionInputENNReal P normalize Potential) :
    SecondaryMinimizerNormalizationENNReal P normalize Potential where
  endpointForm := fun a ha =>
    (hTao.reducedData a ha).toNormalizedEndpointPotential

theorem TaoVariationalReductionInput.baseline_length
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblem α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hTao : TaoVariationalReductionInput P normalize Potential)
    {a : α} (ha : IsSecondaryMinimizingPrimaryMinimizer P a) :
    ENNReal.ofReal (Real.sqrt 2) ≤
      volume (PositiveSet (Potential (normalize a))) := by
  exact ((hTao.reducedData a ha).toNormalizedEndpointPotential).baseline_length_le_positiveSet

theorem TaoVariationalReductionInputENNReal.baseline_length
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hTao : TaoVariationalReductionInputENNReal P normalize Potential)
    {a : α} (ha : IsSecondaryMinimizingPrimaryMinimizerENNReal P a) :
    ENNReal.ofReal (Real.sqrt 2) ≤
      volume (PositiveSet (Potential (normalize a))) := by
  exact ((hTao.reducedData a ha).toNormalizedEndpointPotential).baseline_length_le_positiveSet

def TaoVariationalReductionInput.toVariationalNormalizationTheorem
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblem α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hTao : TaoVariationalReductionInput P normalize Potential) :
    VariationalNormalizationTheorem α Normalized
      (fun a => IsSecondaryMinimizingPrimaryMinimizer P a)
      normalize Potential where
  endpointForm := fun a ha =>
    (hTao.reducedData a ha).toNormalizedEndpointPotential

def TaoVariationalReductionInput.toStandardMinimizerReduction
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblem α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hTao : TaoVariationalReductionInput P normalize Potential) :
    StandardMinimizerReduction α
      (fun a => IsSecondaryMinimizingPrimaryMinimizer P a)
      (fun a => Potential (normalize a)) where
  normalize := fun a ha =>
    (hTao.reducedData a ha).toNormalizedEndpointPotential

def TaoVariationalReductionInputENNReal.toVariationalNormalizationTheorem
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hTao : TaoVariationalReductionInputENNReal P normalize Potential) :
    VariationalNormalizationTheorem α Normalized
      (fun a => IsSecondaryMinimizingPrimaryMinimizerENNReal P a)
      normalize Potential where
  endpointForm := fun a ha =>
    (hTao.reducedData a ha).toNormalizedEndpointPotential

def TaoVariationalReductionInputENNReal.toStandardMinimizerReduction
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hTao : TaoVariationalReductionInputENNReal P normalize Potential) :
    StandardMinimizerReduction α
      (fun a => IsSecondaryMinimizingPrimaryMinimizerENNReal P a)
      (fun a => Potential (normalize a)) where
  normalize := fun a ha =>
    (hTao.reducedData a ha).toNormalizedEndpointPotential

theorem TaoVariationalReductionInput.exists_baseline_length
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblem α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hTao : TaoVariationalReductionInput P normalize Potential) :
    ∃ a : α, IsSecondaryMinimizingPrimaryMinimizer P a ∧
      ENNReal.ofReal (Real.sqrt 2) ≤
        volume (PositiveSet (Potential (normalize a))) := by
  rcases P.exists_secondary_minimizer with ⟨a, ha⟩
  exact ⟨a, ha, hTao.baseline_length ha⟩

theorem TaoVariationalReductionInputENNReal.exists_baseline_length
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hTao : TaoVariationalReductionInputENNReal P normalize Potential) :
    ∃ a : α, IsSecondaryMinimizingPrimaryMinimizerENNReal P a ∧
      ENNReal.ofReal (Real.sqrt 2) ≤
        volume (PositiveSet (Potential (normalize a))) := by
  rcases P.exists_secondary_minimizer with ⟨a, ha⟩
  exact ⟨a, ha, hTao.baseline_length ha⟩

theorem TaoEndpointReductionInput.exists_baseline_length
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblem α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hTao : TaoEndpointReductionInput P normalize Potential) :
    ∃ a : α, IsSecondaryMinimizingPrimaryMinimizer P a ∧
      ENNReal.ofReal (Real.sqrt 2) ≤
        volume (PositiveSet (Potential (normalize a))) := by
  exact hTao.toTaoVariationalReductionInput.exists_baseline_length

theorem TaoEndpointReductionInputENNReal.exists_baseline_length
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hTao : TaoEndpointReductionInputENNReal P normalize Potential) :
    ∃ a : α, IsSecondaryMinimizingPrimaryMinimizerENNReal P a ∧
      ENNReal.ofReal (Real.sqrt 2) ≤
        volume (PositiveSet (Potential (normalize a))) := by
  exact hTao.toTaoVariationalReductionInput.exists_baseline_length

def TaoEndpointReductionInput.toSecondaryMinimizerNormalization
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblem α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hTao : TaoEndpointReductionInput P normalize Potential) :
    SecondaryMinimizerNormalization P normalize Potential :=
  hTao.toTaoVariationalReductionInput.toSecondaryMinimizerNormalization

def TaoEndpointReductionInputENNReal.toSecondaryMinimizerNormalization
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hTao : TaoEndpointReductionInputENNReal P normalize Potential) :
    SecondaryMinimizerNormalizationENNReal P normalize Potential :=
  hTao.toTaoVariationalReductionInput.toSecondaryMinimizerNormalization

def TaoEndpointReductionInput.toStandardMinimizerReduction
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblem α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hTao : TaoEndpointReductionInput P normalize Potential) :
    StandardMinimizerReduction α
      (fun a => IsSecondaryMinimizingPrimaryMinimizer P a)
      (fun a => Potential (normalize a)) :=
  hTao.toTaoVariationalReductionInput.toStandardMinimizerReduction

def TaoEndpointReductionInputENNReal.toStandardMinimizerReduction
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hTao : TaoEndpointReductionInputENNReal P normalize Potential) :
    StandardMinimizerReduction α
      (fun a => IsSecondaryMinimizingPrimaryMinimizerENNReal P a)
      (fun a => Potential (normalize a)) :=
  hTao.toTaoVariationalReductionInput.toStandardMinimizerReduction

theorem standard_reduction_baseline_length_from_tao_reduced_data
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblem α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hReduced :
      ∀ a : α, IsSecondaryMinimizingPrimaryMinimizer P a →
        TaoReducedPotentialData (Potential (normalize a))) :
    ∃ a : α, IsSecondaryMinimizingPrimaryMinimizer P a ∧
      ENNReal.ofReal (Real.sqrt 2) ≤
        volume (PositiveSet (Potential (normalize a))) := by
  exact (TaoVariationalReductionInput.mk hReduced).exists_baseline_length

theorem standard_reduction_baseline_length_from_tao_reduced_data_ennreal
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hReduced :
      ∀ a : α, IsSecondaryMinimizingPrimaryMinimizerENNReal P a →
        TaoReducedPotentialData (Potential (normalize a))) :
    ∃ a : α, IsSecondaryMinimizingPrimaryMinimizerENNReal P a ∧
      ENNReal.ofReal (Real.sqrt 2) ≤
        volume (PositiveSet (Potential (normalize a))) := by
  exact (TaoVariationalReductionInputENNReal.mk hReduced).exists_baseline_length

theorem standard_reduction_baseline_length_from_tao_endpoint_data
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblem α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hEndpoint :
      ∀ a : α, IsSecondaryMinimizingPrimaryMinimizer P a →
        TaoEndpointNormalizationData (Potential (normalize a))) :
    ∃ a : α, IsSecondaryMinimizingPrimaryMinimizer P a ∧
      ENNReal.ofReal (Real.sqrt 2) ≤
        volume (PositiveSet (Potential (normalize a))) := by
  exact (TaoEndpointReductionInput.mk hEndpoint).exists_baseline_length

theorem standard_reduction_baseline_length_from_tao_endpoint_data_ennreal
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hEndpoint :
      ∀ a : α, IsSecondaryMinimizingPrimaryMinimizerENNReal P a →
        TaoEndpointNormalizationData (Potential (normalize a))) :
    ∃ a : α, IsSecondaryMinimizingPrimaryMinimizerENNReal P a ∧
      ENNReal.ofReal (Real.sqrt 2) ≤
        volume (PositiveSet (Potential (normalize a))) := by
  exact (TaoEndpointReductionInputENNReal.mk hEndpoint).exists_baseline_length

theorem SecondaryMinimizerNormalization.exists_normalized_endpoint_potential
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblem α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hNorm : SecondaryMinimizerNormalization P normalize Potential) :
    ∃ a : α, IsSecondaryMinimizingPrimaryMinimizer P a ∧
      Nonempty (NormalizedEndpointPotential (Potential (normalize a))) := by
  rcases P.exists_secondary_minimizer with ⟨a, ha⟩
  exact ⟨a, ha, ⟨hNorm.endpointForm a ha⟩⟩

theorem SecondaryMinimizerNormalizationENNReal.exists_normalized_endpoint_potential
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hNorm : SecondaryMinimizerNormalizationENNReal P normalize Potential) :
    ∃ a : α, IsSecondaryMinimizingPrimaryMinimizerENNReal P a ∧
      Nonempty (NormalizedEndpointPotential (Potential (normalize a))) := by
  rcases P.exists_secondary_minimizer with ⟨a, ha⟩
  exact ⟨a, ha, ⟨hNorm.endpointForm a ha⟩⟩

theorem SecondaryMinimizerNormalization.exists_baseline_length
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblem α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hNorm : SecondaryMinimizerNormalization P normalize Potential) :
    ∃ a : α, IsSecondaryMinimizingPrimaryMinimizer P a ∧
      ENNReal.ofReal (Real.sqrt 2) ≤
        volume (PositiveSet (Potential (normalize a))) := by
  rcases hNorm.exists_normalized_endpoint_potential with ⟨a, ha, ⟨hendpoint⟩⟩
  exact ⟨a, ha, hendpoint.baseline_length_le_positiveSet⟩

theorem SecondaryMinimizerNormalizationENNReal.exists_baseline_length
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hNorm : SecondaryMinimizerNormalizationENNReal P normalize Potential) :
    ∃ a : α, IsSecondaryMinimizingPrimaryMinimizerENNReal P a ∧
      ENNReal.ofReal (Real.sqrt 2) ≤
        volume (PositiveSet (Potential (normalize a))) := by
  rcases hNorm.exists_normalized_endpoint_potential with ⟨a, ha, ⟨hendpoint⟩⟩
  exact ⟨a, ha, hendpoint.baseline_length_le_positiveSet⟩

def secondary_normalization_gives_standard_reduction
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblem α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hNorm : SecondaryMinimizerNormalization P normalize Potential) :
    StandardMinimizerReduction α
      (fun a => IsSecondaryMinimizingPrimaryMinimizer P a)
      (fun a => Potential (normalize a)) where
  normalize := hNorm.endpointForm

def secondary_normalization_ennreal_gives_standard_reduction
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hNorm : SecondaryMinimizerNormalizationENNReal P normalize Potential) :
    StandardMinimizerReduction α
      (fun a => IsSecondaryMinimizingPrimaryMinimizerENNReal P a)
      (fun a => Potential (normalize a)) where
  normalize := hNorm.endpointForm

def secondary_normalization_gives_variational_normalization
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblem α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hNorm : SecondaryMinimizerNormalization P normalize Potential) :
    VariationalNormalizationTheorem α Normalized
      (fun a => IsSecondaryMinimizingPrimaryMinimizer P a)
      normalize Potential where
  endpointForm := hNorm.endpointForm

def secondary_normalization_ennreal_gives_variational_normalization
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hNorm : SecondaryMinimizerNormalizationENNReal P normalize Potential) :
    VariationalNormalizationTheorem α Normalized
      (fun a => IsSecondaryMinimizingPrimaryMinimizerENNReal P a)
      normalize Potential where
  endpointForm := hNorm.endpointForm

theorem SecondaryMinimizerNormalization.baseline_length
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblem α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hNorm : SecondaryMinimizerNormalization P normalize Potential)
    {a : α} (ha : IsSecondaryMinimizingPrimaryMinimizer P a) :
    ENNReal.ofReal (Real.sqrt 2) ≤
      volume (PositiveSet (Potential (normalize a))) := by
  exact (hNorm.endpointForm a ha).baseline_length_le_positiveSet

theorem SecondaryMinimizerNormalizationENNReal.baseline_length
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hNorm : SecondaryMinimizerNormalizationENNReal P normalize Potential)
    {a : α} (ha : IsSecondaryMinimizingPrimaryMinimizerENNReal P a) :
    ENNReal.ofReal (Real.sqrt 2) ≤
      volume (PositiveSet (Potential (normalize a))) := by
  exact (hNorm.endpointForm a ha).baseline_length_le_positiveSet

end

/--
Any selected atom in the real-valued positive set is also selected in the
augmented positive set.
-/
theorem finiteAtomic_selects_augmented_of_selects_positive
    {ι : Type*} {μ : MeasureTheory.ProbabilityMeasure UnitInterval1038}
    {s : Finset ι} {atom : ι → ℝ}
    (hselect : ∃ i : ι, i ∈ s ∧
      atom i ∈ PositiveSet (unitIntervalLogPotential μ)) :
    ∃ i : ι, i ∈ s ∧ atom i ∈ unitIntervalAugmentedPositiveSet μ := by
  rcases hselect with ⟨i, hi, hpos⟩
  exact ⟨i, hi, Or.inl hpos⟩

/--
If a finite candidate atom lies on the diagonal atom set, it is selected by the
augmented positive set branch.  This is the safe real-valued replacement for the
informal `+∞` singular-potential argument.
-/
theorem finiteAtomic_selects_augmented_of_selects_diagonal
    {ι : Type*} {μ : MeasureTheory.ProbabilityMeasure UnitInterval1038}
    {s : Finset ι} {atom : ι → ℝ}
    (hselect : ∃ i : ι, i ∈ s ∧ atom i ∈ diagonalAtomSet μ) :
    ∃ i : ι, i ∈ s ∧ atom i ∈ unitIntervalAugmentedPositiveSet μ := by
  rcases hselect with ⟨i, hi, hdiag⟩
  exact ⟨i, hi, Or.inr hdiag⟩

/--
Finite positive-sum selector lifted to the augmented target.  This theorem uses
the ordinary positive-set selector and then includes that selected atom into the
augmented set.
-/
theorem finiteAtomicUnitIntervalDualPotential_positive_selects_augmented_atom
    {ι : Type*} [DecidableEq ι]
    (μ : MeasureTheory.ProbabilityMeasure UnitInterval1038)
    (s : Finset ι) (w atom : ι → ℝ)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hdual_pos : 0 < finiteAtomicUnitIntervalDualPotential μ s w atom) :
    ∃ i : ι, i ∈ s ∧ atom i ∈ unitIntervalAugmentedPositiveSet μ := by
  exact finiteAtomic_selects_augmented_of_selects_positive
    (finiteAtomicUnitIntervalDualPotential_positive_selects_atom
      μ s w atom hw_nonneg hdual_pos)

/--
Selector from an explicit positive-or-diagonal selected candidate.  This is the
branch that genuinely consumes the diagonal exceptional case.
-/
theorem finiteAtomic_selects_augmented_of_selects_positive_or_diagonal
    {ι : Type*} {μ : MeasureTheory.ProbabilityMeasure UnitInterval1038}
    {s : Finset ι} {atom : ι → ℝ}
    (hselect : ∃ i : ι, i ∈ s ∧
      (atom i ∈ PositiveSet (unitIntervalLogPotential μ) ∨
        atom i ∈ diagonalAtomSet μ)) :
    ∃ i : ι, i ∈ s ∧ atom i ∈ unitIntervalAugmentedPositiveSet μ := by
  rcases hselect with ⟨i, hi, hpos_or_diag⟩
  exact ⟨i, hi, hpos_or_diag⟩

/-- Named finite duality identity selector with augmented target. -/
theorem FiniteAtomicUnitIntervalDualityIdentity.selects_augmented_atom
    {ι : Type*} [DecidableEq ι]
    {μ : MeasureTheory.ProbabilityMeasure UnitInterval1038}
    {s : Finset ι} {w atom : ι → ℝ}
    (hduality : FiniteAtomicUnitIntervalDualityIdentity μ s w atom)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hintegral_pos :
      0 < ∫ x : UnitInterval1038,
        finiteWeightedPotential s w atom (x : ℝ)
          ∂(μ : MeasureTheory.Measure UnitInterval1038)) :
    ∃ i : ι, i ∈ s ∧ atom i ∈ unitIntervalAugmentedPositiveSet μ := by
  exact finiteAtomic_selects_augmented_of_selects_positive
    (hduality.selects_atom hw_nonneg hintegral_pos)

/--
Domain-aware augmented selector.  It carries forward the certificate sweep
domain while allowing the null diagonal branch in the target set.
-/
theorem FiniteAtomicUnitIntervalDualityIdentity.selects_augmented_atom_in_domain
    {ι : Type*} [DecidableEq ι]
    {μ : MeasureTheory.ProbabilityMeasure UnitInterval1038}
    {s : Finset ι} {w atom : ι → ℝ} {Domain : Set ℝ}
    (hduality : FiniteAtomicUnitIntervalDualityIdentity μ s w atom)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hatom_domain : ∀ i ∈ s, atom i ∈ Domain)
    (hintegral_pos :
      0 < ∫ x : UnitInterval1038,
        finiteWeightedPotential s w atom (x : ℝ)
          ∂(μ : MeasureTheory.Measure UnitInterval1038)) :
    ∃ i : ι, i ∈ s ∧ atom i ∈ Domain ∧
      atom i ∈ unitIntervalAugmentedPositiveSet μ := by
  rcases hduality.selects_atom_in_domain
      hw_nonneg hatom_domain hintegral_pos with
    ⟨i, hi, hdomain, hpos⟩
  exact ⟨i, hi, hdomain, Or.inl hpos⟩

end StandardReduction

namespace StandardReduction

/-!
## Tao-style auxiliary lemmas (named for the paper)

Theorems in this block give short, explicit entry points for the five key steps
in the reduction chain as discussed in Tao's notes:

1. compact + lower-semicontinuous minimization (`Lemma 3.1`, existence);
2. secondary minimization by variance (`Lemma 3.1`, two-step selector);
3. finite kernel convexity/Jensen and continuous measure replacement;
4. variance equality implies a Dirac block (`Lemma 3.1`/`3.2` consequence);
5. endpoint normalization package (`Lemma 3.2` consequence).

These are not additional assumptions; they repackage the already-developed
infrastructure above.
-/

open scoped ENNReal
open MeasureTheory

/--
Tao's first step (existence): a compact admissible class + lower semicontinuous
objective has a minimizer.
-/
theorem lemma_3_1_primary_existence
    (primary : AdmissibleProbability1038 → ℝ)
    (hprimary_lsc : LowerSemicontinuous primary) :
    ∃ μ : AdmissibleProbability1038,
      ∀ ν : AdmissibleProbability1038, primary μ ≤ primary ν := by
  exact admissible_probability_lsc_exists_minimizer primary hprimary_lsc

theorem lemma_3_1_primary_existence_ennreal
    (primary : AdmissibleProbability1038 → ℝ≥0∞)
    (hprimary_lsc : LowerSemicontinuous primary) :
    ∃ μ : AdmissibleProbability1038,
      ∀ ν : AdmissibleProbability1038, primary μ ≤ primary ν := by
  exact admissible_probability_lsc_exists_minimizer_ennreal primary hprimary_lsc

/--
Concrete Lemma 3.1 input for the real 1038 objective: a finite tail-core
certificate at each positive threshold implies lower semicontinuity of
`μ ↦ volume {x | 0 < U_μ x}`.
-/
theorem lemma_3_1_positive_objective_lsc_of_finite_tailCore
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ η : NNReal, 0 < η →
        ∃ truncε δ : ℝ, ∃ s : Finset ℝ,
          0 < truncε ∧
          0 < δ ∧
          volume ({x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} \ (s : Set ℝ)) ≤
            (η : ℝ≥0∞) ∧
          (∀ x ∈ s,
            x ∈ unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ
              (diagonalAtomSet μ)) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ s,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalLogPotential ν x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          δ ≤ (1 / ((n : ℝ) + 1)) / 3) :
    LowerSemicontinuous unitIntervalPositiveSetObjective := by
  exact unitIntervalPositiveSetObjective_lowerSemicontinuous_of_finite_tailCore hcore

/--
Concrete Lemma 3.1 conclusion for the real 1038 objective: the same finite
tail-core certificate produces a minimizer of the relaxed positive-set length
objective.
-/
theorem lemma_3_1_positive_objective_exists_minimizer_of_finite_tailCore
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ η : NNReal, 0 < η →
        ∃ truncε δ : ℝ, ∃ s : Finset ℝ,
          0 < truncε ∧
          0 < δ ∧
          volume ({x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} \ (s : Set ℝ)) ≤
            (η : ℝ≥0∞) ∧
          (∀ x ∈ s,
            x ∈ unitIntervalThresholdTailCoreOffDiagonal μ n truncε δ
              (diagonalAtomSet μ)) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ s,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalLogPotential ν x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          δ ≤ (1 / ((n : ℝ) + 1)) / 3) :
    ∃ μ : ProbabilityMeasure UnitInterval1038,
      ∀ ν : ProbabilityMeasure UnitInterval1038,
        unitIntervalPositiveSetObjective μ ≤
          unitIntervalPositiveSetObjective ν := by
  exact unitIntervalPositiveSetObjective_exists_minimizer_of_finite_tailCore hcore

/--
Correct compact-core version of Lemma 3.1 for the real 1038 objective.  Unlike
the finite-core interface, this matches the regularity argument: compact subsets,
not finite sets, approximate positive-length threshold sets.
-/
theorem lemma_3_1_positive_objective_lsc_of_compact_core
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ truncε : ℝ, ∃ K : Set ℝ,
          K ⊆ {x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} ∧
          IsCompact K ∧
          volume ({x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} \ K) ≤ (ε : ℝ≥0∞) ∧
          (∀ x ∈ K,
            |unitIntervalTruncatedPotential truncε μ x -
              unitIntervalLogPotential μ x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ K,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalLogPotential ν x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ K,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalTruncatedPotential truncε μ x| <
              (1 / ((n : ℝ) + 1)) / 3)) :
    LowerSemicontinuous unitIntervalPositiveSetObjective := by
  exact unitIntervalPositiveSetObjective_lowerSemicontinuous_of_compact_core hcore

/--
Correct compact-core minimizer-existence entry point for Lemma 3.1.
-/
theorem lemma_3_1_positive_objective_exists_minimizer_of_compact_core
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ n : ℕ, ∀ ε : NNReal, 0 < ε →
        ∃ truncε : ℝ, ∃ K : Set ℝ,
          K ⊆ {x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} ∧
          IsCompact K ∧
          volume ({x : ℝ | 1 / ((n : ℝ) + 1) <
            unitIntervalLogPotential μ x} \ K) ≤ (ε : ℝ≥0∞) ∧
          (∀ x ∈ K,
            |unitIntervalTruncatedPotential truncε μ x -
              unitIntervalLogPotential μ x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ K,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalLogPotential ν x| <
              (1 / ((n : ℝ) + 1)) / 3) ∧
          (∀ᶠ ν in nhds μ, ∀ x ∈ K,
            |unitIntervalTruncatedPotential truncε ν x -
              unitIntervalTruncatedPotential truncε μ x| <
              (1 / ((n : ℝ) + 1)) / 3)) :
    ∃ μ : ProbabilityMeasure UnitInterval1038,
      ∀ ν : ProbabilityMeasure UnitInterval1038,
        unitIntervalPositiveSetObjective μ ≤
          unitIntervalPositiveSetObjective ν := by
  exact unitIntervalPositiveSetObjective_exists_minimizer_of_compact_core hcore

/--
Tao's second step (secondary selector): among primary minimizers, choose one
minimizing the second-moment objective.
-/
theorem lemma_3_1_secondary_selector
    (primary secondary : AdmissibleProbability1038 → ℝ)
    (hprimary_lsc : LowerSemicontinuous primary)
    (hsecondary_lsc : LowerSemicontinuous secondary) :
    ∃ μ : AdmissibleProbability1038,
      (∀ ν : AdmissibleProbability1038, primary μ ≤ primary ν) ∧
      ∀ ν : AdmissibleProbability1038,
        (∀ η : AdmissibleProbability1038, primary ν ≤ primary η) →
          secondary μ ≤ secondary ν := by
  exact admissible_probability_lsc_exists_secondary_minimizer primary secondary
    hprimary_lsc hsecondary_lsc

theorem lemma_3_1_secondary_selector_ennreal_primary
    (primary : AdmissibleProbability1038 → ℝ≥0∞)
    (secondary : AdmissibleProbability1038 → ℝ)
    (hprimary_lsc : LowerSemicontinuous primary)
    (hsecondary_lsc : LowerSemicontinuous secondary) :
    ∃ μ : AdmissibleProbability1038,
      (∀ ν : AdmissibleProbability1038, primary μ ≤ primary ν) ∧
      ∀ ν : AdmissibleProbability1038,
        (∀ η : AdmissibleProbability1038, primary ν ≤ primary η) →
          secondary μ ≤ secondary ν := by
  exact admissible_probability_lsc_exists_secondary_minimizer_ennreal_primary
    primary secondary hprimary_lsc hsecondary_lsc

/--
Measure-level kernel bridge for Tao's Lemma 3.2 consequences: the existing
nonpositive-mean measure-potential lemma gives nonnegativity of
`measureLogPotential` under the stated support, separation, and integrability
hypotheses.
-/
theorem lemma_3_2_measure_kernel_nonneg_of_nonpositive_mean
    (μ : MeasureTheory.Measure ℝ) (hμ : MeasureTheory.IsProbabilityMeasure μ) {x ε : ℝ}
    (hx0 : -1 ≤ x) (hx1 : x ≤ 0)
    (hε : 0 < ε)
    (hsupp : ∀ᵐ t ∂μ, -1 ≤ t ∧ t ≤ 1)
    (hdist_lower : ∀ᵐ t ∂μ, ε ≤ |x - t|)
    (hdist_int : MeasureTheory.Integrable (fun t : ℝ => |x - t|) μ)
    (hlinear_int : MeasureTheory.Integrable (fun t : ℝ => x * t) μ)
    (hlog_int : MeasureTheory.Integrable (fun t : ℝ => Real.log |x - t|) μ)
    (hmean_nonpos : (∫ t : ℝ, t ∂μ) ≤ 0) :
    0 ≤ measureLogPotential μ x := by
  letI : MeasureTheory.IsProbabilityMeasure μ := hμ
  exact measureLogPotential_nonneg_of_nonpositive_mean μ hx0 hx1 hε hsupp hdist_lower
    hdist_int hlinear_int hlog_int hmean_nonpos

/--
Unit-interval probability-measure form of Tao's Lemma 3.2 kernel implication
on the right half-interval. This is no longer a finite weighted statement: the
measure is an arbitrary `ProbabilityMeasure UnitInterval1038`, pushed forward to
`ℝ` by `realMeasure`.

The theorem is deliberately nonnegative, not strict. Strict positivity at this
level requires excluding the equality case `unitIntervalLogPotential μ x = 0`.
-/
theorem lemma_3_2_unitIntervalLogPotential_nonneg_of_nonnegative_mean
    (μ : ProbabilityMeasure UnitInterval1038) {x ε : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hε : 0 < ε)
    (hdist_lower : ∀ᵐ t ∂realMeasure μ, ε ≤ |x - t|)
    (hdist_int : Integrable (fun t : ℝ => |x - t|) (realMeasure μ))
    (hlinear_int : Integrable (fun t : ℝ => x * t) (realMeasure μ))
    (hlog_int : Integrable (fun t : ℝ => Real.log |x - t|) (realMeasure μ))
    (hmean_nonneg : 0 ≤ ∫ t : ℝ, t ∂realMeasure μ) :
    0 ≤ unitIntervalLogPotential μ x := by
  rw [unitIntervalLogPotential_eq_realMeasure]
  exact measureLogPotential_nonneg_of_nonnegative_mean
    (realMeasure μ) (le_of_lt hx.1) (le_of_lt hx.2) hε
    (realMeasure_ae_mem_unitInterval μ) hdist_lower hdist_int hlinear_int
    hlog_int hmean_nonneg

/--
Reflected unit-interval probability-measure form of Tao's Lemma 3.2 kernel
implication on the left half-interval. This is the nonpositive-mean analogue
of `lemma_3_2_unitIntervalLogPotential_nonneg_of_nonnegative_mean`.
-/
theorem lemma_3_2_unitIntervalLogPotential_nonneg_of_nonpositive_mean
    (μ : ProbabilityMeasure UnitInterval1038) {x ε : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 0)
    (hε : 0 < ε)
    (hdist_lower : ∀ᵐ t ∂realMeasure μ, ε ≤ |x - t|)
    (hdist_int : Integrable (fun t : ℝ => |x - t|) (realMeasure μ))
    (hlinear_int : Integrable (fun t : ℝ => x * t) (realMeasure μ))
    (hlog_int : Integrable (fun t : ℝ => Real.log |x - t|) (realMeasure μ))
    (hmean_nonpos : (∫ t : ℝ, t ∂realMeasure μ) ≤ 0) :
    0 ≤ unitIntervalLogPotential μ x := by
  rw [unitIntervalLogPotential_eq_realMeasure]
  exact measureLogPotential_nonneg_of_nonpositive_mean
    (realMeasure μ) (le_of_lt hx.1) (le_of_lt hx.2) hε
    (realMeasure_ae_mem_unitInterval μ) hdist_lower hdist_int hlinear_int
    hlog_int hmean_nonpos

/--
Strict Jensen/log consequence for the measure-level kernel.  The
anti-degeneracy condition is not phrased in terms of the potential: it says
that the distance average in Jensen's logarithmic step is already strictly
below the equality value `1`.
-/
theorem measureLogPotential_pos_of_abs_integral_lt_one
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {x ε : ℝ}
    (hε : 0 < ε)
    (hdist_lower : ∀ᵐ t ∂μ, ε ≤ |x - t|)
    (hdist_int : Integrable (fun t : ℝ => |x - t|) μ)
    (hlog_int : Integrable (fun t : ℝ => Real.log |x - t|) μ)
    (havg_lt_one : (∫ t, |x - t| ∂μ) < 1) :
    0 < measureLogPotential μ x := by
  have hj :
      (∫ t, Real.log |x - t| ∂μ) ≤
        Real.log (∫ t, |x - t| ∂μ) :=
    measure_log_abs_integral_le_log_abs_integral μ
      hε hdist_lower hdist_int hlog_int
  have hε_le_avg : ε ≤ ∫ t, |x - t| ∂μ := by
    have hle :
        (∫ _ : ℝ, ε ∂μ) ≤ ∫ t, |x - t| ∂μ :=
      integral_mono_ae (integrable_const ε) hdist_int hdist_lower
    simpa using hle
  have havg_pos : 0 < ∫ t, |x - t| ∂μ :=
    lt_of_lt_of_le hε hε_le_avg
  have hlog_neg : Real.log (∫ t, |x - t| ∂μ) < 0 :=
    Real.log_neg havg_pos havg_lt_one
  have hdist_pos : ∀ᵐ t ∂μ, 0 < |x - t| :=
    hdist_lower.mono (fun _ ht => lt_of_lt_of_le hε ht)
  rw [measureLogPotential_eq_neg_log_abs_integral μ hdist_pos]
  linarith

/--
Strict Lemma 3.2 consequence on `(0,1)`: under nonnegative mean, strict
positivity follows once the Jensen equality case is broken by the structural
condition `∫ |x-t| d(realMeasure μ) < 1`.
-/
theorem lemma_3_2_unitIntervalLogPotential_pos_of_nonnegative_mean_and_abs_integral_lt_one
    (μ : ProbabilityMeasure UnitInterval1038) {x ε : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hε : 0 < ε)
    (hdist_lower : ∀ᵐ t ∂realMeasure μ, ε ≤ |x - t|)
    (hdist_int : Integrable (fun t : ℝ => |x - t|) (realMeasure μ))
    (hlinear_int : Integrable (fun t : ℝ => x * t) (realMeasure μ))
    (hlog_int : Integrable (fun t : ℝ => Real.log |x - t|) (realMeasure μ))
    (hmean_nonneg : 0 ≤ ∫ t : ℝ, t ∂realMeasure μ)
    (havg_lt_one : (∫ t, |x - t| ∂realMeasure μ) < 1) :
    0 < unitIntervalLogPotential μ x := by
  have _hnonneg : 0 ≤ unitIntervalLogPotential μ x :=
    lemma_3_2_unitIntervalLogPotential_nonneg_of_nonnegative_mean μ hx hε
      hdist_lower hdist_int hlinear_int hlog_int hmean_nonneg
  rw [unitIntervalLogPotential_eq_realMeasure]
  exact measureLogPotential_pos_of_abs_integral_lt_one
    (realMeasure μ) hε hdist_lower hdist_int hlog_int havg_lt_one

/--
Reflected strict Lemma 3.2 consequence on `(-1,0)`: under nonpositive mean,
strict positivity follows from the same structural breaking of the Jensen
equality case, `∫ |x-t| d(realMeasure μ) < 1`.
-/
theorem lemma_3_2_unitIntervalLogPotential_pos_of_nonpositive_mean_and_abs_integral_lt_one
    (μ : ProbabilityMeasure UnitInterval1038) {x ε : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 0)
    (hε : 0 < ε)
    (hdist_lower : ∀ᵐ t ∂realMeasure μ, ε ≤ |x - t|)
    (hdist_int : Integrable (fun t : ℝ => |x - t|) (realMeasure μ))
    (hlinear_int : Integrable (fun t : ℝ => x * t) (realMeasure μ))
    (hlog_int : Integrable (fun t : ℝ => Real.log |x - t|) (realMeasure μ))
    (hmean_nonpos : (∫ t : ℝ, t ∂realMeasure μ) ≤ 0)
    (havg_lt_one : (∫ t, |x - t| ∂realMeasure μ) < 1) :
    0 < unitIntervalLogPotential μ x := by
  have _hnonneg : 0 ≤ unitIntervalLogPotential μ x :=
    lemma_3_2_unitIntervalLogPotential_nonneg_of_nonpositive_mean μ hx hε
      hdist_lower hdist_int hlinear_int hlog_int hmean_nonpos
  rw [unitIntervalLogPotential_eq_realMeasure]
  exact measureLogPotential_pos_of_abs_integral_lt_one
    (realMeasure μ) hε hdist_lower hdist_int hlog_int havg_lt_one

/--
Strict upgrade for the right half-interval statement. The only additional
hypothesis at this abstraction level is the equality-case exclusion
`unitIntervalLogPotential μ x ≠ 0`; this theorem assumes that exclusion and
does not derive it from replacement or variance-rigidity hypotheses.
-/
theorem lemma_3_2_unitIntervalLogPotential_pos_of_nonnegative_mean_and_ne_zero
    (μ : ProbabilityMeasure UnitInterval1038) {x ε : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hε : 0 < ε)
    (hdist_lower : ∀ᵐ t ∂realMeasure μ, ε ≤ |x - t|)
    (hdist_int : Integrable (fun t : ℝ => |x - t|) (realMeasure μ))
    (hlinear_int : Integrable (fun t : ℝ => x * t) (realMeasure μ))
    (hlog_int : Integrable (fun t : ℝ => Real.log |x - t|) (realMeasure μ))
    (hmean_nonneg : 0 ≤ ∫ t : ℝ, t ∂realMeasure μ)
    (hpotential_ne_zero : unitIntervalLogPotential μ x ≠ 0) :
    0 < unitIntervalLogPotential μ x := by
  have hnonneg :
      0 ≤ unitIntervalLogPotential μ x :=
    lemma_3_2_unitIntervalLogPotential_nonneg_of_nonnegative_mean μ hx hε
      hdist_lower hdist_int hlinear_int hlog_int hmean_nonneg
  exact lt_of_le_of_ne hnonneg hpotential_ne_zero.symm

/--
Variance rigidity step used in Tao's contradiction argument:
if replacing a positive-mass component keeps the primary objective nonincreasing and
has no larger secondary objective than the selected minimizer, secondary
minimality forces equality, and the replaced component is already Dirac at its
mean.
-/
theorem lemma_3_2_variance_rigidity
    {α : Type*} [TopologicalSpace α]
    {P : SecondarySelectorProblem α} {a b : α}
    (ha : IsSecondaryMinimizingPrimaryMinimizer P a)
    (hb_adm : P.Primary.Admissible b)
    (hb_primary : P.Primary.objective b ≤ P.Primary.objective a)
    (hb_secondary_le : P.secondaryObjective b ≤ P.secondaryObjective a)
    (μ : MeasureTheory.Measure ℝ) (hμ : MeasureTheory.IsProbabilityMeasure μ)
    (hfirst : MeasureTheory.Integrable (fun t : ℝ => t) μ)
    (hsecond : MeasureTheory.Integrable (fun t : ℝ => t ^ 2) μ)
    (hsecondary_eq_to_second_moment_eq :
      P.secondaryObjective b = P.secondaryObjective a →
        (∫ t : ℝ, t ^ 2 ∂μ) = (∫ t : ℝ, t ∂μ) ^ 2) :
    μ = MeasureTheory.Measure.dirac (∫ t : ℝ, t ∂μ) := by
 exact
    secondary_minimizer_replacement_forces_block_dirac ha hb_adm hb_primary
      hb_secondary_le μ hfirst hsecond hsecondary_eq_to_second_moment_eq

/--
The same variance-rigidity bridge for the actual `ℝ≥0∞` positive-set length
objective.
-/
theorem lemma_3_2_variance_rigidity_ennreal
    {α : Type*} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α} {a b : α}
    (ha : IsSecondaryMinimizingPrimaryMinimizerENNReal P a)
    (hb_adm : P.Primary.Admissible b)
    (hb_primary : P.Primary.objective b ≤ P.Primary.objective a)
    (hb_secondary_le : P.secondaryObjective b ≤ P.secondaryObjective a)
    (μ : Measure ℝ) (hμ : IsProbabilityMeasure μ)
    (hfirst : Integrable (fun t : ℝ => t) μ)
    (hsecond : Integrable (fun t : ℝ => t ^ 2) μ)
    (hsecondary_eq_to_second_moment_eq :
      P.secondaryObjective b = P.secondaryObjective a →
        (∫ t : ℝ, t ^ 2 ∂μ) = (∫ t : ℝ, t ∂μ) ^ 2) :
    μ = Measure.dirac (∫ t : ℝ, t ∂μ) := by
  letI : IsProbabilityMeasure μ := hμ
  exact
    secondary_minimizer_replacement_forces_block_dirac_ennreal ha hb_adm
      hb_primary hb_secondary_le μ hfirst hsecond hsecondary_eq_to_second_moment_eq

/--
Replacement-rigidity bridge for the truncated-sup selector.  The primary
objective is specialized to `unitIntervalTruncatedPositiveSetObjective`, while
the secondary objective is kept explicit as an arbitrary lower-semicontinuous
selector.  The conclusion is only the rigidity of the supplied replacement
block.
-/
theorem unitIntervalTruncatedPositiveSetObjective_secondary_selector_replacement_forces_block_dirac_ennreal
    (secondary : ProbabilityMeasure UnitInterval1038 → ℝ)
    {P : SecondarySelectorProblemENNReal (ProbabilityMeasure UnitInterval1038)}
    {a b : ProbabilityMeasure UnitInterval1038}
    (hprimary :
      P.Primary.objective = unitIntervalTruncatedPositiveSetObjective)
    (hsecondary : P.secondaryObjective = secondary)
    (ha : IsSecondaryMinimizingPrimaryMinimizerENNReal P a)
    (hb_adm : P.Primary.Admissible b)
    (hb_primary :
      unitIntervalTruncatedPositiveSetObjective b ≤
        unitIntervalTruncatedPositiveSetObjective a)
    (hb_secondary_le : secondary b ≤ secondary a)
    (block : Measure ℝ) (hblock : IsProbabilityMeasure block)
    (hfirst : Integrable (fun t : ℝ => t) block)
    (hsecond : Integrable (fun t : ℝ => t ^ 2) block)
    (hsecondary_eq_to_second_moment_eq :
      secondary b = secondary a →
        (∫ t : ℝ, t ^ 2 ∂block) = (∫ t : ℝ, t ∂block) ^ 2) :
    block = Measure.dirac (∫ t : ℝ, t ∂block) := by
  letI : IsProbabilityMeasure block := hblock
  have hb_primary_P : P.Primary.objective b ≤ P.Primary.objective a := by
    simpa [hprimary] using hb_primary
  have hb_secondary_le_P : P.secondaryObjective b ≤ P.secondaryObjective a := by
    simpa [hsecondary] using hb_secondary_le
  exact
    secondary_minimizer_replacement_forces_block_dirac_ennreal ha hb_adm
      hb_primary_P hb_secondary_le_P block hfirst hsecond
      (fun hsecondary_eq_P =>
        hsecondary_eq_to_second_moment_eq (by
          simpa [hsecondary] using hsecondary_eq_P))

/--
Component-replacement version of the ENNReal variance-rigidity step.  This is
the exact abstract form used after Jensen gives the outside-potential inequality.
-/
theorem lemma_3_2_component_replacement_variance_rigidity_ennreal
    {α : Type*} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α} {a b : α}
    (ha : IsSecondaryMinimizingPrimaryMinimizerENNReal P a)
    (hb_adm : P.Primary.Admissible b)
    {μ0 : ProbabilityMeasure UnitInterval1038} (C : PositiveComponent μ0)
    (hobj_a :
      P.Primary.objective a =
        volume (PositiveSet (unitIntervalLogPotential μ0)))
    (hobj_b :
      P.Primary.objective b =
        volume (PositiveSet (componentReplacementPotential C)))
    (houtside : ∀ x : ℝ, StrictOutsideComponent C x →
      componentReplacementPotential C x ≤ unitIntervalLogPotential μ0 x)
    (hb_secondary_le : P.secondaryObjective b ≤ P.secondaryObjective a)
    (block : Measure ℝ) (hblock : IsProbabilityMeasure block)
    (hfirst : Integrable (fun t : ℝ => t) block)
    (hsecond : Integrable (fun t : ℝ => t ^ 2) block)
    (hsecondary_eq_to_second_moment_eq :
      P.secondaryObjective b = P.secondaryObjective a →
        (∫ t : ℝ, t ^ 2 ∂block) = (∫ t : ℝ, t ∂block) ^ 2) :
    block = Measure.dirac (∫ t : ℝ, t ∂block) := by
  letI : IsProbabilityMeasure block := hblock
  exact
    secondary_minimizer_componentReplacement_forces_block_dirac_ennreal_strictOutside
      ha hb_adm C hobj_a hobj_b houtside hb_secondary_le block hfirst hsecond
      hsecondary_eq_to_second_moment_eq

/--
Specialized atomization bridge for the actual unit-interval positive-set
objective.  If `a` is the selected secondary/variance-minimizing primary
minimizer, `C` is a supplied positive component of `a`, and the admissible
replacement `b` realizes the barycenter-replacement potential, then strict
outside-potential nonincrease plus secondary nonincrease force the supplied
probability block to be a Dirac mass at its barycenter.

Remaining assumptions are explicit: this theorem does not construct the
positive component, does not prove that `b` is an admissible probability
replacement, does not prove the strict-outside Jensen inequality, and does not
identify the secondary-objective equality with second-moment equality.
-/
theorem unitIntervalPositiveSetObjective_component_replacement_forces_block_dirac_ennreal
    (secondary : ProbabilityMeasure UnitInterval1038 → ℝ)
    {P : SecondarySelectorProblemENNReal (ProbabilityMeasure UnitInterval1038)}
    {a b : ProbabilityMeasure UnitInterval1038}
    (hprimary : P.Primary.objective = unitIntervalPositiveSetObjective)
    (hsecondary : P.secondaryObjective = secondary)
    (ha : IsSecondaryMinimizingPrimaryMinimizerENNReal P a)
    (hb_adm : P.Primary.Admissible b)
    (C : PositiveComponent a)
    (hreplacement_potential :
      unitIntervalLogPotential b = componentReplacementPotential C)
    (houtside : ∀ x : ℝ, StrictOutsideComponent C x →
      componentReplacementPotential C x ≤ unitIntervalLogPotential a x)
    (hb_secondary_le : secondary b ≤ secondary a)
    (block : Measure ℝ) (hblock : IsProbabilityMeasure block)
    (hfirst : Integrable (fun t : ℝ => t) block)
    (hsecond : Integrable (fun t : ℝ => t ^ 2) block)
    (hsecondary_eq_to_second_moment_eq :
      secondary b = secondary a →
        (∫ t : ℝ, t ^ 2 ∂block) = (∫ t : ℝ, t ∂block) ^ 2) :
    block = Measure.dirac (∫ t : ℝ, t ∂block) := by
  letI : IsProbabilityMeasure block := hblock
  have hobj_a :
      P.Primary.objective a =
        volume (PositiveSet (unitIntervalLogPotential a)) := by
    simp [hprimary, unitIntervalPositiveSetObjective, PositiveSet]
  have hobj_b :
      P.Primary.objective b =
        volume (PositiveSet (componentReplacementPotential C)) := by
    simp [hprimary, unitIntervalPositiveSetObjective, PositiveSet,
      hreplacement_potential]
  have hb_secondary_le_P : P.secondaryObjective b ≤ P.secondaryObjective a := by
    simpa [hsecondary] using hb_secondary_le
  exact
    secondary_minimizer_componentReplacement_forces_block_dirac_ennreal_strictOutside
      ha hb_adm C hobj_a hobj_b houtside hb_secondary_le_P block hfirst hsecond
      (fun hsecondary_eq_P =>
        hsecondary_eq_to_second_moment_eq (by
          simpa [hsecondary] using hsecondary_eq_P))

/--
Normalization output: a one-step conversion from the component-reduction data to the
abstract endpoint lower-bound interface already required by the finite-atom certificate.
-/
def lemma_3_2_normalization_bridge
    {U : ℝ → ℝ} (D : TaoReducedPotentialData U) :
    NormalizedEndpointPotential U := by
  simpa using D.toNormalizedEndpointPotential

/--
Endpoint-normalization package for the actual `ℝ≥0∞` positive-set objective:
once the Tao component/variation argument supplies endpoint data for every
secondary minimizer, it becomes a standard minimizer-reduction object.
-/
def lemma_3_2_endpoint_normalization_ennreal
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hEndpoint : TaoEndpointReductionInputENNReal P normalize Potential) :
    StandardMinimizerReduction α
      (fun a => IsSecondaryMinimizingPrimaryMinimizerENNReal P a)
      (fun a => Potential (normalize a)) :=
  hEndpoint.toStandardMinimizerReduction

/--
Length consequence of the endpoint-normalization package for the actual
`ℝ≥0∞` positive-set objective.
-/
theorem lemma_3_2_endpoint_normalization_baseline_length_ennreal
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hEndpoint : TaoEndpointReductionInputENNReal P normalize Potential) :
    ∃ a : α, IsSecondaryMinimizingPrimaryMinimizerENNReal P a ∧
      ENNReal.ofReal (Real.sqrt 2) ≤
        volume (PositiveSet (Potential (normalize a))) := by
  exact hEndpoint.exists_baseline_length

/--
Theorem-level bridge from the concrete Tao endpoint package to the
standard-reduction interface.  The hypothesis is deliberately named
`hEndpointFromVariation`: this theorem only consumes endpoint data after
normalization; it does not prove that data from Tao's variation argument.
-/
theorem tao_endpoint_data_provider_ennreal_standard_reduction_and_baseline_length
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hEndpointFromVariation :
      ∀ a : α, IsSecondaryMinimizingPrimaryMinimizerENNReal P a →
        TaoEndpointNormalizationData (Potential (normalize a))) :
    ∃ _hReduction : StandardMinimizerReduction α
        (fun a => IsSecondaryMinimizingPrimaryMinimizerENNReal P a)
        (fun a => Potential (normalize a)),
      ∃ a : α, IsSecondaryMinimizingPrimaryMinimizerENNReal P a ∧
        ENNReal.ofReal (Real.sqrt 2) ≤
          volume (PositiveSet (Potential (normalize a))) := by
  let hEndpoint : TaoEndpointReductionInputENNReal P normalize Potential :=
    ⟨hEndpointFromVariation⟩
  exact ⟨hEndpoint.toStandardMinimizerReduction, hEndpoint.exists_baseline_length⟩

def tao_endpoint_from_component_variation_package_ennreal
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hPackage :
      ∀ a : α, IsSecondaryMinimizingPrimaryMinimizerENNReal P a →
        TaoVariationComponentPackage (Potential (normalize a))) :
    ∀ a : α, IsSecondaryMinimizingPrimaryMinimizerENNReal P a →
      TaoEndpointNormalizationData (Potential (normalize a)) :=
  fun a ha => (hPackage a ha).toTaoEndpointNormalizationData

theorem tao_component_variation_package_standard_reduction_and_baseline_length_ennreal
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hPackage :
      ∀ a : α, IsSecondaryMinimizingPrimaryMinimizerENNReal P a →
        TaoVariationComponentPackage (Potential (normalize a))) :
    ∃ _hReduction : StandardMinimizerReduction α
        (fun a => IsSecondaryMinimizingPrimaryMinimizerENNReal P a)
        (fun a => Potential (normalize a)),
      ∃ a : α, IsSecondaryMinimizingPrimaryMinimizerENNReal P a ∧
        ENNReal.ofReal (Real.sqrt 2) ≤
          volume (PositiveSet (Potential (normalize a))) := by
  exact tao_endpoint_data_provider_ennreal_standard_reduction_and_baseline_length
    (tao_endpoint_from_component_variation_package_ennreal hPackage)

/--
Specialization to the truncated-sup selector.  Once a secondary minimizer for
the truncated-sup objective is available and the replacement-rigidity hypotheses
are in place, the only additional mathematical input consumed here is
`hEndpointFromVariation`, a provider of concrete `TaoEndpointNormalizationData`
for every secondary minimizer of `unitIntervalTruncatedPositiveSetObjective`.

This theorem does not assert that the provider follows from the variation
argument; it only records the endpoint-potential and baseline-length consequence
if that provider is supplied.
-/
theorem unitIntervalTruncatedPositiveSetObjective_exists_normalized_endpoint_baseline_from_variation
    (secondary : ProbabilityMeasure UnitInterval1038 → ℝ)
    {Normalized : Type}
    {normalize : ProbabilityMeasure UnitInterval1038 → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ η : NNReal, 0 < η →
        ∃ truncN thresholdN : ℕ, ∃ K : Set ℝ,
          volume (unitIntervalTruncatedPositiveSet μ) ≤
            volume K + (η : ℝ≥0∞) ∧
          K ⊆ {x : ℝ |
            unitIntervalPositiveTruncationScale thresholdN <
              unitIntervalTruncatedPotential
                (unitIntervalPositiveTruncationScale truncN) μ x} ∧
          IsCompact K)
    (hsecondary_lsc : LowerSemicontinuous secondary)
    (hEndpointFromVariation :
      ∀ μ : ProbabilityMeasure UnitInterval1038,
        (∀ ν : ProbabilityMeasure UnitInterval1038,
          unitIntervalTruncatedPositiveSetObjective μ ≤
            unitIntervalTruncatedPositiveSetObjective ν) →
        (∀ ν : ProbabilityMeasure UnitInterval1038,
          (∀ η : ProbabilityMeasure UnitInterval1038,
            unitIntervalTruncatedPositiveSetObjective ν ≤
              unitIntervalTruncatedPositiveSetObjective η) →
          secondary μ ≤ secondary ν) →
        TaoEndpointNormalizationData (Potential (normalize μ))) :
    ∃ μ : ProbabilityMeasure UnitInterval1038,
      (∀ ν : ProbabilityMeasure UnitInterval1038,
        unitIntervalTruncatedPositiveSetObjective μ ≤
          unitIntervalTruncatedPositiveSetObjective ν) ∧
      (∀ ν : ProbabilityMeasure UnitInterval1038,
        (∀ η : ProbabilityMeasure UnitInterval1038,
          unitIntervalTruncatedPositiveSetObjective ν ≤
            unitIntervalTruncatedPositiveSetObjective η) →
        secondary μ ≤ secondary ν) ∧
      ∃ _hEndpoint : NormalizedEndpointPotential (Potential (normalize μ)),
        ENNReal.ofReal (Real.sqrt 2) ≤
          volume (PositiveSet (Potential (normalize μ))) := by
  rcases unitIntervalTruncatedPositiveSetObjective_exists_secondary_minimizer_of_compact_threshold_core
      secondary hcore hsecondary_lsc with
    ⟨μ, hPrimary, hSecondary⟩
  let D : TaoEndpointNormalizationData (Potential (normalize μ)) :=
    hEndpointFromVariation μ hPrimary hSecondary
  exact ⟨μ, hPrimary, hSecondary, D.toNormalizedEndpointPotential,
    D.baseline_length_le_positiveSet⟩

/--
Variant of
`unitIntervalTruncatedPositiveSetObjective_exists_normalized_endpoint_baseline_from_variation`
that no longer asks for endpoint-normalization data directly.  The remaining
provider is the lower-level Tao component/variation package; endpoint
normalization and the baseline-length consequence are assembled internally.
-/
theorem unitIntervalTruncatedPositiveSetObjective_exists_normalized_endpoint_baseline_from_component_package
    (secondary : ProbabilityMeasure UnitInterval1038 → ℝ)
    {Normalized : Type}
    {normalize : ProbabilityMeasure UnitInterval1038 → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hcore : ∀ μ : ProbabilityMeasure UnitInterval1038,
      ∀ η : NNReal, 0 < η →
        ∃ truncN thresholdN : ℕ, ∃ K : Set ℝ,
          volume (unitIntervalTruncatedPositiveSet μ) ≤
            volume K + (η : ℝ≥0∞) ∧
          K ⊆ {x : ℝ |
            unitIntervalPositiveTruncationScale thresholdN <
              unitIntervalTruncatedPotential
                (unitIntervalPositiveTruncationScale truncN) μ x} ∧
          IsCompact K)
    (hsecondary_lsc : LowerSemicontinuous secondary)
    (hPackageFromVariation :
      ∀ μ : ProbabilityMeasure UnitInterval1038,
        (∀ ν : ProbabilityMeasure UnitInterval1038,
          unitIntervalTruncatedPositiveSetObjective μ ≤
            unitIntervalTruncatedPositiveSetObjective ν) →
        (∀ ν : ProbabilityMeasure UnitInterval1038,
          (∀ η : ProbabilityMeasure UnitInterval1038,
            unitIntervalTruncatedPositiveSetObjective ν ≤
              unitIntervalTruncatedPositiveSetObjective η) →
          secondary μ ≤ secondary ν) →
        TaoVariationComponentPackage (Potential (normalize μ))) :
    ∃ μ : ProbabilityMeasure UnitInterval1038,
      (∀ ν : ProbabilityMeasure UnitInterval1038,
        unitIntervalTruncatedPositiveSetObjective μ ≤
          unitIntervalTruncatedPositiveSetObjective ν) ∧
      (∀ ν : ProbabilityMeasure UnitInterval1038,
        (∀ η : ProbabilityMeasure UnitInterval1038,
          unitIntervalTruncatedPositiveSetObjective ν ≤
            unitIntervalTruncatedPositiveSetObjective η) →
        secondary μ ≤ secondary ν) ∧
      ∃ _hEndpoint : NormalizedEndpointPotential (Potential (normalize μ)),
        ENNReal.ofReal (Real.sqrt 2) ≤
          volume (PositiveSet (Potential (normalize μ))) := by
  rcases unitIntervalTruncatedPositiveSetObjective_exists_secondary_minimizer_of_compact_threshold_core
      secondary hcore hsecondary_lsc with
    ⟨μ, hPrimary, hSecondary⟩
  let Pack : TaoVariationComponentPackage (Potential (normalize μ)) :=
    hPackageFromVariation μ hPrimary hSecondary
  let D : TaoEndpointNormalizationData (Potential (normalize μ)) :=
    Pack.toTaoEndpointNormalizationData
  exact ⟨μ, hPrimary, hSecondary, D.toNormalizedEndpointPotential,
    D.baseline_length_le_positiveSet⟩

/--
Final assembled standard-reduction endpoint consequence for the current concrete
formalization layer.

This theorem removes the already-closed external providers `hcore`,
`hsecondary_lsc`, and `hEndpointFromVariation`: the compact-threshold core,
primary lower semicontinuity, second-moment lower semicontinuity, and secondary
minimizer existence are all generated internally.  The remaining input is the
true Tao component/variation provider, stated at the lowest package level.
-/
theorem unitIntervalTruncatedPositiveSetObjective_exists_secondMoment_normalized_endpoint_baseline_from_component_package
    {Normalized : Type}
    {normalize : ProbabilityMeasure UnitInterval1038 → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hPackageFromVariation :
      ∀ μ : ProbabilityMeasure UnitInterval1038,
        (∀ ν : ProbabilityMeasure UnitInterval1038,
          unitIntervalTruncatedPositiveSetObjective μ ≤
            unitIntervalTruncatedPositiveSetObjective ν) →
        (∀ ν : ProbabilityMeasure UnitInterval1038,
          (∀ η : ProbabilityMeasure UnitInterval1038,
            unitIntervalTruncatedPositiveSetObjective ν ≤
              unitIntervalTruncatedPositiveSetObjective η) →
          unitIntervalSecondMomentObjective μ ≤
            unitIntervalSecondMomentObjective ν) →
        TaoVariationComponentPackage (Potential (normalize μ))) :
    ∃ μ : ProbabilityMeasure UnitInterval1038,
      (∀ ν : ProbabilityMeasure UnitInterval1038,
        unitIntervalTruncatedPositiveSetObjective μ ≤
          unitIntervalTruncatedPositiveSetObjective ν) ∧
      (∀ ν : ProbabilityMeasure UnitInterval1038,
        (∀ η : ProbabilityMeasure UnitInterval1038,
          unitIntervalTruncatedPositiveSetObjective ν ≤
            unitIntervalTruncatedPositiveSetObjective η) →
        unitIntervalSecondMomentObjective μ ≤
          unitIntervalSecondMomentObjective ν) ∧
      ∃ _hEndpoint : NormalizedEndpointPotential (Potential (normalize μ)),
        ENNReal.ofReal (Real.sqrt 2) ≤
          volume (PositiveSet (Potential (normalize μ))) := by
  rcases unitIntervalTruncatedPositiveSetObjective_exists_secondMoment_secondary_minimizer with
    ⟨μ, hPrimary, hSecondary⟩
  let Pack : TaoVariationComponentPackage (Potential (normalize μ)) :=
    hPackageFromVariation μ hPrimary hSecondary
  let D : TaoEndpointNormalizationData (Potential (normalize μ)) :=
    Pack.toTaoEndpointNormalizationData
  exact ⟨μ, hPrimary, hSecondary, D.toNormalizedEndpointPotential,
    D.baseline_length_le_positiveSet⟩

/--
Concrete-data version of the assembled standard-reduction endpoint consequence.

Compared with
`unitIntervalTruncatedPositiveSetObjective_exists_secondMoment_normalized_endpoint_baseline_from_component_package`,
the remaining provider no longer supplies a full
`TaoVariationComponentPackage`.  It only supplies the genuine variational data:
the selected component, its interval/baseline placement, right endpoint
positivity, the boundary-average inequality, and normalized atomization.  The
support facts, endpoint atom bookkeeping, endpoint-remainder mass/decomposition,
and kernel integrability are assembled internally by the canonical constructor.
-/
theorem unitIntervalTruncatedPositiveSetObjective_exists_secondMoment_normalized_endpoint_baseline_from_concrete_component_data
    (hConcreteFromVariation :
      ∀ μ : ProbabilityMeasure UnitInterval1038,
        (∀ ν : ProbabilityMeasure UnitInterval1038,
          unitIntervalTruncatedPositiveSetObjective μ ≤
            unitIntervalTruncatedPositiveSetObjective ν) →
        (∀ ν : ProbabilityMeasure UnitInterval1038,
          (∀ η : ProbabilityMeasure UnitInterval1038,
            unitIntervalTruncatedPositiveSetObjective ν ≤
              unitIntervalTruncatedPositiveSetObjective η) →
          unitIntervalSecondMomentObjective μ ≤
            unitIntervalSecondMomentObjective ν) →
        ∃ _ : TaoVariationMeanChoice,
        ∃ _ : Bool,
        ∃ _ : ℝ,
        ∃ C : PositiveComponent μ,
        ∃ _ : ComponentReplacement μ C,
        ∃ xMinus xPlus : ℝ,
          C.interval = Set.Ioo xMinus xPlus ∧
          Set.Ioo (-1 : ℝ) 0 ⊆ C.interval ∧
          0 < xPlus ∧
          1 ≤ (xPlus + 1) *
              (((μ : Measure UnitInterval1038)
                {t : UnitInterval1038 | (t : ℝ) = -1}).toReal) +
            (1 - xPlus) *
              (1 -
                (((μ : Measure UnitInterval1038)
                  {t : UnitInterval1038 | (t : ℝ) = -1}).toReal)) ∧
          normalizedComponentBlock C = Measure.dirac (-1 : ℝ)) :
    ∃ μ : ProbabilityMeasure UnitInterval1038,
      (∀ ν : ProbabilityMeasure UnitInterval1038,
        unitIntervalTruncatedPositiveSetObjective μ ≤
          unitIntervalTruncatedPositiveSetObjective ν) ∧
      (∀ ν : ProbabilityMeasure UnitInterval1038,
        (∀ η : ProbabilityMeasure UnitInterval1038,
          unitIntervalTruncatedPositiveSetObjective ν ≤
            unitIntervalTruncatedPositiveSetObjective η) →
        unitIntervalSecondMomentObjective μ ≤
          unitIntervalSecondMomentObjective ν) ∧
      ∃ _hEndpoint : NormalizedEndpointPotential (unitIntervalLogPotential μ),
        ENNReal.ofReal (Real.sqrt 2) ≤
          volume (PositiveSet (unitIntervalLogPotential μ)) := by
  rcases unitIntervalTruncatedPositiveSetObjective_exists_secondMoment_secondary_minimizer with
    ⟨μ, hPrimary, hSecondary⟩
  rcases hConcreteFromVariation μ hPrimary hSecondary with
    ⟨mean_choice, reflected, translation, C, R, xMinus, xPlus,
      hcomponent_interval, hbaseline, hright, hboundary, hnormalized_atomized⟩
  let Pack : TaoVariationComponentPackage (unitIntervalLogPotential μ) :=
    taoVariationComponentPackage_of_canonicalEndpointMass_normalized_atomization_baseline_data
      μ mean_choice reflected translation C R xMinus xPlus hcomponent_interval
      hbaseline hright hboundary hnormalized_atomized
  let D : TaoEndpointNormalizationData (unitIntervalLogPotential μ) :=
    Pack.toTaoEndpointNormalizationData
  exact ⟨μ, hPrimary, hSecondary, D.toNormalizedEndpointPotential,
    D.baseline_length_le_positiveSet⟩

/--
Moment-rigidity version of the concrete-data endpoint consequence.

This pushes the remaining atomization input one step upstream: the provider no
longer supplies `normalizedComponentBlock C = Measure.dirac (-1)`.  It supplies
the component-block second-moment equality and the component support uniqueness;
the endpoint Dirac atomization is derived internally by the variance-rigidity
bridge proved above.
-/
theorem unitIntervalTruncatedPositiveSetObjective_exists_secondMoment_normalized_endpoint_baseline_from_moment_rigidity_data
    (hMomentDataFromVariation :
      ∀ μ : ProbabilityMeasure UnitInterval1038,
        (∀ ν : ProbabilityMeasure UnitInterval1038,
          unitIntervalTruncatedPositiveSetObjective μ ≤
            unitIntervalTruncatedPositiveSetObjective ν) →
        (∀ ν : ProbabilityMeasure UnitInterval1038,
          (∀ η : ProbabilityMeasure UnitInterval1038,
            unitIntervalTruncatedPositiveSetObjective ν ≤
              unitIntervalTruncatedPositiveSetObjective η) →
          unitIntervalSecondMomentObjective μ ≤
            unitIntervalSecondMomentObjective ν) →
        ∃ _ : TaoVariationMeanChoice,
        ∃ _ : Bool,
        ∃ _ : ℝ,
        ∃ C : PositiveComponent μ,
        ∃ _ : ComponentReplacement μ C,
        ∃ xMinus xPlus : ℝ,
          C.interval = Set.Ioo xMinus xPlus ∧
          Set.Ioo (-1 : ℝ) 0 ⊆ C.interval ∧
          0 < xPlus ∧
          1 ≤ (xPlus + 1) *
              (((μ : Measure UnitInterval1038)
                {t : UnitInterval1038 | (t : ℝ) = -1}).toReal) +
            (1 - xPlus) *
              (1 -
                (((μ : Measure UnitInterval1038)
                  {t : UnitInterval1038 | (t : ℝ) = -1}).toReal)) ∧
          ((componentMass C).toReal * (componentBarycenter C) ^ 2 =
            ∫ t : ℝ, t ^ 2 ∂componentBlock C) ∧
          (∀ t : ℝ, t ∈ (realMeasure μ).support → t ∈ C.interval → t = -1)) :
    ∃ μ : ProbabilityMeasure UnitInterval1038,
      (∀ ν : ProbabilityMeasure UnitInterval1038,
        unitIntervalTruncatedPositiveSetObjective μ ≤
          unitIntervalTruncatedPositiveSetObjective ν) ∧
      (∀ ν : ProbabilityMeasure UnitInterval1038,
        (∀ η : ProbabilityMeasure UnitInterval1038,
          unitIntervalTruncatedPositiveSetObjective ν ≤
            unitIntervalTruncatedPositiveSetObjective η) →
        unitIntervalSecondMomentObjective μ ≤
          unitIntervalSecondMomentObjective ν) ∧
      ∃ _hEndpoint : NormalizedEndpointPotential (unitIntervalLogPotential μ),
        ENNReal.ofReal (Real.sqrt 2) ≤
          volume (PositiveSet (unitIntervalLogPotential μ)) := by
  refine
    unitIntervalTruncatedPositiveSetObjective_exists_secondMoment_normalized_endpoint_baseline_from_concrete_component_data
      ?_
  intro μ hPrimary hSecondary
  rcases hMomentDataFromVariation μ hPrimary hSecondary with
    ⟨mean_choice, reflected, translation, C, R, xMinus, xPlus,
      hcomponent_interval, hbaseline, hright, hboundary, hsecondMoment_eq,
      hunique⟩
  refine ⟨mean_choice, reflected, translation, C, R, xMinus, xPlus,
    hcomponent_interval, hbaseline, hright, hboundary, ?_⟩
  exact normalizedComponentBlock_eq_dirac_endpoint_of_componentBlock_secondMoment_eq
    R hsecondMoment_eq hunique

/--
Replacement-rigidity version of the endpoint consequence.

This removes the explicit component-block second-moment equality from the
remaining provider.  The provider only supplies an admissible component
replacement whose primary objective is no larger than the selected primary
minimizer.  Since the selected minimizer is also second-moment minimizing among
primary minimizers, and the barycenter replacement never increases the second
moment, equality in the component-block second-moment inequality is derived
internally.
-/
theorem unitIntervalTruncatedPositiveSetObjective_exists_secondMoment_normalized_endpoint_baseline_from_replacement_rigidity_data
    (hReplacementDataFromVariation :
      ∀ μ : ProbabilityMeasure UnitInterval1038,
        (∀ ν : ProbabilityMeasure UnitInterval1038,
          unitIntervalTruncatedPositiveSetObjective μ ≤
            unitIntervalTruncatedPositiveSetObjective ν) →
        (∀ ν : ProbabilityMeasure UnitInterval1038,
          (∀ η : ProbabilityMeasure UnitInterval1038,
            unitIntervalTruncatedPositiveSetObjective ν ≤
              unitIntervalTruncatedPositiveSetObjective η) →
          unitIntervalSecondMomentObjective μ ≤
            unitIntervalSecondMomentObjective ν) →
        ∃ _ : TaoVariationMeanChoice,
        ∃ _ : Bool,
        ∃ _ : ℝ,
        ∃ C : PositiveComponent μ,
        ∃ _ : ComponentReplacement μ C,
        ∃ hmass_unit : componentReplacementMeasure C (Set.Icc (-1 : ℝ) 1) = 1,
        ∃ _ : ∀ᵐ x ∂componentReplacementMeasure C, x ∈ Set.Icc (-1 : ℝ) 1,
        ∃ xMinus xPlus : ℝ,
          C.interval = Set.Ioo xMinus xPlus ∧
          Set.Ioo (-1 : ℝ) 0 ⊆ C.interval ∧
          0 < xPlus ∧
          1 ≤ (xPlus + 1) *
              (((μ : Measure UnitInterval1038)
                {t : UnitInterval1038 | (t : ℝ) = -1}).toReal) +
            (1 - xPlus) *
              (1 -
                (((μ : Measure UnitInterval1038)
                  {t : UnitInterval1038 | (t : ℝ) = -1}).toReal)) ∧
          unitIntervalTruncatedPositiveSetObjective
              (componentReplacementProbability C hmass_unit) ≤
            unitIntervalTruncatedPositiveSetObjective μ ∧
          (∀ t : ℝ, t ∈ (realMeasure μ).support → t ∈ C.interval → t = -1)) :
    ∃ μ : ProbabilityMeasure UnitInterval1038,
      (∀ ν : ProbabilityMeasure UnitInterval1038,
        unitIntervalTruncatedPositiveSetObjective μ ≤
          unitIntervalTruncatedPositiveSetObjective ν) ∧
      (∀ ν : ProbabilityMeasure UnitInterval1038,
        (∀ η : ProbabilityMeasure UnitInterval1038,
          unitIntervalTruncatedPositiveSetObjective ν ≤
            unitIntervalTruncatedPositiveSetObjective η) →
        unitIntervalSecondMomentObjective μ ≤
          unitIntervalSecondMomentObjective ν) ∧
      ∃ _hEndpoint : NormalizedEndpointPotential (unitIntervalLogPotential μ),
        ENNReal.ofReal (Real.sqrt 2) ≤
          volume (PositiveSet (unitIntervalLogPotential μ)) := by
  refine
    unitIntervalTruncatedPositiveSetObjective_exists_secondMoment_normalized_endpoint_baseline_from_moment_rigidity_data
      ?_
  intro μ hPrimary hSecondary
  rcases hReplacementDataFromVariation μ hPrimary hSecondary with
    ⟨mean_choice, reflected, translation, C, R, hmass_unit, hsupport,
      xMinus, xPlus, hcomponent_interval, hbaseline, hright, hboundary,
      hprimary_replacement, hunique⟩
  have hreplacement_primary_min :
      ∀ η : ProbabilityMeasure UnitInterval1038,
        unitIntervalTruncatedPositiveSetObjective
            (componentReplacementProbability C hmass_unit) ≤
          unitIntervalTruncatedPositiveSetObjective η := by
    intro η
    exact le_trans hprimary_replacement (hPrimary η)
  have hsecondary_ge :
      unitIntervalSecondMomentObjective μ ≤
        unitIntervalSecondMomentObjective
          (componentReplacementProbability C hmass_unit) :=
    hSecondary (componentReplacementProbability C hmass_unit)
      hreplacement_primary_min
  have hsecondary_le :
      unitIntervalSecondMomentObjective
          (componentReplacementProbability C hmass_unit) ≤
        unitIntervalSecondMomentObjective μ :=
    unitIntervalSecondMomentObjective_componentReplacement_nonincrease
      R hmass_unit hsupport
  have hsecondary_eq :
      unitIntervalSecondMomentObjective
          (componentReplacementProbability C hmass_unit) =
        unitIntervalSecondMomentObjective μ :=
    le_antisymm hsecondary_le hsecondary_ge
  have hsecondMoment_eq :
      (componentMass C).toReal * (componentBarycenter C) ^ 2 =
        ∫ t : ℝ, t ^ 2 ∂componentBlock C :=
    componentBlock_secondMoment_eq_of_unitIntervalSecondMomentObjective_eq
      hmass_unit hsupport hsecondary_eq
  refine ⟨mean_choice, reflected, translation, C, R, xMinus, xPlus,
    hcomponent_interval, hbaseline, hright, hboundary, hsecondMoment_eq,
    hunique⟩

/-!
### Remaining mathematical input for `hEndpointFromVariation`

The standard-reduction layer above is intentionally conditional.  The remaining
mathematical work is now lower-level: prove the `TaoVariationComponentPackage`
provider from the positive-component variation argument plus the
translation/reflection normalization.  The package constructors above already
infer the real support facts, endpoint atom mass bookkeeping, endpoint remainder
mass/decomposition, component-inside support uniqueness from atomization, and
kernel integrability on `BaselinePunctured`.  The hard inputs that still remain
are the real positive-component selection/maximality, the admissible barycenter
replacement and secondary rigidity producing normalized atomization, and Tao's
boundary-average inequality.
-/

/--
Same endpoint baseline-length conclusion when the component/variation theorem is
already packaged as `SecondaryMinimizerNormalizationENNReal`.
-/
theorem lemma_3_2_secondary_normalization_baseline_length_ennreal
    {α Normalized : Type} [TopologicalSpace α]
    {P : SecondarySelectorProblemENNReal α}
    {normalize : α → Normalized}
    {Potential : Normalized → ℝ → ℝ}
    (hNorm : SecondaryMinimizerNormalizationENNReal P normalize Potential) :
    ∃ a : α, IsSecondaryMinimizingPrimaryMinimizerENNReal P a ∧
      ENNReal.ofReal (Real.sqrt 2) ≤
        volume (PositiveSet (Potential (normalize a))) := by
  exact hNorm.exists_baseline_length

/-! ## Polynomial-to-potential bridge for the original formulation -/

/--
The original Erdos 1038 polynomial sublevel set attached to a real polynomial:
the set where the absolute value of the polynomial is strictly below `1`.
-/
def PolynomialSublevelSet (f : Polynomial ℝ) : Set ℝ :=
  {x : ℝ | |Polynomial.eval x f| < 1}

/--
Equal-weight empirical logarithmic potential of a finite root list.  The list is
intended to carry multiplicity; the normalizing denominator is the list length.
The accompanying interface below requires this length to be positive.
-/
noncomputable def rootListEmpiricalPotential (roots : List ℝ) (x : ℝ) : ℝ :=
  (1 / (roots.length : ℝ)) *
    (roots.map (fun r : ℝ => Real.log (1 / |x - r|))).sum

/--
Polynomial-side logarithmic potential for a degree/normalization parameter `n`.
Away from roots, the identity
`rootListEmpiricalPotential roots x = polynomialLogPotential f roots.length x`
is exactly the product-factorization bridge from the empirical root measure to
the original monic-polynomial expression.
-/
noncomputable def polynomialLogPotential (f : Polynomial ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (1 / (n : ℝ)) * Real.log (1 / |Polynomial.eval x f|)

/--
Interface packaging the still-external polynomial root data needed to compare
the original monic-polynomial formulation with the measure/potential
formulation.

`roots` is a finite list with multiplicity and equal weights
`1 / roots.length`; `product_identity` records the monic product formula using
that exact list; `exceptionalSet` is a supplied null set containing the root
singularities.  This structure deliberately does not prove polynomial
factorization, multiplicity correctness, or nonvanishing away from the root
set; those facts are recorded as fields so this file does not overclaim the
remaining root machinery.
-/
structure PolynomialEmpiricalPotentialData (f : Polynomial ℝ) (U : ℝ → ℝ) where
  roots : List ℝ
  roots_nonempty : 0 < roots.length
  roots_in_unit : ∀ r : ℝ, r ∈ roots → r ∈ Set.Icc (-1 : ℝ) 1
  monic : Polynomial.Monic f
  product_identity :
    f = (roots.map (fun r : ℝ => Polynomial.X - Polynomial.C r)).prod
  exceptionalSet : Set ℝ
  exceptional_null : volume exceptionalSet = 0
  roots_subset_exception : ∀ r : ℝ, r ∈ roots → r ∈ exceptionalSet
  eval_ne_zero_away : ∀ x : ℝ, x ∉ exceptionalSet → Polynomial.eval x f ≠ 0
  potential_eq_empirical_away :
    ∀ x : ℝ, x ∉ exceptionalSet → U x = rootListEmpiricalPotential roots x
  empirical_eq_polynomial_away :
    ∀ x : ℝ, x ∉ exceptionalSet →
      rootListEmpiricalPotential roots x =
        polynomialLogPotential f roots.length x

/-- The finite exceptional set generated by a root list, forgetting multiplicity. -/
def rootListExceptionalSet (roots : List ℝ) : Set ℝ :=
  {x : ℝ | x ∈ roots.toFinset}

/-- A finite root-list exceptional set has zero Lebesgue measure. -/
theorem rootListExceptionalSet_volume_zero (roots : List ℝ) :
    volume (rootListExceptionalSet roots) = 0 := by
  classical
  simpa [rootListExceptionalSet] using
    roots.toFinset.finite_toSet.countable.measure_zero volume

/-- Every listed root lies in its finite exceptional set. -/
theorem rootListExceptionalSet_mem_of_mem {roots : List ℝ} {r : ℝ}
    (hr : r ∈ roots) :
    r ∈ rootListExceptionalSet roots := by
  classical
  simpa [rootListExceptionalSet] using hr

/--
The product identity gives nonvanishing away from the finite root-list
exceptional set.  This proves the root-side nonzero field of
`PolynomialEmpiricalPotentialData` without proving any factorization theorem.
-/
theorem polynomial_eval_ne_zero_of_product_identity_away_rootList
    {f : Polynomial ℝ} {roots : List ℝ}
    (hprod :
      f = (roots.map (fun r : ℝ => Polynomial.X - Polynomial.C r)).prod)
    {x : ℝ} (hx : x ∉ rootListExceptionalSet roots) :
    Polynomial.eval x f ≠ 0 := by
  classical
  induction roots generalizing f with
  | nil =>
      rw [hprod]
      simp
  | cons r roots ih =>
      have hxr : x - r ≠ 0 := by
        intro hzero
        have hx_eq : x = r := by linarith
        exact hx (by simp [rootListExceptionalSet, hx_eq])
      have hx_tail : x ∉ rootListExceptionalSet roots := by
        intro hx_tail
        exact hx (by
          simp [rootListExceptionalSet] at hx_tail ⊢
          exact Or.inr hx_tail)
      have htail :
          Polynomial.eval x
            ((roots.map (fun r : ℝ => Polynomial.X - Polynomial.C r)).prod) ≠ 0 :=
        ih (f := (roots.map (fun r : ℝ => Polynomial.X - Polynomial.C r)).prod)
          rfl hx_tail
      rw [hprod]
      simp [hxr, htail]

/--
Constructor using the canonical finite root-list exceptional set.

This materially narrows `PolynomialEmpiricalPotentialData`: callers no longer
provide the null exceptional set, root containment in it, or nonvanishing away
from it.  The remaining external inputs are exactly the true polynomial/root
facts: roots in the normalized interval, monicity, the explicit product
identity, the chosen potential equality, and the log/product identity away from
the finite root set.
-/
def PolynomialEmpiricalPotentialData.of_rootList
    {f : Polynomial ℝ} {U : ℝ → ℝ}
    (roots : List ℝ)
    (roots_nonempty : 0 < roots.length)
    (roots_in_unit : ∀ r : ℝ, r ∈ roots → r ∈ Set.Icc (-1 : ℝ) 1)
    (monic : Polynomial.Monic f)
    (product_identity :
      f = (roots.map (fun r : ℝ => Polynomial.X - Polynomial.C r)).prod)
    (potential_eq_empirical_away :
      ∀ x : ℝ, x ∉ rootListExceptionalSet roots →
        U x = rootListEmpiricalPotential roots x)
    (empirical_eq_polynomial_away :
      ∀ x : ℝ, x ∉ rootListExceptionalSet roots →
        rootListEmpiricalPotential roots x =
          polynomialLogPotential f roots.length x) :
    PolynomialEmpiricalPotentialData f U where
  roots := roots
  roots_nonempty := roots_nonempty
  roots_in_unit := roots_in_unit
  monic := monic
  product_identity := product_identity
  exceptionalSet := rootListExceptionalSet roots
  exceptional_null := rootListExceptionalSet_volume_zero roots
  roots_subset_exception := fun _r hr => rootListExceptionalSet_mem_of_mem hr
  eval_ne_zero_away := fun _x hx =>
    polynomial_eval_ne_zero_of_product_identity_away_rootList
      product_identity hx
  potential_eq_empirical_away := potential_eq_empirical_away
  empirical_eq_polynomial_away := empirical_eq_polynomial_away

/--
Away from the supplied null exceptional set, the packaged empirical potential is
the polynomial logarithmic potential.  This is the public bridge identity used
by the transfer theorem below.
-/
theorem PolynomialEmpiricalPotentialData.potential_eq_polynomialLogPotential_away
    {f : Polynomial ℝ} {U : ℝ → ℝ}
    (D : PolynomialEmpiricalPotentialData f U) {x : ℝ}
    (hx : x ∉ D.exceptionalSet) :
    U x = polynomialLogPotential f D.roots.length x := by
  rw [D.potential_eq_empirical_away x hx]
  exact D.empirical_eq_polynomial_away x hx

/--
For nonzero polynomial values and positive normalization `n`, positivity of the
polynomial logarithmic potential is equivalent to the original sublevel
condition `|f x| < 1`.
-/
lemma polynomialLogPotential_pos_iff_sublevel
    {f : Polynomial ℝ} {n : ℕ} (hn : 0 < n) {x : ℝ}
    (hne : Polynomial.eval x f ≠ 0) :
    0 < polynomialLogPotential f n x ↔ x ∈ PolynomialSublevelSet f := by
  unfold polynomialLogPotential PolynomialSublevelSet
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hscale_pos : 0 < (1 / (n : ℝ)) := one_div_pos.mpr hnreal
  have habspos : 0 < |Polynomial.eval x f| := abs_pos.mpr hne
  constructor
  · intro h
    have hlogpos : 0 < Real.log (1 / |Polynomial.eval x f|) :=
      (mul_pos_iff_of_pos_left hscale_pos).mp h
    have harg_nonneg : 0 ≤ 1 / |Polynomial.eval x f| :=
      le_of_lt (one_div_pos.mpr habspos)
    have hone_lt : 1 < 1 / |Polynomial.eval x f| :=
      (Real.log_pos_iff harg_nonneg).mp hlogpos
    rw [lt_div_iff₀ habspos] at hone_lt
    simpa using hone_lt
  · intro hsub
    have hone_lt : 1 < 1 / |Polynomial.eval x f| := by
      rw [lt_div_iff₀ habspos]
      simpa using hsub
    exact mul_pos hscale_pos (Real.log_pos hone_lt)

/--
The empirical-potential positive set and the original polynomial sublevel set
agree after deleting the supplied null exceptional set.  Roots and any other
singular points must already be contained in `D.exceptionalSet`.
-/
theorem PolynomialEmpiricalPotentialData.positiveSet_diff_exception_eq_sublevel_diff_exception
    {f : Polynomial ℝ} {U : ℝ → ℝ}
    (D : PolynomialEmpiricalPotentialData f U) :
    PositiveSet U \ D.exceptionalSet =
      PolynomialSublevelSet f \ D.exceptionalSet := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hpos, hnot⟩
    have hpot := D.potential_eq_polynomialLogPotential_away (x := x) hnot
    have hpos_poly : 0 < polynomialLogPotential f D.roots.length x := by
      simpa [PositiveSet, hpot] using hpos
    have hsub : x ∈ PolynomialSublevelSet f :=
      (polynomialLogPotential_pos_iff_sublevel D.roots_nonempty
        (D.eval_ne_zero_away x hnot)).mp hpos_poly
    exact ⟨hsub, hnot⟩
  · intro hx
    rcases hx with ⟨hsub, hnot⟩
    have hpos_poly : 0 < polynomialLogPotential f D.roots.length x :=
      (polynomialLogPotential_pos_iff_sublevel D.roots_nonempty
        (D.eval_ne_zero_away x hnot)).mpr hsub
    have hpot := D.potential_eq_polynomialLogPotential_away (x := x) hnot
    have hpos : x ∈ PositiveSet U := by
      simpa [PositiveSet, hpot] using hpos_poly
    exact ⟨hpos, hnot⟩

/--
Measure-level lower bounds for the potential positive set transfer to the
original polynomial sublevel set once the empirical-polynomial bridge data and
null exceptional set are supplied.
-/
theorem PolynomialEmpiricalPotentialData.measure_lower_bound_transfers_to_polynomial_sublevel
    {f : Polynomial ℝ} {U : ℝ → ℝ} {L : ℝ≥0∞}
    (D : PolynomialEmpiricalPotentialData f U)
    (hU : L ≤ volume (PositiveSet U)) :
    L ≤ volume (PolynomialSublevelSet f) := by
  have hvol_eq : volume (PositiveSet U) = volume (PolynomialSublevelSet f) := by
    calc
      volume (PositiveSet U) =
          volume (PositiveSet U \ D.exceptionalSet) := by
        rw [measure_diff_null D.exceptional_null]
      _ = volume (PolynomialSublevelSet f \ D.exceptionalSet) := by
        rw [D.positiveSet_diff_exception_eq_sublevel_diff_exception]
      _ = volume (PolynomialSublevelSet f) := by
        rw [measure_diff_null D.exceptional_null]
  exact le_of_le_of_eq hU hvol_eq

/--
Specialized bridge from the normalized endpoint lower-bound theorem in this
file to the original monic-polynomial sublevel statement.  The polynomial root
factorization/multiplicity data remain exactly the fields of
`PolynomialEmpiricalPotentialData`.
-/
theorem PolynomialEmpiricalPotentialData.baseline_length_le_polynomial_sublevel
    {f : Polynomial ℝ} {U : ℝ → ℝ}
    (D : PolynomialEmpiricalPotentialData f U)
    (hEndpoint : NormalizedEndpointPotential U) :
    ENNReal.ofReal (Real.sqrt 2) ≤ volume (PolynomialSublevelSet f) :=
  D.measure_lower_bound_transfers_to_polynomial_sublevel
    hEndpoint.baseline_length_le_positiveSet

end StandardReduction
end Erdos1038
