import Mathlib.Tactic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
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

This structure records the remaining external variational input.  Downstream Lean files
can state exactly where the Tao/natso variational reduction is used.
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
Bridge from Tao's component-reduction data to the normalized endpoint-potential
interface used by the finite-atom route.  The field `endpointLowerBound` is the
analytic support-to-potential lower bound obtained from the normalized support
configuration.
-/
structure TaoReducedPotentialData (U : ℝ → ℝ) extends TaoComponentReductionData where
  endpointLowerBound : HasNormalizedEndpointLowerBound U endpointMass

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
problem-specific placeholder.
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

theorem measure_barycenter_second_moment_eq_imp_eq_dirac_at_mean
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hfirst : Integrable (fun t : ℝ => t) μ)
    (hsecond : Integrable (fun t : ℝ => t ^ 2) μ)
    (heq : (∫ t : ℝ, t ^ 2 ∂μ) = (∫ t : ℝ, t ∂μ) ^ 2) :
    μ = Measure.dirac (∫ t : ℝ, t ∂μ) := by
  exact measure_eq_dirac_of_ae_eq_const μ (∫ t : ℝ, t ∂μ)
    (measure_barycenter_second_moment_eq_imp_ae_eq_mean μ
      hfirst hsecond heq)

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

end

end StandardReduction
end Erdos1038
