import Mathlib.Tactic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

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

end

end StandardReduction
end Erdos1038
