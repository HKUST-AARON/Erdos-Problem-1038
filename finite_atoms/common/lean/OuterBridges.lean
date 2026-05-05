import Mathlib

/-!
# Outer bridge lemmas for Erdős 1038

This file contains two independent outer layers that do not use the Tao/natso
standard reduction:

* finite root-list polynomial-to-potential identities;
* compactness/lower-semicontinuity minimizer-existence lemmas.

The finite-atom certificate can depend on the standard reduction separately;
these bridges are reusable outer infrastructure.
-/

namespace Erdos1038
namespace OuterBridges

noncomputable section

open Set
open scoped ENNReal BigOperators

/-! ## Polynomial-to-potential bridge for finite root lists -/

/-- Product polynomial value represented by a finite root list. -/
def rootProduct (roots : List ℝ) (x : ℝ) : ℝ :=
  (roots.map fun t => x - t).prod

/-- Sum version of the logarithmic potential for an equal-weight finite root list. -/
def rootLogPotentialSum (roots : List ℝ) (x : ℝ) : ℝ :=
  (roots.map fun t => Real.log (1 / |x - t|)).sum

/-- Equal-weight empirical logarithmic potential for a nonempty finite root list. -/
def empiricalRootPotential (roots : List ℝ) (x : ℝ) : ℝ :=
  rootLogPotentialSum roots x / (roots.length : ℝ)

lemma abs_rootProduct_pos_of_not_mem {roots : List ℝ} {x : ℝ}
    (hx : ∀ t ∈ roots, x ≠ t) : 0 < |rootProduct roots x| := by
  induction roots with
  | nil =>
      simp [rootProduct]
  | cons t roots ih =>
      have hxt : x ≠ t := hx t (by simp)
      have hxroots : ∀ u ∈ roots, x ≠ u := by
        intro u hu
        exact hx u (by simp [hu])
      have htpos : 0 < |x - t| := abs_pos.mpr (sub_ne_zero.mpr hxt)
      have htail : 0 < |rootProduct roots x| := ih hxroots
      simpa [rootProduct, abs_mul] using mul_pos htpos htail

lemma rootLogPotentialSum_eq_log_inv_abs_rootProduct {roots : List ℝ} {x : ℝ}
    (hx : ∀ t ∈ roots, x ≠ t) :
    rootLogPotentialSum roots x = Real.log (1 / |rootProduct roots x|) := by
  induction roots with
  | nil =>
      simp [rootLogPotentialSum, rootProduct]
  | cons t roots ih =>
      have hxt : x ≠ t := hx t (by simp)
      have hxroots : ∀ u ∈ roots, x ≠ u := by
        intro u hu
        exact hx u (by simp [hu])
      have htpos : 0 < |x - t| := abs_pos.mpr (sub_ne_zero.mpr hxt)
      have hprodpos : 0 < |rootProduct roots x| :=
        abs_rootProduct_pos_of_not_mem hxroots
      have hmulpos : 0 < |x - t| * |rootProduct roots x| :=
        mul_pos htpos hprodpos
      have h_one_div_mul :
          1 / (|x - t| * |rootProduct roots x|) =
            (1 / |x - t|) * (1 / |rootProduct roots x|) := by
        field_simp [(ne_of_gt htpos), (ne_of_gt hprodpos), (ne_of_gt hmulpos)]
      have hlog_mul :
          Real.log (1 / (|x - t| * |rootProduct roots x|)) =
            Real.log (1 / |x - t|) + Real.log (1 / |rootProduct roots x|) := by
        rw [h_one_div_mul]
        exact Real.log_mul (one_div_ne_zero (ne_of_gt htpos))
          (one_div_ne_zero (ne_of_gt hprodpos))
      calc
        rootLogPotentialSum (t :: roots) x
            = Real.log (1 / |x - t|) + rootLogPotentialSum roots x := by
                simp [rootLogPotentialSum]
        _ = Real.log (1 / |x - t|) + Real.log (1 / |rootProduct roots x|) := by
                rw [ih hxroots]
        _ = Real.log (1 / (|x - t| * |rootProduct roots x|)) := by
                rw [hlog_mul]
        _ = Real.log (1 / |rootProduct (t :: roots) x|) := by
                simp [rootProduct, abs_mul, mul_comm]

lemma empiricalRootPotential_eq_log_inv_abs_rootProduct_div_length
    {roots : List ℝ} {x : ℝ}
    (hx : ∀ t ∈ roots, x ≠ t) :
    empiricalRootPotential roots x =
      Real.log (1 / |rootProduct roots x|) / (roots.length : ℝ) := by
  simp [empiricalRootPotential, rootLogPotentialSum_eq_log_inv_abs_rootProduct hx]

lemma log_one_div_abs_rootProduct_pos_iff {roots : List ℝ} {x : ℝ}
    (hx : ∀ t ∈ roots, x ≠ t) :
    0 < Real.log (1 / |rootProduct roots x|) ↔ |rootProduct roots x| < 1 := by
  have hpos : 0 < |rootProduct roots x| := abs_rootProduct_pos_of_not_mem hx
  constructor
  · intro hlog
    have hone_lt : 1 < 1 / |rootProduct roots x| :=
      (Real.log_pos_iff (one_div_pos.mpr hpos).le).mp hlog
    exact (one_div_lt_one_div zero_lt_one hpos).mp (by simpa using hone_lt)
  · intro hlt
    have hone_lt : 1 < 1 / |rootProduct roots x| := by
      exact one_lt_one_div hpos hlt
    exact (Real.log_pos_iff (one_div_pos.mpr hpos).le).mpr hone_lt

/-- For nonempty root lists, positivity of the empirical potential is exactly `|f(x)| < 1`. -/
theorem empiricalRootPotential_pos_iff_abs_rootProduct_lt_one
    {roots : List ℝ} {x : ℝ}
    (hne : roots.length ≠ 0)
    (hx : ∀ t ∈ roots, x ≠ t) :
    0 < empiricalRootPotential roots x ↔ |rootProduct roots x| < 1 := by
  have hlen_pos_nat : 0 < roots.length := Nat.pos_of_ne_zero hne
  have hlen_pos : 0 < (roots.length : ℝ) := by exact_mod_cast hlen_pos_nat
  rw [empiricalRootPotential_eq_log_inv_abs_rootProduct_div_length hx]
  constructor
  · intro h
    have hlog : 0 < Real.log (1 / |rootProduct roots x|) := by
      exact (div_pos_iff_of_pos_right hlen_pos).mp h
    exact (log_one_div_abs_rootProduct_pos_iff hx).mp hlog
  · intro h
    have hlog : 0 < Real.log (1 / |rootProduct roots x|) :=
      (log_one_div_abs_rootProduct_pos_iff hx).mpr h
    exact div_pos hlog hlen_pos

/-! ## Compactness / minimizer-existence bridge -/

/-- Direct method for real-valued lower-semicontinuous objectives on compact nonempty sets. -/
theorem compact_nonempty_lsc_exists_minimizer_real
    {α : Type*} [TopologicalSpace α]
    (s : Set α) (objective : α → ℝ)
    (hne : s.Nonempty)
    (hcompact : IsCompact s)
    (hlsc : LowerSemicontinuousOn objective s) :
    ∃ a : α, a ∈ s ∧ ∀ b : α, b ∈ s → objective a ≤ objective b := by
  rcases hlsc.exists_isMinOn hne hcompact with ⟨a, ha, hmin⟩
  exact ⟨a, ha, fun b hb => hmin hb⟩

/-- Direct method for extended nonnegative objectives on compact nonempty sets. -/
theorem compact_nonempty_lsc_exists_minimizer_ennreal
    {α : Type*} [TopologicalSpace α]
    (s : Set α) (objective : α → ℝ≥0∞)
    (hne : s.Nonempty)
    (hcompact : IsCompact s)
    (hlsc : LowerSemicontinuousOn objective s) :
    ∃ a : α, a ∈ s ∧ ∀ b : α, b ∈ s → objective a ≤ objective b := by
  rcases hlsc.exists_isMinOn hne hcompact with ⟨a, ha, hmin⟩
  exact ⟨a, ha, fun b hb => hmin hb⟩

/-- Compact-space version for real-valued lower-semicontinuous objectives. -/
theorem compactSpace_lsc_exists_minimizer_real
    {α : Type*} [TopologicalSpace α] [CompactSpace α] [Nonempty α]
    (objective : α → ℝ)
    (hlsc : LowerSemicontinuous objective) :
    ∃ a : α, ∀ b : α, objective a ≤ objective b := by
  have hne : (Set.univ : Set α).Nonempty := Set.univ_nonempty
  have hlscOn : LowerSemicontinuousOn objective (Set.univ : Set α) :=
    hlsc.lowerSemicontinuousOn (Set.univ : Set α)
  rcases compact_nonempty_lsc_exists_minimizer_real
      (Set.univ : Set α) objective hne isCompact_univ hlscOn with
    ⟨a, _ha, hmin⟩
  exact ⟨a, fun b => hmin b trivial⟩

/-- Compact-space version for extended nonnegative lower-semicontinuous objectives. -/
theorem compactSpace_lsc_exists_minimizer_ennreal
    {α : Type*} [TopologicalSpace α] [CompactSpace α] [Nonempty α]
    (objective : α → ℝ≥0∞)
    (hlsc : LowerSemicontinuous objective) :
    ∃ a : α, ∀ b : α, objective a ≤ objective b := by
  have hne : (Set.univ : Set α).Nonempty := Set.univ_nonempty
  have hlscOn : LowerSemicontinuousOn objective (Set.univ : Set α) :=
    hlsc.lowerSemicontinuousOn (Set.univ : Set α)
  rcases compact_nonempty_lsc_exists_minimizer_ennreal
      (Set.univ : Set α) objective hne isCompact_univ hlscOn with
    ⟨a, _ha, hmin⟩
  exact ⟨a, fun b => hmin b trivial⟩

/-- Secondary minimizer on the compact argmin set of an extended primary objective. -/
theorem compactSpace_lsc_exists_secondary_minimizer_ennreal_primary
    {α : Type*} [TopologicalSpace α] [CompactSpace α] [Nonempty α]
    (primary : α → ℝ≥0∞) (secondary : α → ℝ)
    (hprimary_lsc : LowerSemicontinuous primary)
    (hsecondary_lsc : LowerSemicontinuous secondary) :
    ∃ a : α,
      (∀ b : α, primary a ≤ primary b) ∧
      ∀ b : α, (∀ c : α, primary b ≤ primary c) → secondary a ≤ secondary b := by
  rcases compactSpace_lsc_exists_minimizer_ennreal primary hprimary_lsc with ⟨a0, ha0⟩
  let Argmin : α → Prop := fun a => ∀ b : α, primary a ≤ primary b
  have hne : ∃ a : α, Argmin a := ⟨a0, ha0⟩
  have hArgmin_eq : {a : α | Argmin a} = primary ⁻¹' Iic (primary a0) := by
    ext a
    constructor
    · intro ha
      exact ha a0
    · intro ha b
      exact le_trans ha (ha0 b)
  have hcompact : IsCompact {a : α | Argmin a} := by
    rw [hArgmin_eq]
    exact (hprimary_lsc.isClosed_preimage (primary a0)).isCompact
  have hsecOn : LowerSemicontinuousOn secondary {a : α | Argmin a} :=
    hsecondary_lsc.lowerSemicontinuousOn {a : α | Argmin a}
  rcases hsecOn.exists_isMinOn hne hcompact with ⟨a, ha, hminsec⟩
  exact ⟨a, ha, fun b hb => hminsec hb⟩

end

end OuterBridges
end Erdos1038
