import Std

/-!
# Erdős 1038: formal proof skeleton for the conditional 1.8063 lower bound

Caveats:

1. This file proves only conditional implications between explicitly stated
   assumptions/certificates.
2. It does not formalize measure theory, real analysis, logarithms, geometric
   reductions, or the external numeric search.
3. The predicate `Short18` below is an abstract bad-case predicate standing for
   "length < 1.8"; the later scaled-length theorems record stronger final
   block consequences up to `1.8063`.
4. The standard reduction, baseline interval reduction, two-dimensional forcing
   selector, and four-atom selector are assumptions in this file.
5. Any Float-based checker in this repository is diagnostic evidence only, not
   a formal proof of the numeric certificate unless a separate sound rational
   interval kernel is proved.

The local project currently has Lean 4 + Std, but not Mathlib.  Therefore this
file does **not** formalize logarithmic potentials, Lebesgue measure, or the
Tao/natso minimizer reduction.  Instead it formalizes the logical spine of the
current proof package:

1. the standard reduction is an external assumption;
2. the two-parameter forcing certificate supplies a selector implication;
3. the finite-atom block supplies the final length once `(-1.7,0)` is known to
   be contained in the positive set;
4. these two branches imply conditional lower bounds through `1.8063`.

Lengths are represented as natural numbers in units of `1/10000`.  Thus

* `18000` means `1.8`;
* `18063` means `1.8063`;
* `18200` means `1.82`;
* `17000` means `1.7`;
* `1000` means `0.1`.

The numerical log certificates themselves are checked in `LeanCertificates.lean`.
This file is a proof-chain ledger: it prevents the project from silently
conflating external analytic assumptions with the finite certificates.
-/

namespace Erdos1038

abbrev ScaledLength := Nat

def length_17 : ScaledLength := 17000
def length_01 : ScaledLength := 1000
def length_0103 : ScaledLength := 1030
def length_18 : ScaledLength := 18000
def length_1803 : ScaledLength := 18030
def length_18035 : ScaledLength := 18035
def length_1804 : ScaledLength := 18040
def length_1805 : ScaledLength := 18050
def length_1806 : ScaledLength := 18060
def length_18063 : ScaledLength := 18063
def length_182 : ScaledLength := 18200

/-! ## Exact arithmetic used by the covering argument -/

theorem fourAtomLengthArithmetic : length_17 + length_01 = length_18 := by
  rfl

theorem forcingBranchIsStrongerThan18 : length_18 ≤ length_182 := by
  decide

theorem strongerFourAtomLengthArithmetic : length_17 + length_0103 = length_1803 := by
  rfl

theorem forcingBranchIsStrongerThan1803 : length_1803 ≤ length_182 := by
  decide

theorem forcingBranchIsStrongerThan18035 : length_18035 ≤ length_182 := by
  decide

theorem forcingBranchIsStrongerThan1804 : length_1804 ≤ length_182 := by
  decide

theorem forcingBranchIsStrongerThan1805 : length_1805 ≤ length_182 := by
  decide

theorem forcingBranchIsStrongerThan1806 : length_1806 ≤ length_182 := by
  decide

theorem forcingBranchIsStrongerThan18063 : length_18063 ≤ length_182 := by
  decide

theorem disjointSweepArithmetic : 2 * 4058 < 10710 := by
  decide

theorem conservativeSweepBound : 4058 < 5355 := by
  decide

/-! ## Abstract no-counterexample pipeline -/

section AbstractPipeline

variable {Config Normalized : Type}

variable (Admissible : Config → Prop)
variable (Short18 : Config → Prop)
variable (normalize : Config → Normalized)
variable (Baseline : Normalized → Prop)
variable (TwoDForced : Normalized → Prop)
variable (FourAtomForced : Normalized → Prop)

/--
External certificate 1: every admissible short counterexample can be reduced
to the normalized baseline regime.
-/
structure StandardReductionCert : Prop where
  reduce :
    ∀ c, Admissible c → Short18 c → Baseline (normalize c)

/--
External certificate 2: the baseline regime is covered by the two available
selector mechanisms.
-/
structure BaselineSelectorCert : Prop where
  cover :
    ∀ n, Baseline n → TwoDForced n ∨ FourAtomForced n

/--
External certificate 3: the two-dimensional forcing selector excludes every
short counterexample in its case.
-/
structure TwoDForcingCert : Prop where
  impossible :
    ∀ c, Admissible c → Short18 c → TwoDForced (normalize c) → False

/--
External certificate 4: the four-atom selector excludes every short
counterexample in its case.
-/
structure FourAtomCert : Prop where
  impossible :
    ∀ c, Admissible c → Short18 c → FourAtomForced (normalize c) → False

theorem noShort18Counterexample
    (std : StandardReductionCert Admissible Short18 normalize Baseline)
    (sel : BaselineSelectorCert Baseline TwoDForced FourAtomForced)
    (two : TwoDForcingCert Admissible Short18 normalize TwoDForced)
    (four : FourAtomCert Admissible Short18 normalize FourAtomForced) :
    ¬ ∃ c, Admissible c ∧ Short18 c := by
  intro h
  rcases h with ⟨c, hcAdmissible, hcShort⟩
  have hb : Baseline (normalize c) :=
    std.reduce c hcAdmissible hcShort
  cases sel.cover (normalize c) hb with
  | inl hTwo =>
      exact two.impossible c hcAdmissible hcShort hTwo
  | inr hFour =>
      exact four.impossible c hcAdmissible hcShort hFour

end AbstractPipeline

/-!
`LongInterval` abstracts the statement `(-1.7,0) subset E_mu`.

`LengthAtLeast n` abstracts the statement `|E_mu| >= n/10000`.

The two branch assumptions correspond exactly to the current paper proof:

* if `LongInterval` fails, the certified two-parameter forcing family gives
  the stronger bound `1.82`;
* if `LongInterval` holds, the high-margin four-atom block gives `1.8`.
-/

structure ConditionalLowerBoundInputs where
  LongInterval : Prop
  LengthAtLeast : ScaledLength → Prop
  monotone :
    ∀ {m n : ScaledLength}, m ≤ n → LengthAtLeast n → LengthAtLeast m
  forcingBranch :
    ¬ LongInterval → LengthAtLeast length_182
  fourAtomBranch :
    LongInterval → LengthAtLeast length_18

theorem conditionalLowerBound18
    (inputs : ConditionalLowerBoundInputs) :
    inputs.LengthAtLeast length_18 := by
  by_cases h : inputs.LongInterval
  · exact inputs.fourAtomBranch h
  · exact inputs.monotone forcingBranchIsStrongerThan18 (inputs.forcingBranch h)

structure Stronger1803Inputs where
  LongInterval : Prop
  LengthAtLeast : ScaledLength → Prop
  monotone :
    ∀ {m n : ScaledLength}, m ≤ n → LengthAtLeast n → LengthAtLeast m
  forcingBranch :
    ¬ LongInterval → LengthAtLeast length_182
  strongerFourAtomBranch :
    LongInterval → LengthAtLeast length_1803

theorem conditionalLowerBound1803
    (inputs : Stronger1803Inputs) :
    inputs.LengthAtLeast length_1803 := by
  by_cases h : inputs.LongInterval
  · exact inputs.strongerFourAtomBranch h
  · exact inputs.monotone forcingBranchIsStrongerThan1803 (inputs.forcingBranch h)

structure Stronger18035Inputs where
  LongInterval : Prop
  LengthAtLeast : ScaledLength → Prop
  monotone :
    ∀ {m n : ScaledLength}, m ≤ n → LengthAtLeast n → LengthAtLeast m
  forcingBranch :
    ¬ LongInterval → LengthAtLeast length_182
  strongerFourAtomBranch :
    LongInterval → LengthAtLeast length_18035

theorem conditionalLowerBound18035
    (inputs : Stronger18035Inputs) :
    inputs.LengthAtLeast length_18035 := by
  by_cases h : inputs.LongInterval
  · exact inputs.strongerFourAtomBranch h
  · exact inputs.monotone forcingBranchIsStrongerThan18035 (inputs.forcingBranch h)

structure Stronger1804Inputs where
  LongInterval : Prop
  LengthAtLeast : ScaledLength → Prop
  monotone :
    ∀ {m n : ScaledLength}, m ≤ n → LengthAtLeast n → LengthAtLeast m
  forcingBranch :
    ¬ LongInterval → LengthAtLeast length_182
  strongerFiveAtomBranch :
    LongInterval → LengthAtLeast length_1804

theorem conditionalLowerBound1804
    (inputs : Stronger1804Inputs) :
    inputs.LengthAtLeast length_1804 := by
  by_cases h : inputs.LongInterval
  · exact inputs.strongerFiveAtomBranch h
  · exact inputs.monotone forcingBranchIsStrongerThan1804 (inputs.forcingBranch h)

structure Stronger1805Inputs where
  LongInterval : Prop
  LengthAtLeast : ScaledLength → Prop
  monotone :
    ∀ {m n : ScaledLength}, m ≤ n → LengthAtLeast n → LengthAtLeast m
  forcingBranch :
    ¬ LongInterval → LengthAtLeast length_182
  strongerFiveAtomBranch :
    LongInterval → LengthAtLeast length_1805

theorem conditionalLowerBound1805
    (inputs : Stronger1805Inputs) :
    inputs.LengthAtLeast length_1805 := by
  by_cases h : inputs.LongInterval
  · exact inputs.strongerFiveAtomBranch h
  · exact inputs.monotone forcingBranchIsStrongerThan1805 (inputs.forcingBranch h)

structure Stronger1806Inputs where
  LongInterval : Prop
  LengthAtLeast : ScaledLength → Prop
  monotone :
    ∀ {m n : ScaledLength}, m ≤ n → LengthAtLeast n → LengthAtLeast m
  forcingBranch :
    ¬ LongInterval → LengthAtLeast length_182
  strongerFiveAtomBranch :
    LongInterval → LengthAtLeast length_1806

theorem conditionalLowerBound1806
    (inputs : Stronger1806Inputs) :
    inputs.LengthAtLeast length_1806 := by
  by_cases h : inputs.LongInterval
  · exact inputs.strongerFiveAtomBranch h
  · exact inputs.monotone forcingBranchIsStrongerThan1806 (inputs.forcingBranch h)

structure Stronger18063Inputs where
  LongInterval : Prop
  LengthAtLeast : ScaledLength → Prop
  monotone :
    ∀ {m n : ScaledLength}, m ≤ n → LengthAtLeast n → LengthAtLeast m
  forcingBranch :
    ¬ LongInterval → LengthAtLeast length_182
  strongerFiveAtomBranch :
    LongInterval → LengthAtLeast length_18063

theorem conditionalLowerBound18063
    (inputs : Stronger18063Inputs) :
    inputs.LengthAtLeast length_18063 := by
  by_cases h : inputs.LongInterval
  · exact inputs.strongerFiveAtomBranch h
  · exact inputs.monotone forcingBranchIsStrongerThan18063 (inputs.forcingBranch h)

/-!
Forum-safe reading of `conditionalLowerBound18063`:

If the standard reduction and the two finite certificate implications are
accepted, then the reduced minimizer satisfies `|E_mu| >= 1.8063`.

This theorem intentionally does not claim the standard reduction, the
potential-theoretic duality lemma, or the logarithm interval bounds as Lean
theorems.
-/

end Erdos1038
