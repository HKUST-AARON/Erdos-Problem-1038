import Mathlib

/-!
# Common finite-atom framework

This file formalizes the finite-atom forcing step used by the 1038 finite
certificate packages.

It does not use logarithmic potential theory directly.  Instead it proves the
finite algebraic implication that the duality identity supplies in the notes:
if a positive weighted finite sum is positive, while every atom outside the
positive set has non-positive primal potential, then at least one atom must lie
inside the positive set.

The theorems named `*_from_duality` formalize the next interface layer: once
the potential-theoretic duality argument has produced a positive dual quantity
equal to the finite weighted atom sum, the selector conclusion follows.
-/

namespace Erdos1038
namespace FiniteAtomFramework

open Finset

/-- A finite atom with location and positive weight. -/
structure Atom where
  x : ℝ
  w : ℝ

def weightedPotentialSum (U : ℝ → ℝ) (atoms : List Atom) : ℝ :=
  (atoms.map fun A => A.w * U A.x).sum

/-- If all atom weights are positive and all atom potentials are non-positive,
then the weighted potential sum is non-positive. -/
lemma weighted_sum_nonpos_of_all_nonpos
    (U : ℝ → ℝ) :
    ∀ atoms : List Atom,
      (∀ A ∈ atoms, 0 < A.w) →
      (∀ A ∈ atoms, U A.x ≤ 0) →
      weightedPotentialSum U atoms ≤ 0
  | [], _, _ => by simp [weightedPotentialSum]
  | A :: rest, hpos, hnonpos => by
      have hApos : 0 < A.w := hpos A (by simp)
      have hAnon : U A.x ≤ 0 := hnonpos A (by simp)
      have hterm : A.w * U A.x ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos hApos.le hAnon
      have hrest : weightedPotentialSum U rest ≤ 0 := by
        apply weighted_sum_nonpos_of_all_nonpos
        · intro B hB
          exact hpos B (by simp [hB])
        · intro B hB
          exact hnonpos B (by simp [hB])
      have hrest' : (rest.map fun A => A.w * U A.x).sum ≤ 0 := by
        simpa [weightedPotentialSum] using hrest
      simp [weightedPotentialSum]
      linarith

/--
Finite dual-forcing lemma.  If the weighted potential sum over the dual atoms is
positive, and outside `E` the primal potential is non-positive, then at least one
of the dual atoms lies in `E`.
-/
theorem finite_dual_forcing
    (U : ℝ → ℝ) (E : Set ℝ) (atoms : List Atom)
    (hposWeights : ∀ A ∈ atoms, 0 < A.w)
    (houtside : ∀ x : ℝ, x ∉ E → U x ≤ 0)
    (hsum : 0 < weightedPotentialSum U atoms) :
    ∃ A ∈ atoms, A.x ∈ E := by
  by_contra hnone
  have hall_nonpos : ∀ A ∈ atoms, U A.x ≤ 0 := by
    intro A hA
    apply houtside
    intro hAE
    exact hnone ⟨A, hA, hAE⟩
  have hle := weighted_sum_nonpos_of_all_nonpos U atoms hposWeights hall_nonpos
  linarith

/--
Duality-to-selector bridge for a finite dual measure.

Here `dualMass` is the positive quantity supplied by the
potential-theoretic side, for instance an integral of the dual potential
against the primal measure.  The hypothesis `hduality` is the finite-atom form
of the symmetry identity, identifying that positive quantity with the weighted
sum of the primal potential over the dual atoms.
-/
theorem finite_atom_selector_from_duality
    (U : ℝ → ℝ) (E : Set ℝ) (atoms : List Atom)
    (dualMass : ℝ)
    (hposWeights : ∀ A ∈ atoms, 0 < A.w)
    (houtside : ∀ x : ℝ, x ∉ E → U x ≤ 0)
    (hdualPositive : 0 < dualMass)
    (hduality : dualMass = weightedPotentialSum U atoms) :
    ∃ A ∈ atoms, A.x ∈ E := by
  apply finite_dual_forcing U E atoms hposWeights houtside
  simpa [hduality] using hdualPositive

/-- Specialized five-atom version used by the tail block. -/
theorem five_atom_forcing
    (U : ℝ → ℝ) (E : Set ℝ)
    (x0 x1 x2 x3 x4 w0 w1 w2 w3 w4 : ℝ)
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2)
    (hw3 : 0 < w3) (hw4 : 0 < w4)
    (houtside : ∀ x : ℝ, x ∉ E → U x ≤ 0)
    (hsum : 0 <
        w0 * U x0 + w1 * U x1 + w2 * U x2 + w3 * U x3 + w4 * U x4) :
    x0 ∈ E ∨ x1 ∈ E ∨ x2 ∈ E ∨ x3 ∈ E ∨ x4 ∈ E := by
  let atoms : List Atom := [
    { x := x0, w := w0 },
    { x := x1, w := w1 },
    { x := x2, w := w2 },
    { x := x3, w := w3 },
    { x := x4, w := w4 }]
  have hposWeights : ∀ A ∈ atoms, 0 < A.w := by
    intro A hA
    simp [atoms] at hA
    rcases hA with hA | hA | hA | hA | hA
    · simpa [hA] using hw0
    · simpa [hA] using hw1
    · simpa [hA] using hw2
    · simpa [hA] using hw3
    · simpa [hA] using hw4
  have hsumAtoms : 0 < weightedPotentialSum U atoms := by
    simp [weightedPotentialSum, atoms]
    linarith
  rcases finite_dual_forcing U E atoms hposWeights houtside hsumAtoms with ⟨A, hA, hAE⟩
  simp [atoms] at hA
  rcases hA with hA | hA | hA | hA | hA
  · exact Or.inl (by simpa [hA] using hAE)
  · exact Or.inr (Or.inl (by simpa [hA] using hAE))
  · exact Or.inr (Or.inr (Or.inl (by simpa [hA] using hAE)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa [hA] using hAE))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (by simpa [hA] using hAE))))

/-- Five-atom selector obtained from a duality identity. -/
theorem five_atom_selector_from_duality
    (U : ℝ → ℝ) (E : Set ℝ)
    (x0 x1 x2 x3 x4 w0 w1 w2 w3 w4 : ℝ)
    (dualMass : ℝ)
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2)
    (hw3 : 0 < w3) (hw4 : 0 < w4)
    (houtside : ∀ x : ℝ, x ∉ E → U x ≤ 0)
    (hdualPositive : 0 < dualMass)
    (hduality : dualMass =
        w0 * U x0 + w1 * U x1 + w2 * U x2 + w3 * U x3 + w4 * U x4) :
    x0 ∈ E ∨ x1 ∈ E ∨ x2 ∈ E ∨ x3 ∈ E ∨ x4 ∈ E := by
  apply five_atom_forcing U E x0 x1 x2 x3 x4 w0 w1 w2 w3 w4
  · exact hw0
  · exact hw1
  · exact hw2
  · exact hw3
  · exact hw4
  · exact houtside
  · simpa [hduality] using hdualPositive

/-- Specialized three-atom version used by the forcing branch. -/
theorem three_atom_forcing
    (U : ℝ → ℝ) (E : Set ℝ)
    (x0 x1 x2 w0 w1 w2 : ℝ)
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2)
    (houtside : ∀ x : ℝ, x ∉ E → U x ≤ 0)
    (hsum : 0 < w0 * U x0 + w1 * U x1 + w2 * U x2) :
    x0 ∈ E ∨ x1 ∈ E ∨ x2 ∈ E := by
  let atoms : List Atom := [
    { x := x0, w := w0 },
    { x := x1, w := w1 },
    { x := x2, w := w2 }]
  have hposWeights : ∀ A ∈ atoms, 0 < A.w := by
    intro A hA
    simp [atoms] at hA
    rcases hA with hA | hA | hA
    · simpa [hA] using hw0
    · simpa [hA] using hw1
    · simpa [hA] using hw2
  have hsumAtoms : 0 < weightedPotentialSum U atoms := by
    simp [weightedPotentialSum, atoms]
    linarith
  rcases finite_dual_forcing U E atoms hposWeights houtside hsumAtoms with ⟨A, hA, hAE⟩
  simp [atoms] at hA
  rcases hA with hA | hA | hA
  · exact Or.inl (by simpa [hA] using hAE)
  · exact Or.inr (Or.inl (by simpa [hA] using hAE))
  · exact Or.inr (Or.inr (by simpa [hA] using hAE))

/-- Three-atom selector obtained from a duality identity. -/
theorem three_atom_selector_from_duality
    (U : ℝ → ℝ) (E : Set ℝ)
    (x0 x1 x2 w0 w1 w2 : ℝ)
    (dualMass : ℝ)
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2)
    (houtside : ∀ x : ℝ, x ∉ E → U x ≤ 0)
    (hdualPositive : 0 < dualMass)
    (hduality : dualMass = w0 * U x0 + w1 * U x1 + w2 * U x2) :
    x0 ∈ E ∨ x1 ∈ E ∨ x2 ∈ E := by
  apply three_atom_forcing U E x0 x1 x2 w0 w1 w2
  · exact hw0
  · exact hw1
  · exact hw2
  · exact houtside
  · simpa [hduality] using hdualPositive

end FiniteAtomFramework
end Erdos1038
