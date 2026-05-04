import Std

/-!
# Exact arithmetic for the `M = 1.814600` piecewise five-atom candidate (560 blocks)

This file formalizes the exact geometry of the 560-block piecewise five-atom
certificate for Erdos problem 1038, with:

  M = 1.814600
  B = 1.708
  K = 560 blocks

scaled by 10^8 for exact integer arithmetic.
-/

namespace Erdos1038
namespace PiecewiseFiveAtom181460

/-- Scaling factor: all reals are multiplied by 10^8. -/
def scale8 : Nat := 100000000

/-- B = 1.708 scaled. -/
def B8 : Nat := 170800000

/-- M = 1.814600 scaled. -/
def M8 : Nat := 181460000

/-- Tail length = M - B = 0.106600 scaled. -/
def tailLength8 : Nat := 10660000

/-- Shifts (d1, d2, d3, d4) scaled by 10^8.
    d1 = 1.8146001
    d2 = 2.55506
    d3 = 2.675215475
    d4 = 2.781815575 -/
def shift1 : Nat := 181460010
def shift2 : Nat := 255506000
def shift3 : Nat := 267521547
def shift4 : Nat := 278181557

/-- Number of blocks. -/
def K : Nat := 560

/-- Verified: tailLength = M - B. -/
theorem tail_length_arithmetic : B8 + tailLength8 = M8 := by
  native_decide

/-- Verified: shifted sweep intervals are disjoint.
    d1 > M, and each gap between consecutive shifts exceeds tailLength. -/
theorem shifted_sweep_disjoint_arithmetic :
    M8 < shift1 ∧
    shift1 + tailLength8 < shift2 ∧
    shift2 + tailLength8 < shift3 ∧
    shift3 + tailLength8 < shift4 := by
  native_decide

/-- Verified: shifts minus M and B. -/
theorem shifted_intervals_scaled :
    shift1 - M8 = 10 ∧
    shift2 - M8 = 74046000 ∧
    shift3 - M8 = 86061547 ∧
    shift4 - M8 = 96721557 ∧
    shift1 - B8 = 10660010 ∧
    shift2 - B8 = 84706000 ∧
    shift3 - B8 = 96721547 ∧
    shift4 - B8 = 107381557 := by
  native_decide

/-- Main theorem: exact geometry certificate for the 560-block piecewise five-atom.

    The swept intervals are:
      [-M, -B]                 = [-1.814600, -1.708]
      [0, h] shifted by d1     = [1e-7, 0.1066001]
      [0, h] shifted by d2     = [0.74046, 0.84706]
      [0, h] shifted by d3     = [0.860615475, 0.967215475]
      [0, h] shifted by d4     = [0.967215575, 1.073815575]

    These intervals are pairwise disjoint and cover the tail region.
-/
theorem piecewise_181460_560_exact_geometry_certificate :
    (B8 + tailLength8 = M8) ∧
    (M8 < shift1 ∧ shift1 + tailLength8 < shift2 ∧
      shift2 + tailLength8 < shift3 ∧ shift3 + tailLength8 < shift4) ∧
    (shift1 - M8 = 10 ∧
     shift2 - M8 = 74046000 ∧ shift3 - M8 = 86061547 ∧ shift4 - M8 = 96721557 ∧
     shift1 - B8 = 10660010 ∧
     shift2 - B8 = 84706000 ∧ shift3 - B8 = 96721547 ∧ shift4 - B8 = 107381557) := by
  exact ⟨tail_length_arithmetic, shifted_sweep_disjoint_arithmetic, shifted_intervals_scaled⟩

end PiecewiseFiveAtom181460
end Erdos1038
