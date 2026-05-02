import Std

/-!
# Exact Lean arithmetic for the five-atom `M = 1.806304` tail certificate

This file is deliberately narrow.  It does **not** claim a full Mathlib
formalization of Erdős 1038, logarithmic potentials, Lebesgue measure, or
`Real.log` interval bounds.

What it does prove in Lean's kernel:

* the exact integer sign checks for the quartic numerator of `V'`;
* the exact geometry/disjointness arithmetic for the moving five-atom sweep;
* the exact scaled-length implication `1.708 + 0.098304 = 1.806304`;

The actual logarithmic lower bounds are still checked by the Decimal interval
checker in `verify_one_variable_certificates.py`.  Without Mathlib's real
analysis library, this local Lean project cannot honestly state or prove the
corresponding `Real.log` theorem.
-/

namespace Erdos1038
namespace FiveAtom1806304

/-! ## Scale conventions -/

def scale8 : Nat := 100000000

def T8 : Nat := 170800000
def M8 : Nat := 180630400
def tailLength8 : Nat := 9830400

def shift1 : Nat := 180650001
def shift2 : Nat := 257053197
def shift3 : Nat := 268367709
def shift4 : Nat := 279017717


theorem tail_length_arithmetic : T8 + tailLength8 = M8 := by
  native_decide

theorem first_shift_starts_after_zero : M8 < shift1 := by
  native_decide

theorem shift12_gap_disjoint : tailLength8 < shift2 - shift1 := by
  native_decide

theorem shift23_gap_disjoint : tailLength8 < shift3 - shift2 := by
  native_decide

theorem shift34_gap_disjoint : tailLength8 < shift4 - shift3 := by
  native_decide

theorem sweep_geometry_certificate :
    M8 < shift1 ∧
    tailLength8 < shift2 - shift1 ∧
    tailLength8 < shift3 - shift2 ∧
    tailLength8 < shift4 - shift3 ∧
    T8 + tailLength8 = M8 := by
  native_decide

/-!
The derivative of

`V(y) = log(1/|y|)
  + 1.174168821 log(1/|y-1.80650001|)
  + 0.025921118 log(1/|y-2.57053197|)
  + 0.118647936 log(1/|y-2.68367709|)
  + 0.180553554 log(1/|y-2.79017717|)`

has the form `V'(y) = -N(y) / D(y)`, away from the poles.  The primitive
integer numerator below is a positive scalar multiple of the quartic `N`.

For a rational point `y = n / d`, `critNum n d` is the numerator of that
quartic after clearing denominators by `d^4`.
-/

def critNum (n d : Int) : Int :=
    833097143000000000000000000000000 * n^4
  - 7203426448779519290000000000000000 * n^3 * d
  + 22271344049495468164668367700000000 * n^2 * d^2
  - 28310680823455635363669075998162907 * n * d^3
  + 11590489097511299183527530554428470 * d^4

def den8 : Int := 100000000

/-! ## Exact critical-bracket sign checks -/

theorem r1_left_positive : 0 < critNum 77003805 den8 := by
  native_decide

theorem r1_right_negative : critNum 77003806 den8 < 0 := by
  native_decide

theorem r2_left_negative : critNum 252642600 den8 < 0 := by
  native_decide

theorem r2_right_positive : 0 < critNum 252642601 den8 := by
  native_decide

theorem r3_left_positive : 0 < critNum 260759965 den8 := by
  native_decide

theorem r3_right_negative : critNum 260759966 den8 < 0 := by
  native_decide

theorem r4_left_negative : critNum 274249871 den8 < 0 := by
  native_decide

theorem r4_right_positive : 0 < critNum 274249872 den8 := by
  native_decide

theorem critical_sign_certificate :
    0 < critNum 77003805 den8 ∧
    critNum 77003806 den8 < 0 ∧
    critNum 252642600 den8 < 0 ∧
    0 < critNum 252642601 den8 ∧
    0 < critNum 260759965 den8 ∧
    critNum 260759966 den8 < 0 ∧
    critNum 274249871 den8 < 0 ∧
    0 < critNum 274249872 den8 := by
  native_decide

/-! ## Exact endpoint/checkpoint order data -/

def yLo : Nat := 70800000
def yHi : Nat := 280630400

theorem domain_order_certificate :
    yLo < 77003805 ∧
    77003806 < shift1 ∧
    shift1 < 252642600 ∧
    252642601 < shift2 ∧
    shift2 < 260759965 ∧
    260759966 < shift3 ∧
    shift3 < 274249871 ∧
    274249872 < shift4 ∧
    shift4 < yHi := by
  native_decide

/-!
The final object exported by this file: all exact arithmetic facts needed by
the `M = 1.806304` five-atom tail certificate.
-/

theorem five_atom_1806304_exact_arithmetic_certificate :
    (M8 < shift1 ∧
      tailLength8 < shift2 - shift1 ∧
      tailLength8 < shift3 - shift2 ∧
      tailLength8 < shift4 - shift3 ∧
      T8 + tailLength8 = M8) ∧
    (0 < critNum 77003805 den8 ∧
      critNum 77003806 den8 < 0 ∧
      critNum 252642600 den8 < 0 ∧
      0 < critNum 252642601 den8 ∧
      0 < critNum 260759965 den8 ∧
      critNum 260759966 den8 < 0 ∧
      critNum 274249871 den8 < 0 ∧
      0 < critNum 274249872 den8) ∧
    (yLo < 77003805 ∧
      77003806 < shift1 ∧
      shift1 < 252642600 ∧
      252642601 < shift2 ∧
      shift2 < 260759965 ∧
      260759966 < shift3 ∧
      shift3 < 274249871 ∧
      274249872 < shift4 ∧
      shift4 < yHi) := by
  exact ⟨sweep_geometry_certificate, critical_sign_certificate, domain_order_certificate⟩

end FiveAtom1806304
end Erdos1038
