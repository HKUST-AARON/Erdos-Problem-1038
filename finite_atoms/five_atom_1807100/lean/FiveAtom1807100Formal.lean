import Std

/-!
# Exact Lean arithmetic for the five-atom `M = 1.807100` tail certificate

This file proves exact integer and natural-number arithmetic used by the
five-atom one-variable certificate:

* quartic critical-bracket sign checks;
* swept-interval disjointness arithmetic;
* the scaled-length identity `1.708 + 0.099100 = 1.807100`.
-/

namespace Erdos1038
namespace FiveAtom1807100

/-! ## Scale conventions -/

def scale8 : Nat := 100000000

def T8 : Nat := 170800000
def M8 : Nat := 180710000
def tailLength8 : Nat := 9910000

def shift1 : Nat := 180710376
def shift2 : Nat := 257979789
def shift3 : Nat := 269319012
def shift4 : Nat := 279229832


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
  + 1.18287976 log(1/|y-1.80710376|)
  + 0.03349753 log(1/|y-2.57979789|)
  + 0.11739956 log(1/|y-2.69319012|)
  + 0.17267833 log(1/|y-2.79229832|)`

has the form `V'(y) = -N(y) / D(y)`, away from the poles.  The primitive
integer numerator below is a positive scalar multiple of the quartic `N`.

For a rational point `y = n / d`, `critNum n d` is the numerator of that
quartic after clearing denominators by `d^4`.
-/

def critNum (n d : Int) : Int :=
    7832672437500000000000000000000 * n^4
  - 67882347547122825312500000000000 * n^3 * d
  + 210299802356320705188282187500000 * n^2 * d^2
  - 267698666880869891311319509896705 * n * d^3
  + 109558889622081288329838022524168 * d^4
def den8 : Int := 100000000

/-! ## Exact critical-bracket sign checks -/

theorem r1_left_positive : 0 < critNum 76763337 den8 := by
  native_decide

theorem r1_right_negative : critNum 76763338 den8 < 0 := by
  native_decide

theorem r2_left_negative : critNum 252916631 den8 < 0 := by
  native_decide

theorem r2_right_positive : 0 < critNum 252916632 den8 := by
  native_decide

theorem r3_left_positive : 0 < critNum 262127142 den8 := by
  native_decide

theorem r3_right_negative : critNum 262127143 den8 < 0 := by
  native_decide

theorem r4_left_negative : critNum 274849168 den8 < 0 := by
  native_decide

theorem r4_right_positive : 0 < critNum 274849169 den8 := by
  native_decide

theorem critical_sign_certificate :
    0 < critNum 76763337 den8 ∧
    critNum 76763338 den8 < 0 ∧
    critNum 252916631 den8 < 0 ∧
    0 < critNum 252916632 den8 ∧
    0 < critNum 262127142 den8 ∧
    critNum 262127143 den8 < 0 ∧
    critNum 274849168 den8 < 0 ∧
    0 < critNum 274849169 den8 := by
  native_decide

/-! ## Exact endpoint/checkpoint order data -/

def yLo : Nat := 70800000
def yHi : Nat := 280710000

theorem domain_order_certificate :
    yLo < 76763337 ∧
    76763338 < shift1 ∧
    shift1 < 252916631 ∧
    252916632 < shift2 ∧
    shift2 < 262127142 ∧
    262127143 < shift3 ∧
    shift3 < 274849168 ∧
    274849169 < shift4 ∧
    shift4 < yHi := by
  native_decide

/-!
The final object exported by this file: all exact arithmetic facts needed by
the `M = 1.807100` five-atom tail certificate.
-/

theorem five_atom_1807100_exact_arithmetic_certificate :
    (M8 < shift1 ∧
      tailLength8 < shift2 - shift1 ∧
      tailLength8 < shift3 - shift2 ∧
      tailLength8 < shift4 - shift3 ∧
      T8 + tailLength8 = M8) ∧
    (0 < critNum 76763337 den8 ∧
      critNum 76763338 den8 < 0 ∧
      critNum 252916631 den8 < 0 ∧
      0 < critNum 252916632 den8 ∧
      0 < critNum 262127142 den8 ∧
      critNum 262127143 den8 < 0 ∧
      critNum 274849168 den8 < 0 ∧
      0 < critNum 274849169 den8) ∧
    (yLo < 76763337 ∧
      76763338 < shift1 ∧
      shift1 < 252916631 ∧
      252916632 < shift2 ∧
      shift2 < 262127142 ∧
      262127143 < shift3 ∧
      shift3 < 274849168 ∧
      274849169 < shift4 ∧
      shift4 < yHi) := by
  exact ⟨sweep_geometry_certificate, critical_sign_certificate, domain_order_certificate⟩

end FiveAtom1807100
end Erdos1038
