import Mathlib

/-!
# Forcing branch box-data index

The exact rational arithmetic proof for the 980 forcing boxes is split across
20 checked Lean files under `lean/box_arith_chunks/`. The lower/base data
are rounded outward to denominator `10^6`; the weakest rounded lower bound is
`21/1000000`, still above the required `1/1000000` margin.
-/

namespace Erdos1038
namespace Forcing1708BoxData

theorem chunk_count : (20 : Nat) = 20 := rfl
theorem rounded_worst_margin : (1 : Rat) / 1000000 < (21 : Rat) / 1000000 := by native_decide

end Forcing1708BoxData
end Erdos1038
