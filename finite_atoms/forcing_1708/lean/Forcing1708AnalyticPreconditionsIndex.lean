import Mathlib

/-!
# Analytic precondition chunk index for the forcing branch

The box-wise scaled-log precondition checks are split across 20 files under
`lean/analytic_precondition_chunks/`. Each chunk uses exact rational arithmetic
with the same power-of-two scaled atanh bounds formalized in
`Forcing1708AnalyticKernel.lean`.
-/

namespace Erdos1038
namespace Forcing1708AnalyticPreconditionsIndex

theorem analytic_precondition_chunk_count : (20 : Nat) = 20 := rfl
theorem analytic_precondition_box_count : 20 * 49 = 980 := by native_decide

end Forcing1708AnalyticPreconditionsIndex
end Erdos1038
