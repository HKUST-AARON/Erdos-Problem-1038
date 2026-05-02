import Mathlib
import analytic_precondition_chunks.Forcing1708AnalyticPre00
import analytic_precondition_chunks.Forcing1708AnalyticPre01
import analytic_precondition_chunks.Forcing1708AnalyticPre02
import analytic_precondition_chunks.Forcing1708AnalyticPre03
import analytic_precondition_chunks.Forcing1708AnalyticPre04
import analytic_precondition_chunks.Forcing1708AnalyticPre05
import analytic_precondition_chunks.Forcing1708AnalyticPre06
import analytic_precondition_chunks.Forcing1708AnalyticPre07
import analytic_precondition_chunks.Forcing1708AnalyticPre08
import analytic_precondition_chunks.Forcing1708AnalyticPre09
import analytic_precondition_chunks.Forcing1708AnalyticPre10
import analytic_precondition_chunks.Forcing1708AnalyticPre11
import analytic_precondition_chunks.Forcing1708AnalyticPre12
import analytic_precondition_chunks.Forcing1708AnalyticPre13
import analytic_precondition_chunks.Forcing1708AnalyticPre14
import analytic_precondition_chunks.Forcing1708AnalyticPre15
import analytic_precondition_chunks.Forcing1708AnalyticPre16
import analytic_precondition_chunks.Forcing1708AnalyticPre17
import analytic_precondition_chunks.Forcing1708AnalyticPre18
import analytic_precondition_chunks.Forcing1708AnalyticPre19

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

theorem aggregate_index_certificates :
    (Forcing1708AnalyticPre00.boxes.size = 49 ∧
      Forcing1708AnalyticPre00.boxes.all Forcing1708AnalyticPre00.preconditionOk = true) ∧
    (Forcing1708AnalyticPre01.boxes.size = 49 ∧
      Forcing1708AnalyticPre01.boxes.all Forcing1708AnalyticPre01.preconditionOk = true) ∧
    (Forcing1708AnalyticPre02.boxes.size = 49 ∧
      Forcing1708AnalyticPre02.boxes.all Forcing1708AnalyticPre02.preconditionOk = true) ∧
    (Forcing1708AnalyticPre03.boxes.size = 49 ∧
      Forcing1708AnalyticPre03.boxes.all Forcing1708AnalyticPre03.preconditionOk = true) ∧
    (Forcing1708AnalyticPre04.boxes.size = 49 ∧
      Forcing1708AnalyticPre04.boxes.all Forcing1708AnalyticPre04.preconditionOk = true) ∧
    (Forcing1708AnalyticPre05.boxes.size = 49 ∧
      Forcing1708AnalyticPre05.boxes.all Forcing1708AnalyticPre05.preconditionOk = true) ∧
    (Forcing1708AnalyticPre06.boxes.size = 49 ∧
      Forcing1708AnalyticPre06.boxes.all Forcing1708AnalyticPre06.preconditionOk = true) ∧
    (Forcing1708AnalyticPre07.boxes.size = 49 ∧
      Forcing1708AnalyticPre07.boxes.all Forcing1708AnalyticPre07.preconditionOk = true) ∧
    (Forcing1708AnalyticPre08.boxes.size = 49 ∧
      Forcing1708AnalyticPre08.boxes.all Forcing1708AnalyticPre08.preconditionOk = true) ∧
    (Forcing1708AnalyticPre09.boxes.size = 49 ∧
      Forcing1708AnalyticPre09.boxes.all Forcing1708AnalyticPre09.preconditionOk = true) ∧
    (Forcing1708AnalyticPre10.boxes.size = 49 ∧
      Forcing1708AnalyticPre10.boxes.all Forcing1708AnalyticPre10.preconditionOk = true) ∧
    (Forcing1708AnalyticPre11.boxes.size = 49 ∧
      Forcing1708AnalyticPre11.boxes.all Forcing1708AnalyticPre11.preconditionOk = true) ∧
    (Forcing1708AnalyticPre12.boxes.size = 49 ∧
      Forcing1708AnalyticPre12.boxes.all Forcing1708AnalyticPre12.preconditionOk = true) ∧
    (Forcing1708AnalyticPre13.boxes.size = 49 ∧
      Forcing1708AnalyticPre13.boxes.all Forcing1708AnalyticPre13.preconditionOk = true) ∧
    (Forcing1708AnalyticPre14.boxes.size = 49 ∧
      Forcing1708AnalyticPre14.boxes.all Forcing1708AnalyticPre14.preconditionOk = true) ∧
    (Forcing1708AnalyticPre15.boxes.size = 49 ∧
      Forcing1708AnalyticPre15.boxes.all Forcing1708AnalyticPre15.preconditionOk = true) ∧
    (Forcing1708AnalyticPre16.boxes.size = 49 ∧
      Forcing1708AnalyticPre16.boxes.all Forcing1708AnalyticPre16.preconditionOk = true) ∧
    (Forcing1708AnalyticPre17.boxes.size = 49 ∧
      Forcing1708AnalyticPre17.boxes.all Forcing1708AnalyticPre17.preconditionOk = true) ∧
    (Forcing1708AnalyticPre18.boxes.size = 49 ∧
      Forcing1708AnalyticPre18.boxes.all Forcing1708AnalyticPre18.preconditionOk = true) ∧
    (Forcing1708AnalyticPre19.boxes.size = 49 ∧
      Forcing1708AnalyticPre19.boxes.all Forcing1708AnalyticPre19.preconditionOk = true) := by
  exact ⟨
    Forcing1708AnalyticPre00.chunk_analytic_preconditions_certificate,
    Forcing1708AnalyticPre01.chunk_analytic_preconditions_certificate,
    Forcing1708AnalyticPre02.chunk_analytic_preconditions_certificate,
    Forcing1708AnalyticPre03.chunk_analytic_preconditions_certificate,
    Forcing1708AnalyticPre04.chunk_analytic_preconditions_certificate,
    Forcing1708AnalyticPre05.chunk_analytic_preconditions_certificate,
    Forcing1708AnalyticPre06.chunk_analytic_preconditions_certificate,
    Forcing1708AnalyticPre07.chunk_analytic_preconditions_certificate,
    Forcing1708AnalyticPre08.chunk_analytic_preconditions_certificate,
    Forcing1708AnalyticPre09.chunk_analytic_preconditions_certificate,
    Forcing1708AnalyticPre10.chunk_analytic_preconditions_certificate,
    Forcing1708AnalyticPre11.chunk_analytic_preconditions_certificate,
    Forcing1708AnalyticPre12.chunk_analytic_preconditions_certificate,
    Forcing1708AnalyticPre13.chunk_analytic_preconditions_certificate,
    Forcing1708AnalyticPre14.chunk_analytic_preconditions_certificate,
    Forcing1708AnalyticPre15.chunk_analytic_preconditions_certificate,
    Forcing1708AnalyticPre16.chunk_analytic_preconditions_certificate,
    Forcing1708AnalyticPre17.chunk_analytic_preconditions_certificate,
    Forcing1708AnalyticPre18.chunk_analytic_preconditions_certificate,
    Forcing1708AnalyticPre19.chunk_analytic_preconditions_certificate⟩

end Forcing1708AnalyticPreconditionsIndex
end Erdos1038
