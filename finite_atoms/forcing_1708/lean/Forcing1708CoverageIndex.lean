import Mathlib
import coverage_chunks.Forcing1708CoverageA00
import coverage_chunks.Forcing1708CoverageA01
import coverage_chunks.Forcing1708CoverageA02
import coverage_chunks.Forcing1708CoverageA03
import coverage_chunks.Forcing1708CoverageA04
import coverage_chunks.Forcing1708CoverageA05
import coverage_chunks.Forcing1708CoverageA06
import coverage_chunks.Forcing1708CoverageA07
import coverage_chunks.Forcing1708CoverageA08
import coverage_chunks.Forcing1708CoverageA09
import coverage_chunks.Forcing1708CoverageA10
import coverage_chunks.Forcing1708CoverageA11
import coverage_chunks.Forcing1708CoverageA12
import coverage_chunks.Forcing1708CoverageA13
import coverage_chunks.Forcing1708CoverageA14

/-!
# Coverage chunk index for the forcing branch

The coverage proof is split into 15 a-slab files under `lean/coverage_chunks/`.
Each slab has 59 * 26 = 1534 elementary `(s,x)` cells, so the files together
check 23010 coverage witnesses.
-/

namespace Erdos1038
namespace Forcing1708CoverageIndex

theorem slab_count : (15 : Nat) = 15 := rfl
theorem total_coverage_cells : 15 * 1534 = 23010 := by native_decide

theorem aggregate_index_certificates :
    (Forcing1708CoverageA00.expectedCells = 1534 ∧
      0 < Forcing1708CoverageA00.boxes.size ∧ Forcing1708CoverageA00.coverageOk = true) ∧
    (Forcing1708CoverageA01.expectedCells = 1534 ∧
      0 < Forcing1708CoverageA01.boxes.size ∧ Forcing1708CoverageA01.coverageOk = true) ∧
    (Forcing1708CoverageA02.expectedCells = 1534 ∧
      0 < Forcing1708CoverageA02.boxes.size ∧ Forcing1708CoverageA02.coverageOk = true) ∧
    (Forcing1708CoverageA03.expectedCells = 1534 ∧
      0 < Forcing1708CoverageA03.boxes.size ∧ Forcing1708CoverageA03.coverageOk = true) ∧
    (Forcing1708CoverageA04.expectedCells = 1534 ∧
      0 < Forcing1708CoverageA04.boxes.size ∧ Forcing1708CoverageA04.coverageOk = true) ∧
    (Forcing1708CoverageA05.expectedCells = 1534 ∧
      0 < Forcing1708CoverageA05.boxes.size ∧ Forcing1708CoverageA05.coverageOk = true) ∧
    (Forcing1708CoverageA06.expectedCells = 1534 ∧
      0 < Forcing1708CoverageA06.boxes.size ∧ Forcing1708CoverageA06.coverageOk = true) ∧
    (Forcing1708CoverageA07.expectedCells = 1534 ∧
      0 < Forcing1708CoverageA07.boxes.size ∧ Forcing1708CoverageA07.coverageOk = true) ∧
    (Forcing1708CoverageA08.expectedCells = 1534 ∧
      0 < Forcing1708CoverageA08.boxes.size ∧ Forcing1708CoverageA08.coverageOk = true) ∧
    (Forcing1708CoverageA09.expectedCells = 1534 ∧
      0 < Forcing1708CoverageA09.boxes.size ∧ Forcing1708CoverageA09.coverageOk = true) ∧
    (Forcing1708CoverageA10.expectedCells = 1534 ∧
      0 < Forcing1708CoverageA10.boxes.size ∧ Forcing1708CoverageA10.coverageOk = true) ∧
    (Forcing1708CoverageA11.expectedCells = 1534 ∧
      0 < Forcing1708CoverageA11.boxes.size ∧ Forcing1708CoverageA11.coverageOk = true) ∧
    (Forcing1708CoverageA12.expectedCells = 1534 ∧
      0 < Forcing1708CoverageA12.boxes.size ∧ Forcing1708CoverageA12.coverageOk = true) ∧
    (Forcing1708CoverageA13.expectedCells = 1534 ∧
      0 < Forcing1708CoverageA13.boxes.size ∧ Forcing1708CoverageA13.coverageOk = true) ∧
    (Forcing1708CoverageA14.expectedCells = 1534 ∧
      0 < Forcing1708CoverageA14.boxes.size ∧ Forcing1708CoverageA14.coverageOk = true) := by
  exact ⟨
    Forcing1708CoverageA00.slab_certificate,
    Forcing1708CoverageA01.slab_certificate,
    Forcing1708CoverageA02.slab_certificate,
    Forcing1708CoverageA03.slab_certificate,
    Forcing1708CoverageA04.slab_certificate,
    Forcing1708CoverageA05.slab_certificate,
    Forcing1708CoverageA06.slab_certificate,
    Forcing1708CoverageA07.slab_certificate,
    Forcing1708CoverageA08.slab_certificate,
    Forcing1708CoverageA09.slab_certificate,
    Forcing1708CoverageA10.slab_certificate,
    Forcing1708CoverageA11.slab_certificate,
    Forcing1708CoverageA12.slab_certificate,
    Forcing1708CoverageA13.slab_certificate,
    Forcing1708CoverageA14.slab_certificate⟩

end Forcing1708CoverageIndex
end Erdos1038
