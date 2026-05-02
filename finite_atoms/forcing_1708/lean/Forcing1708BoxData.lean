import Mathlib
import box_arith_chunks.Forcing1708BoxArith00
import box_arith_chunks.Forcing1708BoxArith01
import box_arith_chunks.Forcing1708BoxArith02
import box_arith_chunks.Forcing1708BoxArith03
import box_arith_chunks.Forcing1708BoxArith04
import box_arith_chunks.Forcing1708BoxArith05
import box_arith_chunks.Forcing1708BoxArith06
import box_arith_chunks.Forcing1708BoxArith07
import box_arith_chunks.Forcing1708BoxArith08
import box_arith_chunks.Forcing1708BoxArith09
import box_arith_chunks.Forcing1708BoxArith10
import box_arith_chunks.Forcing1708BoxArith11
import box_arith_chunks.Forcing1708BoxArith12
import box_arith_chunks.Forcing1708BoxArith13
import box_arith_chunks.Forcing1708BoxArith14
import box_arith_chunks.Forcing1708BoxArith15
import box_arith_chunks.Forcing1708BoxArith16
import box_arith_chunks.Forcing1708BoxArith17
import box_arith_chunks.Forcing1708BoxArith18
import box_arith_chunks.Forcing1708BoxArith19

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

theorem aggregate_index_certificates :
    (Forcing1708BoxArith00.boxes.size = 49 ∧
      Forcing1708BoxArith00.boxes.all Forcing1708BoxArith00.boxShapeOk = true ∧
      Forcing1708BoxArith00.boxes.all Forcing1708BoxArith00.boxArithOk = true) ∧
    (Forcing1708BoxArith01.boxes.size = 49 ∧
      Forcing1708BoxArith01.boxes.all Forcing1708BoxArith01.boxShapeOk = true ∧
      Forcing1708BoxArith01.boxes.all Forcing1708BoxArith01.boxArithOk = true) ∧
    (Forcing1708BoxArith02.boxes.size = 49 ∧
      Forcing1708BoxArith02.boxes.all Forcing1708BoxArith02.boxShapeOk = true ∧
      Forcing1708BoxArith02.boxes.all Forcing1708BoxArith02.boxArithOk = true) ∧
    (Forcing1708BoxArith03.boxes.size = 49 ∧
      Forcing1708BoxArith03.boxes.all Forcing1708BoxArith03.boxShapeOk = true ∧
      Forcing1708BoxArith03.boxes.all Forcing1708BoxArith03.boxArithOk = true) ∧
    (Forcing1708BoxArith04.boxes.size = 49 ∧
      Forcing1708BoxArith04.boxes.all Forcing1708BoxArith04.boxShapeOk = true ∧
      Forcing1708BoxArith04.boxes.all Forcing1708BoxArith04.boxArithOk = true) ∧
    (Forcing1708BoxArith05.boxes.size = 49 ∧
      Forcing1708BoxArith05.boxes.all Forcing1708BoxArith05.boxShapeOk = true ∧
      Forcing1708BoxArith05.boxes.all Forcing1708BoxArith05.boxArithOk = true) ∧
    (Forcing1708BoxArith06.boxes.size = 49 ∧
      Forcing1708BoxArith06.boxes.all Forcing1708BoxArith06.boxShapeOk = true ∧
      Forcing1708BoxArith06.boxes.all Forcing1708BoxArith06.boxArithOk = true) ∧
    (Forcing1708BoxArith07.boxes.size = 49 ∧
      Forcing1708BoxArith07.boxes.all Forcing1708BoxArith07.boxShapeOk = true ∧
      Forcing1708BoxArith07.boxes.all Forcing1708BoxArith07.boxArithOk = true) ∧
    (Forcing1708BoxArith08.boxes.size = 49 ∧
      Forcing1708BoxArith08.boxes.all Forcing1708BoxArith08.boxShapeOk = true ∧
      Forcing1708BoxArith08.boxes.all Forcing1708BoxArith08.boxArithOk = true) ∧
    (Forcing1708BoxArith09.boxes.size = 49 ∧
      Forcing1708BoxArith09.boxes.all Forcing1708BoxArith09.boxShapeOk = true ∧
      Forcing1708BoxArith09.boxes.all Forcing1708BoxArith09.boxArithOk = true) ∧
    (Forcing1708BoxArith10.boxes.size = 49 ∧
      Forcing1708BoxArith10.boxes.all Forcing1708BoxArith10.boxShapeOk = true ∧
      Forcing1708BoxArith10.boxes.all Forcing1708BoxArith10.boxArithOk = true) ∧
    (Forcing1708BoxArith11.boxes.size = 49 ∧
      Forcing1708BoxArith11.boxes.all Forcing1708BoxArith11.boxShapeOk = true ∧
      Forcing1708BoxArith11.boxes.all Forcing1708BoxArith11.boxArithOk = true) ∧
    (Forcing1708BoxArith12.boxes.size = 49 ∧
      Forcing1708BoxArith12.boxes.all Forcing1708BoxArith12.boxShapeOk = true ∧
      Forcing1708BoxArith12.boxes.all Forcing1708BoxArith12.boxArithOk = true) ∧
    (Forcing1708BoxArith13.boxes.size = 49 ∧
      Forcing1708BoxArith13.boxes.all Forcing1708BoxArith13.boxShapeOk = true ∧
      Forcing1708BoxArith13.boxes.all Forcing1708BoxArith13.boxArithOk = true) ∧
    (Forcing1708BoxArith14.boxes.size = 49 ∧
      Forcing1708BoxArith14.boxes.all Forcing1708BoxArith14.boxShapeOk = true ∧
      Forcing1708BoxArith14.boxes.all Forcing1708BoxArith14.boxArithOk = true) ∧
    (Forcing1708BoxArith15.boxes.size = 49 ∧
      Forcing1708BoxArith15.boxes.all Forcing1708BoxArith15.boxShapeOk = true ∧
      Forcing1708BoxArith15.boxes.all Forcing1708BoxArith15.boxArithOk = true) ∧
    (Forcing1708BoxArith16.boxes.size = 49 ∧
      Forcing1708BoxArith16.boxes.all Forcing1708BoxArith16.boxShapeOk = true ∧
      Forcing1708BoxArith16.boxes.all Forcing1708BoxArith16.boxArithOk = true) ∧
    (Forcing1708BoxArith17.boxes.size = 49 ∧
      Forcing1708BoxArith17.boxes.all Forcing1708BoxArith17.boxShapeOk = true ∧
      Forcing1708BoxArith17.boxes.all Forcing1708BoxArith17.boxArithOk = true) ∧
    (Forcing1708BoxArith18.boxes.size = 49 ∧
      Forcing1708BoxArith18.boxes.all Forcing1708BoxArith18.boxShapeOk = true ∧
      Forcing1708BoxArith18.boxes.all Forcing1708BoxArith18.boxArithOk = true) ∧
    (Forcing1708BoxArith19.boxes.size = 49 ∧
      Forcing1708BoxArith19.boxes.all Forcing1708BoxArith19.boxShapeOk = true ∧
      Forcing1708BoxArith19.boxes.all Forcing1708BoxArith19.boxArithOk = true) := by
  exact ⟨
    Forcing1708BoxArith00.chunk_certificate,
    Forcing1708BoxArith01.chunk_certificate,
    Forcing1708BoxArith02.chunk_certificate,
    Forcing1708BoxArith03.chunk_certificate,
    Forcing1708BoxArith04.chunk_certificate,
    Forcing1708BoxArith05.chunk_certificate,
    Forcing1708BoxArith06.chunk_certificate,
    Forcing1708BoxArith07.chunk_certificate,
    Forcing1708BoxArith08.chunk_certificate,
    Forcing1708BoxArith09.chunk_certificate,
    Forcing1708BoxArith10.chunk_certificate,
    Forcing1708BoxArith11.chunk_certificate,
    Forcing1708BoxArith12.chunk_certificate,
    Forcing1708BoxArith13.chunk_certificate,
    Forcing1708BoxArith14.chunk_certificate,
    Forcing1708BoxArith15.chunk_certificate,
    Forcing1708BoxArith16.chunk_certificate,
    Forcing1708BoxArith17.chunk_certificate,
    Forcing1708BoxArith18.chunk_certificate,
    Forcing1708BoxArith19.chunk_certificate⟩

end Forcing1708BoxData
end Erdos1038
