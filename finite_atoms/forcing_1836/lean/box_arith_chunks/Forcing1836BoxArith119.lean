import Mathlib

set_option maxRecDepth 30000
set_option maxHeartbeats 0

/-! Exact rational arithmetic check for stronger forcing boxes 5950 through 5954. -/
namespace Erdos1038
namespace Forcing1836BoxArith119

structure BoxCert where
  aLo : Rat
  aHi : Rat
  sLo : Rat
  sHi : Rat
  xLo : Rat
  xHi : Rat
  lower : Rat
  bLo : Rat
  bHi : Rat
  cLo : Rat
  cHi : Rat
  wLo : Rat
  wHi : Rat
  cWeightLo : Rat
  cWeightHi : Rat
  baseA : Rat
  baseB : Rat
  baseC : Rat
deriving Repr, DecidableEq

def targetMargin : Rat := Rat.normalize (1 : Int) (1000000 : Nat)
def productLowerRat (lo hi base : Rat) : Rat := if 0 ≤ base then lo * base else hi * base
def recombinedLower (B : BoxCert) : Rat :=
  B.baseA + productLowerRat B.wLo B.wHi B.baseB +
    productLowerRat B.cWeightLo B.cWeightHi B.baseC

def boxShapeOk (B : BoxCert) : Bool :=
  decide (B.aLo < B.aHi) && decide (B.sLo < B.sHi) && decide (B.xLo < B.xHi)

def boxArithOk (B : BoxCert) : Bool :=
  decide (0 < B.cLo) && decide (0 < B.wLo) && decide (0 < B.cWeightLo) &&
  decide (targetMargin < B.lower) && decide (B.lower ≤ recombinedLower B)

def boxes : Array BoxCert := #[
  {aLo := (Rat.normalize (-1487660171780 : Int) (1000000000000 : Nat)), aHi := (Rat.normalize (-1414213562373 : Int) (1000000000000 : Nat)), sLo := (Rat.normalize (625000000000 : Int) (1000000000000 : Nat)), sHi := (Rat.normalize (750000000000 : Int) (1000000000000 : Nat)), xLo := (Rat.normalize (875000000000 : Int) (1000000000000 : Nat)), xHi := (Rat.normalize (1000000000000 : Int) (1000000000000 : Nat)), lower := (Rat.normalize (313597464475 : Int) (1000000000000 : Nat)), bLo := (Rat.normalize (217712392637 : Int) (1000000000000 : Nat)), bHi := (Rat.normalize (316339828221 : Int) (1000000000000 : Nat)), cLo := (Rat.normalize (754660171779 : Int) (1000000000000 : Nat)), cHi := (Rat.normalize (853287607363 : Int) (1000000000000 : Nat)), wLo := (Rat.normalize (1078660171779 : Int) (1000000000000 : Nat)), wHi := (Rat.normalize (1177287607363 : Int) (1000000000000 : Nat)), cWeightLo := (Rat.normalize (683286647244 : Int) (1000000000000 : Nat)), cWeightHi := (Rat.normalize (1154912258197 : Int) (1000000000000 : Nat)), baseA := (Rat.normalize (-911342578644 : Int) (1000000000000 : Nat)), baseB := (Rat.normalize (245532821701 : Int) (1000000000000 : Nat)), baseC := (Rat.normalize (1405110975547 : Int) (1000000000000 : Nat))},
  {aLo := (Rat.normalize (-1634553390594 : Int) (1000000000000 : Nat)), aHi := (Rat.normalize (-1561106781186 : Int) (1000000000000 : Nat)), sLo := (Rat.normalize (750000000000 : Int) (1000000000000 : Nat)), sHi := (Rat.normalize (875000000000 : Int) (1000000000000 : Nat)), xLo := (Rat.normalize (500000000000 : Int) (1000000000000 : Nat)), xHi := (Rat.normalize (625000000000 : Int) (1000000000000 : Nat)), lower := (Rat.normalize (320805904683 : Int) (1000000000000 : Nat)), bLo := (Rat.normalize (151084957055 : Int) (1000000000000 : Nat)), bHi := (Rat.normalize (240531566462 : Int) (1000000000000 : Nat)), cLo := (Rat.normalize (830468433538 : Int) (1000000000000 : Nat)), cHi := (Rat.normalize (919915042945 : Int) (1000000000000 : Nat)), wLo := (Rat.normalize (1154468433538 : Int) (1000000000000 : Nat)), wHi := (Rat.normalize (1243915042945 : Int) (1000000000000 : Nat)), cWeightLo := (Rat.normalize (315661160556 : Int) (1000000000000 : Nat)), cWeightHi := (Rat.normalize (666122681721 : Int) (1000000000000 : Nat)), baseA := (Rat.normalize (-815167178976 : Int) (1000000000000 : Nat)), baseB := (Rat.normalize (746727207643 : Int) (1000000000000 : Nat)), baseC := (Rat.normalize (867702866867 : Int) (1000000000000 : Nat))},
  {aLo := (Rat.normalize (-1561106781187 : Int) (1000000000000 : Nat)), aHi := (Rat.normalize (-1414213562373 : Int) (1000000000000 : Nat)), sLo := (Rat.normalize (625000000000 : Int) (1000000000000 : Nat)), sHi := (Rat.normalize (750000000000 : Int) (1000000000000 : Nat)), xLo := (Rat.normalize (750000000000 : Int) (1000000000000 : Nat)), xHi := (Rat.normalize (875000000000 : Int) (1000000000000 : Nat)), lower := (Rat.normalize (323686584424 : Int) (1000000000000 : Nat)), bLo := (Rat.normalize (171808261758 : Int) (1000000000000 : Nat)), bHi := (Rat.normalize (316339828221 : Int) (1000000000000 : Nat)), cLo := (Rat.normalize (754660171779 : Int) (1000000000000 : Nat)), cHi := (Rat.normalize (899191738242 : Int) (1000000000000 : Nat)), wLo := (Rat.normalize (1078660171779 : Int) (1000000000000 : Nat)), wHi := (Rat.normalize (1223191738242 : Int) (1000000000000 : Nat)), cWeightLo := (Rat.normalize (438503941654 : Int) (1000000000000 : Nat)), cWeightHi := (Rat.normalize (1222424326142 : Int) (1000000000000 : Nat)), baseA := (Rat.normalize (-890401183530 : Int) (1000000000000 : Nat)), baseB := (Rat.normalize (352125681482 : Int) (1000000000000 : Nat)), baseC := (Rat.normalize (1902522966460 : Int) (1000000000000 : Nat))},
  {aLo := (Rat.normalize (-1561106781187 : Int) (1000000000000 : Nat)), aHi := (Rat.normalize (-1414213562373 : Int) (1000000000000 : Nat)), sLo := (Rat.normalize (250000000000 : Int) (1000000000000 : Nat)), sHi := (Rat.normalize (375000000000 : Int) (1000000000000 : Nat)), xLo := (Rat.normalize (875000000000 : Int) (1000000000000 : Nat)), xHi := (Rat.normalize (1000000000000 : Int) (1000000000000 : Nat)), lower := (Rat.normalize (323755392592 : Int) (1000000000000 : Nat)), bLo := (Rat.normalize (68723304703 : Int) (1000000000000 : Nat)), bHi := (Rat.normalize (158169914111 : Int) (1000000000000 : Nat)), cLo := (Rat.normalize (912830085889 : Int) (1000000000000 : Nat)), cHi := (Rat.normalize (1002276695297 : Int) (1000000000000 : Nat)), wLo := (Rat.normalize (1236830085889 : Int) (1000000000000 : Nat)), wHi := (Rat.normalize (1326276695297 : Int) (1000000000000 : Nat)), cWeightLo := (Rat.normalize (570553345731 : Int) (1000000000000 : Nat)), cWeightHi := (Rat.normalize (1222853300559 : Int) (1000000000000 : Nat)), baseA := (Rat.normalize (-940439501464 : Int) (1000000000000 : Nat)), baseB := (Rat.normalize (71198843607 : Int) (1000000000000 : Nat)), baseC := (Rat.normalize (2061391859331 : Int) (1000000000000 : Nat))},
  {aLo := (Rat.normalize (-1634553390594 : Int) (1000000000000 : Nat)), aHi := (Rat.normalize (-1561106781186 : Int) (1000000000000 : Nat)), sLo := (Rat.normalize (875000000000 : Int) (1000000000000 : Nat)), sHi := (Rat.normalize (1000000000000 : Int) (1000000000000 : Nat)), xLo := (Rat.normalize (500000000000 : Int) (1000000000000 : Nat)), xHi := (Rat.normalize (625000000000 : Int) (1000000000000 : Nat)), lower := (Rat.normalize (348142706641 : Int) (1000000000000 : Nat)), bLo := (Rat.normalize (176265783230 : Int) (1000000000000 : Nat)), bHi := (Rat.normalize (274893218814 : Int) (1000000000000 : Nat)), cLo := (Rat.normalize (796106781186 : Int) (1000000000000 : Nat)), cHi := (Rat.normalize (894734216770 : Int) (1000000000000 : Nat)), wLo := (Rat.normalize (1120106781186 : Int) (1000000000000 : Nat)), wHi := (Rat.normalize (1218734216770 : Int) (1000000000000 : Nat)), cWeightLo := (Rat.normalize (285883469804 : Int) (1000000000000 : Nat)), cWeightHi := (Rat.normalize (648693569664 : Int) (1000000000000 : Nat)), baseA := (Rat.normalize (-815167178976 : Int) (1000000000000 : Nat)), baseB := (Rat.normalize (801324511342 : Int) (1000000000000 : Nat)), baseC := (Rat.normalize (929542609496 : Int) (1000000000000 : Nat))}
]

theorem chunk_size_certificate : boxes.size = 5 := by native_decide
theorem all_box_shapes_certificate : boxes.all boxShapeOk = true := by native_decide
theorem all_box_arithmetic_certificate : boxes.all boxArithOk = true := by native_decide
theorem chunk_certificate : boxes.size = 5 ∧ boxes.all boxShapeOk = true ∧ boxes.all boxArithOk = true := by
  exact ⟨chunk_size_certificate, all_box_shapes_certificate, all_box_arithmetic_certificate⟩

end Forcing1836BoxArith119
end Erdos1038
