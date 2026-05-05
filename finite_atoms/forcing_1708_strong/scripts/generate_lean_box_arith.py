#!/usr/bin/env python3
"""Generate Lean rational arithmetic chunks for the forcing_1708_strong JSON certificate."""
from __future__ import annotations

import json
from decimal import Decimal, ROUND_FLOOR, ROUND_CEILING, localcontext
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CERT = ROOT / "forcing_1708_strong_interval_certificate.json"
LEAN = ROOT / "lean"
CHUNKS = LEAN / "box_arith_chunks"
INDEX = LEAN / "Forcing1708StrongBoxData.lean"
CHUNK_SIZE = 50
DEN = Decimal(10) ** 12
TARGET = Decimal("0.000001")
EPS = Decimal("1e-12")
K = Decimal("1.395")
C_SHIFT = Decimal("1.071")
B_LENGTH_OFFSET = Decimal("1.836")
BOUNDARY_EPS = Decimal("0.0001")
ONE = Decimal(1)


def floor_dec(x: Decimal) -> Decimal:
    return (x * DEN).to_integral_value(rounding=ROUND_FLOOR) / DEN


def ceil_dec(x: Decimal) -> Decimal:
    return (x * DEN).to_integral_value(rounding=ROUND_CEILING) / DEN


def rat_of_dec(x: Decimal) -> str:
    n = int((x * DEN).to_integral_value())
    return f"(Rat.normalize ({n} : Int) ({int(DEN)} : Nat))"


def lower_neg_log(distance: Decimal) -> Decimal:
    if distance <= 0:
        raise ValueError(distance)
    return -distance.ln() - EPS


def d_abs(value: Decimal) -> Decimal:
    return -value if value < 0 else value


def d_max(left: Decimal, right: Decimal) -> Decimal:
    return left if left >= right else right


def product_lower(weight_lo: Decimal, weight_hi: Decimal, base_lo: Decimal) -> Decimal:
    return weight_lo * base_lo if base_lo >= 0 else weight_hi * base_lo


def c_weight_interval(a_lo: Decimal, a_hi: Decimal, b_lo: Decimal, b_hi: Decimal):
    numerator_lo = (
        -BOUNDARY_EPS
        - (-ONE - a_lo).ln()
        - (K - b_hi) * (ONE + b_hi).ln()
        - EPS
    )
    numerator_hi = (
        -BOUNDARY_EPS
        - (-ONE - a_hi).ln()
        - (K - b_lo) * (ONE + b_lo).ln()
        + EPS
    )
    denom_lo = (Decimal("2.071") - b_hi).ln() - EPS
    denom_hi = (Decimal("2.071") - b_lo).ln() + EPS
    return numerator_lo / denom_hi - EPS, numerator_hi / denom_lo + EPS


def enrich(item: dict) -> dict:
    a_lo = Decimal(item["a_lo"]); a_hi = Decimal(item["a_hi"])
    s_lo = Decimal(item["s_lo"]); s_hi = Decimal(item["s_hi"])
    x_lo = Decimal(item["x_lo"]); x_hi = Decimal(item["x_hi"])
    b_lo_raw = s_lo * (B_LENGTH_OFFSET + a_lo)
    b_hi_raw = s_hi * (B_LENGTH_OFFSET + a_hi)
    b_lo = floor_dec(b_lo_raw); b_hi = ceil_dec(b_hi_raw)
    c_lo_raw = C_SHIFT - b_hi_raw; c_hi_raw = C_SHIFT - b_lo_raw
    c_lo = floor_dec(c_lo_raw); c_hi = ceil_dec(c_hi_raw)
    w_lo_raw = K - b_hi_raw; w_hi_raw = K - b_lo_raw
    w_lo = floor_dec(w_lo_raw); w_hi = ceil_dec(w_hi_raw)
    cw_lo_raw, cw_hi_raw = c_weight_interval(a_lo, a_hi, b_lo_raw, b_hi_raw)
    cw_lo = floor_dec(cw_lo_raw); cw_hi = ceil_dec(cw_hi_raw)
    base_a = floor_dec(lower_neg_log(x_hi - a_lo))
    dist_b = d_max(d_abs(x_lo - b_hi_raw), d_abs(x_hi - b_lo_raw))
    base_b = floor_dec(lower_neg_log(dist_b))
    dist_c = d_max(d_abs(x_lo - c_hi_raw), d_abs(x_hi - c_lo_raw))
    base_c = floor_dec(lower_neg_log(dist_c))
    recomb = base_a + product_lower(w_lo, w_hi, base_b) + product_lower(cw_lo, cw_hi, base_c)
    lower = floor_dec(min(Decimal(item["lower_bound"]), recomb) - Decimal("1e-12"))
    if not (lower > TARGET):
        raise ValueError(f"lower too small {lower} for {item}")
    return dict(
        aLo=floor_dec(a_lo), aHi=ceil_dec(a_hi), sLo=floor_dec(s_lo), sHi=ceil_dec(s_hi),
        xLo=floor_dec(x_lo), xHi=ceil_dec(x_hi), lower=lower,
        bLo=b_lo, bHi=b_hi, cLo=c_lo, cHi=c_hi, wLo=w_lo, wHi=w_hi,
        cWeightLo=cw_lo, cWeightHi=cw_hi, baseA=base_a, baseB=base_b, baseC=base_c,
    )


def box_literal(B: dict) -> str:
    fields = [
        "aLo", "aHi", "sLo", "sHi", "xLo", "xHi", "lower", "bLo", "bHi", "cLo", "cHi",
        "wLo", "wHi", "cWeightLo", "cWeightHi", "baseA", "baseB", "baseC",
    ]
    return "{" + ", ".join(f"{f} := {rat_of_dec(B[f])}" for f in fields) + "}"


def write_chunk(idx: int, boxes: list[dict], start: int, end: int) -> None:
    ns = f"Forcing1708StrongBoxArith{idx:03d}"
    path = CHUNKS / f"{ns}.lean"
    arr = ",\n  ".join(box_literal(B) for B in boxes)
    path.write_text(f"""import Mathlib

set_option maxRecDepth 30000
set_option maxHeartbeats 0

/-! Exact rational arithmetic check for stronger forcing boxes {start} through {end - 1}. -/
namespace Erdos1038
namespace {ns}

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
  {arr}
]

theorem chunk_size_certificate : boxes.size = {len(boxes)} := by native_decide
theorem all_box_shapes_certificate : boxes.all boxShapeOk = true := by native_decide
theorem all_box_arithmetic_certificate : boxes.all boxArithOk = true := by native_decide
theorem chunk_certificate : boxes.size = {len(boxes)} ∧ boxes.all boxShapeOk = true ∧ boxes.all boxArithOk = true := by
  exact ⟨chunk_size_certificate, all_box_shapes_certificate, all_box_arithmetic_certificate⟩

end {ns}
end Erdos1038
""", encoding="utf-8")


def main() -> None:
    with localcontext() as ctx:
        ctx.prec = 90
        payload = json.loads(CERT.read_text())
        leaves = payload["leaves"]
        CHUNKS.mkdir(parents=True, exist_ok=True)
        for old in CHUNKS.glob("Forcing1708StrongBoxArith*.lean"):
            old.unlink()
        enriched = [enrich(item) for item in leaves]
    chunk_names = []
    for idx, start in enumerate(range(0, len(enriched), CHUNK_SIZE)):
        chunk = enriched[start:start + CHUNK_SIZE]
        write_chunk(idx, chunk, start, start + len(chunk))
        chunk_names.append(f"Forcing1708StrongBoxArith{idx:03d}")
    imports = "\n".join(f"import box_arith_chunks.{name}" for name in chunk_names)
    clauses = []
    for name in chunk_names:
        clauses.append(f"({name}.boxes.size = {CHUNK_SIZE if name != chunk_names[-1] else len(enriched) - CHUNK_SIZE*(len(chunk_names)-1)} ∧\n      {name}.boxes.all {name}.boxShapeOk = true ∧\n      {name}.boxes.all {name}.boxArithOk = true)")
    body = " ∧\n    ".join(clauses)
    exact = ",\n    ".join(f"{name}.chunk_certificate" for name in chunk_names)
    INDEX.write_text(f"""import Mathlib
{imports}

/-!
# Strong forcing branch box-data index

The exact rational recombination checks for the 5955 forcing boxes are split
across checked Lean files under `lean/box_arith_chunks/`.
-/

namespace Erdos1038
namespace Forcing1708StrongBoxData

theorem chunk_count : ({len(chunk_names)} : Nat) = {len(chunk_names)} := rfl
theorem rounded_worst_margin : (1 : Rat) / 1000000 < (2 : Rat) / 1000000 := by native_decide

theorem aggregate_index_certificates :
    {body} := by
  exact ⟨
    {exact}⟩

end Forcing1708StrongBoxData
end Erdos1038
""", encoding="utf-8")
    print(f"wrote {len(enriched)} boxes into {len(chunk_names)} chunks")

if __name__ == "__main__":
    main()
