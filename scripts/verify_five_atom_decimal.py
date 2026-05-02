#!/usr/bin/env python3
"""Decimal checker for the M=1.806304 five-atom one-variable certificate.

The Lean/Mathlib file lean/FiveAtom1806304Mathlib.lean is authoritative for
these six Real.log checks.  This script is a small independent reproducibility
check using Decimal arithmetic and conservative endpoint/bracket bounds.
"""
from __future__ import annotations
from dataclasses import dataclass
from decimal import Decimal, localcontext
from fractions import Fraction
from typing import Literal, Sequence

PRECISION = 100
TargetKind = Literal["exact", "bracket"]

@dataclass(frozen=True)
class LogTerm:
    coeff: Fraction
    shift: Fraction

@dataclass(frozen=True)
class Check:
    label: str
    kind: TargetKind
    point: Fraction | None = None
    bracket: tuple[Fraction, Fraction] | None = None
    threshold: Fraction = Fraction(0)

def dec(x: Fraction) -> Decimal:
    return Decimal(x.numerator) / Decimal(x.denominator)

def lower_term(left: Decimal, right: Decimal, term: LogTerm) -> Decimal:
    shift = dec(term.shift)
    coeff = dec(term.coeff)
    if left <= shift <= right:
        raise ValueError(f"check interval crosses pole {shift}")
    dist = max(abs(left - shift), abs(right - shift))
    return coeff * (-dist.ln())

def lower_check(check: Check, terms: Sequence[LogTerm]) -> Decimal:
    if check.kind == "exact":
        assert check.point is not None
        y = dec(check.point)
        return sum(lower_term(y, y, term) for term in terms)
    assert check.bracket is not None
    left, right = map(dec, check.bracket)
    return sum(lower_term(left, right, term) for term in terms)

def main() -> int:
    q = Fraction
    terms = [
        LogTerm(q(1), q(0)),
        LogTerm(q(1174168821, 1000000000), q(180650001, 100000000)),
        LogTerm(q(25921118, 1000000000), q(257053197, 100000000)),
        LogTerm(q(118647936, 1000000000), q(268367709, 100000000)),
        LogTerm(q(180553554, 1000000000), q(279017717, 100000000)),
    ]
    checks = [
        Check("V(0.708)", "exact", point=q(708, 1000), threshold=q(1, 1000)),
        Check("V(r1 bracket)", "bracket", bracket=(q(77003805, 100000000), q(77003806, 100000000)), threshold=q(5, 1000000)),
        Check("V(r2 bracket)", "bracket", bracket=(q(252642600, 100000000), q(252642601, 100000000)), threshold=q(5, 1000000)),
        Check("V(r3 bracket)", "bracket", bracket=(q(260759965, 100000000), q(260759966, 100000000)), threshold=q(5, 1000000)),
        Check("V(r4 bracket)", "bracket", bracket=(q(274249871, 100000000), q(274249872, 100000000)), threshold=q(5, 1000000)),
        Check("V(2.806304)", "exact", point=q(2806304, 1000000), threshold=q(3, 1000000)),
    ]
    with localcontext() as ctx:
        ctx.prec = PRECISION
        print("Five-atom Decimal checker for M=1.806304")
        for check in checks:
            lower = lower_check(check, terms)
            threshold = dec(check.threshold)
            ok = lower > threshold
            print(f"{check.label:18} lower={lower} threshold={threshold} {'PASS' if ok else 'FAIL'}")
            if not ok:
                return 1
    print("status: PASS")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
