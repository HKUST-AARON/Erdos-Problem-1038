#!/usr/bin/env python3
"""Finite checker for distinct covering systems with prescribed moduli.

This is a bounded verifier only. It answers:
given distinct moduli m_1,...,m_k, does there exist one residue a_i modulo
each m_i such that the chosen congruence classes cover Z/lcm(m_i)Z?
"""

from __future__ import annotations

import argparse
import math
import sys
from fractions import Fraction

try:
    import z3
except ImportError as exc:  # pragma: no cover - runtime environment guard
    raise SystemExit(
        "Missing dependency: z3-solver. Install with: python3 -m pip install -r requirements-odd-cover.txt"
    ) from exc


def parse_moduli(raw: str) -> list[int]:
    try:
        moduli = [int(part.strip()) for part in raw.split(",") if part.strip()]
    except ValueError as exc:
        raise argparse.ArgumentTypeError("moduli must be comma-separated integers") from exc

    if not moduli:
        raise argparse.ArgumentTypeError("at least one modulus is required")
    if len(set(moduli)) != len(moduli):
        raise argparse.ArgumentTypeError("moduli must be distinct")
    if any(m <= 1 for m in moduli):
        raise argparse.ArgumentTypeError("all moduli must be greater than 1")
    if any(m % 2 == 0 for m in moduli):
        raise argparse.ArgumentTypeError("this checker expects odd moduli only")
    return sorted(moduli)


def nontrivial_divisors(n: int) -> list[int]:
    divs: set[int] = set()
    for d in range(2, math.isqrt(n) + 1):
        if n % d == 0:
            divs.add(d)
            if d != n // d:
                divs.add(n // d)
    divs.add(n)
    return sorted(d for d in divs if d > 1 and d % 2 == 1)


def lcm_many(values: list[int]) -> int:
    result = 1
    for value in values:
        result = math.lcm(result, value)
    return result


def density_bound(moduli: list[int]) -> Fraction:
    return sum((Fraction(1, m) for m in moduli), Fraction(0, 1))


def solve_cover(moduli: list[int], limit_lcm: int, force: bool, timeout_ms: int) -> int:
    period = lcm_many(moduli)
    reciprocal_sum = density_bound(moduli)

    print(f"moduli={','.join(map(str, moduli))}", flush=True)
    print(f"count={len(moduli)}", flush=True)
    print(f"lcm={period}", flush=True)
    print(f"reciprocal_sum={reciprocal_sum} ({float(reciprocal_sum):.6f})", flush=True)

    if reciprocal_sum < 1:
        print("result=UNSAT", flush=True)
        print("reason=density bound: sum(1/m) < 1", flush=True)
        return 20

    if period > limit_lcm and not force:
        print("result=NOT_RUN", flush=True)
        print(f"reason=lcm {period} exceeds --limit-lcm {limit_lcm}; pass --force to run anyway", flush=True)
        return 2

    solver = z3.Solver()
    solver.set(timeout=timeout_ms)

    residues: dict[int, z3.IntNumRef] = {}
    for m in moduli:
        residue = z3.Int(f"r_{m}")
        residues[m] = residue
        solver.add(residue >= 0, residue < m)

    for value in range(period):
        solver.add(z3.Or([residues[m] == value % m for m in moduli]))

    status = solver.check()
    if status == z3.sat:
        model = solver.model()
        selected: list[tuple[int, int]] = []
        for m in moduli:
            selected.append((model.eval(residues[m], model_completion=True).as_long(), m))
        covered = [False] * period
        for residue, m in selected:
            for value in range(residue, period, m):
                covered[value] = True
        print("result=SAT", flush=True)
        print("selected=" + ",".join(f"{a} mod {m}" for a, m in selected), flush=True)
        print(f"covered={sum(covered)}/{period}", flush=True)
        return 10

    if status == z3.unsat:
        print("result=UNSAT", flush=True)
        print("reason=z3 proof search", flush=True)
        return 20

    print("result=UNKNOWN", flush=True)
    print(f"reason={solver.reason_unknown()}", flush=True)
    return 1


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--moduli", type=parse_moduli, help="comma-separated odd distinct moduli")
    group.add_argument("--divisors-of", type=int, help="use all odd nontrivial divisors of this odd integer")
    parser.add_argument("--limit-lcm", type=int, default=50_000)
    parser.add_argument("--force", action="store_true")
    parser.add_argument("--timeout-ms", type=int, default=30_000)
    args = parser.parse_args()

    if args.divisors_of is not None:
        if args.divisors_of <= 1 or args.divisors_of % 2 == 0:
            parser.error("--divisors-of must be an odd integer greater than 1")
        moduli = nontrivial_divisors(args.divisors_of)
    else:
        moduli = args.moduli

    return solve_cover(moduli, args.limit_lcm, args.force, args.timeout_ms)


if __name__ == "__main__":
    sys.exit(main())
