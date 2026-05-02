#!/usr/bin/env python3
"""Deterministic grid verifier for the conservative (-1.7, 0) forcing family.

This is an exploratory checker, not a proof. It samples the parameter triangle

    a in [-1.7, -sqrt(2)]
    b in [0, 1.82 + a]

and evaluates the potential

    U(x) = -log(|x-a|) - w log(|x-b|) - C log(|x-c|)

at x = -1, 0, 1, and at the real critical roots of the derivative quadratic
that lie in [0, 1] away from the singular barriers b and c.

Standard library only.
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass
from typing import Iterable, List, Sequence, Tuple


AMIN = -1.7
AMAX = -math.sqrt(2.0)

# Conservative forcing family convention:
# w = 1.395 - b, c = 1.071 - b, and C is fixed by the boundary normalization
# U_nu(-1) = 1e-4 under U(x) = -sum(weights * log(distance)).

@dataclass
class CandidateValue:
    value: float
    x: float
    kind: str


@dataclass
class Failure:
    a: float
    b: float
    reason: str


def linspace(lo: float, hi: float, n: int) -> List[float]:
    if n <= 1:
        return [0.5 * (lo + hi)]
    if lo == hi:
        return [lo for _ in range(n)]
    step = (hi - lo) / (n - 1)
    return [lo + step * i for i in range(n)]


def safe_log_abs(x: float) -> float:
    return math.log(abs(x))


def potential(x: float, a: float, b: float, w: float, c: float, C: float, tol: float) -> float:
    if abs(x - b) <= tol or abs(x - c) <= tol:
        return math.inf
    try:
        return -safe_log_abs(x - a) - w * safe_log_abs(x - b) - C * safe_log_abs(x - c)
    except ValueError:
        return math.nan


def quadratic_roots(a2: float, b1: float, c0: float, tol: float = 1e-15) -> List[float]:
    if abs(a2) <= tol:
        if abs(b1) <= tol:
            return []
        return [-c0 / b1]

    disc = b1 * b1 - 4.0 * a2 * c0
    if disc < -tol:
        return []
    if disc < 0.0:
        disc = 0.0
    sqrt_disc = math.sqrt(disc)

    if b1 >= 0.0:
        q = -0.5 * (b1 + sqrt_disc)
    else:
        q = -0.5 * (b1 - sqrt_disc)

    if abs(q) <= tol:
        root = -b1 / (2.0 * a2)
        return [root]

    r1 = q / a2
    r2 = c0 / q
    return [r1, r2]


def unique_sorted(values: Iterable[float], tol: float = 1e-12) -> List[float]:
    out: List[float] = []
    for v in sorted(values):
        if not out or abs(v - out[-1]) > tol:
            out.append(v)
    return out


def critical_roots_in_unit_interval(
    a: float,
    b: float,
    w: float,
    c: float,
    C: float,
    tol: float,
) -> List[float]:
    qa = 1.0 + w + C
    qb = -((b + c) + w * (a + c) + C * (a + b))
    qc = (b * c) + (w * a * c) + (C * a * b)
    roots = quadratic_roots(qa, qb, qc)
    filtered = []
    for r in roots:
        if -tol <= r <= 1.0 + tol and abs(r - b) > tol and abs(r - c) > tol:
            filtered.append(r)
    return unique_sorted(filtered, tol=1e-10)


def evaluate_candidates(
    a: float,
    b: float,
    tol: float,
) -> Tuple[List[CandidateValue], float, float]:
    w = 1.395 - b
    c = 1.071 - b

    denom = math.log(2.071 - b)
    if denom <= 0.0:
        raise ValueError(f"log denominator nonpositive: log(2.071-b) with b={b:.16g}")

    C = (-1.0e-4 - math.log(-1.0 - a) - (1.395 - b) * math.log(1.0 + b)) / denom

    candidates: List[CandidateValue] = []
    for x, kind in [(-1.0, "x=-1"), (0.0, "x=0"), (1.0, "x=1")]:
        candidates.append(CandidateValue(potential(x, a, b, w, c, C, tol), x, kind))

    for r in critical_roots_in_unit_interval(a, b, w, c, C, tol):
        candidates.append(CandidateValue(potential(r, a, b, w, c, C, tol), r, "critical"))

    return candidates, w, C


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--density",
        type=int,
        default=501,
        help="fallback grid density for both axes if axis-specific values are omitted (default: 501)",
    )
    parser.add_argument(
        "--a-density",
        type=int,
        default=None,
        help="grid density for the a-axis (defaults to --density)",
    )
    parser.add_argument(
        "--b-density",
        type=int,
        default=None,
        help="grid density for the b-axis (defaults to --density)",
    )
    parser.add_argument(
        "--tol",
        type=float,
        default=1e-12,
        help="tolerance for singularity detection and root filtering (default: 1e-12)",
    )
    args = parser.parse_args()

    if args.density < 2:
        raise SystemExit("--density must be at least 2")

    a_density = args.a_density if args.a_density is not None else args.density
    b_density = args.b_density if args.b_density is not None else args.density

    if a_density < 2:
        raise SystemExit("--a-density must be at least 2")
    if b_density < 2:
        raise SystemExit("--b-density must be at least 2")

    a_values = linspace(AMIN, AMAX, a_density)

    overall_min = math.inf
    argmin: CandidateValue | None = None
    argmin_params: Tuple[float, float] | None = None
    c_min = math.inf
    c_max = -math.inf

    failures: List[Failure] = []
    barrier_hits = 0
    bad_weights = 0
    scanned = 0
    candidate_count = 0
    positive_count = 0

    for a in a_values:
        b_max = 1.82 + a
        b_values = linspace(0.0, b_max, b_density)
        for b in b_values:
            scanned += 1
            try:
                candidates, w, C = evaluate_candidates(a, b, args.tol)
            except Exception as exc:
                failures.append(Failure(a, b, f"evaluation error: {exc}"))
                continue

            c_min = min(c_min, C)
            c_max = max(c_max, C)

            if w <= 0.0 or C <= 0.0:
                bad_weights += 1
                failures.append(
                    Failure(a, b, f"nonpositive weight: w={w:.16g}, C={C:.16g}")
                )
                continue

            for cand in candidates:
                candidate_count += 1
                if math.isinf(cand.value) and cand.value > 0:
                    barrier_hits += 1
                    continue
                if math.isnan(cand.value):
                    failures.append(Failure(a, b, f"NaN at x={cand.x:.16g} ({cand.kind})"))
                    continue
                if cand.value > 0.0:
                    positive_count += 1
                if cand.value < overall_min:
                    overall_min = cand.value
                    argmin = cand
                    argmin_params = (a, b)
                if cand.value <= 0.0:
                    failures.append(
                        Failure(
                            a,
                            b,
                            f"nonpositive U at x={cand.x:.16g} ({cand.kind}): {cand.value:.16g}",
                        )
                    )

    status = "PASS" if not failures and overall_min > 0.0 else "FAIL"

    print("Conservative (-1.7, 0) forcing family grid verifier")
    print(f"domain: a in [{AMIN:.16g}, {AMAX:.16g}], b in [0, 1.82 + a]")
    print(f"grid density: {a_density} x {b_density}")
    print(f"scanned parameter points: {scanned}")
    print(f"candidate evaluations: {candidate_count}")
    print(f"barrier hits (returned +inf): {barrier_hits}")
    print(f"positive candidate values: {positive_count}")
    print(f"status: {status}")

    if argmin is not None and argmin_params is not None:
        a_star, b_star = argmin_params
        print(
            "minimum U:"
            f" {overall_min:.16g} at a={a_star:.16g}, b={b_star:.16g},"
            f" x={argmin.x:.16g} ({argmin.kind})"
        )
    else:
        print("minimum U: not found")

    if math.isfinite(c_min) and math.isfinite(c_max):
        print(f"C range: [{c_min:.16g}, {c_max:.16g}]")
    else:
        print("C range: unavailable")

    if failures:
        print(f"failures: {len(failures)}")
        for idx, failure in enumerate(failures[:10], start=1):
            print(
                f"  {idx}. a={failure.a:.16g}, b={failure.b:.16g}: {failure.reason}"
            )
        if len(failures) > 10:
            print(f"  ... {len(failures) - 10} more")
    else:
        print("failures: 0")

    return 0 if status == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
