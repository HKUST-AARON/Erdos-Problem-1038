#!/usr/bin/env python3
"""Exploratory optimizer for finite-atom blocks beyond the 1.8 certificate.

This is not a proof.  It searches for a positive atomic dual measure of the form

    delta_a + sum_i w_i delta_{a+d_i}

valid for a in [-M,-T], currently with T=1.7.  If such a block is certified,
it would extend the four-atom part of the 1.8 lower-bound route to M > 1.8,
provided the existing forcing step still proves (-T,0) under |E| < M.
"""
from __future__ import annotations

import argparse
import math
from dataclasses import dataclass
from typing import Sequence

import numpy as np
from scipy.optimize import differential_evolution, linprog


@dataclass
class Candidate:
    M: float
    T: float
    shifts: np.ndarray
    weights: np.ndarray
    margin: float
    lp_success: bool


def y_grid(M: float, shifts: Sequence[float], n: int) -> np.ndarray:
    lo = CURRENT_T - 1.0
    hi = 1.0 + M
    pts = [lo, hi]
    for d in shifts:
        if lo < d < hi:
            eps = 1e-5
            pts.extend([max(lo, d - eps), min(hi, d + eps)])
    pts.extend(np.linspace(lo, hi, n))
    return np.array(sorted(set(round(float(p), 12) for p in pts)))


def valid_shifts(M: float, T: float, shifts: Sequence[float], sep: float) -> bool:
    shifts = list(shifts)
    if any(d <= T - 1.0 or d >= 1.0 + M for d in shifts):
        return False
    if shifts[0] < M + sep:
        return False
    gap = M - T + sep
    return all(shifts[i + 1] - shifts[i] >= gap for i in range(len(shifts) - 1))


def solve_weights(M: float, T: float, shifts: Sequence[float], grid_n: int, wmax: float) -> Candidate:
    shifts = np.array(shifts, dtype=float)
    ys = y_grid(M, shifts, grid_n)
    base = -np.log(np.abs(ys))
    terms = np.stack([-np.log(np.abs(ys - d)) for d in shifts], axis=1)

    # Variables are weights w_i and margin m.  Constraint:
    # base + terms @ w >= m.
    # Equivalently -terms @ w + m <= base.
    c = np.zeros(len(shifts) + 1)
    c[-1] = -1.0
    A_ub = np.concatenate([-terms, np.ones((len(ys), 1))], axis=1)
    b_ub = base
    bounds = [(1e-5, wmax) for _ in shifts] + [(-10.0, 10.0)]
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method="highs")
    if not res.success:
        return Candidate(M, T, shifts, np.zeros_like(shifts), -1e9, False)
    return Candidate(M, T, shifts, res.x[:-1], float(res.x[-1]), True)


CURRENT_T = 1.7


def optimize(M: float, T: float, atoms: int, grid_n: int, iterations: int, seed: int, sep: float) -> Candidate:
    global CURRENT_T
    CURRENT_T = T
    lo = T - 1.0
    hi = 1.0 + M
    bounds = [(lo + 1e-4, hi - 1e-4) for _ in range(atoms)]

    def objective(raw: np.ndarray) -> float:
        shifts = np.sort(raw)
        if not valid_shifts(M, T, shifts, sep):
            # Smooth-ish penalty for invalid geometry.
            return 100.0 + float(np.sum(np.abs(np.diff(shifts))))
        cand = solve_weights(M, T, shifts, grid_n, wmax=8.0)
        return -cand.margin if cand.lp_success else 100.0

    result = differential_evolution(
        objective,
        bounds,
        maxiter=iterations,
        popsize=12,
        seed=seed,
        polish=True,
        workers=1,
        updating="immediate",
        tol=1e-5,
    )
    shifts = np.sort(result.x)
    return solve_weights(M, T, shifts, grid_n * 3, wmax=8.0)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--M", type=float, required=True)
    parser.add_argument("--T", type=float, default=1.7)
    parser.add_argument("--atoms", type=int, default=3, help="number of positive shifted atoms after delta_a")
    parser.add_argument("--grid", type=int, default=1200)
    parser.add_argument("--iter", type=int, default=80)
    parser.add_argument("--seed", type=int, default=1038)
    parser.add_argument("--sep", type=float, default=0.0002)
    args = parser.parse_args()

    cand = optimize(args.M, args.T, args.atoms, args.grid, args.iter, args.seed, args.sep)
    print(f"M={cand.M:.10f} T={cand.T:.10f} atoms_after_delta_a={len(cand.shifts)}")
    print(f"lp_success={cand.lp_success} grid_margin={cand.margin:.12g}")
    print("shifts=" + ", ".join(f"{x:.12f}" for x in cand.shifts))
    print("weights=" + ", ".join(f"{x:.12f}" for x in cand.weights))
    return 0 if cand.lp_success and cand.margin > 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
