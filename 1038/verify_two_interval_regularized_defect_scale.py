#!/usr/bin/env python3
"""Diagnostic scale of the regularized branch defect.

The canonical regularized residual matches the small-eta limiting normal form,
but it is not zero on the original solved positive-eta branch.  This checker
measures that defect and estimates the Newton center correction in fold
coordinates.

Status: diagnostic.  It uses solved double-precision branch points and
finite-difference Jacobians.
"""

from __future__ import annotations

import argparse
import importlib.util
import math
import sys
from pathlib import Path
from typing import Any

import numpy as np
from flint import arb


ROOT = Path(__file__).resolve().parent
SOLVER_PATH = ROOT / "solve_two_interval_finite_gap.py"


def load_solver() -> Any:
    spec = importlib.util.spec_from_file_location("solve_two_interval_finite_gap", SOLVER_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import solver from {SOLVER_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def parse_epsilons(raw: str) -> list[float]:
    return [float(part) for part in raw.split(",") if part.strip()]


def regularized_residual(
    solver: Any,
    A: float,
    alpha: float,
    eta: float,
    limit_A: float,
    limit_alpha: float,
    left_weight: float,
    precision: int,
) -> np.ndarray:
    base_delta_alpha = (alpha - limit_alpha) / eta
    base_delta_A = (A - limit_A) / eta
    arb_eta = arb(repr(float(eta)))
    K1 = float(
        arb(
            solver._potential_residue_log_value_divided_from_arb(
                arb(repr(float(A))),
                arb(repr(float(alpha))),
                arb_eta,
                arb(repr(float(limit_A))),
                arb(repr(float(limit_alpha))),
                "contact",
                precision,
                arb(repr(float(base_delta_A))),
                arb(repr(float(base_delta_alpha))),
            )
        ).mid()
    )
    K2 = float(
        arb(
            solver._combined_residue_log_value_second_divided_from_arb(
                arb(repr(float(A))),
                arb(repr(float(alpha))),
                arb_eta,
                arb(repr(float(left_weight))),
                arb(repr(float(limit_A))),
                arb(repr(float(limit_alpha))),
                precision,
                arb(repr(float(base_delta_A))),
                arb(repr(float(base_delta_alpha))),
                regularize_joint_limit_layer=True,
            )
        ).mid()
    )
    return np.asarray([K1, K2], dtype=float)


def finite_difference_jacobian(fn: Any, z: np.ndarray, h: float) -> np.ndarray:
    columns = []
    for index in range(2):
        step = np.zeros(2)
        step[index] = h
        columns.append((fn(z + step) - fn(z - step)) / (2.0 * h))
    return np.column_stack(columns)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--epsilons", default="1e-8,3e-8,1e-7,3e-7,1e-6,3e-6,1e-5")
    parser.add_argument("--precision", type=int, default=192)
    parser.add_argument("--fd-step", type=float, default=1.0e-6)
    parser.add_argument("--max-correction", type=float, default=1.0e-3)
    args = parser.parse_args()

    solver = load_solver()
    limit = solver.solve_limit()
    left_weight, null_slope, _forcing_ratios, _curvature, amplitude_alpha, amplitude_A = solver.fold_diagnostics()
    guess = (limit.A + amplitude_A * math.sqrt(1.0e-8), limit.alpha + amplitude_alpha * math.sqrt(1.0e-8))

    rows = []
    worst_defect = 0.0
    worst_correction = 0.0
    for epsilon in parse_epsilons(args.epsilons):
        eta = math.sqrt(epsilon)
        solution, guess = solver.solve_one(epsilon, guess)
        B = (solution.A - limit.A) / eta - float(null_slope) * ((solution.alpha - limit.alpha) / eta)
        tau = (solution.alpha - limit.alpha) / eta

        def map_in_fold(point: np.ndarray) -> np.ndarray:
            Bp, taup = float(point[0]), float(point[1])
            A = limit.A + eta * (float(null_slope) * taup + Bp)
            alpha = limit.alpha + eta * taup
            return regularized_residual(
                solver,
                A,
                alpha,
                eta,
                limit.A,
                limit.alpha,
                float(left_weight),
                args.precision,
            )

        z = np.asarray([B, tau], dtype=float)
        defect = map_in_fold(z)
        J = finite_difference_jacobian(map_in_fold, z, args.fd_step)
        correction = -np.linalg.solve(J, defect)
        corrected_defect = map_in_fold(z + correction)
        defect_norm = float(np.linalg.norm(defect, ord=np.inf))
        correction_norm = float(np.linalg.norm(correction, ord=np.inf))
        corrected_norm = float(np.linalg.norm(corrected_defect, ord=np.inf))
        worst_defect = max(worst_defect, defect_norm)
        worst_correction = max(worst_correction, correction_norm)
        rows.append((eta, defect_norm))
        print(
            f"epsilon={epsilon:.6e} eta={eta:.6e} B={B:.6e} tau={tau:.6e} "
            f"defect_inf={defect_norm:.6e} correction=({correction[0]:.6e},{correction[1]:.6e}) "
            f"correction_inf={correction_norm:.6e} corrected_inf={corrected_norm:.6e}"
        )

    if len(rows) >= 2:
        log_eta = np.log([row[0] for row in rows])
        log_defect = np.log([max(row[1], 1.0e-300) for row in rows])
        slope, intercept = np.polyfit(log_eta, log_defect, 1)
    else:
        slope, intercept = float("nan"), float("nan")

    ok = worst_correction <= args.max_correction
    print(
        "TWO-INTERVAL REGULARIZED DEFECT SCALE: "
        f"{'PASS-DIAGNOSTIC' if ok else 'FAIL-DIAGNOSTIC'} rows={len(rows)} "
        f"worst_defect={worst_defect:.6e} worst_correction={worst_correction:.6e} "
        f"loglog_slope={slope:.6e} loglog_intercept={intercept:.6e}"
    )
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
