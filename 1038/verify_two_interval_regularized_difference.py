#!/usr/bin/env python3
"""Diagnostic scan of the raw-vs-regularized K2 difference.

The regularized residual map replaces the joint limit-layer contribution in K2.
For the singular branch theorem this replacement must be justified by an
equivalence lemma.  This script maps where the replacement changes K2:

* on solved branch points the difference should be tiny;
* on a boundary grid the difference may be nonzero, so the equivalence proof
  cannot simply claim raw K2 == regularized K2 pointwise;
* near the K1=0 slice, the scan estimates whether the difference is controlled
  by K1 or requires the joint-limit identity directly.
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


def arb_mid(raw: str) -> float:
    return float(arb(raw).mid())


def residual_values(
    solver: Any,
    A: float,
    alpha: float,
    eta: float,
    limit_A: float,
    limit_alpha: float,
    left_weight: float,
    precision: int,
) -> tuple[float, float, float]:
    base_delta_alpha = (alpha - limit_alpha) / eta
    base_delta_A = (A - limit_A) / eta

    def args() -> tuple[arb, arb, arb, arb, arb, arb, arb, arb]:
        return (
            arb(repr(float(A))),
            arb(repr(float(alpha))),
            arb(repr(float(eta))),
            arb(repr(float(left_weight))),
            arb(repr(float(limit_A))),
            arb(repr(float(limit_alpha))),
            arb(repr(float(base_delta_A))),
            arb(repr(float(base_delta_alpha))),
        )

    arb_A, arb_alpha, arb_eta, _arb_left_weight, arb_limit_A, arb_limit_alpha, arb_delta_A, arb_delta_alpha = args()
    K1 = arb_mid(
        solver._potential_residue_log_value_divided_from_arb(
            arb_A,
            arb_alpha,
            arb_eta,
            arb_limit_A,
            arb_limit_alpha,
            "contact",
            precision,
            arb_delta_A,
            arb_delta_alpha,
        )
    )
    # Important: evaluate the regularized kernel before the raw kernel.  The
    # raw path can perturb subsequent regularized evaluations in the same Python
    # process through shared Arb/context state inside the grouped algebra.
    arb_A, arb_alpha, arb_eta, arb_left_weight, arb_limit_A, arb_limit_alpha, arb_delta_A, arb_delta_alpha = args()
    K2_reg = arb_mid(
        solver._combined_residue_log_value_second_divided_from_arb(
            arb_A,
            arb_alpha,
            arb_eta,
            arb_left_weight,
            arb_limit_A,
            arb_limit_alpha,
            precision,
            arb_delta_A,
            arb_delta_alpha,
            regularize_joint_limit_layer=True,
        )
    )
    arb_A, arb_alpha, arb_eta, arb_left_weight, arb_limit_A, arb_limit_alpha, arb_delta_A, arb_delta_alpha = args()
    K2_raw = arb_mid(
        solver._combined_residue_log_value_second_divided_from_arb(
            arb_A,
            arb_alpha,
            arb_eta,
            arb_left_weight,
            arb_limit_A,
            arb_limit_alpha,
            precision,
            arb_delta_A,
            arb_delta_alpha,
        )
    )
    return K1, K2_raw, K2_reg


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--epsilons", default="1e-8,3e-8,1e-7,3e-7,1e-6")
    parser.add_argument(
        "--etas",
        help="Optional comma-separated eta values for grid-only scans; skips solved branch checks.",
    )
    parser.add_argument("--precision", type=int, default=192)
    parser.add_argument("--radius-B", type=float, default=0.01)
    parser.add_argument("--radius-tau", type=float, default=0.05)
    parser.add_argument("--grid", type=int, default=9)
    parser.add_argument("--branch-tol", type=float, default=1.0e-6)
    args = parser.parse_args()

    if args.grid < 3:
        raise SystemExit("--grid must be at least 3")

    solver = load_solver()
    limit = solver.solve_limit()
    left_weight, null_slope, _forcing_ratios, _curvature, tau0, amplitude_A = solver.fold_diagnostics()

    eta_values = parse_epsilons(args.etas) if args.etas else None
    worst_branch_diff = 0.0
    worst_grid_diff = 0.0
    worst_grid = None
    worst_ratio = 0.0
    worst_ratio_row = None
    small_k1_count = 0
    worst_small_k1_diff = 0.0
    if eta_values is None:
        guess = (limit.A + amplitude_A * math.sqrt(1.0e-8), limit.alpha + tau0 * math.sqrt(1.0e-8))
        eta_values = []
        for epsilon in parse_epsilons(args.epsilons):
            eta = math.sqrt(epsilon)
            eta_values.append(eta)
            solution, guess = solver.solve_one(epsilon, guess)
            K1, K2_raw, K2_reg = residual_values(
                solver,
                solution.A,
                solution.alpha,
                eta,
                limit.A,
                limit.alpha,
                float(left_weight),
                args.precision,
            )
            branch_diff = abs(K2_raw - K2_reg)
            worst_branch_diff = max(worst_branch_diff, branch_diff)
            print(
                f"branch epsilon={epsilon:.6e} K1={K1:.6e} raw_minus_reg={branch_diff:.6e} "
                f"K2_raw={K2_raw:.6e} K2_reg={K2_reg:.6e}"
            )

    for eta in eta_values:
        for B in np.linspace(-args.radius_B, args.radius_B, args.grid):
            for tau_offset in np.linspace(-args.radius_tau, args.radius_tau, args.grid):
                tau = tau0 + float(tau_offset)
                A = limit.A + eta * (float(null_slope) * tau + float(B))
                alpha = limit.alpha + eta * tau
                K1, K2_raw, K2_reg = residual_values(
                    solver,
                    A,
                    alpha,
                    eta,
                    limit.A,
                    limit.alpha,
                    float(left_weight),
                    args.precision,
                )
                diff = abs(K2_raw - K2_reg)
                if diff > worst_grid_diff:
                    worst_grid_diff = diff
                    worst_grid = (eta, float(B), tau, K1, K2_raw, K2_reg)
                ratio = diff / max(abs(K1), 1.0e-300)
                if ratio > worst_ratio:
                    worst_ratio = ratio
                    worst_ratio_row = (eta, float(B), tau, K1, diff)
                if abs(K1) <= args.branch_tol:
                    small_k1_count += 1
                    worst_small_k1_diff = max(worst_small_k1_diff, diff)

    print(
        "TWO-INTERVAL REGULARIZED DIFFERENCE: PASS-DIAGNOSTIC "
        f"eta_values={len(eta_values)} grid={args.grid} "
        f"worst_branch_diff={worst_branch_diff:.6e} worst_grid_diff={worst_grid_diff:.6e} "
        f"worst_grid={worst_grid!r} worst_diff_over_abs_K1={worst_ratio:.6e} "
        f"worst_ratio_row={worst_ratio_row!r} small_k1_count={small_k1_count} "
        f"worst_small_k1_diff={worst_small_k1_diff:.6e}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
