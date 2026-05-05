#!/usr/bin/env python3
"""Acceptance gate for the remaining small-eta asymptotic obligation.

This script does not prove the endpoint theorem.  It makes the remaining proof
obligation explicit and machine-checks the numerical slack that a future Arb
interval remainder certificate must beat.
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


def arb_mid(value: str) -> float:
    return float(arb(value).mid())


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--eta-min", type=float, default=1.0e-16)
    parser.add_argument("--eta-max", type=float, default=1.0e-8)
    parser.add_argument("--eta-samples", type=int, default=9)
    parser.add_argument("--edge-samples", type=int, default=8)
    parser.add_argument("--radius-B", type=float, default=0.01)
    parser.add_argument("--radius-tau", type=float, default=0.05)
    parser.add_argument("--target-bound", type=float, default=7.0e-3)
    parser.add_argument("--precision", type=int, default=192)
    args = parser.parse_args()

    if not (0.0 < args.eta_min <= args.eta_max):
        raise SystemExit("expected 0 < eta-min <= eta-max")
    if args.target_bound <= 0.0:
        raise SystemExit("target-bound must be positive")

    solver = load_solver()
    limit_solution = solver.solve_limit()
    left_weight, null_slope, forcing_ratios, curvature, tau0, _amp_A = solver.fold_diagnostics()
    jacobian = solver.limit_jacobian()
    j00 = float(jacobian[0, 0])
    forcing = float(forcing_ratios[-1][1])
    curvature = float(curvature)
    tau0 = float(tau0)
    left_null = np.asarray([float(left_weight), 1.0], dtype=float)

    def second_coefficients() -> tuple[float, float, float]:
        h = 1.0e-4
        base = np.asarray(solver.limit_equations(np.asarray([limit_solution.A, limit_solution.alpha])), dtype=float)

        def q(B: float, tau: float) -> float:
            delta = np.asarray([h * (float(null_slope) * tau + B), h * tau], dtype=float)
            point = np.asarray([limit_solution.A, limit_solution.alpha], dtype=float) + delta
            value = np.asarray(solver.limit_equations(point), dtype=float)
            linear = jacobian @ delta
            return float(left_null @ (value - base - linear) / (h * h))

        q20 = q(1.0, 0.0)
        q02 = q(0.0, 1.0)
        q11 = q(1.0, 1.0) - q20 - q02
        return q20, q11, q02

    q20, q11, q02 = second_coefficients()

    def K0(B: float, tau: float) -> np.ndarray:
        return np.asarray([j00 * B, forcing + q20 * B * B + q11 * B * tau + q02 * tau * tau], dtype=float)

    boundary: list[tuple[float, float, str]] = []
    for index in range(args.edge_samples):
        t = -1.0 + 2.0 * index / args.edge_samples
        boundary.append((args.radius_B, tau0 + t * args.radius_tau, "right"))
    for index in range(args.edge_samples):
        t = 1.0 - 2.0 * index / args.edge_samples
        boundary.append((t * args.radius_B, tau0 + args.radius_tau, "top"))
    for index in range(args.edge_samples):
        t = 1.0 - 2.0 * index / args.edge_samples
        boundary.append((-args.radius_B, tau0 + t * args.radius_tau, "left"))
    for index in range(args.edge_samples):
        t = -1.0 + 2.0 * index / args.edge_samples
        boundary.append((t * args.radius_B, tau0 - args.radius_tau, "bottom"))

    limiting_min_origin = abs(j00) * args.radius_B
    eta_values = np.geomspace(args.eta_min, args.eta_max, args.eta_samples)
    worst_norm = -1.0
    worst = None
    failures = 0

    for eta in eta_values:
        arb_eta = arb(repr(float(eta)))
        for B, tau, side in boundary:
            base_delta_A = arb(repr(float(null_slope * tau + B)))
            base_delta_alpha = arb(repr(float(tau)))
            A = arb(repr(float(limit_solution.A))) + arb_eta * base_delta_A
            alpha = arb(repr(float(limit_solution.alpha))) + arb_eta * base_delta_alpha
            try:
                K1 = arb_mid(
                    solver._potential_residue_log_value_divided_from_arb(
                        A,
                        alpha,
                        arb_eta,
                        arb(repr(float(limit_solution.A))),
                        arb(repr(float(limit_solution.alpha))),
                        "contact",
                        args.precision,
                        base_delta_A,
                        base_delta_alpha,
                    )
                )
                K2 = arb_mid(
                    solver._combined_residue_log_value_second_divided_from_arb(
                        A,
                        alpha,
                        arb_eta,
                        arb(repr(float(left_weight))),
                        arb(repr(float(limit_solution.A))),
                        arb(repr(float(limit_solution.alpha))),
                        args.precision,
                        base_delta_A,
                        base_delta_alpha,
                        regularize_joint_limit_layer=True,
                    )
                )
            except Exception as exc:  # noqa: BLE001
                failures += 1
                if worst is None:
                    worst = (float("inf"), eta, B, tau, side, f"{type(exc).__name__}: {exc}")
                continue

            diff = np.asarray([K1, K2], dtype=float) - K0(B, tau)
            norm = float(np.linalg.norm(diff, ord=2))
            if norm > worst_norm:
                worst_norm = norm
                worst = (norm, eta, B, tau, side, diff)

    sampled_ratio = worst_norm / limiting_min_origin if math.isfinite(worst_norm) else float("inf")
    target_ratio = args.target_bound / limiting_min_origin
    slack_to_margin = limiting_min_origin - args.target_bound
    sampled_slack_to_target = args.target_bound - worst_norm
    sampled_ok = failures == 0 and worst_norm < args.target_bound < limiting_min_origin
    theorem_status = "OPEN"

    print(
        "TWO-INTERVAL ASYMPTOTIC OBLIGATION: "
        f"theorem_status={theorem_status} sampled_gate={'PASS' if sampled_ok else 'FAIL'} "
        f"eta_range=(0,{math.sqrt(3.0e-16):.16e}] "
        f"sample_eta_min={args.eta_min:.6e} sample_eta_max={args.eta_max:.6e} "
        f"samples={len(eta_values) * len(boundary)} failures={failures} "
        f"limiting_min_origin={limiting_min_origin:.6e} target_bound={args.target_bound:.6e} "
        f"slack_to_margin={slack_to_margin:.6e} max_sampled_remainder={worst_norm:.6e} "
        f"sampled_slack_to_target={sampled_slack_to_target:.6e} "
        f"sampled_ratio={sampled_ratio:.6e} target_ratio={target_ratio:.6e} "
        f"needed_certificate='uniform Arb bound for K_eta-K0 below target_bound on boundary boxes' "
        f"worst={worst!r}"
    )
    return 0 if sampled_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
