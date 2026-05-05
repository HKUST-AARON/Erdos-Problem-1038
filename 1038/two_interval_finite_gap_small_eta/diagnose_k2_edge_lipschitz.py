#!/usr/bin/env python3
"""Sampled K2 edge remainder and tau-Lipschitz diagnostic."""

from __future__ import annotations

import argparse
import importlib.util
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


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--grid", type=int, default=41)
    parser.add_argument("--target-bound", type=float, default=7.0e-3)
    parser.add_argument("--candidate-lipschitz", type=float, default=2.0e-4)
    parser.add_argument("--eta-values", default="1e-16,1e-12,1e-8")
    args = parser.parse_args()

    if args.grid < 3:
        raise SystemExit("grid must be at least 3")

    solver = load_solver()
    limit = solver.solve_limit()
    left_weight, null_slope, forcing_ratios, _curvature, tau0, _amp_A = solver.fold_diagnostics()
    jacobian = solver.limit_jacobian()
    left_null = np.asarray([float(left_weight), 1.0], dtype=float)
    forcing = float(forcing_ratios[-1][1])
    tau0 = float(tau0)

    def second_coefficients() -> tuple[float, float, float]:
        h = 1.0e-4
        base = np.asarray(solver.limit_equations(np.asarray([limit.A, limit.alpha])), dtype=float)

        def q(B_value: float, tau_value: float) -> float:
            delta = np.asarray([h * (float(null_slope) * tau_value + B_value), h * tau_value], dtype=float)
            point = np.asarray([limit.A, limit.alpha], dtype=float) + delta
            value = np.asarray(solver.limit_equations(point), dtype=float)
            linear = jacobian @ delta
            return float(left_null @ (value - base - linear) / (h * h))

        q20 = q(1.0, 0.0)
        q02 = q(0.0, 1.0)
        q11 = q(1.0, 1.0) - q20 - q02
        return q20, q11, q02

    q20, q11, q02 = second_coefficients()

    def K2_point(B: float, tau: float, eta: float) -> float:
        arb_eta = arb(repr(float(eta)))
        base_delta_A = arb(repr(float(null_slope * tau + B)))
        base_delta_alpha = arb(repr(float(tau)))
        A = arb(repr(float(limit.A))) + arb_eta * base_delta_A
        alpha = arb(repr(float(limit.alpha))) + arb_eta * base_delta_alpha
        return float(
            arb(
                solver._combined_residue_log_value_second_divided_from_arb(
                    A,
                    alpha,
                    arb_eta,
                    arb(repr(float(left_weight))),
                    arb(repr(float(limit.A))),
                    arb(repr(float(limit.alpha))),
                    192,
                    base_delta_A,
                    base_delta_alpha,
                    regularize_joint_limit_layer=True,
                )
            ).mid()
        )

    def K0_2(B: float, tau: float) -> float:
        return forcing + q20 * B * B + q11 * B * tau + q02 * tau * tau

    eta_values = [float(part) for part in args.eta_values.split(",") if part.strip()]
    worst_value = 0.0
    worst_slope = 0.0
    worst_source = ""
    for B in (0.01, -0.01):
        for eta in eta_values:
            values = []
            for index in range(args.grid):
                dt = -0.05 + 0.1 * index / (args.grid - 1)
                tau = tau0 + dt
                values.append(K2_point(B, tau, eta) - K0_2(B, tau))
            local_worst = max(abs(value) for value in values)
            step = 0.1 / (args.grid - 1)
            local_slope = max(abs((values[index + 1] - values[index]) / step) for index in range(args.grid - 1))
            if local_worst > worst_value:
                worst_value = local_worst
                worst_source = f"B={B:+.2f},eta={eta:.1e}"
            worst_slope = max(worst_slope, local_slope)
            print(
                f"B={B:+.2f} eta={eta:.1e} "
                f"range=[{min(values):.6e},{max(values):.6e}] "
                f"max_abs={local_worst:.6e} max_slope={local_slope:.6e}"
            )

    # If a formal slope bound at the candidate level is later certified, even
    # one box per edge would sit far below the 7e-3 winding-margin target.
    tau_radius = 0.05
    implied_bound = worst_value + args.candidate_lipschitz * tau_radius
    status = "PASS-DIAGNOSTIC" if implied_bound < args.target_bound else "FAIL-DIAGNOSTIC"
    print(
        "TWO-INTERVAL K2 EDGE LIPSCHITZ: "
        f"{status} worst_value={worst_value:.6e} sampled_worst_slope={worst_slope:.6e} "
        f"candidate_lipschitz={args.candidate_lipschitz:.6e} implied_edge_bound={implied_bound:.6e} "
        f"target_bound={args.target_bound:.6e} worst_source={worst_source!r}"
    )
    return 0 if status == "PASS-DIAGNOSTIC" else 1


if __name__ == "__main__":
    raise SystemExit(main())
