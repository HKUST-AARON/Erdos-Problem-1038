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
    parser.add_argument(
        "--hybrid-certificate",
        action="store_true",
        help="also run a point-value plus Arb eta-variation plus candidate tau-Lipschitz enclosure",
    )
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

    def K2_eta_variation_abs_upper(B: float, tau: float, eta_low: float, eta_high: float) -> float:
        eta_mid = 0.5 * (eta_low + eta_high)
        arb_eta = solver._arb_interval_from_bounds(eta_low, eta_high)
        arb_eta_mid = arb(repr(float(eta_mid)))
        base_delta_A = arb(repr(float(null_slope * tau + B)))
        base_delta_alpha = arb(repr(float(tau)))
        A = arb(repr(float(limit.A))) + arb_eta * base_delta_A
        alpha = arb(repr(float(limit.alpha))) + arb_eta * base_delta_alpha
        variation = arb(
            solver._combined_residue_log_value_second_divided_eta_variation_from_arb(
                A,
                alpha,
                arb_eta,
                arb_eta_mid,
                arb(repr(float(left_weight))),
                arb(repr(float(limit.A))),
                arb(repr(float(limit.alpha))),
                192,
                base_delta_A,
                base_delta_alpha,
                regularize_joint_limit_layer=True,
            )
        )
        return float(abs(variation).upper())

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

    if args.hybrid_certificate:
        eta_low = min(eta_values)
        eta_high = max(eta_values)
        eta_mid = 0.5 * (eta_low + eta_high)
        tau_step = 0.1 / (args.grid - 1)
        hybrid_worst = 0.0
        hybrid_source = ""
        for B in (0.01, -0.01):
            for index in range(args.grid):
                tau = tau0 - 0.05 + 0.1 * index / (args.grid - 1)
                center_remainder = K2_point(B, tau, eta_mid) - K0_2(B, tau)
                eta_variation = K2_eta_variation_abs_upper(B, tau, eta_low, eta_high)
                tau_allowance = args.candidate_lipschitz * (0.5 * tau_step if 0 < index < args.grid - 1 else tau_step)
                bound = abs(center_remainder) + eta_variation + tau_allowance
                if bound > hybrid_worst:
                    hybrid_worst = bound
                    hybrid_source = (
                        f"B={B:+.2f},index={index},tau={tau:.12e},"
                        f"center={center_remainder:.6e},eta_var={eta_variation:.6e},"
                        f"tau_allowance={tau_allowance:.6e}"
                    )
        hybrid_status = "PASS-DIAGNOSTIC" if hybrid_worst < args.target_bound else "FAIL-DIAGNOSTIC"
        print(
            "TWO-INTERVAL K2 HYBRID EDGE CERTIFICATE: "
            f"{hybrid_status} grid={args.grid:d} eta_low={eta_low:.6e} eta_high={eta_high:.6e} "
            f"candidate_lipschitz={args.candidate_lipschitz:.6e} worst_bound={hybrid_worst:.6e} "
            f"target_bound={args.target_bound:.6e} worst_source={hybrid_source!r}"
        )
        if hybrid_status != "PASS-DIAGNOSTIC":
            status = "FAIL-DIAGNOSTIC"
    return 0 if status == "PASS-DIAGNOSTIC" else 1


if __name__ == "__main__":
    raise SystemExit(main())
