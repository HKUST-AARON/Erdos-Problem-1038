#!/usr/bin/env python3
"""Finite-difference stress test for the K2 edge tau derivative."""

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
    parser.add_argument("--grid", type=int, default=401)
    parser.add_argument("--h", type=float, default=1.0e-5)
    parser.add_argument("--eta-values", default="1e-16,1e-12,1e-8")
    parser.add_argument("--candidate-lipschitz", type=float, default=2.0e-4)
    parser.add_argument("--candidate-curvature", type=float, default=2.5e-4)
    args = parser.parse_args()

    if args.grid < 3:
        raise SystemExit("grid must be at least 3")
    if args.h <= 0:
        raise SystemExit("h must be positive")

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

    def k2_point(B: float, tau: float, eta: float) -> float:
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

    def k0_2(B: float, tau: float) -> float:
        return forcing + q20 * B * B + q11 * B * tau + q02 * tau * tau

    def remainder(B: float, tau: float, eta: float) -> float:
        return k2_point(B, tau, eta) - k0_2(B, tau)

    eta_values = [float(part) for part in args.eta_values.split(",") if part.strip()]
    worst_derivative = 0.0
    worst_curvature = 0.0
    worst_derivative_source = ""
    worst_curvature_source = ""
    for B in (0.01, -0.01):
        for eta in eta_values:
            local_derivative = 0.0
            local_curvature = 0.0
            for index in range(args.grid):
                tau = tau0 - 0.05 + 0.1 * index / (args.grid - 1)
                if tau - args.h < tau0 - 0.05:
                    derivative = (remainder(B, tau + args.h, eta) - remainder(B, tau, eta)) / args.h
                    curvature = (
                        remainder(B, tau + 2 * args.h, eta)
                        - 2 * remainder(B, tau + args.h, eta)
                        + remainder(B, tau, eta)
                    ) / (args.h * args.h)
                elif tau + args.h > tau0 + 0.05:
                    derivative = (remainder(B, tau, eta) - remainder(B, tau - args.h, eta)) / args.h
                    curvature = (
                        remainder(B, tau, eta)
                        - 2 * remainder(B, tau - args.h, eta)
                        + remainder(B, tau - 2 * args.h, eta)
                    ) / (args.h * args.h)
                else:
                    derivative = (remainder(B, tau + args.h, eta) - remainder(B, tau - args.h, eta)) / (2 * args.h)
                    curvature = (
                        remainder(B, tau + args.h, eta)
                        - 2 * remainder(B, tau, eta)
                        + remainder(B, tau - args.h, eta)
                    ) / (args.h * args.h)
                abs_derivative = abs(derivative)
                abs_curvature = abs(curvature)
                local_derivative = max(local_derivative, abs_derivative)
                local_curvature = max(local_curvature, abs_curvature)
                if abs_derivative > worst_derivative:
                    worst_derivative = abs_derivative
                    worst_derivative_source = f"B={B:+.2f},eta={eta:.1e},tau={tau:.12e}"
                if abs_curvature > worst_curvature:
                    worst_curvature = abs_curvature
                    worst_curvature_source = f"B={B:+.2f},eta={eta:.1e},tau={tau:.12e}"
            print(
                f"B={B:+.2f} eta={eta:.1e} "
                f"max_abs_derivative={local_derivative:.6e} "
                f"max_abs_curvature={local_curvature:.6e}"
            )

    derivative_status = worst_derivative < args.candidate_lipschitz
    curvature_status = worst_curvature < args.candidate_curvature
    status = "PASS-DIAGNOSTIC" if derivative_status and curvature_status else "FAIL-DIAGNOSTIC"
    print(
        "TWO-INTERVAL K2 TAU DERIVATIVE: "
        f"{status} grid={args.grid:d} h={args.h:.6e} "
        f"worst_derivative={worst_derivative:.6e} candidate_lipschitz={args.candidate_lipschitz:.6e} "
        f"worst_derivative_source={worst_derivative_source!r} "
        f"worst_curvature={worst_curvature:.6e} candidate_curvature={args.candidate_curvature:.6e} "
        f"worst_curvature_source={worst_curvature_source!r}"
    )
    return 0 if status == "PASS-DIAGNOSTIC" else 1


if __name__ == "__main__":
    raise SystemExit(main())
