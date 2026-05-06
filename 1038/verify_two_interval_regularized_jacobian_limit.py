#!/usr/bin/env python3
"""Diagnostic convergence of the regularized residual Jacobian to the limit.

The small-eta theorem needs a uniform determinant lower bound for the
regularized residual map.  This checker compares finite-eta finite-difference
Jacobians in fold coordinates (B,tau) with the quadratic limiting normal form.

Status: diagnostic.  It samples boxes and uses finite differences, not a
proof-grade interval derivative.
"""

from __future__ import annotations

import argparse
import importlib.util
import math
import sys
from pathlib import Path
from typing import Any

import numpy as np


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


def parse_values(raw: str) -> list[float]:
    return [float(part) for part in raw.split(",") if part.strip()]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--etas", default="1e-8,3e-8,1e-7,3e-7,1e-6,1e-5,1e-4")
    parser.add_argument("--radius-B", type=float, default=0.01)
    parser.add_argument("--radius-tau", type=float, default=0.05)
    parser.add_argument("--grid", type=int, default=5)
    parser.add_argument("--fd-step", type=float, default=1.0e-5)
    parser.add_argument("--max-jacobian-error", type=float, default=0.05)
    parser.add_argument("--det-lower", type=float, default=0.01)
    args = parser.parse_args()

    solver = load_solver()
    limit = solver.solve_limit()
    left_weight, null_slope, forcing_ratios, _curvature, tau0, _amp_A = solver.fold_diagnostics()
    limit_jacobian = solver.limit_jacobian()
    j00 = float(limit_jacobian[0, 0])
    left_null = np.asarray([float(left_weight), 1.0], dtype=float)

    def second_coefficients() -> tuple[float, float, float]:
        h = 1.0e-4
        base = np.asarray(solver.limit_equations(np.asarray([limit.A, limit.alpha])), dtype=float)

        def q(B: float, tau: float) -> float:
            delta = np.asarray([h * (float(null_slope) * tau + B), h * tau], dtype=float)
            point = np.asarray([limit.A, limit.alpha], dtype=float) + delta
            value = np.asarray(solver.limit_equations(point), dtype=float)
            linear = limit_jacobian @ delta
            return float(left_null @ (value - base - linear) / (h * h))

        q20 = q(1.0, 0.0)
        q02 = q(0.0, 1.0)
        q11 = q(1.0, 1.0) - q20 - q02
        return q20, q11, q02

    q20, q11, q02 = second_coefficients()

    def K0_jacobian(B: float, tau: float) -> np.ndarray:
        return np.asarray(
            [
                [j00, 0.0],
                [2.0 * q20 * B + q11 * tau, q11 * B + 2.0 * q02 * tau],
            ],
            dtype=float,
        )

    def K_reg(B: float, tau: float, eta: float) -> np.ndarray:
        A = limit.A + eta * (float(null_slope) * tau + B)
        alpha = limit.alpha + eta * tau
        base_delta_A = float(null_slope) * tau + B
        base_delta_alpha = tau
        from flint import arb

        arb_eta = arb(repr(float(eta)))
        K1 = float(
            arb(
                solver._potential_residue_log_value_divided_from_arb(
                    arb(repr(float(A))),
                    arb(repr(float(alpha))),
                    arb_eta,
                    arb(repr(float(limit.A))),
                    arb(repr(float(limit.alpha))),
                    "contact",
                    192,
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
                    arb(repr(float(limit.A))),
                    arb(repr(float(limit.alpha))),
                    192,
                    arb(repr(float(base_delta_A))),
                    arb(repr(float(base_delta_alpha))),
                    regularize_joint_limit_layer=True,
                )
            ).mid()
        )
        return np.asarray([K1, K2], dtype=float)

    def fd_jacobian(B: float, tau: float, eta: float) -> np.ndarray:
        h = args.fd_step
        dB = (K_reg(B + h, tau, eta) - K_reg(B - h, tau, eta)) / (2.0 * h)
        dTau = (K_reg(B, tau + h, eta) - K_reg(B, tau - h, eta)) / (2.0 * h)
        return np.column_stack([dB, dTau])

    worst_error = 0.0
    worst_error_row = None
    min_abs_det = float("inf")
    min_abs_det_row = None
    for eta in parse_values(args.etas):
        for B in np.linspace(-args.radius_B, args.radius_B, args.grid):
            for tau_offset in np.linspace(-args.radius_tau, args.radius_tau, args.grid):
                tau = tau0 + float(tau_offset)
                J = fd_jacobian(float(B), tau, eta)
                J0 = K0_jacobian(float(B), tau)
                error = float(np.linalg.norm(J - J0, ord=np.inf))
                det = float(np.linalg.det(J))
                if error > worst_error:
                    worst_error = error
                    worst_error_row = (eta, float(B), tau, J.tolist(), J0.tolist())
                if abs(det) < min_abs_det:
                    min_abs_det = abs(det)
                    min_abs_det_row = (eta, float(B), tau, det)

    ok = worst_error <= args.max_jacobian_error and min_abs_det >= args.det_lower
    print(
        "TWO-INTERVAL REGULARIZED JACOBIAN LIMIT: "
        f"{'PASS-DIAGNOSTIC' if ok else 'FAIL-DIAGNOSTIC'} "
        f"etas={len(parse_values(args.etas))} grid={args.grid} "
        f"worst_error={worst_error:.6e} worst_error_row={worst_error_row!r} "
        f"min_abs_det={min_abs_det:.6e} min_abs_det_row={min_abs_det_row!r}"
    )
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
