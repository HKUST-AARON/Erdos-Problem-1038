#!/usr/bin/env python3
"""Diagnostic remainder check for the small-eta limiting winding.

This compares the positive-eta branch map K_eta against a limiting fold
normal form

    K0(B,tau) = (J00 * B, forcing + q20 B^2 + q11 B tau + q02 tau^2)

on the boundary rectangle used by ``verify_two_interval_small_eta_limit.py``.

Status: diagnostic.  It uses fixed-parameter Arb residue-log values at sampled
eta and boundary points.  A proof-grade version must replace the sampling by
uniform eta and boundary interval enclosures.
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


ARTIFACT_ROOT = Path(__file__).resolve().parent
ROOT = ARTIFACT_ROOT.parent
SOLVER_PATH = ARTIFACT_ROOT / "solve_two_interval_finite_gap.py"


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
    parser.add_argument("--eta-max", type=float, default=math.sqrt(1.0e-5))
    parser.add_argument("--eta-min", type=float, default=1.0e-8)
    parser.add_argument("--eta-samples", type=int, default=9)
    parser.add_argument("--radius-B", type=float, default=0.01)
    parser.add_argument("--radius-tau", type=float, default=0.05)
    parser.add_argument("--edge-samples", type=int, default=16)
    parser.add_argument("--precision", type=int, default=192)
    parser.add_argument("--fail-ratio", type=float, default=1.0)
    parser.add_argument(
        "--renormalize-limit-layer",
        action="store_true",
        help="Diagnostic only: use the solver's regularized joint limit-layer K2 kernel before comparing with K0.",
    )
    args = parser.parse_args()

    if not (0.0 < args.eta_min <= args.eta_max):
        raise SystemExit("expected 0 < eta-min <= eta-max")

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
                        regularize_joint_limit_layer=args.renormalize_limit_layer,
                    )
                )
            except Exception as exc:  # noqa: BLE001 - diagnostic reports exact blocker.
                failures += 1
                current = (float("inf"), eta, B, tau, side, f"{type(exc).__name__}: {exc}")
                worst = current if worst is None else worst
                continue
            diff = np.asarray([K1, K2], dtype=float) - K0(B, tau)
            norm = float(np.linalg.norm(diff, ord=2))
            if norm > worst_norm:
                worst_norm = norm
                worst = (norm, eta, B, tau, side, diff)

    # From verify_two_interval_small_eta_limit.py with the same default radius.
    limiting_min_origin = abs(j00) * args.radius_B
    ratio = worst_norm / limiting_min_origin if math.isfinite(worst_norm) else float("inf")
    status = "PASS-DIAGNOSTIC" if failures == 0 and ratio < args.fail_ratio else "FAIL-DIAGNOSTIC"
    print(
        "TWO-INTERVAL SMALL-ETA REMAINDER: "
        f"{status} samples={len(eta_values) * len(boundary)} failures={failures} "
        f"eta_min={args.eta_min:.6e} eta_max={args.eta_max:.6e} "
        f"max_remainder={worst_norm:.6e} limiting_min_origin={limiting_min_origin:.6e} ratio={ratio:.6e} "
        f"worst={worst!r}"
    )
    return 0 if status == "PASS-DIAGNOSTIC" else 1


if __name__ == "__main__":
    raise SystemExit(main())
