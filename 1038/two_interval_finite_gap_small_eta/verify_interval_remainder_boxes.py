#!/usr/bin/env python3
"""Interval box checker for the small-eta remainder on the boundary.

This is a proof-engineering step between sampled diagnostics and the final
asymptotic lemma.  It subdivides the limiting rectangle boundary and directly
encloses ``K_eta - K0`` on each boundary box for a fixed eta interval.
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


def arb_abs_upper(value: Any) -> float:
    return float(abs(value).upper())


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--eta-low", type=float, default=1.0e-16)
    parser.add_argument("--eta-high", type=float, default=1.0e-8)
    parser.add_argument("--radius-B", type=float, default=0.01)
    parser.add_argument("--radius-tau", type=float, default=0.05)
    parser.add_argument("--edge-boxes", type=int, default=64)
    parser.add_argument("--target-bound", type=float, default=7.0e-3)
    parser.add_argument("--precision", type=int, default=192)
    args = parser.parse_args()

    if not (0.0 < args.eta_low <= args.eta_high):
        raise SystemExit("expected 0 < eta-low <= eta-high")
    if args.edge_boxes <= 0:
        raise SystemExit("edge-boxes must be positive")

    solver = load_solver()
    limit = solver.solve_limit()
    left_weight, null_slope, forcing_ratios, curvature, tau0, _amp_A = solver.fold_diagnostics()
    jacobian = solver.limit_jacobian()
    j00 = float(jacobian[0, 0])
    forcing = float(forcing_ratios[-1][1])
    tau0 = float(tau0)
    left_null = np.asarray([float(left_weight), 1.0], dtype=float)
    eta = solver._arb_interval_from_bounds(args.eta_low, args.eta_high)

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

    def box(low: float, high: float) -> Any:
        return solver._arb_interval_from_bounds(low, high)

    def eval_box(label: str, B_low: float, B_high: float, tau_low: float, tau_high: float) -> tuple[float, str]:
        B = box(B_low, B_high)
        tau = box(float(tau0) + tau_low, float(tau0) + tau_high)
        base_delta_A = arb(repr(float(null_slope))) * tau + B
        base_delta_alpha = tau
        A = arb(repr(float(limit.A))) + eta * base_delta_A
        alpha = arb(repr(float(limit.alpha))) + eta * base_delta_alpha
        K1 = arb(
            solver._potential_residue_log_value_divided_from_arb(
                A,
                alpha,
                eta,
                arb(repr(float(limit.A))),
                arb(repr(float(limit.alpha))),
                "contact",
                args.precision,
                base_delta_A,
                base_delta_alpha,
            )
        )
        K2 = arb(
            solver._combined_residue_log_value_second_divided_from_arb(
                A,
                alpha,
                eta,
                arb(repr(float(left_weight))),
                arb(repr(float(limit.A))),
                arb(repr(float(limit.alpha))),
                args.precision,
                base_delta_A,
                base_delta_alpha,
                regularize_joint_limit_layer=True,
            )
        )
        K01 = arb(repr(float(j00))) * B
        K02 = (
            arb(repr(float(forcing)))
            + arb(repr(float(q20))) * B * B
            + arb(repr(float(q11))) * B * tau
            + arb(repr(float(q02))) * tau * tau
        )
        D1 = K1 - K01
        D2 = K2 - K02
        bound = math.hypot(arb_abs_upper(D1), arb_abs_upper(D2))
        return bound, f"{label}: D1={D1} D2={D2}"

    worst_bound = -1.0
    worst_source = ""
    failures = 0
    edges: list[tuple[str, float, float, float, float]] = []
    for index in range(args.edge_boxes):
        a = -1.0 + 2.0 * index / args.edge_boxes
        b = -1.0 + 2.0 * (index + 1) / args.edge_boxes
        edges.append(("right", args.radius_B, args.radius_B, a * args.radius_tau, b * args.radius_tau))
        edges.append(("left", -args.radius_B, -args.radius_B, a * args.radius_tau, b * args.radius_tau))
        edges.append(("top", a * args.radius_B, b * args.radius_B, args.radius_tau, args.radius_tau))
        edges.append(("bottom", a * args.radius_B, b * args.radius_B, -args.radius_tau, -args.radius_tau))

    for label, B_low, B_high, tau_low, tau_high in edges:
        try:
            bound, source = eval_box(label, B_low, B_high, tau_low, tau_high)
        except Exception as exc:  # noqa: BLE001
            failures += 1
            if not worst_source:
                worst_source = f"{label}: {type(exc).__name__}: {exc}"
            continue
        if bound > worst_bound:
            worst_bound = bound
            worst_source = source

    status = "PASS" if failures == 0 and worst_bound < args.target_bound else "FAIL"
    print(
        "TWO-INTERVAL INTERVAL REMAINDER BOXES: "
        f"{status} eta_low={args.eta_low:.6e} eta_high={args.eta_high:.6e} "
        f"edge_boxes={args.edge_boxes:d} boxes={len(edges):d} failures={failures:d} "
        f"target_bound={args.target_bound:.6e} worst_bound={worst_bound:.6e} "
        f"worst_source={worst_source}"
    )
    return 0 if status == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
