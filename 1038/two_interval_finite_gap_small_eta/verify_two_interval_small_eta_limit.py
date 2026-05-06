#!/usr/bin/env python3
"""Limiting winding certificate for the small-eta two-interval branch.

This is the eta=0 target for the remaining small-eta theorem.  The fold
normal form gives

    K0(B,tau) = (J00 * B, forcing + curvature * tau^2),

where ``J00 > 0``, ``forcing > 0``, and ``curvature < 0`` are computed from the
epsilon=0 limiting system.  On a rectangle around the positive root

    tau0 = sqrt(-forcing / curvature),

the boundary has winding degree 1 as long as the bottom edge has K0_2 > 0 and
the top edge has K0_2 < 0.  This verifies the limiting branch target; a
separate remainder theorem is still needed to transfer it to all sufficiently
small positive eta.
"""

from __future__ import annotations

import argparse
import importlib.util
import math
import sys
from pathlib import Path
from typing import Any

import numpy as np


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


def boundary_degree(points: list[complex]) -> tuple[int, float, float]:
    angles = np.unwrap(np.angle(np.asarray(points + [points[0]], dtype=complex)))
    total = float(angles[-1] - angles[0])
    degree = int(round(total / (2.0 * math.pi)))
    min_norm = min(abs(point) for point in points)
    max_jump = max(abs(float(angles[index + 1] - angles[index])) for index in range(len(angles) - 1))
    return degree, min_norm, max_jump


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--radius-B", type=float, default=0.01)
    parser.add_argument("--radius-tau", type=float, default=0.05)
    parser.add_argument("--edge-samples", type=int, default=64)
    args = parser.parse_args()

    if args.radius_B <= 0 or args.radius_tau <= 0 or args.edge_samples < 4:
        raise SystemExit("positive radii and at least 4 edge samples are required")

    solver = load_solver()
    limit_solution = solver.solve_limit()
    left_weight, null_slope, forcing_ratios, curvature, tau0, _amp_A = solver.fold_diagnostics()
    jacobian = solver.limit_jacobian()
    j00 = float(jacobian[0, 0])
    forcing = float(forcing_ratios[-1][1])
    curvature = float(curvature)
    tau0 = float(tau0)

    tau_low = tau0 - args.radius_tau
    tau_high = tau0 + args.radius_tau
    if not (j00 > 0.0 and forcing > 0.0 and curvature < 0.0 and tau_low > 0.0):
        raise SystemExit("fold constants do not satisfy the expected signs")

    bottom_k2 = forcing + curvature * tau_low * tau_low
    top_k2 = forcing + curvature * tau_high * tau_high
    if bottom_k2 <= 0.0 or top_k2 >= 0.0:
        raise SystemExit(
            "rectangle does not separate the positive limiting root: "
            f"bottom_k2={bottom_k2:.6e} top_k2={top_k2:.6e}"
        )

    def K0(B: float, tau: float) -> complex:
        return complex(j00 * B, forcing + curvature * tau * tau)

    boundary: list[complex] = []
    for index in range(args.edge_samples):
        t = -1.0 + 2.0 * index / args.edge_samples
        boundary.append(K0(args.radius_B, tau0 + t * args.radius_tau))
    for index in range(args.edge_samples):
        t = 1.0 - 2.0 * index / args.edge_samples
        boundary.append(K0(t * args.radius_B, tau0 + args.radius_tau))
    for index in range(args.edge_samples):
        t = 1.0 - 2.0 * index / args.edge_samples
        boundary.append(K0(-args.radius_B, tau0 + t * args.radius_tau))
    for index in range(args.edge_samples):
        t = -1.0 + 2.0 * index / args.edge_samples
        boundary.append(K0(t * args.radius_B, tau0 - args.radius_tau))

    degree, min_norm, max_jump = boundary_degree(boundary)
    if abs(degree) != 1:
        raise SystemExit(f"unexpected limiting winding degree {degree}")

    structural_margins = {
        "A>1": limit_solution.A - 1.0,
        "A<-ell": -solver.X_LEFT - (limit_solution.A + args.radius_B),
        "ell<-1": -1.0 - solver.X_LEFT,
        "r<alpha": limit_solution.alpha - solver.X_RIGHT,
        "alpha<1": 1.0 - limit_solution.alpha,
    }

    print(
        "TWO-INTERVAL SMALL-ETA LIMIT: PASS "
        f"degree_abs={abs(degree)} min_origin={min_norm:.6e} max_angle={max_jump:.6e} "
        f"j00={j00:.12e} forcing={forcing:.12e} curvature={curvature:.12e} "
        f"tau0={tau0:.12e} bottom_k2={bottom_k2:.12e} top_k2={top_k2:.12e} "
        f"limit_A={limit_solution.A:.12e} limit_alpha={limit_solution.alpha:.12e} "
        f"left_weight={float(left_weight):.12e} null_slope={float(null_slope):.12e} "
        f"min_structural_margin={min(structural_margins.values()):.6e}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
