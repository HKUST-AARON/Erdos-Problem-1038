#!/usr/bin/env python3
"""Diagnose where the K1 first-divided interval kernel loses conditioning."""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path
from typing import Any

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
    solver = load_solver()
    limit = solver.solve_limit()
    _left_weight, null_slope, _forcing_ratios, _curvature, tau0, _amp_A = solver.fold_diagnostics()
    probes = [(1e-16, 1e-8), (1e-12, 1e-8), (1e-10, 1e-8), (1e-9, 1e-8), (5e-9, 1e-8)]
    worst_radius = 0.0
    best_radius = float("inf")
    for eta_low, eta_high in probes:
        eta = solver._arb_interval_from_bounds(eta_low, eta_high)
        B = 0.0
        tau = float(tau0) + 0.05
        base_delta_A = arb(repr(float(null_slope * tau + B)))
        base_delta_alpha = arb(repr(float(tau)))
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
                192,
                base_delta_A,
                base_delta_alpha,
            )
        )
        radius = float(K1.rad())
        worst_radius = max(worst_radius, radius)
        best_radius = min(best_radius, radius)
        print(f"eta=[{eta_low:.0e},{eta_high:.0e}] K1={K1} K1_radius={radius:.6e}")

    ratio = worst_radius / best_radius if best_radius > 0.0 else float("inf")
    status = "FAIL-DIAGNOSTIC" if ratio > 1.0e5 else "PASS-DIAGNOSTIC"
    conclusion = (
        "K1 eta floor remains unresolved"
        if status == "FAIL-DIAGNOSTIC"
        else "K1 endpoint-safe first-divided kernel controls eta floor"
    )
    print(
        "TWO-INTERVAL K1 ETA FLOOR: "
        f"{status} worst_radius={worst_radius:.6e} best_radius={best_radius:.6e} "
        f"radius_ratio={ratio:.6e} conclusion={conclusion!r}"
    )
    return 0 if status == "PASS-DIAGNOSTIC" else 1


if __name__ == "__main__":
    raise SystemExit(main())
