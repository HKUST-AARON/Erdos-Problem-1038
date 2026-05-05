#!/usr/bin/env python3
"""Component diagnostic for the endpoint interval remainder kernel.

This probes the current Arb interval value kernels on the limiting rectangle
boundary.  It is meant to identify which residual component blocks a uniform
``K_eta - K0`` remainder proof near eta=0.
"""

from __future__ import annotations

import argparse
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
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--eta-low", type=float, default=1.0e-16)
    parser.add_argument("--eta-high", type=float, default=1.0e-8)
    parser.add_argument("--precision", type=int, default=192)
    args = parser.parse_args()

    if not (0.0 < args.eta_low <= args.eta_high):
        raise SystemExit("expected 0 < eta-low <= eta-high")

    solver = load_solver()
    limit = solver.solve_limit()
    left_weight, null_slope, _forcing_ratios, _curvature, tau0, _amp_A = solver.fold_diagnostics()
    eta = solver._arb_interval_from_bounds(args.eta_low, args.eta_high)

    probes = [
        ("top-mid", 0.0, float(tau0) + 0.05),
        ("right-mid", 0.01, float(tau0)),
        ("bottom-mid", 0.0, float(tau0) - 0.05),
        ("left-mid", -0.01, float(tau0)),
    ]

    worst_k1_radius = 0.0
    worst_k2_radius = 0.0
    failures = 0
    for label, B, tau in probes:
        base_delta_A = arb(repr(float(null_slope * tau + B)))
        base_delta_alpha = arb(repr(float(tau)))
        A = arb(repr(float(limit.A))) + eta * base_delta_A
        alpha = arb(repr(float(limit.alpha))) + eta * base_delta_alpha
        try:
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
        except Exception as exc:  # noqa: BLE001
            failures += 1
            print(f"{label}: FAIL {type(exc).__name__}: {exc}")
            continue
        k1_radius = float(K1.rad())
        k2_radius = float(K2.rad())
        worst_k1_radius = max(worst_k1_radius, k1_radius)
        worst_k2_radius = max(worst_k2_radius, k2_radius)
        print(f"{label}: K1={K1} K1_radius={k1_radius:.6e} K2={K2} K2_radius={k2_radius:.6e}")

    blocker = "K1" if worst_k1_radius > worst_k2_radius else "K2"
    status = "FAIL-DIAGNOSTIC" if failures or worst_k1_radius > 1.0 else "PASS-DIAGNOSTIC"
    print(
        "TWO-INTERVAL INTERVAL REMAINDER COMPONENTS: "
        f"{status} eta_low={args.eta_low:.6e} eta_high={args.eta_high:.6e} "
        f"worst_k1_radius={worst_k1_radius:.6e} worst_k2_radius={worst_k2_radius:.6e} "
        f"blocker={blocker} failures={failures}"
    )
    return 0 if status == "PASS-DIAGNOSTIC" else 1


if __name__ == "__main__":
    raise SystemExit(main())
