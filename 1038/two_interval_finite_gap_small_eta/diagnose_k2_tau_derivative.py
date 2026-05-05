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
    parser.add_argument("--h", type=float, default=1.0e-4)
    parser.add_argument("--eta-values", default="1e-16,1e-12,1e-8")
    parser.add_argument("--candidate-lipschitz", type=float, default=2.0e-4)
    parser.add_argument("--candidate-curvature", type=float, default=2.5e-4)
    parser.add_argument(
        "--secant-certificate",
        action="store_true",
        help="also enclose eta-uniform cell secant slopes with endpoint Arb eta variation",
    )
    parser.add_argument(
        "--taylor-lipschitz-diagnostic",
        action="store_true",
        help="combine eta-uniform cell secants with the candidate curvature allowance",
    )
    parser.add_argument(
        "--cell-curvature-scan",
        action="store_true",
        help="scan the two tau cells on each B edge for finite-difference curvature stress",
    )
    parser.add_argument("--cell-grid", type=int, default=101)
    parser.add_argument(
        "--interval-curvature-box-test",
        action="store_true",
        help="try direct Arb second-difference boxes on the four K2 edge cells",
    )
    parser.add_argument("--interval-subboxes", type=int, default=8)
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

    def k2_eta_variation_abs_upper(B: float, tau: float, eta_low: float, eta_high: float) -> float:
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

    def k2_box(B: float, tau_box: Any, eta_box: Any) -> Any:
        base_delta_A = arb(repr(float(null_slope))) * tau_box + arb(repr(float(B)))
        base_delta_alpha = tau_box
        A = arb(repr(float(limit.A))) + eta_box * base_delta_A
        alpha = arb(repr(float(limit.alpha))) + eta_box * base_delta_alpha
        return arb(
            solver._combined_residue_log_value_second_divided_from_arb(
                A,
                alpha,
                eta_box,
                arb(repr(float(left_weight))),
                arb(repr(float(limit.A))),
                arb(repr(float(limit.alpha))),
                192,
                base_delta_A,
                base_delta_alpha,
                regularize_joint_limit_layer=True,
            )
        )

    def k0_2_box(B: float, tau_box: Any) -> Any:
        qB = arb(repr(float(B)))
        return (
            arb(repr(float(forcing)))
            + arb(repr(float(q20))) * qB * qB
            + arb(repr(float(q11))) * qB * tau_box
            + arb(repr(float(q02))) * tau_box * tau_box
        )

    def remainder_box(B: float, tau_box: Any, eta_box: Any) -> Any:
        return k2_box(B, tau_box, eta_box) - k0_2_box(B, tau_box)

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

    if args.secant_certificate:
        eta_low = min(eta_values)
        eta_high = max(eta_values)
        eta_mid = 0.5 * (eta_low + eta_high)
        step = 0.1 / (args.grid - 1)
        worst_secant = 0.0
        worst_secant_source = ""
        for B in (0.01, -0.01):
            for index in range(args.grid - 1):
                tau_left = tau0 - 0.05 + step * index
                tau_right = tau_left + step
                left = remainder(B, tau_left, eta_mid)
                right = remainder(B, tau_right, eta_mid)
                left_eta = k2_eta_variation_abs_upper(B, tau_left, eta_low, eta_high)
                right_eta = k2_eta_variation_abs_upper(B, tau_right, eta_low, eta_high)
                secant_bound = (abs(right - left) + left_eta + right_eta) / step
                if secant_bound > worst_secant:
                    worst_secant = secant_bound
                    worst_secant_source = (
                        f"B={B:+.2f},index={index},tau_left={tau_left:.12e},"
                        f"tau_right={tau_right:.12e},left_eta={left_eta:.6e},right_eta={right_eta:.6e}"
                    )
        secant_status = "PASS-DIAGNOSTIC" if worst_secant < args.candidate_lipschitz else "FAIL-DIAGNOSTIC"
        print(
            "TWO-INTERVAL K2 ETA-UNIFORM SECANTS: "
            f"{secant_status} grid={args.grid:d} eta_low={eta_low:.6e} eta_high={eta_high:.6e} "
            f"worst_secant_bound={worst_secant:.6e} candidate_lipschitz={args.candidate_lipschitz:.6e} "
            f"worst_source={worst_secant_source!r}"
        )
        if secant_status != "PASS-DIAGNOSTIC":
            status = "FAIL-DIAGNOSTIC"
        if args.taylor_lipschitz_diagnostic:
            curvature_allowance = 0.5 * args.candidate_curvature * step
            taylor_bound = worst_secant + curvature_allowance
            taylor_status = "PASS-DIAGNOSTIC" if taylor_bound < args.candidate_lipschitz else "FAIL-DIAGNOSTIC"
            print(
                "TWO-INTERVAL K2 TAYLOR LIPSCHITZ: "
                f"{taylor_status} grid={args.grid:d} step={step:.6e} "
                f"worst_secant_bound={worst_secant:.6e} "
                f"candidate_curvature={args.candidate_curvature:.6e} "
                f"curvature_allowance={curvature_allowance:.6e} "
                f"taylor_lipschitz_bound={taylor_bound:.6e} "
                f"candidate_lipschitz={args.candidate_lipschitz:.6e}"
            )
            if taylor_status != "PASS-DIAGNOSTIC":
                status = "FAIL-DIAGNOSTIC"
    if args.cell_curvature_scan:
        if args.cell_grid < 3:
            raise SystemExit("cell-grid must be at least 3")
        cell_step = 0.05
        scan_worst = 0.0
        scan_source = ""
        for B in (0.01, -0.01):
            for cell in range(2):
                tau_low = tau0 - 0.05 + cell_step * cell
                tau_high = tau_low + cell_step
                cell_worst = 0.0
                cell_source = ""
                for eta in eta_values:
                    for tau in np.linspace(tau_low + args.h, tau_high - args.h, args.cell_grid):
                        curvature = (
                            remainder(B, float(tau + args.h), eta)
                            - 2 * remainder(B, float(tau), eta)
                            + remainder(B, float(tau - args.h), eta)
                        ) / (args.h * args.h)
                        abs_curvature = abs(curvature)
                        if abs_curvature > cell_worst:
                            cell_worst = abs_curvature
                            cell_source = f"eta={eta:.1e},tau={float(tau):.12e},curvature={curvature:.6e}"
                        if abs_curvature > scan_worst:
                            scan_worst = abs_curvature
                            scan_source = f"B={B:+.2f},cell={cell},{cell_source}"
                print(
                    f"K2_CELL_CURVATURE B={B:+.2f} cell={cell:d} "
                    f"tau_low={tau_low:.12e} tau_high={tau_high:.12e} "
                    f"max_abs_curvature={cell_worst:.6e} source={cell_source!r}"
                )
        scan_status = "PASS-DIAGNOSTIC" if scan_worst < args.candidate_curvature else "FAIL-DIAGNOSTIC"
        print(
            "TWO-INTERVAL K2 CELL CURVATURE SCAN: "
            f"{scan_status} cell_grid={args.cell_grid:d} h={args.h:.6e} "
            f"worst_curvature={scan_worst:.6e} candidate_curvature={args.candidate_curvature:.6e} "
            f"worst_source={scan_source!r}"
        )
        if scan_status != "PASS-DIAGNOSTIC":
            status = "FAIL-DIAGNOSTIC"
    if args.interval_curvature_box_test:
        if args.interval_subboxes <= 0:
            raise SystemExit("interval-subboxes must be positive")
        eta_box = solver._arb_interval_from_bounds(min(eta_values), max(eta_values))
        h_box = arb(repr(float(args.h)))
        interval_worst = 0.0
        interval_source = ""
        failures = 0
        cell_step = 0.05
        for B in (0.01, -0.01):
            for cell in range(2):
                tau_low = tau0 - 0.05 + cell_step * cell
                tau_high = tau_low + cell_step
                usable_low = tau_low + args.h
                usable_high = tau_high - args.h
                cell_worst = 0.0
                for subbox in range(args.interval_subboxes):
                    low = usable_low + (usable_high - usable_low) * subbox / args.interval_subboxes
                    high = usable_low + (usable_high - usable_low) * (subbox + 1) / args.interval_subboxes
                    tau_box = solver._arb_interval_from_bounds(low, high)
                    try:
                        curvature = (
                            remainder_box(B, tau_box + h_box, eta_box)
                            - 2 * remainder_box(B, tau_box, eta_box)
                            + remainder_box(B, tau_box - h_box, eta_box)
                        ) / (h_box * h_box)
                    except Exception as exc:  # noqa: BLE001
                        failures += 1
                        if not interval_source:
                            interval_source = f"B={B:+.2f},cell={cell},subbox={subbox},{type(exc).__name__}:{exc}"
                        continue
                    bound = float(abs(curvature).upper())
                    cell_worst = max(cell_worst, bound)
                    if bound > interval_worst:
                        interval_worst = bound
                        interval_source = (
                            f"B={B:+.2f},cell={cell},subbox={subbox},"
                            f"tau=[{low:.12e},{high:.12e}],curvature={curvature}"
                        )
                print(
                    f"K2_INTERVAL_CURVATURE_BOX B={B:+.2f} cell={cell:d} "
                    f"subboxes={args.interval_subboxes:d} worst_bound={cell_worst:.6e}"
                )
        interval_status = (
            "PASS-DIAGNOSTIC"
            if failures == 0 and interval_worst < args.candidate_curvature
            else "FAIL-DIAGNOSTIC"
        )
        print(
            "TWO-INTERVAL K2 INTERVAL CURVATURE BOX TEST: "
            f"{interval_status} subboxes={args.interval_subboxes:d} h={args.h:.6e} "
            f"worst_bound={interval_worst:.6e} candidate_curvature={args.candidate_curvature:.6e} "
            f"failures={failures:d} worst_source={interval_source!r}"
        )
    return 0 if status == "PASS-DIAGNOSTIC" else 1


if __name__ == "__main__":
    raise SystemExit(main())
