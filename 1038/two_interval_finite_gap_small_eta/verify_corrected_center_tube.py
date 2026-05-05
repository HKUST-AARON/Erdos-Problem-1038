#!/usr/bin/env python3
"""Diagnostic corrected-center tube for the regularized tiny-eta branch.

The canonical small-eta regularized residual is not exactly zero on the
positive-eta branch solved for the raw equations.  This checker applies the
local Newton correction measured by ``verify_two_interval_regularized_defect_scale.py``
and then samples a small boundary tube around the corrected center.

Status: diagnostic.  It is a bridge artifact toward a proof-grade
Newton-Krawczyk or boundary-degree certificate for ``0 < epsilon < 1e-8``.
It uses double-precision branch centers, finite-difference Jacobians, and
sampled boundary winding.
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
SOLVER_PATH = ROOT / "solve_two_interval_finite_gap.py"
TUBE_VERIFIER_PATH = ROOT / "verify_two_interval_continuation_tube.py"


def load_solver() -> Any:
    spec = importlib.util.spec_from_file_location("solve_two_interval_finite_gap", SOLVER_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import solver from {SOLVER_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def load_tube_verifier() -> Any:
    spec = importlib.util.spec_from_file_location("verify_two_interval_continuation_tube", TUBE_VERIFIER_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import tube verifier from {TUBE_VERIFIER_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def parse_epsilons(raw: str) -> list[float]:
    epsilons = [float(part) for part in raw.split(",") if part.strip()]
    if not epsilons:
        raise argparse.ArgumentTypeError("expected at least one epsilon")
    if any(epsilon <= 0.0 for epsilon in epsilons):
        raise argparse.ArgumentTypeError("epsilons must be positive")
    return epsilons


def regularized_residual(
    solver: Any,
    A: float,
    alpha: float,
    eta: float,
    limit_A: float,
    limit_alpha: float,
    left_weight: float,
    precision: int,
) -> np.ndarray:
    base_delta_alpha = (alpha - limit_alpha) / eta
    base_delta_A = (A - limit_A) / eta
    arb_eta = arb(repr(float(eta)))
    K1 = float(
        arb(
            solver._potential_residue_log_value_divided_from_arb(
                arb(repr(float(A))),
                arb(repr(float(alpha))),
                arb_eta,
                arb(repr(float(limit_A))),
                arb(repr(float(limit_alpha))),
                "contact",
                precision,
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
                arb(repr(float(limit_A))),
                arb(repr(float(limit_alpha))),
                precision,
                arb(repr(float(base_delta_A))),
                arb(repr(float(base_delta_alpha))),
                regularize_joint_limit_layer=True,
            )
        ).mid()
    )
    return np.asarray([K1, K2], dtype=float)


def finite_difference_jacobian(fn: Any, z: np.ndarray, h: float) -> np.ndarray:
    columns = []
    for index in range(2):
        step = np.zeros(2)
        step[index] = h
        columns.append((fn(z + step) - fn(z - step)) / (2.0 * h))
    return np.column_stack(columns)


def boundary_points(center: np.ndarray, radii: np.ndarray, edge_samples: int) -> np.ndarray:
    if edge_samples < 4:
        raise argparse.ArgumentTypeError("edge-samples must be at least 4")
    points: list[tuple[float, float]] = []
    cB, cTau = float(center[0]), float(center[1])
    rB, rTau = float(radii[0]), float(radii[1])
    for index in range(edge_samples):
        t = -1.0 + 2.0 * index / edge_samples
        points.append((cB + rB, cTau + t * rTau))
    for index in range(edge_samples):
        t = 1.0 - 2.0 * index / edge_samples
        points.append((cB + t * rB, cTau + rTau))
    for index in range(edge_samples):
        t = 1.0 - 2.0 * index / edge_samples
        points.append((cB - rB, cTau + t * rTau))
    for index in range(edge_samples):
        t = -1.0 + 2.0 * index / edge_samples
        points.append((cB + t * rB, cTau - rTau))
    return np.asarray(points, dtype=float)


def winding_degree(values: np.ndarray) -> tuple[int, float, float]:
    if values.shape[0] < 4:
        raise ValueError("need at least four boundary values")
    norms = np.linalg.norm(values, axis=1)
    min_norm = float(np.min(norms))
    z = values[:, 0] + 1j * values[:, 1]
    z_next = np.roll(z, -1)
    increments = np.angle(z_next / z)
    total_turn = float(np.sum(increments))
    jumps = np.abs(increments)
    degree = int(round(total_turn / (2.0 * math.pi)))
    return degree, min_norm, float(np.max(jumps))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--epsilons", default="1e-8,3e-8,1e-7,3e-7,1e-6,3e-6,1e-5")
    parser.add_argument("--precision", type=int, default=192)
    parser.add_argument("--fd-step", type=float, default=1.0e-6)
    parser.add_argument("--tube-radius-B", type=float, default=1.0e-3)
    parser.add_argument("--tube-radius-tau", type=float, default=1.0e-3)
    parser.add_argument("--edge-samples", type=int, default=64)
    parser.add_argument("--max-correction", type=float, default=1.0e-3)
    parser.add_argument("--max-corrected-residual", type=float, default=1.0e-6)
    parser.add_argument("--min-boundary-norm", type=float, default=1.0e-4)
    parser.add_argument(
        "--center-mode",
        choices=("raw-corrected", "limiting"),
        default="raw-corrected",
        help="Use Newton-corrected raw branch centers, or the eta=0 limiting center B=0,tau=tau0.",
    )
    parser.add_argument(
        "--interval-boundary-winding",
        default=None,
        help=(
            "Optional proof-grade interval boundary winding on adjacent corrected-center slabs, "
            "formatted eta_subdivisions,edge_boxes."
        ),
    )
    parser.add_argument("--interval-boundary-winding-adaptive-depth", type=int, default=1)
    args = parser.parse_args()

    epsilons = parse_epsilons(args.epsilons)
    if args.tube_radius_B <= 0.0 or args.tube_radius_tau <= 0.0:
        parser.error("tube radii must be positive")

    solver = load_solver()
    limit = solver.solve_limit()
    left_weight, null_slope, _forcing_ratios, _curvature, tau0, amplitude_A = solver.fold_diagnostics()
    amplitude_alpha = tau0
    guess = (limit.A + amplitude_A * math.sqrt(min(epsilons)), limit.alpha + amplitude_alpha * math.sqrt(min(epsilons)))
    radii = np.asarray([args.tube_radius_B, args.tube_radius_tau], dtype=float)

    worst_correction = 0.0
    worst_corrected_residual = 0.0
    worst_abs_degree_error = 0
    min_boundary_norm = float("inf")
    max_angle_jump = 0.0
    corrected_rows: list[tuple[float, float, float]] = []

    for epsilon in epsilons:
        eta = math.sqrt(epsilon)
        if args.center_mode == "limiting":
            B = 0.0
            tau = float(tau0)
        else:
            solution, guess = solver.solve_one(epsilon, guess)
            B = (solution.A - limit.A) / eta - float(null_slope) * ((solution.alpha - limit.alpha) / eta)
            tau = (solution.alpha - limit.alpha) / eta

        def map_in_fold(point: np.ndarray) -> np.ndarray:
            Bp, taup = float(point[0]), float(point[1])
            A = limit.A + eta * (float(null_slope) * taup + Bp)
            alpha = limit.alpha + eta * taup
            return regularized_residual(
                solver,
                A,
                alpha,
                eta,
                limit.A,
                limit.alpha,
                float(left_weight),
                args.precision,
            )

        raw_center = np.asarray([B, tau], dtype=float)
        raw_defect = map_in_fold(raw_center)
        if args.center_mode == "limiting":
            correction = np.zeros(2)
        else:
            jacobian = finite_difference_jacobian(map_in_fold, raw_center, args.fd_step)
            correction = -np.linalg.solve(jacobian, raw_defect)
        corrected_center = raw_center + correction
        corrected_residual = map_in_fold(corrected_center)
        boundary = boundary_points(corrected_center, radii, args.edge_samples)
        boundary_values = np.asarray([map_in_fold(point) for point in boundary], dtype=float)
        degree, boundary_norm, angle_jump = winding_degree(boundary_values)

        correction_norm = float(np.linalg.norm(correction, ord=np.inf))
        corrected_norm = float(np.linalg.norm(corrected_residual, ord=np.inf))
        worst_correction = max(worst_correction, correction_norm)
        worst_corrected_residual = max(worst_corrected_residual, corrected_norm)
        worst_abs_degree_error = max(worst_abs_degree_error, abs(abs(degree) - 1))
        min_boundary_norm = min(min_boundary_norm, boundary_norm)
        max_angle_jump = max(max_angle_jump, angle_jump)
        corrected_rows.append((epsilon, float(corrected_center[0]), float(corrected_center[1])))

        print(
            f"epsilon={epsilon:.6e} eta={eta:.6e} "
            f"raw_center=({raw_center[0]:.6e},{raw_center[1]:.6e}) "
            f"correction=({correction[0]:.6e},{correction[1]:.6e}) "
            f"correction_inf={correction_norm:.6e} corrected_inf={corrected_norm:.6e} "
            f"degree={degree:d} boundary_min_norm={boundary_norm:.6e} "
            f"max_angle_jump={angle_jump:.6e}"
        )

    interval_winding_min_origin = float("inf")
    interval_winding_max_angle = 0.0
    interval_winding_checked = 0
    interval_winding_ok = True
    if args.interval_boundary_winding is not None:
        parts = args.interval_boundary_winding.split(",")
        if len(parts) != 2:
            parser.error("--interval-boundary-winding expects eta_subdivisions,edge_boxes")
        eta_subdivisions = int(parts[0])
        edge_boxes = int(parts[1])
        if eta_subdivisions <= 0 or edge_boxes <= 0:
            parser.error("--interval-boundary-winding values must be positive")
        tube = load_tube_verifier()
        endpoint_rows = [
            tube.v.EndpointRow(index=index, epsilon=epsilon, B=B, tau=tau)
            for index, (epsilon, B, tau) in enumerate(corrected_rows)
        ]
        for low_row, high_row in zip(endpoint_rows, endpoint_rows[1:]):
            try:
                (
                    winding_status,
                    winding_degree_abs,
                    winding_min_origin,
                    winding_max_angle,
                    winding_source,
                ) = tube.interval_boundary_winding(
                    low_row,
                    high_row,
                    radii,
                    limit,
                    float(left_weight),
                    float(null_slope),
                    eta_subdivisions,
                    edge_boxes,
                    "residue-log-mv",
                    0,
                    args.interval_boundary_winding_adaptive_depth,
                    None,
                    True,
                )
            except tube.v.VerificationError as exc:
                winding_status = "FAIL"
                winding_degree_abs = 0
                winding_min_origin = 0.0
                winding_max_angle = 0.0
                winding_source = str(exc)
            if winding_status not in {"PASS", "proof"} or winding_degree_abs != 1:
                print(
                    f"interval slab {low_row.epsilon:.6e}:{high_row.epsilon:.6e}: "
                    f"status={winding_status} degree_abs={winding_degree_abs} "
                    f"min_origin={winding_min_origin:.6e} max_angle={winding_max_angle:.6e} "
                    f"source={winding_source}"
                )
                interval_winding_ok = False
            interval_winding_checked += 1
            interval_winding_min_origin = min(interval_winding_min_origin, winding_min_origin)
            interval_winding_max_angle = max(interval_winding_max_angle, winding_max_angle)
            print(
                f"interval slab {low_row.epsilon:.6e}:{high_row.epsilon:.6e}: "
                f"status={winding_status} degree_abs={winding_degree_abs} "
                f"min_origin={winding_min_origin:.6e} max_angle={winding_max_angle:.6e}"
            )

    ok = (
        worst_correction <= args.max_correction
        and worst_corrected_residual <= args.max_corrected_residual
        and worst_abs_degree_error == 0
        and min_boundary_norm >= args.min_boundary_norm
        and interval_winding_ok
    )
    if args.interval_boundary_winding is not None and interval_winding_checked != max(0, len(corrected_rows) - 1):
        ok = False
    print(
        "TWO-INTERVAL CORRECTED-CENTER TUBE: "
        f"{'PASS-DIAGNOSTIC' if ok else 'FAIL-DIAGNOSTIC'} rows={len(epsilons)} "
        f"worst_correction={worst_correction:.6e} "
        f"worst_corrected_residual={worst_corrected_residual:.6e} "
        f"min_boundary_norm={min_boundary_norm:.6e} "
        f"max_angle_jump={max_angle_jump:.6e} "
        f"interval_winding_checked={interval_winding_checked:d} "
        f"interval_winding_min_origin={interval_winding_min_origin:.6e} "
        f"interval_winding_max_angle={interval_winding_max_angle:.6e}"
    )
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
