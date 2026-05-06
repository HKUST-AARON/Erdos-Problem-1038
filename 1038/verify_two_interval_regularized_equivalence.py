#!/usr/bin/env python3
"""Diagnostic equivalence checks for the regularized small-eta residual map.

This is not a proof of the singular small-eta theorem.  It checks the concrete
finite-eta consistency conditions that the eventual equivalence lemma must
formalize:

* on solved branch points, the original equations and regularized residual map
  vanish together;
* the regularized residual Jacobian stays nonsingular on those branch points;
* the regularized map has the same local orientation sign as the original
  rescaled equations on the checked finite-eta rows.
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


def parse_epsilons(raw: str) -> list[float]:
    return [float(part) for part in raw.split(",") if part.strip()]


def arb_mid(raw: str) -> float:
    return float(arb(raw).mid())


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
    K1 = arb_mid(
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
    )
    K2 = arb_mid(
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
    )
    return np.asarray([K1, K2], dtype=float)


def regularized_residual_arb(
    solver: Any,
    A: float,
    alpha: float,
    eta: float,
    limit_A: float,
    limit_alpha: float,
    left_weight: float,
    precision: int,
) -> tuple[arb, arb]:
    base_delta_alpha = (alpha - limit_alpha) / eta
    base_delta_A = (A - limit_A) / eta
    arb_eta = arb(repr(float(eta)))
    K1 = arb(
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
    )
    K2 = arb(
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
    )
    return K1, K2


def finite_difference_jacobian(fn: Any, z: np.ndarray, h: float) -> np.ndarray:
    columns = []
    for index in range(2):
        step = np.zeros(2)
        step[index] = h
        columns.append((fn(z + step) - fn(z - step)) / (2.0 * h))
    return np.column_stack(columns)


def arb_fd_jacobian_det(
    solver: Any,
    z: np.ndarray,
    eta: float,
    limit_A: float,
    limit_alpha: float,
    left_weight: float,
    precision: int,
    h: float,
) -> arb:
    h_box = arb(repr(float(h)))

    def value(point: np.ndarray) -> tuple[arb, arb]:
        return regularized_residual_arb(
            solver,
            float(point[0]),
            float(point[1]),
            eta,
            limit_A,
            limit_alpha,
            left_weight,
            precision,
        )

    step_A = np.asarray([h, 0.0], dtype=float)
    step_alpha = np.asarray([0.0, h], dtype=float)
    plus_A = value(z + step_A)
    minus_A = value(z - step_A)
    plus_alpha = value(z + step_alpha)
    minus_alpha = value(z - step_alpha)
    dA = ((plus_A[0] - minus_A[0]) / (2 * h_box), (plus_A[1] - minus_A[1]) / (2 * h_box))
    dAlpha = (
        (plus_alpha[0] - minus_alpha[0]) / (2 * h_box),
        (plus_alpha[1] - minus_alpha[1]) / (2 * h_box),
    )
    return dA[0] * dAlpha[1] - dAlpha[0] * dA[1]


def arb_abs_lower(value: arb) -> float:
    lower = float(value.lower())
    upper = float(value.upper())
    if lower <= 0.0 <= upper:
        return 0.0
    return min(abs(lower), abs(upper))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--epsilons", default="1e-8,3e-8,1e-7,3e-7,1e-6,3e-6,1e-5")
    parser.add_argument("--precision", type=int, default=192)
    parser.add_argument("--residual-tol", type=float, default=1.0e-6)
    parser.add_argument("--det-tol", type=float, default=1.0e-6)
    parser.add_argument("--fd-step", type=float, default=1.0e-6)
    parser.add_argument(
        "--arb-fd-det",
        action="store_true",
        help="Also check an Arb finite-difference determinant box for the regularized residual map.",
    )
    args = parser.parse_args()

    solver = load_solver()
    limit = solver.solve_limit()
    left_weight, null_slope, _forcing_ratios, _curvature, amplitude_alpha, amplitude_A = solver.fold_diagnostics()

    worst_original = 0.0
    worst_regularized = 0.0
    min_abs_det_original = float("inf")
    min_abs_det_regularized = float("inf")
    max_condition_regularized = 0.0
    orientation_mismatches = 0
    min_arb_fd_det_abs_lower = float("inf")
    arb_fd_det_contains_zero = 0
    rows = 0
    guess = (limit.A + amplitude_A * math.sqrt(1.0e-8), limit.alpha + amplitude_alpha * math.sqrt(1.0e-8))

    for epsilon in parse_epsilons(args.epsilons):
        eta = math.sqrt(epsilon)
        try:
            solution, guess = solver.solve_one(epsilon, guess)
        except Exception as exc:  # noqa: BLE001 - diagnostic reports the exact failed row.
            print(f"epsilon={epsilon:.6e} FAIL solve_one {type(exc).__name__}: {exc}")
            return 1

        z = np.asarray([solution.A, solution.alpha], dtype=float)
        original = np.asarray(solver.equations(z, epsilon), dtype=float)
        raw_K = np.asarray(
            [
                original[0] / eta,
                (float(left_weight) * original[0] + original[1]) / (eta * eta),
            ],
            dtype=float,
        )
        regularized = regularized_residual(
            solver,
            solution.A,
            solution.alpha,
            eta,
            limit.A,
            limit.alpha,
            float(left_weight),
            args.precision,
        )

        def original_rescaled(point: np.ndarray) -> np.ndarray:
            value = np.asarray(solver.equations(point, epsilon), dtype=float)
            return np.asarray([value[0] / eta, (float(left_weight) * value[0] + value[1]) / (eta * eta)])

        def regularized_map(point: np.ndarray) -> np.ndarray:
            return regularized_residual(
                solver,
                float(point[0]),
                float(point[1]),
                eta,
                limit.A,
                limit.alpha,
                float(left_weight),
                args.precision,
            )

        J_original = finite_difference_jacobian(original_rescaled, z, args.fd_step)
        J_regularized = finite_difference_jacobian(regularized_map, z, args.fd_step)
        det_original = float(np.linalg.det(J_original))
        det_regularized = float(np.linalg.det(J_regularized))
        condition_regularized = float(np.linalg.cond(J_regularized))
        arb_det = None
        if args.arb_fd_det:
            arb_det = arb_fd_jacobian_det(
                solver,
                z,
                eta,
                limit.A,
                limit.alpha,
                float(left_weight),
                args.precision,
                args.fd_step,
            )
            det_abs_lower = arb_abs_lower(arb_det)
            min_arb_fd_det_abs_lower = min(min_arb_fd_det_abs_lower, det_abs_lower)
            if det_abs_lower <= 0.0:
                arb_fd_det_contains_zero += 1

        original_norm = float(np.linalg.norm(raw_K, ord=np.inf))
        regularized_norm = float(np.linalg.norm(regularized, ord=np.inf))
        worst_original = max(worst_original, original_norm)
        worst_regularized = max(worst_regularized, regularized_norm)
        min_abs_det_original = min(min_abs_det_original, abs(det_original))
        min_abs_det_regularized = min(min_abs_det_regularized, abs(det_regularized))
        max_condition_regularized = max(max_condition_regularized, condition_regularized)
        if det_original == 0.0 or det_regularized == 0.0 or math.copysign(1.0, det_original) != math.copysign(1.0, det_regularized):
            orientation_mismatches += 1

        extra = ""
        if arb_det is not None:
            extra = f" arb_fd_det={arb_det} arb_fd_det_abs_lower={arb_abs_lower(arb_det):.6e}"
        print(
            f"epsilon={epsilon:.6e} original_inf={original_norm:.6e} "
            f"regularized_inf={regularized_norm:.6e} det_original={det_original:.6e} "
            f"det_regularized={det_regularized:.6e} cond_regularized={condition_regularized:.6e}{extra}"
        )
        rows += 1

    ok = (
        rows > 0
        and worst_original <= args.residual_tol
        and worst_regularized <= args.residual_tol
        and min_abs_det_original >= args.det_tol
        and min_abs_det_regularized >= args.det_tol
        and orientation_mismatches == 0
        and (not args.arb_fd_det or arb_fd_det_contains_zero == 0)
    )
    arb_summary = ""
    if args.arb_fd_det:
        arb_summary = (
            f" min_arb_fd_det_abs_lower={min_arb_fd_det_abs_lower:.6e} "
            f"arb_fd_det_contains_zero={arb_fd_det_contains_zero}"
        )
    print(
        "TWO-INTERVAL REGULARIZED EQUIVALENCE: "
        f"{'PASS-DIAGNOSTIC' if ok else 'FAIL-DIAGNOSTIC'} rows={rows} "
        f"worst_original={worst_original:.6e} worst_regularized={worst_regularized:.6e} "
        f"min_abs_det_original={min_abs_det_original:.6e} "
        f"min_abs_det_regularized={min_abs_det_regularized:.6e} "
        f"max_condition_regularized={max_condition_regularized:.6e} "
        f"orientation_mismatches={orientation_mismatches}{arb_summary}"
    )
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
