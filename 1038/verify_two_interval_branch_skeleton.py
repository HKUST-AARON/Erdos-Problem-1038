#!/usr/bin/env python3
"""Verifier for the two-interval finite-gap branch skeleton.

This checks an exported JSON skeleton from ``solve_two_interval_finite_gap.py``.
It deliberately does not rerun the nonlinear root search.  Instead, it treats
the stored rows as finite diagnostic certificate candidates and recomputes:

* extracted atom/density masses and contact residuals;
* Lyapunov-Schmidt ``(B, tau)`` coordinates and rescaled equations;
* analytic ``D_(B,tau) K`` and its finite-difference comparison;
* sampled Krawczyk inclusion/margin data;
* sign-chart margins on both the branch box and local Krawczyk box.

This is still not a proof-grade interval Krawczyk verifier.  Its purpose is to
make the current branch skeleton reproducible and auditable without trusting
the printed output of the generator.
"""

from __future__ import annotations

import argparse
import copy
import importlib.util
import json
import math
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np


ROOT = Path(__file__).resolve().parent
SOLVER_PATH = ROOT / "solve_two_interval_finite_gap.py"

spec = importlib.util.spec_from_file_location("solve_two_interval_finite_gap", SOLVER_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot import solver from {SOLVER_PATH}")
solver = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = solver
spec.loader.exec_module(solver)


@dataclass(frozen=True)
class Thresholds:
    residual: float = 1.0e-8
    mass_total: float = 1.0e-8
    stored_value: float = 5.0e-10
    k_residual: float = 1.0e-8
    analytic_fd_diff: float = 5.0e-8
    determinant_abs: float = 2.5e-1
    krawczyk_margin: float = 9.0e-3
    contraction: float = 2.0e-2
    potential_difference: float = 1.0e-10
    path_separation: float = 9.0e-1
    sign_margin: float = 0.0
    arb_box_uminus_abs: float = 2.0e-3
    arb_box_uminus_derivative_abs: float = 1.0e-2
    arb_box_contact_derivative_abs: float = 1.0e-1


class VerificationError(Exception):
    pass


ARB_CENTER_RE = re.compile(r"^\[\s*(?P<center>[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?)\s+\+/-")


def fail(message: str) -> None:
    raise VerificationError(message)


def assert_close(name: str, actual: float, expected: float, tolerance: float) -> None:
    if not math.isfinite(actual) or not math.isfinite(expected):
        fail(f"{name}: non-finite comparison actual={actual!r}, expected={expected!r}")
    if abs(actual - expected) > tolerance:
        fail(
            f"{name}: actual {actual:.17g} differs from stored "
            f"{expected:.17g} by {abs(actual - expected):.3e} > {tolerance:.3e}"
        )


def arb_ball_center(ball: str) -> float:
    if not isinstance(ball, str):
        fail(f"Arb ball: expected string, got {type(ball).__name__}")
    stripped = ball.strip()
    if stripped.startswith("[+/-") or stripped.startswith("[-/+"):
        return 0.0
    match = ARB_CENTER_RE.match(stripped)
    if match is None:
        fail(f"Arb ball: cannot parse center from {ball!r}")
    return float(match.group("center"))


def assert_arb_center_close(context: str, field: str, actual_ball: str, expected_ball: str) -> None:
    actual = arb_ball_center(actual_ball)
    expected = arb_ball_center(expected_ball)
    tolerance = max(1.0e-12, 1.0e-10 * max(abs(actual), abs(expected)))
    assert_close(f"{context} {field} center", actual, expected, tolerance)


def assert_equal(name: str, actual: Any, expected: Any) -> None:
    if actual != expected:
        fail(f"{name}: actual {actual!r} differs from stored {expected!r}")


def assert_finite_arb_ball(name: str, value: Any) -> None:
    if not hasattr(value, "is_finite") or not value.is_finite():
        fail(f"{name}: expected finite Arb ball, got {value!r}")


def arb_abs_upper(name: str, value: Any) -> float:
    assert_finite_arb_ball(name, value)
    upper = float(abs(value).upper())
    if not math.isfinite(upper):
        fail(f"{name}: non-finite Arb abs upper {upper!r} for {value!r}")
    return upper


def assert_positive_margins(context: str, margins: dict[str, float], threshold: float) -> None:
    for key, value in sorted(margins.items()):
        if value <= threshold:
            fail(f"{context}: margin {key}={value:.6e} <= {threshold:.6e}")


def stored_pair(item: dict[str, Any], key: str) -> tuple[float, float]:
    raw = item[key]
    if not isinstance(raw, list) or len(raw) != 2:
        fail(f"{key}: expected pair list")
    return float(raw[0]), float(raw[1])


def parse_subdivisions(raw: str) -> tuple[int, int]:
    parts = raw.split(",")
    if len(parts) != 2:
        fail(f"--arb-box-dk-subdivisions: expected B,tau pair, got {raw!r}")
    try:
        b_count = int(parts[0])
        tau_count = int(parts[1])
    except ValueError:
        fail(f"--arb-box-dk-subdivisions: expected integer pair, got {raw!r}")
    if b_count <= 0 or tau_count <= 0:
        fail(f"--arb-box-dk-subdivisions: counts must be positive, got {raw!r}")
    return b_count, tau_count


def recompute_row(
    row_index: int,
    row: dict[str, Any],
    payload: dict[str, Any],
    thresholds: Thresholds,
    arb_primitive_check: bool,
    arb_center_residual_check: bool,
    arb_box_uminus_check: bool,
    arb_box_uminus_derivative_check: bool,
    arb_box_contact_derivative_check: bool,
    arb_box_dk_check: bool,
    arb_interval_krawczyk_check: bool,
    arb_box_dk_subdivisions: tuple[int, int],
    verbose: bool,
) -> None:
    epsilon = float(row["epsilon"])
    row_context = f"row={row_index} eps={epsilon:g}"
    eta = math.sqrt(epsilon)
    solution = row["solution"]
    A = float(solution["A"])
    alpha = float(solution["alpha"])

    ell, r, beta, mass_ell, mass_r, mass_one = solver.atoms(A, alpha, epsilon)
    density_mass = solver.continuous_mass(A, alpha, epsilon)
    residual_alpha, residual_minus_one = solver.equations(np.array([A, alpha]), epsilon)
    total_mass = mass_ell + mass_r + mass_one + density_mass

    stored_masses = solution["masses"]
    assert_close(f"eps={epsilon:g} ell", ell, float(solution["ell"]), thresholds.stored_value)
    assert_close(f"eps={epsilon:g} r", r, float(solution["r"]), thresholds.stored_value)
    assert_close(f"eps={epsilon:g} beta", beta, float(solution["beta"]), thresholds.stored_value)
    assert_close(f"eps={epsilon:g} mass_ell", mass_ell, float(stored_masses["ell"]), thresholds.stored_value)
    assert_close(f"eps={epsilon:g} mass_r", mass_r, float(stored_masses["r"]), thresholds.stored_value)
    assert_close(f"eps={epsilon:g} mass_one", mass_one, float(stored_masses["one"]), thresholds.stored_value)
    assert_close(
        f"eps={epsilon:g} density_mass",
        density_mass,
        float(stored_masses["density"]),
        thresholds.stored_value,
    )
    assert_close(f"eps={epsilon:g} total_mass", total_mass, float(stored_masses["total"]), thresholds.stored_value)
    if abs(total_mass - 1.0) > thresholds.mass_total:
        fail(f"eps={epsilon:g}: total mass {total_mass:.17g} is not within {thresholds.mass_total:g} of 1")
    if abs(residual_alpha) > thresholds.residual or abs(residual_minus_one) > thresholds.residual:
        fail(
            f"eps={epsilon:g}: residuals too large "
            f"U_alpha={residual_alpha:.3e}, U_minus_one={residual_minus_one:.3e}"
        )
    stored_residuals = solution["residuals"]
    assert_close(
        f"eps={epsilon:g} U_alpha residual",
        residual_alpha,
        float(stored_residuals["U_alpha"]),
        thresholds.stored_value,
    )
    assert_close(
        f"eps={epsilon:g} U_minus_one residual",
        residual_minus_one,
        float(stored_residuals["U_minus_one"]),
        thresholds.stored_value,
    )

    valid_sign_chart = (
        1.0 < A < -ell
        and ell < -1.0 < r < alpha < beta < 1.0
        and mass_ell > 0.0
        and mass_r > 0.0
        and mass_one > 0.0
        and density_mass > 0.0
    )
    if not valid_sign_chart:
        fail(f"eps={epsilon:g}: sign chart or positivity failed at stored center")

    fold = payload["fold"]
    limit_solution = solver.LimitSolution(
        A=float(payload["limit_solution"]["A"]),
        alpha=float(payload["limit_solution"]["alpha"]),
        mass_ell=0.0,
        mass_r=0.0,
        density_mass=0.0,
        residual_alpha=0.0,
        residual_minus_one=0.0,
    )
    left_weight = float(fold["left_weight"])
    null_slope = float(fold["null_slope"])

    B = (A - limit_solution.A) / eta - null_slope * ((alpha - limit_solution.alpha) / eta)
    tau = (alpha - limit_solution.alpha) / eta
    k1, k2 = solver.rescaled_system(B, tau, eta, limit_solution, left_weight, null_slope)
    if abs(k1) > thresholds.k_residual or abs(k2) > thresholds.k_residual:
        fail(f"eps={epsilon:g}: rescaled residuals too large K=({k1:.3e}, {k2:.3e})")

    krawczyk = row["krawczyk_box"]
    assert_close(f"eps={epsilon:g} B", B, float(krawczyk["center"]["B"]), thresholds.stored_value)
    assert_close(f"eps={epsilon:g} tau", tau, float(krawczyk["center"]["tau"]), thresholds.stored_value)
    assert_close(f"eps={epsilon:g} K1", k1, float(krawczyk["rescaled_residual"]["K1"]), thresholds.stored_value)
    assert_close(f"eps={epsilon:g} K2", k2, float(krawczyk["rescaled_residual"]["K2"]), thresholds.stored_value)

    analytic_jacobian = solver.analytic_rescaled_jacobian(B, tau, eta, limit_solution, left_weight, null_slope)
    finite_difference_jacobian = solver.rescaled_jacobian(B, tau, eta, limit_solution, left_weight, null_slope)
    analytic_det = float(np.linalg.det(analytic_jacobian))
    if abs(analytic_det) < thresholds.determinant_abs:
        fail(f"eps={epsilon:g}: analytic determinant too small: {analytic_det:.6e}")
    analytic_fd_diff = float(np.max(np.abs(analytic_jacobian - finite_difference_jacobian)))
    if analytic_fd_diff > thresholds.analytic_fd_diff:
        fail(f"eps={epsilon:g}: analytic/FD Jacobian mismatch {analytic_fd_diff:.3e}")
    assert_close(
        f"eps={epsilon:g} analytic determinant",
        analytic_det,
        float(krawczyk["analytic_determinant"]),
        thresholds.stored_value,
    )

    radius_B = float(krawczyk["radii"]["B"])
    radius_tau = float(krawczyk["radii"]["tau"])
    correction, inclusion, margin, contraction = solver.krawczyk_diagnostic(
        B,
        tau,
        eta,
        limit_solution,
        left_weight,
        null_slope,
        radius_B=radius_B,
        radius_tau=radius_tau,
    )
    for idx, label in enumerate(["B", "tau"]):
        assert_close(
            f"eps={epsilon:g} correction {label}",
            float(correction[idx]),
            float(krawczyk["correction"][idx]),
            thresholds.stored_value,
        )
        assert_close(
            f"eps={epsilon:g} inclusion {label}",
            float(inclusion[idx]),
            float(krawczyk["sampled_inclusion"][idx]),
            thresholds.stored_value,
        )
        assert_close(
            f"eps={epsilon:g} sampled margin {label}",
            float(margin[idx]),
            float(krawczyk["sampled_margin"][idx]),
            thresholds.stored_value,
        )
        if float(margin[idx]) <= thresholds.krawczyk_margin:
            fail(f"eps={epsilon:g}: sampled Krawczyk margin {label}={float(margin[idx]):.6e} too small")
    assert_close(
        f"eps={epsilon:g} sampled contraction",
        float(contraction),
        float(krawczyk["sampled_contraction"]),
        thresholds.stored_value,
    )
    if contraction >= thresholds.contraction:
        fail(f"eps={epsilon:g}: sampled contraction {contraction:.6e} >= {thresholds.contraction:.6e}")

    diff_by_f = solver.potential_difference_by_F(A, alpha, epsilon)
    diff_direct = residual_minus_one - residual_alpha
    if abs(diff_by_f - diff_direct) > thresholds.potential_difference:
        fail(f"eps={epsilon:g}: F-cont potential difference mismatch {abs(diff_by_f - diff_direct):.3e}")

    primitive = krawczyk["potential_difference_check"].get("residue_log_primitive")
    if primitive is not None:
        path_separation = float(primitive["path_separation_diagnostic"])
        pole_count = int(primitive["pole_count_after_path_cancellation"])
        if path_separation <= thresholds.path_separation:
            fail(f"eps={epsilon:g}: residue-log path separation too small: {path_separation:.6e}")
        if pole_count != 6:
            fail(f"eps={epsilon:g}: expected 6 reduced residue-log poles, got {pole_count}")

    recomputed_arb_full_difference: str | None = None
    if arb_primitive_check or arb_center_residual_check or arb_interval_krawczyk_check:
        (
            arb_real,
            arb_imag,
            arb_full_difference,
            arb_full_contains_zero,
            path_separation,
            pole_count,
        ) = solver.continuous_difference_by_w_residues_acb(A, alpha, epsilon)
        recomputed_arb_full_difference = arb_full_difference

    if arb_primitive_check:
        if primitive is None:
            fail(f"{row_context}: missing stored residue-log primitive fields for Arb comparison")
        assert_arb_center_close(row_context, "arb_real_ball", arb_real, primitive["arb_real_ball"])
        assert_arb_center_close(row_context, "arb_imag_ball", arb_imag, primitive["arb_imag_ball"])
        assert_arb_center_close(
            row_context,
            "arb_full_difference_ball",
            arb_full_difference,
            primitive["arb_full_difference_ball"],
        )
        assert_equal(
            f"{row_context} arb_full_difference_contains_zero",
            bool(arb_full_contains_zero),
            bool(primitive["arb_full_difference_contains_zero"]),
        )
        assert_close(
            f"{row_context} path_separation_diagnostic",
            float(path_separation),
            float(primitive["path_separation_diagnostic"]),
            thresholds.stored_value,
        )
        assert_equal(
            f"{row_context} pole_count_after_path_cancellation",
            int(pole_count),
            int(primitive["pole_count_after_path_cancellation"]),
        )
        if path_separation <= thresholds.path_separation:
            fail(f"{row_context}: recomputed Arb path separation too small: {path_separation:.6e}")
        if pole_count != 6:
            fail(f"{row_context}: recomputed Arb pole count expected 6, got {pole_count}")

    arb_center_k: list[Any] | None = None
    if arb_center_residual_check or arb_interval_krawczyk_check:
        from flint import arb, ctx

        if recomputed_arb_full_difference is None:
            fail(f"{row_context}: internal error, missing recomputed Arb full difference")
        ctx.prec = 256
        arb_u_minus_one = arb(solver.potential_minus_one_acb(A, alpha, epsilon))
        arb_difference = arb(recomputed_arb_full_difference)
        arb_u_alpha = arb_u_minus_one - arb_difference
        assert_finite_arb_ball(f"{row_context} Arb U(-1)", arb_u_minus_one)
        assert_finite_arb_ball(f"{row_context} Arb U(-1)-U(alpha)", arb_difference)
        assert_finite_arb_ball(f"{row_context} Arb U(alpha)", arb_u_alpha)
        assert_close(
            f"{row_context} Arb U(-1) center",
            arb_ball_center(str(arb_u_minus_one)),
            residual_minus_one,
            thresholds.stored_value,
        )
        assert_close(
            f"{row_context} Arb U(alpha) center via difference",
            arb_ball_center(str(arb_u_alpha)),
            residual_alpha,
            thresholds.stored_value,
        )
        arb_eta = arb(repr(float(eta)))
        arb_left_weight = arb(repr(float(left_weight)))
        arb_k1 = arb_u_alpha / arb_eta
        arb_k2 = (arb_left_weight * arb_u_alpha + arb_u_minus_one) / (arb_eta * arb_eta)
        assert_finite_arb_ball(f"{row_context} Arb K1 center residual", arb_k1)
        assert_finite_arb_ball(f"{row_context} Arb K2 center residual", arb_k2)
        arb_center_k = [arb_k1, arb_k2]
        arb_k1_upper = arb_abs_upper(f"{row_context} Arb K1 center residual", arb_k1)
        arb_k2_upper = arb_abs_upper(f"{row_context} Arb K2 center residual", arb_k2)
        if arb_center_residual_check and (
            arb_k1_upper > thresholds.k_residual or arb_k2_upper > thresholds.k_residual
        ):
            fail(
                f"{row_context}: Arb center K residual too large "
                f"(|K1|<={arb_k1_upper:.3e}, |K2|<={arb_k2_upper:.3e}, "
                f"threshold={thresholds.k_residual:.3e})"
            )

    if arb_box_uminus_check:
        from flint import arb

        radius_B = float(krawczyk["radii"]["B"])
        radius_tau = float(krawczyk["radii"]["tau"])
        A_values = [
            limit_solution.A
            + eta * (null_slope * (tau + delta_tau) + (B + delta_B))
            for delta_B in [-radius_B, radius_B]
            for delta_tau in [-radius_tau, radius_tau]
        ]
        alpha_values = [
            limit_solution.alpha + eta * (tau + delta_tau)
            for delta_tau in [-radius_tau, radius_tau]
        ]
        arb_box = arb(
            solver.potential_minus_one_box_acb(
                min(A_values),
                max(A_values),
                min(alpha_values),
                max(alpha_values),
                epsilon,
            )
        )
        assert_finite_arb_ball(f"{row_context} Arb box U(-1)", arb_box)
        if not arb_box.contains(arb(repr(float(residual_minus_one)))):
            fail(f"{row_context}: Arb box U(-1) does not contain stored center residual")
        arb_box_upper = arb_abs_upper(f"{row_context} Arb box U(-1)", arb_box)
        if arb_box_upper > thresholds.arb_box_uminus_abs:
            fail(
                f"{row_context}: Arb box U(-1) abs upper {arb_box_upper:.6e} "
                f"> threshold {thresholds.arb_box_uminus_abs:.6e}"
            )

    if arb_box_uminus_derivative_check:
        from flint import arb

        radius_B = float(krawczyk["radii"]["B"])
        radius_tau = float(krawczyk["radii"]["tau"])
        A_values = [
            limit_solution.A
            + eta * (null_slope * (tau + delta_tau) + (B + delta_B))
            for delta_B in [-radius_B, radius_B]
            for delta_tau in [-radius_tau, radius_tau]
        ]
        alpha_values = [
            limit_solution.alpha + eta * (tau + delta_tau)
            for delta_tau in [-radius_tau, radius_tau]
        ]
        derivative_cases = [
            ("B", eta, 0.0, solver.analytic_G_derivative(A, alpha, epsilon, eta, 0.0)[1]),
            (
                "tau",
                eta * null_slope,
                eta,
                solver.analytic_G_derivative(A, alpha, epsilon, eta * null_slope, eta)[1],
            ),
        ]
        for label, direction_A, direction_alpha, center_derivative in derivative_cases:
            derivative_box = arb(
                solver.potential_minus_one_derivative_box_acb(
                    min(A_values),
                    max(A_values),
                    min(alpha_values),
                    max(alpha_values),
                    epsilon,
                    direction_A,
                    direction_alpha,
                )
            )
            assert_finite_arb_ball(f"{row_context} Arb box dU(-1)/d{label}", derivative_box)
            if not derivative_box.contains(arb(repr(float(center_derivative)))):
                fail(f"{row_context}: Arb box dU(-1)/d{label} does not contain center derivative")
            derivative_upper = arb_abs_upper(f"{row_context} Arb box dU(-1)/d{label}", derivative_box)
            if derivative_upper > thresholds.arb_box_uminus_derivative_abs:
                fail(
                    f"{row_context}: Arb box dU(-1)/d{label} abs upper {derivative_upper:.6e} "
                    f"> threshold {thresholds.arb_box_uminus_derivative_abs:.6e}"
                )

    if arb_box_contact_derivative_check:
        from flint import arb

        radius_B = float(krawczyk["radii"]["B"])
        radius_tau = float(krawczyk["radii"]["tau"])
        A_values = [
            limit_solution.A
            + eta * (null_slope * (tau + delta_tau) + (B + delta_B))
            for delta_B in [-radius_B, radius_B]
            for delta_tau in [-radius_tau, radius_tau]
        ]
        alpha_values = [
            limit_solution.alpha + eta * (tau + delta_tau)
            for delta_tau in [-radius_tau, radius_tau]
        ]
        derivative_cases = [
            ("B", eta, 0.0, solver.analytic_G_derivative(A, alpha, epsilon, eta, 0.0)[0]),
            (
                "tau",
                eta * null_slope,
                eta,
                solver.analytic_G_derivative(A, alpha, epsilon, eta * null_slope, eta)[0],
            ),
        ]
        for label, direction_A, direction_alpha, center_derivative in derivative_cases:
            derivative_box = arb(
                solver.contact_derivative_box_acb(
                    min(A_values),
                    max(A_values),
                    min(alpha_values),
                    max(alpha_values),
                    epsilon,
                    direction_A,
                    direction_alpha,
                )
            )
            assert_finite_arb_ball(f"{row_context} Arb box dU(alpha)/d{label}", derivative_box)
            if not derivative_box.contains(arb(repr(float(center_derivative)))):
                fail(f"{row_context}: Arb box dU(alpha)/d{label} does not contain center derivative")
            derivative_upper = arb_abs_upper(f"{row_context} Arb box dU(alpha)/d{label}", derivative_box)
            if derivative_upper > thresholds.arb_box_contact_derivative_abs:
                fail(
                    f"{row_context}: Arb box dU(alpha)/d{label} abs upper {derivative_upper:.6e} "
                    f"> threshold {thresholds.arb_box_contact_derivative_abs:.6e}"
                )

    if arb_box_dk_check or arb_interval_krawczyk_check:
        from flint import arb

        radius_B = float(krawczyk["radii"]["B"])
        radius_tau = float(krawczyk["radii"]["tau"])
        arb_eta = arb(repr(float(eta)))
        arb_eta2 = arb_eta * arb_eta
        arb_left_weight = arb(repr(float(left_weight)))

        center_inverse = np.linalg.inv(analytic_jacobian)
        arb_center_inverse = [
            [arb(repr(float(center_inverse[i, j]))) for j in range(2)]
            for i in range(2)
        ]
        radii = [radius_B, radius_tau]
        sampled_correction = [float(krawczyk["correction"][0]), float(krawczyk["correction"][1])]
        interval_correction: list[float] | None = None
        if arb_interval_krawczyk_check:
            if arb_center_k is None:
                fail(f"{row_context}: internal error, missing Arb center K residual vector")
            interval_correction = []
            for row_idx, label in enumerate(["B", "tau"]):
                correction_entry = arb(0)
                for inner_idx in range(2):
                    correction_entry += arb_center_inverse[row_idx][inner_idx] * arb_center_k[inner_idx]
                assert_finite_arb_ball(f"{row_context} Arb interval Krawczyk correction {label}", correction_entry)
                interval_correction.append(
                    arb_abs_upper(f"{row_context} Arb interval Krawczyk correction {label}", correction_entry)
                )
        max_defect_action = [0.0, 0.0]
        worst_subbox: list[tuple[int, int] | None] = [None, None]
        max_entry_radius = 0.0
        subdivision_B, subdivision_tau = arb_box_dk_subdivisions

        def build_dk_box(
            delta_B_low: float,
            delta_B_high: float,
            delta_tau_low: float,
            delta_tau_high: float,
        ) -> list[list[Any]]:
            A_values = [
                limit_solution.A
                + eta * (null_slope * (tau + delta_tau) + (B + delta_B))
                for delta_B in [delta_B_low, delta_B_high]
                for delta_tau in [delta_tau_low, delta_tau_high]
            ]
            alpha_values = [
                limit_solution.alpha + eta * (tau + delta_tau)
                for delta_tau in [delta_tau_low, delta_tau_high]
            ]
            derivative_columns = []
            derivative_cases = [
                ("B", eta, 0.0),
                ("tau", eta * null_slope, eta),
            ]
            for label, direction_A, direction_alpha in derivative_cases:
                dG1 = arb(
                    solver.contact_derivative_box_acb(
                        min(A_values),
                        max(A_values),
                        min(alpha_values),
                        max(alpha_values),
                        epsilon,
                        direction_A,
                        direction_alpha,
                    )
                )
                dG2 = arb(
                    solver.potential_minus_one_derivative_box_acb(
                        min(A_values),
                        max(A_values),
                        min(alpha_values),
                        max(alpha_values),
                        epsilon,
                        direction_A,
                        direction_alpha,
                    )
                )
                assert_finite_arb_ball(f"{row_context} Arb box dG1/d{label}", dG1)
                assert_finite_arb_ball(f"{row_context} Arb box dG2/d{label}", dG2)
                derivative_columns.append(
                    [
                        dG1 / arb_eta,
                        (arb_left_weight * dG1 + dG2) / arb_eta2,
                    ]
                )
            return [
                [derivative_columns[0][0], derivative_columns[1][0]],
                [derivative_columns[0][1], derivative_columns[1][1]],
            ]

        full_dk_box = build_dk_box(-radius_B, radius_B, -radius_tau, radius_tau)
        for row_idx in range(2):
            for col_idx in range(2):
                entry_name = f"{row_context} Arb full-box DK[{row_idx},{col_idx}]"
                assert_finite_arb_ball(entry_name, full_dk_box[row_idx][col_idx])
                if not full_dk_box[row_idx][col_idx].contains(
                    arb(repr(float(analytic_jacobian[row_idx, col_idx])))
                ):
                    fail(
                        f"{row_context}: Arb full-box DK[{row_idx},{col_idx}] does not contain "
                        "center analytic Jacobian entry"
                    )

        for box_B_index in range(subdivision_B):
            delta_B_low = -radius_B + 2.0 * radius_B * box_B_index / subdivision_B
            delta_B_high = -radius_B + 2.0 * radius_B * (box_B_index + 1) / subdivision_B
            for box_tau_index in range(subdivision_tau):
                delta_tau_low = -radius_tau + 2.0 * radius_tau * box_tau_index / subdivision_tau
                delta_tau_high = -radius_tau + 2.0 * radius_tau * (box_tau_index + 1) / subdivision_tau
                dk_box = build_dk_box(delta_B_low, delta_B_high, delta_tau_low, delta_tau_high)
                for row_idx in range(2):
                    for col_idx in range(2):
                        entry_name = f"{row_context} Arb DK[{row_idx},{col_idx}]"
                        assert_finite_arb_ball(entry_name, dk_box[row_idx][col_idx])
                        max_entry_radius = max(max_entry_radius, float(dk_box[row_idx][col_idx].rad()))

                for row_idx in range(2):
                    defect_action = 0.0
                    for col_idx in range(2):
                        product_entry = arb(0)
                        for inner_idx in range(2):
                            product_entry += arb_center_inverse[row_idx][inner_idx] * dk_box[inner_idx][col_idx]
                        identity_entry = arb(1) if row_idx == col_idx else arb(0)
                        defect_action += (
                            arb_abs_upper(
                                f"{row_context} Arb DK defect M[{row_idx},{col_idx}]",
                                identity_entry - product_entry,
                            )
                            * radii[col_idx]
                        )
                    if defect_action > max_defect_action[row_idx]:
                        max_defect_action[row_idx] = defect_action
                        worst_subbox[row_idx] = (box_B_index, box_tau_index)

        sampled_defect_margins = [
            radii[idx] - sampled_correction[idx] - max_defect_action[idx]
            for idx in range(2)
        ]
        if arb_box_dk_check:
            for idx, label in enumerate(["B", "tau"]):
                sampled_budget = float(krawczyk["sampled_inclusion"][idx]) - sampled_correction[idx]
                if sampled_defect_margins[idx] <= 0.0:
                    fail(
                        f"{row_context}: subdivided Arb DK defect-action {label} fails "
                        f"correction+defect<radius: correction={sampled_correction[idx]:.6e}, "
                        f"defect={max_defect_action[idx]:.6e}, radius={radii[idx]:.6e}, "
                        f"margin={sampled_defect_margins[idx]:.6e}, sampled_defect_budget={sampled_budget:.6e}, "
                        f"subdivisions={subdivision_B},{subdivision_tau}, "
                        f"worst_subbox={worst_subbox[idx]}, max_DK_entry_radius={max_entry_radius:.6e}"
                    )

        interval_margins: list[float] | None = None
        if interval_correction is not None:
            interval_margins = [
                radii[idx] - interval_correction[idx] - max_defect_action[idx]
                for idx in range(2)
            ]
            for idx, label in enumerate(["B", "tau"]):
                dominant = "correction" if interval_correction[idx] >= max_defect_action[idx] else "defect"
                if interval_margins[idx] <= 0.0:
                    fail(
                        f"{row_context}: Arb interval Krawczyk inclusion {label} fails "
                        f"correction+defect<radius: correction={interval_correction[idx]:.6e}, "
                        f"defect={max_defect_action[idx]:.6e}, dominant={dominant}, "
                        f"radius={radii[idx]:.6e}, margin={interval_margins[idx]:.6e}, "
                        f"stored_sampled_correction={sampled_correction[idx]:.6e}, "
                        f"subdivisions={subdivision_B},{subdivision_tau}, "
                        f"worst_subbox={worst_subbox[idx]}, max_DK_entry_radius={max_entry_radius:.6e}"
                    )

        if verbose:
            if interval_margins is not None and interval_correction is not None:
                print(
                    f"  Arb interval Krawczyk subdivisions={subdivision_B},{subdivision_tau} "
                    f"correction=({interval_correction[0]:.6e}, {interval_correction[1]:.6e}) "
                    f"defect=({max_defect_action[0]:.6e}, {max_defect_action[1]:.6e}) "
                    f"margin=({interval_margins[0]:.6e}, {interval_margins[1]:.6e}) "
                    f"max_entry_radius={max_entry_radius:.6e}"
                )
            else:
                print(
                    f"  Arb DK defect-action subdivisions={subdivision_B},{subdivision_tau} "
                    f"defect=({max_defect_action[0]:.6e}, {max_defect_action[1]:.6e}) "
                    f"margin=({sampled_defect_margins[0]:.6e}, {sampled_defect_margins[1]:.6e}) "
                    f"max_entry_radius={max_entry_radius:.6e}"
                )

    branch_A = stored_pair(row["branch_box"], "A")
    branch_alpha = stored_pair(row["branch_box"], "alpha")
    branch_margins = solver.parameter_box_margins(epsilon, branch_A[0], branch_A[1], branch_alpha[0], branch_alpha[1])
    assert_positive_margins(f"eps={epsilon:g} branch box", branch_margins, thresholds.sign_margin)

    A_values = [
        limit_solution.A
        + eta * (null_slope * (tau + delta_tau) + (B + delta_B))
        for delta_B in [-radius_B, radius_B]
        for delta_tau in [-radius_tau, radius_tau]
    ]
    alpha_values = [limit_solution.alpha + eta * (tau + delta_tau) for delta_tau in [-radius_tau, radius_tau]]
    krawczyk_margins = solver.parameter_box_margins(
        epsilon,
        min(A_values),
        max(A_values),
        min(alpha_values),
        max(alpha_values),
    )
    assert_positive_margins(f"eps={epsilon:g} Krawczyk box", krawczyk_margins, thresholds.sign_margin)

    if verbose:
        print(
            f"eps={epsilon:g}: PASS "
            f"det={analytic_det:.6e} contraction={contraction:.6e} "
            f"margin=({float(margin[0]):.6e}, {float(margin[1]):.6e}) "
            f"min_sign={min(krawczyk_margins.values()):.6e}"
        )


def verify_payload(
    payload: dict[str, Any],
    thresholds: Thresholds,
    arb_primitive_check: bool,
    arb_center_residual_check: bool,
    arb_box_uminus_check: bool,
    arb_box_uminus_derivative_check: bool,
    arb_box_contact_derivative_check: bool,
    arb_box_dk_check: bool,
    arb_interval_krawczyk_check: bool,
    arb_box_dk_subdivisions: tuple[int, int],
    verbose: bool,
) -> int:
    rows = payload.get("rows", [])
    if not rows:
        fail("payload: no rows found")
    for row_index, row in enumerate(rows):
        recompute_row(
            row_index,
            row,
            payload,
            thresholds,
            arb_primitive_check=arb_primitive_check,
            arb_center_residual_check=arb_center_residual_check,
            arb_box_uminus_check=arb_box_uminus_check,
            arb_box_uminus_derivative_check=arb_box_uminus_derivative_check,
            arb_box_contact_derivative_check=arb_box_contact_derivative_check,
            arb_box_dk_check=arb_box_dk_check,
            arb_interval_krawczyk_check=arb_interval_krawczyk_check,
            arb_box_dk_subdivisions=arb_box_dk_subdivisions,
            verbose=verbose,
        )
    return len(rows)


def run_tamper_self_test(
    payload: dict[str, Any],
    thresholds: Thresholds,
    arb_primitive_check: bool,
    arb_center_residual_check: bool,
    arb_box_uminus_check: bool,
    arb_box_uminus_derivative_check: bool,
    arb_box_contact_derivative_check: bool,
    arb_box_dk_check: bool,
    arb_interval_krawczyk_check: bool,
    arb_box_dk_subdivisions: tuple[int, int],
) -> int:
    def mutate_sampled_margin(tampered: dict[str, Any]) -> None:
        margin = tampered["rows"][0]["krawczyk_box"]["sampled_margin"]
        margin[0] = float(margin[0]) + 0.1

    def mutate_sampled_contraction(tampered: dict[str, Any]) -> None:
        krawczyk = tampered["rows"][0]["krawczyk_box"]
        krawczyk["sampled_contraction"] = float(krawczyk["sampled_contraction"]) + 0.1

    def mutate_arb_contains_zero(tampered: dict[str, Any]) -> None:
        primitive = tampered["rows"][0]["krawczyk_box"]["potential_difference_check"]["residue_log_primitive"]
        primitive["arb_full_difference_contains_zero"] = not bool(primitive["arb_full_difference_contains_zero"])

    def mutate_branch_A_high(tampered: dict[str, Any]) -> None:
        branch_A = tampered["rows"][0]["branch_box"]["A"]
        branch_A[1] = max(float(branch_A[1]), 10.0)

    def mutate_center_residual(tampered: dict[str, Any]) -> None:
        residuals = tampered["rows"][0]["solution"]["residuals"]
        residuals["U_alpha"] = float(residuals["U_alpha"]) + 1.0

    tamper_cases = [
        ("sampled_margin[0]", True, mutate_sampled_margin),
        ("sampled_contraction", True, mutate_sampled_contraction),
        ("arb_full_difference_contains_zero", arb_primitive_check, mutate_arb_contains_zero),
        ("branch_box.A[1]", True, mutate_branch_A_high),
        ("solution.residuals.U_alpha", True, mutate_center_residual),
    ]

    checked = 0
    if (
        arb_box_uminus_check
        or arb_box_uminus_derivative_check
        or arb_box_contact_derivative_check
        or arb_box_dk_check
        or arb_interval_krawczyk_check
    ):
        from flint import arb

        checked += 1
        try:
            assert_finite_arb_ball("finite Arb guard self-test", arb("nan"))
        except VerificationError:
            pass
        else:
            fail("self-test finite Arb guard: non-finite Arb ball unexpectedly passed")

    for name, enabled, mutate in tamper_cases:
        if not enabled:
            continue
        checked += 1
        tampered = copy.deepcopy(payload)
        mutate(tampered)
        try:
            verify_payload(
                tampered,
                thresholds,
                arb_primitive_check=arb_primitive_check,
                arb_center_residual_check=arb_center_residual_check,
                arb_box_uminus_check=arb_box_uminus_check,
                arb_box_uminus_derivative_check=arb_box_uminus_derivative_check,
                arb_box_contact_derivative_check=arb_box_contact_derivative_check,
                arb_box_dk_check=arb_box_dk_check,
                arb_interval_krawczyk_check=arb_interval_krawczyk_check,
                arb_box_dk_subdivisions=arb_box_dk_subdivisions,
                verbose=False,
            )
        except VerificationError:
            continue
        fail(f"self-test tamper case {name}: tampered payload unexpectedly passed")
    return checked


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "json_path",
        nargs="?",
        default=str(ROOT / "two_interval_branch_certificate_skeleton.json"),
        help="skeleton JSON exported by solve_two_interval_finite_gap.py",
    )
    parser.add_argument(
        "--arb-primitive-check",
        action="store_true",
        help="recompute the reduced Arb residue-log primitive diagnostics for every row",
    )
    parser.add_argument(
        "--arb-center-residual-check",
        action="store_true",
        help=(
            "recompute an Arb/Acb U(-1) ball and combine it with the residue-log "
            "Arb difference to check the center K residuals"
        ),
    )
    parser.add_argument(
        "--arb-box-uminus-check",
        action="store_true",
        help="recompute an Arb/Acb enclosure for U(-1) over each full local Krawczyk parameter box",
    )
    parser.add_argument(
        "--arb-box-uminus-derivative-check",
        action="store_true",
        help="recompute Arb/Acb enclosures for the U(-1) directional derivatives over each local Krawczyk box",
    )
    parser.add_argument(
        "--arb-box-contact-derivative-check",
        action="store_true",
        help="recompute Arb/Acb enclosures for the U(alpha) contact directional derivatives over each local Krawczyk box",
    )
    parser.add_argument(
        "--arb-box-dk-check",
        action="store_true",
        help=(
            "assemble an Arb interval D_(B,tau)K matrix from the derivative primitives, "
            "check center containment, and run the subdivided defect-action diagnostic"
        ),
    )
    parser.add_argument(
        "--arb-interval-krawczyk-check",
        action="store_true",
        help=(
            "assemble the Arb center K residual and subdivided Arb interval DK defect-action "
            "into the diagnostic inclusion abs(C*K_center)+defect<radius"
        ),
    )
    parser.add_argument(
        "--arb-box-dk-subdivisions",
        default="1,1",
        help="subdivide the local Krawczyk box as B,tau counts for the Arb DK defect-action diagnostic",
    )
    parser.add_argument(
        "--self-test-tamper",
        action="store_true",
        help="after normal verification passes, verify in-memory tampered payloads are rejected",
    )
    parser.add_argument("--quiet", action="store_true", help="print only the final PASS line")
    args = parser.parse_args()

    path = Path(args.json_path)
    payload = json.loads(path.read_text(encoding="utf-8"))

    thresholds = Thresholds()
    arb_box_dk_subdivisions = parse_subdivisions(args.arb_box_dk_subdivisions)
    row_count = verify_payload(
        payload,
        thresholds,
        arb_primitive_check=args.arb_primitive_check,
        arb_center_residual_check=args.arb_center_residual_check,
        arb_box_uminus_check=args.arb_box_uminus_check,
        arb_box_uminus_derivative_check=args.arb_box_uminus_derivative_check,
        arb_box_contact_derivative_check=args.arb_box_contact_derivative_check,
        arb_box_dk_check=args.arb_box_dk_check,
        arb_interval_krawczyk_check=args.arb_interval_krawczyk_check,
        arb_box_dk_subdivisions=arb_box_dk_subdivisions,
        verbose=not args.quiet,
    )

    if args.self_test_tamper:
        tamper_count = run_tamper_self_test(
            payload,
            thresholds,
            arb_primitive_check=args.arb_primitive_check,
            arb_center_residual_check=args.arb_center_residual_check,
            arb_box_uminus_check=args.arb_box_uminus_check,
            arb_box_uminus_derivative_check=args.arb_box_uminus_derivative_check,
            arb_box_contact_derivative_check=args.arb_box_contact_derivative_check,
            arb_box_dk_check=args.arb_box_dk_check,
            arb_interval_krawczyk_check=args.arb_interval_krawczyk_check,
            arb_box_dk_subdivisions=arb_box_dk_subdivisions,
        )
        print(
            "OVERALL TWO-INTERVAL SKELETON CHECK: PASS "
            f"({row_count} rows; tamper self-test PASS {tamper_count} cases; "
            "verifier integrity only, not a math proof)"
        )
    else:
        print(f"OVERALL TWO-INTERVAL SKELETON CHECK: PASS ({row_count} rows)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
