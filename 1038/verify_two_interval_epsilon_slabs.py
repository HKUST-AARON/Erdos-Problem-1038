#!/usr/bin/env python3
"""Diagnostic epsilon-slab verifier for the two-interval finite-gap branch.

This is a binary MVP for adjacent finite epsilon rows.  For a slab
``[epsilon_low, epsilon_high]`` it works in ``eta = sqrt(epsilon)`` and uses
affine endpoint center functions

    B_c(eta), tau_c(eta)

interpolated from the stored endpoint rows.  The checked box variables are
offsets ``u, v`` around those centers:

    B = B_c(eta) + u,   tau = tau_c(eta) + v.

The Arb/Acb derivative primitives in ``solve_two_interval_finite_gap.py`` are
used to assemble diagnostic DK boxes on u/v subboxes.  By default the eta
dependence is sampled.  With ``--eta-interval-dk-check``, eta is enclosed on
eta subintervals for the DK boxes.  The center correction is still sampled, so
a PASS from this script is slab diagnostic evidence and not a continuum proof.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np


ROOT = Path(__file__).resolve().parent
SOLVER_PATH = ROOT / "solve_two_interval_finite_gap.py"

solver: Any | None = None


def load_solver() -> Any:
    global solver
    if solver is not None:
        return solver
    spec = importlib.util.spec_from_file_location("solve_two_interval_finite_gap", SOLVER_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import solver from {SOLVER_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    solver = module
    return module


class VerificationError(Exception):
    pass


@dataclass(frozen=True)
class SlabSpec:
    eps_low: float
    eps_high: float


@dataclass(frozen=True)
class EndpointRow:
    index: int
    epsilon: float
    B: float
    tau: float


@dataclass(frozen=True)
class SlabResult:
    spec: SlabSpec
    low_row: EndpointRow
    high_row: EndpointRow
    eta_subdivisions: int
    uv_subdivisions: int
    radii: np.ndarray
    correction: np.ndarray
    defect: np.ndarray
    margin: np.ndarray
    defect_source: tuple[str, str]
    max_dk_entry_radius: float
    min_sign_margin: float
    eta_interval_dk_check: bool
    center_correction_mode: str
    worst_defect_detail: tuple[str, ...]

    @property
    def worst_margin(self) -> float:
        return float(np.min(self.margin))

    @property
    def limiting_component(self) -> str:
        return "u" if int(np.argmin(self.margin)) == 0 else "v"

    @property
    def dominant_term(self) -> str:
        idx = int(np.argmin(self.margin))
        return "correction" if self.correction[idx] >= self.defect[idx] else "defect"


def fail(message: str) -> None:
    raise VerificationError(message)


def finite_float(value: Any, path: str) -> float:
    if isinstance(value, bool):
        fail(f"{path}: expected finite float, got bool")
    try:
        result = float(value)
    except (TypeError, ValueError) as exc:
        fail(f"{path}: invalid float {value!r}: {exc}")
    if not math.isfinite(result):
        fail(f"{path}: expected finite float, got {result!r}")
    return result


def finite_array(name: str, value: Any) -> np.ndarray:
    try:
        array = np.asarray(value, dtype=float)
    except (TypeError, ValueError) as exc:
        fail(f"{name}: not numeric: {exc}")
    if not np.all(np.isfinite(array)):
        fail(f"{name}: non-finite values {array!r}")
    return array


def require_mapping(value: Any, path: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        fail(f"{path}: expected object, got {type(value).__name__}")
    return value


def parse_positive_pair(raw: str, name: str) -> tuple[float, float]:
    parts = raw.split(",")
    if len(parts) != 2:
        raise argparse.ArgumentTypeError(f"{name}: expected a,b pair")
    try:
        first = float(parts[0])
        second = float(parts[1])
    except ValueError as exc:
        raise argparse.ArgumentTypeError(f"{name}: expected numeric pair") from exc
    if first <= 0.0 or second <= 0.0 or not math.isfinite(first) or not math.isfinite(second):
        raise argparse.ArgumentTypeError(f"{name}: entries must be finite and positive")
    return first, second


def parse_subdivisions(raw: str) -> tuple[int, int]:
    parts = raw.split(",")
    if len(parts) != 2:
        raise argparse.ArgumentTypeError("--arb-box-dk-subdivisions: expected eta_samples,uv_subdivisions pair")
    try:
        eta_count = int(parts[0])
        uv_count = int(parts[1])
    except ValueError as exc:
        raise argparse.ArgumentTypeError("--arb-box-dk-subdivisions: expected integer pair") from exc
    if eta_count <= 0 or uv_count <= 0:
        raise argparse.ArgumentTypeError("--arb-box-dk-subdivisions: counts must be positive")
    return eta_count, uv_count


def parse_positive_int_list(raw: str) -> tuple[int, ...]:
    try:
        values = tuple(int(part) for part in raw.split(",") if part)
    except ValueError as exc:
        raise argparse.ArgumentTypeError("expected comma-separated positive integers") from exc
    if not values or any(value <= 0 for value in values):
        raise argparse.ArgumentTypeError("expected comma-separated positive integers")
    return values


def parse_slab(raw: str) -> SlabSpec:
    parts = raw.split(":")
    if len(parts) != 2:
        raise argparse.ArgumentTypeError("--slab: expected eps_low:eps_high")
    try:
        low = float(parts[0])
        high = float(parts[1])
    except ValueError as exc:
        raise argparse.ArgumentTypeError("--slab: expected numeric endpoints") from exc
    if low <= 0.0 or high <= 0.0 or not math.isfinite(low) or not math.isfinite(high):
        raise argparse.ArgumentTypeError("--slab: endpoints must be finite and positive")
    if low == high:
        raise argparse.ArgumentTypeError("--slab: endpoints must be distinct")
    return SlabSpec(min(low, high), max(low, high))


def arb_abs_upper(name: str, value: Any) -> float:
    if not hasattr(value, "is_finite") or not value.is_finite():
        fail(f"{name}: expected finite Arb ball, got {value!r}")
    upper = float(abs(value).upper())
    if not math.isfinite(upper):
        fail(f"{name}: non-finite Arb abs upper {upper!r}")
    return upper


def row_endpoint(index: int, row: Any) -> EndpointRow:
    row_map = require_mapping(row, f"rows[{index}]")
    epsilon = finite_float(row_map.get("epsilon"), f"rows[{index}].epsilon")
    box = require_mapping(row_map.get("krawczyk_box"), f"rows[{index}].krawczyk_box")
    center = require_mapping(box.get("center"), f"rows[{index}].krawczyk_box.center")
    return EndpointRow(
        index=index,
        epsilon=epsilon,
        B=finite_float(center.get("B"), f"rows[{index}].krawczyk_box.center.B"),
        tau=finite_float(center.get("tau"), f"rows[{index}].krawczyk_box.center.tau"),
    )


def find_endpoint(rows: list[Any], epsilon: float) -> EndpointRow:
    candidates = sorted_endpoints(rows)
    scale = max(1.0, abs(epsilon))
    for endpoint in candidates:
        if abs(endpoint.epsilon - epsilon) <= 1.0e-12 * scale:
            return endpoint
    available = ", ".join(f"{item.epsilon:g}" for item in sorted(candidates, key=lambda item: item.epsilon))
    fail(f"slab endpoint epsilon={epsilon:g}: no stored row found; available epsilons: {available}")


def sorted_endpoints(rows: list[Any]) -> list[EndpointRow]:
    return sorted((row_endpoint(index, row) for index, row in enumerate(rows)), key=lambda item: item.epsilon)


def assert_adjacent_endpoint_rows(rows: list[Any], low_row: EndpointRow, high_row: EndpointRow) -> None:
    endpoints = sorted_endpoints(rows)
    positions = {endpoint.index: index for index, endpoint in enumerate(endpoints)}
    low_position = positions[low_row.index]
    high_position = positions[high_row.index]
    if abs(low_position - high_position) == 1:
        return
    available = ", ".join(f"{endpoints[i].epsilon:g}:{endpoints[i + 1].epsilon:g}" for i in range(len(endpoints) - 1))
    fail(
        f"slab {low_row.epsilon:g}:{high_row.epsilon:g}: endpoints are not adjacent stored rows; "
        f"available adjacent slabs: {available}"
    )


def payload_constants(payload: dict[str, Any]) -> tuple[Any, float, float]:
    solver_module = load_solver()
    limit_raw = require_mapping(payload.get("limit_solution"), "payload.limit_solution")
    fold_raw = require_mapping(payload.get("fold"), "payload.fold")
    limit_solution = solver_module.LimitSolution(
        A=finite_float(limit_raw.get("A"), "payload.limit_solution.A"),
        alpha=finite_float(limit_raw.get("alpha"), "payload.limit_solution.alpha"),
        mass_ell=0.0,
        mass_r=0.0,
        density_mass=0.0,
        residual_alpha=0.0,
        residual_minus_one=0.0,
    )
    return (
        limit_solution,
        finite_float(fold_raw.get("left_weight"), "payload.fold.left_weight"),
        finite_float(fold_raw.get("null_slope"), "payload.fold.null_slope"),
    )


def affine_coefficients(low_row: EndpointRow, high_row: EndpointRow) -> tuple[float, float, float, float]:
    eta_low = math.sqrt(low_row.epsilon)
    eta_high = math.sqrt(high_row.epsilon)
    if eta_low >= eta_high:
        fail(f"invalid eta endpoints {eta_low:.17g}, {eta_high:.17g}")
    b_slope = (high_row.B - low_row.B) / (eta_high - eta_low)
    tau_slope = (high_row.tau - low_row.tau) / (eta_high - eta_low)
    b_intercept = low_row.B - b_slope * eta_low
    tau_intercept = low_row.tau - tau_slope * eta_low
    return b_slope, b_intercept, tau_slope, tau_intercept


def center_at(
    eta: float,
    low_row: EndpointRow,
    high_row: EndpointRow,
) -> tuple[float, float]:
    eta_low = math.sqrt(low_row.epsilon)
    eta_high = math.sqrt(high_row.epsilon)
    weight = (eta - eta_low) / (eta_high - eta_low)
    return (
        low_row.B + weight * (high_row.B - low_row.B),
        low_row.tau + weight * (high_row.tau - low_row.tau),
    )


def quadratic_range(c2: float, c1: float, c0: float, eta_low: float, eta_high: float) -> tuple[float, float]:
    values = [c2 * eta_low * eta_low + c1 * eta_low + c0, c2 * eta_high * eta_high + c1 * eta_high + c0]
    if c2 != 0.0:
        eta_star = -c1 / (2.0 * c2)
        if eta_low <= eta_star <= eta_high:
            values.append(c2 * eta_star * eta_star + c1 * eta_star + c0)
    return min(values), max(values)


def parameter_ranges(
    eta_low: float,
    eta_high: float,
    u_low: float,
    u_high: float,
    v_low: float,
    v_high: float,
    limit_solution: Any,
    null_slope: float,
    b_slope: float,
    b_intercept: float,
    tau_slope: float,
    tau_intercept: float,
) -> tuple[float, float, float, float]:
    A_values: list[float] = []
    alpha_values: list[float] = []
    for u in [u_low, u_high]:
        for v in [v_low, v_high]:
            A_low, A_high = quadratic_range(
                null_slope * tau_slope + b_slope,
                null_slope * (tau_intercept + v) + b_intercept + u,
                limit_solution.A,
                eta_low,
                eta_high,
            )
            alpha_low, alpha_high = quadratic_range(
                tau_slope,
                tau_intercept + v,
                limit_solution.alpha,
                eta_low,
                eta_high,
            )
            A_values.extend([A_low, A_high])
            alpha_values.extend([alpha_low, alpha_high])
    return min(A_values), max(A_values), min(alpha_values), max(alpha_values)


def arb_affine_parameters(
    solver_module: Any,
    arb_type: Any,
    arb_eta: Any,
    u_low: float,
    u_high: float,
    v_low: float,
    v_high: float,
    limit_solution: Any,
    null_slope: float,
    b_slope: float,
    b_intercept: float,
    tau_slope: float,
    tau_intercept: float,
) -> tuple[Any, Any, Any, Any]:
    arb_u = solver_module._arb_interval_from_bounds(u_low, u_high)
    arb_v = solver_module._arb_interval_from_bounds(v_low, v_high)
    tau = arb_type(repr(float(tau_slope))) * arb_eta + arb_type(repr(float(tau_intercept))) + arb_v
    B = arb_type(repr(float(b_slope))) * arb_eta + arb_type(repr(float(b_intercept))) + arb_u
    base_delta_alpha = tau
    base_delta_A = arb_type(repr(float(null_slope))) * tau + B
    alpha = arb_type(repr(float(limit_solution.alpha))) + arb_eta * base_delta_alpha
    A = arb_type(repr(float(limit_solution.A))) + arb_eta * base_delta_A
    return A, alpha, base_delta_A, base_delta_alpha


def slab_sign_margin(eps_low: float, eps_high: float, A_low: float, A_high: float, alpha_low: float, alpha_high: float) -> float:
    solver_module = load_solver()
    margins = {
        "A>1": A_low - 1.0,
        "A<-ell": -(solver_module.X_LEFT + eps_high) - A_high,
        "ell<-1": -1.0 - (solver_module.X_LEFT + eps_high),
        "r<alpha": alpha_low - solver_module.X_RIGHT,
        "alpha<beta": (1.0 - eps_high) - alpha_high,
        "beta<1": eps_low,
    }
    for key, value in margins.items():
        if not math.isfinite(value):
            fail(f"sign margin {key}: non-finite {value!r}")
    return min(margins.values())


def eta_grid(eta_low: float, eta_high: float, count: int) -> tuple[float, ...]:
    if count <= 1:
        return ((eta_low + eta_high) / 2.0,)
    return tuple(float(value) for value in np.linspace(eta_low, eta_high, count))


def eta_intervals(eta_low: float, eta_high: float, count: int) -> tuple[tuple[float, float], ...]:
    if count <= 0:
        fail(f"eta interval count must be positive, got {count}")
    grid = np.linspace(eta_low, eta_high, count + 1)
    return tuple((float(grid[index]), float(grid[index + 1])) for index in range(count))


def center_correction_over_slab(
    eta_low: float,
    eta_high: float,
    low_row: EndpointRow,
    high_row: EndpointRow,
    limit_solution: Any,
    left_weight: float,
    null_slope: float,
    grid_size: int,
) -> np.ndarray:
    solver_module = load_solver()
    correction = np.zeros(2)
    for eta in np.linspace(eta_low, eta_high, max(grid_size, 3)):
        eta_f = float(eta)
        B, tau = center_at(eta_f, low_row, high_row)
        K = finite_array("sampled center K", solver_module.rescaled_system(B, tau, eta_f, limit_solution, left_weight, null_slope))
        J = finite_array(
            "sampled center DK",
            solver_module.analytic_rescaled_jacobian(B, tau, eta_f, limit_solution, left_weight, null_slope),
        )
        try:
            C = np.linalg.inv(J)
        except np.linalg.LinAlgError as exc:
            fail(f"eta={eta_f:.17g}: center Jacobian is singular: {exc}")
        correction = np.maximum(correction, np.abs(C @ K))
    return correction


def interval_center_correction_over_slab(
    eta_low: float,
    eta_high: float,
    low_row: EndpointRow,
    high_row: EndpointRow,
    limit_solution: Any,
    left_weight: float,
    null_slope: float,
    eta_subdivisions: int,
) -> np.ndarray:
    from flint import arb

    solver_module = load_solver()
    b_slope, b_intercept, tau_slope, tau_intercept = affine_coefficients(low_row, high_row)
    correction = np.zeros(2)
    for eta_index, (eta_interval_low, eta_interval_high) in enumerate(eta_intervals(eta_low, eta_high, eta_subdivisions)):
        eta_mid = (eta_interval_low + eta_interval_high) / 2.0
        B_mid, tau_mid = center_at(eta_mid, low_row, high_row)
        J_mid = finite_array(
            "interval center correction DK",
            solver_module.analytic_rescaled_jacobian(B_mid, tau_mid, eta_mid, limit_solution, left_weight, null_slope),
        )
        try:
            C_mid = np.linalg.inv(J_mid)
        except np.linalg.LinAlgError as exc:
            fail(f"eta-correction-slice {eta_index}: center Jacobian is singular: {exc}")
        C_arb = [[arb(repr(float(C_mid[i, j]))) for j in range(2)] for i in range(2)]
        arb_eta = solver_module._arb_interval_from_bounds(eta_interval_low, eta_interval_high)
        arb_epsilon = solver_module._arb_interval_from_bounds(
            eta_interval_low * eta_interval_low,
            eta_interval_high * eta_interval_high,
        )
        arb_A, arb_alpha, _base_delta_A, _base_delta_alpha = arb_affine_parameters(
            solver_module,
            arb,
            arb_eta,
            0.0,
            0.0,
            0.0,
            0.0,
            limit_solution,
            null_slope,
            b_slope,
            b_intercept,
            tau_slope,
            tau_intercept,
        )
        U_alpha = arb(solver_module._contact_potential_acb_from_arb(arb_A, arb_alpha, arb_epsilon, 192))
        U_minus_one = arb(solver_module._potential_minus_one_acb_from_arb(arb_A, arb_alpha, arb_epsilon, 192))
        if not U_alpha.is_finite() or not U_minus_one.is_finite():
            fail(f"eta-correction-slice {eta_index}: non-finite Arb center residual")
        K = [
            U_alpha / arb_eta,
            (arb(repr(float(left_weight))) * U_alpha + U_minus_one) / (arb_eta * arb_eta),
        ]
        for row_idx in range(2):
            value = arb(0)
            for col_idx in range(2):
                value += C_arb[row_idx][col_idx] * K[col_idx]
            correction[row_idx] = max(
                correction[row_idx],
                arb_abs_upper(f"interval center correction[{row_idx}]", value),
            )
    return correction


def verify_slab(
    spec: SlabSpec,
    rows: list[Any],
    limit_solution: Any,
    left_weight: float,
    null_slope: float,
    radii: np.ndarray,
    eta_subdivisions: int,
    uv_subdivisions: int,
    eta_interval_dk_check: bool,
    eta_interval_dk_kernel: str,
    center_correction_mode: str,
) -> SlabResult:
    from flint import arb

    solver_module = load_solver()
    low_row = find_endpoint(rows, spec.eps_low)
    high_row = find_endpoint(rows, spec.eps_high)
    if low_row.epsilon > high_row.epsilon:
        low_row, high_row = high_row, low_row
    assert_adjacent_endpoint_rows(rows, low_row, high_row)

    eta_low = math.sqrt(spec.eps_low)
    eta_high = math.sqrt(spec.eps_high)
    b_slope, b_intercept, tau_slope, tau_intercept = affine_coefficients(low_row, high_row)
    if center_correction_mode == "interval":
        correction = interval_center_correction_over_slab(
            eta_low,
            eta_high,
            low_row,
            high_row,
            limit_solution,
            left_weight,
            null_slope,
            eta_subdivisions,
        )
    else:
        correction = center_correction_over_slab(
            eta_low,
            eta_high,
            low_row,
            high_row,
            limit_solution,
            left_weight,
            null_slope,
            grid_size=2 * eta_subdivisions + 1,
        )

    max_defect = np.zeros(2)
    defect_source = ["none", "none"]
    defect_detail = [(), ()]
    max_dk_entry_radius = 0.0
    min_sign_margin = math.inf
    identity = [[arb(1), arb(0)], [arb(0), arb(1)]]

    for u_index in range(uv_subdivisions):
        u_low = -float(radii[0]) + 2.0 * float(radii[0]) * u_index / uv_subdivisions
        u_high = -float(radii[0]) + 2.0 * float(radii[0]) * (u_index + 1) / uv_subdivisions
        for v_index in range(uv_subdivisions):
            v_low = -float(radii[1]) + 2.0 * float(radii[1]) * v_index / uv_subdivisions
            v_high = -float(radii[1]) + 2.0 * float(radii[1]) * (v_index + 1) / uv_subdivisions
            A_low, A_high, alpha_low, alpha_high = parameter_ranges(
                eta_low,
                eta_high,
                u_low,
                u_high,
                v_low,
                v_high,
                limit_solution,
                null_slope,
                b_slope,
                b_intercept,
                tau_slope,
                tau_intercept,
            )
            min_sign_margin = min(
                min_sign_margin,
                slab_sign_margin(spec.eps_low, spec.eps_high, A_low, A_high, alpha_low, alpha_high),
            )

    if eta_interval_dk_check:
        eta_items: tuple[tuple[float, float, float], ...] = tuple(
            (eta_interval_low, eta_interval_high, (eta_interval_low + eta_interval_high) / 2.0)
            for eta_interval_low, eta_interval_high in eta_intervals(eta_low, eta_high, eta_subdivisions)
        )
    else:
        eta_items = tuple((eta_sample, eta_sample, eta_sample) for eta_sample in eta_grid(eta_low, eta_high, eta_subdivisions))

    for eta_index, (eta_interval_low, eta_interval_high, eta_sample) in enumerate(eta_items):
        B_sample, tau_sample = center_at(eta_sample, low_row, high_row)
        J_sample = finite_array(
            "eta-slice center DK",
            solver_module.analytic_rescaled_jacobian(
                B_sample,
                tau_sample,
                eta_sample,
                limit_solution,
                left_weight,
                null_slope,
            ),
        )
        try:
            C_sample = np.linalg.inv(J_sample)
        except np.linalg.LinAlgError as exc:
            fail(f"eta-slice {eta_index}: center Jacobian is singular: {exc}")
        C_arb = [[arb(repr(float(C_sample[i, j]))) for j in range(2)] for i in range(2)]
        for u_index in range(uv_subdivisions):
            u_low = -float(radii[0]) + 2.0 * float(radii[0]) * u_index / uv_subdivisions
            u_high = -float(radii[0]) + 2.0 * float(radii[0]) * (u_index + 1) / uv_subdivisions
            for v_index in range(uv_subdivisions):
                v_low = -float(radii[1]) + 2.0 * float(radii[1]) * v_index / uv_subdivisions
                v_high = -float(radii[1]) + 2.0 * float(radii[1]) * (v_index + 1) / uv_subdivisions
                A_low, A_high, alpha_low, alpha_high = parameter_ranges(
                    eta_interval_low,
                    eta_interval_high,
                    u_low,
                    u_high,
                    v_low,
                    v_high,
                    limit_solution,
                    null_slope,
                    b_slope,
                    b_intercept,
                    tau_slope,
                    tau_intercept,
                )
                derivative_columns = []
                if eta_interval_dk_check:
                    arb_eta = solver_module._arb_interval_from_bounds(eta_interval_low, eta_interval_high)
                    arb_epsilon = solver_module._arb_interval_from_bounds(
                        eta_interval_low * eta_interval_low,
                        eta_interval_high * eta_interval_high,
                    )
                    arb_A, arb_alpha, base_delta_A, base_delta_alpha = arb_affine_parameters(
                        solver_module,
                        arb,
                        arb_eta,
                        u_low,
                        u_high,
                        v_low,
                        v_high,
                        limit_solution,
                        null_slope,
                        b_slope,
                        b_intercept,
                        tau_slope,
                        tau_intercept,
                    )
                    # For an eta interval, keep the Lyapunov-Schmidt direction
                    # unscaled.  Algebraically
                    #
                    #   dG[eta*s] / eta = dG[s],
                    #   dH[eta*s] / eta^2 = dH[s] / eta,
                    #
                    # but putting the eta factor into the Arb direction first
                    # loses a full layer of dependency before the division.
                    derivative_cases = [
                        ("u", arb(1), arb(0), False),
                        ("v", arb(repr(float(null_slope))), arb(1), False),
                    ]
                else:
                    arb_eta = arb(repr(float(eta_sample)))
                    arb_epsilon = arb(repr(float(eta_sample * eta_sample)))
                    arb_A = solver_module._arb_interval_from_bounds(A_low, A_high)
                    arb_alpha = solver_module._arb_interval_from_bounds(alpha_low, alpha_high)
                    derivative_cases = [
                        ("u", arb_eta, arb(0), True),
                        ("v", arb_eta * arb(repr(float(null_slope))), arb_eta, True),
                    ]
                for label, direction_A, direction_alpha, direction_is_eta_scaled in derivative_cases:
                    dG1 = arb(
                        solver_module._contact_directional_derivative_acb_from_arb(
                            arb_A,
                            arb_alpha,
                            arb_epsilon,
                            direction_A,
                            direction_alpha,
                            192,
                        )
                    )
                    if eta_interval_dk_check and eta_interval_dk_kernel == "residue-log":
                        combined_dG_over_eta = arb(
                            solver_module._combined_directional_derivative_residue_log_pair_divided_from_arb(
                                arb_A,
                                arb_alpha,
                                arb_eta,
                                direction_A,
                                direction_alpha,
                                arb(repr(float(left_weight))),
                                arb(repr(float(limit_solution.A))),
                                arb(repr(float(limit_solution.alpha))),
                                192,
                                base_delta_A,
                                base_delta_alpha,
                            )
                        )
                    elif eta_interval_dk_check:
                        combined_dG = arb(
                            solver_module._combined_contact_minus_one_directional_derivative_acb_from_arb(
                                arb_A,
                                arb_alpha,
                                arb_epsilon,
                                direction_A,
                                direction_alpha,
                                arb(repr(float(left_weight))),
                                192,
                            )
                        )
                        combined_dG_over_eta = combined_dG / arb_eta
                    else:
                        dG2 = arb(
                            solver_module._potential_minus_one_directional_derivative_acb_from_arb(
                                arb_A,
                                arb_alpha,
                                arb_epsilon,
                                direction_A,
                                direction_alpha,
                                192,
                            )
                        )
                        combined_dG = arb(repr(float(left_weight))) * dG1 + dG2
                    if direction_is_eta_scaled:
                        derivative_columns.append(
                            [
                                dG1 / arb_eta,
                                combined_dG / (arb_eta * arb_eta),
                            ]
                        )
                    else:
                        derivative_columns.append(
                            [
                                dG1,
                                combined_dG_over_eta,
                            ]
                        )
                    for value, name in (
                        [(dG1, "dU(alpha)"), (combined_dG_over_eta, "dH/eta")]
                        if eta_interval_dk_check
                        else [(dG1, "dU(alpha)"), (combined_dG, "dH")]
                    ):
                        if not value.is_finite():
                            fail(
                                f"slab {spec.eps_low:g}:{spec.eps_high:g} "
                                f"eta-slice={eta_index} u-subbox={u_index} v-subbox={v_index}: "
                                f"non-finite {name}/d{label} Arb ball"
                            )

                DK = [
                    [derivative_columns[0][0], derivative_columns[1][0]],
                    [derivative_columns[0][1], derivative_columns[1][1]],
                ]
                for row_idx in range(2):
                    for col_idx in range(2):
                        if not DK[row_idx][col_idx].is_finite():
                            fail(f"slab {spec.eps_low:g}:{spec.eps_high:g}: non-finite DK entry")
                        max_dk_entry_radius = max(max_dk_entry_radius, float(DK[row_idx][col_idx].rad()))
                for row_idx in range(2):
                    defect_action = 0.0
                    row_detail = []
                    for col_idx in range(2):
                        product_entry = arb(0)
                        for inner_idx in range(2):
                            product_entry += C_arb[row_idx][inner_idx] * DK[inner_idx][col_idx]
                        defect_entry = identity[row_idx][col_idx] - product_entry
                        entry_action = arb_abs_upper(
                            f"slab DK defect[{row_idx},{col_idx}]",
                            defect_entry,
                        ) * float(radii[col_idx])
                        defect_action += entry_action
                        row_detail.append(
                            (
                                f"entry[{row_idx},{col_idx}] "
                                f"action={entry_action:.6e} "
                                f"defect=[{float(defect_entry.lower()):.6e},{float(defect_entry.upper()):.6e}] "
                                f"DK=[{float(DK[0][col_idx].lower()):.6e},{float(DK[0][col_idx].upper()):.6e};"
                                f"{float(DK[1][col_idx].lower()):.6e},{float(DK[1][col_idx].upper()):.6e}]"
                            )
                        )
                    if defect_action > max_defect[row_idx]:
                        max_defect[row_idx] = defect_action
                        defect_source[row_idx] = (
                            f"eta_sample={eta_index},u_subbox={u_index},v_subbox={v_index},"
                            f"eta=[{eta_interval_low:.17g},{eta_interval_high:.17g}]"
                        )
                        defect_detail[row_idx] = tuple(row_detail)

    margin = finite_array("slab margin", radii - correction - max_defect)
    result = SlabResult(
        spec=spec,
        low_row=low_row,
        high_row=high_row,
        eta_subdivisions=eta_subdivisions,
        uv_subdivisions=uv_subdivisions,
        radii=radii,
        correction=correction,
        defect=max_defect,
        margin=margin,
        defect_source=(defect_source[0], defect_source[1]),
        max_dk_entry_radius=max_dk_entry_radius,
        min_sign_margin=min_sign_margin,
        eta_interval_dk_check=eta_interval_dk_check,
        center_correction_mode=center_correction_mode,
        worst_defect_detail=tuple(defect_detail[int(np.argmin(margin))]),
    )
    if min_sign_margin <= 0.0:
        idx = int(np.argmin(result.margin))
        label = "u" if idx == 0 else "v"
        dominant = "correction" if result.correction[idx] >= result.defect[idx] else "defect"
        fail(
            f"slab {spec.eps_low:g}:{spec.eps_high:g} rows={low_row.index}->{high_row.index}: "
            f"sign chart fails with min_sign_margin={min_sign_margin:.6e}; "
            f"Krawczyk component={label} margin={result.margin[idx]:.6e} "
            f"correction={result.correction[idx]:.6e} defect={result.defect[idx]:.6e} "
            f"radius={radii[idx]:.6e} dominant={dominant} "
            f"worst_defect_source={result.defect_source[idx]} "
            f"worst_defect_detail={' | '.join(result.worst_defect_detail)}"
        )
    if result.worst_margin <= 0.0:
        idx = int(np.argmin(result.margin))
        label = "u" if idx == 0 else "v"
        dominant = "correction" if result.correction[idx] >= result.defect[idx] else "defect"
        fail(
            f"slab {spec.eps_low:g}:{spec.eps_high:g} rows={low_row.index}->{high_row.index}: "
            f"FAIL component={label} margin={result.margin[idx]:.6e} "
            f"correction={result.correction[idx]:.6e} defect={result.defect[idx]:.6e} "
            f"radius={radii[idx]:.6e} dominant={dominant} "
            f"worst_defect_source={result.defect_source[idx]} "
            f"worst_defect_detail={' | '.join(result.worst_defect_detail)}"
        )
    return result


def report_dk11_eta_radius(
    spec: SlabSpec,
    rows: list[Any],
    limit_solution: Any,
    left_weight: float,
    null_slope: float,
    radii: np.ndarray,
    eta_counts: tuple[int, ...],
    uv_subdivisions: int,
    sample_grid_size: int,
    eta_interval_dk_kernel: str,
) -> None:
    from flint import arb

    solver_module = load_solver()
    low_row = find_endpoint(rows, spec.eps_low)
    high_row = find_endpoint(rows, spec.eps_high)
    if low_row.epsilon > high_row.epsilon:
        low_row, high_row = high_row, low_row
    assert_adjacent_endpoint_rows(rows, low_row, high_row)

    eta_low = math.sqrt(spec.eps_low)
    eta_high = math.sqrt(spec.eps_high)
    b_slope, b_intercept, tau_slope, tau_intercept = affine_coefficients(low_row, high_row)
    sample_grid = max(sample_grid_size, 2)

    print(
        "DK[1,1] ETA-INTERVAL RADIUS REPORT "
        f"slab={spec.eps_low:g}:{spec.eps_high:g} rows={low_row.index}->{high_row.index} "
        f"uv_subdivisions={uv_subdivisions} sample_grid={sample_grid} "
        f"kernel={eta_interval_dk_kernel} status=diagnostic-not-continuum-proof"
    )
    for eta_count in eta_counts:
        max_interval_radius = 0.0
        max_interval_width = 0.0
        max_sample_span = 0.0
        max_sample_radius = 0.0
        max_radius_inflation = 0.0
        max_sample_outside_gap = 0.0
        worst_source = "none"
        worst_interval = (math.nan, math.nan)
        worst_sample = (math.nan, math.nan)

        for eta_index, (eta_interval_low, eta_interval_high) in enumerate(eta_intervals(eta_low, eta_high, eta_count)):
            arb_eta = solver_module._arb_interval_from_bounds(eta_interval_low, eta_interval_high)
            arb_epsilon = solver_module._arb_interval_from_bounds(
                eta_interval_low * eta_interval_low,
                eta_interval_high * eta_interval_high,
            )
            for u_index in range(uv_subdivisions):
                u_low = -float(radii[0]) + 2.0 * float(radii[0]) * u_index / uv_subdivisions
                u_high = -float(radii[0]) + 2.0 * float(radii[0]) * (u_index + 1) / uv_subdivisions
                for v_index in range(uv_subdivisions):
                    v_low = -float(radii[1]) + 2.0 * float(radii[1]) * v_index / uv_subdivisions
                    v_high = -float(radii[1]) + 2.0 * float(radii[1]) * (v_index + 1) / uv_subdivisions
                    _A_low, _A_high, _alpha_low, _alpha_high = parameter_ranges(
                        eta_interval_low,
                        eta_interval_high,
                        u_low,
                        u_high,
                        v_low,
                        v_high,
                        limit_solution,
                        null_slope,
                        b_slope,
                        b_intercept,
                        tau_slope,
                        tau_intercept,
                    )
                    arb_A, arb_alpha, base_delta_A, base_delta_alpha = arb_affine_parameters(
                        solver_module,
                        arb,
                        arb_eta,
                        u_low,
                        u_high,
                        v_low,
                        v_high,
                        limit_solution,
                        null_slope,
                        b_slope,
                        b_intercept,
                        tau_slope,
                        tau_intercept,
                    )
                    if eta_interval_dk_kernel == "residue-log":
                        dk11 = arb(
                            solver_module._combined_directional_derivative_residue_log_pair_divided_from_arb(
                                arb_A,
                                arb_alpha,
                                arb_eta,
                                arb(repr(float(null_slope))),
                                arb(1),
                                arb(repr(float(left_weight))),
                                arb(repr(float(limit_solution.A))),
                                arb(repr(float(limit_solution.alpha))),
                                192,
                                base_delta_A,
                                base_delta_alpha,
                            )
                        )
                    else:
                        combined_dG = arb(
                            solver_module._combined_contact_minus_one_directional_derivative_acb_from_arb(
                                arb_A,
                                arb_alpha,
                                arb_epsilon,
                                arb(repr(float(null_slope))),
                                arb(1),
                                arb(repr(float(left_weight))),
                                192,
                            )
                        )
                        dk11 = combined_dG / arb_eta
                    if not dk11.is_finite():
                        fail(
                            f"slab {spec.eps_low:g}:{spec.eps_high:g} eta_count={eta_count} "
                            f"eta-slice={eta_index} u-subbox={u_index} v-subbox={v_index}: "
                            "non-finite DK[1,1] Arb ball"
                        )

                    sample_values = []
                    for eta_sample in np.linspace(eta_interval_low, eta_interval_high, sample_grid):
                        eta_f = float(eta_sample)
                        center_B, center_tau = center_at(eta_f, low_row, high_row)
                        for u_sample in np.linspace(u_low, u_high, sample_grid):
                            for v_sample in np.linspace(v_low, v_high, sample_grid):
                                J = finite_array(
                                    "sampled analytic DK",
                                    solver_module.analytic_rescaled_jacobian(
                                        center_B + float(u_sample),
                                        center_tau + float(v_sample),
                                        eta_f,
                                        limit_solution,
                                        left_weight,
                                        null_slope,
                                    ),
                                )
                                sample_values.append(float(J[1, 1]))
                    sample_low = min(sample_values)
                    sample_high = max(sample_values)
                    sample_span = sample_high - sample_low
                    sample_radius = 0.5 * sample_span
                    interval_low = float(dk11.lower())
                    interval_high = float(dk11.upper())
                    interval_width = interval_high - interval_low
                    interval_radius = float(dk11.rad())
                    outside_gap = max(sample_low - interval_high, interval_low - sample_high, 0.0)
                    if sample_radius > 0.0:
                        max_radius_inflation = max(max_radius_inflation, interval_radius / sample_radius)
                    max_sample_outside_gap = max(max_sample_outside_gap, outside_gap)
                    max_sample_span = max(max_sample_span, sample_span)
                    max_sample_radius = max(max_sample_radius, sample_radius)
                    max_interval_width = max(max_interval_width, interval_width)
                    if interval_radius > max_interval_radius:
                        max_interval_radius = interval_radius
                        worst_source = (
                            f"eta_slice={eta_index},u_subbox={u_index},v_subbox={v_index},"
                            f"eta=[{eta_interval_low:.17g},{eta_interval_high:.17g}]"
                        )
                        worst_interval = (interval_low, interval_high)
                        worst_sample = (sample_low, sample_high)

        print(
            f"  eta_subdivisions={eta_count} "
            f"max_interval_radius={max_interval_radius:.6e} "
            f"max_interval_width={max_interval_width:.6e} "
            f"max_sample_radius={max_sample_radius:.6e} "
            f"max_sample_span={max_sample_span:.6e} "
            f"max_radius_inflation={max_radius_inflation:.6e} "
            f"max_sample_outside_gap={max_sample_outside_gap:.6e} "
            f"worst_interval=[{worst_interval[0]:.6e},{worst_interval[1]:.6e}] "
            f"worst_sample=[{worst_sample[0]:.6e},{worst_sample[1]:.6e}] "
            f"worst_source={worst_source}"
        )


def adjacent_specs(rows: list[Any]) -> list[SlabSpec]:
    endpoints = sorted_endpoints(rows)
    if len(endpoints) < 2:
        fail("payload.rows: need at least two rows for adjacent slabs")
    return [SlabSpec(endpoints[i].epsilon, endpoints[i + 1].epsilon) for i in range(len(endpoints) - 1)]


def load_payload(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except OSError as exc:
        fail(f"{path}: cannot read JSON: {exc}")
    except json.JSONDecodeError as exc:
        fail(f"{path}: invalid JSON: {exc}")
    return require_mapping(payload, str(path))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("json_path", help="two-interval branch skeleton JSON")
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--slab", type=parse_slab, help="single epsilon slab as eps_low:eps_high")
    group.add_argument("--slabs", choices=["adjacent"], help="verify every adjacent stored epsilon slab")
    parser.add_argument("--center", choices=["affine-endpoints"], required=True)
    parser.add_argument("--uv-radii", type=lambda raw: parse_positive_pair(raw, "--uv-radii"), required=True)
    parser.add_argument(
        "--arb-box-dk-subdivisions",
        type=parse_subdivisions,
        default=(3, 5),
        help=(
            "eta sample count and uv subdivision count; uv count is used for both u and v. "
            "Eta is sampled diagnostically, not interval-enclosed."
        ),
    )
    parser.add_argument(
        "--eta-interval-dk-check",
        action="store_true",
        help=(
            "enclose DK over eta subintervals instead of sampled eta slices. "
            "The center correction remains sampled, so this is still diagnostic."
        ),
    )
    parser.add_argument(
        "--eta-interval-dk-kernel",
        choices=["acb", "residue-log"],
        default="acb",
        help=(
            "kernel for eta-interval DK[1,*] enclosure. "
            "The residue-log option is experimental and currently diagnostic."
        ),
    )
    parser.add_argument(
        "--center-correction",
        choices=["sampled", "interval"],
        default="sampled",
        help=(
            "How to bound C K(center). The interval mode encloses the center "
            "residual on eta subintervals with Arb/Acb."
        ),
    )
    parser.add_argument(
        "--dk11-eta-radius-report",
        type=parse_positive_int_list,
        help=(
            "print a DK[1,1]-focused eta-interval radius diagnostic for the given "
            "comma-separated eta subdivision counts and compare against sampled analytic DK"
        ),
    )
    parser.add_argument(
        "--dk11-sample-grid",
        type=int,
        default=3,
        help="sample points per eta/u/v axis for --dk11-eta-radius-report",
    )
    parser.add_argument("--quiet", action="store_true", help="print only the final binary diagnostic line")
    args = parser.parse_args()

    try:
        payload = load_payload(Path(args.json_path))
        rows_raw = payload.get("rows")
        if not isinstance(rows_raw, list) or not rows_raw:
            fail("payload.rows: expected non-empty list")
        limit_solution, left_weight, null_slope = payload_constants(payload)
        radii = finite_array("--uv-radii", args.uv_radii)
        eta_subdivisions, uv_subdivisions = args.arb_box_dk_subdivisions
        if args.dk11_sample_grid <= 0:
            fail("--dk11-sample-grid: expected positive integer")
        if args.dk11_eta_radius_report is not None:
            if args.slab is None:
                fail("--dk11-eta-radius-report currently requires a single --slab")
            report_dk11_eta_radius(
                args.slab,
                rows_raw,
                limit_solution,
                left_weight,
                null_slope,
                radii,
                args.dk11_eta_radius_report,
                uv_subdivisions,
                args.dk11_sample_grid,
                args.eta_interval_dk_kernel,
            )
            return 0
        specs = adjacent_specs(rows_raw) if args.slabs == "adjacent" else [args.slab]

        results = [
            verify_slab(
                spec,
                rows_raw,
                limit_solution,
                left_weight,
                null_slope,
                radii,
                eta_subdivisions,
                uv_subdivisions,
                args.eta_interval_dk_check,
                args.eta_interval_dk_kernel,
                args.center_correction,
            )
            for spec in specs
        ]
    except VerificationError as exc:
        print(f"TWO-INTERVAL EPSILON SLAB DIAGNOSTIC: FAIL ({exc})")
        return 1

    if not args.quiet:
        for result in results:
            print(
                f"slab={result.spec.eps_low:g}:{result.spec.eps_high:g} "
                f"rows={result.low_row.index}->{result.high_row.index} "
                f"margin=({result.margin[0]:.6e}, {result.margin[1]:.6e}) "
                f"correction=({result.correction[0]:.6e}, {result.correction[1]:.6e}) "
                f"defect=({result.defect[0]:.6e}, {result.defect[1]:.6e}) "
                f"min_sign={result.min_sign_margin:.6e} "
                f"max_DK_entry_radius={result.max_dk_entry_radius:.6e} "
                f"eta_DK_mode={'interval' if result.eta_interval_dk_check else 'sampled'} "
                f"center_correction={result.center_correction_mode} "
                f"worst_defect_source={result.defect_source[int(np.argmin(result.margin))]}"
            )

    worst = min(results, key=lambda item: item.worst_margin)
    print(
        "TWO-INTERVAL EPSILON SLAB DIAGNOSTIC: PASS "
        f"(slabs={len(results)}, worst_slab={worst.spec.eps_low:g}:{worst.spec.eps_high:g}, "
        f"rows={worst.low_row.index}->{worst.high_row.index}, "
        f"worst_margin={worst.worst_margin:.6e}, component={worst.limiting_component}, "
        f"dominant={worst.dominant_term}, "
        f"correction=({worst.correction[0]:.6e}, {worst.correction[1]:.6e}), "
        f"defect=({worst.defect[0]:.6e}, {worst.defect[1]:.6e}), "
        f"eta_samples_uv_subdivisions={worst.eta_subdivisions},{worst.uv_subdivisions}, "
        f"eta_DK_mode={'interval' if worst.eta_interval_dk_check else 'sampled'}, "
        f"center_correction={worst.center_correction_mode}, "
        f"worst_defect_source={worst.defect_source[int(np.argmin(worst.margin))]}, "
        "status=diagnostic-not-continuum-proof)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
