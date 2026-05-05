#!/usr/bin/env python3
"""Continuation-tube diagnostic for the two-interval finite-gap branch.

This verifier checks the part of the continuation argument that does not
depend on evaluating the center residual.  For each epsilon slab it verifies
that the rescaled Jacobian stays uniformly invertible inside the tube

    (B, tau) = (B_c(eta), tau_c(eta)) + [-r_B,r_B] x [-r_tau,r_tau].

The checked quantity is the weighted defect norm

    max_i sum_j |(I - C(eta_mid) DK(tube, eta))_ij| r_j / r_i,

where C is the inverse of the center Jacobian at the eta slice midpoint.  If
this is < 1, the Krawczyk/degree map is uniformly nondegenerate on the tube.

This is not by itself the full existence proof: it is the matrix/invertibility
certificate needed by the continuation lemma that replaces sampled center
residuals.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np


ROOT = Path(__file__).resolve().parent
SLAB_VERIFIER_PATH = ROOT / "verify_two_interval_epsilon_slabs.py"


def load_slab_verifier() -> Any:
    spec = importlib.util.spec_from_file_location("verify_two_interval_epsilon_slabs", SLAB_VERIFIER_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import verifier from {SLAB_VERIFIER_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


v = load_slab_verifier()


@dataclass(frozen=True)
class TubeConfig:
    slab: Any
    radii: np.ndarray
    eta_subdivisions: int
    uv_subdivisions: int


def parse_tube_config(raw: str) -> TubeConfig:
    # Format: eps_low:eps_high:rB,rTau:eta,uv
    parts = raw.split(":")
    if len(parts) != 4:
        raise argparse.ArgumentTypeError("expected eps_low:eps_high:rB,rTau:eta,uv")
    slab = v.parse_slab(f"{parts[0]}:{parts[1]}")
    radii = np.asarray(v.parse_positive_pair(parts[2], "rB,rTau"), dtype=float)
    eta_subdivisions, uv_subdivisions = v.parse_subdivisions(parts[3])
    return TubeConfig(slab=slab, radii=radii, eta_subdivisions=eta_subdivisions, uv_subdivisions=uv_subdivisions)


def load_payload(path: Path) -> dict[str, Any]:
    return v.load_payload(path)


def endpoint_anchor_metrics(rows: list[Any], low_row: Any, high_row: Any, radii: np.ndarray) -> tuple[float, float, float]:
    """Return endpoint residual, sign, and normalized endpoint-step diagnostics."""

    def row_map(row: Any) -> dict[str, Any]:
        raw = v.require_mapping(rows[row.index], f"rows[{row.index}]")
        return raw

    max_residual = 0.0
    min_sign = float("inf")
    for endpoint in (low_row, high_row):
        raw = row_map(endpoint)
        solution = v.require_mapping(raw.get("solution"), f"rows[{endpoint.index}].solution")
        residuals = v.require_mapping(solution.get("residuals"), f"rows[{endpoint.index}].solution.residuals")
        max_residual = max(
            max_residual,
            abs(v.finite_float(residuals.get("U_alpha"), f"rows[{endpoint.index}].solution.residuals.U_alpha")),
            abs(v.finite_float(residuals.get("U_minus_one"), f"rows[{endpoint.index}].solution.residuals.U_minus_one")),
        )
        box = v.require_mapping(raw.get("krawczyk_box"), f"rows[{endpoint.index}].krawczyk_box")
        signs = v.require_mapping(box.get("sign_margins"), f"rows[{endpoint.index}].krawczyk_box.sign_margins")
        for key, value in signs.items():
            min_sign = min(min_sign, v.finite_float(value, f"rows[{endpoint.index}].krawczyk_box.sign_margins.{key}"))

    step_units = max(
        abs(high_row.B - low_row.B) / float(radii[0]),
        abs(high_row.tau - low_row.tau) / float(radii[1]),
    )
    return max_residual, min_sign, step_units


def sampled_boundary_degree(
    low_row: Any,
    high_row: Any,
    radii: np.ndarray,
    limit_solution: Any,
    left_weight: float,
    null_slope: float,
    eta_samples: int,
    edge_samples: int,
) -> tuple[int, float, float]:
    """Sample the winding of K on the tube boundary.

    This is a diagnostic existence probe, not an interval proof.  It is useful
    for deciding whether the next proof artifact should be a boundary-degree
    certificate or a different continuation bound.
    """

    if eta_samples <= 0 or edge_samples <= 0:
        return 0, float("inf"), 0.0
    solver = v.load_solver()
    eta_low = low_row.epsilon ** 0.5
    eta_high = high_row.epsilon ** 0.5
    worst_abs_degree = 10**9
    min_norm = float("inf")
    max_jump = 0.0
    for eta_index in range(eta_samples):
        eta = eta_low + (eta_high - eta_low) * (eta_index + 0.5) / eta_samples
        center_B, center_tau = v.center_at(eta, low_row, high_row)
        boundary: list[tuple[float, float]] = []
        for index in range(edge_samples):
            t = -1.0 + 2.0 * index / edge_samples
            boundary.append((center_B + float(radii[0]), center_tau + t * float(radii[1])))
        for index in range(edge_samples):
            t = 1.0 - 2.0 * index / edge_samples
            boundary.append((center_B + t * float(radii[0]), center_tau + float(radii[1])))
        for index in range(edge_samples):
            t = 1.0 - 2.0 * index / edge_samples
            boundary.append((center_B - float(radii[0]), center_tau + t * float(radii[1])))
        for index in range(edge_samples):
            t = -1.0 + 2.0 * index / edge_samples
            boundary.append((center_B + t * float(radii[0]), center_tau - float(radii[1])))
        values = np.asarray(
            [solver.rescaled_system(B, tau, eta, limit_solution, left_weight, null_slope) for B, tau in boundary],
            dtype=float,
        )
        if not np.all(np.isfinite(values)):
            v.fail(f"sampled boundary degree eta_index={eta_index}: non-finite K value")
        norms = np.linalg.norm(values, axis=1)
        min_norm = min(min_norm, float(np.min(norms)))
        angles = np.unwrap(np.arctan2(values[:, 1], values[:, 0]))
        jumps = np.abs(np.diff(np.r_[angles, angles[0] + 2.0 * np.pi * round((angles[-1] - angles[0]) / (2.0 * np.pi))]))
        max_jump = max(max_jump, float(np.max(jumps)))
        total_turn = angles[-1] - angles[0]
        closing_turn = np.angle(np.exp(1j * (angles[0] - angles[-1])))
        degree = int(round((total_turn + closing_turn) / (2.0 * np.pi)))
        worst_abs_degree = min(worst_abs_degree, abs(degree))
    return worst_abs_degree, min_norm, max_jump


def interval_boundary_exclusion(
    low_row: Any,
    high_row: Any,
    radii: np.ndarray,
    limit_solution: Any,
    left_weight: float,
    null_slope: float,
    eta_subdivisions: int,
    edge_subdivisions: int,
    value_kernel: str,
) -> tuple[float, str]:
    """Check the interval precondition 0 notin K(boundary tube boxes)."""

    if eta_subdivisions <= 0 or edge_subdivisions <= 0:
        return float("inf"), "disabled"
    from flint import arb

    solver = v.load_solver()
    eta_low = low_row.epsilon ** 0.5
    eta_high = high_row.epsilon ** 0.5
    b_slope, b_intercept, tau_slope, tau_intercept = v.affine_coefficients(low_row, high_row)
    worst_separation = float("inf")
    worst_source = "none"

    def component_separation(value: Any) -> float:
        lower = float(value.lower())
        upper = float(value.upper())
        if lower <= 0.0 <= upper:
            return 0.0
        return min(abs(lower), abs(upper))

    def sampled_lipschitz_component(
        eta_interval_low: float,
        eta_interval_high: float,
        u_low: float,
        u_high: float,
        tau_low: float,
        tau_high: float,
    ) -> tuple[Any, Any]:
        eta_mid = (eta_interval_low + eta_interval_high) / 2.0
        u_mid = (u_low + u_high) / 2.0
        tau_mid = (tau_low + tau_high) / 2.0
        center_B, center_tau = v.center_at(eta_mid, low_row, high_row)
        K_mid = np.asarray(
            solver.rescaled_system(
                center_B + u_mid,
                center_tau + tau_mid,
                eta_mid,
                limit_solution,
                left_weight,
                null_slope,
            ),
            dtype=float,
        )
        if not np.all(np.isfinite(K_mid)):
            v.fail("sampled-lipschitz value kernel: non-finite midpoint K")
        arb_eta = solver._arb_interval_from_bounds(eta_interval_low, eta_interval_high)
        arb_epsilon = solver._arb_interval_from_bounds(eta_interval_low * eta_interval_low, eta_interval_high * eta_interval_high)
        arb_A, arb_alpha, base_delta_A, base_delta_alpha = v.arb_affine_parameters(
            solver,
            arb,
            arb_eta,
            u_low,
            u_high,
            tau_low,
            tau_high,
            limit_solution,
            null_slope,
            b_slope,
            b_intercept,
            tau_slope,
            tau_intercept,
        )
        columns = []
        for direction_A, direction_alpha in ((arb(1), arb(0)), (arb(repr(float(null_slope))), arb(1))):
            dG1 = arb(
                solver._contact_directional_derivative_acb_from_arb(
                    arb_A, arb_alpha, arb_epsilon, direction_A, direction_alpha, 192
                )
            )
            dH_over_eta = arb(
                solver._combined_directional_derivative_residue_log_pair_divided_from_arb(
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
            columns.append([dG1, dH_over_eta])
        DK = [[columns[0][0], columns[1][0]], [columns[0][1], columns[1][1]]]
        u_radius = max(abs(u_mid - u_low), abs(u_high - u_mid))
        tau_radius = max(abs(tau_mid - tau_low), abs(tau_high - tau_mid))
        # Eta variation is intentionally sampled; this is diagnostic only.
        eta_radius = max(abs(eta_mid - eta_interval_low), abs(eta_interval_high - eta_mid))
        eta_samples = []
        if eta_radius > 0.0:
            for eta_sample in (eta_interval_low, eta_interval_high):
                sample_center_B, sample_center_tau = v.center_at(eta_sample, low_row, high_row)
                eta_samples.append(
                    np.asarray(
                        solver.rescaled_system(
                            sample_center_B + u_mid,
                            sample_center_tau + tau_mid,
                            eta_sample,
                            limit_solution,
                            left_weight,
                            null_slope,
                        ),
                        dtype=float,
                    )
                )
        eta_error = np.zeros(2)
        if eta_samples:
            eta_error = np.max(np.abs(np.asarray(eta_samples) - K_mid), axis=0)
        values = []
        for row_idx in range(2):
            radius = (
                v.arb_abs_upper("sampled-lipschitz DK", DK[row_idx][0]) * u_radius
                + v.arb_abs_upper("sampled-lipschitz DK", DK[row_idx][1]) * tau_radius
                + float(eta_error[row_idx])
            )
            values.append(arb(repr(float(K_mid[row_idx]))) + arb(f"[+/- {radius!r}]"))
        return values[0], values[1]

    def check_box(
        eta_interval_low: float,
        eta_interval_high: float,
        u_low: float,
        u_high: float,
        tau_low: float,
        tau_high: float,
        source: str,
    ) -> None:
        nonlocal worst_separation, worst_source
        arb_eta = solver._arb_interval_from_bounds(eta_interval_low, eta_interval_high)
        arb_epsilon = solver._arb_interval_from_bounds(eta_interval_low * eta_interval_low, eta_interval_high * eta_interval_high)
        arb_A, arb_alpha, _base_delta_A, _base_delta_alpha = v.arb_affine_parameters(
            solver,
            arb,
            arb_eta,
            u_low,
            u_high,
            tau_low,
            tau_high,
            limit_solution,
            null_slope,
            b_slope,
            b_intercept,
            tau_slope,
            tau_intercept,
        )
        if value_kernel == "direct":
            U_alpha = arb(solver._contact_potential_acb_from_arb(arb_A, arb_alpha, arb_epsilon, 192))
            H = arb(
                solver._combined_contact_minus_one_potential_acb_from_arb(
                    arb_A,
                    arb_alpha,
                    arb_epsilon,
                    arb(repr(float(left_weight))),
                    192,
                )
            )
            K1 = U_alpha / arb_eta
            K2 = H / (arb_eta * arb_eta)
        elif value_kernel == "sampled-lipschitz":
            K1, K2 = sampled_lipschitz_component(
                eta_interval_low,
                eta_interval_high,
                u_low,
                u_high,
                tau_low,
                tau_high,
            )
        else:
            v.fail(f"interval boundary exclusion {source}: unknown value kernel {value_kernel!r}")
        if not K1.is_finite() or not K2.is_finite():
            v.fail(f"interval boundary exclusion {source}: non-finite K value")
        sep = max(component_separation(K1), component_separation(K2))
        if sep <= 0.0:
            v.fail(f"interval boundary exclusion {source}: both K components contain 0; K1={K1}, K2={K2}")
        if sep < worst_separation:
            worst_separation = sep
            worst_source = source

    for eta_index, (eta_interval_low, eta_interval_high) in enumerate(v.eta_intervals(eta_low, eta_high, eta_subdivisions)):
        for edge_index in range(edge_subdivisions):
            t0 = -1.0 + 2.0 * edge_index / edge_subdivisions
            t1 = -1.0 + 2.0 * (edge_index + 1) / edge_subdivisions
            check_box(
                eta_interval_low,
                eta_interval_high,
                float(radii[0]),
                float(radii[0]),
                t0 * float(radii[1]),
                t1 * float(radii[1]),
                f"eta={eta_index},right={edge_index}",
            )
            check_box(
                eta_interval_low,
                eta_interval_high,
                t0 * float(radii[0]),
                t1 * float(radii[0]),
                float(radii[1]),
                float(radii[1]),
                f"eta={eta_index},top={edge_index}",
            )
            check_box(
                eta_interval_low,
                eta_interval_high,
                -float(radii[0]),
                -float(radii[0]),
                t0 * float(radii[1]),
                t1 * float(radii[1]),
                f"eta={eta_index},left={edge_index}",
            )
            check_box(
                eta_interval_low,
                eta_interval_high,
                t0 * float(radii[0]),
                t1 * float(radii[0]),
                -float(radii[1]),
                -float(radii[1]),
                f"eta={eta_index},bottom={edge_index}",
            )
    return worst_separation, worst_source


def verify_tube(
    config: TubeConfig,
    rows: list[Any],
    limit_solution: Any,
    left_weight: float,
    null_slope: float,
    kernel: str,
    max_weighted_defect: float,
    boundary_degree_samples: tuple[int, int],
    interval_boundary_subdivisions: tuple[int, int],
    interval_boundary_value_kernel: str,
) -> tuple[float, str, float, float, float, float, int, float, float, float, str]:
    from flint import arb

    solver = v.load_solver()
    low_row = v.find_endpoint(rows, config.slab.eps_low)
    high_row = v.find_endpoint(rows, config.slab.eps_high)
    if low_row.epsilon > high_row.epsilon:
        low_row, high_row = high_row, low_row
    v.assert_adjacent_endpoint_rows(rows, low_row, high_row)
    endpoint_residual, endpoint_sign, endpoint_step_units = endpoint_anchor_metrics(rows, low_row, high_row, config.radii)
    sampled_degree, sampled_boundary_min_norm, sampled_boundary_max_jump = sampled_boundary_degree(
        low_row,
        high_row,
        config.radii,
        limit_solution,
        left_weight,
        null_slope,
        boundary_degree_samples[0],
        boundary_degree_samples[1],
    )
    interval_boundary_sep, interval_boundary_source = interval_boundary_exclusion(
        low_row,
        high_row,
        config.radii,
        limit_solution,
        left_weight,
        null_slope,
        interval_boundary_subdivisions[0],
        interval_boundary_subdivisions[1],
        interval_boundary_value_kernel,
    )

    eta_low = low_row.epsilon ** 0.5
    eta_high = high_row.epsilon ** 0.5
    b_slope, b_intercept, tau_slope, tau_intercept = v.affine_coefficients(low_row, high_row)
    identity = [[arb(1), arb(0)], [arb(0), arb(1)]]
    worst = 0.0
    worst_source = "none"
    min_sign_margin = float("inf")

    eta_items = tuple(
        (eta_interval_low, eta_interval_high, (eta_interval_low + eta_interval_high) / 2.0)
        for eta_interval_low, eta_interval_high in v.eta_intervals(eta_low, eta_high, config.eta_subdivisions)
    )
    for eta_index, (eta_interval_low, eta_interval_high, eta_sample) in enumerate(eta_items):
        B_sample, tau_sample = v.center_at(eta_sample, low_row, high_row)
        J_sample = v.finite_array(
            "tube center DK",
            solver.analytic_rescaled_jacobian(B_sample, tau_sample, eta_sample, limit_solution, left_weight, null_slope),
        )
        try:
            C_sample = np.linalg.inv(J_sample)
        except np.linalg.LinAlgError as exc:
            v.fail(f"eta-slice {eta_index}: center Jacobian is singular: {exc}")
        C_arb = [[arb(repr(float(C_sample[i, j]))) for j in range(2)] for i in range(2)]

        for u_index in range(config.uv_subdivisions):
            u_low = -float(config.radii[0]) + 2.0 * float(config.radii[0]) * u_index / config.uv_subdivisions
            u_high = -float(config.radii[0]) + 2.0 * float(config.radii[0]) * (u_index + 1) / config.uv_subdivisions
            for vv_index in range(config.uv_subdivisions):
                tau_low = -float(config.radii[1]) + 2.0 * float(config.radii[1]) * vv_index / config.uv_subdivisions
                tau_high = -float(config.radii[1]) + 2.0 * float(config.radii[1]) * (vv_index + 1) / config.uv_subdivisions
                A_low, A_high, alpha_low, alpha_high = v.parameter_ranges(
                    eta_interval_low,
                    eta_interval_high,
                    u_low,
                    u_high,
                    tau_low,
                    tau_high,
                    limit_solution,
                    null_slope,
                    b_slope,
                    b_intercept,
                    tau_slope,
                    tau_intercept,
                )
                min_sign_margin = min(
                    min_sign_margin,
                    v.slab_sign_margin(config.slab.eps_low, config.slab.eps_high, A_low, A_high, alpha_low, alpha_high),
                )
                arb_eta = solver._arb_interval_from_bounds(eta_interval_low, eta_interval_high)
                arb_epsilon = solver._arb_interval_from_bounds(eta_interval_low * eta_interval_low, eta_interval_high * eta_interval_high)
                arb_A, arb_alpha, base_delta_A, base_delta_alpha = v.arb_affine_parameters(
                    solver,
                    arb,
                    arb_eta,
                    u_low,
                    u_high,
                    tau_low,
                    tau_high,
                    limit_solution,
                    null_slope,
                    b_slope,
                    b_intercept,
                    tau_slope,
                    tau_intercept,
                )
                columns = []
                for direction_A, direction_alpha in ((arb(1), arb(0)), (arb(repr(float(null_slope))), arb(1))):
                    dG1 = arb(
                        solver._contact_directional_derivative_acb_from_arb(
                            arb_A, arb_alpha, arb_epsilon, direction_A, direction_alpha, 192
                        )
                    )
                    if kernel == "residue-log":
                        dH_over_eta = arb(
                            solver._combined_directional_derivative_residue_log_pair_divided_from_arb(
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
                    else:
                        dH = arb(
                            solver._combined_contact_minus_one_directional_derivative_acb_from_arb(
                                arb_A, arb_alpha, arb_epsilon, direction_A, direction_alpha, arb(repr(float(left_weight))), 192
                            )
                        )
                        dH_over_eta = dH / arb_eta
                    columns.append([dG1, dH_over_eta])
                DK = [[columns[0][0], columns[1][0]], [columns[0][1], columns[1][1]]]
                for row_idx in range(2):
                    row_sum = 0.0
                    for col_idx in range(2):
                        product = arb(0)
                        for inner_idx in range(2):
                            product += C_arb[row_idx][inner_idx] * DK[inner_idx][col_idx]
                        defect = identity[row_idx][col_idx] - product
                        row_sum += v.arb_abs_upper("tube DK defect", defect) * float(config.radii[col_idx]) / float(config.radii[row_idx])
                    if row_sum > worst:
                        worst = row_sum
                        worst_source = (
                            f"eta={eta_index},u={u_index},v={vv_index},"
                            f"eta_interval=[{eta_interval_low:.17g},{eta_interval_high:.17g}]"
                        )
    if min_sign_margin <= 0.0:
        v.fail(f"slab {config.slab.eps_low:g}:{config.slab.eps_high:g}: sign margin {min_sign_margin:.6e} <= 0")
    if worst >= max_weighted_defect:
        v.fail(
            f"slab {config.slab.eps_low:g}:{config.slab.eps_high:g}: weighted defect {worst:.6e} "
            f">= threshold {max_weighted_defect:.6e}; worst_source={worst_source}"
        )
    return (
        worst,
        worst_source,
        min_sign_margin,
        endpoint_residual,
        endpoint_sign,
        endpoint_step_units,
        sampled_degree,
        sampled_boundary_min_norm,
        sampled_boundary_max_jump,
        interval_boundary_sep,
        interval_boundary_source,
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("json_path", type=Path)
    parser.add_argument("--config", action="append", type=parse_tube_config, required=True)
    parser.add_argument("--eta-interval-dk-kernel", choices=["acb", "residue-log"], default="acb")
    parser.add_argument("--max-weighted-defect", type=float, default=0.95)
    parser.add_argument(
        "--sample-boundary-degree",
        type=v.parse_subdivisions,
        default=(0, 0),
        metavar="ETA,EDGE",
        help="Diagnostic only: sample K on the tube boundary at ETA eta slices and EDGE points per edge.",
    )
    parser.add_argument(
        "--interval-boundary-exclusion",
        type=v.parse_subdivisions,
        default=(0, 0),
        metavar="ETA,EDGE",
        help="Interval precondition check: subdivide the tube boundary and verify 0 is outside every K box.",
    )
    parser.add_argument(
        "--interval-boundary-value-kernel",
        choices=["direct", "sampled-lipschitz"],
        default="direct",
        help="Value kernel used by --interval-boundary-exclusion.",
    )
    args = parser.parse_args()

    try:
        payload = load_payload(args.json_path)
        rows = payload.get("rows")
        if not isinstance(rows, list) or not rows:
            v.fail("payload.rows: expected non-empty list")
        limit_solution, left_weight, null_slope = v.payload_constants(payload)
        worst = -1.0
        worst_label = "none"
        for config in args.config:
            (
                value,
                source,
                sign_margin,
                endpoint_residual,
                endpoint_sign,
                endpoint_step_units,
                sampled_degree,
                sampled_boundary_min_norm,
                sampled_boundary_max_jump,
                interval_boundary_sep,
                interval_boundary_source,
            ) = verify_tube(
                config,
                rows,
                limit_solution,
                left_weight,
                null_slope,
                args.eta_interval_dk_kernel,
                args.max_weighted_defect,
                args.sample_boundary_degree,
                args.interval_boundary_exclusion,
                args.interval_boundary_value_kernel,
            )
            label = f"{config.slab.eps_low:g}:{config.slab.eps_high:g}"
            print(
                f"tube={label} PASS weighted_defect={value:.6e} "
                f"radii=({config.radii[0]:.6e},{config.radii[1]:.6e}) "
                f"eta_uv={config.eta_subdivisions},{config.uv_subdivisions} "
                f"min_sign={sign_margin:.6e} "
                f"endpoint_residual={endpoint_residual:.6e} "
                f"endpoint_sign={endpoint_sign:.6e} "
                f"endpoint_step_units={endpoint_step_units:.6e} "
                f"sampled_degree_abs={sampled_degree:d} "
                f"sampled_boundary_min_norm={sampled_boundary_min_norm:.6e} "
                f"sampled_boundary_max_jump={sampled_boundary_max_jump:.6e} "
                f"interval_boundary_sep={interval_boundary_sep:.6e} "
                f"interval_boundary_source={interval_boundary_source} "
                f"worst_source={source}"
            )
            if value > worst:
                worst = value
                worst_label = label
    except v.VerificationError as exc:
        print(f"TWO-INTERVAL CONTINUATION TUBE: FAIL ({exc})")
        return 1

    print(f"TWO-INTERVAL CONTINUATION TUBE: PASS configs={len(args.config)} worst={worst:.6e} worst_slab={worst_label}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
