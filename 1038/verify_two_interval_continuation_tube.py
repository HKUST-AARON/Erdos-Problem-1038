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


def verify_tube(
    config: TubeConfig,
    rows: list[Any],
    limit_solution: Any,
    left_weight: float,
    null_slope: float,
    kernel: str,
    max_weighted_defect: float,
) -> tuple[float, str, float]:
    from flint import arb

    solver = v.load_solver()
    low_row = v.find_endpoint(rows, config.slab.eps_low)
    high_row = v.find_endpoint(rows, config.slab.eps_high)
    if low_row.epsilon > high_row.epsilon:
        low_row, high_row = high_row, low_row
    v.assert_adjacent_endpoint_rows(rows, low_row, high_row)

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
    return worst, worst_source, min_sign_margin


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("json_path", type=Path)
    parser.add_argument("--config", action="append", type=parse_tube_config, required=True)
    parser.add_argument("--eta-interval-dk-kernel", choices=["acb", "residue-log"], default="acb")
    parser.add_argument("--max-weighted-defect", type=float, default=0.95)
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
            value, source, sign_margin = verify_tube(
                config,
                rows,
                limit_solution,
                left_weight,
                null_slope,
                args.eta_interval_dk_kernel,
                args.max_weighted_defect,
            )
            label = f"{config.slab.eps_low:g}:{config.slab.eps_high:g}"
            print(
                f"tube={label} PASS weighted_defect={value:.6e} "
                f"radii=({config.radii[0]:.6e},{config.radii[1]:.6e}) "
                f"eta_uv={config.eta_subdivisions},{config.uv_subdivisions} "
                f"min_sign={sign_margin:.6e} worst_source={source}"
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
