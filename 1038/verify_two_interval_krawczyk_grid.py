#!/usr/bin/env python3
"""Deterministic grid stress verifier for two-interval Krawczyk boxes.

This reads the exported two-interval branch skeleton JSON and checks each
stored ``krawczyk_box`` by sampling the full ``(B, tau)`` box on a configurable
tensor grid.  For every row it recomputes the rescaled system ``K`` and the
analytic ``D_(B,tau) K`` from ``solve_two_interval_finite_gap.py``.

The checked inclusion condition deliberately matches the existing sampled
Krawczyk diagnostic:

    abs(C K(center)) + max_grid(abs(I - C DK(grid_point)) @ radii) < radii,

where ``C`` is the inverse of the analytic Jacobian at the box center.  A
positive minimum-margin threshold is used as a stress safety factor.

Important caveat: this is deterministic sampled stress evidence, not an
outward-rounded interval Krawczyk proof.  It does not enclose all floating-point
roundoff or all unsampled points in the box.
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
DEFAULT_JSON = ROOT / "two_interval_branch_certificate_skeleton.json"
SOLVER_PATH = ROOT / "solve_two_interval_finite_gap.py"

spec = importlib.util.spec_from_file_location("solve_two_interval_finite_gap", SOLVER_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot import solver from {SOLVER_PATH}")
solver = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = solver
spec.loader.exec_module(solver)


class VerificationError(Exception):
    pass


@dataclass(frozen=True)
class GridResult:
    row_index: int
    epsilon: float
    grid_size: int
    radii: np.ndarray
    correction: np.ndarray
    inclusion: np.ndarray
    margin: np.ndarray
    contraction: float
    max_abs_k: np.ndarray
    max_abs_c_k: np.ndarray
    sampled_defect_action: np.ndarray
    inverse_abs_row_sums: np.ndarray

    @property
    def worst_margin(self) -> float:
        return float(np.min(self.margin))


@dataclass(frozen=True)
class RefinementRowResult:
    row_index: int
    epsilon: float
    grid_results: tuple[GridResult, ...]
    max_drift: float


@dataclass(frozen=True)
class ObligationBudget:
    row_index: int
    epsilon: float
    grid_size: int
    worst_margin: float
    uniform_center_k_budget: float
    uniform_dk_entry_budget: float

    @property
    def limiting_budget(self) -> float:
        return min(self.uniform_center_k_budget, self.uniform_dk_entry_budget)


def fail(message: str) -> None:
    raise VerificationError(message)


def require_mapping(value: Any, path: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        fail(f"{path}: expected object, got {type(value).__name__}")
    return value


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


def row_context(row_index: int, epsilon: float, B: float | None = None, tau: float | None = None) -> str:
    context = f"rows[{row_index}] eps={epsilon:g}"
    if B is not None and tau is not None:
        context += f" B={B:.17g} tau={tau:.17g}"
    return context


def finite_array(
    name: str,
    value: Any,
    row_index: int,
    epsilon: float,
    B: float | None = None,
    tau: float | None = None,
) -> np.ndarray:
    try:
        array = np.asarray(value, dtype=float)
    except (TypeError, ValueError) as exc:
        fail(f"{row_context(row_index, epsilon, B, tau)}: {name} is not numeric: {exc}")
    if not np.all(np.isfinite(array)):
        fail(f"{row_context(row_index, epsilon, B, tau)}: non-finite {name}: {array!r}")
    return array


def finite_scalar(
    name: str,
    value: Any,
    row_index: int,
    epsilon: float,
    B: float | None = None,
    tau: float | None = None,
) -> float:
    try:
        result = float(value)
    except (TypeError, ValueError) as exc:
        fail(f"{row_context(row_index, epsilon, B, tau)}: {name} is not numeric: {exc}")
    if not math.isfinite(result):
        fail(f"{row_context(row_index, epsilon, B, tau)}: non-finite {name}: {result!r}")
    return result


def load_payload(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except OSError as exc:
        fail(f"{path}: cannot read JSON: {exc}")
    except json.JSONDecodeError as exc:
        fail(f"{path}: invalid JSON: {exc}")
    return require_mapping(payload, str(path))


def payload_constants(payload: dict[str, Any]) -> tuple[Any, float, float]:
    limit_raw = require_mapping(payload.get("limit_solution"), "payload.limit_solution")
    fold_raw = require_mapping(payload.get("fold"), "payload.fold")
    limit_solution = solver.LimitSolution(
        A=finite_float(limit_raw.get("A"), "payload.limit_solution.A"),
        alpha=finite_float(limit_raw.get("alpha"), "payload.limit_solution.alpha"),
        mass_ell=0.0,
        mass_r=0.0,
        density_mass=0.0,
        residual_alpha=0.0,
        residual_minus_one=0.0,
    )
    left_weight = finite_float(fold_raw.get("left_weight"), "payload.fold.left_weight")
    null_slope = finite_float(fold_raw.get("null_slope"), "payload.fold.null_slope")
    return limit_solution, left_weight, null_slope


def grid_values(center: float, radius: float, grid_size: int) -> np.ndarray:
    if radius <= 0.0:
        fail(f"grid radius must be positive, got {radius:.17g}")
    return np.linspace(center - radius, center + radius, grid_size)


def verify_row(
    row_index: int,
    raw_row: Any,
    limit_solution: Any,
    left_weight: float,
    null_slope: float,
    grid_size: int,
    min_margin: float,
    max_contraction: float,
) -> GridResult:
    row = require_mapping(raw_row, f"rows[{row_index}]")
    epsilon = finite_float(row.get("epsilon"), f"rows[{row_index}].epsilon")
    if epsilon <= 0.0:
        fail(f"rows[{row_index}].epsilon: expected positive value, got {epsilon:.17g}")
    eta = math.sqrt(epsilon)

    box = require_mapping(row.get("krawczyk_box"), f"rows[{row_index}].krawczyk_box")
    center = require_mapping(box.get("center"), f"rows[{row_index}].krawczyk_box.center")
    radii_raw = require_mapping(box.get("radii"), f"rows[{row_index}].krawczyk_box.radii")
    B0 = finite_float(center.get("B"), f"rows[{row_index}].krawczyk_box.center.B")
    tau0 = finite_float(center.get("tau"), f"rows[{row_index}].krawczyk_box.center.tau")
    radii = np.array(
        [
            finite_float(radii_raw.get("B"), f"rows[{row_index}].krawczyk_box.radii.B"),
            finite_float(radii_raw.get("tau"), f"rows[{row_index}].krawczyk_box.radii.tau"),
        ]
    )
    if np.any(radii <= 0.0):
        fail(f"rows[{row_index}]: krawczyk radii must be positive, got {radii.tolist()}")

    center_value = finite_array(
        "center K value",
        solver.rescaled_system(B0, tau0, eta, limit_solution, left_weight, null_slope),
        row_index,
        epsilon,
        B0,
        tau0,
    )
    center_jacobian = finite_array(
        "center analytic Jacobian",
        solver.analytic_rescaled_jacobian(B0, tau0, eta, limit_solution, left_weight, null_slope),
        row_index,
        epsilon,
        B0,
        tau0,
    )
    try:
        C = finite_array("center inverse C", np.linalg.inv(center_jacobian), row_index, epsilon, B0, tau0)
    except np.linalg.LinAlgError as exc:
        fail(f"rows[{row_index}] eps={epsilon:g}: center Jacobian is singular: {exc}")
    correction = finite_array("center correction", np.abs(C @ center_value), row_index, epsilon, B0, tau0)
    inverse_abs_row_sums = finite_array(
        "center inverse absolute row sums",
        np.sum(np.abs(C), axis=1),
        row_index,
        epsilon,
        B0,
        tau0,
    )
    if np.any(inverse_abs_row_sums <= 0.0):
        fail(
            f"rows[{row_index}] eps={epsilon:g}: inverse absolute row sums must be positive, "
            f"got {inverse_abs_row_sums!r}"
        )

    max_abs_k = np.zeros(2)
    max_abs_c_k = np.zeros(2)
    sampled_defect_action = np.zeros(2)
    identity = np.eye(2)
    B_grid = grid_values(B0, float(radii[0]), grid_size)
    tau_grid = grid_values(tau0, float(radii[1]), grid_size)
    for B in B_grid:
        for tau in tau_grid:
            sample_B = float(B)
            sample_tau = float(tau)
            value = finite_array(
                "sampled K value",
                solver.rescaled_system(sample_B, sample_tau, eta, limit_solution, left_weight, null_slope),
                row_index,
                epsilon,
                sample_B,
                sample_tau,
            )
            jacobian = finite_array(
                "sampled analytic Jacobian",
                solver.analytic_rescaled_jacobian(
                    sample_B,
                    sample_tau,
                    eta,
                    limit_solution,
                    left_weight,
                    null_slope,
                ),
                row_index,
                epsilon,
                sample_B,
                sample_tau,
            )
            defect_action = finite_array(
                "sampled defect action",
                np.abs(identity - C @ jacobian) @ radii,
                row_index,
                epsilon,
                sample_B,
                sample_tau,
            )
            c_value = finite_array(
                "sampled C K value",
                C @ value,
                row_index,
                epsilon,
                sample_B,
                sample_tau,
            )
            max_abs_k = np.maximum(max_abs_k, np.abs(value))
            max_abs_c_k = np.maximum(max_abs_c_k, np.abs(c_value))
            sampled_defect_action = np.maximum(sampled_defect_action, defect_action)

    inclusion = finite_array(
        "final inclusion",
        correction + sampled_defect_action,
        row_index,
        epsilon,
    )
    margin = finite_array(
        "final margin",
        radii - inclusion,
        row_index,
        epsilon,
    )
    contraction = finite_scalar(
        "final contraction",
        np.max(sampled_defect_action / radii),
        row_index,
        epsilon,
    )
    if float(np.min(margin)) < min_margin:
        fail(
            f"rows[{row_index}] eps={epsilon:g}: Krawczyk grid margin "
            f"{float(np.min(margin)):.6e} < threshold {min_margin:.6e}; "
            f"component margins=({float(margin[0]):.6e}, {float(margin[1]):.6e})"
        )
    if contraction > max_contraction:
        fail(
            f"rows[{row_index}] eps={epsilon:g}: Krawczyk grid contraction "
            f"{contraction:.6e} > threshold {max_contraction:.6e}"
        )

    return GridResult(
        row_index=row_index,
        epsilon=epsilon,
        grid_size=grid_size,
        radii=radii,
        correction=correction,
        inclusion=inclusion,
        margin=margin,
        contraction=contraction,
        max_abs_k=max_abs_k,
        max_abs_c_k=max_abs_c_k,
        sampled_defect_action=sampled_defect_action,
        inverse_abs_row_sums=inverse_abs_row_sums,
    )


def positive_int(value: str) -> int:
    try:
        result = int(value)
    except ValueError as exc:
        raise argparse.ArgumentTypeError(f"expected integer, got {value!r}") from exc
    if result < 2:
        raise argparse.ArgumentTypeError("grid size must be at least 2")
    return result


def refine_grid_sizes(value: str) -> tuple[int, ...]:
    parts = [part.strip() for part in value.split(",")]
    if len(parts) < 2 or any(part == "" for part in parts):
        raise argparse.ArgumentTypeError(
            "--refine-grid-sizes must contain at least two strictly increasing grid sizes, e.g. 11,21,41"
        )
    if len(parts) > 16:
        raise argparse.ArgumentTypeError("--refine-grid-sizes accepts at most 16 grid sizes")

    sizes: list[int] = []
    for part in parts:
        try:
            size = int(part)
        except ValueError as exc:
            raise argparse.ArgumentTypeError(f"--refine-grid-sizes entry {part!r} is not an integer") from exc
        if size < 2:
            raise argparse.ArgumentTypeError(
                f"--refine-grid-sizes entry {size} is invalid; every grid size must be at least 2"
            )
        if sizes and size <= sizes[-1]:
            raise argparse.ArgumentTypeError(
                "--refine-grid-sizes must be strictly increasing; "
                f"got {sizes[-1]} followed by {size}"
            )
        sizes.append(size)

    return tuple(sizes)


def nonnegative_float(value: str) -> float:
    try:
        result = float(value)
    except ValueError as exc:
        raise argparse.ArgumentTypeError(f"expected float, got {value!r}") from exc
    if result < 0.0 or not math.isfinite(result):
        raise argparse.ArgumentTypeError("value must be finite and nonnegative")
    return result


def positive_float(value: str) -> float:
    result = nonnegative_float(value)
    if result <= 0.0:
        raise argparse.ArgumentTypeError("value must be positive")
    return result


def refinement_drift(previous: GridResult, current: GridResult) -> float:
    margin_drift = float(np.max(np.abs(current.margin - previous.margin)))
    contraction_drift = abs(current.contraction - previous.contraction)
    return max(margin_drift, contraction_drift)


def obligation_budget(result: GridResult) -> ObligationBudget:
    """Translate unused Krawczyk margin into interval-kernel error budgets.

    This is not an interval proof.  It answers a narrower engineering question:
    if the future outward-rounded proof spends half of the current margin on
    enclosing the center residual ``K(center)`` and half on enclosing the
    Jacobian defect action, how much uniform component error can each primitive
    tolerate?

    The budgets are in rescaled coordinates:

    * ``uniform_center_k_budget`` bounds an added uniform radius for each
      component of ``K(center)`` before multiplication by ``C``;
    * ``uniform_dk_entry_budget`` bounds an added uniform radius for every entry
      of ``DK`` over the parameter box.
    """

    half_margin = 0.5 * result.margin
    row_sums = result.inverse_abs_row_sums
    radius_sum = float(np.sum(result.radii))
    if radius_sum <= 0.0:
        fail(f"rows[{result.row_index}] eps={result.epsilon:g}: nonpositive radius sum {radius_sum:.17g}")
    center_budgets = half_margin / row_sums
    dk_entry_budgets = half_margin / (row_sums * radius_sum)
    return ObligationBudget(
        row_index=result.row_index,
        epsilon=result.epsilon,
        grid_size=result.grid_size,
        worst_margin=result.worst_margin,
        uniform_center_k_budget=float(np.min(center_budgets)),
        uniform_dk_entry_budget=float(np.min(dk_entry_budgets)),
    )


def print_obligation_report(results: list[GridResult]) -> None:
    budgets = [obligation_budget(result) for result in results]
    worst_center = min(budgets, key=lambda item: item.uniform_center_k_budget)
    worst_dk = min(budgets, key=lambda item: item.uniform_dk_entry_budget)
    worst_margin = min(budgets, key=lambda item: item.worst_margin)
    print(
        "TWO-INTERVAL KRAWCZYK INTERVALIZATION BUDGET "
        f"(rows={len(budgets)}, margin_split=centerK:0.5,DK:0.5, "
        f"worst_margin={worst_margin.worst_margin:.6e} at row {worst_margin.row_index}, "
        f"min_uniform_center_K_radius={worst_center.uniform_center_k_budget:.6e} "
        f"at row {worst_center.row_index}, "
        f"min_uniform_DK_entry_radius={worst_dk.uniform_dk_entry_budget:.6e} "
        f"at row {worst_dk.row_index}, "
        "caveat=budget for future outward-rounded primitives, not a proof)"
    )


def verify_row_refinement(
    row_index: int,
    row: Any,
    limit_solution: Any,
    left_weight: float,
    null_slope: float,
    grid_sizes: tuple[int, ...],
    min_margin: float,
    max_contraction: float,
    max_refinement_drift: float,
) -> RefinementRowResult:
    grid_results = tuple(
        verify_row(
            row_index,
            row,
            limit_solution,
            left_weight,
            null_slope,
            grid_size,
            min_margin,
            max_contraction,
        )
        for grid_size in grid_sizes
    )

    max_drift = 0.0
    for previous, current in zip(grid_results, grid_results[1:]):
        drift = refinement_drift(previous, current)
        max_drift = max(max_drift, drift)
        if drift > max_refinement_drift:
            fail(
                f"rows[{row_index}] eps={current.epsilon:g}: refinement drift "
                f"{drift:.6e} > threshold {max_refinement_drift:.6e} "
                f"between grid sizes {previous.grid_size} and {current.grid_size}"
            )

    return RefinementRowResult(
        row_index=row_index,
        epsilon=grid_results[0].epsilon,
        grid_results=grid_results,
        max_drift=max_drift,
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "json_path",
        nargs="?",
        default=str(DEFAULT_JSON),
        help="two-interval branch skeleton JSON",
    )
    parser.add_argument(
        "--grid-size",
        type=positive_int,
        default=11,
        help="number of sample points per B/tau axis over each full Krawczyk box",
    )
    parser.add_argument(
        "--min-margin",
        type=nonnegative_float,
        default=9.0e-3,
        help="minimum allowed componentwise inclusion margin",
    )
    parser.add_argument(
        "--max-contraction",
        type=positive_float,
        default=3.0e-2,
        help="maximum allowed sampled defect-action/radius contraction",
    )
    parser.add_argument(
        "--refine-grid-sizes",
        type=refine_grid_sizes,
        default=None,
        help=(
            "optional comma-separated strictly increasing list of at least two grid sizes for deterministic "
            "sampled refinement/stability stress checks, e.g. 11,21,41"
        ),
    )
    parser.add_argument(
        "--max-refinement-drift",
        type=nonnegative_float,
        default=5.0e-6,
        help="maximum allowed max absolute drift between successive refinement grid sizes",
    )
    parser.add_argument(
        "--obligation-report",
        action="store_true",
        help="print intervalization error budgets implied by the unused sampled Krawczyk margin",
    )
    parser.add_argument("--quiet", action="store_true", help="print only the final PASS line")
    args = parser.parse_args()

    payload = load_payload(Path(args.json_path))
    rows = payload.get("rows")
    if not isinstance(rows, list) or not rows:
        fail(f"{args.json_path}: expected nonempty payload.rows list")
    limit_solution, left_weight, null_slope = payload_constants(payload)

    if args.refine_grid_sizes is not None:
        refinement_results = []
        for row_index, row in enumerate(rows):
            result = verify_row_refinement(
                row_index,
                row,
                limit_solution,
                left_weight,
                null_slope,
                args.refine_grid_sizes,
                args.min_margin,
                args.max_contraction,
                args.max_refinement_drift,
            )
            refinement_results.append(result)
            if not args.quiet:
                detail = ", ".join(
                    f"{grid_result.grid_size}x{grid_result.grid_size}:"
                    f"worst_margin={grid_result.worst_margin:.6e},"
                    f"contraction={grid_result.contraction:.6e}"
                    for grid_result in result.grid_results
                )
                print(
                    f"row {result.row_index} eps={result.epsilon:g}: PASS "
                    f"refine_grids=[{detail}] max_refinement_drift={result.max_drift:.6e}"
                )

        all_grid_results = [
            grid_result
            for refinement_result in refinement_results
            for grid_result in refinement_result.grid_results
        ]
        worst = min(all_grid_results, key=lambda item: item.worst_margin)
        worst_contraction = max(result.contraction for result in all_grid_results)
        max_drift = max(result.max_drift for result in refinement_results)
        grid_list = ",".join(str(size) for size in args.refine_grid_sizes)
        row_drifts = ",".join(
            f"{result.row_index}:{result.max_drift:.6e}" for result in refinement_results
        )
        finest_results = [result.grid_results[-1] for result in refinement_results]
        if args.obligation_report:
            print_obligation_report(finest_results)
        print(
            "OVERALL TWO-INTERVAL KRAWCZYK GRID REFINEMENT STRESS CHECK: PASS "
            f"({len(refinement_results)} rows, grids=[{grid_list}], "
            f"worst_margin={worst.worst_margin:.6e} at row {worst.row_index} "
            f"grid={worst.grid_size}x{worst.grid_size}, "
            f"worst_contraction={worst_contraction:.6e}, "
            f"max_refinement_drift={max_drift:.6e}, "
            f"row_drifts=[{row_drifts}], "
            "caveat=deterministic sampled stress evidence, not outward-rounded interval proof)"
        )
        return 0

    results = []
    for row_index, row in enumerate(rows):
        result = verify_row(
            row_index,
            row,
            limit_solution,
            left_weight,
            null_slope,
            args.grid_size,
            args.min_margin,
            args.max_contraction,
        )
        results.append(result)
        if not args.quiet:
            print(
                f"row {result.row_index} eps={result.epsilon:g}: PASS "
                f"grid={result.grid_size}x{result.grid_size} "
                f"margin=({float(result.margin[0]):.6e}, {float(result.margin[1]):.6e}) "
                f"worst_margin={result.worst_margin:.6e} "
                f"contraction={result.contraction:.6e} "
                f"max|K|=({float(result.max_abs_k[0]):.6e}, {float(result.max_abs_k[1]):.6e}) "
                f"max|C K|=({float(result.max_abs_c_k[0]):.6e}, {float(result.max_abs_c_k[1]):.6e})"
            )

    worst = min(results, key=lambda item: item.worst_margin)
    worst_contraction = max(result.contraction for result in results)
    if args.obligation_report:
        print_obligation_report(results)
    print(
        "OVERALL TWO-INTERVAL KRAWCZYK GRID STRESS CHECK: PASS "
        f"({len(results)} rows, grid={args.grid_size}x{args.grid_size}, "
        f"worst_margin={worst.worst_margin:.6e} at row {worst.row_index}, "
        f"worst_contraction={worst_contraction:.6e})"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except VerificationError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(1) from exc
