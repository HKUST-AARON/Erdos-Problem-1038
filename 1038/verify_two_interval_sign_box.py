#!/usr/bin/env python3
"""Interval sign-chart verifier for the two-interval branch skeleton.

This script verifies the algebraic sign conditions from §15.1 of
``1038_dual_two_interval_progress.md`` over exported parameter boxes, rather
than only at the stored center.  By default it reads
``two_interval_branch_certificate_skeleton.json`` and checks both the local
``krawczyk_box`` and the wider ``branch_box`` for every row.

The checked conditions are sufficient for positivity of the extracted measure
in the fixed two-interval geometry:

* ``1 < A < -ell`` and ``ell < -1 < r < alpha < beta < 1``;
* atom residue signs at ``ell``, ``r``, and ``1``;
* expected signs of the residue denominators and square-root factors;
* density signs on ``[alpha,beta]``:
  ``x+A>0``, ``x-ell>0``, ``x-r>0``, and ``x-1<0``.

``python-flint`` is not required.  The current proof obligation is a finite
endpoint sign check over the decimal endpoints exported in the JSON.  Those
serialized endpoints, and the hard-coded geometry constants, are certified as
given; a small outward pad is applied only around recomputed quantities such as
``sqrt(epsilon)`` and the Krawczyk-coordinate affine box map.  Future
thin-margin certificates should export interval endpoints or rational
constants explicitly.  This is an external verifier for the exported JSON
boxes, not a final Mathlib proof.
"""

from __future__ import annotations

import argparse
import copy
import json
from decimal import Decimal, InvalidOperation, getcontext, localcontext
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent
DEFAULT_JSON = ROOT / "two_interval_branch_certificate_skeleton.json"

X_LEFT = Decimal("-1.8081073680988165")
X_RIGHT = Decimal("0.02632310766384517")
ONE = Decimal(1)
ZERO = Decimal(0)
PAD = Decimal("1e-50")
STORED_MARGIN_TOL = Decimal("1e-12")
getcontext().prec = 90

Interval = tuple[Decimal, Decimal]


class VerificationError(Exception):
    pass


def fail(message: str) -> None:
    raise VerificationError(message)


def dec(value: Any) -> Decimal:
    if isinstance(value, Decimal):
        return value
    return Decimal(str(value))


def require_mapping(value: Any, path: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        fail(f"{path}: expected object, got {type(value).__name__}")
    return value


def require_list(value: Any, path: str) -> list[Any]:
    if not isinstance(value, list):
        fail(f"{path}: expected list, got {type(value).__name__}")
    return value


def field(mapping: dict[str, Any], key: str, path: str) -> Any:
    if key not in mapping:
        fail(f"{path}: missing required field {key!r}")
    return mapping[key]


def mapping_field(mapping: dict[str, Any], key: str, path: str) -> dict[str, Any]:
    return require_mapping(field(mapping, key, path), f"{path}.{key}")


def decimal_field(mapping: dict[str, Any], key: str, path: str) -> Decimal:
    return decimal_value(field(mapping, key, path), f"{path}.{key}")


def decimal_value(value: Any, path: str) -> Decimal:
    if isinstance(value, bool) or isinstance(value, (dict, list)):
        fail(f"{path}: expected decimal scalar, got {type(value).__name__}")
    try:
        result = dec(value)
    except (InvalidOperation, ValueError, TypeError) as exc:
        fail(f"{path}: invalid decimal value {value!r}: {exc}")
    if not result.is_finite():
        fail(f"{path}: expected finite decimal, got {result}")
    return result


def pad_interval(interval: Interval, pad: Decimal = PAD) -> Interval:
    return interval[0] - pad, interval[1] + pad


def singleton(value: Decimal) -> Interval:
    return value, value


def pair_interval(raw: Any, name: str) -> Interval:
    if not isinstance(raw, list) or len(raw) != 2:
        fail(f"{name}: expected a two-endpoint list")
    lo, hi = decimal_value(raw[0], f"{name}[0]"), decimal_value(raw[1], f"{name}[1]")
    if lo > hi:
        fail(f"{name}: lower endpoint {lo} exceeds upper endpoint {hi}")
    return lo, hi


def min_margin(margins: dict[str, Decimal]) -> tuple[str, Decimal]:
    return min(margins.items(), key=lambda item: item[1])


def require_positive(context: str, margins: dict[str, Decimal]) -> None:
    bad = [(name, value) for name, value in sorted(margins.items()) if value <= ZERO]
    if bad:
        detail = ", ".join(f"{name}={value}" for name, value in bad)
        fail(f"{context}: unsafe sign margin(s): {detail}")


def require_close(context: str, name: str, actual: Decimal, expected: Decimal, tolerance: Decimal) -> None:
    delta = abs(actual - expected)
    if delta > tolerance:
        fail(f"{context}: stored {name}={expected} differs from recomputed {actual} by {delta} > {tolerance}")


def check_stored_sign_margins(context: str, row: dict[str, Any], box_type: str, margins: dict[str, Decimal]) -> None:
    box = mapping_field(row, box_type, context)
    stored = mapping_field(box, "sign_margins", f"{context}.{box_type}")
    for name, raw_value in sorted(stored.items()):
        if name not in margins:
            fail(f"{context}.{box_type}.sign_margins: unknown stored margin {name!r}")
        expected = decimal_value(raw_value, f"{context}.{box_type}.sign_margins.{name}")
        require_close(
            f"{context} {box_type}",
            f"sign_margins.{name}",
            margins[name],
            expected,
            STORED_MARGIN_TOL,
        )


def containment_margins(name: str, interval: Interval, value: Decimal) -> dict[str, Decimal]:
    return {
        f"{name}:above_low": value - interval[0],
        f"{name}:below_high": interval[1] - value,
    }


def sqrt_interval(value: Decimal) -> Interval:
    if value <= ZERO:
        fail(f"epsilon must be positive, got {value}")
    with localcontext() as ctx:
        ctx.prec = 90
        root = value.sqrt()
    return pad_interval((root, root))


def krawczyk_parameter_box(row: dict[str, Any], payload: dict[str, Any]) -> tuple[Interval, Interval]:
    epsilon = decimal_field(row, "epsilon", "row")
    eta = sqrt_interval(epsilon)
    eta_values = [eta[0], eta[1]]

    box = mapping_field(row, "krawczyk_box", "row")
    center = mapping_field(box, "center", "row.krawczyk_box")
    radii = mapping_field(box, "radii", "row.krawczyk_box")
    B = decimal_field(center, "B", "row.krawczyk_box.center")
    tau = decimal_field(center, "tau", "row.krawczyk_box.center")
    radius_B = decimal_field(radii, "B", "row.krawczyk_box.radii")
    radius_tau = decimal_field(radii, "tau", "row.krawczyk_box.radii")

    B_values = [B - radius_B, B + radius_B]
    tau_values = [tau - radius_tau, tau + radius_tau]

    limit_solution = mapping_field(payload, "limit_solution", "payload")
    fold = mapping_field(payload, "fold", "payload")
    limit_A = decimal_field(limit_solution, "A", "payload.limit_solution")
    limit_alpha = decimal_field(limit_solution, "alpha", "payload.limit_solution")
    null_slope = decimal_field(fold, "null_slope", "payload.fold")

    A_values = [
        limit_A + eta_value * (null_slope * tau_value + B_value)
        for eta_value in eta_values
        for B_value in B_values
        for tau_value in tau_values
    ]
    alpha_values = [
        limit_alpha + eta_value * tau_value
        for eta_value in eta_values
        for tau_value in tau_values
    ]
    return pad_interval((min(A_values), max(A_values))), pad_interval((min(alpha_values), max(alpha_values)))


def branch_parameter_box(row: dict[str, Any], _payload: dict[str, Any]) -> tuple[Interval, Interval]:
    box = mapping_field(row, "branch_box", "row")
    return pair_interval(field(box, "A", "row.branch_box"), "row.branch_box.A"), pair_interval(
        field(box, "alpha", "row.branch_box"), "row.branch_box.alpha"
    )


def geometry_intervals(epsilon: Decimal) -> tuple[Interval, Interval, Interval]:
    ell = singleton(X_LEFT + epsilon)
    r = singleton(X_RIGHT)
    beta = singleton(ONE - epsilon)
    return ell, r, beta


def sign_margins(A: Interval, alpha: Interval, ell: Interval, r: Interval, beta: Interval) -> dict[str, Decimal]:
    return {
        # Parameter order.
        "A>1": A[0] - ONE,
        "A<-ell": -(A[1] + ell[1]),
        "ell<-1": -ONE - ell[1],
        "-1<r": r[0] + ONE,
        "r<alpha": alpha[0] - r[1],
        "alpha<beta": beta[0] - alpha[1],
        "beta<1": ONE - beta[1],
        # Atom numerator and branch/radicand signs.
        "ell+A<0": -(ell[1] + A[1]),
        "r+A>0": r[0] + A[0],
        "1+A>0": ONE + A[0],
        "alpha-ell>0": alpha[0] - ell[1],
        "beta-ell>0": beta[0] - ell[1],
        "alpha-r>0": alpha[0] - r[1],
        "beta-r>0": beta[0] - r[1],
        "1-alpha>0": ONE - alpha[1],
        "1-beta>0": ONE - beta[1],
        # Residue denominator factor signs.
        "ell-r<0": r[0] - ell[1],
        "ell-1<0": ONE - ell[1],
        "r-ell>0": r[0] - ell[1],
        "r-1<0": ONE - r[1],
        "1-ell>0": ONE - ell[1],
        "1-r>0": ONE - r[1],
        # Density signs for every x in [alpha,beta].
        "density:x+A>0": alpha[0] + A[0],
        "density:x-ell>0": alpha[0] - ell[1],
        "density:x-r>0": alpha[0] - r[1],
        "density:x-1<0": ONE - beta[1],
    }


def row_error_message(row_path: str, exc: VerificationError) -> str:
    message = str(exc)
    if message == row_path or message.startswith(f"{row_path}:") or message.startswith(f"{row_path}."):
        return message
    if message == "row":
        return row_path
    if message.startswith("row:"):
        return f"{row_path}{message[len('row'):]}"
    if message.startswith("row."):
        return f"{row_path}{message[len('row'):]}"
    return f"{row_path}: {message}"


def verify_box(
    row_index: int, raw_row: Any, payload: dict[str, Any], box_type: str
) -> tuple[Decimal, dict[str, Decimal]]:
    row_path = f"rows[{row_index}]"
    try:
        row = require_mapping(raw_row, row_path)
        epsilon = decimal_field(row, "epsilon", row_path)
        ell, r, beta = geometry_intervals(epsilon)
        if box_type == "krawczyk_box":
            A, alpha = krawczyk_parameter_box(row, payload)
        elif box_type == "branch_box":
            A, alpha = branch_parameter_box(row, payload)
        else:
            fail(f"unknown box type: {box_type}")
        margins = sign_margins(A, alpha, ell, r, beta)
        solution = mapping_field(row, "solution", row_path)
        solution_A = decimal_field(solution, "A", f"{row_path}.solution")
        solution_alpha = decimal_field(solution, "alpha", f"{row_path}.solution")
        margins.update(containment_margins("solution_A", A, solution_A))
        margins.update(containment_margins("solution_alpha", alpha, solution_alpha))
        require_positive(f"{row_path} eps={epsilon} {box_type}", margins)
        check_stored_sign_margins(row_path, row, box_type, margins)
        return epsilon, margins
    except VerificationError as exc:
        raise VerificationError(row_error_message(row_path, exc)) from exc


def load_payload(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"), parse_float=Decimal, parse_int=Decimal)
    except json.JSONDecodeError as exc:
        fail(f"{path}: invalid JSON: {exc}")
    payload = require_mapping(payload, str(path))
    require_mapping(field(payload, "fold", str(path)), f"{path}.fold")
    require_mapping(field(payload, "limit_solution", str(path)), f"{path}.limit_solution")
    rows = require_list(field(payload, "rows", str(path)), f"{path}.rows")
    if not rows:
        fail(f"{path}: expected a nonempty rows list")
    return payload


def verify_payload(payload: dict[str, Any], boxes: list[str], quiet: bool) -> tuple[int, int]:
    checked = 0
    rows = payload["rows"]
    for index, row in enumerate(rows):
        for box_type in boxes:
            epsilon, margins = verify_box(index, row, payload, box_type)
            checked += 1
            if not quiet:
                name, value = min_margin(margins)
                print(f"row={index} eps={epsilon} box={box_type}: PASS min_margin {name}={value}")
    return len(rows), checked


def run_tamper_self_test(payload: dict[str, Any], boxes: list[str]) -> int:
    def mutate_solution_alpha(tampered: dict[str, Any]) -> None:
        tampered["rows"][0]["solution"]["alpha"] = "-10"

    def mutate_branch_A_high(tampered: dict[str, Any]) -> None:
        branch_A = tampered["rows"][0]["branch_box"]["A"]
        branch_A[1] = "10"

    def mutate_krawczyk_tau_center(tampered: dict[str, Any]) -> None:
        center = tampered["rows"][0]["krawczyk_box"]["center"]
        center["tau"] = str(dec(center["tau"]) + Decimal("1"))

    def mutate_stored_sign_margin(tampered: dict[str, Any]) -> None:
        stored = tampered["rows"][0]["branch_box"]["sign_margins"]
        stored["A>1"] = str(dec(stored["A>1"]) + Decimal("0.1"))

    enabled_boxes = set(boxes)
    tamper_cases = [
        ("solution.alpha containment", True, mutate_solution_alpha),
        ("branch_box.A[1] sign", "branch_box" in enabled_boxes, mutate_branch_A_high),
        ("krawczyk_box.center.tau containment", "krawczyk_box" in enabled_boxes, mutate_krawczyk_tau_center),
        ("branch_box.sign_margins.A>1", "branch_box" in enabled_boxes, mutate_stored_sign_margin),
    ]

    checked = 0
    for name, enabled, mutate in tamper_cases:
        if not enabled:
            continue
        checked += 1
        tampered = copy.deepcopy(payload)
        mutate(tampered)
        try:
            verify_payload(tampered, boxes, quiet=True)
        except VerificationError:
            continue
        fail(f"self-test tamper case {name}: tampered payload unexpectedly passed")
    return checked


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "json_path",
        nargs="?",
        default=str(DEFAULT_JSON),
        help="skeleton JSON exported by solve_two_interval_finite_gap.py",
    )
    parser.add_argument(
        "--boxes",
        nargs="+",
        choices=["krawczyk_box", "branch_box"],
        default=["krawczyk_box", "branch_box"],
        help="box types to verify for each row",
    )
    parser.add_argument(
        "--self-test-tamper",
        action="store_true",
        help="after normal verification passes, verify in-memory tampered payloads are rejected",
    )
    parser.add_argument("--quiet", action="store_true", help="print only the final PASS line")
    args = parser.parse_args()

    path = Path(args.json_path)
    payload = load_payload(path)

    row_count, checked = verify_payload(payload, args.boxes, quiet=args.quiet)
    if args.self_test_tamper:
        tamper_count = run_tamper_self_test(payload, args.boxes)
        print(
            "OVERALL TWO-INTERVAL SIGN-BOX CHECK: PASS "
            f"({row_count} rows, {checked} boxes; tamper self-test PASS {tamper_count} cases; "
            "verifier integrity only, not a math proof)"
        )
    else:
        print(f"OVERALL TWO-INTERVAL SIGN-BOX CHECK: PASS ({row_count} rows, {checked} boxes)")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except VerificationError as exc:
        raise SystemExit(f"FAIL: {exc}")
