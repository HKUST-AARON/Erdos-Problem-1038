#!/usr/bin/env python3
"""Finite interval-box verifier for the conservative (-1.7, 0) forcing family.

This verifies the key positivity claim needed by the 1.8 lower-bound route:

    a in [-1.7, -sqrt(2)],  b in [0, 1.82 + a],
    w = 1.395 - b,          c = 1.071 - b,
    nu_{a,b} = delta_a + w delta_b + C(a,b) delta_c,

where C(a,b) is chosen so that U_nu(-1) = 1e-4.

The script covers the parameter triangle by the rectangle

    a in [-1.7, -sqrt(2)],  s in [0, 1],  b = s(1.82+a),

and proves U_nu(x) > 0 for all x in [0,1] by recursively subdividing
(a,s,x)-boxes.  On each box it uses the elementary bound

    log(1/|x-t|) >= -log(max_box |x-t|)

and interval bounds for w and C.  Singularities at x=b or x=c are harmless:
the bound deliberately ignores the +infinity improvement and only uses the
maximum possible distance over the box.

This is a finite numerical interval certificate with explicit safety padding.
It is intended as the proof-engineering bridge between the exploratory grid
check and a later Lean/Mathlib formalization of the logarithm bounds.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from decimal import Decimal, localcontext
from heapq import heappop, heappush
from pathlib import Path
from typing import List, Tuple


PRECISION = 80
EPS = Decimal("1e-12")
TARGET_MARGIN = Decimal("1e-6")
MAX_DEPTH = 40

A_MIN = Decimal("-1.7")

# This rational endpoint is slightly larger than -sqrt(2), hence the verifier
# covers a harmless superset of the original a-interval.
A_MAX = -Decimal(1414213562373095) / Decimal(10) ** 15

ONE = Decimal(1)
K = Decimal("1.395")
C_SHIFT = Decimal("1.071")
B_LENGTH_OFFSET = Decimal("1.82")
BOUNDARY_EPS = Decimal("0.0001")


@dataclass(frozen=True)
class Box:
    a_lo: Decimal
    a_hi: Decimal
    s_lo: Decimal
    s_hi: Decimal
    x_lo: Decimal
    x_hi: Decimal
    depth: int


@dataclass(frozen=True)
class CertStats:
    certified_boxes: int
    split_boxes: int
    worst_lower_bound: Decimal
    max_depth: int
    leaves: Tuple[Tuple[Box, Decimal], ...]


def decimal_to_json(value: Decimal) -> str:
    return format(value, "f")


def decimal_from_json(value: str) -> Decimal:
    return Decimal(value)


def box_to_json(box: Box, lower: Decimal) -> dict[str, str | int]:
    return {
        "a_lo": decimal_to_json(box.a_lo),
        "a_hi": decimal_to_json(box.a_hi),
        "s_lo": decimal_to_json(box.s_lo),
        "s_hi": decimal_to_json(box.s_hi),
        "x_lo": decimal_to_json(box.x_lo),
        "x_hi": decimal_to_json(box.x_hi),
        "depth": box.depth,
        "lower_bound": decimal_to_json(lower),
    }


def box_from_json(item: dict[str, str | int]) -> Tuple[Box, Decimal]:
    box = Box(
        decimal_from_json(str(item["a_lo"])),
        decimal_from_json(str(item["a_hi"])),
        decimal_from_json(str(item["s_lo"])),
        decimal_from_json(str(item["s_hi"])),
        decimal_from_json(str(item["x_lo"])),
        decimal_from_json(str(item["x_hi"])),
        int(item["depth"]),
    )
    return box, decimal_from_json(str(item["lower_bound"]))


def d_abs(value: Decimal) -> Decimal:
    return -value if value < 0 else value


def d_max(left: Decimal, right: Decimal) -> Decimal:
    return left if left >= right else right


def lower_neg_log(distance: Decimal) -> Decimal:
    if distance <= 0:
        raise ValueError(f"nonpositive distance in log bound: {distance}")
    return -distance.ln() - EPS


def product_lower(weight_lo: Decimal, weight_hi: Decimal, base_lo: Decimal) -> Decimal:
    """Lower-bound weight * base with positive weight in [lo, hi]."""

    return weight_lo * base_lo if base_lo >= 0 else weight_hi * base_lo


def b_interval(box: Box) -> Tuple[Decimal, Decimal]:
    length_lo = B_LENGTH_OFFSET + box.a_lo
    length_hi = B_LENGTH_OFFSET + box.a_hi
    return box.s_lo * length_lo, box.s_hi * length_hi


def c_weight_interval(
    a_lo: Decimal,
    a_hi: Decimal,
    b_lo: Decimal,
    b_hi: Decimal,
) -> Tuple[Decimal, Decimal]:
    """Return a conservative interval for C(a,b).

    On the verified domain,

        N(a,b) = -1e-4 - log(-1-a) - (1.395-b)log(1+b)

    is increasing in a and decreasing in b.  The denominator log(2.071-b)
    is positive and decreasing in b.
    """

    numerator_lo = (
        -BOUNDARY_EPS
        - (-ONE - a_lo).ln()
        - (K - b_hi) * (ONE + b_hi).ln()
        - EPS
    )
    numerator_hi = (
        -BOUNDARY_EPS
        - (-ONE - a_hi).ln()
        - (K - b_lo) * (ONE + b_lo).ln()
        + EPS
    )
    denom_lo = (Decimal("2.071") - b_hi).ln() - EPS
    denom_hi = (Decimal("2.071") - b_lo).ln() + EPS

    if numerator_lo <= 0 or denom_lo <= 0:
        raise ValueError(
            f"C interval lost positivity: N_lo={numerator_lo}, denom_lo={denom_lo}"
        )

    return numerator_lo / denom_hi - EPS, numerator_hi / denom_lo + EPS


def lower_bound_on_box(box: Box) -> Decimal:
    b_lo, b_hi = b_interval(box)
    c_lo = C_SHIFT - b_hi
    c_hi = C_SHIFT - b_lo

    c_weight_lo, c_weight_hi = c_weight_interval(box.a_lo, box.a_hi, b_lo, b_hi)
    if c_weight_lo <= 0:
        raise ValueError(f"nonpositive C lower bound: {c_weight_lo}")

    w_lo = K - b_hi
    w_hi = K - b_lo
    if w_lo <= 0:
        raise ValueError(f"nonpositive w lower bound: {w_lo}")

    # Since x in [0,1] and a < 0, max |x-a| is x_hi - a_lo.
    dist_a = box.x_hi - box.a_lo
    base_a = lower_neg_log(dist_a)

    # For two intervals I,J, max |I-J| occurs at an opposite endpoint pair.
    dist_b = d_max(d_abs(box.x_lo - b_hi), d_abs(box.x_hi - b_lo))
    base_b = lower_neg_log(dist_b)

    dist_c = d_max(d_abs(box.x_lo - c_hi), d_abs(box.x_hi - c_lo))
    base_c = lower_neg_log(dist_c)

    return (
        base_a
        + product_lower(w_lo, w_hi, base_b)
        + product_lower(c_weight_lo, c_weight_hi, base_c)
    )


def split_box(box: Box) -> List[Box]:
    widths = [
        (box.a_hi - box.a_lo, "a"),
        (box.s_hi - box.s_lo, "s"),
        (box.x_hi - box.x_lo, "x"),
    ]
    _, axis = max(widths, key=lambda item: item[0])

    if axis == "a":
        mid = (box.a_lo + box.a_hi) / 2
        return [
            Box(box.a_lo, mid, box.s_lo, box.s_hi, box.x_lo, box.x_hi, box.depth + 1),
            Box(mid, box.a_hi, box.s_lo, box.s_hi, box.x_lo, box.x_hi, box.depth + 1),
        ]
    if axis == "s":
        mid = (box.s_lo + box.s_hi) / 2
        return [
            Box(box.a_lo, box.a_hi, box.s_lo, mid, box.x_lo, box.x_hi, box.depth + 1),
            Box(box.a_lo, box.a_hi, mid, box.s_hi, box.x_lo, box.x_hi, box.depth + 1),
        ]

    mid = (box.x_lo + box.x_hi) / 2
    return [
        Box(box.a_lo, box.a_hi, box.s_lo, box.s_hi, box.x_lo, mid, box.depth + 1),
        Box(box.a_lo, box.a_hi, box.s_lo, box.s_hi, mid, box.x_hi, box.depth + 1),
    ]


def verify_interval_certificate() -> CertStats:
    start = Box(A_MIN, A_MAX, Decimal(0), Decimal(1), Decimal(0), Decimal(1), 0)
    first_lower = lower_bound_on_box(start)

    heap: List[Tuple[Decimal, int, Box]] = []
    serial = 0
    heappush(heap, (first_lower, serial, start))

    certified = 0
    splits = 0
    worst = Decimal("Infinity")
    max_depth = 0
    leaves: List[Tuple[Box, Decimal]] = []

    while heap:
        lower, _, box = heappop(heap)
        if lower > TARGET_MARGIN:
            certified += 1
            worst = lower if lower < worst else worst
            max_depth = max(max_depth, box.depth)
            leaves.append((box, lower))
            continue

        if box.depth >= MAX_DEPTH:
            raise RuntimeError(
                "failed to certify a box before max depth: "
                f"lower={lower}, box={box}"
            )

        splits += 1
        for child in split_box(box):
            serial += 1
            heappush(heap, (lower_bound_on_box(child), serial, child))

    return CertStats(
        certified_boxes=certified,
        split_boxes=splits,
        worst_lower_bound=worst,
        max_depth=max_depth,
        leaves=tuple(leaves),
    )


def box_volume(box: Box) -> Decimal:
    return (
        (box.a_hi - box.a_lo)
        * (box.s_hi - box.s_lo)
        * (box.x_hi - box.x_lo)
    )


def full_domain_volume() -> Decimal:
    return (A_MAX - A_MIN) * ONE * ONE


def box_inside_domain(box: Box) -> bool:
    return (
        A_MIN <= box.a_lo <= box.a_hi <= A_MAX
        and Decimal(0) <= box.s_lo <= box.s_hi <= Decimal(1)
        and Decimal(0) <= box.x_lo <= box.x_hi <= Decimal(1)
    )


def interval_positive_overlap(
    left_lo: Decimal,
    left_hi: Decimal,
    right_lo: Decimal,
    right_hi: Decimal,
) -> bool:
    return max(left_lo, right_lo) < min(left_hi, right_hi)


def boxes_positive_overlap(left: Box, right: Box) -> bool:
    return (
        interval_positive_overlap(left.a_lo, left.a_hi, right.a_lo, right.a_hi)
        and interval_positive_overlap(left.s_lo, left.s_hi, right.s_lo, right.s_hi)
        and interval_positive_overlap(left.x_lo, left.x_hi, right.x_lo, right.x_hi)
    )


def export_certificate(path: Path, stats: CertStats) -> None:
    payload = {
        "format": "erdos1038.conservative_forcing_interval.v1",
        "precision": PRECISION,
        "target_margin": decimal_to_json(TARGET_MARGIN),
        "a_min": decimal_to_json(A_MIN),
        "a_max": decimal_to_json(A_MAX),
        "leaf_count": stats.certified_boxes,
        "split_boxes": stats.split_boxes,
        "max_depth": stats.max_depth,
        "worst_lower_bound": decimal_to_json(stats.worst_lower_bound),
        "leaves": [box_to_json(box, lower) for box, lower in stats.leaves],
    }
    path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")


def check_exported_certificate(path: Path) -> CertStats:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("format") != "erdos1038.conservative_forcing_interval.v1":
        raise ValueError(f"unexpected certificate format in {path}")
    if int(payload.get("precision", -1)) != PRECISION:
        raise ValueError(f"unexpected precision metadata in {path}")
    if decimal_from_json(str(payload.get("target_margin"))) != TARGET_MARGIN:
        raise ValueError(f"unexpected target_margin metadata in {path}")
    if decimal_from_json(str(payload.get("a_min"))) != A_MIN:
        raise ValueError(f"unexpected a_min metadata in {path}")
    if decimal_from_json(str(payload.get("a_max"))) != A_MAX:
        raise ValueError(f"unexpected a_max metadata in {path}")

    leaves = tuple(box_from_json(item) for item in payload["leaves"])
    if not leaves:
        raise ValueError("certificate has no leaves")
    if int(payload.get("leaf_count", -1)) != len(leaves):
        raise ValueError("leaf_count metadata does not match leaf list")

    worst = Decimal("Infinity")
    max_depth = 0
    total_volume = Decimal(0)

    for idx, (box, stored_lower) in enumerate(leaves):
        if not box_inside_domain(box):
            raise ValueError(f"leaf {idx} is not contained in the full domain: {box}")
        recomputed = lower_bound_on_box(box)
        if recomputed <= TARGET_MARGIN:
            raise ValueError(f"leaf lower bound no longer passes: {recomputed}, box={box}")
        if stored_lower <= TARGET_MARGIN:
            raise ValueError(f"stored lower bound is not passing: {stored_lower}, box={box}")
        # The stored value is diagnostic; the recomputed value is authoritative.
        worst = recomputed if recomputed < worst else worst
        max_depth = max(max_depth, box.depth)
        total_volume += box_volume(box)

    if int(payload.get("max_depth", -1)) != max_depth:
        raise ValueError("max_depth metadata does not match leaf list")
    if int(payload.get("split_boxes", -1)) != len(leaves) - 1:
        raise ValueError("split_boxes metadata does not match a binary leaf count")

    for left_idx, (left, _) in enumerate(leaves):
        for right_idx in range(left_idx + 1, len(leaves)):
            right, _ = leaves[right_idx]
            if boxes_positive_overlap(left, right):
                raise ValueError(
                    f"leaves {left_idx} and {right_idx} have positive-volume overlap"
                )

    volume_gap = abs(total_volume - full_domain_volume())
    if volume_gap > Decimal("1e-40"):
        raise ValueError(
            f"leaf volumes do not cover the domain volume: gap={volume_gap}"
        )

    return CertStats(
        certified_boxes=len(leaves),
        split_boxes=len(leaves) - 1,
        worst_lower_bound=worst,
        max_depth=max_depth,
        leaves=leaves,
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--export-json",
        type=Path,
        default=None,
        help="write the terminal interval boxes to a JSON certificate file",
    )
    parser.add_argument(
        "--check-json",
        type=Path,
        default=None,
        help="check a previously exported JSON certificate instead of searching",
    )
    args = parser.parse_args()

    with localcontext() as ctx:
        ctx.prec = PRECISION
        if args.check_json is not None:
            stats = check_exported_certificate(args.check_json)
        else:
            stats = verify_interval_certificate()
            if args.export_json is not None:
                export_certificate(args.export_json, stats)

    print("Finite interval-box verifier for conservative forcing family")
    print(f"a-domain: [{A_MIN}, {A_MAX}]")
    print("s-domain: [0, 1], b=s(1.82+a)")
    print("x-domain: [0, 1]")
    print(f"certified boxes: {stats.certified_boxes}")
    print(f"split boxes: {stats.split_boxes}")
    print(f"max depth: {stats.max_depth}")
    print(f"worst certified lower bound: {stats.worst_lower_bound}")
    if args.export_json is not None and args.check_json is None:
        print(f"exported certificate: {args.export_json}")
    if args.check_json is not None:
        print(f"checked certificate: {args.check_json}")
    print("status: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
