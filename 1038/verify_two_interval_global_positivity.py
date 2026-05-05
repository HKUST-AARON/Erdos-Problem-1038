#!/usr/bin/env python3
"""Global positivity verifier for the two-interval finite-gap branch.

This checks the sign-chart theorem that turns the local branch equation

    U(alpha) = 0,  U(-1) = 0

into the global dual-sign condition

    U_lambda(x) >= 0  for x in {-1} union [0,1].

For the corrected two-interval ansatz, outside the cut [alpha,beta],

    U'(x) = -F(x),
    F(x) = (x + A) R(x) / ((x - ell)(x - r)(x - 1)).

Under the certified inequalities

    1 < A < -ell,       ell < -1 < r < alpha < beta < 1,

the signs are forced:

    F < 0 on [-1,r),    F > 0 on (r,alpha),    F < 0 on (beta,1).

Thus U increases from U(-1)=0 to r, decreases to U(alpha)=0, is flat on
[alpha,beta] by the branch identity, and then increases from U(beta)=0 to 1.

The verifier does not prove the branch equation itself.  It is meant to be run
after the proof-grade winding certificate has supplied a zero of K inside each
tube slice.  Its job is to certify that every such zero lies in a parameter
region where the sign-chart positivity proof applies.
"""

from __future__ import annotations

import argparse
import copy
import importlib.util
import math
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np


ROOT = Path(__file__).resolve().parent
SLAB_VERIFIER_PATH = ROOT / "verify_two_interval_epsilon_slabs.py"
DEFAULT_JSON = ROOT / "two_interval_branch_certificate_top_split.json"


def load_slab_verifier() -> Any:
    spec = importlib.util.spec_from_file_location("verify_two_interval_epsilon_slabs", SLAB_VERIFIER_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import verifier from {SLAB_VERIFIER_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


v = load_slab_verifier()


class VerificationError(Exception):
    pass


def fail(message: str) -> None:
    raise VerificationError(message)


@dataclass(frozen=True)
class PositivityConfig:
    slab: Any
    radii: np.ndarray
    eta_subdivisions: int
    uv_subdivisions: int


@dataclass(frozen=True)
class PositivityResult:
    config: PositivityConfig
    min_margin: float
    margin_name: str
    source: str
    checked_slices: int


DEFAULT_CONFIGS = (
    "0.00005:0.0001:0.0003,0.0003:224,1",
    "0.0001:0.0002:0.0003,0.0003:224,1",
    "0.0002:0.0005:0.00029,0.00029:1024,1",
    "0.0005:0.001:0.0006,0.0006:1344,1",
    "0.001:0.00125:0.0002,0.0002:224,1",
    "0.00125:0.0015:0.0002,0.0002:224,1",
    "0.0015:0.00175:0.0002,0.0002:224,1",
    "0.00175:0.002:0.0002,0.0002:224,1",
)


def parse_config(raw: str) -> PositivityConfig:
    parts = raw.split(":")
    if len(parts) != 4:
        raise argparse.ArgumentTypeError("expected eps_low:eps_high:rB,rTau:eta,uv")
    slab = v.parse_slab(f"{parts[0]}:{parts[1]}")
    radii = np.asarray(v.parse_positive_pair(parts[2], "rB,rTau"), dtype=float)
    eta_subdivisions, uv_subdivisions = v.parse_subdivisions(parts[3])
    return PositivityConfig(slab=slab, radii=radii, eta_subdivisions=eta_subdivisions, uv_subdivisions=uv_subdivisions)


def parse_index_slice(raw: str) -> tuple[int, int]:
    parts = raw.split(":")
    if len(parts) != 2:
        raise argparse.ArgumentTypeError("expected start:end")
    try:
        start = int(parts[0])
        end = int(parts[1])
    except ValueError as exc:
        raise argparse.ArgumentTypeError("slice endpoints must be integers") from exc
    if start < 0 or end <= start:
        raise argparse.ArgumentTypeError("expected 0 <= start < end")
    return start, end


def sign_chart_margins(
    eps_low: float,
    eps_high: float,
    A_low: float,
    A_high: float,
    alpha_low: float,
    alpha_high: float,
) -> dict[str, float]:
    solver = v.load_solver()
    ell_low = solver.X_LEFT + eps_low
    ell_high = solver.X_LEFT + eps_high
    beta_low = 1.0 - eps_high
    beta_high = 1.0 - eps_low
    r = solver.X_RIGHT
    margins = {
        "A>1": A_low - 1.0,
        "A<-ell": -ell_high - A_high,
        "ell<-1": -1.0 - ell_high,
        "r<alpha": alpha_low - r,
        "alpha<beta": beta_low - alpha_high,
        "beta<1": 1.0 - beta_high,
        "x+A on cut": alpha_low + A_low,
        "cut above ell": alpha_low - ell_high,
        "cut above r": alpha_low - r,
        "cut below 1": 1.0 - beta_high,
        "left atom residue": -(A_high + ell_high),
        "right atom numerator": A_low + r,
        "one atom numerator": A_low + 1.0,
    }
    for name, value in margins.items():
        if not math.isfinite(value):
            fail(f"{name}: non-finite margin {value!r}")
    return margins


def eta_intervals_for_config(config: PositivityConfig) -> tuple[tuple[float, float], ...]:
    eta_low = math.sqrt(config.slab.eps_low)
    eta_high = math.sqrt(config.slab.eps_high)
    return v.eta_intervals(eta_low, eta_high, config.eta_subdivisions)


def verify_config(
    payload: dict[str, Any],
    config: PositivityConfig,
    eta_index_slice: tuple[int, int] | None,
) -> PositivityResult:
    rows = v.require_mapping(payload, "payload").get("rows")
    if not isinstance(rows, list):
        fail("payload.rows: expected list")
    low_row = v.find_endpoint(rows, config.slab.eps_low)
    high_row = v.find_endpoint(rows, config.slab.eps_high)
    v.assert_adjacent_endpoint_rows(rows, low_row, high_row)
    limit_solution, _left_weight, null_slope = v.payload_constants(payload)
    b_slope, b_intercept, tau_slope, tau_intercept = v.affine_coefficients(low_row, high_row)

    intervals = eta_intervals_for_config(config)
    start = 0
    end = len(intervals)
    if eta_index_slice is not None:
        start, end = eta_index_slice
        if end > len(intervals):
            fail(f"slice {eta_index_slice}: end exceeds eta subdivisions {len(intervals)}")

    worst_name = ""
    worst_margin = float("inf")
    worst_source = ""
    uv_count = config.uv_subdivisions
    u_edges = np.linspace(-float(config.radii[0]), float(config.radii[0]), uv_count + 1)
    tau_edges = np.linspace(-float(config.radii[1]), float(config.radii[1]), uv_count + 1)
    for eta_index, (eta_low, eta_high) in enumerate(intervals[start:end], start=start):
        eps_low = eta_low * eta_low
        eps_high = eta_high * eta_high
        for u_index in range(uv_count):
            for tau_index in range(uv_count):
                u_low = float(u_edges[u_index])
                u_high = float(u_edges[u_index + 1])
                tau_low = float(tau_edges[tau_index])
                tau_high = float(tau_edges[tau_index + 1])
                A_low, A_high, alpha_low, alpha_high = v.parameter_ranges(
                    eta_low,
                    eta_high,
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
                margins = sign_chart_margins(eps_low, eps_high, A_low, A_high, alpha_low, alpha_high)
                name, value = min(margins.items(), key=lambda item: item[1])
                if value < worst_margin:
                    worst_name = name
                    worst_margin = value
                    worst_source = (
                        f"eta={eta_index},u={u_index},tau={tau_index},"
                        f"eta_interval=[{eta_low:.17g},{eta_high:.17g}]"
                    )
                if value <= 0.0:
                    detail = ", ".join(f"{key}={val:.6e}" for key, val in sorted(margins.items()))
                    fail(
                        f"slab={config.slab.eps_low:g}:{config.slab.eps_high:g} "
                        f"{worst_source}: sign-chart positivity margin failed: {detail}"
                    )

    return PositivityResult(
        config=config,
        min_margin=worst_margin,
        margin_name=worst_name,
        source=worst_source,
        checked_slices=end - start,
    )


def theorem_text() -> str:
    return (
        "logic=branch_zero_plus_sign_chart: "
        "winding gives U(alpha)=U(-1)=0 inside each tube; "
        "the checked inequalities force F<0 on [-1,r), F>0 on (r,alpha), "
        "F<0 on (beta,1), with U flat on [alpha,beta]; hence U>=0 on {-1} union [0,1]."
    )


def run_tamper_self_test(payload: dict[str, Any], configs: list[PositivityConfig]) -> None:
    """Check that an unsafe parameter box is rejected."""

    if not configs:
        fail("self-test requires at least one config")
    tampered = copy.deepcopy(payload)
    rows = tampered.get("rows")
    if not isinstance(rows, list):
        fail("payload.rows: expected list")
    changed = False
    for row in rows:
        if isinstance(row, dict):
            box = row.setdefault("krawczyk_box", {})
            center = box.setdefault("center", {})
            center["B"] = float(center.get("B", 0.0)) + 1000.0
            changed = True
    if not changed:
        fail("self-test: no rows were available to tamper")
    try:
        verify_config(tampered, configs[0], None)
    except (VerificationError, v.VerificationError):
        return
    fail("self-test tamper was not rejected")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("json", nargs="?", default=str(DEFAULT_JSON), help="two-interval branch certificate JSON")
    parser.add_argument(
        "--config",
        action="append",
        type=parse_config,
        help="slab config eps_low:eps_high:rB,rTau:eta,uv; defaults cover stored finite range",
    )
    parser.add_argument(
        "--eta-slice",
        type=parse_index_slice,
        help="optional eta subdivision slice start:end, for remote split runs",
    )
    parser.add_argument("--self-test-tamper", action="store_true", help="verify that an unsafe tampered tube fails")
    parser.add_argument("--quiet", action="store_true", help="only print final PASS/FAIL")
    args = parser.parse_args()

    payload = v.load_payload(Path(args.json))
    configs = args.config if args.config else [parse_config(raw) for raw in DEFAULT_CONFIGS]

    try:
        if args.self_test_tamper:
            run_tamper_self_test(payload, configs)
        results = [verify_config(payload, config, args.eta_slice) for config in configs]
    except (VerificationError, v.VerificationError) as exc:
        print(f"TWO-INTERVAL GLOBAL POSITIVITY: FAIL {exc}")
        return 1

    if not args.quiet:
        for result in results:
            slab = result.config.slab
            print(
                f"positivity={slab.eps_low:g}:{slab.eps_high:g} PASS "
                f"eta_slices={result.checked_slices} uv={result.config.uv_subdivisions} "
                f"min_margin={result.min_margin:.6e} margin={result.margin_name} "
                f"source={result.source}"
            )
        print(theorem_text())
    worst = min(results, key=lambda item: item.min_margin)
    print(
        "TWO-INTERVAL GLOBAL POSITIVITY: PASS "
        f"configs={len(results)} worst_margin={worst.min_margin:.6e} "
        f"worst_slab={worst.config.slab.eps_low:g}:{worst.config.slab.eps_high:g} "
        f"worst_margin_name={worst.margin_name}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
