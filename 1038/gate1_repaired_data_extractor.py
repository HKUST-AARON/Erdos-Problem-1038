#!/usr/bin/env python3
"""Gate 1 repaired moving-Schiffer data extractor.

This is a numerical algebra core for the Gate 1 oracle.  It does not solve the
finite-gap equations by itself.  Given a regular moving chart

    P, Q, D(z)=prod_gamma (z-gamma),

and a list of chart rows, it constructs the canonical correction basis

    B_m(z)=D(z) z^m, 0 <= m <= 2 deg(Q)-3,

then computes

    A_{row,m}=row(B_m),  r_gamma=row(-1/2 P Q D_gamma),
    A X_gamma = -r_gamma,  H_gamma^rep = -1/2 P Q D_gamma + B X_gamma.

The output is the exact object that later Gate 1 contact and majorant oracles
must consume.  Existing two-interval ansatz scripts do not produce these data.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from typing import Any

import numpy as np


Array = np.ndarray


def trim(poly: Array, tol: float = 0.0) -> Array:
    p = np.array(poly, dtype=float)
    while len(p) > 1 and abs(p[-1]) <= tol:
        p = p[:-1]
    return p


def poly_mul(a: Array, b: Array) -> Array:
    return trim(np.polynomial.polynomial.polymul(a, b))


def poly_add(a: Array, b: Array) -> Array:
    n = max(len(a), len(b))
    out = np.zeros(n)
    out[: len(a)] += a
    out[: len(b)] += b
    return trim(out)


def poly_scale(a: Array, c: float) -> Array:
    return trim(np.array(a, dtype=float) * c)


def poly_eval(a: Array, x: float) -> float:
    return float(np.polynomial.polynomial.polyval(x, a))


def poly_derivative(a: Array, order: int = 1) -> Array:
    p = np.array(a, dtype=float)
    for _ in range(order):
        if len(p) <= 1:
            return np.array([0.0])
        p = np.array([i * p[i] for i in range(1, len(p))], dtype=float)
    return trim(p)


def poly_from_roots(roots: list[float]) -> Array:
    p = np.array([1.0])
    for root in roots:
        p = poly_mul(p, np.array([-root, 1.0]))
    return trim(p)


def monomial(k: int) -> Array:
    p = np.zeros(k + 1)
    p[k] = 1.0
    return p


def divide_by_linear(poly: Array, root: float) -> Array:
    """Divide ascending-coefficient poly by z-root, assuming exact division."""
    desc = np.array(list(reversed(poly)), dtype=float)
    q_desc, rem = np.polydiv(desc, np.array([1.0, -root]))
    if np.linalg.norm(rem) > 1.0e-7:
        raise ValueError(f"polynomial not divisible by z-{root}: remainder {rem}")
    return trim(np.array(list(reversed(q_desc)), dtype=float), tol=1.0e-12)


@dataclass(frozen=True)
class Row:
    kind: str
    x: float
    order: int = 0
    scale: float = 1.0
    name: str | None = None

    def apply(self, poly: Array) -> float:
        if self.kind == "eval":
            value = poly_eval(poly, self.x)
        elif self.kind == "deriv":
            value = poly_eval(poly_derivative(poly, self.order), self.x)
        else:
            raise ValueError(f"unknown row kind {self.kind!r}")
        return self.scale * value

    def to_json(self) -> dict[str, Any]:
        return {
            "kind": self.kind,
            "x": self.x,
            "order": self.order,
            "scale": self.scale,
            "name": self.name or f"{self.kind}@{self.x:g}",
        }


def canonical_correction_basis(D: Array, q_degree: int) -> list[Array]:
    max_power = 2 * q_degree - 3
    if max_power < 0:
        raise ValueError("deg(Q) must be at least 2 for the Gate 1 correction basis")
    return [poly_mul(D, monomial(m)) for m in range(max_power + 1)]


def raw_endpoint_column(P: Array, Q: Array, D: Array, gamma: float) -> Array:
    D_gamma = divide_by_linear(D, gamma)
    return poly_scale(poly_mul(poly_mul(P, Q), D_gamma), -0.5)


def extract_repaired_data(
    P: Array,
    Q: Array,
    gammas: list[float],
    rows: list[Row],
) -> dict[str, Any]:
    D = poly_from_roots(gammas)
    d = len(trim(Q)) - 1
    basis = canonical_correction_basis(D, d)
    if len(rows) != len(basis):
        raise ValueError(
            f"need square chart matrix: got {len(rows)} rows for {len(basis)} correction columns"
        )

    A = np.array([[row.apply(col) for col in basis] for row in rows], dtype=float)
    det_A = float(np.linalg.det(A))
    cond_A = float(np.linalg.cond(A))
    if not math.isfinite(cond_A) or abs(det_A) < 1.0e-12:
        raise ValueError(f"singular or ill-conditioned chart matrix: det={det_A}, cond={cond_A}")

    endpoint_payload = {}
    max_row_residual = 0.0
    max_reconstruction_residual = 0.0
    for gamma in gammas:
        h_raw = raw_endpoint_column(P, Q, D, gamma)
        r = np.array([row.apply(h_raw) for row in rows], dtype=float)
        X = np.linalg.solve(A, -r)
        correction = np.zeros(max(len(col) for col in basis))
        for coeff, col in zip(X, basis):
            if len(col) > len(correction):
                correction = np.pad(correction, (0, len(col) - len(correction)))
            correction[: len(col)] += coeff * col
        h_rep = poly_add(h_raw, correction)
        row_values = np.array([row.apply(h_rep) for row in rows], dtype=float)
        max_row_residual = max(max_row_residual, float(np.max(np.abs(row_values))))
        max_reconstruction_residual = max(
            max_reconstruction_residual,
            float(np.max(np.abs(A @ X + r))),
        )
        endpoint_payload[f"{gamma:.17g}"] = {
            "gamma": gamma,
            "h_raw_coefficients_ascending": h_raw.tolist(),
            "r": r.tolist(),
            "X": X.tolist(),
            "h_rep_coefficients_ascending": h_rep.tolist(),
            "chart_row_values_after_repair": row_values.tolist(),
            "max_abs_chart_row_after_repair": float(np.max(np.abs(row_values))),
        }

    return {
        "P_coefficients_ascending": trim(P).tolist(),
        "Q_coefficients_ascending": trim(Q).tolist(),
        "D_coefficients_ascending": trim(D).tolist(),
        "gammas": gammas,
        "rows": [row.to_json() for row in rows],
        "canonical_basis_coefficients_ascending": [col.tolist() for col in basis],
        "A": A.tolist(),
        "det_A": det_A,
        "cond_A": cond_A,
        "max_abs_AX_plus_r": max_reconstruction_residual,
        "max_abs_chart_row_after_repair": max_row_residual,
        "endpoints": endpoint_payload,
    }


def toy_g2_inputs() -> tuple[Array, Array, list[float], list[Row]]:
    """A regular synthetic g=2 smoke test, not the 1038 extremal chart."""
    gammas = [-2.4, -1.3, 0.7, 1.8]
    P = np.array([0.9, 1.0])  # z + 0.9
    Q = poly_from_roots([-3.1, -0.25, 2.6])  # monic cubic
    # deg(Q)=3, so four correction columns D, zD, z^2D, z^3D.
    rows = [
        Row("eval", -3.1, name="Qpole_eval_left"),
        Row("deriv", -3.1, order=1, name="Qpole_deriv_left"),
        Row("eval", -0.25, name="Qpole_eval_mid"),
        Row("eval", 2.6, name="Qpole_eval_right"),
    ]
    return P, Q, gammas, rows


def parse_float_list(raw: str) -> list[float]:
    return [float(part) for part in raw.split(",") if part.strip()]


def parse_rows(raw: str) -> list[Row]:
    rows: list[Row] = []
    if not raw:
        return rows
    for item in raw.split(","):
        item = item.strip()
        if not item:
            continue
        parts = item.split(":")
        if parts[0] == "eval" and len(parts) == 2:
            rows.append(Row("eval", float(parts[1])))
        elif parts[0] == "deriv" and len(parts) in {2, 3}:
            order = int(parts[2]) if len(parts) == 3 else 1
            rows.append(Row("deriv", float(parts[1]), order=order))
        else:
            raise ValueError(
                f"bad row spec {item!r}; use eval:x or deriv:x:order, comma-separated"
            )
    return rows


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--toy-g2", action="store_true", help="run a synthetic g=2 smoke test")
    parser.add_argument("--P", help="ascending coefficients, comma-separated")
    parser.add_argument("--Q", help="ascending coefficients, comma-separated")
    parser.add_argument("--gammas", help="branch endpoints, comma-separated")
    parser.add_argument("--rows", help="row specs: eval:x,deriv:x:1,...")
    parser.add_argument("--write-json", help="write extractor output")
    args = parser.parse_args()

    if args.toy_g2:
        P, Q, gammas, rows = toy_g2_inputs()
    else:
        if not (args.P and args.Q and args.gammas and args.rows):
            parser.error("provide --toy-g2 or all of --P --Q --gammas --rows")
        P = np.array(parse_float_list(args.P), dtype=float)
        Q = np.array(parse_float_list(args.Q), dtype=float)
        gammas = parse_float_list(args.gammas)
        rows = parse_rows(args.rows)

    payload = extract_repaired_data(P, Q, gammas, rows)
    print("Gate 1 repaired data extractor")
    print(f"  deg P, deg Q, #gammas = {len(trim(P))-1} {len(trim(Q))-1} {len(gammas)}")
    print(f"  rows/correction columns = {len(rows)}")
    print(f"  det(A) = {payload['det_A']:.12e}")
    print(f"  cond(A) = {payload['cond_A']:.12e}")
    print(f"  max |AX+r| = {payload['max_abs_AX_plus_r']:.12e}")
    print(f"  max repaired chart row = {payload['max_abs_chart_row_after_repair']:.12e}")
    if args.write_json:
        with open(args.write_json, "w", encoding="utf-8") as handle:
            json.dump(payload, handle, indent=2, sort_keys=True)
        print(f"  wrote {args.write_json}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
