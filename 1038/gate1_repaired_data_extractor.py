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
from pathlib import Path
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


def audit_two_interval_json(path: Path) -> dict[str, Any]:
    """Inspect an old two-interval diagnostic JSON for Gate 1 input readiness.

    The existing two-interval solver records the local ansatz

        F=(z+A) R / ((z-ell)(z-r)(z-1)).

    That is useful diagnostic data, but it is not the compact non-pinched g=2
    moving chart required by this extractor.  This audit makes the mismatch
    explicit and computes the old ansatz P,Q candidates so they are not
    confused with proof-grade Gate 1 inputs.
    """
    payload = json.loads(path.read_text(encoding="utf-8"))
    rows = payload.get("rows")
    if not isinstance(rows, list) or not rows:
        raise ValueError(f"{path}: expected nonempty rows list")

    audits: list[dict[str, Any]] = []
    for index, row in enumerate(rows):
        solution = row.get("solution")
        if not isinstance(solution, dict):
            raise ValueError(f"{path}: rows[{index}].solution missing")
        required = ["A", "alpha", "beta", "ell", "r"]
        missing = [key for key in required if key not in solution]
        if missing:
            raise ValueError(f"{path}: rows[{index}].solution missing {missing}")

        A_value = float(solution["A"])
        ell = float(solution["ell"])
        r = float(solution["r"])
        alpha = float(solution["alpha"])
        beta = float(solution["beta"])
        old_P = np.array([A_value, 1.0])
        old_Q = poly_from_roots([ell, r, 1.0])
        audits.append(
            {
                "row_index": index,
                "epsilon": row.get("epsilon"),
                "old_ansatz_P_coefficients_ascending": old_P.tolist(),
                "old_ansatz_Q_coefficients_ascending": old_Q.tolist(),
                "old_ansatz_cut_endpoints": [alpha, beta],
                "old_ansatz_poles": [ell, r, 1.0],
                "gate1_ready": False,
                "missing_gate1_inputs": [
                    "compact_non_pinched_four_branch_endpoints_Gamma",
                    "regular_moving_chart_rows_ell",
                    "period_orientation_kappa",
                    "Z0_components_and_anchor_rows_u_c_v",
                ],
            }
        )

    return {
        "path": str(path),
        "description": payload.get("description"),
        "row_count": len(rows),
        "gate1_ready": False,
        "reason": (
            "old two-interval ansatz has one moving cut [alpha,beta] and "
            "three poles; Gate 1 extractor needs a compact non-pinched g=2 "
            "moving chart with four branch endpoints Gamma and chart rows"
        ),
        "rows": audits,
    }


def diagnose_json_file(path: Path) -> dict[str, Any]:
    """Classify a JSON file by whether it can feed the Gate 1 chart extractor."""
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except Exception as exc:  # noqa: BLE001 - diagnostic payload should keep scanning.
        return {
            "path": str(path),
            "kind": "unreadable_json",
            "gate1_chart_ready": False,
            "reason": str(exc),
        }
    if not isinstance(payload, dict):
        return {
            "path": str(path),
            "kind": "json_non_object",
            "gate1_chart_ready": False,
            "reason": "top-level JSON is not an object",
        }

    chart_required = ["P", "Q", "gammas", "rows"]
    missing_chart = [key for key in chart_required if key not in payload]
    if not missing_chart:
        raw_rows = payload.get("rows")
        rows_ok = isinstance(raw_rows, list)
        gammas_ok = isinstance(payload.get("gammas"), list) and len(payload["gammas"]) == 4
        return {
            "path": str(path),
            "kind": "gate1_chart_json" if rows_ok and gammas_ok else "malformed_gate1_chart_json",
            "gate1_chart_ready": bool(rows_ok and gammas_ok),
            "missing_required_fields": [],
            "row_count": len(raw_rows) if isinstance(raw_rows, list) else None,
            "gamma_count": len(payload.get("gammas", [])) if isinstance(payload.get("gammas"), list) else None,
            "optional_fields_present": {
                key: key in payload
                for key in ["kappa", "Z0", "u", "c", "v", "contact_points", "right_exterior_grid"]
            },
            "reason": None if rows_ok and gammas_ok else "requires list rows and exactly four gammas",
        }

    rows = payload.get("rows")
    if isinstance(rows, list) and rows and isinstance(rows[0], dict) and "solution" in rows[0]:
        return {
            "path": str(path),
            "kind": "old_two_interval_diagnostic",
            "gate1_chart_ready": False,
            "missing_required_fields": missing_chart,
            "row_count": len(rows),
            "reason": (
                "old local ansatz data; lacks compact non-pinched g=2 "
                "Gamma, moving-chart rows, kappa, and Z0/u/c/v"
            ),
        }

    return {
        "path": str(path),
        "kind": "other_json",
        "gate1_chart_ready": False,
        "missing_required_fields": missing_chart,
        "reason": "not a Gate 1 chart schema",
    }


def scan_jsons_for_gate1(root: Path) -> dict[str, Any]:
    records = [diagnose_json_file(path) for path in sorted(root.rglob("*.json"))]
    by_kind: dict[str, int] = {}
    for record in records:
        kind = str(record["kind"])
        by_kind[kind] = by_kind.get(kind, 0) + 1
    ready = [record for record in records if record.get("gate1_chart_ready")]
    old = [record for record in records if record.get("kind") == "old_two_interval_diagnostic"]
    malformed = [record for record in records if record.get("kind") == "malformed_gate1_chart_json"]
    return {
        "root": str(root),
        "total_json_files": len(records),
        "counts_by_kind": by_kind,
        "gate1_chart_ready_count": len(ready),
        "gate1_chart_ready": ready,
        "old_two_interval_diagnostic_count": len(old),
        "old_two_interval_diagnostics": old,
        "malformed_gate1_chart_count": len(malformed),
        "malformed_gate1_charts": malformed,
    }


def row_from_json(item: dict[str, Any]) -> Row:
    kind = str(item["kind"])
    x = float(item["x"])
    order = int(item.get("order", 0 if kind == "eval" else 1))
    scale = float(item.get("scale", 1.0))
    name = item.get("name")
    return Row(kind, x, order=order, scale=scale, name=name)


def load_chart_json(path: Path) -> tuple[Array, Array, list[float], list[Row], dict[str, Any]]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    missing = [key for key in ["P", "Q", "gammas", "rows"] if key not in payload]
    if missing:
        raise ValueError(f"{path}: missing required chart fields {missing}")
    P = np.array([float(x) for x in payload["P"]], dtype=float)
    Q = np.array([float(x) for x in payload["Q"]], dtype=float)
    gammas = [float(x) for x in payload["gammas"]]
    raw_rows = payload["rows"]
    if not isinstance(raw_rows, list):
        raise ValueError(f"{path}: rows must be a list")
    rows = [row_from_json(item) for item in raw_rows]
    return P, Q, gammas, rows, payload


def period_endpoint_quotient_residual(P: Array, Q: Array, gammas: list[float]) -> dict[str, Any]:
    D = poly_from_roots(gammas)
    q2 = poly_mul(Q, Q)
    interpolation = np.zeros(max(len(q2), len(D) + max(0, len(q2) - len(D) + 1)))
    coefficients: dict[str, float] = {}
    for gamma in gammas:
        D_gamma = divide_by_linear(D, gamma)
        denom = poly_eval(P, gamma) * poly_eval(D_gamma, gamma)
        if abs(denom) < 1.0e-14:
            raise ValueError(f"endpoint interpolation denominator vanishes at gamma={gamma}")
        coeff = poly_eval(Q, gamma) / denom
        endpoint_col = poly_mul(poly_mul(P, Q), D_gamma)
        if len(endpoint_col) > len(interpolation):
            interpolation = np.pad(interpolation, (0, len(endpoint_col) - len(interpolation)))
        interpolation[: len(endpoint_col)] += coeff * endpoint_col
        coefficients[f"{gamma:.17g}"] = float(coeff)

    numerator = poly_add(q2, poly_scale(interpolation, -1.0))
    desc_num = np.array(list(reversed(numerator)), dtype=float)
    desc_D = np.array(list(reversed(D)), dtype=float)
    quotient_desc, rem_desc = np.polydiv(desc_num, desc_D)
    quotient = trim(np.array(list(reversed(quotient_desc)), dtype=float), tol=1.0e-11)
    remainder = trim(np.array(list(reversed(rem_desc)), dtype=float), tol=1.0e-11)
    return {
        "coefficients": coefficients,
        "W_Q_coefficients_ascending": quotient.tolist(),
        "max_abs_remainder_after_dividing_by_D": float(np.max(np.abs(remainder))) if len(remainder) else 0.0,
        "raw_remainder_coefficients_ascending": remainder.tolist(),
    }


def real_R_value(x: float, gammas: list[float]) -> float:
    ordered = sorted(gammas)
    if len(ordered) != 4:
        raise ValueError("real_R_value currently expects four g=2 branch endpoints")
    a1, b1, a2, b2 = ordered
    if a1 <= x <= b1 or a2 <= x <= b2:
        raise ValueError(f"x={x} lies on a cut; real off-cut R is not defined")
    radicand = math.prod(x - gamma for gamma in ordered)
    if radicand <= 0.0:
        raise ValueError(f"x={x}: nonpositive off-cut radicand {radicand}")
    # Branch convention R(z)~z^2 at +infinity. Crossing each cut flips the sign.
    sign = -1.0 if b1 < x < a2 else 1.0
    return sign * math.sqrt(radicand)


def cauchy_column_value(h_coefficients: list[float], Q: Array, gammas: list[float], x: float) -> float:
    R_x = real_R_value(x, gammas)
    Q_x = poly_eval(Q, x)
    if abs(Q_x) < 1.0e-14:
        raise ValueError(f"x={x}: Q vanishes, C column is singular")
    return poly_eval(np.array(h_coefficients, dtype=float), x) / (Q_x * Q_x * R_x)


def period_cauchy_value(kappa: float, gammas: list[float], x: float) -> float:
    return kappa / real_R_value(x, gammas)


def integrate_to_infinity_right_exterior(
    value_at: Any,
    start: float,
    right_endpoint: float,
    nodes: int = 500,
) -> float:
    if start <= right_endpoint:
        raise ValueError(
            f"start={start} is not in the right exterior component ({right_endpoint}, infinity)"
        )
    xs, ws = np.polynomial.legendre.leggauss(nodes)
    ts = 0.5 * (xs + 1.0)
    weights = 0.5 * ws
    total = 0.0
    for t, weight in zip(ts, weights):
        y = start + t / (1.0 - t)
        jac = 1.0 / ((1.0 - t) * (1.0 - t))
        total += float(weight) * value_at(float(y)) * jac
    return float(total)


def anchor_rho_payload(repaired: dict[str, Any], c_value: float) -> dict[str, Any]:
    Q = np.array(repaired["Q_coefficients_ascending"], dtype=float)
    gammas = [float(x) for x in repaired["gammas"]]
    rho: dict[str, float] = {}
    C_values: dict[str, float] = {}
    for key, endpoint in repaired["endpoints"].items():
        C_c = cauchy_column_value(endpoint["h_rep_coefficients_ascending"], Q, gammas, c_value)
        C_values[key] = C_c
        rho[key] = -C_c
    return {
        "c": c_value,
        "R_c": real_R_value(c_value, gammas),
        "C_gamma_at_c": C_values,
        "rho_S": rho,
    }


def right_exterior_potential_payload(
    repaired: dict[str, Any],
    source: dict[str, Any],
    nodes: int = 500,
) -> dict[str, Any]:
    Q = np.array(repaired["Q_coefficients_ascending"], dtype=float)
    gammas = [float(x) for x in repaired["gammas"]]
    right_endpoint = max(gammas)
    points: dict[str, float] = {}
    for key in ["u", "v"]:
        if key in source:
            points[key] = float(source[key])
    for index, value in enumerate(source.get("contact_points", []) or []):
        points[f"contact_{index}"] = float(value)

    values: dict[str, dict[str, float]] = {}
    skipped: dict[str, str] = {}
    for name, point in points.items():
        if point <= right_endpoint:
            skipped[name] = "not in right exterior component"
            continue
        row: dict[str, float] = {}
        for key, endpoint in repaired["endpoints"].items():
            row[key] = integrate_to_infinity_right_exterior(
                lambda y, coeffs=endpoint["h_rep_coefficients_ascending"]: cauchy_column_value(
                    coeffs, Q, gammas, y
                ),
                point,
                right_endpoint,
                nodes=nodes,
            )
        if "kappa" in source:
            kappa = float(source["kappa"])
            row["Pi"] = integrate_to_infinity_right_exterior(
                lambda y: period_cauchy_value(kappa, gammas, y),
                point,
                right_endpoint,
                nodes=nodes,
            )
        values[name] = row

    boundary_b: dict[str, float] | None = None
    if {"a", "b", "u", "v"}.issubset(source) and "u" in values and "v" in values:
        a_weight = float(source["a"])
        b_weight = float(source["b"])
        boundary_b = {}
        for key in values["u"]:
            if key in values["v"]:
                boundary_b[key] = a_weight * values["u"][key] + b_weight * values["v"][key]

    return {
        "component": "right_exterior",
        "right_endpoint": right_endpoint,
        "quadrature": "Gauss-Legendre after y=s+t/(1-t)",
        "nodes": nodes,
        "values": values,
        "skipped": skipped,
        "b": boundary_b,
    }


def sign_label(value: float, tol: float = 1.0e-10) -> int:
    if value > tol:
        return 1
    if value < -tol:
        return -1
    return 0


def right_exterior_offrow_determinant_payload(
    potentials: dict[str, Any],
    rho_payload: dict[str, Any] | None,
    gammas: list[float],
) -> dict[str, Any] | None:
    if rho_payload is None:
        return None
    values = potentials.get("values", {})
    contact_names = sorted(name for name in values if name.startswith("contact_"))
    if len(contact_names) < 4:
        return {
            "status": "insufficient_contacts",
            "available_contact_rows": contact_names,
            "required": 4,
        }
    selected = contact_names[:4]
    gamma_keys = [f"{gamma:.17g}" for gamma in gammas]
    matrix = np.array(
        [[float(values[name][gamma_key]) for gamma_key in gamma_keys] for name in selected],
        dtype=float,
    )
    rho_row = np.array([float(rho_payload["rho_S"][gamma_key]) for gamma_key in gamma_keys], dtype=float)
    det_E = float(np.linalg.det(matrix))
    cofactors: list[dict[str, Any]] = []
    cofactor_signs: list[int] = []
    for index in range(4):
        replaced = matrix.copy()
        replaced[index, :] = rho_row
        det_i = float(np.linalg.det(replaced))
        sign_i = sign_label(det_i / det_E) if sign_label(det_E) != 0 else 0
        cofactor_signs.append(sign_i)
        cofactors.append(
            {
                "row_index": index,
                "contact": selected[index],
                "det_replace_row_by_rho": det_i,
                "relative_sign": sign_i,
            }
        )
    alternates = all(
        cofactor_signs[i] != 0 and cofactor_signs[i + 1] == -cofactor_signs[i]
        for i in range(3)
    )
    return {
        "status": "computed",
        "component": "right_exterior",
        "selected_contacts": selected,
        "gamma_order": gamma_keys,
        "det_E": det_E,
        "det_E_sign": sign_label(det_E),
        "cofactors": cofactors,
        "relative_signs": cofactor_signs,
        "alternating_relative_signs": alternates,
    }


def right_exterior_offrow_grid_payload(
    repaired: dict[str, Any],
    rho_payload: dict[str, Any] | None,
    source: dict[str, Any],
    nodes: int = 500,
) -> dict[str, Any] | None:
    if rho_payload is None:
        return None
    spec = source.get("right_exterior_grid")
    if spec is None:
        return None
    if not isinstance(spec, dict):
        raise ValueError("right_exterior_grid must be an object")
    start = float(spec["start"])
    stop = float(spec["stop"])
    count = int(spec.get("count", 8))
    if count < 4:
        raise ValueError("right_exterior_grid.count must be at least 4")
    if not start < stop:
        raise ValueError("right_exterior_grid requires start < stop")

    Q = np.array(repaired["Q_coefficients_ascending"], dtype=float)
    gammas = [float(x) for x in repaired["gammas"]]
    right_endpoint = max(gammas)
    if start <= right_endpoint:
        raise ValueError("right_exterior_grid.start must be in the right exterior component")

    gamma_keys = [f"{gamma:.17g}" for gamma in gammas]
    grid = np.linspace(start, stop, count)
    rows_by_point: dict[float, list[float]] = {}
    for point in grid:
        row = []
        for gamma_key in gamma_keys:
            endpoint = repaired["endpoints"][gamma_key]
            row.append(
                integrate_to_infinity_right_exterior(
                    lambda y, coeffs=endpoint["h_rep_coefficients_ascending"]: cauchy_column_value(
                        coeffs, Q, gammas, y
                    ),
                    float(point),
                    right_endpoint,
                    nodes=nodes,
                )
            )
        rows_by_point[float(point)] = row

    rho_row = np.array([float(rho_payload["rho_S"][gamma_key]) for gamma_key in gamma_keys], dtype=float)
    total = 0
    alternating = 0
    singular = 0
    min_abs_det_E = math.inf
    min_abs_det_tuple: dict[str, Any] | None = None
    first_failure: dict[str, Any] | None = None
    sign_patterns: dict[str, int] = {}

    from itertools import combinations

    for combo in combinations(range(count), 4):
        total += 1
        points = [float(grid[i]) for i in combo]
        matrix = np.array([rows_by_point[point] for point in points], dtype=float)
        det_E = float(np.linalg.det(matrix))
        if abs(det_E) < min_abs_det_E:
            min_abs_det_E = abs(det_E)
            min_abs_det_tuple = {"points": points, "det_E": det_E}
        if sign_label(det_E) == 0:
            singular += 1
            sign_patterns["singular"] = sign_patterns.get("singular", 0) + 1
            if first_failure is None:
                first_failure = {"kind": "singular", "points": points, "det_E": det_E}
            continue
        signs: list[int] = []
        cofactors = []
        for index in range(4):
            replaced = matrix.copy()
            replaced[index, :] = rho_row
            det_i = float(np.linalg.det(replaced))
            sign_i = sign_label(det_i / det_E)
            signs.append(sign_i)
            cofactors.append(det_i)
        pattern_key = ",".join(str(sign) for sign in signs)
        sign_patterns[pattern_key] = sign_patterns.get(pattern_key, 0) + 1
        ok = all(signs[i] != 0 and signs[i + 1] == -signs[i] for i in range(3))
        if ok:
            alternating += 1
        elif first_failure is None:
            first_failure = {
                "kind": "nonalternating",
                "points": points,
                "det_E": det_E,
                "relative_signs": signs,
                "cofactors": cofactors,
            }

    return {
        "status": "computed",
        "component": "right_exterior",
        "grid_start": start,
        "grid_stop": stop,
        "grid_count": count,
        "quad_nodes": nodes,
        "total_four_tuples": total,
        "alternating_four_tuples": alternating,
        "singular_four_tuples": singular,
        "min_abs_det_E": None if math.isinf(min_abs_det_E) else min_abs_det_E,
        "min_abs_det_tuple": min_abs_det_tuple,
        "nonalternating_four_tuples": total - alternating - singular,
        "sign_patterns": sign_patterns,
        "first_failure": first_failure,
        "all_nonsingular_alternating": total > 0 and alternating == total,
    }


def run_chart_json(path: Path) -> dict[str, Any]:
    P, Q, gammas, rows, source = load_chart_json(path)
    repaired = extract_repaired_data(P, Q, gammas, rows)
    period_residual = period_endpoint_quotient_residual(P, Q, gammas)
    result = {
        "path": str(path),
        "description": source.get("description"),
        "repaired": repaired,
        "period_endpoint_quotient": period_residual,
        "optional_fields_present": {
            key: key in source for key in ["kappa", "Z0", "u", "c", "v", "contact_points"]
        },
    }
    if "c" in source:
        result["anchor_rho"] = anchor_rho_payload(repaired, float(source["c"]))
    if any(key in source for key in ["u", "v", "contact_points"]):
        result["right_exterior_potentials"] = right_exterior_potential_payload(repaired, source)
    if "right_exterior_potentials" in result:
        result["right_exterior_offrow_determinants"] = right_exterior_offrow_determinant_payload(
            result["right_exterior_potentials"],
            result.get("anchor_rho"),
            [float(x) for x in repaired["gammas"]],
        )
    grid_payload = right_exterior_offrow_grid_payload(repaired, result.get("anchor_rho"), source)
    if grid_payload is not None:
        result["right_exterior_offrow_grid"] = grid_payload
    return result


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
    parser.add_argument("--audit-two-interval-json", help="audit old two-interval JSON for Gate 1 readiness")
    parser.add_argument("--scan-jsons", help="scan a directory for Gate 1 chart JSON candidates")
    parser.add_argument("--chart-json", help="run extractor on a proof-grade chart JSON")
    parser.add_argument("--P", help="ascending coefficients, comma-separated")
    parser.add_argument("--Q", help="ascending coefficients, comma-separated")
    parser.add_argument("--gammas", help="branch endpoints, comma-separated")
    parser.add_argument("--rows", help="row specs: eval:x,deriv:x:1,...")
    parser.add_argument("--write-json", help="write extractor output")
    args = parser.parse_args()

    if args.scan_jsons:
        scan = scan_jsons_for_gate1(Path(args.scan_jsons))
        print("Gate 1 JSON input scan")
        print(f"  root = {scan['root']}")
        print(f"  total JSON files = {scan['total_json_files']}")
        print(f"  counts by kind = {scan['counts_by_kind']}")
        print(f"  gate1 chart ready = {scan['gate1_chart_ready_count']}")
        if scan["gate1_chart_ready"]:
            print("  ready chart candidates:")
            for record in scan["gate1_chart_ready"]:
                print(f"    - {record['path']}")
        print(f"  old two-interval diagnostics = {scan['old_two_interval_diagnostic_count']}")
        if scan["old_two_interval_diagnostics"]:
            print("  first old diagnostic:")
            first = scan["old_two_interval_diagnostics"][0]
            print(f"    path = {first['path']}")
            print(f"    missing = {', '.join(first['missing_required_fields'])}")
        if scan["malformed_gate1_chart_count"]:
            print(f"  malformed Gate 1 chart JSONs = {scan['malformed_gate1_chart_count']}")
        if args.write_json:
            with open(args.write_json, "w", encoding="utf-8") as handle:
                json.dump(scan, handle, indent=2, sort_keys=True)
            print(f"  wrote {args.write_json}")
        return 0

    if args.audit_two_interval_json:
        audit = audit_two_interval_json(Path(args.audit_two_interval_json))
        print("Gate 1 old two-interval input audit")
        print(f"  path = {audit['path']}")
        print(f"  rows = {audit['row_count']}")
        print(f"  gate1_ready = {audit['gate1_ready']}")
        print(f"  reason = {audit['reason']}")
        first = audit["rows"][0]
        print(f"  first old ansatz P = {first['old_ansatz_P_coefficients_ascending']}")
        print(f"  first old ansatz Q = {first['old_ansatz_Q_coefficients_ascending']}")
        print(f"  missing = {', '.join(first['missing_gate1_inputs'])}")
        if args.write_json:
            with open(args.write_json, "w", encoding="utf-8") as handle:
                json.dump(audit, handle, indent=2, sort_keys=True)
            print(f"  wrote {args.write_json}")
        return 0

    if args.chart_json:
        payload = run_chart_json(Path(args.chart_json))
        repaired = payload["repaired"]
        period = payload["period_endpoint_quotient"]
        print("Gate 1 repaired chart JSON")
        print(f"  path = {payload['path']}")
        print(
            "  deg P, deg Q, #gammas = "
            f"{len(repaired['P_coefficients_ascending'])-1} "
            f"{len(repaired['Q_coefficients_ascending'])-1} "
            f"{len(repaired['gammas'])}"
        )
        print(f"  rows/correction columns = {len(repaired['rows'])}")
        print(f"  det(A) = {repaired['det_A']:.12e}")
        print(f"  cond(A) = {repaired['cond_A']:.12e}")
        print(f"  max |AX+r| = {repaired['max_abs_AX_plus_r']:.12e}")
        print(f"  max repaired chart row = {repaired['max_abs_chart_row_after_repair']:.12e}")
        print(
            "  period quotient remainder = "
            f"{period['max_abs_remainder_after_dividing_by_D']:.12e}"
        )
        print(f"  optional fields = {payload['optional_fields_present']}")
        if "anchor_rho" in payload:
            rho = payload["anchor_rho"]
            max_abs_rho = max(abs(value) for value in rho["rho_S"].values())
            print(f"  R(c) = {rho['R_c']:.12e}")
            print(f"  max |rho_S| = {max_abs_rho:.12e}")
        if "right_exterior_potentials" in payload:
            potentials = payload["right_exterior_potentials"]
            computed = len(potentials["values"])
            skipped = len(potentials["skipped"])
            print(f"  right-exterior V rows computed/skipped = {computed}/{skipped}")
            if potentials.get("b") is not None:
                max_abs_b = max(abs(value) for value in potentials["b"].values())
                print(f"  max |b| = {max_abs_b:.12e}")
        if payload.get("right_exterior_offrow_determinants"):
            det_payload = payload["right_exterior_offrow_determinants"]
            print(f"  right-exterior offrow status = {det_payload['status']}")
            if det_payload["status"] == "computed":
                print(f"  det(E) = {det_payload['det_E']:.12e}")
                print(f"  relative signs = {det_payload['relative_signs']}")
                print(f"  alternating = {det_payload['alternating_relative_signs']}")
        if payload.get("right_exterior_offrow_grid"):
            grid_payload = payload["right_exterior_offrow_grid"]
            print(
                "  right-exterior grid alternating = "
                f"{grid_payload['alternating_four_tuples']}/{grid_payload['total_four_tuples']}"
            )
            print(f"  right-exterior grid singular = {grid_payload['singular_four_tuples']}")
            print(f"  right-exterior grid nonalternating = {grid_payload['nonalternating_four_tuples']}")
            print(f"  right-exterior grid patterns = {grid_payload['sign_patterns']}")
            print(f"  right-exterior grid all ok = {grid_payload['all_nonsingular_alternating']}")
        if args.write_json:
            with open(args.write_json, "w", encoding="utf-8") as handle:
                json.dump(payload, handle, indent=2, sort_keys=True)
            print(f"  wrote {args.write_json}")
        return 0

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
