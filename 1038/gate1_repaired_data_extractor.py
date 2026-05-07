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
from itertools import combinations
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


def q_roots_real(Q: Array, tol: float = 1.0e-8) -> list[float]:
    roots = np.roots(list(reversed(trim(Q))))
    real_roots = []
    for root in roots:
        if abs(root.imag) > tol:
            raise ValueError(f"Q has non-real root {root}")
        real_roots.append(float(root.real))
    return sorted(real_roots)


def pole_row_subset_audit(P: Array, Q: Array, gammas: list[float]) -> dict[str, Any]:
    """Enumerate square subgauges of pole eval/deriv rows on the correction image."""
    D = poly_from_roots(gammas)
    d = len(trim(Q)) - 1
    basis = canonical_correction_basis(D, d)
    roots = q_roots_real(Q)
    rows: list[Row] = []
    for index, root in enumerate(roots):
        rows.append(Row("eval", root, name=f"Qpole_{index}_eval"))
        rows.append(Row("deriv", root, order=1, name=f"Qpole_{index}_deriv"))
    ncols = len(basis)
    full_rank = []
    singular = 0
    min_abs_det = math.inf
    max_abs_det = 0.0
    det_sign_counts: dict[str, int] = {}
    kind_pattern_counts: dict[str, int] = {}
    kind_pattern_sign_counts: dict[str, dict[str, int]] = {}
    named_pattern_sign_counts: dict[str, dict[str, int]] = {}
    full_pair_subsets = []
    for combo in combinations(range(len(rows)), ncols):
        matrix = np.array([[rows[i].apply(col) for col in basis] for i in combo], dtype=float)
        det = float(np.linalg.det(matrix))
        abs_det = abs(det)
        min_abs_det = min(min_abs_det, abs_det)
        max_abs_det = max(max_abs_det, abs_det)
        det_sign = sign_label(det)
        sign_key = str(det_sign)
        row_names = [rows[i].to_json()["name"] for i in combo]
        kind_pattern = ",".join("E" if rows[i].kind == "eval" else f"D{rows[i].order}" for i in combo)
        named_pattern = ",".join(str(name) for name in row_names)
        kind_pattern_counts[kind_pattern] = kind_pattern_counts.get(kind_pattern, 0) + 1
        det_sign_counts[sign_key] = det_sign_counts.get(sign_key, 0) + 1
        kind_pattern_sign_counts.setdefault(kind_pattern, {})
        kind_pattern_sign_counts[kind_pattern][sign_key] = (
            kind_pattern_sign_counts[kind_pattern].get(sign_key, 0) + 1
        )
        named_pattern_sign_counts.setdefault(named_pattern, {})
        named_pattern_sign_counts[named_pattern][sign_key] = (
            named_pattern_sign_counts[named_pattern].get(sign_key, 0) + 1
        )
        if det_sign == 0:
            singular += 1
            continue
        selected_pairs = {
            i // 2 for i in combo if i % 2 == 0 and i + 1 in combo
        }
        is_full_pair_subset = len(selected_pairs) * 2 == len(combo)
        if is_full_pair_subset:
            selected_roots = [roots[index] for index in sorted(selected_pairs)]
            formula_det = 1.0
            selected_M = np.array([1.0])
            for root in selected_roots:
                formula_det *= poly_eval(D, root) ** 2
                selected_M = poly_mul(selected_M, np.array([-root, 1.0]))
            for left, right in combinations(selected_roots, 2):
                formula_det *= (right - left) ** 4
            repaired_formula_errors: dict[str, float] = {}
            repaired_endpoint_constants: dict[str, float] = {}
            repaired_formula_max_relative_error = 0.0
            repaired = extract_repaired_data(P, Q, gammas, [rows[i] for i in combo])
            selected_M_squared = poly_mul(selected_M, selected_M)
            for gamma in gammas:
                D_gamma = divide_by_linear(D, gamma)
                coeff = (
                    -0.5
                    * poly_eval(P, gamma)
                    * poly_eval(Q, gamma)
                    / (poly_eval(selected_M, gamma) ** 2)
                )
                repaired_endpoint_constants[f"{gamma:.17g}"] = float(coeff)
                formula_h = poly_scale(poly_mul(selected_M_squared, D_gamma), coeff)
                endpoint = repaired["endpoints"][f"{gamma:.17g}"]
                direct_h = np.array(endpoint["h_rep_coefficients_ascending"], dtype=float)
                width = max(len(formula_h), len(direct_h))
                formula_padded = np.pad(formula_h, (0, width - len(formula_h)))
                direct_padded = np.pad(direct_h, (0, width - len(direct_h)))
                relative_error = float(
                    np.linalg.norm(direct_padded - formula_padded)
                    / max(1.0, np.linalg.norm(formula_padded))
                )
                repaired_formula_errors[f"{gamma:.17g}"] = relative_error
                repaired_formula_max_relative_error = max(
                    repaired_formula_max_relative_error, relative_error
                )
            full_pair_subsets.append(
                {
                    "pole_indices": sorted(selected_pairs),
                    "omitted_pole_indices": [
                        index for index in range(len(roots)) if index not in selected_pairs
                    ],
                    "row_names": row_names,
                    "det": det,
                    "det_sign": det_sign,
                    "full_pair_formula_det": formula_det,
                    "full_pair_formula_relative_error": (
                        abs(det - formula_det) / max(1.0, abs(formula_det))
                    ),
                    "repaired_endpoint_formula_relative_errors": repaired_formula_errors,
                    "repaired_endpoint_formula_max_relative_error": (
                        repaired_formula_max_relative_error
                    ),
                    "repaired_endpoint_constants": repaired_endpoint_constants,
                    "repaired_endpoint_constant_signs": {
                        key: sign_label(value)
                        for key, value in repaired_endpoint_constants.items()
                    },
                }
            )
        full_rank.append(
            {
                "row_indices": list(combo),
                "row_names": row_names,
                "row_kind_pattern": kind_pattern,
                "det": det,
                "det_sign": det_sign,
            }
        )
    nonzero_signs = sorted(
        int(sign) for sign, count in det_sign_counts.items() if sign != "0" and count
    )
    full_pair_signs = sorted({item["det_sign"] for item in full_pair_subsets})
    max_full_pair_formula_relative_error = (
        max(item["full_pair_formula_relative_error"] for item in full_pair_subsets)
        if full_pair_subsets
        else None
    )
    max_full_pair_repaired_formula_relative_error = (
        max(item["repaired_endpoint_formula_max_relative_error"] for item in full_pair_subsets)
        if full_pair_subsets
        else None
    )
    return {
        "degree_Q": d,
        "gammas": gammas,
        "q_roots": roots,
        "candidate_rows": [row.to_json() for row in rows],
        "correction_columns": ncols,
        "total_subsets": math.comb(len(rows), ncols) if len(rows) >= ncols else 0,
        "full_rank_subsets": len(full_rank),
        "singular_subsets": singular,
        "min_abs_det": None if math.isinf(min_abs_det) else min_abs_det,
        "max_abs_det": max_abs_det,
        "first_full_rank_subset": full_rank[0] if full_rank else None,
        "full_rank_subsets_preview": full_rank[:10],
        "det_sign_counts": det_sign_counts,
        "nonzero_det_signs": nonzero_signs,
        "all_full_rank_subsets_same_orientation": len(nonzero_signs) <= 1 and singular == 0,
        "row_kind_pattern_counts": kind_pattern_counts,
        "row_kind_pattern_sign_counts": kind_pattern_sign_counts,
        "named_pattern_sign_counts_preview": dict(list(named_pattern_sign_counts.items())[:10]),
        "full_confluent_pair_subsets": full_pair_subsets,
        "full_confluent_pair_subset_count": len(full_pair_subsets),
        "full_confluent_pair_subset_signs": full_pair_signs,
        "all_full_confluent_pair_subsets_same_orientation": len(full_pair_signs) <= 1,
        "max_full_confluent_pair_formula_relative_error": max_full_pair_formula_relative_error,
        "max_full_confluent_pair_repaired_formula_relative_error": (
            max_full_pair_repaired_formula_relative_error
        ),
    }


def endpoint_heavy_split_pattern_audit() -> dict[str, Any]:
    """Diagnostic quartic primitive audit for endpoint-heavy 2+2 split patterns.

    This is a bare model on [-2,-1] union [1,2].  It is not a Gate 1 chart
    certificate; it only checks which contact pattern types are plausible
    before the actual split-connection row is used.
    """
    intervals = [(-2.0, -1.0), (1.0, 2.0)]
    patterns = [
        (("L", "R"), ("L", "R")),
        (("L", "R"), ("L", "I")),
        (("L", "R"), ("I", "R")),
        (("L", "I"), ("L", "R")),
        (("I", "R"), ("L", "R")),
    ]

    def contact_x(component_index: int, marker: str) -> float:
        left, right = intervals[component_index]
        if marker == "L":
            return left
        if marker == "R":
            return right
        if marker == "I":
            return 0.5 * (left + right)
        raise ValueError(marker)

    records = []
    for pattern in patterns:
        root_budget_by_component = []
        for component in pattern:
            interior_count = sum(1 for marker in component if marker == "I")
            root_budget_by_component.append(1 + interior_count)
        xs = [
            contact_x(component_index, marker)
            for component_index, component in enumerate(pattern)
            for marker in component
        ]
        matrix = np.array([[1.0, x, x * x, x * x * x] for x in xs], dtype=float)
        rhs = np.array([-x**4 for x in xs], dtype=float)
        coefficients = np.linalg.solve(matrix, rhs)
        primitive = np.array([*coefficients, 1.0], dtype=float)
        derivative = poly_derivative(primitive)
        grid = np.concatenate(
            [
                np.linspace(intervals[0][0], intervals[0][1], 201),
                np.linspace(intervals[1][0], intervals[1][1], 201),
            ]
        )
        values = np.polynomial.polynomial.polyval(grid, primitive)
        endpoint_derivatives = {
            "left_component_left_endpoint": poly_eval(derivative, intervals[0][0]),
            "left_component_right_endpoint": poly_eval(derivative, intervals[0][1]),
            "right_component_left_endpoint": poly_eval(derivative, intervals[1][0]),
            "right_component_right_endpoint": poly_eval(derivative, intervals[1][1]),
        }
        inward_signs_ok = (
            endpoint_derivatives["left_component_left_endpoint"] >= -1.0e-10
            and endpoint_derivatives["left_component_right_endpoint"] <= 1.0e-10
            and endpoint_derivatives["right_component_left_endpoint"] >= -1.0e-10
            and endpoint_derivatives["right_component_right_endpoint"] <= 1.0e-10
        )
        records.append(
            {
                "pattern": pattern,
                "contact_points": xs,
                "forced_numerator_roots_by_component": root_budget_by_component,
                "forced_numerator_roots_total": sum(root_budget_by_component),
                "primitive_coefficients_ascending": primitive.tolist(),
                "derivative_coefficients_ascending": derivative.tolist(),
                "sample_min_on_components": float(np.min(values)),
                "endpoint_derivatives": endpoint_derivatives,
                "all_endpoint_inward_signs_ok": bool(inward_signs_ok),
            }
        )
    return {
        "model": "monic quartic primitive on [-2,-1] union [1,2]",
        "records": records,
        "patterns_with_nonnegative_sample": [
            record["pattern"] for record in records if record["sample_min_on_components"] >= -1.0e-10
        ],
        "patterns_with_all_endpoint_inward_signs_ok": [
            record["pattern"] for record in records if record["all_endpoint_inward_signs_ok"]
        ],
        "forced_numerator_root_budgets": {
            str(record["pattern"]): record["forced_numerator_roots_total"]
            for record in records
        },
    }


def split_R_value(x: float, gammas: list[float]) -> float:
    a1, b1, a2, b2 = sorted(gammas)
    radicand = math.prod(x - gamma for gamma in [a1, b1, a2, b2])
    if radicand <= 0.0:
        raise ValueError(f"x={x} is not in a real off-cut gap for gammas={gammas}")
    sign = -1.0 if b1 < x < a2 else 1.0
    return sign * math.sqrt(radicand)


def split_cut_R_abs(x: float, gammas: list[float]) -> float:
    a1, b1, a2, b2 = sorted(gammas)
    if a1 < x < b1 or a2 < x < b2:
        return math.sqrt(abs(math.prod(x - gamma for gamma in [a1, b1, a2, b2])))
    raise ValueError(f"x={x} is not inside a cut component for gammas={gammas}")


def integrate_real_interval(func: Any, left: float, right: float, nodes: int = 200) -> float:
    xs, ws = np.polynomial.legendre.leggauss(nodes)
    mid = 0.5 * (left + right)
    half = 0.5 * (right - left)
    total = 0.0
    for x, w in zip(xs, ws):
        total += float(w) * func(float(mid + half * x))
    return float(half * total)


def endpoint_heavy_connection_audit(
    gammas: list[float] | None = None,
    omitted_pole: float = 0.0,
    nodes: int = 200,
) -> dict[str, Any]:
    """Diagnostic connection-integral audit for endpoint-heavy split patterns.

    This uses a normalized full-pair kernel 1 / ((x-p)^2 R(x)) with one omitted
    pole p.  It is not a Gate 1 certificate; it checks whether the proposed
    split-connection sign is stable in a concrete two-cut model.
    """
    if gammas is None:
        gammas = [-2.0, -1.0, 1.0, 2.0]
    a1, b1, a2, b2 = sorted(gammas)
    left_interval = (a1, b1)
    right_interval = (a2, b2)
    patterns = [
        (("L", "R"), ("L", "R")),
        (("L", "R"), ("L", "I")),
        (("L", "R"), ("I", "R")),
        (("L", "I"), ("L", "R")),
        (("I", "R"), ("L", "R")),
    ]

    def point(component_index: int, marker: str) -> float:
        left, right = left_interval if component_index == 0 else right_interval
        if marker == "L":
            return left
        if marker == "R":
            return right
        if marker == "I":
            return 0.5 * (left + right)
        raise ValueError(marker)

    def interval_mid(lo: float, hi: float) -> float:
        return 0.5 * (lo + hi)

    def forced_roots(pattern: tuple[tuple[str, str], tuple[str, str]]) -> list[float]:
        roots: list[float] = []
        for component_index, component in enumerate(pattern):
            x0 = point(component_index, component[0])
            x1 = point(component_index, component[1])
            roots.append(interval_mid(x0, x1))
            for marker in component:
                if marker == "I":
                    roots.append(point(component_index, "I"))
        return roots

    def omega_gap_value(poly: Array, x: float) -> float:
        denom = ((x - omitted_pole) ** 2) * split_R_value(x, gammas)
        return poly_eval(poly, x) / denom

    def omega_cut_value(poly: Array, x: float) -> float:
        denom = ((x - omitted_pole) ** 2) * split_cut_R_abs(x, gammas)
        return poly_eval(poly, x) / denom

    def safe_integral(poly: Array, left: float, right: float) -> float:
        if abs(right - left) < 1.0e-12:
            return 0.0
        if right < left:
            return -safe_integral(poly, right, left)
        eps = 1.0e-8
        if a1 <= left and right <= b1:
            return integrate_real_interval(
                lambda x, p=poly: omega_cut_value(p, x),
                left + eps,
                right - eps,
                nodes=nodes,
            )
        if a2 <= left and right <= b2:
            return integrate_real_interval(
                lambda x, p=poly: omega_cut_value(p, x),
                left + eps,
                right - eps,
                nodes=nodes,
            )
        total = 0.0
        if left < b1:
            total += safe_integral(poly, left, b1)
            left = b1
        if left < a2 and right > b1:
            total += integrate_real_interval(
                lambda x, p=poly: omega_gap_value(p, x),
                max(left, b1) + eps,
                min(right, a2) - eps,
                nodes=nodes,
            )
            left = a2
        if right > a2:
            total += safe_integral(poly, max(left, a2), right)
        return float(total)

    def pattern_contacts(pattern: tuple[tuple[str, str], tuple[str, str]], params: dict[str, float]) -> list[float]:
        contacts = []
        for component_index, component in enumerate(pattern):
            left, right = left_interval if component_index == 0 else right_interval
            for marker in component:
                if marker == "L":
                    contacts.append(left)
                elif marker == "R":
                    contacts.append(right)
                elif marker == "I":
                    contacts.append(params[f"y{component_index}"])
        return contacts

    def roots_from_params(pattern: tuple[tuple[str, str], tuple[str, str]], params: dict[str, float]) -> list[float]:
        roots = []
        for component_index, component in enumerate(pattern):
            left, right = left_interval if component_index == 0 else right_interval
            if component == ("L", "R"):
                roots.append(params[f"r{component_index}"])
            elif component == ("L", "I"):
                roots.append(params[f"r{component_index}"])
                roots.append(params[f"y{component_index}"])
            elif component == ("I", "R"):
                roots.append(params[f"y{component_index}"])
                roots.append(params[f"r{component_index}"])
            else:
                raise ValueError(component)
        if len(roots) == 2:
            roots.append(params["q"])
        return roots

    def solve_pattern(pattern: tuple[tuple[str, str], tuple[str, str]]) -> list[dict[str, Any]]:
        from scipy.optimize import least_squares

        specs = []
        lower = []
        upper = []
        start = []
        for component_index, component in enumerate(pattern):
            left, right = left_interval if component_index == 0 else right_interval
            if component == ("L", "R"):
                specs.append((f"r{component_index}", left, right))
                lower.append(left + 1.0e-5)
                upper.append(right - 1.0e-5)
                start.append(0.5 * (left + right))
            elif component == ("L", "I"):
                specs.extend([(f"y{component_index}", left, right), (f"r{component_index}", left, right)])
                lower.extend([left + 1.0e-5, left + 1.0e-5])
                upper.extend([right - 1.0e-5, right - 1.0e-5])
                start.extend([left + 0.65 * (right - left), left + 0.35 * (right - left)])
            elif component == ("I", "R"):
                specs.extend([(f"y{component_index}", left, right), (f"r{component_index}", left, right)])
                lower.extend([left + 1.0e-5, left + 1.0e-5])
                upper.extend([right - 1.0e-5, right - 1.0e-5])
                start.extend([left + 0.35 * (right - left), left + 0.65 * (right - left)])
        if len(specs) == 2:
            specs.append(("q", a1 - 4.0, b2 + 4.0))
            lower.append(a1 - 10.0)
            upper.append(b2 + 10.0)
            start.append(0.5 * (b1 + a2))

        def unpack(vector: Array) -> dict[str, float]:
            return {name: float(value) for (name, _lo, _hi), value in zip(specs, vector)}

        def residual(vector: Array) -> Array:
            params = unpack(vector)
            # Enforce ordering for LI/IR by penalty residuals.
            penalties = []
            for component_index, component in enumerate(pattern):
                if component == ("L", "I"):
                    penalties.append(max(0.0, params[f"r{component_index}"] - params[f"y{component_index}"]))
                elif component == ("I", "R"):
                    penalties.append(max(0.0, params[f"y{component_index}"] - params[f"r{component_index}"]))
            roots = roots_from_params(pattern, params)
            poly = poly_from_roots(roots)
            contacts = pattern_contacts(pattern, params)
            return np.array(
                [
                    safe_integral(poly, contacts[0], contacts[1]),
                    safe_integral(poly, contacts[2], contacts[3]),
                    *penalties,
                ],
                dtype=float,
            )

        solutions = []
        starts = [np.array(start, dtype=float)]
        for jitter in np.linspace(-0.35, 0.35, 5):
            v = np.array(start, dtype=float)
            for index, (_name, lo, hi) in enumerate(specs):
                v[index] = min(max(v[index] + jitter * (hi - lo), lo + 1.0e-5), hi - 1.0e-5)
            starts.append(v)
        for seed in starts:
            result = least_squares(
                residual,
                seed,
                bounds=(np.array(lower), np.array(upper)),
                xtol=1.0e-10,
                ftol=1.0e-10,
                gtol=1.0e-10,
                max_nfev=2000,
            )
            if float(np.linalg.norm(residual(result.x))) > 1.0e-6:
                continue
            params = unpack(result.x)
            roots = roots_from_params(pattern, params)
            poly = poly_from_roots(roots)
            contacts = pattern_contacts(pattern, params)
            connection = safe_integral(poly, contacts[1], contacts[2])
            if not any(
                np.linalg.norm(result.x - np.array(existing["vector"], dtype=float)) < 1.0e-5
                for existing in solutions
            ):
                solutions.append(
                    {
                        "vector": result.x.tolist(),
                        "params": params,
                        "roots": roots,
                        "contacts": contacts,
                        "connection_integral": connection,
                        "connection_sign": sign_label(connection),
                        "within_integrals": [
                            safe_integral(poly, contacts[0], contacts[1]),
                            safe_integral(poly, contacts[2], contacts[3]),
                        ],
                    }
                )
        return solutions

    records = []
    for pattern in patterns:
        roots = forced_roots(pattern)
        if len(roots) > 3:
            continue
        free_root_candidates = []
        if len(roots) < 3:
            free_root_candidates = [
                a1 - 1.0,
                0.5 * (b1 + a2),
                b2 + 1.0,
            ]
        else:
            free_root_candidates = [None]
        for free_root in free_root_candidates:
            all_roots = list(roots)
            if free_root is not None:
                all_roots.append(float(free_root))
            numerator = poly_from_roots(all_roots)
            left_component_integral = integrate_real_interval(
                lambda x, p=numerator: omega_cut_value(p, x),
                a1 + 1.0e-8,
                b1 - 1.0e-8,
                nodes=nodes,
            )
            gap_integral = integrate_real_interval(
                lambda x, p=numerator: omega_gap_value(p, x),
                b1 + 1.0e-8,
                a2 - 1.0e-8,
                nodes=nodes,
            )
            right_component_integral = integrate_real_interval(
                lambda x, p=numerator: omega_cut_value(p, x),
                a2 + 1.0e-8,
                b2 - 1.0e-8,
                nodes=nodes,
            )
            records.append(
                {
                    "pattern": pattern,
                    "forced_roots": roots,
                    "free_root": free_root,
                    "numerator_coefficients_ascending": numerator.tolist(),
                    "left_component_integral": left_component_integral,
                    "gap_connection_integral": gap_integral,
                    "right_component_integral": right_component_integral,
                    "connection_sign": sign_label(gap_integral),
                }
            )
        solved = solve_pattern(pattern)
        for solution in solved:
            records.append(
                {
                    "pattern": pattern,
                    "solved_contact_equations": True,
                    **solution,
                }
            )
    sign_counts: dict[str, int] = {}
    solved_sign_counts_by_pattern: dict[str, dict[str, int]] = {}
    for record in records:
        key = str(record["connection_sign"])
        sign_counts[key] = sign_counts.get(key, 0) + 1
        if record.get("solved_contact_equations"):
            pattern_key = str(record["pattern"])
            solved_sign_counts_by_pattern.setdefault(pattern_key, {})
            solved_sign_counts_by_pattern[pattern_key][key] = (
                solved_sign_counts_by_pattern[pattern_key].get(key, 0) + 1
            )
    return {
        "model": "normalized two-cut full-pair omitted-pole kernel",
        "gammas": gammas,
        "omitted_pole": omitted_pole,
        "nodes": nodes,
        "records": records,
        "connection_sign_counts": sign_counts,
        "solved_connection_sign_counts_by_pattern": solved_sign_counts_by_pattern,
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
    parser.add_argument("--audit-pole-row-subsets", action="store_true", help="enumerate square pole-row subgauges")
    parser.add_argument(
        "--audit-endpoint-heavy-patterns",
        action="store_true",
        help="diagnose endpoint-heavy 2+2 split contact patterns in a bare quartic model",
    )
    parser.add_argument(
        "--audit-endpoint-heavy-connection",
        action="store_true",
        help="diagnose endpoint-heavy connection integrals in a normalized two-cut model",
    )
    parser.add_argument("--connection-gammas", help="four branch endpoints for connection audit")
    parser.add_argument("--connection-omitted-pole", type=float, default=0.0)
    parser.add_argument("--connection-nodes", type=int, default=200)
    parser.add_argument("--chart-json", help="run extractor on a proof-grade chart JSON")
    parser.add_argument("--P", help="ascending coefficients, comma-separated")
    parser.add_argument("--Q", help="ascending coefficients, comma-separated")
    parser.add_argument("--gammas", help="branch endpoints, comma-separated")
    parser.add_argument("--rows", help="row specs: eval:x,deriv:x:1,...")
    parser.add_argument("--write-json", help="write extractor output")
    args = parser.parse_args()

    if args.audit_endpoint_heavy_patterns:
        audit = endpoint_heavy_split_pattern_audit()
        print("Gate 1 endpoint-heavy split pattern audit")
        print(f"  model = {audit['model']}")
        for record in audit["records"]:
            print(
                "  pattern = "
                f"{record['pattern']}, sample min = {record['sample_min_on_components']:.12e}, "
                f"inward signs = {record['all_endpoint_inward_signs_ok']}, "
                f"forced roots = {record['forced_numerator_roots_total']}"
            )
        print(
            "  nonnegative sampled patterns = "
            f"{audit['patterns_with_nonnegative_sample']}"
        )
        print(
            "  all-inward-sign patterns = "
            f"{audit['patterns_with_all_endpoint_inward_signs_ok']}"
        )
        if args.write_json:
            with open(args.write_json, "w", encoding="utf-8") as handle:
                json.dump(audit, handle, indent=2, sort_keys=True)
            print(f"  wrote {args.write_json}")
        return 0

    if args.audit_endpoint_heavy_connection:
        gammas = parse_float_list(args.connection_gammas) if args.connection_gammas else None
        audit = endpoint_heavy_connection_audit(
            gammas=gammas,
            omitted_pole=args.connection_omitted_pole,
            nodes=args.connection_nodes,
        )
        print("Gate 1 endpoint-heavy connection audit")
        print(f"  model = {audit['model']}")
        print(f"  gammas = {audit['gammas']}")
        print(f"  omitted pole = {audit['omitted_pole']}")
        print(f"  connection sign counts = {audit['connection_sign_counts']}")
        print(
            "  solved connection sign counts by pattern = "
            f"{audit['solved_connection_sign_counts_by_pattern']}"
        )
        for record in audit["records"][:12]:
            if record.get("solved_contact_equations"):
                print(
                    "  solved pattern = "
                    f"{record['pattern']}, connection = {record['connection_integral']:.6e}, "
                    f"sign = {record['connection_sign']}, params = {record['params']}"
                )
            else:
                print(
                    "  pattern = "
                    f"{record['pattern']}, free root = {record['free_root']}, "
                    f"left = {record['left_component_integral']:.6e}, "
                    f"gap = {record['gap_connection_integral']:.6e}, "
                    f"right = {record['right_component_integral']:.6e}, "
                    f"sign = {record['connection_sign']}"
                )
        if args.write_json:
            with open(args.write_json, "w", encoding="utf-8") as handle:
                json.dump(audit, handle, indent=2, sort_keys=True)
            print(f"  wrote {args.write_json}")
        return 0

    if args.audit_pole_row_subsets:
        if args.chart_json:
            P, Q, gammas, _rows, _source = load_chart_json(Path(args.chart_json))
        elif args.toy_g2:
            P, Q, gammas, _rows = toy_g2_inputs()
        else:
            if not (args.P and args.Q and args.gammas):
                parser.error("provide --toy-g2, --chart-json, or all of --P --Q --gammas")
            P = np.array(parse_float_list(args.P), dtype=float)
            Q = np.array(parse_float_list(args.Q), dtype=float)
            gammas = parse_float_list(args.gammas)
        audit = pole_row_subset_audit(P, Q, gammas)
        print("Gate 1 pole-row subset audit")
        print(f"  deg Q = {audit['degree_Q']}")
        print(f"  Q roots = {audit['q_roots']}")
        print(f"  candidate rows = {len(audit['candidate_rows'])}")
        print(f"  correction columns = {audit['correction_columns']}")
        print(f"  total square subsets = {audit['total_subsets']}")
        print(f"  full-rank subsets = {audit['full_rank_subsets']}")
        print(f"  singular subsets = {audit['singular_subsets']}")
        print(f"  min |det| = {audit['min_abs_det']}")
        print(f"  max |det| = {audit['max_abs_det']}")
        print(f"  det sign counts = {audit['det_sign_counts']}")
        print(
            "  all full-rank subsets same orientation = "
            f"{audit['all_full_rank_subsets_same_orientation']}"
        )
        print(f"  row-kind patterns = {audit['row_kind_pattern_counts']}")
        print(f"  row-kind pattern signs = {audit['row_kind_pattern_sign_counts']}")
        print(
            "  full confluent pole-pair subsets = "
            f"{audit['full_confluent_pair_subset_count']}"
        )
        print(
            "  full confluent pole-pair signs = "
            f"{audit['full_confluent_pair_subset_signs']}"
        )
        print(
            "  full confluent pole-pair same orientation = "
            f"{audit['all_full_confluent_pair_subsets_same_orientation']}"
        )
        print(
            "  max full confluent pole-pair formula relative error = "
            f"{audit['max_full_confluent_pair_formula_relative_error']}"
        )
        print(
            "  max full confluent pole-pair repaired formula relative error = "
            f"{audit['max_full_confluent_pair_repaired_formula_relative_error']}"
        )
        if audit["full_confluent_pair_subsets"]:
            first_pair = audit["full_confluent_pair_subsets"][0]
            print(
                "  first full confluent pole-pair endpoint constant signs = "
                f"{first_pair['repaired_endpoint_constant_signs']}"
            )
        if audit["first_full_rank_subset"]:
            first = audit["first_full_rank_subset"]
            print(f"  first full-rank subset = {first['row_names']}")
            print(f"  first row-kind pattern = {first['row_kind_pattern']}")
            print(f"  first det = {first['det']:.12e}")
        if args.write_json:
            with open(args.write_json, "w", encoding="utf-8") as handle:
                json.dump(audit, handle, indent=2, sort_keys=True)
            print(f"  wrote {args.write_json}")
        return 0

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
