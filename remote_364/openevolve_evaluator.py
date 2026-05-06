"""Evaluator for OpenEvolve Erdős 364 filter proposals."""

from __future__ import annotations

import importlib.util
import math
from pathlib import Path

LOCAL_PRIMES = (2, 3, 5, 7)
MAX_COMBINED_MODULUS = 500_000
MAX_FILTERS = 8
MAX_ALLOWED_SIZE = 20_000


def is_powerful(n: int) -> bool:
    if n == 1:
        return True
    m = n
    p = 2
    while p * p <= m:
        if m % p == 0:
            e = 0
            while m % p == 0:
                m //= p
                e += 1
            if e == 1:
                return False
        p += 1 if p == 2 else 2
    return m == 1


def known_pair_starts(limit: int = 200_000) -> list[int]:
    out = []
    for x in range(1, limit):
        if is_powerful(x) and is_powerful(x + 1):
            out.append(x)
        if is_powerful(x) and is_powerful(x + 2):
            out.append(x)
    return out


def load_program(path: str):
    spec = importlib.util.spec_from_file_location("candidate", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load candidate")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def local_squarefull_ok(x: int, primes: tuple[int, ...] = LOCAL_PRIMES) -> bool:
    """Necessary local condition for x, x+1, x+2 to all be powerful."""
    for p in primes:
        pp = p * p
        for i in (0, 1, 2):
            if (x + i) % p == 0 and (x + i) % pp != 0:
                return False
    return True


def normalize_filters(filters: list) -> tuple[list[tuple[int, frozenset[int]]], float]:
    normalized: list[tuple[int, frozenset[int]]] = []
    valid = 1.0
    if len(filters) > MAX_FILTERS:
        valid = 0.0
        filters = filters[:MAX_FILTERS]
    for item in filters:
        if not isinstance(item, tuple) or len(item) != 2:
            valid = 0.0
            continue
        modulus, allowed = item
        if not isinstance(modulus, int) or modulus <= 0:
            valid = 0.0
            continue
        try:
            residue_values = set()
            for index, value in enumerate(allowed):
                if index >= MAX_ALLOWED_SIZE:
                    valid = 0.0
                    break
                residue_values.add(int(value) % modulus)
        except (TypeError, ValueError, OverflowError):
            valid = 0.0
            continue
        residues = frozenset(residue_values)
        if not residues or len(residues) > MAX_ALLOWED_SIZE:
            valid = 0.0
            continue
        normalized.append((modulus, residues))
    return normalized, valid


def residue_set(modulus: int, filters: list[tuple[int, frozenset[int]]]) -> set[int]:
    return {
        x
        for x in range(modulus)
        if all(x % m in allowed for m, allowed in filters)
    }


def independence_report(filters: list[tuple[int, frozenset[int]]]) -> dict:
    """Measure whether each proposed congruence strictly shrinks candidates.

    The baseline universe is the residue set selected by the previous filters.
    Soundness is checked separately against local squarefull necessities for
    primes 2, 3, 5, 7.  A filter is independent only if adding it to previous
    filters removes at least one residue from the current candidate set.
    """
    current_modulus = 1
    current_filters: list[tuple[int, frozenset[int]]] = []
    current = residue_set(current_modulus, current_filters)
    steps = []
    redundant = 0
    invalid_lcm = False

    for index, (modulus, allowed) in enumerate(filters):
        next_modulus = math.lcm(current_modulus, modulus)
        if next_modulus > MAX_COMBINED_MODULUS:
            invalid_lcm = True
            steps.append(
                {
                    "index": index,
                    "modulus": modulus,
                    "strict_shrink": False,
                    "removed": 0,
                    "before": len(current),
                    "after": len(current),
                    "note": "combined modulus too large for evaluator",
                }
            )
            redundant += 1
            continue

        lifted_filters = current_filters
        before = residue_set(next_modulus, lifted_filters)
        after = residue_set(next_modulus, lifted_filters + [(modulus, allowed)])
        removed = len(before) - len(after)
        strict = removed > 0
        if not strict:
            redundant += 1
        steps.append(
            {
                "index": index,
                "modulus": modulus,
                "strict_shrink": strict,
                "removed": removed,
                "before": len(before),
                "after": len(after),
            }
        )
        current_modulus = next_modulus
        current_filters.append((modulus, allowed))
        current = after

    initial = residue_set(1, [])
    final = residue_set(current_modulus, current_filters)
    compression = 1.0 - len(final) / max(1, current_modulus)
    baseline_compression = 1.0 - len(initial) / 1
    independent = sum(1 for step in steps if step["strict_shrink"])
    return {
        "steps": steps,
        "redundant": redundant,
        "independent": independent,
        "invalid_lcm": invalid_lcm,
        "final_modulus": current_modulus,
        "final_candidates": len(final),
        "compression": compression,
        "incremental_compression": max(0.0, compression - baseline_compression),
    }


def combined_local_validity_report(filters: list[tuple[int, frozenset[int]]]) -> dict:
    """Check that the combined filters keep every checked local residue."""
    combined_modulus = 1
    for modulus, _allowed in filters:
        combined_modulus = math.lcm(combined_modulus, modulus)
        if combined_modulus > MAX_COMBINED_MODULUS:
            return {
                "local_valid": False,
                "checked_modulus": combined_modulus,
                "missing_local_residues": -1,
                "note": "combined modulus too large for evaluator",
            }

    checked_modulus = math.lcm(combined_modulus, math.prod(p * p for p in LOCAL_PRIMES))
    if checked_modulus > MAX_COMBINED_MODULUS:
        return {
            "local_valid": False,
            "checked_modulus": checked_modulus,
            "missing_local_residues": -1,
            "note": "local check modulus too large for evaluator",
        }

    missing = 0
    for x in range(checked_modulus):
        if local_squarefull_ok(x) and any(x % modulus not in allowed for modulus, allowed in filters):
            missing += 1

    return {
        "local_valid": missing == 0,
        "checked_modulus": checked_modulus,
        "missing_local_residues": missing,
    }


def compute_combined_score(
    valid: float,
    local_report: dict,
    report: dict,
    pair_penalty: int,
    num_filters: int,
) -> float:
    """Single normalized guidance score for OpenEvolve.

    Keep raw metrics such as final_modulus in the result for logs, but do not
    expose them as dominant reward dimensions.  This score rewards validity,
    local preservation, real incremental compression, and independent filters;
    it penalizes redundant clauses, known-pair rejection, too many filters, and
    overly large combined moduli on bounded 0..1-ish scales.
    """
    if valid <= 0.0 or not local_report.get("local_valid", False):
        return 0.0

    filter_count = max(1, num_filters)
    independent_ratio = report["independent"] / filter_count
    redundant_ratio = report["redundant"] / filter_count
    pair_ratio = min(1.0, pair_penalty / 200)
    filter_penalty = max(0.0, (num_filters - 3) / MAX_FILTERS)
    modulus_ratio = min(1.0, math.log1p(report["final_modulus"]) / math.log1p(MAX_COMBINED_MODULUS))

    combined = (
        0.55 * report["incremental_compression"]
        + 0.25 * independent_ratio
        - 0.30 * redundant_ratio
        - 0.20 * pair_ratio
        - 0.08 * filter_penalty
        - 0.07 * modulus_ratio
    )
    return max(0.0, min(1.0, combined))


def evaluate(program_path: str) -> dict:
    module = load_program(program_path)
    filters = module.proposed_filters()
    if not isinstance(filters, list):
        return {"score": 0.0, "valid": 0.0, "compression": 0.0}

    normalized, valid = normalize_filters(filters)
    local_report = combined_local_validity_report(normalized)
    if not local_report["local_valid"]:
        valid = 0.0
    report = independence_report(normalized)
    if report["invalid_lcm"]:
        valid = 0.0

    # Preserve known pair phenomena: do not reward filters that only encode
    # "no consecutive powerful numbers" by accident.
    pair_penalty = 0
    pairs = known_pair_starts()
    for x in pairs[:200]:
        if any(x % modulus not in allowed for modulus, allowed in normalized):
            pair_penalty += 1

    combined_score = compute_combined_score(
        valid=valid,
        local_report=local_report,
        report=report,
        pair_penalty=pair_penalty,
        num_filters=len(normalized),
    )
    return {
        "score": combined_score,
        "combined_score": combined_score,
        "valid": valid,
        "compression": report["compression"],
        "incremental_compression": report["incremental_compression"],
        "redundant_filters": report["redundant"],
        "independent_filters": report["independent"],
        "strict_shrink_steps": report["steps"],
        "local_validity": local_report,
        "final_modulus": report["final_modulus"],
        "final_candidates": report["final_candidates"],
        "pair_penalty": pair_penalty,
        "num_filters": len(normalized),
    }


if __name__ == "__main__":
    import sys

    print(evaluate(sys.argv[1]))
