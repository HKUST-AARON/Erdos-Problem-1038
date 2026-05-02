#!/usr/bin/env python3
"""Reproducible high-precision verifier for the finite one-variable log certificates.

This is a deterministic, standard-library-only check. It is not a formal proof
assistant; it uses Decimal arithmetic with high precision and conservative
endpoint-based lower bounds for each positive log term on a checked point or
closed bracket.
"""

from __future__ import annotations

from dataclasses import dataclass
from decimal import Decimal, localcontext
from fractions import Fraction
from typing import Literal, Sequence


PRECISION = 100


class VerificationError(ValueError):
    """Raised when a certificate check is invalid or fails safely."""


def q(num: int, den: int = 1) -> Fraction:
    return Fraction(num, den)


def dec_from_fraction(value: Fraction) -> Decimal:
    return Decimal(value.numerator) / Decimal(value.denominator)


def fmt_decimal(value: Decimal, places: int = 18) -> str:
    return f"{value:.{places}f}"


TargetKind = Literal["exact_sqrt2_minus_1", "exact_rational_point", "rational_bracket"]


@dataclass(frozen=True)
class LogTerm:
    coeff: Fraction
    shift: Fraction


@dataclass(frozen=True)
class CheckTarget:
    kind: TargetKind
    point: Fraction | None = None
    bracket: tuple[Fraction, Fraction] | None = None


@dataclass(frozen=True)
class Check:
    label: str
    target: CheckTarget
    threshold: Fraction


def exact_sqrt2_minus_1() -> CheckTarget:
    return CheckTarget(kind="exact_sqrt2_minus_1")


def exact_rational_point(point: Fraction) -> CheckTarget:
    return CheckTarget(kind="exact_rational_point", point=point)


def rational_bracket(left: Fraction, right: Fraction) -> CheckTarget:
    return CheckTarget(kind="rational_bracket", bracket=(left, right))


def _assert_shift_not_in_closed_interval(
    left: Decimal,
    right: Decimal,
    shift: Decimal,
    context: str,
) -> None:
    if left > right:
        raise VerificationError(f"{context}: invalid interval [{left}, {right}]")
    if left <= shift <= right:
        raise VerificationError(
            f"{context}: interval [{fmt_decimal(left, 18)}, {fmt_decimal(right, 18)}] "
            f"touches or crosses pole at shift {fmt_decimal(shift, 18)}"
        )


def conservative_term_lower_bound(
    y_left: Decimal,
    y_right: Decimal,
    term: LogTerm,
    context: str,
) -> tuple[Decimal, str]:
    """Lower bound coeff * log(1 / |y - shift|) on [y_left, y_right].

    The logarithmic term is monotone in the distance to the shift. On a closed
    interval that avoids the shift, the minimum occurs at the endpoint farthest
    from the shift.
    """

    shift = dec_from_fraction(term.shift)
    coeff = dec_from_fraction(term.coeff)
    _assert_shift_not_in_closed_interval(y_left, y_right, shift, context)

    dist_left = abs(y_left - shift)
    dist_right = abs(y_right - shift)
    if dist_left >= dist_right:
        chosen_y = y_left
        chosen_dist = dist_left
        chosen_side = "left"
    else:
        chosen_y = y_right
        chosen_dist = dist_right
        chosen_side = "right"

    lower = coeff * (-chosen_dist.ln())
    witness = f"{chosen_side}@{fmt_decimal(chosen_y, 12)}"
    return lower, witness


def conservative_point_lower_bound(
    y: Decimal,
    terms: Sequence[LogTerm],
    context: str,
) -> tuple[Decimal, list[str]]:
    total = Decimal(0)
    witnesses: list[str] = []
    for term in terms:
        shift = dec_from_fraction(term.shift)
        coeff = dec_from_fraction(term.coeff)
        if y == shift:
            raise VerificationError(
                f"{context}: point {fmt_decimal(y, 18)} coincides with pole at shift {fmt_decimal(shift, 18)}"
            )
        dist = abs(y - shift)
        total += coeff * (-dist.ln())
        witnesses.append(f"exact@{fmt_decimal(y, 12)}")
    return total, witnesses


def evaluate_check(
    check: Check,
    terms: Sequence[LogTerm],
    sqrt2_minus_1: Decimal,
) -> tuple[Decimal, bool, list[str], Decimal]:
    target = check.target
    context = check.label

    if target.kind == "exact_sqrt2_minus_1":
        lower, witnesses = conservative_point_lower_bound(sqrt2_minus_1, terms, context)
    elif target.kind == "exact_rational_point":
        if target.point is None:
            raise VerificationError(f"{context}: exact rational point target missing point value")
        lower, witnesses = conservative_point_lower_bound(dec_from_fraction(target.point), terms, context)
    elif target.kind == "rational_bracket":
        if target.bracket is None:
            raise VerificationError(f"{context}: rational bracket target missing bracket endpoints")
        left = dec_from_fraction(target.bracket[0])
        right = dec_from_fraction(target.bracket[1])
        witnesses = []
        lower = Decimal(0)
        for term in terms:
            piece, witness = conservative_term_lower_bound(left, right, term, context)
            lower += piece
            witnesses.append(witness)
    else:
        raise VerificationError(f"{context}: unknown check target kind {target.kind!r}")

    threshold = dec_from_fraction(check.threshold)
    return lower, lower > threshold, witnesses, threshold


def print_table(title: str, checks: Sequence[Check], terms: Sequence[LogTerm], sqrt2_minus_1: Decimal) -> bool:
    if title:
        print(title)
    print(f"{'check':34} {'lower bound':>24} {'threshold':>24} {'result':>8}")
    print("-" * 96)
    all_ok = True
    for check in checks:
        lower, ok, witnesses, threshold = evaluate_check(check, terms, sqrt2_minus_1)
        all_ok &= ok
        threshold_str = f"{check.threshold} ({fmt_decimal(threshold, 18)})"
        print(
            f"{check.label:34} {fmt_decimal(lower, 18):>24} {threshold_str:>24} "
            f"{'PASS' if ok else 'FAIL':>8}"
        )
        print(f"{'':34} witnesses: {', '.join(witnesses)}")
    print()
    return all_ok


def main() -> int:
    try:
        with localcontext() as ctx:
            ctx.prec = PRECISION
            sqrt2_minus_1 = Decimal(2).sqrt() - Decimal(1)

            fixed_terms = [
                LogTerm(q(1), q(0)),
                LogTerm(q(127383, 100000), q(17877, 10000)),
                LogTerm(q(34979, 100000), q(136718, 50000)),
            ]
            fixed_checks = [
                Check("V(sqrt2-1)", exact_sqrt2_minus_1(), q(1827, 10000)),
                Check(
                    "V(r1 bracket)",
                    rational_bracket(q(72710566, 100000000), q(72710567, 100000000)),
                    q(223, 10000000),
                ),
                Check(
                    "V(r2 bracket)",
                    rational_bracket(q(256242916, 100000000), q(256242917, 100000000)),
                    q(103, 2500000),
                ),
                Check("V(1+M)", exact_rational_point(q(27877, 10000)), q(26, 625000)),
            ]

            fixed_178772_terms = [
                LogTerm(q(1), q(0)),
                LogTerm(q(127437, 100000), q(44693, 25000)),
                LogTerm(q(87431, 250000), q(546881, 200000)),
            ]
            fixed_178772_checks = [
                Check("V(sqrt2-1)", exact_sqrt2_minus_1(), q(1825, 10000)),
                Check(
                    "V(r1 bracket)",
                    rational_bracket(q(72696113, 100000000), q(72696114, 100000000)),
                    q(4, 1000000),
                ),
                Check(
                    "V(r2 bracket)",
                    rational_bracket(q(256254651, 100000000), q(256254652, 100000000)),
                    q(4, 1000000),
                ),
                Check("V(1+M)", exact_rational_point(q(69693, 25000)), q(4, 1000000)),
            ]
            fixed_178771_terms = [
                LogTerm(q(1), q(0)),
                LogTerm(q(637013, 500000), q(178771, 100000)),
                LogTerm(q(349761, 1000000), q(273438, 100000)),
            ]
            fixed_178771_checks = [
                Check("V(sqrt2-1)", exact_sqrt2_minus_1(), q(1826, 10000)),
                Check(
                    "V(r1 bracket)",
                    rational_bracket(q(72705510, 100000000), q(72705511, 100000000)),
                    q(15, 1000000),
                ),
                Check(
                    "V(r2 bracket)",
                    rational_bracket(q(256247733, 100000000), q(256247734, 100000000)),
                    q(15, 1000000),
                ),
                Check("V(1+M)", exact_rational_point(q(278771, 100000)), q(18, 1000000)),
            ]

            block_terms = [
                LogTerm(q(1), q(0)),
                LogTerm(q(2457, 2000), q(18003, 10000)),
                LogTerm(q(767, 5000), q(26628, 10000)),
                LogTerm(q(1749, 10000), q(557, 200)),
            ]
            block_checks = [
                Check("V(7/10)", exact_rational_point(q(7, 10)), q(7, 1000)),
                Check(
                    "V(r1 bracket)",
                    rational_bracket(q(74916852, 100000000), q(74916853, 100000000)),
                    q(9, 2500),
                ),
                Check(
                    "V(r2 bracket)",
                    rational_bracket(q(254570327, 100000000), q(254570328, 100000000)),
                    q(7, 1250),
                ),
                Check(
                    "V(r3 bracket)",
                    rational_bracket(q(273794401, 100000000), q(273794402, 100000000)),
                    q(7, 2000),
                ),
                Check("V(14/5)", exact_rational_point(q(14, 5)), q(99, 10000)),
            ]

            stronger_1803_terms = [
                LogTerm(q(1), q(0)),
                LogTerm(q(6107, 5000), q(180321, 100000)),
                LogTerm(q(15563, 100000), q(266713, 100000)),
                LogTerm(q(4293, 25000), q(278795, 100000)),
            ]
            stronger_1803_checks = [
                Check("V(7/10)", exact_rational_point(q(7, 10)), q(49, 10000)),
                Check(
                    "V(r1 bracket)",
                    rational_bracket(q(75277143, 100000000), q(75277144, 100000000)),
                    q(4, 5000),
                ),
                Check(
                    "V(r2 bracket)",
                    rational_bracket(q(254863247, 100000000), q(254863248, 100000000)),
                    q(39, 50000),
                ),
                Check(
                    "V(r3 bracket)",
                    rational_bracket(q(274206592, 100000000), q(274206593, 100000000)),
                    q(39, 50000),
                ),
                Check("V(2803/1000)", exact_rational_point(q(2803, 1000)), q(4, 5000)),
            ]
            stronger_18035_terms = [
                LogTerm(q(1), q(0)),
                LogTerm(q(1214075, 1000000), q(18037, 10000)),
                LogTerm(q(78647, 500000), q(1333789, 500000)),
                LogTerm(q(85271, 500000), q(1394283, 500000)),
            ]
            stronger_18035_checks = [
                Check("V(7/10)", exact_rational_point(q(7, 10)), q(48, 10000)),
                Check(
                    "V(r1 bracket)",
                    rational_bracket(q(75523882, 100000000), q(75523883, 100000000)),
                    q(25, 100000),
                ),
                Check(
                    "V(r2 bracket)",
                    rational_bracket(q(254795697, 100000000), q(254795698, 100000000)),
                    q(26, 100000),
                ),
                Check(
                    "V(r3 bracket)",
                    rational_bracket(q(274299881, 100000000), q(274299882, 100000000)),
                    q(25, 100000),
                ),
                Check("V(5607/2000)", exact_rational_point(q(5607, 2000)), q(25, 100000)),
            ]
            stronger_1804_terms = [
                LogTerm(q(1), q(0)),
                LogTerm(q(1180333, 1000000), q(9021, 5000)),
                LogTerm(q(3543, 125000), q(2571118, 1000000)),
                LogTerm(q(117723, 1000000), q(2684011, 1000000)),
                LogTerm(q(179033, 1000000), q(2788213, 1000000)),
            ]
            stronger_1804_checks = [
                Check("V(7/10)", exact_rational_point(q(7, 10)), q(47, 5000)),
                Check(
                    "V(r1 bracket)",
                    rational_bracket(q(76702920, 100000000), q(76702921, 100000000)),
                    q(7, 2500),
                ),
                Check(
                    "V(r2 bracket)",
                    rational_bracket(q(252493236, 100000000), q(252493237, 100000000)),
                    q(7, 2500),
                ),
                Check(
                    "V(r3 bracket)",
                    rational_bracket(q(260961793, 100000000), q(260961794, 100000000)),
                    q(7, 2500),
                ),
                Check(
                    "V(r4 bracket)",
                    rational_bracket(q(274154611, 100000000), q(274154612, 100000000)),
                    q(7, 2500),
                ),
                Check("V(701/250)", exact_rational_point(q(701, 250)), q(7, 2500)),
            ]
            stronger_1805_terms = [
                LogTerm(q(1), q(0)),
                LogTerm(q(117735, 100000), q(9026, 5000)),
                LogTerm(q(13473, 500000), q(257054, 100000)),
                LogTerm(q(23869, 200000), q(134199, 50000)),
                LogTerm(q(89427, 500000), q(278919, 100000)),
            ]
            stronger_1805_checks = [
                Check("V(7/10)", exact_rational_point(q(7, 10)), q(84, 10000)),
                Check(
                    "V(r1 bracket)",
                    rational_bracket(q(76842878, 100000000), q(76842879, 100000000)),
                    q(16, 10000),
                ),
                Check(
                    "V(r2 bracket)",
                    rational_bracket(q(252553845, 100000000), q(252553846, 100000000)),
                    q(16, 10000),
                ),
                Check(
                    "V(r3 bracket)",
                    rational_bracket(q(260824271, 100000000), q(260824272, 100000000)),
                    q(16, 10000),
                ),
                Check(
                    "V(r4 bracket)",
                    rational_bracket(q(274238380, 100000000), q(274238381, 100000000)),
                    q(159, 100000),
                ),
                Check("V(561/200)", exact_rational_point(q(561, 200)), q(16, 10000)),
            ]
            stronger_1806_terms = [
                LogTerm(q(1), q(0)),
                LogTerm(q(29348, 25000), q(9031, 5000)),
                LogTerm(q(2657, 100000), q(25707, 10000)),
                LogTerm(q(5887, 50000), q(2683635, 1000000)),
                LogTerm(q(180873, 1000000), q(2789842, 1000000)),
            ]
            stronger_1806_checks = [
                Check("V(7/10)", exact_rational_point(q(7, 10)), q(75, 10000)),
                Check(
                    "V(r1 bracket)",
                    rational_bracket(q(76998681, 100000000), q(76998682, 100000000)),
                    q(41, 100000),
                ),
                Check(
                    "V(r2 bracket)",
                    rational_bracket(q(252599663, 100000000), q(252599664, 100000000)),
                    q(41, 100000),
                ),
                Check(
                    "V(r3 bracket)",
                    rational_bracket(q(260818086, 100000000), q(260818087, 100000000)),
                    q(41, 100000),
                ),
                Check(
                    "V(r4 bracket)",
                    rational_bracket(q(274209420, 100000000), q(274209421, 100000000)),
                    q(41, 100000),
                ),
                Check("V(1403/500)", exact_rational_point(q(1403, 500)), q(42, 100000)),
            ]
            stronger_18063_terms = [
                LogTerm(q(1), q(0)),
                LogTerm(q(1174168821, 1000000000), q(180650001, 100000000)),
                LogTerm(q(25921118, 1000000000), q(257053197, 100000000)),
                LogTerm(q(118647936, 1000000000), q(268367709, 100000000)),
                LogTerm(q(180553554, 1000000000), q(279017717, 100000000)),
            ]
            stronger_18063_checks = [
                Check("V(7/10)", exact_rational_point(q(7, 10)), q(72, 10000)),
                Check(
                    "V(r1 bracket)",
                    rational_bracket(q(77003805, 100000000), q(77003806, 100000000)),
                    q(59, 1000000),
                ),
                Check(
                    "V(r2 bracket)",
                    rational_bracket(q(252642600, 100000000), q(252642601, 100000000)),
                    q(58, 1000000),
                ),
                Check(
                    "V(r3 bracket)",
                    rational_bracket(q(260759965, 100000000), q(260759966, 100000000)),
                    q(58, 1000000),
                ),
                Check(
                    "V(r4 bracket)",
                    rational_bracket(q(274249871, 100000000), q(274249872, 100000000)),
                    q(57, 1000000),
                ),
                Check("V(28063/10000)", exact_rational_point(q(28063, 10000)), q(59, 1000000)),
            ]

            print("High-precision conservative verifier (Decimal precision = 100)")
            print("All log terms are lower-bounded by the farther endpoint of each closed bracket, after explicit pole checks.")
            print()

            ok = True

            print("A. Fixed three-atom forum candidate M=1.7877")
            ok &= print_table("", fixed_checks, fixed_terms, sqrt2_minus_1)

            print("B. Forum-stable pushed three-atom candidate M=1.78771")
            ok &= print_table("", fixed_178771_checks, fixed_178771_terms, sqrt2_minus_1)

            print("C. Thin experimental three-atom candidate M=1.78772")
            ok &= print_table("", fixed_178772_checks, fixed_178772_terms, sqrt2_minus_1)

            print("D. High-margin four-atom block in section 11.2")
            ok &= print_table("", block_checks, block_terms, sqrt2_minus_1)

            print("E. Stronger four-atom block for M=1.803")
            ok &= print_table("", stronger_1803_checks, stronger_1803_terms, sqrt2_minus_1)

            print("F. Stronger four-atom block for M=1.8035")
            ok &= print_table("", stronger_18035_checks, stronger_18035_terms, sqrt2_minus_1)

            stronger_18036_terms = [
                LogTerm(q(1), q(0)),
                LogTerm(q(121285, 100000), q(9019, 5000)),
                LogTerm(q(158249, 1000000), q(2667994, 1000000)),
                LogTerm(q(169671, 1000000), q(2788781, 1000000)),
            ]
            stronger_18036_checks = [
                Check("V(7/10)", exact_rational_point(q(7, 10)), q(47, 10000)),
                Check(
                    "V(r1 bracket)",
                    rational_bracket(q(75565871, 100000000), q(75565872, 100000000)),
                    q(14, 100000),
                ),
                Check(
                    "V(r2 bracket)",
                    rational_bracket(q(254792151, 100000000), q(254792152, 100000000)),
                    q(14, 100000),
                ),
                Check(
                    "V(r3 bracket)",
                    rational_bracket(q(274353528, 100000000), q(274353529, 100000000)),
                    q(15, 100000),
                ),
                Check("V(7009/2500)", exact_rational_point(q(7009, 2500)), q(14, 100000)),
            ]

            print("G. Stronger four-atom block for M=1.8036")
            ok &= print_table("", stronger_18036_checks, stronger_18036_terms, sqrt2_minus_1)

            print("H. Stronger five-atom block for M=1.804")
            ok &= print_table("", stronger_1804_checks, stronger_1804_terms, sqrt2_minus_1)

            print("I. Stronger five-atom block for M=1.805")
            ok &= print_table("", stronger_1805_checks, stronger_1805_terms, sqrt2_minus_1)

            print("J. Stronger five-atom block for M=1.806")
            ok &= print_table("", stronger_1806_checks, stronger_1806_terms, sqrt2_minus_1)

            print("K. Strongest five-atom block for M=1.8063")
            ok &= print_table("", stronger_18063_checks, stronger_18063_terms, sqrt2_minus_1)

            if ok:
                print("OVERALL RESULT: PASS")
                return 0
            print("OVERALL RESULT: FAIL")
            return 1
    except VerificationError as exc:
        print(f"ERROR: {exc}")
        print("OVERALL RESULT: FAIL")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
