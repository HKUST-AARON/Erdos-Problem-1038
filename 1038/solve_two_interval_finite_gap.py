#!/usr/bin/env python3
"""Numerical solver for the corrected two-interval finite-gap dual ansatz.

This script is intentionally diagnostic, not a proof certificate.  It checks
the corrected Cauchy-transform ansatz

    F(z) = (z + A) sqrt((z - alpha)(z - beta))
           / ((z - ell)(z - r)(z - 1)),

with beta = 1 - epsilon and ell = x_L + epsilon.  The branch is normalized by
R(z) ~ z at infinity.  The associated measure has atoms at ell, r, and 1, plus
an absolutely continuous density on [alpha, beta].

For each epsilon, it solves the two scalar equations

    U_lambda(alpha) = 0,
    U_lambda(-1) = 0,

and reports whether the sign-chart assumptions for the analytic positivity
argument hold.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from typing import Iterable

import numpy as np
from scipy.integrate import quad
from scipy.optimize import root


X_LEFT = -1.8081073680988165
X_RIGHT = 0.02632310766384517
RESIDUAL_TOLERANCE = 1.0e-8
TOTAL_MASS_TOLERANCE = 1.0e-8
BRANCH_BOX_A_RADIUS = 6.0
BRANCH_BOX_ALPHA_RADIUS = 4.0
KRAWCZYK_RADIUS_B = 1.0e-2
KRAWCZYK_RADIUS_TAU = 1.0e-2


@dataclass(frozen=True)
class AnsatzSolution:
    epsilon: float
    A: float
    alpha: float
    ell: float
    r: float
    beta: float
    mass_ell: float
    mass_r: float
    mass_1: float
    density_mass: float
    residual_alpha: float
    residual_minus_one: float
    valid_sign_chart: bool
    sample_min: float

    @property
    def total_mass(self) -> float:
        return self.mass_ell + self.mass_r + self.mass_1 + self.density_mass


@dataclass(frozen=True)
class LimitSolution:
    A: float
    alpha: float
    mass_ell: float
    mass_r: float
    density_mass: float
    residual_alpha: float
    residual_minus_one: float

    @property
    def total_mass(self) -> float:
        return self.mass_ell + self.mass_r + self.density_mass


def branch_R_real(t: float, alpha: float, beta: float) -> float:
    if t < alpha:
        return -math.sqrt((alpha - t) * (beta - t))
    if t > beta:
        return math.sqrt((t - alpha) * (t - beta))
    raise ValueError("branch_R_real called on the cut")


def branch_R_limit_left(t: float, alpha: float) -> float:
    if t < alpha:
        return -math.sqrt((alpha - t) * (1.0 - t))
    raise ValueError("branch_R_limit_left called on the limiting cut")


def atoms(A: float, alpha: float, epsilon: float) -> tuple[float, float, float, float, float, float]:
    ell = X_LEFT + epsilon
    r = X_RIGHT
    beta = 1.0 - epsilon
    R_ell = branch_R_real(ell, alpha, beta)
    R_r = branch_R_real(r, alpha, beta)
    R_1 = branch_R_real(1.0, alpha, beta)
    mass_ell = (ell + A) * R_ell / ((ell - r) * (ell - 1.0))
    mass_r = (r + A) * R_r / ((r - ell) * (r - 1.0))
    mass_1 = (1.0 + A) * R_1 / ((1.0 - ell) * (1.0 - r))
    return ell, r, beta, mass_ell, mass_r, mass_1


def density(t: float, A: float, alpha: float, epsilon: float) -> float:
    ell = X_LEFT + epsilon
    r = X_RIGHT
    beta = 1.0 - epsilon
    radicand = max(0.0, (t - alpha) * (beta - t))
    return -(
        (t + A)
        * math.sqrt(radicand)
        / (math.pi * (t - ell) * (t - r) * (t - 1.0))
    )


def integrate_cut(func, alpha: float, beta: float) -> float:
    mid = (alpha + beta) / 2.0
    half = (beta - alpha) / 2.0

    def integrand(theta: float) -> float:
        t = mid + half * math.cos(theta)
        return func(t) * half * math.sin(theta)

    value, _ = quad(integrand, 0.0, math.pi, epsabs=1e-10, epsrel=1e-10, limit=200)
    return value


def continuous_potential(x: float, A: float, alpha: float, epsilon: float) -> float:
    beta = 1.0 - epsilon

    def integrand(t: float) -> float:
        return density(t, A, alpha, epsilon) * math.log(1.0 / abs(x - t))

    return integrate_cut(integrand, alpha, beta)


def continuous_mass(A: float, alpha: float, epsilon: float) -> float:
    beta = 1.0 - epsilon
    return integrate_cut(lambda t: density(t, A, alpha, epsilon), alpha, beta)


def limit_atoms(A: float, alpha: float) -> tuple[float, float]:
    ell = X_LEFT
    r = X_RIGHT
    R_ell = branch_R_limit_left(ell, alpha)
    R_r = branch_R_limit_left(r, alpha)
    mass_ell = (ell + A) * R_ell / ((ell - r) * (ell - 1.0))
    mass_r = (r + A) * R_r / ((r - ell) * (r - 1.0))
    return mass_ell, mass_r


def limit_density(t: float, A: float, alpha: float) -> float:
    ell = X_LEFT
    r = X_RIGHT
    return -(
        (t + A)
        * math.sqrt((t - alpha) * (1.0 - t))
        / (math.pi * (t - ell) * (t - r) * (t - 1.0))
    )


def limit_continuous_potential(x: float, A: float, alpha: float) -> float:
    def integrand(t: float) -> float:
        return limit_density(t, A, alpha) * math.log(1.0 / abs(x - t))

    return integrate_cut(integrand, alpha, 1.0)


def limit_continuous_mass(A: float, alpha: float) -> float:
    return integrate_cut(lambda t: limit_density(t, A, alpha), alpha, 1.0)


def limit_potential(x: float, A: float, alpha: float) -> float:
    mass_ell, mass_r = limit_atoms(A, alpha)
    return (
        mass_ell * math.log(1.0 / abs(x - X_LEFT))
        + mass_r * math.log(1.0 / abs(x - X_RIGHT))
        + limit_continuous_potential(x, A, alpha)
    )


def potential(x: float, A: float, alpha: float, epsilon: float) -> float:
    ell, r, _beta, mass_ell, mass_r, mass_1 = atoms(A, alpha, epsilon)
    return (
        mass_ell * math.log(1.0 / abs(x - ell))
        + mass_r * math.log(1.0 / abs(x - r))
        + mass_1 * math.log(1.0 / abs(x - 1.0))
        + continuous_potential(x, A, alpha, epsilon)
    )


def F_real(x: float, A: float, alpha: float, epsilon: float) -> float:
    ell = X_LEFT + epsilon
    r = X_RIGHT
    beta = 1.0 - epsilon
    R = branch_R_real(x, alpha, beta)
    return (x + A) * R / ((x - ell) * (x - r) * (x - 1.0))


def F_continuous_real(x: float, A: float, alpha: float, epsilon: float) -> float:
    ell, r, _beta, mass_ell, mass_r, mass_1 = atoms(A, alpha, epsilon)
    if abs(x - r) < 1.0e-7:
        beta = 1.0 - epsilon
        R = branch_R_real(r, alpha, beta)
        Rprime = R * (-0.5 * (1.0 / (alpha - r) + 1.0 / (beta - r)))
        N = (r + A) * R
        Nprime = R + (r + A) * Rprime
        B = (r - ell) * (r - 1.0)
        Bprime = (r - 1.0) + (r - ell)
        regular_part = (Nprime * B - N * Bprime) / (B * B)
        return regular_part - mass_ell / (r - ell) - mass_1 / (r - 1.0)
    return (
        F_real(x, A, alpha, epsilon)
        - mass_ell / (x - ell)
        - mass_r / (x - r)
        - mass_1 / (x - 1.0)
    )


def potential_difference_by_F(A: float, alpha: float, epsilon: float) -> float:
    ell, r, _beta, mass_ell, mass_r, mass_1 = atoms(A, alpha, epsilon)
    atom_difference = (
        mass_ell * (math.log(1.0 / abs(-1.0 - ell)) - math.log(1.0 / abs(alpha - ell)))
        + mass_r * (math.log(1.0 / abs(-1.0 - r)) - math.log(1.0 / abs(alpha - r)))
        + mass_1 * (math.log(1.0 / abs(-2.0)) - math.log(1.0 / abs(alpha - 1.0)))
    )
    continuous_difference = quad(
        lambda x: F_continuous_real(x, A, alpha, epsilon),
        -1.0,
        alpha,
        points=[r],
        epsabs=1e-10,
        epsrel=1e-10,
        limit=200,
    )[0]
    return atom_difference + continuous_difference


def continuous_difference_by_w_residues(A: float, alpha: float, epsilon: float) -> tuple[float, float]:
    import sympy as sp

    ell, r, beta, mass_ell, mass_r, mass_1 = atoms(A, alpha, epsilon)
    w = sp.symbols("w")
    sp_A = sp.Float(A, 80)
    sp_alpha = sp.Float(alpha, 80)
    sp_ell = sp.Float(ell, 80)
    sp_r = sp.Float(r, 80)
    sp_beta = sp.Float(beta, 80)
    sp_mass_ell = sp.Float(mass_ell, 80)
    sp_mass_r = sp.Float(mass_r, 80)
    sp_mass_1 = sp.Float(mass_1, 80)
    half_width = (sp_beta - sp_alpha) / 2
    center = (sp_alpha + sp_beta) / 2
    joukowski_scale = half_width / 2
    z = center + joukowski_scale * (w + 1 / w)
    R = joukowski_scale * (w - 1 / w)
    dz = sp.diff(z, w)
    F = (z + sp_A) * R / ((z - sp_ell) * (z - sp_r) * (z - 1))
    F_cont = F - sp_mass_ell / (z - sp_ell) - sp_mass_r / (z - sp_r) - sp_mass_1 / (z - 1)
    expression = sp.cancel(F_cont * dz)
    numerator, denominator = sp.fraction(expression)
    numerator_poly = sp.Poly(numerator, w)
    denominator_poly = sp.Poly(denominator, w)
    denominator_derivative = sp.Poly(sp.diff(denominator, w), w)
    roots = denominator_poly.nroots(n=60, maxsteps=200)
    y = 2 * (sp.Float(-1, 80) - center) / half_width
    w_left = (y - sp.sqrt(y * y - 4)) / 2
    w_right = sp.Float(-1, 80)
    value = 0
    for pole in roots:
        residue = numerator_poly.eval(pole) / denominator_derivative.eval(pole)
        value += residue * (sp.log(w_right - pole) - sp.log(w_left - pole))
    return float(sp.re(value)), float(sp.im(value))


def continuous_difference_by_w_residues_acb(
    A: float, alpha: float, epsilon: float, precision: int = 320
) -> tuple[str, str, str, bool, float, int]:
    import sympy as sp
    from flint import acb, acb_poly, arb, ctx

    ctx.prec = precision
    ell, r, beta, mass_ell, mass_r, mass_1 = atoms(A, alpha, epsilon)
    w = sp.symbols("w")
    sp_A = sp.Float(A, 100)
    sp_alpha = sp.Float(alpha, 100)
    sp_ell = sp.Float(ell, 100)
    sp_r = sp.Float(r, 100)
    sp_beta = sp.Float(beta, 100)
    half_width = (sp_beta - sp_alpha) / 2
    center = (sp_alpha + sp_beta) / 2
    joukowski_scale = half_width / 2
    z = center + joukowski_scale * (w + 1 / w)
    R = joukowski_scale * (w - 1 / w)
    dz = sp.diff(z, w)

    def physical_preimage(q: sp.Float) -> sp.Expr:
        y = (q - center) / joukowski_scale
        if q < sp_alpha:
            return (y - sp.sqrt(y * y - 4)) / 2
        return (y + sp.sqrt(y * y - 4)) / 2

    def branch_value(q: sp.Float) -> sp.Expr:
        preimage = physical_preimage(q)
        return joukowski_scale * (preimage - 1 / preimage)

    sp_mass_ell = (sp_ell + sp_A) * branch_value(sp_ell) / ((sp_ell - sp_r) * (sp_ell - 1))
    sp_mass_r = (sp_r + sp_A) * branch_value(sp_r) / ((sp_r - sp_ell) * (sp_r - 1))
    sp_mass_1 = (1 + sp_A) * branch_value(sp.Float(1, 100)) / ((1 - sp_ell) * (1 - sp_r))
    F = (z + sp_A) * R / ((z - sp_ell) * (z - sp_r) * (z - 1))
    F_cont = F - sp_mass_ell / (z - sp_ell) - sp_mass_r / (z - sp_r) - sp_mass_1 / (z - 1)
    expression = sp.together(F_cont * dz)
    numerator, denominator = sp.fraction(expression)
    numerator_poly = sp.Poly(numerator, w)
    denominator_poly = sp.Poly(denominator, w)
    r_preimage = physical_preimage(sp_r)
    numerator_poly = sp.div(numerator_poly, sp.Poly(w - r_preimage, w))[0]
    denominator_poly = sp.div(denominator_poly, sp.Poly(w - r_preimage, w))[0]
    denominator_derivative = sp.Poly(sp.diff(denominator, w), w)
    denominator_derivative = sp.Poly(sp.diff(denominator_poly.as_expr(), w), w)

    def poly_to_acb(poly: sp.Poly) -> acb_poly:
        return acb_poly([acb(str(sp.N(coefficient, 80))) for coefficient in reversed(poly.all_coeffs())])

    numerator_acb = poly_to_acb(numerator_poly)
    denominator_acb = poly_to_acb(denominator_poly)
    derivative_acb = poly_to_acb(denominator_derivative)
    roots = denominator_acb.roots(tol=2.0 ** -120, maxprec=max(precision, 512))
    y = 2 * (sp.Float(-1, 100) - center) / half_width
    w_left = (y - sp.sqrt(y * y - 4)) / 2
    w_left_acb = acb(str(sp.N(w_left, 80)))
    w_right_acb = acb(-1)
    value = acb(0)
    for pole in roots:
        residue = numerator_acb(pole) / derivative_acb(pole)
        value += residue * ((w_right_acb - pole).log() - (w_left_acb - pole).log())

    def arb_from_sp(value: sp.Expr) -> arb:
        return arb(str(sp.N(value, 80)))

    def log_inverse_abs(value: sp.Expr) -> arb:
        return -arb_from_sp(abs(value)).log()

    atom_difference = (
        arb_from_sp(sp_mass_ell)
        * (log_inverse_abs(-1 - sp_ell) - log_inverse_abs(sp_alpha - sp_ell))
        + arb_from_sp(sp_mass_r)
        * (log_inverse_abs(-1 - sp_r) - log_inverse_abs(sp_alpha - sp_r))
        + arb_from_sp(sp_mass_1)
        * (log_inverse_abs(-2) - log_inverse_abs(sp_alpha - 1))
    )
    full_difference = value.real + atom_difference
    w_left_float = float(w_left)
    w_right_float = -1.0

    def distance_to_path(point: complex) -> float:
        real_part = point.real
        imag_part = point.imag
        if w_left_float <= real_part <= w_right_float:
            return abs(imag_part)
        return min(abs(point - w_left_float), abs(point - w_right_float))

    sympy_roots = [complex(root) for root in denominator_poly.nroots(n=50, maxsteps=200)]
    path_separation = min(distance_to_path(root) for root in sympy_roots)
    return str(value.real), str(value.imag), str(full_difference), full_difference.contains(0), path_separation, len(sympy_roots)


def _arb_interval_from_bounds(low: float, high: float):
    from flint import arb

    if not math.isfinite(low) or not math.isfinite(high) or low > high:
        raise ValueError(f"invalid interval bounds [{low!r}, {high!r}]")
    center = (low + high) / 2.0
    radius = (high - low) / 2.0
    return arb(repr(center)) + arb(f"[+/- {radius!r}]")


def _potential_minus_one_acb_from_arb(A, alpha, epsilon, precision: int) -> str:
    from flint import acb, arb, ctx

    ctx.prec = precision
    arb_A = A
    arb_alpha = alpha
    arb_epsilon = epsilon
    arb_ell = arb(repr(X_LEFT)) + arb_epsilon
    arb_r = arb(repr(X_RIGHT))
    arb_beta = arb(1) - arb_epsilon
    pi = arb.pi()

    def branch_left(q: arb) -> arb:
        return -((arb_alpha - q) * (arb_beta - q)).sqrt()

    def branch_right(q: arb) -> arb:
        return ((q - arb_alpha) * (q - arb_beta)).sqrt()

    def log_inverse_positive(value: arb) -> arb:
        return -value.log()

    mass_ell = (arb_ell + arb_A) * branch_left(arb_ell) / ((arb_ell - arb_r) * (arb_ell - arb(1)))
    mass_r = (arb_r + arb_A) * branch_left(arb_r) / ((arb_r - arb_ell) * (arb_r - arb(1)))
    mass_1 = (arb(1) + arb_A) * branch_right(arb(1)) / ((arb(1) - arb_ell) * (arb(1) - arb_r))

    atom_part = (
        mass_ell * log_inverse_positive(-arb(1) - arb_ell)
        + mass_r * log_inverse_positive(arb(1) + arb_r)
        + mass_1 * log_inverse_positive(arb(2))
    )

    # Use u = sin(theta/2), so t = beta - 2 h u^2 and the boundary layer near
    # beta = 1 - epsilon has denominator t - 1 = -epsilon - 2 h u^2.  This
    # avoids complex-neighbourhood balls crossing the pole at 1 in the original
    # theta parametrization when epsilon is small.
    half = (arb_beta - arb_alpha) / 2
    acb_half = acb(half)
    acb_beta = acb(arb_beta)
    acb_A = acb(arb_A)
    acb_ell = acb(arb_ell)
    acb_r = acb(arb_r)
    acb_pi = acb(pi)

    def integrand(u: acb, analytic: bool) -> acb:
        u2 = u * u
        endpoint_factor = (acb(1) - u2).sqrt(analytic=analytic)
        t = acb_beta - acb(2) * acb_half * u2
        denominator = (t - acb_ell) * (t - acb_r) * (t - acb(1))
        density_times_dt = -(
            acb(8) * acb_half * acb_half * u2 * endpoint_factor / acb_pi
        ) * (t + acb_A) / denominator
        return density_times_dt * (-(t + acb(1)).log(analytic=analytic))

    # The final endpoint u=1 is a harmless square-root endpoint.  Splitting
    # keeps Arb's automatic complex neighbourhoods small enough to avoid
    # spurious non-finite balls.
    breakpoints = [0.0, 0.05, 0.1, 0.2, 0.35, 0.5, 0.65, 0.8, 0.9, 0.97, 0.99, 0.997, 0.999, 1.0]
    continuous_part = acb(0)
    for left, right in zip(breakpoints, breakpoints[1:]):
        continuous_part += acb.integral(
            integrand,
            arb(repr(left)),
            arb(repr(right)),
            rel_tol=arb("1e-50"),
            abs_tol=arb("1e-50"),
            deg_limit=64,
            eval_limit=20000,
            depth_limit=100,
        )
    return str((acb(atom_part) + continuous_part).real)


def potential_minus_one_acb(A: float, alpha: float, epsilon: float, precision: int = 256) -> str:
    """Arb/Acb diagnostic enclosure for ``U(-1)`` at a fixed parameter point.

    The contact value ``U(alpha)`` has an endpoint logarithmic singularity in
    the theta variable.  The verifier therefore derives it from this direct
    ``U(-1)`` enclosure and the separate residue-log Arb ball for
    ``U(-1)-U(alpha)``.
    """

    from flint import arb

    return _potential_minus_one_acb_from_arb(
        arb(repr(float(A))),
        arb(repr(float(alpha))),
        arb(repr(float(epsilon))),
        precision,
    )


def potential_minus_one_box_acb(
    A_low: float,
    A_high: float,
    alpha_low: float,
    alpha_high: float,
    epsilon: float,
    precision: int = 192,
) -> str:
    """Arb/Acb diagnostic enclosure for ``U(-1)`` over an ``(A, alpha)`` box."""

    from flint import arb

    return _potential_minus_one_acb_from_arb(
        _arb_interval_from_bounds(A_low, A_high),
        _arb_interval_from_bounds(alpha_low, alpha_high),
        arb(repr(float(epsilon))),
        precision,
    )


def _contact_potential_acb_from_arb(A, alpha, epsilon, precision: int) -> str:
    from flint import acb, arb, ctx

    ctx.prec = precision
    arb_ell = arb(repr(X_LEFT)) + epsilon
    arb_r = arb(repr(X_RIGHT))
    arb_beta = arb(1) - epsilon
    pi = arb.pi()

    def branch_left(q: arb) -> arb:
        return -((alpha - q) * (arb_beta - q)).sqrt()

    def branch_right(q: arb) -> arb:
        return ((q - alpha) * (q - arb_beta)).sqrt()

    mass_ell = (arb_ell + A) * branch_left(arb_ell) / ((arb_ell - arb_r) * (arb_ell - arb(1)))
    mass_r = (arb_r + A) * branch_left(arb_r) / ((arb_r - arb_ell) * (arb_r - arb(1)))
    mass_1 = (arb(1) + A) * branch_right(arb(1)) / ((arb(1) - arb_ell) * (arb(1) - arb_r))
    atom_part = (
        mass_ell * (-(alpha - arb_ell).log())
        + mass_r * (-(alpha - arb_r).log())
        + mass_1 * (-(arb(1) - alpha).log())
    )

    # Use the same two endpoint charts as the contact derivative enclosure.
    # The v=0 endpoint has an integrable v^2 log(v^2) singularity; we bound a
    # short tail explicitly.
    half = (arb_beta - alpha) / 2
    acb_half = acb(half)
    acb_beta = acb(arb_beta)
    acb_A = acb(A)
    acb_ell = acb(arb_ell)
    acb_r = acb(arb_r)
    acb_pi = acb(pi)

    def density_times_dt(u2, endpoint_factor, t):
        denominator = (t - acb_ell) * (t - acb_r) * (t - acb(1))
        prefactor = -(acb(8) * u2 * endpoint_factor / acb_pi)
        return prefactor * acb_half * acb_half * (t + acb_A) / denominator

    def u_integrand(u: acb, analytic: bool) -> acb:
        u2 = u * u
        endpoint_factor = (acb(1) - u2).sqrt(analytic=analytic)
        t = acb_beta - acb(2) * acb_half * u2
        log_contact = -((acb(2) * acb_half) * (acb(1) - u2)).log(analytic=analytic)
        return density_times_dt(u2, endpoint_factor, t) * log_contact

    def v_integrand(v: acb, analytic: bool) -> acb:
        v2 = v * v
        endpoint_factor = (acb(1) - v2).sqrt(analytic=analytic)
        t = acb(2) * acb_half * v2 + acb_beta - acb(2) * acb_half
        log_contact = -((acb(2) * acb_half) * v2).log(analytic=analytic)
        return density_times_dt(v2, endpoint_factor, t) * log_contact

    continuous_part = acb(0)
    u_breakpoints = [0.0, 0.05, 0.1, 0.2, 0.35, 0.5, 0.65, 0.8]
    for left, right in zip(u_breakpoints, u_breakpoints[1:]):
        continuous_part += acb.integral(
            u_integrand,
            arb(repr(left)),
            arb(repr(right)),
            rel_tol=arb("1e-45"),
            abs_tol=arb("1e-45"),
            deg_limit=64,
            eval_limit=20000,
            depth_limit=100,
        )

    delta = 1.0e-4
    v_breakpoints = [delta, 0.001, 0.005, 0.02, 0.06, 0.12, 0.25, 0.4, 0.6]
    for left, right in zip(v_breakpoints, v_breakpoints[1:]):
        continuous_part += acb.integral(
            v_integrand,
            arb(repr(left)),
            arb(repr(right)),
            rel_tol=arb("1e-45"),
            abs_tol=arb("1e-45"),
            deg_limit=64,
            eval_limit=20000,
            depth_limit=100,
        )

    def tail_radius() -> arb:
        v = _arb_interval_from_bounds(0.0, delta)
        v2 = v * v
        endpoint_factor = (1 - v2).sqrt()
        t = alpha + 2 * half * v2
        density = density_times_dt(acb(v2), acb(endpoint_factor), acb(t)).real
        half_low = max(float(half.lower()), 1.0e-300)
        coef = float(abs(density).upper()) / (delta * delta)
        log_weight = -math.log(2.0 * half_low * delta * delta) + 2.0 / 3.0
        radius = coef * delta**3 * max(log_weight, 0.0) / 3.0
        return arb(f"[+/- {radius!r}]")

    return str(atom_part + continuous_part.real + tail_radius())


def contact_potential_acb(A: float, alpha: float, epsilon: float, precision: int = 256) -> str:
    """Arb/Acb diagnostic enclosure for ``U(alpha)`` at a fixed point."""

    from flint import arb

    return _contact_potential_acb_from_arb(
        arb(repr(float(A))),
        arb(repr(float(alpha))),
        arb(repr(float(epsilon))),
        precision,
    )


def _combined_contact_minus_one_potential_acb_from_arb(A, alpha, epsilon, left_weight, precision: int) -> str:
    """Arb/Acb box for ``left_weight*U(alpha) + U(-1)``.

    This keeps the contact and fixed-point potential values in one expression
    so that their leading cancellation is not lost before interval evaluation.
    """

    from flint import acb, arb, ctx

    ctx.prec = precision
    arb_ell = arb(repr(X_LEFT)) + epsilon
    arb_r = arb(repr(X_RIGHT))
    arb_beta = arb(1) - epsilon
    pi = arb.pi()

    def branch_left(q: arb) -> arb:
        return -((alpha - q) * (arb_beta - q)).sqrt()

    def branch_right(q: arb) -> arb:
        return ((q - alpha) * (q - arb_beta)).sqrt()

    mass_ell = (arb_ell + A) * branch_left(arb_ell) / ((arb_ell - arb_r) * (arb_ell - arb(1)))
    mass_r = (arb_r + A) * branch_left(arb_r) / ((arb_r - arb_ell) * (arb_r - arb(1)))
    mass_1 = (arb(1) + A) * branch_right(arb(1)) / ((arb(1) - arb_ell) * (arb(1) - arb_r))
    contact_atom = (
        mass_ell * (-(alpha - arb_ell).log())
        + mass_r * (-(alpha - arb_r).log())
        + mass_1 * (-(arb(1) - alpha).log())
    )
    minus_one_atom = (
        mass_ell * (-(-arb(1) - arb_ell).log())
        + mass_r * (-(arb(1) + arb_r).log())
        + mass_1 * (-arb(2).log())
    )
    atom_part = left_weight * contact_atom + minus_one_atom

    half = (arb_beta - alpha) / 2
    acb_half = acb(half)
    acb_beta = acb(arb_beta)
    acb_A = acb(A)
    acb_ell = acb(arb_ell)
    acb_r = acb(arb_r)
    acb_pi = acb(pi)
    acb_left_weight = acb(left_weight)

    def density_times_dt(u2, endpoint_factor, t):
        denominator = (t - acb_ell) * (t - acb_r) * (t - acb(1))
        prefactor = -(acb(8) * u2 * endpoint_factor / acb_pi)
        return prefactor * acb_half * acb_half * (t + acb_A) / denominator

    def combined_kernel(t, log_contact, analytic: bool):
        log_minus_one = -((t + acb(1)).log(analytic=analytic))
        return acb_left_weight * log_contact + log_minus_one

    def u_integrand(u: acb, analytic: bool) -> acb:
        u2 = u * u
        endpoint_factor = (acb(1) - u2).sqrt(analytic=analytic)
        t = acb_beta - acb(2) * acb_half * u2
        log_contact = -((acb(2) * acb_half) * (acb(1) - u2)).log(analytic=analytic)
        return density_times_dt(u2, endpoint_factor, t) * combined_kernel(t, log_contact, analytic)

    def v_integrand(v: acb, analytic: bool) -> acb:
        v2 = v * v
        endpoint_factor = (acb(1) - v2).sqrt(analytic=analytic)
        t = acb(2) * acb_half * v2 + acb_beta - acb(2) * acb_half
        log_contact = -((acb(2) * acb_half) * v2).log(analytic=analytic)
        return density_times_dt(v2, endpoint_factor, t) * combined_kernel(t, log_contact, analytic)

    continuous_part = acb(0)
    u_breakpoints = [0.0, 0.05, 0.1, 0.2, 0.35, 0.5, 0.65, 0.8]
    for left, right in zip(u_breakpoints, u_breakpoints[1:]):
        continuous_part += acb.integral(
            u_integrand,
            arb(repr(left)),
            arb(repr(right)),
            rel_tol=arb("1e-45"),
            abs_tol=arb("1e-45"),
            deg_limit=64,
            eval_limit=20000,
            depth_limit=100,
        )

    delta = 1.0e-4
    v_breakpoints = [delta, 0.001, 0.005, 0.02, 0.06, 0.12, 0.25, 0.4, 0.6]
    for left, right in zip(v_breakpoints, v_breakpoints[1:]):
        continuous_part += acb.integral(
            v_integrand,
            arb(repr(left)),
            arb(repr(right)),
            rel_tol=arb("1e-45"),
            abs_tol=arb("1e-45"),
            deg_limit=64,
            eval_limit=20000,
            depth_limit=100,
        )

    def tail_radius() -> arb:
        v = _arb_interval_from_bounds(0.0, delta)
        v2 = v * v
        endpoint_factor = (1 - v2).sqrt()
        t = alpha + 2 * half * v2
        log_contact = -((2 * half) * v2).log()
        log_minus_one = -(t + 1).log()
        density = density_times_dt(acb(v2), acb(endpoint_factor), acb(t)).real
        kernel = left_weight * log_contact + log_minus_one
        half_low = max(float(half.lower()), 1.0e-300)
        density_coef = float(abs(density).upper()) / (delta * delta)
        log_weight = max(abs(float(left_weight.upper())), abs(float(left_weight.lower()))) * (
            -math.log(2.0 * half_low * delta * delta) + 2.0 / 3.0
        )
        log_weight += float(abs(log_minus_one).upper())
        radius = density_coef * delta**3 * max(log_weight, 0.0) / 3.0
        radius = max(radius, float(abs(density * kernel).upper()) * delta)
        return arb(f"[+/- {radius!r}]")

    return str(atom_part + continuous_part.real + tail_radius())


def _potential_minus_one_directional_derivative_acb_from_arb(
    A,
    alpha,
    epsilon,
    direction_A,
    direction_alpha,
    precision: int,
) -> str:
    from flint import acb, arb, ctx

    ctx.prec = precision
    arb_ell = arb(repr(X_LEFT)) + epsilon
    arb_r = arb(repr(X_RIGHT))
    arb_beta = arb(1) - epsilon
    pi = arb.pi()

    def branch_left(q: arb) -> arb:
        return -((alpha - q) * (arb_beta - q)).sqrt()

    def branch_right(q: arb) -> arb:
        return ((q - alpha) * (q - arb_beta)).sqrt()

    mass_ell = (arb_ell + A) * branch_left(arb_ell) / ((arb_ell - arb_r) * (arb_ell - arb(1)))
    mass_r = (arb_r + A) * branch_left(arb_r) / ((arb_r - arb_ell) * (arb_r - arb(1)))
    mass_1 = (arb(1) + A) * branch_right(arb(1)) / ((arb(1) - arb_ell) * (arb(1) - arb_r))
    dmass_ell = direction_A * mass_ell / (arb_ell + A) + direction_alpha * mass_ell / (2 * (alpha - arb_ell))
    dmass_r = direction_A * mass_r / (arb_r + A) + direction_alpha * mass_r / (2 * (alpha - arb_r))
    dmass_1 = direction_A * mass_1 / (arb(1) + A) - direction_alpha * mass_1 / (2 * (arb(1) - alpha))

    atom_part = (
        dmass_ell * (-(-arb(1) - arb_ell).log())
        + dmass_r * (-(arb(1) + arb_r).log())
        + dmass_1 * (-arb(2).log())
    )

    half = (arb_beta - alpha) / 2
    acb_half = acb(half)
    acb_beta = acb(arb_beta)
    acb_A = acb(A)
    acb_ell = acb(arb_ell)
    acb_r = acb(arb_r)
    acb_pi = acb(pi)
    acb_direction_A = acb(direction_A)
    acb_direction_alpha = acb(direction_alpha)
    acb_half_s = -acb("0.5") * acb_direction_alpha

    def integrand(u: acb, analytic: bool) -> acb:
        u2 = u * u
        endpoint_factor = (acb(1) - u2).sqrt(analytic=analytic)
        t = acb_beta - acb(2) * acb_half * u2
        t_s = u2 * acb_direction_alpha
        denominator = (t - acb_ell) * (t - acb_r) * (t - acb(1))
        denominator_prime = (
            (t - acb_r) * (t - acb(1))
            + (t - acb_ell) * (t - acb(1))
            + (t - acb_ell) * (t - acb_r)
        )
        denominator_s = t_s * denominator_prime
        prefactor = -(acb(8) * u2 * endpoint_factor / acb_pi)
        density_times_dt = prefactor * acb_half * acb_half * (t + acb_A) / denominator
        density_times_dt_s = prefactor * (
            acb(2) * acb_half * acb_half_s * (t + acb_A) / denominator
            + acb_half
            * acb_half
            * ((t_s + acb_direction_A) * denominator - (t + acb_A) * denominator_s)
            / (denominator * denominator)
        )
        log_kernel = -(t + acb(1)).log(analytic=analytic)
        log_kernel_s = -t_s / (t + acb(1))
        return density_times_dt_s * log_kernel + density_times_dt * log_kernel_s

    breakpoints = [0.0, 0.05, 0.1, 0.2, 0.35, 0.5, 0.65, 0.8, 0.9, 0.97, 0.99, 0.997, 0.999, 1.0]
    continuous_part = acb(0)
    for left, right in zip(breakpoints, breakpoints[1:]):
        continuous_part += acb.integral(
            integrand,
            arb(repr(left)),
            arb(repr(right)),
            rel_tol=arb("1e-45"),
            abs_tol=arb("1e-45"),
            deg_limit=64,
            eval_limit=20000,
            depth_limit=100,
        )
    return str((acb(atom_part) + continuous_part).real)


def potential_minus_one_derivative_box_acb(
    A_low: float,
    A_high: float,
    alpha_low: float,
    alpha_high: float,
    epsilon: float,
    direction_A: float,
    direction_alpha: float,
    precision: int = 192,
) -> str:
    """Arb/Acb box enclosure for a directional derivative of ``U(-1)``."""

    from flint import arb

    return _potential_minus_one_directional_derivative_acb_from_arb(
        _arb_interval_from_bounds(A_low, A_high),
        _arb_interval_from_bounds(alpha_low, alpha_high),
        arb(repr(float(epsilon))),
        arb(repr(float(direction_A))),
        arb(repr(float(direction_alpha))),
        precision,
    )


def _contact_directional_derivative_acb_from_arb(
    A,
    alpha,
    epsilon,
    direction_A,
    direction_alpha,
    precision: int,
) -> str:
    from flint import acb, arb, ctx

    ctx.prec = precision
    arb_ell = arb(repr(X_LEFT)) + epsilon
    arb_r = arb(repr(X_RIGHT))
    arb_beta = arb(1) - epsilon
    pi = arb.pi()

    def branch_left(q: arb) -> arb:
        return -((alpha - q) * (arb_beta - q)).sqrt()

    def branch_right(q: arb) -> arb:
        return ((q - alpha) * (q - arb_beta)).sqrt()

    mass_ell = (arb_ell + A) * branch_left(arb_ell) / ((arb_ell - arb_r) * (arb_ell - arb(1)))
    mass_r = (arb_r + A) * branch_left(arb_r) / ((arb_r - arb_ell) * (arb_r - arb(1)))
    mass_1 = (arb(1) + A) * branch_right(arb(1)) / ((arb(1) - arb_ell) * (arb(1) - arb_r))
    dmass_ell = direction_A * mass_ell / (arb_ell + A) + direction_alpha * mass_ell / (2 * (alpha - arb_ell))
    dmass_r = direction_A * mass_r / (arb_r + A) + direction_alpha * mass_r / (2 * (alpha - arb_r))
    dmass_1 = direction_A * mass_1 / (arb(1) + A) - direction_alpha * mass_1 / (2 * (arb(1) - alpha))

    atom_part = (
        dmass_ell * (-(alpha - arb_ell).log()) - mass_ell * direction_alpha / (alpha - arb_ell)
        + dmass_r * (-(alpha - arb_r).log()) - mass_r * direction_alpha / (alpha - arb_r)
        + dmass_1 * (-(arb(1) - alpha).log()) - mass_1 * direction_alpha / (alpha - arb(1))
    )

    # Use two endpoint charts.  The u = sin(theta/2) chart keeps the beta-side
    # pole at 1 separated; the v = cos(theta/2) chart keeps the contact log
    # away from log(0).  They meet at u=0.8, v=0.6.
    half = (arb_beta - alpha) / 2
    acb_half = acb(half)
    acb_beta = acb(arb_beta)
    acb_A = acb(A)
    acb_ell = acb(arb_ell)
    acb_r = acb(arb_r)
    acb_pi = acb(pi)
    acb_direction_A = acb(direction_A)
    acb_direction_alpha = acb(direction_alpha)
    acb_half_s = -acb("0.5") * acb_direction_alpha

    def derivative_integrand(u2, endpoint_factor, t, t_s, analytic: bool) -> acb:
        denominator = (t - acb_ell) * (t - acb_r) * (t - acb(1))
        denominator_prime = (
            (t - acb_r) * (t - acb(1))
            + (t - acb_ell) * (t - acb(1))
            + (t - acb_ell) * (t - acb_r)
        )
        denominator_s = t_s * denominator_prime
        prefactor = -(acb(8) * u2 * endpoint_factor / acb_pi)
        density_times_dt = prefactor * acb_half * acb_half * (t + acb_A) / denominator
        density_times_dt_s = prefactor * (
            acb(2) * acb_half * acb_half_s * (t + acb_A) / denominator
            + acb_half
            * acb_half
            * ((t_s + acb_direction_A) * denominator - (t + acb_A) * denominator_s)
            / (denominator * denominator)
        )
        log_contact_s = acb_direction_alpha / (acb(2) * acb_half)
        return density_times_dt_s, density_times_dt, log_contact_s

    def u_integrand(u: acb, analytic: bool) -> acb:
        u2 = u * u
        endpoint_factor = (acb(1) - u2).sqrt(analytic=analytic)
        t = acb_beta - acb(2) * acb_half * u2
        t_s = u2 * acb_direction_alpha
        density_times_dt_s, density_times_dt, log_contact_s = derivative_integrand(
            u2,
            endpoint_factor,
            t,
            t_s,
            analytic,
        )
        log_contact = -((acb(2) * acb_half) * (acb(1) - u2)).log(analytic=analytic)
        return density_times_dt_s * log_contact + density_times_dt * log_contact_s

    def v_integrand(v: acb, analytic: bool) -> acb:
        v2 = v * v
        endpoint_factor = (acb(1) - v2).sqrt(analytic=analytic)
        t = acb(2) * acb_half * v2 + acb_beta - acb(2) * acb_half
        t_s = (acb(1) - v2) * acb_direction_alpha
        density_times_dt_s, density_times_dt, log_contact_s = derivative_integrand(
            v2,
            endpoint_factor,
            t,
            t_s,
            analytic,
        )
        log_contact = -((acb(2) * acb_half) * v2).log(analytic=analytic)
        return density_times_dt_s * log_contact + density_times_dt * log_contact_s

    continuous_part = acb(0)
    u_breakpoints = [0.0, 0.05, 0.1, 0.2, 0.35, 0.5, 0.65, 0.8]
    for left, right in zip(u_breakpoints, u_breakpoints[1:]):
        continuous_part += acb.integral(
            u_integrand,
            arb(repr(left)),
            arb(repr(right)),
            rel_tol=arb("1e-45"),
            abs_tol=arb("1e-45"),
            deg_limit=64,
            eval_limit=20000,
            depth_limit=100,
        )

    delta = 1.0e-4
    v_breakpoints = [delta, 0.001, 0.005, 0.02, 0.06, 0.12, 0.25, 0.4, 0.6]
    for left, right in zip(v_breakpoints, v_breakpoints[1:]):
        continuous_part += acb.integral(
            v_integrand,
            arb(repr(left)),
            arb(repr(right)),
            rel_tol=arb("1e-45"),
            abs_tol=arb("1e-45"),
            deg_limit=64,
            eval_limit=20000,
            depth_limit=100,
        )

    def tail_radius() -> arb:
        v = _arb_interval_from_bounds(0.0, delta)
        v2 = v * v
        endpoint_factor = (1 - v2).sqrt()
        t = alpha + 2 * half * v2
        t_s = (1 - v2) * direction_alpha
        denominator = (t - arb_ell) * (t - arb_r) * (t - arb(1))
        denominator_prime = (
            (t - arb_r) * (t - arb(1))
            + (t - arb_ell) * (t - arb(1))
            + (t - arb_ell) * (t - arb_r)
        )
        denominator_s = t_s * denominator_prime
        prefactor = -(8 * v2 * endpoint_factor / pi)
        density_times_dt = prefactor * half * half * (t + A) / denominator
        density_times_dt_s = prefactor * (
            2 * half * (-direction_alpha / 2) * (t + A) / denominator
            + half
            * half
            * ((t_s + direction_A) * denominator - (t + A) * denominator_s)
            / (denominator * denominator)
        )

        half_low = max(float(half.lower()), 1.0e-300)
        pcoef = float(abs(density_times_dt_s).upper()) / (delta * delta)
        q_upper = abs(density_times_dt * direction_alpha / (2 * half)).upper()
        qcoef = float(q_upper) / (delta * delta)
        log_weight = -math.log(2.0 * half_low * delta * delta) + 2.0 / 3.0
        radius = pcoef * delta**3 * max(log_weight, 0.0) / 3.0
        radius += qcoef * delta**3 / 3.0
        return arb(f"[+/- {radius!r}]")

    return str(atom_part + continuous_part.real + tail_radius())


def _combined_contact_minus_one_directional_derivative_acb_from_arb(
    A,
    alpha,
    epsilon,
    direction_A,
    direction_alpha,
    left_weight,
    precision: int,
) -> str:
    """Arb/Acb box for ``left_weight*dU(alpha) + dU(-1)``.

    This combined primitive is used for the rescaled K2 derivative.  Computing
    the two derivatives separately and adding them after interval evaluation
    loses the leading cancellation in the singular Lyapunov-Schmidt coordinate.
    """

    from flint import acb, arb, ctx

    ctx.prec = precision
    arb_ell = arb(repr(X_LEFT)) + epsilon
    arb_r = arb(repr(X_RIGHT))
    arb_beta = arb(1) - epsilon
    pi = arb.pi()

    def branch_left(q: arb) -> arb:
        return -((alpha - q) * (arb_beta - q)).sqrt()

    def branch_right(q: arb) -> arb:
        return ((q - alpha) * (q - arb_beta)).sqrt()

    mass_ell = (arb_ell + A) * branch_left(arb_ell) / ((arb_ell - arb_r) * (arb_ell - arb(1)))
    mass_r = (arb_r + A) * branch_left(arb_r) / ((arb_r - arb_ell) * (arb_r - arb(1)))
    mass_1 = (arb(1) + A) * branch_right(arb(1)) / ((arb(1) - arb_ell) * (arb(1) - arb_r))
    dmass_ell = direction_A * mass_ell / (arb_ell + A) + direction_alpha * mass_ell / (2 * (alpha - arb_ell))
    dmass_r = direction_A * mass_r / (arb_r + A) + direction_alpha * mass_r / (2 * (alpha - arb_r))
    dmass_1 = direction_A * mass_1 / (arb(1) + A) - direction_alpha * mass_1 / (2 * (arb(1) - alpha))

    contact_atom = (
        dmass_ell * (-(alpha - arb_ell).log()) - mass_ell * direction_alpha / (alpha - arb_ell)
        + dmass_r * (-(alpha - arb_r).log()) - mass_r * direction_alpha / (alpha - arb_r)
        + dmass_1 * (-(arb(1) - alpha).log()) - mass_1 * direction_alpha / (alpha - arb(1))
    )
    minus_one_atom = (
        dmass_ell * (-(-arb(1) - arb_ell).log())
        + dmass_r * (-(arb(1) + arb_r).log())
        + dmass_1 * (-arb(2).log())
    )
    atom_part = left_weight * contact_atom + minus_one_atom

    half = (arb_beta - alpha) / 2
    acb_half = acb(half)
    acb_beta = acb(arb_beta)
    acb_A = acb(A)
    acb_ell = acb(arb_ell)
    acb_r = acb(arb_r)
    acb_pi = acb(pi)
    acb_direction_A = acb(direction_A)
    acb_direction_alpha = acb(direction_alpha)
    acb_left_weight = acb(left_weight)
    acb_half_s = -acb("0.5") * acb_direction_alpha

    def density_parts(u2, endpoint_factor, t, t_s):
        denominator = (t - acb_ell) * (t - acb_r) * (t - acb(1))
        denominator_prime = (
            (t - acb_r) * (t - acb(1))
            + (t - acb_ell) * (t - acb(1))
            + (t - acb_ell) * (t - acb_r)
        )
        denominator_s = t_s * denominator_prime
        prefactor = -(acb(8) * u2 * endpoint_factor / acb_pi)
        density_times_dt = prefactor * acb_half * acb_half * (t + acb_A) / denominator
        density_times_dt_s = prefactor * (
            acb(2) * acb_half * acb_half_s * (t + acb_A) / denominator
            + acb_half
            * acb_half
            * ((t_s + acb_direction_A) * denominator - (t + acb_A) * denominator_s)
            / (denominator * denominator)
        )
        return density_times_dt_s, density_times_dt

    def combined_integrand(u2, endpoint_factor, t, t_s, log_contact, analytic: bool) -> acb:
        density_times_dt_s, density_times_dt = density_parts(u2, endpoint_factor, t, t_s)
        log_contact_s = acb_direction_alpha / (acb(2) * acb_half)
        contact = density_times_dt_s * log_contact + density_times_dt * log_contact_s
        log_minus_one = -((t + acb(1)).log(analytic=analytic))
        log_minus_one_s = -t_s / (t + acb(1))
        minus_one = density_times_dt_s * log_minus_one + density_times_dt * log_minus_one_s
        return acb_left_weight * contact + minus_one

    def u_integrand(u: acb, analytic: bool) -> acb:
        u2 = u * u
        endpoint_factor = (acb(1) - u2).sqrt(analytic=analytic)
        t = acb_beta - acb(2) * acb_half * u2
        t_s = u2 * acb_direction_alpha
        log_contact = -((acb(2) * acb_half) * (acb(1) - u2)).log(analytic=analytic)
        return combined_integrand(u2, endpoint_factor, t, t_s, log_contact, analytic)

    def v_integrand(v: acb, analytic: bool) -> acb:
        v2 = v * v
        endpoint_factor = (acb(1) - v2).sqrt(analytic=analytic)
        t = acb(2) * acb_half * v2 + acb_beta - acb(2) * acb_half
        t_s = (acb(1) - v2) * acb_direction_alpha
        log_contact = -((acb(2) * acb_half) * v2).log(analytic=analytic)
        return combined_integrand(v2, endpoint_factor, t, t_s, log_contact, analytic)

    continuous_part = acb(0)
    u_breakpoints = [0.0, 0.05, 0.1, 0.2, 0.35, 0.5, 0.65, 0.8]
    for left, right in zip(u_breakpoints, u_breakpoints[1:]):
        continuous_part += acb.integral(
            u_integrand,
            arb(repr(left)),
            arb(repr(right)),
            rel_tol=arb("1e-45"),
            abs_tol=arb("1e-45"),
            deg_limit=64,
            eval_limit=20000,
            depth_limit=100,
        )

    delta = 1.0e-4
    v_breakpoints = [delta, 0.001, 0.005, 0.02, 0.06, 0.12, 0.25, 0.4, 0.6]
    for left, right in zip(v_breakpoints, v_breakpoints[1:]):
        continuous_part += acb.integral(
            v_integrand,
            arb(repr(left)),
            arb(repr(right)),
            rel_tol=arb("1e-45"),
            abs_tol=arb("1e-45"),
            deg_limit=64,
            eval_limit=20000,
            depth_limit=100,
        )

    def tail_radius() -> arb:
        v = _arb_interval_from_bounds(0.0, delta)
        v2 = v * v
        endpoint_factor = (1 - v2).sqrt()
        t = alpha + 2 * half * v2
        t_s = (1 - v2) * direction_alpha
        denominator = (t - arb_ell) * (t - arb_r) * (t - arb(1))
        denominator_prime = (
            (t - arb_r) * (t - arb(1))
            + (t - arb_ell) * (t - arb(1))
            + (t - arb_ell) * (t - arb_r)
        )
        denominator_s = t_s * denominator_prime
        prefactor = -(8 * v2 * endpoint_factor / pi)
        density_times_dt = prefactor * half * half * (t + A) / denominator
        density_times_dt_s = prefactor * (
            2 * half * (-direction_alpha / 2) * (t + A) / denominator
            + half
            * half
            * ((t_s + direction_A) * denominator - (t + A) * denominator_s)
            / (denominator * denominator)
        )

        half_low = max(float(half.lower()), 1.0e-300)
        pcoef = float(abs(density_times_dt_s).upper()) / (delta * delta)
        q_upper = abs(density_times_dt * direction_alpha / (2 * half)).upper()
        qcoef = float(q_upper) / (delta * delta)
        log_weight = -math.log(2.0 * half_low * delta * delta) + 2.0 / 3.0
        contact_radius = pcoef * delta**3 * max(log_weight, 0.0) / 3.0
        contact_radius += qcoef * delta**3 / 3.0

        density_times_dt_s, density_times_dt = density_parts(acb(v2), acb(endpoint_factor), acb(t), acb(t_s))
        fixed_tail_integrand = (
            density_times_dt_s * (-(acb(t + 1)).log())
            + density_times_dt * (-acb(t_s) / acb(t + 1))
        )
        fixed_tail_radius = float(abs(fixed_tail_integrand.real).upper()) * delta
        return arb(f"[+/- {float(abs(left_weight).upper()) * contact_radius + fixed_tail_radius!r}]")

    return str(atom_part + continuous_part.real + tail_radius())


def _combined_directional_derivative_residue_log_from_arb(
    A,
    alpha,
    epsilon,
    direction_A,
    direction_alpha,
    left_weight,
    precision: int,
) -> str:
    """Residue-log box for ``left_weight*dU(alpha) + dU(-1)``.

    This uses the full differentiated Cauchy transform

        F_s(z) = R(z)/D(z) * (direction_A - (z + A) direction_alpha/(2(z-alpha)))

    in the Joukowski coordinate.  It avoids splitting the derivative measure
    into endpoint atoms plus a continuous density, which is exactly where the
    eta-slab K2/tau interval check loses the leading cancellation.
    """

    from flint import arb, ctx

    ctx.prec = precision
    ell = arb(repr(X_LEFT)) + epsilon
    r = arb(repr(X_RIGHT))
    beta = arb(1) - epsilon
    eta = epsilon.sqrt()
    center = (alpha + beta) / 2
    scale = (beta - alpha) / 4

    def preimages(q):
        y = (q - center) / scale
        root = (y * y - 4).sqrt()
        return ((y - root) / 2, (y + root) / 2)

    def left_preimages(q):
        y = (q - center) / scale
        root = (y * y - 4).sqrt()
        outer = (y - root) / 2
        return (outer, 1 / outer)

    def branch_value(rho):
        return scale * (rho - 1 / rho)

    sqrt_one_minus_alpha = (arb(1) - alpha).sqrt()
    one_preimages = (
        (sqrt_one_minus_alpha - eta) / (sqrt_one_minus_alpha + eta),
        (sqrt_one_minus_alpha + eta) / (sqrt_one_minus_alpha - eta),
    )
    pole_data = (
        (ell, (ell - r) * (ell - arb(1)), left_preimages(ell)),
        (r, (r - ell) * (r - arb(1)), left_preimages(r)),
        (arb(1), (arb(1) - ell) * (arb(1) - r), one_preimages),
    )

    def residue(q, q_derivative, rho):
        return branch_value(rho) / q_derivative * (
            direction_A - (q + A) * direction_alpha / (2 * (q - alpha))
        )

    def log_abs(value):
        return abs(value).log()

    def primitive(w):
        total = arb(0)
        for q, q_derivative, explicit_preimages in pole_data:
            q_preimages = explicit_preimages if explicit_preimages is not None else preimages(q)
            for rho in q_preimages:
                total += residue(q, q_derivative, rho) * log_abs(w - rho)
        return total

    y_minus_one = (-arb(1) - center) / scale
    w_minus_one = (y_minus_one - (y_minus_one * y_minus_one - 4).sqrt()) / 2
    return str(-left_weight * primitive(-arb(1)) - primitive(w_minus_one))


def _combined_directional_derivative_residue_log_divided_from_arb(
    A,
    alpha,
    eta,
    direction_A,
    direction_alpha,
    left_weight,
    limit_A,
    limit_alpha,
    precision: int,
) -> str:
    """Eta-divided residue-log box for the rescaled K2 derivative.

    Returns ``H_s(A, alpha, eta) / eta`` using the eta-divided form

    where ``H_s = left_weight*dU(alpha)[s] + dU(-1)[s]`` and the direction
    ``s`` is ``direction_A*dA + direction_alpha*dalpha`` at fixed eta.  This is
    the quantity needed in the second row of the eta-slab DK check.
    """

    from flint import arb, ctx

    ctx.prec = precision
    epsilon = eta * eta
    ell = arb(repr(X_LEFT)) + epsilon
    ell0 = arb(repr(X_LEFT))
    r = arb(repr(X_RIGHT))
    beta = arb(1) - epsilon
    beta0 = arb(1)
    center = (alpha + beta) / 2
    scale = (beta - alpha) / 4
    center0 = (limit_alpha + beta0) / 2
    scale0 = (beta0 - limit_alpha) / 4

    def left_preimages(q, q_center, q_scale):
        y = (q - q_center) / q_scale
        root = (y * y - 4).sqrt()
        outer = (y - root) / 2
        return (outer, 1 / outer)

    def branch_value(rho, q_scale):
        return q_scale * (rho - 1 / rho)

    def residue(q, q_derivative, rho, q_A, q_alpha, q_scale):
        return branch_value(rho, q_scale) / q_derivative * (
            direction_A - (q + q_A) * direction_alpha / (2 * (q - q_alpha))
        )

    def log_abs(value):
        return abs(value).log()

    def divided_smooth_term(q, q0, q_derivative, q0_derivative, x, x0):
        total = arb(0)
        current_preimages = left_preimages(q, center, scale)
        limit_preimages = left_preimages(q0, center0, scale0)
        for rho, rho0 in zip(current_preimages, limit_preimages):
            a = residue(q, q_derivative, rho, A, alpha, scale)
            a0 = residue(q0, q0_derivative, rho0, limit_A, limit_alpha, scale0)
            b = x - rho
            b0 = x0 - rho0
            total += ((a - a0) / eta) * log_abs(b0)
            total += a * log_abs(b / b0) / eta
        return total

    def endpoint_pair_divided(x):
        sqrt_one_minus_alpha = (arb(1) - alpha).sqrt()
        rho_minus = (sqrt_one_minus_alpha - eta) / (sqrt_one_minus_alpha + eta)
        rho_plus = (sqrt_one_minus_alpha + eta) / (sqrt_one_minus_alpha - eta)
        coefficient = sqrt_one_minus_alpha / ((arb(1) - ell) * (arb(1) - r)) * (
            direction_A - (arb(1) + A) * direction_alpha / (2 * (arb(1) - alpha))
        )
        return coefficient * log_abs((x - rho_plus) / (x - rho_minus))

    ell_derivative = (ell - r) * (ell - arb(1))
    ell0_derivative = (ell0 - r) * (ell0 - arb(1))
    r_derivative = (r - ell) * (r - arb(1))
    r0_derivative = (r - ell0) * (r - arb(1))

    x_alpha = -arb(1)
    x_alpha0 = -arb(1)
    x_minus_one = left_preimages(-arb(1), center, scale)[0]
    x_minus_one0 = left_preimages(-arb(1), center0, scale0)[0]

    def primitive_divided(x, x0):
        return (
            divided_smooth_term(ell, ell0, ell_derivative, ell0_derivative, x, x0)
            + divided_smooth_term(r, r, r_derivative, r0_derivative, x, x0)
            + endpoint_pair_divided(x)
        )

    def primitive_limit(x0):
        total = arb(0)
        for q0, q0_derivative in ((ell0, ell0_derivative), (r, r0_derivative)):
            for rho0 in left_preimages(q0, center0, scale0):
                a0 = residue(q0, q0_derivative, rho0, limit_A, limit_alpha, scale0)
                total += a0 * log_abs(x0 - rho0)
        return total

    divided = -left_weight * primitive_divided(x_alpha, x_alpha0) - primitive_divided(x_minus_one, x_minus_one0)
    limit_value = -left_weight * primitive_limit(x_alpha0) - primitive_limit(x_minus_one0)
    return str(divided + limit_value / eta)


def _combined_directional_derivative_residue_log_pair_divided_from_arb(
    A,
    alpha,
    eta,
    direction_A,
    direction_alpha,
    left_weight,
    limit_A,
    limit_alpha,
    precision: int,
    base_delta_A=None,
    base_delta_alpha=None,
) -> str:
    """Eta-divided residue-log prototype with paired ell/r sheets.

    This is a stricter experiment than
    ``_combined_directional_derivative_residue_log_divided_from_arb``: the two
    large smooth-pole terms on each Joukowski sheet are paired before interval
    enclosure, so the cancellation between the ell and r residues is kept
    inside the same expression.
    """

    from flint import arb, ctx

    ctx.prec = precision
    epsilon = eta * eta
    ell = arb(repr(X_LEFT)) + epsilon
    ell0 = arb(repr(X_LEFT))
    r = arb(repr(X_RIGHT))
    beta = arb(1) - epsilon
    beta0 = arb(1)
    center = (alpha + beta) / 2
    scale = (beta - alpha) / 4
    center0 = (limit_alpha + beta0) / 2
    scale0 = (beta0 - limit_alpha) / 4

    def left_preimages(q, q_center, q_scale):
        y = (q - q_center) / q_scale
        root = (y * y - 4).sqrt()
        outer = (y - root) / 2
        return (outer, 1 / outer)

    def branch_value(rho, q_scale):
        return q_scale * (rho - 1 / rho)

    def residue(q, q_derivative, rho, q_A, q_alpha, q_scale):
        return branch_value(rho, q_scale) / q_derivative * (
            direction_A - (q + q_A) * direction_alpha / (2 * (q - q_alpha))
        )

    def log_abs(value):
        return abs(value).log()

    def log_one_plus_over_z(z):
        radius = float(abs(z).upper())
        if radius >= 0.25:
            return abs(arb(1) + z).log() / z
        total = arb(0)
        power = arb(1)
        terms = 40
        for index in range(terms):
            if index:
                power *= z
            term = power / arb(index + 1)
            total += -term if index % 2 else term
        tail = radius**terms / ((terms + 1) * (1.0 - radius))
        return total + arb(f"[+/- {tail!r}]")

    def log_abs_ratio_divided(value, value0, value_div):
        z = eta * value_div / value0
        if float(abs(z).upper()) < 0.25 and float((arb(1) + z).lower()) > 0.0:
            return value_div / value0 * log_one_plus_over_z(z)
        return log_abs(value / value0) / eta

    ell_derivative = (ell - r) * (ell - arb(1))
    ell0_derivative = (ell0 - r) * (ell0 - arb(1))
    r_derivative = (r - ell) * (r - arb(1))
    r0_derivative = (r - ell0) * (r - arb(1))

    tau = base_delta_alpha if base_delta_alpha is not None else (alpha - limit_alpha) / eta
    A_div = base_delta_A if base_delta_A is not None else (A - limit_A) / eta
    center_div = (tau - eta) / 2
    scale_div = -(tau + eta) / 4

    def preimage_pair_divided(q, q0, q_div):
        y = (q - center) / scale
        y0 = (q0 - center0) / scale0
        root = (y * y - 4).sqrt()
        outer = (y - root) / 2
        root0 = (y0 * y0 - 4).sqrt()
        outer0 = (y0 - root0) / 2
        inner = 1 / outer
        inner0 = 1 / outer0
        outer_div = (q_div - center_div - scale_div * (outer0 + 1 / outer0)) / (
            scale * (1 - 1 / (outer * outer0))
        )
        inner_div = (q_div - center_div - scale_div * (inner0 + 1 / inner0)) / (
            scale * (1 - 1 / (inner * inner0))
        )
        return ((outer, outer0, outer_div), (inner, inner0, inner_div))

    def branch_value_divided(rho, rho0, rho_div):
        inverse_div = -rho_div / (rho * rho0)
        return scale_div * (rho0 - 1 / rho0) + scale * (rho_div - inverse_div)

    def quotient_divided(numerator, numerator0, numerator_div, denominator, denominator0, denominator_div):
        return (numerator_div * denominator0 - numerator0 * denominator_div) / (denominator * denominator0)

    def residue_divided(q, q0, q_div, q_derivative, q0_derivative, q_derivative_div, rho, rho0, rho_div):
        branch = branch_value(rho, scale)
        branch0 = branch_value(rho0, scale0)
        branch_div = branch_value_divided(rho, rho0, rho_div)
        multiplier = branch / q_derivative
        multiplier0 = branch0 / q0_derivative
        multiplier_div = quotient_divided(
            branch,
            branch0,
            branch_div,
            q_derivative,
            q0_derivative,
            q_derivative_div,
        )
        numerator = q + A
        numerator0 = q0 + limit_A
        numerator_div = q_div + A_div
        denominator = q - alpha
        denominator0 = q0 - limit_alpha
        denominator_div = q_div - tau
        ratio_div = quotient_divided(
            numerator,
            numerator0,
            numerator_div,
            denominator,
            denominator0,
            denominator_div,
        )
        factor = direction_A - numerator * direction_alpha / (2 * denominator)
        factor0 = direction_A - numerator0 * direction_alpha / (2 * denominator0)
        factor_div = -direction_alpha * ratio_div / 2
        return multiplier_div * factor0 + multiplier * factor_div

    ell_q_div = eta
    r_q_div = arb(0)
    ell_derivative_div = eta * (ell0 - arb(1)) + eta * (ell - r)
    r_derivative_div = -eta * (r - arb(1))

    ell_preimage_data = preimage_pair_divided(ell, ell0, ell_q_div)
    r_preimage_data = preimage_pair_divided(r, r, r_q_div)

    def paired_smooth_divided(x, x0, x_div):
        total = arb(0)
        for (rho_ell, rho_ell0, rho_ell_div), (rho_r, rho_r0, rho_r_div) in zip(
            ell_preimage_data,
            r_preimage_data,
        ):
            a_ell = residue(ell, ell_derivative, rho_ell, A, alpha, scale)
            a_ell0 = residue(ell0, ell0_derivative, rho_ell0, limit_A, limit_alpha, scale0)
            a_r = residue(r, r_derivative, rho_r, A, alpha, scale)
            a_r0 = residue(r, r0_derivative, rho_r0, limit_A, limit_alpha, scale0)
            a_ell_div = residue_divided(
                ell,
                ell0,
                ell_q_div,
                ell_derivative,
                ell0_derivative,
                ell_derivative_div,
                rho_ell,
                rho_ell0,
                rho_ell_div,
            )
            a_r_div = residue_divided(
                r,
                r,
                r_q_div,
                r_derivative,
                r0_derivative,
                r_derivative_div,
                rho_r,
                rho_r0,
                rho_r_div,
            )
            sum_residue = a_ell + a_r
            sum_residue_div = a_ell_div + a_r_div

            ratio = (x - rho_ell) / (x - rho_r)
            ratio0 = (x0 - rho_ell0) / (x0 - rho_r0)
            ratio_div = quotient_divided(
                x - rho_ell,
                x0 - rho_ell0,
                x_div - rho_ell_div,
                x - rho_r,
                x0 - rho_r0,
                x_div - rho_r_div,
            )
            base = x - rho_r
            base0 = x0 - rho_r0
            base_div = x_div - rho_r_div

            total += a_ell_div * log_abs(ratio0)
            total += a_ell * log_abs_ratio_divided(ratio, ratio0, ratio_div)
            total += sum_residue_div * log_abs(base0)
            total += sum_residue * log_abs_ratio_divided(base, base0, base_div)
        return total

    def paired_smooth_limit(x0):
        total = arb(0)
        for (_rho_ell, rho_ell0, _rho_ell_div), (_rho_r, rho_r0, _rho_r_div) in zip(
            ell_preimage_data,
            r_preimage_data,
        ):
            a_ell0 = residue(ell0, ell0_derivative, rho_ell0, limit_A, limit_alpha, scale0)
            a_r0 = residue(r, r0_derivative, rho_r0, limit_A, limit_alpha, scale0)
            total += a_ell0 * log_abs(x0 - rho_ell0) + a_r0 * log_abs(x0 - rho_r0)
        return total

    def endpoint_pair_divided(x):
        sqrt_one_minus_alpha = (arb(1) - alpha).sqrt()
        rho_minus = (sqrt_one_minus_alpha - eta) / (sqrt_one_minus_alpha + eta)
        rho_plus = (sqrt_one_minus_alpha + eta) / (sqrt_one_minus_alpha - eta)
        coefficient = sqrt_one_minus_alpha / ((arb(1) - ell) * (arb(1) - r)) * (
            direction_A - (arb(1) + A) * direction_alpha / (2 * (arb(1) - alpha))
        )
        return coefficient * log_abs((x - rho_plus) / (x - rho_minus))

    x_alpha = -arb(1)
    x_alpha0 = -arb(1)
    x_alpha_div = arb(0)
    x_minus_one, x_minus_one0, x_minus_one_div = preimage_pair_divided(-arb(1), -arb(1), arb(0))[0]

    divided = -left_weight * (
        paired_smooth_divided(x_alpha, x_alpha0, x_alpha_div) + endpoint_pair_divided(x_alpha)
    ) - (
        paired_smooth_divided(x_minus_one, x_minus_one0, x_minus_one_div) + endpoint_pair_divided(x_minus_one)
    )
    limit_value = -left_weight * paired_smooth_limit(x_alpha0) - paired_smooth_limit(x_minus_one0)
    return str(divided + limit_value / eta)


def _potential_residue_log_value_from_arb(A, alpha, eta, x_kind: str, precision: int) -> str:
    """Residue-log value primitive for the full potential.

    This evaluates the normalized absolute potential using

        U(x) = -log|x| - sum Res((F(z(w)) - 1/z(w)) z'(w)) log|w_x-rho|.

    Unlike the atom-plus-density value kernels, this keeps the atom and
    continuous contributions in one residue-log expression.  That is the value
    level analogue of the derivative residue-log kernels above.
    """

    from flint import arb, ctx

    ctx.prec = precision
    epsilon = eta * eta
    ell = arb(repr(X_LEFT)) + epsilon
    r = arb(repr(X_RIGHT))
    one = arb(1)
    zero = arb(0)
    beta = one - epsilon
    center = (alpha + beta) / 2
    scale = (beta - alpha) / 4

    def log_abs(value):
        return abs(value).log()

    def preimage_pair(q):
        y = (q - center) / scale
        root = (y * y - 4).sqrt()
        outer = (y - root) / 2
        return (outer, 1 / outer)

    def left_preimage(q):
        return preimage_pair(q)[0]

    def branch_value(rho):
        return scale * (rho - 1 / rho)

    if x_kind == "contact":
        x = alpha
        w_x = -one
    elif x_kind == "minus_one":
        x = -one
        w_x = left_preimage(x)
    else:
        raise ValueError(f"unknown x_kind {x_kind!r}")

    total = arb(0)
    pole_data = (
        (ell, (ell - r) * (ell - one)),
        (r, (r - ell) * (r - one)),
        (one, (one - ell) * (one - r)),
    )
    for q, q_derivative in pole_data:
        for rho in preimage_pair(q):
            residue = (q + A) * branch_value(rho) / q_derivative
            total += residue * log_abs(w_x - rho)

    # The -1/z normalization contributes residue -1 at both preimages of z=0.
    for rho in preimage_pair(zero):
        total -= log_abs(w_x - rho)

    # The Joukowski coordinate contributes an additional residue at w=0.  This
    # term vanishes at the contact point w=-1, but is essential on the left
    # sheet, for example at x=-1.
    total += 2 * log_abs(w_x)

    return str(-log_abs(x) - total)


def _rescaled_residue_log_values_from_arb(A, alpha, eta, left_weight, precision: int) -> tuple[str, str]:
    """Return residue-log boxes for K1=U(alpha)/eta and K2=H/eta^2."""

    from flint import arb

    U_alpha = arb(_potential_residue_log_value_from_arb(A, alpha, eta, "contact", precision))
    U_minus_one = arb(_potential_residue_log_value_from_arb(A, alpha, eta, "minus_one", precision))
    H = left_weight * U_alpha + U_minus_one
    return str(U_alpha / eta), str(H / (eta * eta))


def _potential_residue_log_value_divided_from_arb(
    A,
    alpha,
    eta,
    limit_A,
    limit_alpha,
    x_kind: str,
    precision: int,
    base_delta_A=None,
    base_delta_alpha=None,
) -> str:
    """First eta-divided residue-log value primitive.

    Returns ``(U_eta(x_eta)-U_0(x_0))/eta`` with pole/preimage/log-ratio
    differences paired before interval evaluation.
    """

    from flint import arb, ctx

    ctx.prec = precision
    one = arb(1)
    zero = arb(0)
    epsilon = eta * eta
    ell = arb(repr(X_LEFT)) + epsilon
    ell0 = arb(repr(X_LEFT))
    r = arb(repr(X_RIGHT))
    beta = one - epsilon
    beta0 = one
    center = (alpha + beta) / 2
    scale = (beta - alpha) / 4
    center0 = (limit_alpha + beta0) / 2
    scale0 = (beta0 - limit_alpha) / 4
    tau = base_delta_alpha if base_delta_alpha is not None else (alpha - limit_alpha) / eta
    A_div = base_delta_A if base_delta_A is not None else (A - limit_A) / eta
    center_div = (tau - eta) / 2
    scale_div = -(tau + eta) / 4

    def log_abs(value):
        return abs(value).log()

    def log_one_plus_over_z(z):
        radius = float(abs(z).upper())
        if radius >= 0.25:
            return abs(one + z).log() / z
        total = arb(0)
        power = arb(1)
        terms = 48
        for index in range(terms):
            if index:
                power *= z
            term = power / arb(index + 1)
            total += -term if index % 2 else term
        tail = radius**terms / ((terms + 1) * (1.0 - radius))
        return total + arb(f"[+/- {tail!r}]")

    def log_abs_ratio_divided(value, value0, value_div):
        z = eta * value_div / value0
        if float(abs(z).upper()) < 0.25 and float((one + z).lower()) > 0.0:
            return value_div / value0 * log_one_plus_over_z(z)
        return log_abs(value / value0) / eta

    def preimage_pair_divided(q, q0, q_div):
        y = (q - center) / scale
        y0 = (q0 - center0) / scale0
        root = (y * y - 4).sqrt()
        outer = (y - root) / 2
        root0 = (y0 * y0 - 4).sqrt()
        outer0 = (y0 - root0) / 2
        inner = 1 / outer
        inner0 = 1 / outer0
        outer_div = (q_div - center_div - scale_div * (outer0 + 1 / outer0)) / (
            scale * (1 - 1 / (outer * outer0))
        )
        inner_div = (q_div - center_div - scale_div * (inner0 + 1 / inner0)) / (
            scale * (1 - 1 / (inner * inner0))
        )
        return ((outer, outer0, outer_div), (inner, inner0, inner_div))

    def branch_value(rho, q_scale):
        return q_scale * (rho - 1 / rho)

    def branch_value_divided(rho, rho0, rho_div):
        inverse_div = -rho_div / (rho * rho0)
        return scale_div * (rho0 - 1 / rho0) + scale * (rho_div - inverse_div)

    def quotient_divided(numerator, numerator0, numerator_div, denominator, denominator0, denominator_div):
        return (numerator_div * denominator0 - numerator0 * denominator_div) / (denominator * denominator0)

    def residue(q, q_derivative, rho, q_A, q_scale):
        return (q + q_A) * branch_value(rho, q_scale) / q_derivative

    def residue_divided(q, q0, q_div, q_derivative, q0_derivative, q_derivative_div, rho, rho0, rho_div):
        numerator = (q + A) * branch_value(rho, scale)
        numerator0 = (q0 + limit_A) * branch_value(rho0, scale0)
        numerator_div = (q_div + A_div) * branch_value(rho0, scale0) + (q + A) * branch_value_divided(rho, rho0, rho_div)
        return quotient_divided(numerator, numerator0, numerator_div, q_derivative, q0_derivative, q_derivative_div)

    if x_kind == "contact":
        x = alpha
        x0 = limit_alpha
        x_div = tau
        w_x = -one
        w_x0 = -one
        w_x_div = zero
    elif x_kind == "minus_one":
        x = -one
        x0 = -one
        x_div = zero
        w_x, w_x0, w_x_div = preimage_pair_divided(x, x0, x_div)[0]
    else:
        raise ValueError(f"unknown x_kind {x_kind!r}")

    total = -log_abs_ratio_divided(x, x0, x_div)

    ell_derivative = (ell - r) * (ell - one)
    ell0_derivative = (ell0 - r) * (ell0 - one)
    r_derivative = (r - ell) * (r - one)
    r0_derivative = (r - ell0) * (r - one)
    ell_q_div = eta
    r_q_div = zero
    ell_derivative_div = eta * (ell0 - one) + eta * (ell - r)
    r_derivative_div = -eta * (r - one)

    ell_preimages = preimage_pair_divided(ell, ell0, ell_q_div)
    r_preimages = preimage_pair_divided(r, r, r_q_div)
    for (rho_ell, rho_ell0, rho_ell_div), (rho_r, rho_r0, rho_r_div) in zip(ell_preimages, r_preimages):
        a_ell = residue(ell, ell_derivative, rho_ell, A, scale)
        a_r = residue(r, r_derivative, rho_r, A, scale)
        a_ell_div = residue_divided(
            ell,
            ell0,
            ell_q_div,
            ell_derivative,
            ell0_derivative,
            ell_derivative_div,
            rho_ell,
            rho_ell0,
            rho_ell_div,
        )
        a_r_div = residue_divided(
            r,
            r,
            r_q_div,
            r_derivative,
            r0_derivative,
            r_derivative_div,
            rho_r,
            rho_r0,
            rho_r_div,
        )
        sum_residue = a_ell + a_r
        sum_residue_div = a_ell_div + a_r_div
        ratio = (w_x - rho_ell) / (w_x - rho_r)
        ratio0 = (w_x0 - rho_ell0) / (w_x0 - rho_r0)
        ratio_div = quotient_divided(
            w_x - rho_ell,
            w_x0 - rho_ell0,
            w_x_div - rho_ell_div,
            w_x - rho_r,
            w_x0 - rho_r0,
            w_x_div - rho_r_div,
        )
        base = w_x - rho_r
        base0 = w_x0 - rho_r0
        base_div = w_x_div - rho_r_div
        total -= a_ell_div * log_abs(ratio0)
        total -= a_ell * log_abs_ratio_divided(ratio, ratio0, ratio_div)
        total -= sum_residue_div * log_abs(base0)
        total -= sum_residue * log_abs_ratio_divided(base, base0, base_div)

    # The -1/z normalization poles at z=0 have constant residue -1.
    for rho, rho0, rho_div in preimage_pair_divided(zero, zero, zero):
        total += log_abs_ratio_divided(w_x - rho, w_x0 - rho0, w_x_div - rho_div)

    # The coordinate pole at w=0 has residue 2.
    total -= 2 * log_abs_ratio_divided(w_x, w_x0, w_x_div)

    # Endpoint atom at z=1 is absent at eta=0; keep the two endpoint sheets
    # paired before dividing by eta.
    one_derivative = (one - ell) * (one - r)
    sqrt_one_minus_alpha = (one - alpha).sqrt()
    rho_minus = (sqrt_one_minus_alpha - eta) / (sqrt_one_minus_alpha + eta)
    rho_plus = (sqrt_one_minus_alpha + eta) / (sqrt_one_minus_alpha - eta)
    for rho in (rho_minus, rho_plus):
        a = (one + A) * branch_value(rho, scale) / one_derivative
        total -= (a / eta) * log_abs(w_x - rho)

    return str(total)


def _rescaled_residue_log_divided_values_from_arb(
    A,
    alpha,
    eta,
    left_weight,
    limit_A,
    limit_alpha,
    precision: int,
    base_delta_A=None,
    base_delta_alpha=None,
) -> tuple[str, str]:
    """Return first-order divided K1 and provisional K2 boxes."""

    from flint import arb

    U_alpha_div = arb(
        _potential_residue_log_value_divided_from_arb(
            A,
            alpha,
            eta,
            limit_A,
            limit_alpha,
            "contact",
            precision,
            base_delta_A,
            base_delta_alpha,
        )
    )
    K2 = _combined_residue_log_value_second_divided_from_arb(
        A,
        alpha,
        eta,
        left_weight,
        limit_A,
        limit_alpha,
        precision,
        base_delta_A,
        base_delta_alpha,
    )
    return str(U_alpha_div), K2


def _combined_residue_log_value_second_divided_from_arb(
    A,
    alpha,
    eta,
    left_weight,
    limit_A,
    limit_alpha,
    precision: int,
    base_delta_A=None,
    base_delta_alpha=None,
) -> str:
    """Term-paired box for ``(left_weight*U(alpha)+U(-1))/eta^2``.

    This is the second cancellation layer for the value kernel: the contact
    and minus-one first divided contributions are combined term-by-term before
    the final division by eta.
    """

    from flint import arb, ctx

    ctx.prec = precision
    one = arb(1)
    zero = arb(0)
    epsilon = eta * eta
    ell = arb(repr(X_LEFT)) + epsilon
    ell0 = arb(repr(X_LEFT))
    r = arb(repr(X_RIGHT))
    beta = one - epsilon
    beta0 = one
    center = (alpha + beta) / 2
    scale = (beta - alpha) / 4
    center0 = (limit_alpha + beta0) / 2
    scale0 = (beta0 - limit_alpha) / 4
    tau = base_delta_alpha if base_delta_alpha is not None else (alpha - limit_alpha) / eta
    A_div = base_delta_A if base_delta_A is not None else (A - limit_A) / eta
    center_div = (tau - eta) / 2
    scale_div = -(tau + eta) / 4

    def log_abs(value):
        return abs(value).log()

    def log_one_plus_over_z(z):
        radius = float(abs(z).upper())
        if radius >= 0.25:
            return abs(one + z).log() / z
        total = arb(0)
        power = arb(1)
        terms = 48
        for index in range(terms):
            if index:
                power *= z
            term = power / arb(index + 1)
            total += -term if index % 2 else term
        tail = radius**terms / ((terms + 1) * (1.0 - radius))
        return total + arb(f"[+/- {tail!r}]")

    def log_abs_ratio_divided(value, value0, value_div):
        z = eta * value_div / value0
        if float(abs(z).upper()) < 0.25 and float((one + z).lower()) > 0.0:
            return value_div / value0 * log_one_plus_over_z(z)
        return log_abs(value / value0) / eta

    def preimage_pair_divided(q, q0, q_div):
        y = (q - center) / scale
        y0 = (q0 - center0) / scale0
        root = (y * y - 4).sqrt()
        outer = (y - root) / 2
        root0 = (y0 * y0 - 4).sqrt()
        outer0 = (y0 - root0) / 2
        inner = 1 / outer
        inner0 = 1 / outer0
        outer_div = (q_div - center_div - scale_div * (outer0 + 1 / outer0)) / (
            scale * (1 - 1 / (outer * outer0))
        )
        inner_div = (q_div - center_div - scale_div * (inner0 + 1 / inner0)) / (
            scale * (1 - 1 / (inner * inner0))
        )
        return ((outer, outer0, outer_div), (inner, inner0, inner_div))

    def branch_value(rho, q_scale):
        return q_scale * (rho - 1 / rho)

    def branch_value_divided(rho, rho0, rho_div):
        inverse_div = -rho_div / (rho * rho0)
        return scale_div * (rho0 - 1 / rho0) + scale * (rho_div - inverse_div)

    def quotient_divided(numerator, numerator0, numerator_div, denominator, denominator0, denominator_div):
        return (numerator_div * denominator0 - numerator0 * denominator_div) / (denominator * denominator0)

    def residue(q, q_derivative, rho, q_A, q_scale):
        return (q + q_A) * branch_value(rho, q_scale) / q_derivative

    def residue_divided(q, q0, q_div, q_derivative, q0_derivative, q_derivative_div, rho, rho0, rho_div):
        numerator = (q + A) * branch_value(rho, scale)
        numerator0 = (q0 + limit_A) * branch_value(rho0, scale0)
        numerator_div = (q_div + A_div) * branch_value(rho0, scale0) + (q + A) * branch_value_divided(rho, rho0, rho_div)
        return quotient_divided(numerator, numerator0, numerator_div, q_derivative, q0_derivative, q_derivative_div)

    contact = {
        "weight": left_weight,
        "x": alpha,
        "x0": limit_alpha,
        "x_div": tau,
        "w": -one,
        "w0": -one,
        "w_div": zero,
    }
    w_minus, w_minus0, w_minus_div = preimage_pair_divided(-one, -one, zero)[0]
    minus_one = {
        "weight": one,
        "x": -one,
        "x0": -one,
        "x_div": zero,
        "w": w_minus,
        "w0": w_minus0,
        "w_div": w_minus_div,
    }
    contexts = (contact, minus_one)

    combined_first_divided = arb(0)
    for item in contexts:
        combined_first_divided -= item["weight"] * log_abs_ratio_divided(item["x"], item["x0"], item["x_div"])

    ell_derivative = (ell - r) * (ell - one)
    ell0_derivative = (ell0 - r) * (ell0 - one)
    r_derivative = (r - ell) * (r - one)
    r0_derivative = (r - ell0) * (r - one)
    ell_q_div = eta
    r_q_div = zero
    ell_derivative_div = eta * (ell0 - one) + eta * (ell - r)
    r_derivative_div = -eta * (r - one)

    ell_preimages = preimage_pair_divided(ell, ell0, ell_q_div)
    r_preimages = preimage_pair_divided(r, r, r_q_div)
    for (rho_ell, rho_ell0, rho_ell_div), (rho_r, rho_r0, rho_r_div) in zip(ell_preimages, r_preimages):
        a_ell = residue(ell, ell_derivative, rho_ell, A, scale)
        a_r = residue(r, r_derivative, rho_r, A, scale)
        a_ell_div = residue_divided(
            ell,
            ell0,
            ell_q_div,
            ell_derivative,
            ell0_derivative,
            ell_derivative_div,
            rho_ell,
            rho_ell0,
            rho_ell_div,
        )
        a_r_div = residue_divided(
            r,
            r,
            r_q_div,
            r_derivative,
            r0_derivative,
            r_derivative_div,
            rho_r,
            rho_r0,
            rho_r_div,
        )
        sum_residue = a_ell + a_r
        sum_residue_div = a_ell_div + a_r_div
        for item in contexts:
            ratio = (item["w"] - rho_ell) / (item["w"] - rho_r)
            ratio0 = (item["w0"] - rho_ell0) / (item["w0"] - rho_r0)
            ratio_div = quotient_divided(
                item["w"] - rho_ell,
                item["w0"] - rho_ell0,
                item["w_div"] - rho_ell_div,
                item["w"] - rho_r,
                item["w0"] - rho_r0,
                item["w_div"] - rho_r_div,
            )
            base = item["w"] - rho_r
            base0 = item["w0"] - rho_r0
            base_div = item["w_div"] - rho_r_div
            item_term = (
                -a_ell_div * log_abs(ratio0)
                - a_ell * log_abs_ratio_divided(ratio, ratio0, ratio_div)
                - sum_residue_div * log_abs(base0)
                - sum_residue * log_abs_ratio_divided(base, base0, base_div)
            )
            combined_first_divided += item["weight"] * item_term

    for rho, rho0, rho_div in preimage_pair_divided(zero, zero, zero):
        for item in contexts:
            combined_first_divided += item["weight"] * log_abs_ratio_divided(
                item["w"] - rho,
                item["w0"] - rho0,
                item["w_div"] - rho_div,
            )

    for item in contexts:
        combined_first_divided -= 2 * item["weight"] * log_abs_ratio_divided(item["w"], item["w0"], item["w_div"])

    one_derivative = (one - ell) * (one - r)
    sqrt_one_minus_alpha = (one - alpha).sqrt()
    rho_minus = (sqrt_one_minus_alpha - eta) / (sqrt_one_minus_alpha + eta)
    rho_plus = (sqrt_one_minus_alpha + eta) / (sqrt_one_minus_alpha - eta)
    for rho in (rho_minus, rho_plus):
        a = (one + A) * branch_value(rho, scale) / one_derivative
        for item in contexts:
            combined_first_divided -= item["weight"] * (a / eta) * log_abs(item["w"] - rho)

    return str(combined_first_divided / eta)


def contact_derivative_box_acb(
    A_low: float,
    A_high: float,
    alpha_low: float,
    alpha_high: float,
    epsilon: float,
    direction_A: float,
    direction_alpha: float,
    precision: int = 192,
) -> str:
    """Arb/Acb box enclosure for a contact directional derivative of ``U(alpha)``."""

    from flint import arb

    return _contact_directional_derivative_acb_from_arb(
        _arb_interval_from_bounds(A_low, A_high),
        _arb_interval_from_bounds(alpha_low, alpha_high),
        arb(repr(float(epsilon))),
        arb(repr(float(direction_A))),
        arb(repr(float(direction_alpha))),
        precision,
    )


def atom_derivatives(A: float, alpha: float, epsilon: float) -> dict[str, dict[str, float]]:
    ell, r, beta, mass_ell, mass_r, mass_1 = atoms(A, alpha, epsilon)

    def dlog_R_left(t: float) -> float:
        return 0.5 / (alpha - t)

    derivatives: dict[str, dict[str, float]] = {}
    derivatives["ell"] = {
        "mass": mass_ell,
        "q": ell,
        "dA": mass_ell / (ell + A),
        "dalpha": mass_ell * dlog_R_left(ell),
    }
    derivatives["r"] = {
        "mass": mass_r,
        "q": r,
        "dA": mass_r / (r + A),
        "dalpha": mass_r * dlog_R_left(r),
    }
    derivatives["one"] = {
        "mass": mass_1,
        "q": 1.0,
        "dA": mass_1 / (1.0 + A),
        "dalpha": -0.5 * mass_1 / (1.0 - alpha),
    }
    return derivatives


def continuous_derivative_fixed_x(
    x: float,
    A: float,
    alpha: float,
    epsilon: float,
    direction_A: float,
    direction_alpha: float,
) -> float:
    ell = X_LEFT + epsilon
    r = X_RIGHT
    beta = 1.0 - epsilon
    c = (alpha + beta) / 2.0
    half = (beta - alpha) / 2.0

    def integrand(theta: float) -> float:
        sin_theta = math.sin(theta)
        cos_theta = math.cos(theta)
        t = c + half * cos_theta
        D = (t - ell) * (t - r) * (t - 1.0)
        Dprime = (t - r) * (t - 1.0) + (t - ell) * (t - 1.0) + (t - ell) * (t - r)
        t_alpha = (1.0 - cos_theta) / 2.0
        H = -(half * half * sin_theta * sin_theta / math.pi) * (t + A) / D
        H_A = -(half * half * sin_theta * sin_theta / math.pi) / D
        H_alpha = (sin_theta * sin_theta / math.pi) * (
            half * (t + A) / D
            - half * half * t_alpha * (D - (t + A) * Dprime) / (D * D)
        )
        H_s = direction_A * H_A + direction_alpha * H_alpha
        t_s = direction_alpha * t_alpha
        return H_s * math.log(1.0 / abs(x - t)) + H * t_s / (x - t)

    return quad(integrand, 0.0, math.pi, epsabs=1e-10, epsrel=1e-10, limit=200)[0]


def continuous_derivative_contact(
    A: float,
    alpha: float,
    epsilon: float,
    direction_A: float,
    direction_alpha: float,
) -> float:
    ell = X_LEFT + epsilon
    r = X_RIGHT
    beta = 1.0 - epsilon
    c = (alpha + beta) / 2.0
    half = (beta - alpha) / 2.0

    def integrand(theta: float) -> float:
        sin_theta = math.sin(theta)
        cos_theta = math.cos(theta)
        t = c + half * cos_theta
        D = (t - ell) * (t - r) * (t - 1.0)
        Dprime = (t - r) * (t - 1.0) + (t - ell) * (t - 1.0) + (t - ell) * (t - r)
        t_alpha = (1.0 - cos_theta) / 2.0
        H = -(half * half * sin_theta * sin_theta / math.pi) * (t + A) / D
        H_A = -(half * half * sin_theta * sin_theta / math.pi) / D
        H_alpha = (sin_theta * sin_theta / math.pi) * (
            half * (t + A) / D
            - half * half * t_alpha * (D - (t + A) * Dprime) / (D * D)
        )
        H_s = direction_A * H_A + direction_alpha * H_alpha
        if abs(theta - math.pi) < 1e-8:
            log_contact = -math.log(2.0 * half) - 2.0 * math.log(max(abs(math.cos(theta / 2.0)), 1e-300))
        else:
            log_contact = math.log(1.0 / abs(alpha - t))
        return H_s * log_contact + (direction_alpha / (2.0 * half)) * H

    return quad(integrand, 0.0, math.pi, epsabs=1e-10, epsrel=1e-10, limit=200)[0]


def analytic_G_derivative(
    A: float,
    alpha: float,
    epsilon: float,
    direction_A: float,
    direction_alpha: float,
) -> np.ndarray:
    atom_data = atom_derivatives(A, alpha, epsilon)
    dU_alpha = 0.0
    dU_minus_one = 0.0
    for data in atom_data.values():
        mass = data["mass"]
        q = data["q"]
        mass_s = direction_A * data["dA"] + direction_alpha * data["dalpha"]
        dU_alpha += mass_s * math.log(1.0 / abs(alpha - q)) - mass * direction_alpha / (alpha - q)
        dU_minus_one += mass_s * math.log(1.0 / abs(-1.0 - q))
    dU_alpha += continuous_derivative_contact(A, alpha, epsilon, direction_A, direction_alpha)
    dU_minus_one += continuous_derivative_fixed_x(-1.0, A, alpha, epsilon, direction_A, direction_alpha)
    return np.array([dU_alpha, dU_minus_one])


def equations(z: np.ndarray, epsilon: float) -> list[float]:
    A, alpha = float(z[0]), float(z[1])
    try:
        return [
            potential(alpha, A, alpha, epsilon),
            potential(-1.0, A, alpha, epsilon),
        ]
    except (ValueError, ZeroDivisionError, OverflowError):
        return [1.0e3, 1.0e3]


def limit_equations(z: np.ndarray) -> list[float]:
    A, alpha = float(z[0]), float(z[1])
    try:
        return [
            limit_potential(alpha, A, alpha),
            limit_potential(-1.0, A, alpha),
        ]
    except (ValueError, ZeroDivisionError, OverflowError):
        return [1.0e3, 1.0e3]


def sample_minimum(A: float, alpha: float, epsilon: float) -> float:
    ell, r, beta, *_ = atoms(A, alpha, epsilon)
    points: list[float] = []
    points.extend(np.linspace(-1.0, r - 1e-5, 80))
    points.extend(np.linspace(r + 1e-5, alpha - 1e-5, 80))
    if beta + 1e-5 < 1.0 - 1e-5:
        points.extend(np.linspace(beta + 1e-5, 1.0 - 1e-5, 30))
    values = [potential(float(x), A, alpha, epsilon) for x in points]
    return min(values) if values else float("nan")


def finite_difference_jacobian_det(A: float, alpha: float, epsilon: float, h: float = 3.0e-6) -> float:
    plus_A = equations(np.array([A + h, alpha]), epsilon)
    minus_A = equations(np.array([A - h, alpha]), epsilon)
    plus_alpha = equations(np.array([A, alpha + h]), epsilon)
    minus_alpha = equations(np.array([A, alpha - h]), epsilon)
    dA = [(plus_A[i] - minus_A[i]) / (2.0 * h) for i in range(2)]
    dAlpha = [(plus_alpha[i] - minus_alpha[i]) / (2.0 * h) for i in range(2)]
    return dA[0] * dAlpha[1] - dAlpha[0] * dA[1]


def limit_jacobian(h: float = 3.0e-5) -> np.ndarray:
    limit_solution = solve_limit()
    A = limit_solution.A
    alpha = limit_solution.alpha
    plus_A = limit_equations(np.array([A + h, alpha]))
    minus_A = limit_equations(np.array([A - h, alpha]))
    plus_alpha = limit_equations(np.array([A, alpha + h]))
    minus_alpha = limit_equations(np.array([A, alpha - h]))
    dA = [(plus_A[i] - minus_A[i]) / (2.0 * h) for i in range(2)]
    dAlpha = [(plus_alpha[i] - minus_alpha[i]) / (2.0 * h) for i in range(2)]
    return np.array([[dA[0], dAlpha[0]], [dA[1], dAlpha[1]]])


def fold_diagnostics() -> tuple[float, float, list[tuple[float, float]], float, float, float]:
    limit_solution = solve_limit()
    A0 = limit_solution.A
    alpha0 = limit_solution.alpha
    jacobian = limit_jacobian()
    left_weight = -jacobian[1, 0] / jacobian[0, 0]
    null_slope = -jacobian[0, 1] / jacobian[0, 0]
    left_null = np.array([left_weight, 1.0])
    null_vector = np.array([null_slope, 1.0])

    projected_forcing_ratios = []
    for eps_probe in [1.0e-3, 1.0e-4, 1.0e-5]:
        ratio = float(left_null @ np.array(equations(np.array([A0, alpha0]), eps_probe)) / eps_probe)
        projected_forcing_ratios.append((eps_probe, ratio))

    h = 2.0e-4
    base = np.array(limit_equations(np.array([A0, alpha0])))
    plus = np.array(limit_equations(np.array([A0 + h * null_slope, alpha0 + h])))
    minus = np.array(limit_equations(np.array([A0 - h * null_slope, alpha0 - h])))
    second = (plus - 2.0 * base + minus) / (h * h)
    curvature = 0.5 * float(left_null @ second)
    projected_forcing = projected_forcing_ratios[-1][1]
    amplitude_squared = -projected_forcing / curvature
    if curvature == 0.0 or amplitude_squared <= 0.0:
        raise RuntimeError(
            "fold diagnostics did not predict a real positive branch: "
            f"projected_forcing={projected_forcing}, curvature={curvature}"
        )
    amplitude_alpha = math.sqrt(amplitude_squared)
    amplitude_A = null_slope * amplitude_alpha
    return left_weight, null_slope, projected_forcing_ratios, curvature, amplitude_alpha, amplitude_A


def rescaled_system(
    B: float,
    tau: float,
    eta: float,
    limit_solution: LimitSolution,
    left_weight: float,
    null_slope: float,
) -> tuple[float, float]:
    epsilon = eta * eta
    A = limit_solution.A + eta * (null_slope * tau + B)
    alpha = limit_solution.alpha + eta * tau
    G = equations(np.array([A, alpha]), epsilon)
    return G[0] / eta, (left_weight * G[0] + G[1]) / (eta * eta)


def rescaled_jacobian(
    B: float,
    tau: float,
    eta: float,
    limit_solution: LimitSolution,
    left_weight: float,
    null_slope: float,
    h: float = 1.0e-4,
) -> np.ndarray:
    plus_B = rescaled_system(B + h, tau, eta, limit_solution, left_weight, null_slope)
    minus_B = rescaled_system(B - h, tau, eta, limit_solution, left_weight, null_slope)
    plus_tau = rescaled_system(B, tau + h, eta, limit_solution, left_weight, null_slope)
    minus_tau = rescaled_system(B, tau - h, eta, limit_solution, left_weight, null_slope)
    dB = [(plus_B[i] - minus_B[i]) / (2.0 * h) for i in range(2)]
    dTau = [(plus_tau[i] - minus_tau[i]) / (2.0 * h) for i in range(2)]
    return np.array([[dB[0], dTau[0]], [dB[1], dTau[1]]])


def rescaled_jacobian_det(
    B: float,
    tau: float,
    eta: float,
    limit_solution: LimitSolution,
    left_weight: float,
    null_slope: float,
    h: float = 1.0e-4,
) -> float:
    jacobian = rescaled_jacobian(B, tau, eta, limit_solution, left_weight, null_slope, h=h)
    dB = jacobian[:, 0]
    dTau = jacobian[:, 1]
    return dB[0] * dTau[1] - dTau[0] * dB[1]


def analytic_rescaled_jacobian(
    B: float,
    tau: float,
    eta: float,
    limit_solution: LimitSolution,
    left_weight: float,
    null_slope: float,
) -> np.ndarray:
    epsilon = eta * eta
    A = limit_solution.A + eta * (null_slope * tau + B)
    alpha = limit_solution.alpha + eta * tau
    dG_B = analytic_G_derivative(A, alpha, epsilon, eta, 0.0)
    dG_tau = analytic_G_derivative(A, alpha, epsilon, eta * null_slope, eta)
    columns = []
    for dG in [dG_B, dG_tau]:
        columns.append([dG[0] / eta, (left_weight * dG[0] + dG[1]) / (eta * eta)])
    return np.array([[columns[0][0], columns[1][0]], [columns[0][1], columns[1][1]]])


def krawczyk_diagnostic(
    B: float,
    tau: float,
    eta: float,
    limit_solution: LimitSolution,
    left_weight: float,
    null_slope: float,
    radius_B: float = KRAWCZYK_RADIUS_B,
    radius_tau: float = KRAWCZYK_RADIUS_TAU,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, float]:
    center_value = np.array(rescaled_system(B, tau, eta, limit_solution, left_weight, null_slope))
    center_jacobian = analytic_rescaled_jacobian(B, tau, eta, limit_solution, left_weight, null_slope)
    inverse = np.linalg.inv(center_jacobian)
    correction = np.abs(inverse @ center_value)
    radii = np.array([radius_B, radius_tau])
    sampled_linear = np.zeros(2)
    stencil_h = 1.0e-4
    sample_B_values = [-radius_B - stencil_h, -radius_B, 0.0, radius_B, radius_B + stencil_h]
    sample_tau_values = [-radius_tau - stencil_h, -radius_tau, 0.0, radius_tau, radius_tau + stencil_h]
    for delta_B in sample_B_values:
        for delta_tau in sample_tau_values:
            jacobian = analytic_rescaled_jacobian(
                B + delta_B,
                tau + delta_tau,
                eta,
                limit_solution,
                left_weight,
                null_slope,
            )
            defect = np.eye(2) - inverse @ jacobian
            sampled_linear = np.maximum(sampled_linear, np.abs(defect) @ radii)
    inclusion = correction + sampled_linear
    margin = radii - inclusion
    contraction = float(max(sampled_linear / radii))
    return correction, inclusion, margin, contraction


def parameter_box_margins(
    epsilon: float,
    A_low: float,
    A_high: float,
    alpha_low: float,
    alpha_high: float,
) -> dict[str, float]:
    ell = X_LEFT + epsilon
    beta = 1.0 - epsilon
    return {
        "A>1": A_low - 1.0,
        "A<-ell": -ell - A_high,
        "ell<-1": -1.0 - ell,
        "r<alpha": alpha_low - X_RIGHT,
        "alpha<beta": beta - alpha_high,
        "beta<1": 1.0 - beta,
    }


def solve_one(epsilon: float, guess: tuple[float, float]) -> tuple[AnsatzSolution, tuple[float, float]]:
    sol = root(lambda z: equations(z, epsilon), np.array(guess), method="hybr", options={"xtol": 1e-10, "maxfev": 500})
    if not sol.success:
        raise RuntimeError(f"epsilon={epsilon}: root solver failed: {sol.message}")

    A, alpha = float(sol.x[0]), float(sol.x[1])
    ell, r, beta, mass_ell, mass_r, mass_1 = atoms(A, alpha, epsilon)
    residual_alpha, residual_minus_one = equations(sol.x, epsilon)
    density_mass = continuous_mass(A, alpha, epsilon)
    valid_sign_chart = (
        1.0 < A < -ell
        and ell < -1.0 < r < alpha < beta < 1.0
        and mass_ell > 0.0
        and mass_r > 0.0
        and mass_1 > 0.0
        and density_mass > 0.0
        and abs(residual_alpha) < RESIDUAL_TOLERANCE
        and abs(residual_minus_one) < RESIDUAL_TOLERANCE
        and abs((mass_ell + mass_r + mass_1 + density_mass) - 1.0) < TOTAL_MASS_TOLERANCE
    )
    result = AnsatzSolution(
        epsilon=epsilon,
        A=A,
        alpha=alpha,
        ell=ell,
        r=r,
        beta=beta,
        mass_ell=mass_ell,
        mass_r=mass_r,
        mass_1=mass_1,
        density_mass=density_mass,
        residual_alpha=residual_alpha,
        residual_minus_one=residual_minus_one,
        valid_sign_chart=valid_sign_chart,
        sample_min=sample_minimum(A, alpha, epsilon),
    )
    return result, (A, alpha)


def solve_limit(guess: tuple[float, float] = (1.18, 0.804)) -> LimitSolution:
    sol = root(lambda z: limit_equations(z), np.array(guess), method="hybr", options={"xtol": 1e-12, "maxfev": 500})
    A, alpha = float(sol.x[0]), float(sol.x[1])
    residual_alpha, residual_minus_one = limit_equations(sol.x)
    if not sol.success and max(abs(residual_alpha), abs(residual_minus_one)) >= RESIDUAL_TOLERANCE:
        raise RuntimeError(f"limit solve failed: {sol.message}")
    mass_ell, mass_r = limit_atoms(A, alpha)
    density_mass = limit_continuous_mass(A, alpha)
    if (
        not (1.0 < A < -X_LEFT and X_RIGHT < alpha < 1.0)
        or mass_ell <= 0.0
        or mass_r <= 0.0
        or density_mass <= 0.0
        or abs(residual_alpha) >= RESIDUAL_TOLERANCE
        or abs(residual_minus_one) >= RESIDUAL_TOLERANCE
        or abs((mass_ell + mass_r + density_mass) - 1.0) >= TOTAL_MASS_TOLERANCE
    ):
        raise RuntimeError("limit solution failed sign, residual, or mass checks")
    return LimitSolution(
        A=A,
        alpha=alpha,
        mass_ell=mass_ell,
        mass_r=mass_r,
        density_mass=density_mass,
        residual_alpha=residual_alpha,
        residual_minus_one=residual_minus_one,
    )


def default_epsilons() -> list[float]:
    return [0.02, 0.01, 0.005, 0.002, 0.001, 0.0005]


def parse_epsilons(raw: str | None) -> list[float]:
    if not raw:
        return default_epsilons()
    return [float(part) for part in raw.split(",") if part.strip()]


def print_solution(solution: AnsatzSolution) -> None:
    print(f"epsilon = {solution.epsilon:g}")
    print(
        "  A alpha ell r beta = "
        f"{solution.A:.12f} {solution.alpha:.12f} {solution.ell:.12f} "
        f"{solution.r:.12f} {solution.beta:.12f}"
    )
    print(
        "  masses ell r 1 density total = "
        f"{solution.mass_ell:.12f} {solution.mass_r:.12f} "
        f"{solution.mass_1:.12f} {solution.density_mass:.12f} "
        f"{solution.total_mass:.12f}"
    )
    print(
        "  residuals U(alpha), U(-1) = "
        f"{solution.residual_alpha:.3e} {solution.residual_minus_one:.3e}"
    )
    print(f"  sign_chart_valid = {solution.valid_sign_chart}")
    print(f"  sampled_min = {solution.sample_min:.3e}")
    print(
        "  finite-difference det DG = "
        f"{finite_difference_jacobian_det(solution.A, solution.alpha, solution.epsilon):.6e}"
    )


def print_limit_solution(solution: LimitSolution) -> None:
    print("epsilon = 0 limiting system")
    print(f"  A alpha = {solution.A:.12f} {solution.alpha:.12f}")
    print(
        "  masses ell r density total = "
        f"{solution.mass_ell:.12f} {solution.mass_r:.12f} "
        f"{solution.density_mass:.12f} {solution.total_mass:.12f}"
    )
    print(
        "  residuals U(alpha), U(-1) = "
        f"{solution.residual_alpha:.3e} {solution.residual_minus_one:.3e}"
    )
    _left_weight, null_slope, forcing_ratios, curvature, amplitude_alpha, amplitude_A = fold_diagnostics()
    print(
        "  fold diagnostics dA/dalpha, curvature, alpha-amplitude, A-amplitude = "
        f"{null_slope:.12f} {curvature:.12f} {amplitude_alpha:.12f} {amplitude_A:.12f}"
    )
    print(
        "  projected forcing ratios wG/eps at eps=1e-3,1e-4,1e-5 = "
        + " ".join(f"{ratio:.12f}" for _eps, ratio in forcing_ratios)
    )


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--epsilons", help="comma-separated epsilon values")
    parser.add_argument("--write-json", help="write diagnostic certificate skeleton to this path")
    parser.add_argument("--primitive-check", action="store_true", help="run slow high-precision residue-log primitive check")
    parser.add_argument("--arb-primitive-check", action="store_true", help="run Arb ball residue-log primitive check")
    args = parser.parse_args(list(argv) if argv is not None else None)

    limit_solution = solve_limit()
    print_limit_solution(limit_solution)
    left_weight, null_slope, _forcing_ratios, _curvature, amplitude_alpha, amplitude_A = fold_diagnostics()
    certificate_rows = []

    guess = (1.38, 0.91)
    ok = True
    for epsilon in parse_epsilons(args.epsilons):
        solution, guess = solve_one(epsilon, guess)
        print_solution(solution)
        eta = math.sqrt(epsilon)
        print(
            "  scaled deltas (A-A0)/sqrt(eps), (alpha-alpha0)/sqrt(eps) = "
            f"{(solution.A - limit_solution.A) / eta:.12f} "
            f"{(solution.alpha - limit_solution.alpha) / eta:.12f}"
        )
        predicted_A = limit_solution.A + amplitude_A * eta
        predicted_alpha = limit_solution.alpha + amplitude_alpha * eta
        normalized_A_error = (solution.A - predicted_A) / epsilon
        normalized_alpha_error = (solution.alpha - predicted_alpha) / epsilon
        print(
            "  LS prediction errors (A-Apred)/eps, (alpha-alphapred)/eps = "
            f"{normalized_A_error:.12f} "
            f"{normalized_alpha_error:.12f}"
        )
        print(
            "  diagnostic branch box |A-Apred|<=6eps, |alpha-alphapred|<=4eps = "
            f"{abs(normalized_A_error) <= BRANCH_BOX_A_RADIUS and abs(normalized_alpha_error) <= BRANCH_BOX_ALPHA_RADIUS}"
        )
        print(
            "  diagnostic branch box intervals A, alpha = "
            f"[{predicted_A - BRANCH_BOX_A_RADIUS * epsilon:.12f}, "
            f"{predicted_A + BRANCH_BOX_A_RADIUS * epsilon:.12f}] "
            f"[{predicted_alpha - BRANCH_BOX_ALPHA_RADIUS * epsilon:.12f}, "
            f"{predicted_alpha + BRANCH_BOX_ALPHA_RADIUS * epsilon:.12f}]"
        )
        branch_margins = parameter_box_margins(
            epsilon,
            predicted_A - BRANCH_BOX_A_RADIUS * epsilon,
            predicted_A + BRANCH_BOX_A_RADIUS * epsilon,
            predicted_alpha - BRANCH_BOX_ALPHA_RADIUS * epsilon,
            predicted_alpha + BRANCH_BOX_ALPHA_RADIUS * epsilon,
        )
        print(
            "  branch-box sign margins min, A>1, A<-ell, r<alpha, alpha<beta = "
            f"{min(branch_margins.values()):.6e} "
            f"{branch_margins['A>1']:.6e} {branch_margins['A<-ell']:.6e} "
            f"{branch_margins['r<alpha']:.6e} {branch_margins['alpha<beta']:.6e}"
        )
        tau = (solution.alpha - limit_solution.alpha) / eta
        B = (solution.A - limit_solution.A) / eta - null_slope * tau
        K1, K2 = rescaled_system(B, tau, eta, limit_solution, left_weight, null_slope)
        jacobian_K = rescaled_jacobian(B, tau, eta, limit_solution, left_weight, null_slope)
        det_K_h1 = rescaled_jacobian_det(B, tau, eta, limit_solution, left_weight, null_slope, h=1.0e-4)
        det_K_h2 = rescaled_jacobian_det(B, tau, eta, limit_solution, left_weight, null_slope, h=5.0e-5)
        print(
            "  LS variables B, tau; rescaled K residuals; det DK = "
            f"{B:.12f} {tau:.12f}; {K1:.3e} {K2:.3e}; "
            f"{det_K_h1:.6e}"
        )
        print(
            "  DK rows = "
            f"[{jacobian_K[0, 0]:.9f}, {jacobian_K[0, 1]:.9f}] "
            f"[{jacobian_K[1, 0]:.9f}, {jacobian_K[1, 1]:.9f}]; "
            f"det sensitivity h=1e-4,5e-5 = {det_K_h1:.6e} {det_K_h2:.6e}"
        )
        analytic_jacobian_K = analytic_rescaled_jacobian(
            B, tau, eta, limit_solution, left_weight, null_slope
        )
        analytic_det_K = float(np.linalg.det(analytic_jacobian_K))
        print(
            "  analytic DK rows; det; max|analytic-fd| = "
            f"[{analytic_jacobian_K[0, 0]:.9f}, {analytic_jacobian_K[0, 1]:.9f}] "
            f"[{analytic_jacobian_K[1, 0]:.9f}, {analytic_jacobian_K[1, 1]:.9f}]; "
            f"{analytic_det_K:.6e}; {np.max(np.abs(analytic_jacobian_K - jacobian_K)):.3e}"
        )
        diff_by_F = potential_difference_by_F(solution.A, solution.alpha, solution.epsilon)
        diff_direct = solution.residual_minus_one - solution.residual_alpha
        print(
            "  U(-1)-U(alpha): direct, F-cont integral, abs diff = "
            f"{diff_direct:.3e} {diff_by_F:.3e} {abs(diff_direct - diff_by_F):.3e}"
        )
        primitive_check = None
        if args.primitive_check:
            atom_difference = (
                solution.mass_ell
                * (math.log(1.0 / abs(-1.0 - solution.ell)) - math.log(1.0 / abs(solution.alpha - solution.ell)))
                + solution.mass_r
                * (math.log(1.0 / abs(-1.0 - solution.r)) - math.log(1.0 / abs(solution.alpha - solution.r)))
                + solution.mass_1
                * (math.log(1.0 / abs(-2.0)) - math.log(1.0 / abs(solution.alpha - 1.0)))
            )
            primitive_real, primitive_imag = continuous_difference_by_w_residues(
                solution.A, solution.alpha, solution.epsilon
            )
            continuous_by_quad = diff_by_F - atom_difference
            primitive_check = {
                "continuous_quad": continuous_by_quad,
                "primitive_real": primitive_real,
                "primitive_imag": primitive_imag,
                "abs_real_difference": abs(continuous_by_quad - primitive_real),
            }
            print(
                "  residue-log primitive continuous diff, imag, abs diff vs quad = "
                f"{primitive_real:.15e} {primitive_imag:.3e} {abs(continuous_by_quad - primitive_real):.3e}"
            )
        if args.arb_primitive_check:
            if primitive_check is None:
                atom_difference = (
                    solution.mass_ell
                    * (
                        math.log(1.0 / abs(-1.0 - solution.ell))
                        - math.log(1.0 / abs(solution.alpha - solution.ell))
                    )
                    + solution.mass_r
                    * (
                        math.log(1.0 / abs(-1.0 - solution.r))
                        - math.log(1.0 / abs(solution.alpha - solution.r))
                    )
                    + solution.mass_1
                    * (math.log(1.0 / abs(-2.0)) - math.log(1.0 / abs(solution.alpha - 1.0)))
                )
                continuous_by_quad = diff_by_F - atom_difference
            (
                arb_real,
                arb_imag,
                arb_full_difference,
                arb_full_contains_zero,
                path_separation,
                pole_count,
            ) = continuous_difference_by_w_residues_acb(
                solution.A, solution.alpha, solution.epsilon
            )
            if primitive_check is None:
                primitive_check = {}
            primitive_check["arb_real_ball"] = arb_real
            primitive_check["arb_imag_ball"] = arb_imag
            primitive_check["arb_full_difference_ball"] = arb_full_difference
            primitive_check["arb_full_difference_contains_zero"] = arb_full_contains_zero
            primitive_check["path_separation_diagnostic"] = path_separation
            primitive_check["pole_count_after_path_cancellation"] = pole_count
            primitive_check["continuous_quad"] = continuous_by_quad
            print(
                "  Arb residue-log primitive continuous diff real ball, full diff ball, path sep = "
                f"{arb_real} {arb_full_difference} {path_separation:.6e}"
            )
        correction, inclusion, margin, contraction = krawczyk_diagnostic(
            B, tau, eta, limit_solution, left_weight, null_slope
        )
        A_values = [
            limit_solution.A
            + eta * (null_slope * (tau + delta_tau) + (B + delta_B))
            for delta_B in [-KRAWCZYK_RADIUS_B, KRAWCZYK_RADIUS_B]
            for delta_tau in [-KRAWCZYK_RADIUS_TAU, KRAWCZYK_RADIUS_TAU]
        ]
        alpha_values = [
            limit_solution.alpha + eta * (tau + delta_tau)
            for delta_tau in [-KRAWCZYK_RADIUS_TAU, KRAWCZYK_RADIUS_TAU]
        ]
        krawczyk_margins = parameter_box_margins(
            epsilon,
            min(A_values),
            max(A_values),
            min(alpha_values),
            max(alpha_values),
        )
        print(
            "  sampled Krawczyk radii B,tau; correction; inclusion; margin; contraction = "
            f"{KRAWCZYK_RADIUS_B:.3e} {KRAWCZYK_RADIUS_TAU:.3e}; "
            f"{correction[0]:.3e} {correction[1]:.3e}; "
            f"{inclusion[0]:.3e} {inclusion[1]:.3e}; "
            f"{margin[0]:.3e} {margin[1]:.3e}; {contraction:.3e}"
        )
        print(
            "  Krawczyk-box sign margins min, A>1, A<-ell, r<alpha, alpha<beta = "
            f"{min(krawczyk_margins.values()):.6e} "
            f"{krawczyk_margins['A>1']:.6e} {krawczyk_margins['A<-ell']:.6e} "
            f"{krawczyk_margins['r<alpha']:.6e} {krawczyk_margins['alpha<beta']:.6e}"
        )
        certificate_rows.append(
            {
                "epsilon": epsilon,
                "eta": eta,
                "solution": {
                    "A": solution.A,
                    "alpha": solution.alpha,
                    "ell": solution.ell,
                    "r": solution.r,
                    "beta": solution.beta,
                    "masses": {
                        "ell": solution.mass_ell,
                        "r": solution.mass_r,
                        "one": solution.mass_1,
                        "density": solution.density_mass,
                        "total": solution.total_mass,
                    },
                    "residuals": {
                        "U_alpha": solution.residual_alpha,
                        "U_minus_one": solution.residual_minus_one,
                    },
                },
                "branch_box": {
                    "A": [predicted_A - BRANCH_BOX_A_RADIUS * epsilon, predicted_A + BRANCH_BOX_A_RADIUS * epsilon],
                    "alpha": [
                        predicted_alpha - BRANCH_BOX_ALPHA_RADIUS * epsilon,
                        predicted_alpha + BRANCH_BOX_ALPHA_RADIUS * epsilon,
                    ],
                    "sign_margins": branch_margins,
                },
                "krawczyk_box": {
                    "center": {"B": B, "tau": tau},
                    "radii": {"B": KRAWCZYK_RADIUS_B, "tau": KRAWCZYK_RADIUS_TAU},
                    "rescaled_residual": {"K1": K1, "K2": K2},
                    "potential_difference_check": {
                        "direct": diff_direct,
                        "F_cont_integral": diff_by_F,
                        "abs_difference": abs(diff_direct - diff_by_F),
                        "residue_log_primitive": primitive_check,
                    },
                    "jacobian": jacobian_K.tolist(),
                    "analytic_jacobian": analytic_jacobian_K.tolist(),
                    "analytic_jacobian_max_abs_diff_from_fd": float(np.max(np.abs(analytic_jacobian_K - jacobian_K))),
                    "determinant": det_K_h1,
                    "analytic_determinant": analytic_det_K,
                    "determinant_h_5e-5": det_K_h2,
                    "correction": correction.tolist(),
                    "sampled_inclusion": inclusion.tolist(),
                    "sampled_margin": margin.tolist(),
                    "sampled_contraction": contraction,
                    "sign_margins": krawczyk_margins,
                },
            }
        )
        ok = ok and solution.valid_sign_chart
    print(f"OVERALL SIGN-CHART STATUS: {'PASS' if ok else 'FAIL'}")
    if args.write_json:
        payload = {
            "description": "Diagnostic skeleton for the corrected two-interval finite-gap dual ansatz; sampled, not proof-grade.",
            "limit_solution": {"A": limit_solution.A, "alpha": limit_solution.alpha},
            "fold": {
                "left_weight": left_weight,
                "null_slope": null_slope,
                "alpha_amplitude": amplitude_alpha,
                "A_amplitude": amplitude_A,
            },
            "rows": certificate_rows,
        }
        with open(args.write_json, "w", encoding="utf-8") as handle:
            json.dump(payload, handle, indent=2, sort_keys=True)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
