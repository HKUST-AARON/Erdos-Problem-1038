#!/usr/bin/env python3
"""
Correct-domain verifier for the piecewise five-atom tail certificate.

Important:
For the normalized minimizer reduction used in the finite-atom route,
    supp(mu) subset {-1} union [0,1].
For a block a in [-A,-C] and y = x-a, the required positivity domains are

    x = -1       -> y in [C-1, A-1]
    x in [0,1]  -> y in [C, A+1]

The middle interval [A-1, C] corresponds to x in (-1,0), which is NOT part
of the normalized support except the single point x=-1 already handled above.

Thus scanning all y in [C-1, A+1] is a stronger, irrelevant test and can find
negative values that do not invalidate this conditional certificate.
"""

import argparse
import json
import math
import numpy as np

try:
    from scipy.optimize import brentq  # type: ignore
except Exception:  # pragma: no cover - fallback for environments without scipy
    brentq = None



def _bisection_root(f, a, b, max_iter=60):
    fa = f(a)
    fb = f(b)
    if not (math.isfinite(fa) and math.isfinite(fb)):
        return None
    if fa == 0.0:
        return a
    if fb == 0.0:
        return b
    if fa * fb > 0:
        return None
    lo, hi = a, b
    flo, fhi = fa, fb
    for _ in range(max_iter):
        mid = 0.5 * (lo + hi)
        fm = f(mid)
        if not math.isfinite(fm):
            return None
        if flo * fm <= 0:
            hi, fhi = mid, fm
        else:
            lo, flo = mid, fm
    return 0.5 * (lo + hi)



def _interval_samples(shifted_intervals, shifts):
    # include tiny offsets from poles so bisection avoids evaluating at singular points
    out = []
    for lo, hi in shifted_intervals:
        pts = [lo, hi] + [d for d in shifts if lo < d < hi]
        pts = sorted(pts)
        for a, b in zip(pts[:-1], pts[1:]):
            eps_a = 1e-10 if any(abs(a - d) < 1e-14 for d in shifts) else 0.0
            eps_b = 1e-10 if any(abs(b - d) < 1e-14 for d in shifts) else 0.0
            aa = a + eps_a
            bb = b - eps_b
            if aa < bb:
                out.append((aa, bb))
    return out



def _safe_log1_over_abs(x):
    return math.log(1.0 / abs(x))


def V_value(y, weights, shifts):
    return _safe_log1_over_abs(y) + sum(
        float(w) * math.log(1.0 / abs(y - d))
        for w, d in zip(weights, shifts)
    )


def g_derivative(y, weights, shifts):
    # This is the analytic derivative V'(y).
    return -(1.0 / y) - sum(float(w) / (y - d) for w, d in zip(weights, shifts))


def critical_points(intervals, weights, shifts):
    pts = []
    for lo, hi in intervals:
        pts.extend([lo, hi])
        for a, b in _interval_samples([(lo, hi)], shifts):
            try:
                ga = g_derivative(a, weights, shifts)
                gb = g_derivative(b, weights, shifts)
                if math.isfinite(ga) and math.isfinite(gb) and ga * gb < 0:
                    if brentq is not None:
                        pts.append(brentq(lambda yy: g_derivative(yy, weights, shifts), a, b))
                    else:
                        root = _bisection_root(lambda yy: g_derivative(yy, weights, shifts), a, b)
                        if root is not None:
                            pts.append(root)
            except Exception:
                pass
    uniq = []
    for y in pts:
        if all(abs(y - z) > 1e-8 for z in uniq) and all(abs(y - d) > 1e-8 for d in shifts):
            uniq.append(y)
    return sorted(uniq)


def verify_required_domain(cert):
    shifts = cert["shifts"]
    worst = None
    bad_blocks = []
    for block in cert["blocks"]:
        A = block["A"]
        C = block["C"]
        weights = block["weights"]
        intervals = [(C - 1.0, A - 1.0), (C, A + 1.0)]
        pts = critical_points(intervals, weights, shifts)
        vals = [(V_value(y, weights, shifts), y) for y in pts]
        block_min, block_y = min(vals, key=lambda t: t[0])
        if worst is None or block_min < worst[0]:
            worst = (block_min, block["i"], block_y)
        if block_min <= 0:
            bad_blocks.append((block["i"], block_min, block_y))
    return worst, bad_blocks


def scan_overcheck_gap(cert, samples_per_block=1000):
    """Scan the irrelevant middle gap [A-1, C] to reproduce overcheck negatives."""
    shifts = cert["shifts"]
    worst = None
    for block in cert["blocks"]:
        A = block["A"]
        C = block["C"]
        weights = block["weights"]
        lo, hi = A - 1.0, C
        if lo >= hi:
            continue
        ys = np.linspace(lo, hi, samples_per_block)
        vals = []
        for y in ys:
            if all(abs(float(y) - d) > 1e-9 for d in shifts):
                vals.append((V_value(float(y), weights, shifts), float(y)))
        if not vals:
            continue
        block_min, block_y = min(vals, key=lambda t: t[0])
        if worst is None or block_min < worst[0]:
            worst = (block_min, block["i"], block_y)
    return worst


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("json_path")
    ap.add_argument("--gap-scan", action="store_true", help="also scan irrelevant middle gap")
    args = ap.parse_args()

    with open(args.json_path, "r") as f:
        cert = json.load(f)

    worst, bad = verify_required_domain(cert)
    print("Certificate:", cert.get("name", args.json_path))
    print("M =", cert["M"], "K =", cert["K"])
    print("Required-domain worst margin:", "{:.12g}".format(worst[0]))
    print("Required-domain worst block:", worst[1], "y =", "{:.15g}".format(worst[2]))
    print("Bad required-domain blocks:", len(bad))

    if args.gap_scan:
        gap_worst = scan_overcheck_gap(cert)
        print()
        print("Irrelevant middle-gap overcheck worst:", "{:.12g}".format(gap_worst[0]))
        print("Irrelevant middle-gap block:", gap_worst[1], "y =", "{:.15g}".format(gap_worst[2]))
        print("This gap corresponds to x in (-1,0), not to {-1} union [0,1].")


if __name__ == "__main__":
    main()
