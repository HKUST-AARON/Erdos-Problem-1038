#!/usr/bin/env python3
"""Generate required-domain certificate for the 560-block 1.8146 candidate."""

from __future__ import annotations

import json
import math
from pathlib import Path
import numpy as np


def safe_log1_over_abs(x: float) -> float:
    return math.log(1.0 / abs(x))


def V_value(y: float, weights, shifts):
    return safe_log1_over_abs(y) + sum(
        float(w) * math.log(1.0 / abs(y - d))
        for w, d in zip(weights, shifts)
    )


def g_derivative(y: float, weights, shifts):
    return -(1.0 / y) - sum(float(w) / (y - d) for w, d in zip(weights, shifts))


def interval_samples(shifts, lo, hi):
    pts = [lo, hi] + [d for d in shifts if lo < d < hi]
    pts = sorted(pts)
    out = []
    for a, b in zip(pts[:-1], pts[1:]):
        eps_a = 1e-10 if any(abs(a - d) < 1e-14 for d in shifts) else 0.0
        eps_b = 1e-10 if any(abs(b - d) < 1e-14 for d in shifts) else 0.0
        aa = a + eps_a
        bb = b - eps_b
        if aa < bb:
            out.append((aa, bb))
    return out


def bisection_root(f, a, b, it=80):
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
    for _ in range(it):
        mid = 0.5 * (lo + hi)
        fm = f(mid)
        if not math.isfinite(fm):
            return None
        if flo * fm <= 0:
            hi, fhi = mid, fm
        else:
            lo, flo = mid, fm
    return 0.5 * (lo + hi)


def required_domain_min(weights, shifts, A, C):
    intervals = [(C - 1.0, A - 1.0), (C, A + 1.0)]
    points = []
    for lo, hi in intervals:
        points.extend([lo, hi])
        for a, b in interval_samples(shifts, lo, hi):
            try:
                ga = g_derivative(a, weights, shifts)
                gb = g_derivative(b, weights, shifts)
                if math.isfinite(ga) and math.isfinite(gb) and ga * gb < 0:
                    rt = bisection_root(lambda yy: g_derivative(yy, weights, shifts), a, b)
                    if rt is not None:
                        points.append(rt)
            except Exception:
                pass

    uniq = []
    for y in points:
        if any(abs(y - z) <= 1e-8 for z in uniq):
            continue
        if any(abs(y - d) <= 1e-9 for d in shifts):
            continue
        uniq.append(y)
    pts = sorted(uniq)
    if not pts:
        for lo, hi in intervals:
            pts.extend(np.linspace(lo, hi, 3000).tolist())
            pts.append(lo)
            pts.append(hi)

    vals = [(V_value(float(y), weights, shifts), float(y)) for y in pts]
    return min(vals, key=lambda t: t[0])


def gap_worst(weights, shifts, A, C):
    lo, hi = A - 1.0, C
    if lo >= hi:
        return None
    vals = []
    for y in np.linspace(lo, hi, 5000):
        if any(abs(float(y) - d) <= 1e-10 for d in shifts):
            continue
        vals.append((V_value(float(y), weights, shifts), float(y)))
    if not vals:
        return None
    return min(vals, key=lambda t: t[0])


def main():
    cert_path = (
        Path(__file__).resolve().parent.parent
        / "data"
        / "piecewise_five_atom_181460_560blocks_margin_tuned_candidate.json"
    )
    with open(cert_path, "r") as f:
        cert = json.load(f)

    shifts = cert['shifts']
    bad_blocks = []
    worst = (float('inf'), None, None)

    for block in cert['blocks']:
        A = float(block['A'])
        C = float(block['C'])
        w = [float(x) for x in block['weights']]
        mval, my = required_domain_min(w, shifts, A, C)
        if mval <= 0:
            bad_blocks.append({'i': block['i'], 'value': mval, 'argmin_y': my})
        if mval < worst[0]:
            worst = (mval, block['i'], my)

    gap_worst_val = float('inf')
    gap_worst_block = None
    gap_worst_y = None
    for block in cert['blocks']:
        A = float(block['A'])
        C = float(block['C'])
        w = [float(x) for x in block['weights']]
        r = gap_worst(w, shifts, A, C)
        if r is None:
            continue
        val, y = r
        if val < gap_worst_val:
            gap_worst_val = val
            gap_worst_block = block['i']
            gap_worst_y = y

    report = {
        'name': 'piecewise_five_atom_181460_560blocks_required_domain_certificate',
        'timestamp': '2026-05-04',
        'certificate_file': "data/piecewise_five_atom_181460_560blocks_margin_tuned_candidate.json",
        'M': cert['M'],
        'K': cert['K'],
        'mode': 'conditional',
        'support_assumption': 'supp(mu) subset {-1} union [0,1]',
        'required_check_formula': 'U_{lambda_a}(x)>0 on {-1} U [0,1] for all a in blocks',
        'required_domains_in_y': '[C-1, A-1] U [C, A+1] (per block)',
        'irrelevant_gap': '[A-1, C] (corresponds x in (-1,0), not required)',
        'result': 'FAIL' if bad_blocks else 'PASS',
        'all_required_blocks_ok': len(bad_blocks) == 0,
        'overall_worst_required': {
            'value': worst[0],
            'block': int(worst[1]),
            'argmin_y': worst[2],
        },
        'num_blocks': len(cert['blocks']),
        'bad_required_blocks': bad_blocks,
        'irrelevant_gap_worst': {
            'value': gap_worst_val,
            'block': gap_worst_block,
            'argmin_y': gap_worst_y,
        },
    }

    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
