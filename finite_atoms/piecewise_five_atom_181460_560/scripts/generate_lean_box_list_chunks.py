#!/usr/bin/env python3
from __future__ import annotations
import json, math, argparse
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'data' / 'piecewise_five_atom_181460_560blocks_margin_tuned_candidate.json'
OUT = ROOT / 'lean' / 'box_list_chunks'
THRESH = 1e-6
MAX_DEPTH = 30


def F(x):
    return Fraction(str(x))


def rat(x: Fraction) -> str:
    return f'(({x.numerator} : Rat) / {x.denominator})' if x.denominator != 1 else f'({x.numerator} : Rat)'


def atanh_lower(t, n):
    return 2 * sum(t ** (2 * i + 1) / (2 * i + 1) for i in range(n))


def atanh_upper(t, n):
    return atanh_lower(t, n) + 2 * t ** (2 * n + 1) / (1 - t * t)


def log_inv_lower_float(d, npos=150, nneg=60):
    if d < 1:
        t = (1 - d) / (1 + d)
        return atanh_lower(t, npos)
    t = (d - 1) / (d + 1)
    return -atanh_upper(t, nneg)


def approx_lower(lo, hi, w, sh):
    ds = [max(abs(float(lo)), abs(float(hi)))] + [max(abs(float(lo - d)), abs(float(hi - d))) for d in sh]
    return log_inv_lower_float(ds[0]) + sum(float(w[i]) * log_inv_lower_float(ds[i + 1]) for i in range(4))


def lb_float(lo, hi, w, sh):
    ds = [max(abs(float(lo)), abs(float(hi)))] + [max(abs(float(lo - d)), abs(float(hi - d))) for d in sh]
    return math.log(1 / ds[0]) + sum(float(w[i]) * math.log(1 / ds[i + 1]) for i in range(4))


def split(ints, sh):
    out = []
    for lo, hi in ints:
        pts = sorted(set([lo, hi] + [d for d in sh if lo < d < hi]))
        for a, b in zip(pts, pts[1:]):
            if a < b:
                out.append((a, b))
    return out


def cover(lo, hi, w, sh, depth=0):
    if approx_lower(lo, hi, w, sh) > THRESH:
        return [(lo, hi)]
    if depth >= MAX_DEPTH:
        raise RuntimeError((float(lo), float(hi), lb_float(lo, hi, w, sh)))
    m = (lo + hi) / 2
    return cover(lo, m, w, sh, depth + 1) + cover(m, hi, w, sh, depth + 1)


def boxes_for_interval(lo, hi, w, sh):
    out = []
    for a, b in split([(lo, hi)], sh):
        for L, R in cover(a, b, w, sh):
            Ds = [max(abs(L), abs(R))] + [max(abs(L - d), abs(R - d)) for d in sh]
            out.append((w, L, R, Ds))
    return out


def box_line(item):
    w, L, R, Ds = item
    vals = w + [L, R] + Ds
    fields = ['w1', 'w2', 'w3', 'w4', 'L', 'R', 'D0', 'D1', 'D2', 'D3', 'D4']
    return '  { ' + ', '.join(f'{f} := {rat(v)}' for f, v in zip(fields, vals)) + ' }'


def gen_list(name, items):
    return [f'def {name} : List RatBox := [', ',\n'.join(box_line(x) for x in items), ']']


def prove_branch(i: int, side: str):
    cap = side.capitalize()
    boxes = f'block{i:03d}{cap}Boxes'
    covers = f'block{i:03d}_{side}_covers'
    valid = f'block{i:03d}_{side}_boxes_valid'
    same = f'block{i:03d}_{side}_boxes_same_weights'
    return [
        f'  · rcases RatBox.mem_of_coversFrom {covers} hy with ⟨b, hb, hyb⟩',
        f'    have hv := {valid} b hb',
        f'    have hsame := {same} b hb',
        '    rcases hsame with ⟨hw1, hw2, hw3, hw4⟩',
        '    have hp := V_pos_of_valid_ratbox hv hyb hy0ne hy1ne hy2ne hy3ne hy4ne',
        f'    simpa [block{i:03d}W1, block{i:03d}W2, block{i:03d}W3, block{i:03d}W4, hw1, hw2, hw3, hw4] using hp',
    ]


def gen(block, sh):
    i = block['i']
    A = F(block['A'])
    C = F(block['C'])
    w = [F(x) for x in block['weights']]
    leftL, leftR = C - 1, A - 1
    rightL, rightR = C, A + 1
    left = boxes_for_interval(leftL, leftR, w, sh)
    right = boxes_for_interval(rightL, rightR, w, sh)
    lines = [
        'import PiecewiseFiveAtom181460BoxListCore',
        '',
        'set_option maxRecDepth 100000',
        'set_option maxHeartbeats 0',
        '',
        'namespace Erdos1038',
        'namespace PiecewiseFiveAtom181460Mathlib',
        '',
        'open Set',
        '',
        f'def block{i:03d}W1 : Rat := {rat(w[0])}',
        f'def block{i:03d}W2 : Rat := {rat(w[1])}',
        f'def block{i:03d}W3 : Rat := {rat(w[2])}',
        f'def block{i:03d}W4 : Rat := {rat(w[3])}',
        f'def block{i:03d}LeftL : Rat := {rat(leftL)}',
        f'def block{i:03d}LeftR : Rat := {rat(leftR)}',
        f'def block{i:03d}RightL : Rat := {rat(rightL)}',
        f'def block{i:03d}RightR : Rat := {rat(rightR)}',
        '',
    ]
    lines += gen_list(f'block{i:03d}LeftBoxes', left)
    lines += ['', '']
    lines += gen_list(f'block{i:03d}RightBoxes', right)
    lines += [
        '',
        f'def block{i:03d}Boxes : List RatBox := block{i:03d}LeftBoxes ++ block{i:03d}RightBoxes',
        '',
        f'theorem block{i:03d}_left_boxes_valid : ∀ b ∈ block{i:03d}LeftBoxes, b.Valid := by',
        '  native_decide',
        '',
        f'theorem block{i:03d}_right_boxes_valid : ∀ b ∈ block{i:03d}RightBoxes, b.Valid := by',
        '  native_decide',
        '',
        f'theorem block{i:03d}_left_boxes_same_weights : ∀ b ∈ block{i:03d}LeftBoxes,',
        f'    RatBox.SameWeights b block{i:03d}W1 block{i:03d}W2 block{i:03d}W3 block{i:03d}W4 := by',
        '  native_decide',
        '',
        f'theorem block{i:03d}_right_boxes_same_weights : ∀ b ∈ block{i:03d}RightBoxes,',
        f'    RatBox.SameWeights b block{i:03d}W1 block{i:03d}W2 block{i:03d}W3 block{i:03d}W4 := by',
        '  native_decide',
        '',
        f'theorem block{i:03d}_left_covers : RatBox.CoversFrom block{i:03d}LeftBoxes block{i:03d}LeftL block{i:03d}LeftR := by',
        '  native_decide',
        '',
        f'theorem block{i:03d}_right_covers : RatBox.CoversFrom block{i:03d}RightBoxes block{i:03d}RightL block{i:03d}RightR := by',
        '  native_decide',
        '',
        f'theorem block{i:03d}_required_pos',
        '    {y : ℝ}',
        f'    (hy : y ∈ Icc (block{i:03d}LeftL : ℝ) (block{i:03d}LeftR : ℝ) ∪',
        f'          Icc (block{i:03d}RightL : ℝ) (block{i:03d}RightR : ℝ))',
        '    (hy0ne : y ≠ 0)',
        '    (hy1ne : y ≠ d1)',
        '    (hy2ne : y ≠ d2)',
        '    (hy3ne : y ≠ d3)',
        '    (hy4ne : y ≠ d4) :',
        f'    0 < V (block{i:03d}W1 : ℝ) (block{i:03d}W2 : ℝ) (block{i:03d}W3 : ℝ) (block{i:03d}W4 : ℝ) y := by',
        '  rcases hy with hy | hy',
    ]
    lines += prove_branch(i, 'left')
    lines += prove_branch(i, 'right')
    lines += ['', '', 'end PiecewiseFiveAtom181460Mathlib', 'end Erdos1038', '']
    return '\n'.join(lines), len(left), len(right)


def main():
    cert = json.load(open(DATA))
    sh = [F(x) for x in cert['shifts']]
    ap = argparse.ArgumentParser()
    ap.add_argument('--only', type=int)
    args = ap.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    blocks = cert['blocks'] if args.only is None else [cert['blocks'][args.only]]
    total = 0
    for b in blocks:
        text, nl, nr = gen(b, sh)
        (OUT / f'PiecewiseFiveAtom181460BoxList{b["i"]:03d}.lean').write_text(text)
        print('block', b['i'], 'left', nl, 'right', nr)
        total += nl + nr
    print('total boxes', total)


if __name__ == '__main__':
    main()
