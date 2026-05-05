# Piecewise five-atom tail certificate (M = 1.814600, K = 560)

This folder contains the piecewise five-atom tail package for the finite-atom
lower-bound route at

\[
M = 1.814600,\quad B = 1.708,\quad K = 560
\]

The route uses the Tao/natso standard reduction. The required support condition is

\[
\operatorname{supp}\mu \subseteq \{-1\}\cup[0,1].
\]

Under this assumption, for each block with parameter $a\in[-A,-C]$ the dual atom
sum only needs

\[
U_{\lambda_a}(x)>0\quad\text{on}\quad \{-1\}\cup[0,1].
\]

In $y=x-a$, this is equivalent to checking two disjoint required domains

\[
[C-1,A-1]\quad\text{and}\quad [C,A+1]
\]

The interval $(A-1,C)$ corresponds to $x\in(-1,0)$ and is not part of the
normalized support (except the point $x=-1$ already handled separately), so it is
not required.

## Candidate data

Candidate file:

- `data/piecewise_five_atom_181460_560blocks_margin_tuned_candidate.json`

Shifts:

- `d1 = 1.8146001`
- `d2 = 2.55506`
- `d3 = 2.675215475`
- `d4 = 2.781815575`

For each block $a\in[-A,-C]$ the measure is

\[
\lambda_a=\delta_a+w_1\delta_{a+d_1}+w_2\delta_{a+d_2}+w_3\delta_{a+d_3}+w_4\delta_{a+d_4}.
\]

The sweeps and critical geometry are formalized in
`lean/PiecewiseFiveAtom181460Formal.lean`.

## Certificate Status

- Required-domain positivity, the domain relevant for support `{-1}∪[0,1]`, is
  verified by the generated checker with margin
  \[
  9.534343713646365\times 10^{-6}.
  \]

- This is **not** a full `[-1,1]` positivity certificate.

- The Lean files in this folder formalize the exact geometry, route arithmetic,
  and all 560 block weights. The 560 individual one-variable logarithmic
  positivity blocks are checked by the generated required-domain certificate,
  not expanded as 560 standalone Lean proof terms.

## Verification artifacts

- `certificates/piecewise_five_atom_181460_560blocks_required_domain_certificate.json`
- `certificates/piecewise_five_atom_181460_560blocks_required_domain_certificate.md`

## Commands

From this directory:

```bash
# show required-domain margin only
python3 scripts/verify_piecewise_181460_560.py

# show required-domain margin + middle-gap diagnostic + regenerate certificate
bash scripts/verify_piecewise_181460_560_test.sh
```

`verify_piecewise_tail_correct_domain.py` is the required-domain checker.
`verify_piecewise_181460_560_test.sh` runs the checker, regenerates the
certificate summary, and checks the PASS condition.

## Caveat

This package proves the finite tail block in the normalized-support setting.
It should be cited together with the standard reduction and the long forcing
branch.
