# Piecewise 5-atom (560-block, M=1.8146) required-domain certificate

## Claim
Using the 560-block piecewise five-atom tail package
`piecewise_five_atom_181460_560blocks_margin_tuned_candidate.json`,
the required-domain positivity certificate passes under the Tao/natso standard reduction.

## Reduction Assumption

A standard reduction to minimizers is assumed:

\[
\operatorname{supp}\mu \subseteq \{-1\}\cup[0,1].
\]

So for each block with parameter `a \in [-A,-C]`, we only require

\[
U_{\lambda_a}(x)>0\quad\text{on } \{-1\}\cup[0,1],
\]

equivalently in `y = x-a`:

- required domains: `[C-1, A-1]` (from x=-1) and `[C, A+1]` (from x in [0,1]);
- irrelevant middle gap: `(A-1, C)` (corresponds to x in (-1,0)), not required.

## Result

Generated certificate file:
`certificates/piecewise_five_atom_181460_560blocks_required_domain_certificate.json`

- `M = 1.814600`
- `K = 560`
- `overall_worst_required.value = 9.534343713646365e-06`
- `all_required_blocks_ok = true`
- `num bad required blocks = 0`

An irrelevant-gap negative point exists (overcheck only), reported separately in the certificate as
`irrelevant_gap_worst.value < 0`, but it lies in x in (-1,0) and does not affect this conditional argument.

## Repro

```bash
python3 scripts/verify_piecewise_tail_correct_domain.py data/piecewise_five_atom_181460_560blocks_margin_tuned_candidate.json --gap-scan
python3 scripts/generate_piecewise_560_181460_certificate.py > certificates/piecewise_five_atom_181460_560blocks_required_domain_certificate.json
```

You can also run the packaged test:

```bash
bash scripts/verify_piecewise_181460_560_test.sh
```

## Caveat

This is a normalized-support finite-atom tail certificate and is **not** a full
`[-1,1]` positivity certificate.
