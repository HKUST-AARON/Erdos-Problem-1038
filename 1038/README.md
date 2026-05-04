# Erdős Problem 1038 finite-atom tail certificate (M = 1.8146, K = 560)

This directory contains a complete required-domain verification package for the
piecewise five-atom tail block certificate:

- `piecewise_five_atom_181460_560blocks_margin_tuned_candidate.json`
- `verify_piecewise_tail_correct_domain.py`
- `scripts/generate_piecewise_560_181460_certificate.py`
- `scripts/verify_piecewise_181460_560_test.sh`
- `certificates/piecewise_five_atom_181460_560blocks_required_domain_certificate.json`
- `certificates/piecewise_five_atom_181460_560blocks_required_domain_certificate.md`

## Assumption

Checks are done under the standard Tao/natso normalization

a.s.:

	supp(\mu) ⊆ {−1} ∪ [0,1].

So each block is only required to satisfy

	a) positivity at x = −1, i.e. on y ∈ [C−1, A−1]
	b) positivity on x ∈ [0,1], i.e. on y ∈ [C, A+1]

on each block interval x-parameterized by a ∈ [−A,−C].

The middle interval (A−1, C), corresponding to x ∈ (−1, 0), is an overcheck region
and is not part of the requirement.

## Repro

Run:

```bash
bash scripts/verify_piecewise_181460_560_test.sh
```

Expected output includes `[OK] required-domain certificate pass` with worst required margin
≈ 9.534343713646365e-06.

## Caveat

This is a conditional tail certificate and is not a full 
`[-1,1]` positivity certificate.
