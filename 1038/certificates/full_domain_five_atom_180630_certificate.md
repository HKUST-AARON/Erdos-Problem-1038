# Full-domain 5-atom candidate (M=1.8063)

## Claim

The candidate
`1038/full_domain_five_atom_180630_candidate.json` passes the executable
full-domain check on

\[
y\in[C-1,A+1].
\]

This is stronger than the required-domain check used by the \(M=1.8146\)
package, because it includes the middle gap corresponding to \(x\in(-1,0)\).

## Data

- `M = 1.8063`
- `B = 1.7`
- `K = 1`
- shifts:
  `1.80650622062, 2.569946468152, 2.68375450413, 2.79028947924`
- weights:
  `1.171198733876, 0.025826760715, 0.119855590488, 0.1796615493`

## Verification

Run:

```bash
python3 1038/verify_piecewise_tail_correct_domain.py 1038/full_domain_five_atom_180630_candidate.json --full-domain
```

Observed output:

```text
Full-domain worst margin: 4.76003592105e-05
Full-domain worst block: 0 y = 2.74289951754338
Bad full-domain blocks: 0
```

## Caveat

This is an executable numerical certificate candidate, not a formal Lean
certificate.  It supports the middle-gap / \(N=1\) residual-domain route at the
older \(M=1.8063\) level.  It does not close the current \(M=1.8146\) target.
