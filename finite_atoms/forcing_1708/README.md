# Forcing branch certificate

This folder is for the two-parameter forcing branch used before the five-atom tail block.

The branch uses

$$
a\in[-1.7,-\sqrt2],\qquad b=s(1.82+a),\qquad s\in[0,1],
$$

and

$$
\nu_{a,b}=\delta_a+(1.395-b)\delta_b+C(a,b)\delta_{1.071-b},
$$

where $C(a,b)$ is chosen by $U_{\nu_{a,b}}(-1)=10^{-4}$.

The certificate file is generated with a Lean-friendly interval kernel:

```text
forcing_1708_lean_friendly_certificate.json
```

It contains 980 boxes covering

```text
a ∈ [-1.7, -1.414213562373095]
s ∈ [0,1]
x ∈ [0,1]
```

with worst certified lower bound

```text
0.0000239208811537315956105078504291399218154660738757721383353416021873
```

## Lean files

The Lean formalization is split so each file remains fast to check.

```text
lean/Forcing1708Formal.lean
```

Formalizes the fixed constants and domain arithmetic for
`a in [-1.7,-sqrt(2)]`, `s in [0,1]`, `x in [0,1]`.

```text
lean/Forcing1708Mathlib.lean
```

Defines the `Real.log` forcing potential and proves the generic interval-box
soundness lemma.

```text
lean/Forcing1708BoxData.lean
lean/box_arith_chunks/Forcing1708BoxArith00.lean
...
lean/box_arith_chunks/Forcing1708BoxArith19.lean
```

Proves the exact rational arithmetic for the 980 recorded boxes.  The stored
log/base data are rounded outward to denominator `10^6`; the weakest rounded
lower bound is `21/1000000`, still above the required `1/1000000` margin.

```text
lean/Forcing1708CoverageIndex.lean
lean/coverage_chunks/Forcing1708CoverageA00.lean
...
lean/coverage_chunks/Forcing1708CoverageA14.lean
```

Proves the finite coverage witness table.  The 15 slabs contain
`15 * 1534 = 23010` elementary `(s,x)` cells.

## Check commands

Run these from the local Mathlib workspace:

```bash
cd /Users/aaron/Downloads/erdos数学问题
lake env lean /Users/aaron/Downloads/Erdos-Problem-1038/finite_atoms/forcing_1708/lean/Forcing1708Formal.lean
lake env lean /Users/aaron/Downloads/Erdos-Problem-1038/finite_atoms/forcing_1708/lean/Forcing1708Mathlib.lean
lake env lean /Users/aaron/Downloads/Erdos-Problem-1038/finite_atoms/forcing_1708/lean/Forcing1708BoxData.lean
lake env lean /Users/aaron/Downloads/Erdos-Problem-1038/finite_atoms/forcing_1708/lean/Forcing1708CoverageIndex.lean
find /Users/aaron/Downloads/Erdos-Problem-1038/finite_atoms/forcing_1708/lean/box_arith_chunks -name 'Forcing1708BoxArith*.lean' -print | sort | xargs -n 1 -P 4 sh -c 'lake env lean "$0"'
find /Users/aaron/Downloads/Erdos-Problem-1038/finite_atoms/forcing_1708/lean/coverage_chunks -name 'Forcing1708CoverageA*.lean' -print | sort | xargs -n 1 -P 4 sh -c 'lake env lean "$0"'
```
