# Five-atom certificate for Erdős Problem 1038

This repository contains the five-atom one-variable certificate used in a conditional lower-bound argument for Erdős Problem 1038.

It does **not** contain a full proof of the infimum problem.  In particular, the Tao/natso minimizer reduction, the duality lemma, the two-parameter forcing branch, and the global dual certificate problem are not formalized here.

## Five-atom certificate

For

\[
a\in[-1.806304,-1.708],
\]

consider

\[
\lambda_a=
\delta_a
+1.174168821\,\delta_{a+1.80650001}
+0.025921118\,\delta_{a+2.57053197}
+0.118647936\,\delta_{a+2.68367709}
+0.180553554\,\delta_{a+2.79017717}.
\]

Writing `y=x-a`, the required one-variable check is

\[
V(y)>0\qquad(0.708\le y\le 2.806304),
\]

where

\[
\begin{aligned}
V(y)=&\log |y|^{-1}
+1.174168821\log |y-1.80650001|^{-1}\\
&+0.025921118\log |y-2.57053197|^{-1}
+0.118647936\log |y-2.68367709|^{-1}\\
&+0.180553554\log |y-2.79017717|^{-1}.
\end{aligned}
\]

The derivative numerator is quartic.  The relevant critical brackets are

```text
[0.77003805,0.77003806]
[2.52642600,2.52642601]
[2.60759965,2.60759966]
[2.74249871,2.74249872]
```

The Lean/Mathlib file proves the endpoint and critical-bracket `Real.log` checks using rational Taylor/atanh bounds, with no floating-point arithmetic.

## Files

```text
lean/FiveAtom1806304Mathlib.lean   # Mathlib Real.log formal checks
lean/FiveAtom1806304Formal.lean    # exact arithmetic/sign/geometry checks
scripts/verify_five_atom_decimal.py # independent Decimal checker
lean-toolchain
lakefile.toml
lake-manifest.json
```

## Reproduce

```bash
lake exe cache get
lake env lean lean/FiveAtom1806304Formal.lean
lake env lean lean/FiveAtom1806304Mathlib.lean
python3 scripts/verify_five_atom_decimal.py
```

Expected Decimal output ends with:

```text
V(2.806304) lower=0.000004054663365146... threshold=0.000003 PASS
status: PASS
```

## Status

This is a formalized five-atom tail-block certificate.  It is suitable as a referenced certificate package in a forum comment, but it should not be described as a full solution of Erdős Problem 1038.
