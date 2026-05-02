# Five-atom certificate for Erdős Problem 1038

This folder contains a Lean/Mathlib formalization of the five-atom one-variable certificate with parameter $M=1.806304$.

GitHub renders formulas reliably when this file uses inline `$...$` math and block `$$...$$` math.

## Certificate

For

$$
a\in[-1.806304,-1.708],
$$

consider

$$
\lambda_a=
\delta_a
+1.174168821\,\delta_{a+1.80650001}
+0.025921118\,\delta_{a+2.57053197}
+0.118647936\,\delta_{a+2.68367709}
+0.180553554\,\delta_{a+2.79017717}.
$$

Writing `y=x-a`, the one-variable potential is

$$
\begin{aligned}
V(y)=&\log |y|^{-1}
+1.174168821\log |y-1.80650001|^{-1}\\
&+0.025921118\log |y-2.57053197|^{-1}
+0.118647936\log |y-2.68367709|^{-1}\\
&+0.180553554\log |y-2.79017717|^{-1}.
\end{aligned}
$$

The formalized checks prove positivity at the endpoints and on the four critical brackets:

```text
0.708
[0.77003805,0.77003806]
[2.52642600,2.52642601]
[2.60759965,2.60759966]
[2.74249871,2.74249872]
2.806304
```

## Files

```text
lean/FiveAtom1806304Mathlib.lean   # Real.log checks using Mathlib
lean/FiveAtom1806304Formal.lean    # exact arithmetic/sign/geometry checks
lean-toolchain
lakefile.toml
lake-manifest.json
```

## Reproduce

From this folder:

```bash
lake exe cache get
lake env lean lean/FiveAtom1806304Formal.lean
lake env lean lean/FiveAtom1806304Mathlib.lean
```
