# Five-atom one-variable certificate

This note records only the five-atom tail block.

For `a in [-1.806304,-1.708]`, define

\[
\lambda_a=
\delta_a
+1.174168821\delta_{a+1.80650001}
+0.025921118\delta_{a+2.57053197}
+0.118647936\delta_{a+2.68367709}
+0.180553554\delta_{a+2.79017717}.
\]

With `y=x-a`, the required check is `V(y)>0` on `[0.708,2.806304]`, where

\[
\begin{aligned}
V(y)=&\log |y|^{-1}
+1.174168821\log |y-1.80650001|^{-1}\\
&+0.025921118\log |y-2.57053197|^{-1}
+0.118647936\log |y-2.68367709|^{-1}\\
&+0.180553554\log |y-2.79017717|^{-1}.
\end{aligned}
\]

The derivative numerator is quartic, and the relevant critical brackets are:

```text
[0.77003805,0.77003806]
[2.52642600,2.52642601]
[2.60759965,2.60759966]
[2.74249871,2.74249872]
```

The theorem `all_five_atom_log_checks_internal` in `lean/FiveAtom1806304Mathlib.lean` proves positivity at the endpoints and on these four brackets using Mathlib `Real.log` plus rational Taylor/atanh bounds.  No Float and no `sorry` are used.
