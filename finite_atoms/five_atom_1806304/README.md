# Five-atom tail certificate

This folder contains the Lean files for the $M=1.806304$ five-atom tail block in Erdős Problem 1038.

## Method

This is a moving finite-atom dual certificate. For each parameter $a$ in a short interval, we build a five-atom positive measure $\lambda_a$. If its logarithmic potential is positive on the allowed primal support, the duality identity

$$
\int U_\mu\,d\lambda_a = \int U_{\lambda_a}\,d\mu
$$

forces at least one of the five swept points to lie in the positive set $\lbrace U_\mu>0\rbrace$.

For this tail block the swept intervals are disjoint from the already-covered long interval. So the sweep contributes its full parameter length.

The analytic check reduces to one variable. Writing $y=x-a$, the potential of $\lambda_a$ is a fixed function $V(y)$. Away from its poles, any minimum of $V$ on the relevant interval occurs at an endpoint or a critical point. The derivative numerator is a quartic, so the proof brackets the four critical points and checks $V>0$ on those brackets and at the two endpoints.

## Certificate

For

$$
a\in[-1.806304,-1.708],
$$

the measure is

$$
\lambda_a=
\delta_a
+1.174168821\,\delta_{a+1.80650001}
+0.025921118\,\delta_{a+2.57053197}
+0.118647936\,\delta_{a+2.68367709}
+0.180553554\,\delta_{a+2.79017717}.
$$

After writing $y=x-a$, the potential becomes

$$
\begin{aligned}
V(y)={}&\log \lvert y\rvert^{-1}
+1.174168821\log \lvert y-1.80650001\rvert^{-1}\\
&+0.025921118\log \lvert y-2.57053197\rvert^{-1}
+0.118647936\log \lvert y-2.68367709\rvert^{-1}\\
&+0.180553554\log \lvert y-2.79017717\rvert^{-1}.
\end{aligned}
$$

The relevant interval for $y$ is

$$
0.708\le y\le 2.806304.
$$

The proof checks positivity at the two endpoints and on these four critical brackets:

$$
\begin{gathered}
0.708,\\
[0.77003805,0.77003806],\\
[2.52642600,2.52642601],\\
[2.60759965,2.60759966],\\
[2.74249871,2.74249872],\\
2.806304.
\end{gathered}
$$

## What the Lean files prove

```text
lean/FiveAtom1806304Mathlib.lean
```

proves the `Real.log` positivity checks for $V$ using Mathlib logarithm estimates.

```text
lean/FiveAtom1806304Formal.lean
```

proves the exact integer arithmetic: the quartic sign changes giving the critical brackets, the ordering of the endpoints and poles, and the disjointness/length arithmetic for the swept intervals.

## Check it

Run this from the folder:

```bash
lake exe cache get
lake env lean lean/FiveAtom1806304Formal.lean
lake env lean lean/FiveAtom1806304Mathlib.lean
```
