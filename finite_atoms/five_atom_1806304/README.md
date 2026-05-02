# Five-atom tail certificate

This is the folder to reference for the five-atom part of the $M=1.806304$ finite-atom update for Erdős Problem 1038.

It contains the Lean files for the five-atom tail block, including the full pole-free one-variable interval-box certificate.

Direct link:

[finite_atoms/five_atom_1806304](https://github.com/HKUST-AARON/Erdos-Problem-1038/tree/main/finite_atoms/five_atom_1806304)

## Method

This is a moving finite-atom dual certificate. For each parameter $a$ in a short interval, we build a five-atom positive measure $\lambda_a$. If its logarithmic potential is positive on the allowed primal support, the duality identity

$$
\int U_\mu\,d\lambda_a = \int U_{\lambda_a}\,d\mu
$$

forces at least one of the five swept points to lie in the positive set $\lbrace U_\mu>0\rbrace$.

For this tail block the swept intervals are disjoint from the already-covered long interval. So the sweep contributes its full parameter length.

The analytic check reduces to one variable. Writing $y=x-a$, the potential of $\lambda_a$ is a fixed function $V(y)$. The package records the endpoint and critical-bracket checks, and also includes a separate rational interval-box closure that covers the full pole-free interval.

In the full finite-atom route, this tail block is combined with the earlier forcing branch covering the long interval $(-1.708,0)$. The tail sweep then contributes

$$
1.806304-1.708=0.098304,
$$

so the route closes at

$$
1.708+0.098304=1.806304.
$$

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

The five swept points are therefore

$$
a,\quad
a+1.80650001,\quad
a+2.57053197,\quad
a+2.68367709,\quad
a+2.79017717.
$$

As $a$ moves through $[-1.806304,-1.708]$, these sweep the five intervals

$$
[-1.806304,-1.708],
$$

$$
[0.00019601,0.09850001],
$$

$$
[0.76422797,0.86253197],
$$

$$
[0.87737309,0.97567709],
$$

$$
[0.98387317,1.08217717].
$$

The Lean route file checks the exact disjointness arithmetic for these intervals.

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

The four shifted locations

$$
s_1=1.80650001,\quad s_2=2.57053197,\quad s_3=2.68367709,\quad s_4=2.79017717
$$

are the potential singularities of the one-variable `Real.log` expression.
The formal one-variable target is therefore pole-free: it asserts positivity
on the interval above only for $y\ne s_1,s_2,s_3,s_4$, not on the closed
interval including the poles.

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

The interval-box closure then covers all five smooth components between the poles, so the final one-variable theorem is not merely a finite list of sampled checks.

## What the Lean files prove

```text
lean/FiveAtom1806304Mathlib.lean
```

proves the `Real.log` positivity checks for $V$ using Mathlib logarithm estimates
and defines the pole-free target `PoleFreeOneVariableLogPositivity`, excluding
the four potential singularities $s_1,\ldots,s_4$.

```text
lean/FiveAtom1806304BoxCertificate.lean
```

proves the unconditional pole-free one-variable target
`poleFreeOneVariableLogPositivity_from_boxes` by a rational interval-box cover
of the five smooth components between the poles.

This is the main formal certificate for the five-atom positivity statement.

```text
lean/FiveAtom1806304Formal.lean
```

proves the exact integer arithmetic: the quartic sign changes giving the critical brackets and the ordering of the endpoints and poles.

```text
lean/FiveAtom1806304Route.lean
```

proves the route-level bookkeeping: the tail length, the swept-interval disjointness facts, the compatibility with the earlier forcing threshold, and the conditional implication from the long-interval forcing step plus the tail selector to the target $M=1.806304$.

## Scope

The Lean files in this folder formalize the five-atom tail certificate and its
route bookkeeping. The standard minimizer reduction, the logarithmic-potential
duality identity, and the measure-theoretic sweep/additivity framework are used
as the surrounding mathematical framework for the finite-atom route.

## Check it

Run the current finite-atom checks from the repository root:

```bash
finite_atoms/check_all.sh
```

The script uses the local Mathlib workspace and handles the temporary `.olean`
needed by `FiveAtom1806304BoxCertificate.lean`.
