# Five-atom tail certificate

This folder contains the five-atom tail certificate for the finite-atom lower-bound route at

$$
M=1.806304.
$$

It is one proof block inside the larger finite-atom route. The other blocks are the earlier forcing branch, the shared finite-atom selector lemmas, and the route-level arithmetic closure.

## Role in the route

The tail block is used after the long interval contribution has reached $1.708$. The tail sweep contributes

$$
1.806304-1.708=0.098304,
$$

so the finite route closes at

$$
1.708+0.098304=1.806304.
$$

The mathematical mechanism is the usual finite-atom dual forcing argument. For each parameter $a$, a positive finite measure $\lambda_a$ is chosen. Positivity of its logarithmic potential on the normalized primal support forces at least one of its atoms to lie in the positive set. Sweeping $a$ then gives a length contribution.

## Five atoms

For

$$
a\in[-1.806304,-1.708],
$$

the certificate uses

$$
\lambda_a=
\delta_a
+1.174168821\,\delta_{a+1.80650001}
+0.025921118\,\delta_{a+2.57053197}
+0.118647936\,\delta_{a+2.68367709}
+0.180553554\,\delta_{a+2.79017717}.
$$

The five swept points are

$$
a,
\quad a+1.80650001,
\quad a+2.57053197,
\quad a+2.68367709,
\quad a+2.79017717.
$$

As $a$ varies in $[-1.806304,-1.708]$, these sweep the intervals

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

The Lean route file checks the exact disjointness arithmetic for these swept intervals.

## One-variable potential

Writing $y=x-a$, the five-atom logarithmic potential becomes

$$
\begin{aligned}
V(y)={}&\log |y|^{-1}
+1.174168821\log |y-1.80650001|^{-1}\\
&+0.025921118\log |y-2.57053197|^{-1}
+0.118647936\log |y-2.68367709|^{-1}\\
&+0.180553554\log |y-2.79017717|^{-1}.
\end{aligned}
$$

The relevant interval is

$$
0.708\le y\le 2.806304.
$$

The four shifted locations

$$
s_1=1.80650001,
\quad s_2=2.57053197,
\quad s_3=2.68367709,
\quad s_4=2.79017717
$$

are poles of the logarithmic potential. The formal Lean target is therefore pole-free: it proves positivity for $y\ne s_1,s_2,s_3,s_4$.

## Lean files

```text
lean/FiveAtom1806304Mathlib.lean
```

Defines $V$, the pole-free positivity target, and the reusable Mathlib logarithm estimates.

```text
lean/FiveAtom1806304BoxCertificate.lean
```

The main formal certificate for this folder. It proves

```text
poleFreeOneVariableLogPositivity_from_boxes
```

by a rational interval-box cover of the five smooth components between the poles.

```text
lean/FiveAtom1806304Formal.lean
```

Checks exact integer arithmetic for the critical brackets, endpoint ordering, and swept-interval constants.

```text
lean/FiveAtom1806304Route.lean
```

Checks tail length, swept-interval disjointness, compatibility with the forcing threshold, and the route-level implication from the long interval contribution plus the tail selector.

It also formalizes the sweep-length step:

```text
tailSelector_measure_sum_lower_bound
tailSelector_length_sum_lower_bound
```

These theorems say that if the five-atom selector holds for every parameter in the tail interval, then the five swept pieces have total measure at least $1.806304-1.708$.

The multiple Lean files are split by proof obligation. They are not separate mathematical claims: together they form the five-atom tail certificate package.

## Check it

From the repository root, run:

```bash
finite_atoms/check_all.sh
```

The script uses the Mathlib workspace provided by `MATHLIB_WORKSPACE` and handles the temporary `.olean` needed by `FiveAtom1806304BoxCertificate.lean`.
