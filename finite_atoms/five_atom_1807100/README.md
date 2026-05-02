# Five-atom tail certificate

This folder contains the five-atom tail certificate for the finite-atom lower-bound route at

$$
M=1.807100.
$$

It is one proof block inside the larger finite-atom route. The other blocks are the earlier forcing branch, the shared finite-atom selector lemmas, and the route-level arithmetic closure.

## Role in the route

The tail block is used after the long interval contribution has reached $1.708$. The tail sweep contributes

$$
1.807100-1.708=0.099100,
$$

so the finite route closes at

$$
1.708+0.099100=1.807100.
$$

The mathematical mechanism is the usual finite-atom dual forcing argument. For each parameter $a$, a positive finite measure $\lambda_a$ is chosen. Positivity of its logarithmic potential on the normalized primal support forces at least one of its atoms to lie in the positive set. Sweeping $a$ then gives a length contribution.

## Five atoms

For

$$
a\in[-1.807100,-1.708],
$$

the certificate uses

$$
\lambda_a=
\delta_a
+1.18287976\,\delta_{a+1.80710376}
+0.03349753\,\delta_{a+2.57979789}
+0.11739956\,\delta_{a+2.69319012}
+0.17267833\,\delta_{a+2.79229832}.
$$

The five swept points are

$$
a,
\quad a+1.80710376,
\quad a+2.57979789,
\quad a+2.69319012,
\quad a+2.79229832.
$$

As $a$ varies in $[-1.807100,-1.708]$, these sweep the intervals

$$
[-1.807100,-1.708],
$$

$$
[0.00000376,0.09910376],
$$

$$
[0.77269789,0.87179789],
$$

$$
[0.88609012,0.98519012],
$$

$$
[0.98519832,1.08429832].
$$

The Lean route file checks the exact disjointness arithmetic for these swept intervals.

## One-variable potential

Writing $y=x-a$, the five-atom logarithmic potential becomes

$$
\begin{aligned}
V(y)={}&\log |y|^{-1}
+1.18287976\log |y-1.80710376|^{-1}\\
&+0.03349753\log |y-2.57979789|^{-1}
+0.11739956\log |y-2.69319012|^{-1}\\
&+0.17267833\log |y-2.79229832|^{-1}.
\end{aligned}
$$

The relevant interval is

$$
0.708\le y\le 2.807100.
$$

The four shifted locations

$$
s_1=1.80710376,
\quad s_2=2.57979789,
\quad s_3=2.69319012,
\quad s_4=2.79229832
$$

are poles of the logarithmic potential. The formal Lean target is therefore pole-free: it proves positivity for $y\ne s_1,s_2,s_3,s_4$.

## Lean files

```text
lean/FiveAtom1807100Mathlib.lean
```

Defines $V$, the pole-free positivity target, and the reusable Mathlib logarithm estimates.

```text
lean/FiveAtom1807100BoxCertificate.lean
```

The main formal certificate for this folder. It proves

```text
poleFreeOneVariableLogPositivity_from_boxes
```

by a rational interval-box cover of the five smooth components between the poles.

```text
lean/FiveAtom1807100Formal.lean
```

Checks exact integer arithmetic for the critical brackets, endpoint ordering, and swept-interval constants.

```text
lean/FiveAtom1807100Route.lean
```

Checks tail length, swept-interval disjointness, compatibility with the forcing threshold, and the route-level implication from the long interval contribution plus the tail selector.

It also formalizes the sweep-length step:

```text
tailSelector_measure_sum_lower_bound
tailSelector_length_sum_lower_bound
```

These theorems say that if the five-atom selector holds for every parameter in the tail interval, then the five swept pieces have total measure at least $1.807100-1.708$.

The multiple Lean files are split by proof obligation. They are not separate mathematical claims: together they form the five-atom tail certificate package.

## Check it

From the repository root, run:

```bash
MATHLIB_WORKSPACE=/path/to/mathlib finite_atoms/check_all.sh
```

The script uses the Mathlib workspace provided by `MATHLIB_WORKSPACE` and handles the temporary `.olean` needed by `FiveAtom1807100BoxCertificate.lean`.
