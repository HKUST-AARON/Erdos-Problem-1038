# Concrete fixed-epsilon two-interval diagnostic artifact

This is a concrete, reproducible diagnostic artifact for the corrected Tao two-interval ansatz at epsilon = 0.001.

It is not a final proof of Erdős 1038 and not yet an interval-certified fixed-epsilon existence proof. In particular, the Arb full-difference ball below does **not** contain zero; it records the residual at the current floating root. The value of this artifact is that it fixes the exact numerical object to be lifted to interval Krawczyk boxes.

## Reproduction

Run from `/Users/aaron/Downloads/erdos数学问题`:

```bash
.venv/bin/python 1038/solve_two_interval_finite_gap.py --epsilons 0.002,0.001,0.0005,0.0002,0.0001,0.00005 --arb-primitive-check --write-json 1038/two_interval_branch_certificate_skeleton.json
.venv/bin/python 1038/verify_two_interval_branch_skeleton.py
.venv/bin/python 1038/verify_two_interval_branch_skeleton.py --quiet --self-test-tamper
.venv/bin/python 1038/verify_two_interval_branch_skeleton.py --quiet --arb-primitive-check --self-test-tamper
.venv/bin/python 1038/verify_two_interval_branch_skeleton.py --quiet --arb-primitive-check --arb-center-residual-check --arb-box-uminus-check --arb-box-uminus-derivative-check --arb-box-contact-derivative-check --arb-box-dk-check --arb-interval-krawczyk-check --arb-box-dk-subdivisions 7,7 --self-test-tamper
.venv/bin/python 1038/verify_two_interval_sign_box.py --quiet
.venv/bin/python 1038/verify_two_interval_sign_box.py --quiet --self-test-tamper
.venv/bin/python 1038/verify_two_interval_krawczyk_grid.py --quiet
.venv/bin/python 1038/verify_two_interval_krawczyk_grid.py --quiet --obligation-report
.venv/bin/python 1038/verify_two_interval_krawczyk_grid.py --quiet --refine-grid-sizes 11,21,41
.venv/bin/python 1038/verify_two_interval_krawczyk_grid.py --quiet --refine-grid-sizes 11,21,41 --obligation-report
```

Script SHA256:

```text
a088e62244a92fe00d2f531663c8c39af17d0c2258bef91fae53d75c8db4641d  1038/solve_two_interval_finite_gap.py
```

JSON SHA256 after the run used here:

```text
b9fed0078911cda260f594d28a1203a58f9d46286ff3c538c5b61744cb52f106  1038/two_interval_branch_certificate_skeleton.json
```

Skeleton checker SHA256:

```text
c69b90bb4e4fecca2d34b06923aecd8e6979a4dad67b2e1a868ecdaea9679a4f  1038/verify_two_interval_branch_skeleton.py
```

Split verifier SHA256:

```text
80f50814a51ddab2935389f619c64b74b5f6da6467e3aa3863ade0361364dfe2  1038/verify_two_interval_sign_box.py
4abbe67fe5d14ca2e8fa9053e952707d158baf9a448f3a3228cce5da87d220f1  1038/verify_two_interval_krawczyk_grid.py
```

Dependency versions:

```text
numpy 2.4.4
scipy 1.17.1
sympy 1.14.0
python-flint 0.8.0
```

## Parameters

- epsilon: `0.001`
- eta: `0.03162277660168379`
- A: `1.241527550107589`
- alpha: `0.8344829019292586`
- ell: `-1.8071073680988166`
- r: `0.02632310766384517`
- beta: `0.999`

## Measure masses

- m_ell: `0.29919566983212226`
- m_r: `0.6296826260049989`
- m_1: `0.010550951467229052`
- density mass: `0.060570752695649654`
- total mass: `0.9999999999999998`

## Scalar equations

Floating potential residuals:

- U(alpha): `-4.496403249731884e-15`
- U(-1): `-1.249000902703301e-16`

Arb residue-log diagnostic for the difference equation:

- continuous part real ball: `[-0.177978719152763789865257351646441823004380971905459153238491310975847379 +/- 3.20e-73]`
- full difference U(-1)-U(alpha) Arb ball: `[1.03041556343898686133345207081894064467949830655595907225e-16 +/- 1.75e-73]`
- full difference contains zero: `False`
- path separation diagnostic: `0.9537100679675978`
- poles after removable-path cancellation: `6`

Interpretation: this is an Arb diagnostic for the current floating parameter value. Since `contains_zero = false`, it is **not** a proof that the scalar equation is exactly solved at this point. It shows the residual that the interval Krawczyk parameter box must absorb.

## Analytic Jacobian and sampled Krawczyk diagnostic

- analytic DK: `[[0.6911826895324055, -0.11407007261545841], [-0.02782129441437562, -0.455493245805725]]`
- analytic det DK: `-0.31800262377394994`
- max |analytic DK - finite-difference DK|: `1.8453977235211028e-10`
- sampled Krawczyk correction: `[1.8440102134040594e-13, 2.3638413054135236e-12]`
- sampled Krawczyk inclusion: `[4.771821705383822e-06, 0.0001160680377195088]`
- sampled Krawczyk margin: `[0.009995228178294617, 0.009883931962280492]`
- sampled contraction: `0.01160680353556675`

## Sign margins on Krawczyk box

`{'A<-ell': 0.5646617171079902, 'A>1': 0.24060944922406535, 'alpha<beta': 0.16420087030479702, 'beta<1': 0.0010000000000000009, 'ell<-1': 0.8071073680988166, 'r<alpha': 0.8078435664993242}`

## Status

PASS as a concrete fixed-epsilon diagnostic artifact, not as a proof certificate.

What is concretely established by this run:

- endpoint atom at 1 is included;
- measure/sign-chart inequalities have positive margins at the sampled Krawczyk box;
- analytic DK matches finite differences;
- sampled Krawczyk margin is large;
- stored sampled Krawczyk margin and contraction fields are rechecked by the branch skeleton verifier;
- stored floating contact residuals are rechecked by the branch skeleton verifier;
- the branch skeleton verifier's tamper self-test rejects in-memory corruptions of sampled margin, sampled contraction, stored residuals, branch sign margins, and Arb `contains_zero` when Arb mode is enabled;
- the branch skeleton verifier can additionally recompute an Arb/Acb ball for `U(-1)` and combine it with the residue-log Arb ball for `U(-1)-U(alpha)` to check the center K residuals without directly integrating the contact log singularity;
- the branch skeleton verifier can also enclose `U(-1)` over each full local Krawczyk parameter box using the boundary-layer variable `u=sin(theta/2)`; this avoids the spurious `nan` failure caused by complex-neighbourhood balls crossing the pole at `1` in the original theta coordinate;
- the same boundary-layer primitive also encloses the `U(-1)` directional derivatives with respect to the local `B` and `tau` coordinates over each Krawczyk box;
- the branch skeleton verifier now assembles a diagnostic Arb interval `DK` matrix from the `U(alpha)` and `U(-1)` derivative primitives and checks that every entry contains the center analytic Jacobian entry;
- the unsubdivided full-box defect-action check is too wide in the tau component; for row 0 it reports `defect=4.135115e-02`, `radius=1.000000e-02`, `margin=-3.135115e-02`, `max_DK_entry_radius=1.367222e+00`;
- with `--arb-interval-krawczyk-check --arb-box-dk-subdivisions 7,7`, the verifier now computes the center correction as an Arb upper bound for `abs(C*K_center)` instead of trusting stored floating `krawczyk["correction"]`, then combines it with the subdivided interval-DK defect action; all six rows pass `correction_arb_upper + max_subbox_defect_action < radii`; the worst remaining component is row 1, epsilon `0.001`, tau margin `4.163420e-03` with tau defect `5.836580e-03`, so the defect term dominates;
- the exported sign boxes pass a separate positivity/order/center-containment/stored-margin checker, including a tamper self-test;
- the exported Krawczyk boxes pass a separate deterministic full-box grid stress checker, with non-finite arithmetic rejected before PASS;
- the Krawczyk checker's refinement mode passes on grids `11,21,41` with zero reported row drift at the printed precision;
- the Krawczyk checker also reports intervalization budgets: with a conservative half-margin split, the worst uniform center-`K` radius budget is `2.110507e-03`, and the worst uniform `DK` entry-radius budget is `1.055254e-01` in the rescaled coordinates;
- the second scalar equation has a residue-log Arb evaluation at this fixed parameter value;
- poles in the Joukowski primitive are separated from the real integration path after cancelling the removable physical preimage of r.

Remaining to become a proof: lift this diagnostic local interval Krawczyk inclusion into the full fixed-epsilon proof chain with all outward-rounded primitives and the surrounding two-interval positivity/support checks; it is not a full \(1.83\) proof by itself.
