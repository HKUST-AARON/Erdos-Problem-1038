# Common finite-atom framework

This folder contains Lean lemmas shared by the finite-atom certificate route.

```text
lean/FiniteAtomFramework.lean
```

The file proves the finite dual-forcing implication used by both the forcing
branch and the five-atom tail block:

if a positive weighted finite atom sum is positive, and the primal potential is
non-positive outside a set `E`, then at least one atom lies in `E`.

It also proves the duality-to-selector interface:

```text
finite_atom_selector_from_duality
three_atom_selector_from_duality
five_atom_selector_from_duality
```

These theorems say that once a positive dual quantity is identified, via the
duality identity, with the finite weighted atom sum, the selector conclusion
follows.  The analytic proof of the logarithmic-potential integral identity is
not in this file; this file formalizes the finite step that follows from that
identity.

```text
lean/StandardReduction.lean
```

Formalizes the normalized-support consequence used by the standard reduction.
Once the reduced potential has the endpoint lower bound coming from at least
half of the mass at `-1`, the file proves that the punctured baseline interval

```text
(-sqrt 2, 0) \\ {-1}
```

lies in the positive set.  The point `-1` is removed only because this Lean file
uses real-valued `Real.log`; at an atom the logarithmic potential is infinite in
the underlying potential-theoretic formulation.

The file also proves that this puncture does not change the Lebesgue length:

```text
baselinePunctured_volume
```

Check command:

```bash
cd /Users/aaron/Downloads/erdos数学问题
lake env lean /Users/aaron/Downloads/Erdos-Problem-1038/finite_atoms/common/lean/FiniteAtomFramework.lean
lake env lean /Users/aaron/Downloads/Erdos-Problem-1038/finite_atoms/common/lean/StandardReduction.lean
```
