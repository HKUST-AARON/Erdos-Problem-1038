# Route closure for the 1.806304 finite-atom update

This folder is the entry point for the conditional finite-atom update at

```text
M = 1.806304
```

It records what is internal to the Lean certificate package and what remains an
external mathematical input.

## Lean file

```text
lean/Route1806304Closure.lean
```

This file proves the exact arithmetic closure of the route:

```text
1.708 + (1.806304 - 1.708) = 1.806304
1.806304 < 1.836
```

It also packages the finite route as an implication:

```text
long forcing contribution
+ tail contribution
+ addition rule
=> final 1.806304 contribution
```

The finite certificates supplying the two contributions are in:

```text
finite_atoms/forcing_1708/
finite_atoms/five_atom_1806304/
finite_atoms/common/
```

## Scope

This is the closure layer for the finite certificate route.  It is not the
Tao/natso standard minimizer reduction, and it is not a full formalization of
the original Erdős Problem 1038 statement.
