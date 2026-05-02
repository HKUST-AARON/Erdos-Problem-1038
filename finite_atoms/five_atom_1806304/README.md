# Five-atom tail certificate

This folder contains the Lean files for the `M = 1.806304` five-atom tail block in Erdős Problem 1038.

## Certificate

For

```text
a ∈ [-1.806304, -1.708]
```

the measure is

```text
λ_a =
  δ_a
  + 1.174168821 δ_(a + 1.80650001)
  + 0.025921118 δ_(a + 2.57053197)
  + 0.118647936 δ_(a + 2.68367709)
  + 0.180553554 δ_(a + 2.79017717)
```

After writing `y = x - a`, the potential becomes the one-variable function

```text
V(y) =
  log(|y|⁻¹)
  + 1.174168821 log(|y - 1.80650001|⁻¹)
  + 0.025921118 log(|y - 2.57053197|⁻¹)
  + 0.118647936 log(|y - 2.68367709|⁻¹)
  + 0.180553554 log(|y - 2.79017717|⁻¹)
```

The Lean proof checks positivity at the two endpoints and on these four critical brackets:

```text
0.708
[0.77003805, 0.77003806]
[2.52642600, 2.52642601]
[2.60759965, 2.60759966]
[2.74249871, 2.74249872]
2.806304
```

## Files

```text
lean/FiveAtom1806304Mathlib.lean   # Real.log estimates in Mathlib
lean/FiveAtom1806304Formal.lean    # integer arithmetic, signs, interval geometry
lean-toolchain
lakefile.toml
lake-manifest.json
```

## Check it

Run this from the folder:

```bash
lake exe cache get
lake env lean lean/FiveAtom1806304Formal.lean
lake env lean lean/FiveAtom1806304Mathlib.lean
```
