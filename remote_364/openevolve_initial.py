"""Initial OpenEvolve program for Erdős 364 experiments.

The evolved function should return filters for possible starts x of three
consecutive powerful numbers x, x+1, x+2. A filter is represented as a pair
(modulus, allowed_residues). The evaluator rewards filters that are correct
for all true local squarefull constraints it can verify, that remove candidate
residues beyond the current local baseline, and that are not implied by earlier
filters. Redundant congruences such as mod 4 or mod 8 consequences of mod 36
are penalized.
"""


def proposed_filters():
    # Baseline theorem: x must be 7, 27, or 35 modulo 36.
    # Add new filters only when they strictly shrink the current residue set;
    # check this with: python3 check_filter_shrink.py openevolve_initial.py
    return [(36, {7, 27, 35})]
