import Forcing1708StrongFormal
import Forcing1708StrongBoxData

/-!
# Aggregate entry point for the stronger `1.836` forcing certificate

This file collects the checked Lean layers currently available for the stronger
forcing handoff used by the `M = 1.814600` finite-atom route:

* exact parameter-domain arithmetic for `a in [-1.708,-sqrt(2)]` and
  `b=s(1.836+a)`;
* rational recombination checks for all 5955 interval boxes.

The analytic interval-log verification is still checked by the fixed JSON
certificate verifier in `scripts/verify_forcing_1708_strong_interval.py`.
-/

namespace Erdos1038
namespace Forcing1708StrongAggregate

theorem aggregate_certificate : True := by
  have _hdomain : ∀ {a s : ℝ},
      a ∈ Forcing1708Strong.ADomain → s ∈ Forcing1708Strong.SDomain →
        0 ≤ Forcing1708Strong.bOf a s ∧
        Forcing1708Strong.bOf a s ≤
          Forcing1708Strong.q 421786437626905 1000000000000000 ∧
        0 < Forcing1708Strong.wOf a s ∧
        Forcing1708Strong.q 649213562373095 1000000000000000 ≤
          Forcing1708Strong.cOf a s ∧
        Forcing1708Strong.cOf a s ≤ Forcing1708Strong.cShift ∧
        0 < -1 - a ∧
        1 < Forcing1708Strong.q 2071 1000 - Forcing1708Strong.bOf a s := by
    intro a s ha hs
    exact Forcing1708Strong.forcing_domain_arithmetic_certificate ha hs
  have _hbox := Forcing1708StrongBoxData.aggregate_index_certificates
  have _hmargin := Forcing1708StrongBoxData.rounded_worst_margin
  trivial

end Forcing1708StrongAggregate
end Erdos1038
