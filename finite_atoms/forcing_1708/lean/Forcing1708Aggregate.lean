import Forcing1708BoxData
import Forcing1708CoverageIndex
import Forcing1708GeometryIndex
import Forcing1708AnalyticPreconditionsIndex

/-!
# Aggregate entry point for the `1.7` forcing certificate

This file makes the four checked forcing indexes available through one Lean
entry point.  The route-level implication from this finite certificate to the
long-interval forcing statement is proved elsewhere.
-/

namespace Erdos1038
namespace Forcing1708Aggregate

theorem aggregate_certificate : True := by
  have _hbox := Forcing1708BoxData.aggregate_index_certificates
  have _hcoverage := Forcing1708CoverageIndex.aggregate_index_certificates
  have _hgeometry := Forcing1708GeometryIndex.aggregate_index_certificates
  have _hanalytic := Forcing1708AnalyticPreconditionsIndex.aggregate_index_certificates
  have _hmargin := Forcing1708BoxData.rounded_worst_margin
  have _hcells := Forcing1708CoverageIndex.total_coverage_cells
  exact trivial

end Forcing1708Aggregate
end Erdos1038
