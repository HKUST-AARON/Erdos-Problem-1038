import Mathlib

/-!
# Geometry chunk index for the forcing branch

The rational geometry checks are split into 10 files under
`lean/geometry_chunks/`. They check the box-level bounds for
`b=s(1.82+a)` and the three positive distance bounds used by the analytic
log kernel.
-/

namespace Erdos1038
namespace Forcing1708GeometryIndex

theorem geometry_chunk_count : (10 : Nat) = 10 := rfl

end Forcing1708GeometryIndex
end Erdos1038
