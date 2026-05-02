import Mathlib
import geometry_chunks.Forcing1708Geometry00
import geometry_chunks.Forcing1708Geometry01
import geometry_chunks.Forcing1708Geometry02
import geometry_chunks.Forcing1708Geometry03
import geometry_chunks.Forcing1708Geometry04
import geometry_chunks.Forcing1708Geometry05
import geometry_chunks.Forcing1708Geometry06
import geometry_chunks.Forcing1708Geometry07
import geometry_chunks.Forcing1708Geometry08
import geometry_chunks.Forcing1708Geometry09

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

theorem aggregate_index_certificates :
    (Forcing1708Geometry00.boxes.size = 98 ∧
      Forcing1708Geometry00.boxes.all Forcing1708Geometry00.geometryOk = true) ∧
    (Forcing1708Geometry01.boxes.size = 98 ∧
      Forcing1708Geometry01.boxes.all Forcing1708Geometry01.geometryOk = true) ∧
    (Forcing1708Geometry02.boxes.size = 98 ∧
      Forcing1708Geometry02.boxes.all Forcing1708Geometry02.geometryOk = true) ∧
    (Forcing1708Geometry03.boxes.size = 98 ∧
      Forcing1708Geometry03.boxes.all Forcing1708Geometry03.geometryOk = true) ∧
    (Forcing1708Geometry04.boxes.size = 98 ∧
      Forcing1708Geometry04.boxes.all Forcing1708Geometry04.geometryOk = true) ∧
    (Forcing1708Geometry05.boxes.size = 98 ∧
      Forcing1708Geometry05.boxes.all Forcing1708Geometry05.geometryOk = true) ∧
    (Forcing1708Geometry06.boxes.size = 98 ∧
      Forcing1708Geometry06.boxes.all Forcing1708Geometry06.geometryOk = true) ∧
    (Forcing1708Geometry07.boxes.size = 98 ∧
      Forcing1708Geometry07.boxes.all Forcing1708Geometry07.geometryOk = true) ∧
    (Forcing1708Geometry08.boxes.size = 98 ∧
      Forcing1708Geometry08.boxes.all Forcing1708Geometry08.geometryOk = true) ∧
    (Forcing1708Geometry09.boxes.size = 98 ∧
      Forcing1708Geometry09.boxes.all Forcing1708Geometry09.geometryOk = true) := by
  exact ⟨
    Forcing1708Geometry00.chunk_geometry_certificate,
    Forcing1708Geometry01.chunk_geometry_certificate,
    Forcing1708Geometry02.chunk_geometry_certificate,
    Forcing1708Geometry03.chunk_geometry_certificate,
    Forcing1708Geometry04.chunk_geometry_certificate,
    Forcing1708Geometry05.chunk_geometry_certificate,
    Forcing1708Geometry06.chunk_geometry_certificate,
    Forcing1708Geometry07.chunk_geometry_certificate,
    Forcing1708Geometry08.chunk_geometry_certificate,
    Forcing1708Geometry09.chunk_geometry_certificate⟩

end Forcing1708GeometryIndex
end Erdos1038
