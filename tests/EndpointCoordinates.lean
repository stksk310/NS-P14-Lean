module
public import NSP14
@[expose] public section
open NSP14
namespace EndpointCoordinatesAcceptance
variable (D : Endpoint.Data)

theorem unique_nonnegative (p : D.corePoints) : D.decodeCoordinate (D.coreCoordinates p)=p.val :=
  D.decode_coreCoordinates p

theorem actual_coordinate_module_indices : Nonempty (D.corePoints ≃ D.CoordinatePoint) :=
  ⟨D.coreCoordinateEquiv⟩
end EndpointCoordinatesAcceptance
