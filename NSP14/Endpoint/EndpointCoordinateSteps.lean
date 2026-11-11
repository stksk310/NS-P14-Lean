module
public import NSP14.Endpoint.SocleCorePoints
public import NSP14.Endpoint.ActualKernel
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Endpoint.Data
variable (D : Data)

theorem core_dead_coordinate (p : D.corePoints) :
    (D.coreCoordinates p).2∈D.actualDeadFiber (D.coreCoordinates p).1 ↔
      D.coreDegree p<D.source.order (D.coreValue p).val := by
  change ((D.coreCoordinates p).2∈D.coreFiber (D.coreCoordinates p).1 ∧
    (D.decodeCoordinate (D.coreCoordinates p)).1<D.source.order
      ((D.decodeCoordinate (D.coreCoordinates p)).1*D.m+(D.decodeCoordinate (D.coreCoordinates p)).2*D.d)) ↔ _
  rw [D.decode_coreCoordinates]
  exact and_iff_right (D.coordinate_mem_fiber p)

theorem coreCoordinates_endpoint_x (p : D.corePoints) :
    D.coreCoordinates (p+D.coreGeneratorPoint D.xVariable)=
      ((D.coreCoordinates p).1,(D.coreCoordinates p).2.1+1,(D.coreCoordinates p).2.2) := by
  let r := (D.coreCoordinates p).1
  let c := (D.coreCoordinates p).2
  have hc : (c.1+1,c.2)∈D.coreFiber r := D.coreFiber_upward r (a:=c) (b:=(c.1+1,c.2)) (D.coordinate_mem_fiber p) ⟨by omega,le_rfl⟩
  have he : (⟨D.decodeCoordinate (r,(c.1+1,c.2)),hc⟩ : D.corePoints)=p+D.coreGeneratorPoint D.xVariable := by
    apply Subtype.ext
    have h := D.decode_coreCoordinates p
    change (c.1+c.2+D.epsilon r,r.val+D.u*c.2)=p.val at h
    change D.decodeCoordinate (r,(c.1+1,c.2))=p.val+(1,0)
    rw [←h]
    apply Prod.ext <;> dsimp [decodeCoordinate]; omega
  rw [←he,D.coreCoordinates_decode]

theorem coreCoordinates_endpoint_v (p : D.corePoints) :
    D.coreCoordinates (p+D.coreGeneratorPoint D.vVariable)=
      ((D.coreCoordinates p).1,(D.coreCoordinates p).2.1,(D.coreCoordinates p).2.2+1) := by
  let r := (D.coreCoordinates p).1
  let c := (D.coreCoordinates p).2
  have hc : (c.1,c.2+1)∈D.coreFiber r := D.coreFiber_upward r (a:=c) (b:=(c.1,c.2+1)) (D.coordinate_mem_fiber p) ⟨le_rfl,by omega⟩
  have he : (⟨D.decodeCoordinate (r,(c.1,c.2+1)),hc⟩ : D.corePoints)=p+D.coreGeneratorPoint D.vVariable := by
    apply Subtype.ext
    have h := D.decode_coreCoordinates p
    change (c.1+c.2+D.epsilon r,r.val+D.u*c.2)=p.val at h
    change D.decodeCoordinate (r,(c.1,c.2+1))=p.val+(1,D.u)
    rw [←h]
    apply Prod.ext <;> dsimp [decodeCoordinate] <;> ring
  rw [←he,D.coreCoordinates_decode]
end NSP14.Endpoint.Data
