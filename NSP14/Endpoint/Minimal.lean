module
public import NSP14.Endpoint.CoreWords
public import Mathlib.Order.Minimal
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

theorem coreCoordinates_add_endpoint (p : D.corePoints) (c : ℕ×ℕ) :
    D.coreCoordinates (p+D.coreEndpointPoint c)=
      ((D.coreCoordinates p).1,(D.coreCoordinates p).2.1+c.1,(D.coreCoordinates p).2.2+c.2) := by
  apply D.decodeCoordinate_injective
  rw [D.decode_coreCoordinates]
  change p.val+(D.coreEndpointPoint c).val=_
  rw [← D.decode_coreCoordinates p,D.coreEndpointPoint_coe]
  apply Prod.ext
  · dsimp [decodeCoordinate];ring
  · dsimp [decodeCoordinate];ring

theorem exists_minimalFiber_le (r : Fin D.u) (c : ℕ×ℕ) (hc : c∈D.coreFiber r) :
    ∃ b≤c,Minimal (·∈D.coreFiber r) b :=
  exists_minimal_le_of_wellFoundedLT (·∈D.coreFiber r) c hc

theorem coordinate_mem_fiber (p : D.corePoints) :
    (D.coreCoordinates p).2∈D.coreFiber (D.coreCoordinates p).1 :=
  (D.coreCoordinateEquiv p).property

/-- A genuine minimal fiber monomial has no nonconstant endpoint
factor, including factors consisting only of x or only of v. -/
theorem minimal_endpoint_factor (p q : D.corePoints) (c : ℕ×ℕ)
    (hmin : Minimal (·∈D.coreFiber (D.coreCoordinates p).1) (D.coreCoordinates p).2)
    (h : p=q+D.coreEndpointPoint c) : c=0 := by
  have hc := D.coreCoordinates_add_endpoint q c
  rw [← h] at hc
  have hr := congrArg (fun a : D.Coordinate => a.1) hc
  change (D.coreCoordinates p).1=(D.coreCoordinates q).1 at hr
  have hM := D.coordinate_mem_fiber q
  rw [← hr] at hM
  have h1 : (D.coreCoordinates p).2.1=(D.coreCoordinates q).2.1+c.1 :=
    congrArg (fun a : D.Coordinate => a.2.1) hc
  have h2 : (D.coreCoordinates p).2.2=(D.coreCoordinates q).2.2+c.2 :=
    congrArg (fun a : D.Coordinate => a.2.2) hc
  have hle : (D.coreCoordinates q).2≤(D.coreCoordinates p).2 := ⟨by omega,by omega⟩
  have he := hmin.eq_of_le hM hle
  have he1 := congrArg Prod.fst he
  have he2 := congrArg Prod.snd he
  apply Prod.ext
  · change c.1=0
    omega
  · change c.2=0
    omega
end NSP14.Endpoint.Data
