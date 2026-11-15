module
public import NSP14.Width.EdgeHoleGeometry
public import NSP14.Width.TripleCorePoint
@[expose] public section
namespace NSP14.Tests.EdgeGeometry
variable (D : Endpoint.Data)
theorem missing_offset (hu : D.u=D.q+2) :
    ∃ h : ℕ,0<h ∧ h<D.u ∧ D.a=Finset.Ioo 0 D.u \ {h} :=
  D.one_missing_offset hu
end NSP14.Tests.EdgeGeometry
