module
public import NSP14.Endpoint.AssemblyCoefficients
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical DirectSum
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

theorem coreToG_zero_iff (f : D.Core k) : D.coreToG k f=0 ↔
    ∀ p : D.corePoints,¬D.coreDegree p<D.source.order (D.coreValue p).val → f.coeff p=0 := by
  change f∈(D.coreToG k).toLinearMap.ker ↔ _
  rw [D.coreToG_kernel_span]
  change f∈Submodule.span k ((fun p => AddMonoidAlgebra.single p (1:k)) '' _) ↔ _
  rw [←AddMonoidAlgebra.supported_eq_span_single,AddMonoidAlgebra.mem_supported']
  rfl

/-- The E-linear assembly has exactly the independently defined actual
N_r in each component, not the whole forbidden ideal T_r. -/
theorem assembled_kernel_iff (f : ⨁ r : Fin D.u,D.coreFiberIdeal k r) :
    D.coreToG k (D.coreFiberLinearAssembly k f)=0 ↔
      ∀ r,(f r).val∈D.actualKernelIdeal k r := by
  rw [D.coreToG_zero_iff]
  constructor
  · intro h r
    rw [D.actualKernelIdeal_mem]
    intro β hβ
    have hM := (D.coreFiberIdeal_mem k r (f r).val).mp (f r).property β hβ
    refine ⟨hM,?_⟩
    let b : D.FiberBasisIndex := ⟨r,⟨β,hM⟩⟩
    by_contra hdead
    have hz := h (D.fiberPolynomialPoint b.1 b.2) hdead
    rw [D.coreFiberLinearAssembly_coeff] at hz
    exact (Finsupp.mem_support_iff.mp hβ) hz
  · intro h p hp
    let b := D.fiberPolynomialIndexEquiv.symm p
    have he : D.fiberPolynomialPoint b.1 b.2=p := D.fiberPolynomialIndexEquiv.apply_symm_apply p
    rw [←he,D.coreFiberLinearAssembly_coeff]
    by_contra hne
    have hβ : b.2.val∈(f b.1).val.support := Finsupp.mem_support_iff.mpr hne
    have hd := ((D.actualKernelIdeal_mem k b.1 (f b.1).val).mp (h b.1) b.2.val hβ).2
    apply hp
    rw [←he]
    exact hd
end NSP14.Endpoint.Data
