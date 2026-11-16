module
public import NSP14.ArithmeticSequence.ModelKernel
public import NSP14.Homological.BasisShiftWindow
public import NSP14.Homological.RegularModuleReduction
@[expose] public section
open scoped Classical
namespace NSP14.ArithmeticSequence.Data
variable (D : NSP14.ArithmeticSequence.Data) (hv : 2 ≤ D.v) (k : Type) [Field k]

theorem modelMultiplicityMonomial :
    (D.ordinaryModel hv).source.xElement k=D.modelMonomial hv k D.v := by
  change (D.ordinaryModel hv).source.initialMonomial k _=(D.ordinaryModel hv).source.initialMonomial k _
  apply congrArg ((D.ordinaryModel hv).source.initialMonomial k)
  apply Subtype.ext
  change (D.ordinaryModel hv).source.multiplicity=D.modelExponent D.v
  rw [(D.ordinaryModel hv).multiplicity]
  simp only [modelExponent,D.blockCount_v,Nat.mul_one,Nat.two_mul,Nat.add_sub_cancel]
  rfl

noncomputable def modelKernelX : D.modelKernel hv k →ₗ[k] D.modelKernel hv k where
  toFun a := (D.ordinaryModel hv).source.xElement k • a
  map_add' _ _ := smul_add _ _ _
  map_smul' _ _ := smul_comm _ _ _

theorem modelKernelX_monomial (i : {i : ℕ // D.m ≤ i}) :
    D.modelKernelX hv k (D.modelKernelMonomial hv k i)=
      D.modelKernelMonomial hv k ⟨i.val+D.v,by omega⟩ := by
  apply Subtype.ext
  change (D.ordinaryModel hv).source.xElement k*D.modelMonomial hv k i.val=D.modelMonomial hv k (i.val+D.v)
  rw [D.modelMultiplicityMonomial,mul_comm,D.modelMonomial_mul,D.blockCount_add_v,D.blockCount_v]
  exact ite_eq_left rfl

theorem modelKernelX_injective : Function.Injective (D.modelKernelX hv k) := by
  intro a b he
  apply Subtype.ext
  apply (D.ordinaryModel hv).xMultiply_injective k
  change a.val*(D.ordinaryModel hv).source.xElement k=b.val*(D.ordinaryModel hv).source.xElement k
  have hex := congrArg Subtype.val he
  change (D.ordinaryModel hv).source.xElement k*a.val=(D.ordinaryModel hv).source.xElement k*b.val at hex
  simpa only [mul_comm] using hex

noncomputable def modelTailEquiv : ℕ ≃ {i : ℕ // D.m ≤ i} where
  toFun n := ⟨D.m+n,by omega⟩
  invFun n := n.val-D.m
  left_inv n := by simp
  right_inv n := Subtype.ext (Nat.add_sub_of_le n.property)

noncomputable def modelKernelNatBasis : Module.Basis ℕ k (D.modelKernel hv k) :=
  (D.modelKernelBasis hv k).reindex D.modelTailEquiv.symm

theorem modelKernelNatBasis_monomial (n : ℕ) :
    D.modelKernelNatBasis hv k n=D.modelKernelMonomial hv k ⟨D.m+n,by omega⟩ := by
  rw [modelKernelNatBasis,Module.Basis.reindex_apply]
  exact D.modelKernelBasis_monomial hv k (D.modelTailEquiv n)

theorem modelKernelX_natBasis (n : ℕ) :
    D.modelKernelX hv k (D.modelKernelNatBasis hv k n)=D.modelKernelNatBasis hv k (n+D.v) := by
  rw [D.modelKernelNatBasis_monomial,D.modelKernelNatBasis_monomial,D.modelKernelX_monomial]
  apply congrArg (D.modelKernelMonomial hv k)
  apply Subtype.ext
  exact Nat.add_assoc _ _ _

noncomputable def modelKernelWindowEquiv :
    (D.modelKernel hv k ⧸ (D.modelKernelX hv k).range) ≃ₗ[k] (Fin D.v → k) :=
  NSP14.Homological.basisShiftQuotientEquiv k (D.modelKernelNatBasis hv k) D.v
    (D.modelKernelX hv k) (D.modelKernelX_natBasis hv k)
end NSP14.ArithmeticSequence.Data
