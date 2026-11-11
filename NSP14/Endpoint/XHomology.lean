module
public import NSP14.Endpoint.HomologyFinite
public import NSP14.Endpoint.SingleAction
public import NSP14.Semigroup.ActualFinite
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

theorem endpoint_xElement : D.endpointToG k (MvPolynomial.X 0)=D.source.xElement k := by
  rw [endpointToG,AlgHom.comp_apply,endpointToFull,MvPolynomial.rename_X]
  change D.fullToG k (MvPolynomial.X D.xVariable)=_
  rw [D.fullToG_X]
  unfold NumericalSemigroup.xElement
  apply congrArg (D.source.initialMonomial k)
  apply Subtype.ext
  change D.m+0*D.d=D.source.multiplicity
  simpa only [zero_mul,add_zero] using D.multiplicity.symm

noncomputable def xNativeComplex : ChainComplex (ModuleCat (D.source.TangentAlgebra k)) ℕ :=
  actionRegularComplex (D.source.TangentAlgebra k) [D.source.xElement k]

noncomputable def xComplex : ChainComplex (ModuleCat k) ℕ :=
  nativeCoefficientComplex k (D.source.TangentAlgebra k) (D.xNativeComplex k)

noncomputable def xNativeH0Equiv : (D.xNativeComplex k).homology 0 ≃ₗ[D.source.TangentAlgebra k]
    D.source.HeadAlgebra k :=
  (actionRegularH0Equiv (D.source.TangentAlgebra k) [D.source.xElement k]).trans
    (Submodule.quotEquivOfEq _ _ (by
      change Ideal.span {a : D.source.TangentAlgebra k | a∈[D.source.xElement k]}=D.source.xIdeal k
      congr 1
      ext a
      simp only [List.mem_singleton,Set.mem_ofPred_eq,Set.mem_singleton_iff]))

noncomputable def headNativeCoefficients : ModuleCat k :=
  (ModuleCat.restrictScalars (algebraMap k (D.source.TangentAlgebra k))).obj
    (ModuleCat.of (D.source.TangentAlgebra k) (D.source.HeadAlgebra k))

noncomputable def headCoefficientEquiv : D.headNativeCoefficients k ≃ₗ[k] D.source.HeadAlgebra k where
  toFun a := a
  invFun a := a
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c a := by
    change (algebraMap k (D.source.TangentAlgebra k) c) • (show D.source.HeadAlgebra k from a)=
      c • (show D.source.HeadAlgebra k from a)
    rw [algebraMap_smul]

noncomputable def xH0Equiv : (D.xComplex k).homology 0 ≃ₗ[k] D.source.HeadAlgebra k :=
  (nativeCoefficientHomologyIso k (D.source.TangentAlgebra k) (D.xNativeComplex k) 0).toLinearEquiv.trans
    (((ModuleCat.restrictScalars (algebraMap k (D.source.TangentAlgebra k))).mapIso
      (D.xNativeH0Equiv k).toModuleIso).toLinearEquiv.trans (D.headCoefficientEquiv k))

noncomputable def xNativeKernel : Submodule (D.source.TangentAlgebra k) (D.source.TangentAlgebra k) :=
  ((D.source.xElement k) • 𝟙 (ModuleCat.of (D.source.TangentAlgebra k) (D.source.TangentAlgebra k))).hom.ker

noncomputable def xNativeKernelCoefficients : ModuleCat k :=
  (ModuleCat.restrictScalars (algebraMap k (D.source.TangentAlgebra k))).obj
    (ModuleCat.of (D.source.TangentAlgebra k) (D.xNativeKernel k))

noncomputable def xKernelCoefficientEquiv : D.xNativeKernelCoefficients k ≃ₗ[k] (D.source.xMultiply k).ker where
  toFun a := ⟨a.val,by
    have h : D.source.xElement k*a.val=0 := a.property
    change a.val*D.source.xElement k=0
    rw [mul_comm]
    exact h⟩
  invFun a := ⟨a.val,by
    have h : a.val*D.source.xElement k=0 := a.property
    change D.source.xElement k*a.val=0
    rw [mul_comm]
    exact h⟩
  left_inv a := rfl
  right_inv a := rfl
  map_add' a b := rfl
  map_smul' c a := by
    apply Subtype.ext
    change (algebraMap k (D.source.TangentAlgebra k) c)*a.val=c • a.val
    exact (Algebra.smul_def c a.val).symm

noncomputable def xH1Equiv : (D.xComplex k).homology 1 ≃ₗ[k] (D.source.xMultiply k).ker :=
  (nativeCoefficientHomologyIso k (D.source.TangentAlgebra k) (D.xNativeComplex k) 1).toLinearEquiv.trans
    (((ModuleCat.restrictScalars (algebraMap k (D.source.TangentAlgebra k))).mapIso
      (NSP14.Endpoint.singleActionH1Equiv (D.source.TangentAlgebra k) (D.source.xElement k)
        (ModuleCat.of (D.source.TangentAlgebra k) (D.source.TangentAlgebra k))).toModuleIso).toLinearEquiv.trans
      (D.xKernelCoefficientEquiv k))

theorem xHomology_above (i : ℕ) (hi : 1 < i) : IsZero ((D.xComplex k).homology i) := by
  have hz : IsZero ((D.xNativeComplex k).homology i) :=
    HomologicalComplex.ExactAt.isZero_homology (HomologicalComplex.ExactAt.of_isZero
      (NSP14.Endpoint.action_piece_isZero_of_gt _ [_] _ i (by simpa using hi)))
  exact IsZero.of_iso ((ModuleCat.restrictScalars (algebraMap k (D.source.TangentAlgebra k))).map_isZero hz)
    (nativeCoefficientHomologyIso k (D.source.TangentAlgebra k) (D.xNativeComplex k) i)

noncomputable instance xHomologyFinite (i : ℕ) : Module.Finite k ((D.xComplex k).homology i) := by
  cases i with
  | zero => exact Module.Finite.equiv (D.xH0Equiv k).symm
  | succ i =>
    cases i with
    | zero => exact Module.Finite.equiv (D.xH1Equiv k).symm
    | succ i =>
      have : Subsingleton ((D.xComplex k).homology (i+1+1)) :=
        ModuleCat.subsingleton_of_isZero (D.xHomology_above k _ (by omega))
      infer_instance
end NSP14.Endpoint.Data
