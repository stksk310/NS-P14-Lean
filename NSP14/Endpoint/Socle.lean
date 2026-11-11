module
public import NSP14.Endpoint.TwoActionTop
public import NSP14.Endpoint.ArtinTransport
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

noncomputable def endpointMultiply (i : Fin 2) : D.source.TangentAlgebra k →ₗ[k] D.source.TangentAlgebra k :=
  (LinearMap.mul k (D.source.TangentAlgebra k)).flip (D.endpointToG k (MvPolynomial.X i))

/-- The actual simultaneous annihilator inside the actual G. -/
noncomputable def actualSocle : Submodule k (D.source.TangentAlgebra k) :=
  (D.endpointMultiply k 0).ker⊓(D.endpointMultiply k 1).ker

noncomputable def nativeSocle : Submodule (D.source.TangentAlgebra k) (D.source.TangentAlgebra k) :=
  (D.endpointToG k (MvPolynomial.X 0) •
    𝟙 (ModuleCat.of (D.source.TangentAlgebra k) (D.source.TangentAlgebra k))).hom.ker⊓
  (D.endpointToG k (MvPolynomial.X 1) •
    𝟙 (ModuleCat.of (D.source.TangentAlgebra k) (D.source.TangentAlgebra k))).hom.ker

noncomputable def nativeSocleCoefficients : ModuleCat k :=
  (ModuleCat.restrictScalars (algebraMap k (D.source.TangentAlgebra k))).obj
    (ModuleCat.of (D.source.TangentAlgebra k) (D.nativeSocle k))

noncomputable def socleCoefficientEquiv : D.nativeSocleCoefficients k ≃ₗ[k] D.actualSocle k where
  toFun a := ⟨a.val,by
    have ha0 : D.endpointToG k (MvPolynomial.X 0)*a.val=0 := a.property.1
    have ha1 : D.endpointToG k (MvPolynomial.X 1)*a.val=0 := a.property.2
    exact ⟨by change a.val*D.endpointToG k (MvPolynomial.X 0)=0;rw [mul_comm];exact ha0,
      by change a.val*D.endpointToG k (MvPolynomial.X 1)=0;rw [mul_comm];exact ha1⟩⟩
  invFun a := ⟨a.val,by
    have ha0 : a.val*D.endpointToG k (MvPolynomial.X 0)=0 := a.property.1
    have ha1 : a.val*D.endpointToG k (MvPolynomial.X 1)=0 := a.property.2
    exact ⟨by change D.endpointToG k (MvPolynomial.X 0)*a.val=0;rw [mul_comm];exact ha0,
      by change D.endpointToG k (MvPolynomial.X 1)*a.val=0;rw [mul_comm];exact ha1⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c a := by
    apply Subtype.ext
    change (algebraMap k (D.source.TangentAlgebra k) c)*a.val=c • a.val
    exact (Algebra.smul_def c a.val).symm

/-- The true endpoint H2 is the simultaneous actual annihilator.
The native comparison is G-linear before coefficient restriction. -/
noncomputable def actualH2SocleEquiv : (D.endpointComplex k).homology 2 ≃ₗ[k] D.actualSocle k :=
  (nativeCoefficientHomologyIso k (D.source.TangentAlgebra k)
    (actionRegularComplex (D.source.TangentAlgebra k) (D.endpointElements k)) 2).toLinearEquiv.trans
    (((ModuleCat.restrictScalars (algebraMap k (D.source.TangentAlgebra k))).mapIso
      (NSP14.Endpoint.twoActionH2Equiv (D.source.TangentAlgebra k)
        (D.endpointToG k (MvPolynomial.X 0)) (D.endpointToG k (MvPolynomial.X 1))
        (ModuleCat.of (D.source.TangentAlgebra k) (D.source.TangentAlgebra k))).toModuleIso).toLinearEquiv.trans
      (D.socleCoefficientEquiv k))

noncomputable instance actualSocleFinite : Module.Finite k (D.actualSocle k) :=
  Module.Finite.equiv (D.actualH2SocleEquiv k)

theorem actualR_socle_dimension : D.actualR k=Module.finrank k (D.actualSocle k) :=
  (D.actualH2SocleEquiv k).finrank_eq
end NSP14.Endpoint.Data
