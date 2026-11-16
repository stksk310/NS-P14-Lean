module
public import NSP14.ArithmeticSequence.ModelWindowAction
public import NSP14.Homological.RestrictedScalars
public import NSP14.Homological.ReverseWindowSplit
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
open scoped BigOperators Classical
namespace NSP14.ArithmeticSequence.Data
variable (D : NSP14.ArithmeticSequence.Data) (hv : 2 ≤ D.v) (k : Type) [Field k]

noncomputable def modelWindowPolynomial :
    VariableRing k (Fin (D.v-1)) →ₐ[k] (D.ordinaryModel hv).source.TangentAlgebra k :=
  MvPolynomial.aeval (fun i => D.modelMonomial hv k (i.val+1))

noncomputable abbrev modelWindowModule : ModuleCat (VariableRing k (Fin (D.v-1))) :=
  (ModuleCat.restrictScalars (D.modelWindowPolynomial hv k).toRingHom).obj (D.modelNativeQuotient hv k)

noncomputable def modelWindowCoefficientEquiv :
    coefficientModule k (Fin (D.v-1)) (D.modelWindowModule hv k) ≃ₗ[k]
    (ModuleCat.restrictScalars (algebraMap k ((D.ordinaryModel hv).source.TangentAlgebra k))).obj
      (D.modelNativeQuotient hv k) :=
  algebraRestrictionCoefficientEquiv k (VariableRing k (Fin (D.v-1)))
    ((D.ordinaryModel hv).source.TangentAlgebra k) (D.modelWindowPolynomial hv k) (D.modelNativeQuotient hv k)

noncomputable def modelWindowCoordinates :
    coefficientModule k (Fin (D.v-1)) (D.modelWindowModule hv k) ≃ₗ[k] (Fin D.v → k) :=
  (D.modelWindowCoefficientEquiv hv k).trans (D.modelNativeWindowEquiv hv k)

noncomputable instance modelWindowCoefficientFinite :
    Module.Finite k (coefficientModule k (Fin (D.v-1)) (D.modelWindowModule hv k)) :=
  Module.Finite.equiv (D.modelWindowCoordinates hv k).symm

noncomputable instance modelWindowFinite :
    Module.Finite (VariableRing k (Fin (D.v-1))) (D.modelWindowModule hv k) :=
  polynomialFinite_of_coefficientFinite _

noncomputable def modelPairCoordinates :
    coefficientModule k (Fin (D.v-1)) (D.modelWindowModule hv k) ≃ₗ[k]
      ((Fin D.residueDefect → k) × (Fin (D.v-D.residueDefect) → k)) :=
  (D.modelWindowCoordinates hv k).trans (reverseWindowSplit k D.v D.residueDefect D.residueDefect_le)

noncomputable def modelWindowUnit (a : Fin D.v) :
    coefficientModule k (Fin (D.v-1)) (D.modelWindowModule hv k) :=
  (D.modelWindowCoefficientEquiv hv k).symm (D.modelWindowClass hv k a.val)

theorem modelWindowUnit_coordinates (a : Fin D.v) :
    D.modelWindowCoordinates hv k (D.modelWindowUnit hv k a)=Pi.single a 1 := by
  change D.modelNativeWindowEquiv hv k
    ((D.modelWindowCoefficientEquiv hv k) ((D.modelWindowCoefficientEquiv hv k).symm (D.modelWindowClass hv k a.val)))=_
  rw [LinearEquiv.apply_symm_apply,D.modelWindowClass_coordinates]
  funext b
  by_cases he : a=b
  · subst b;simp
  · have hn : a.val≠b.val := fun h => he (Fin.ext h)
    simp [he,hn]

noncomputable def modelWindowBasis :
    Module.Basis (Fin D.v) k (coefficientModule k (Fin (D.v-1)) (D.modelWindowModule hv k)) :=
  (Pi.basisFun k (Fin D.v)).map (D.modelWindowCoordinates hv k).symm

theorem modelWindowBasis_unit (a : Fin D.v) : D.modelWindowBasis hv k a=D.modelWindowUnit hv k a := by
  apply (D.modelWindowCoordinates hv k).injective
  rw [D.modelWindowUnit_coordinates]
  rw [modelWindowBasis,Module.Basis.map_apply,Pi.basisFun_apply]
  exact (D.modelWindowCoordinates hv k).apply_symm_apply (Pi.single a 1)

theorem modelWindowVariable (j : Fin (D.v-1))
    (a : coefficientModule k (Fin (D.v-1)) (D.modelWindowModule hv k)) :
    D.modelWindowCoefficientEquiv hv k ((MvPolynomial.X j : VariableRing k (Fin (D.v-1))) • a)=
      D.modelMonomial hv k (j.val+1) • D.modelWindowCoefficientEquiv hv k a := by
  change D.modelWindowPolynomial hv k (MvPolynomial.X j) • (show D.modelNativeQuotient hv k from a)=_
  rw [modelWindowPolynomial,MvPolynomial.aeval_X]
  rfl
end NSP14.ArithmeticSequence.Data
