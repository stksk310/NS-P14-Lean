module
public import NSP14.ArithmeticSequence.WindowPolynomialModule
public import NSP14.Homological.HankelDelta
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
open scoped BigOperators Classical
namespace NSP14.ArithmeticSequence.Data
variable (D : NSP14.ArithmeticSequence.Data) (hv : 2 ≤ D.v) (k : Type) [Field k]

noncomputable def modelNativePairCoordinates :
    (ModuleCat.restrictScalars (algebraMap k ((D.ordinaryModel hv).source.TangentAlgebra k))).obj
      (D.modelNativeQuotient hv k) ≃ₗ[k]
      ((Fin D.residueDefect → k) × (Fin (D.v-D.residueDefect) → k)) :=
  (D.modelNativeWindowEquiv hv k).trans (reverseWindowSplit k D.v D.residueDefect D.residueDefect_le)

theorem modelNativePairCoordinates_class (n : ℕ) :
    D.modelNativePairCoordinates hv k (D.modelWindowClass hv k n)=
      ((fun a : Fin D.residueDefect => if n=D.residueDefect-1-a.val then (1:k) else 0),
       (fun b : Fin (D.v-D.residueDefect) => if n=D.residueDefect+b.val then (1:k) else 0)) := by
  change reverseWindowSplit k D.v D.residueDefect D.residueDefect_le
    (D.modelNativeWindowEquiv hv k (D.modelWindowClass hv k n))=_
  rw [D.modelWindowClass_coordinates]
  rfl

theorem modelPairCoordinates_unit (a : Fin D.v) :
    D.modelPairCoordinates hv k (D.modelWindowUnit hv k a)=
      ((fun b : Fin D.residueDefect => if a.val=D.residueDefect-1-b.val then (1:k) else 0),
       (fun b : Fin (D.v-D.residueDefect) => if a.val=D.residueDefect+b.val then (1:k) else 0)) := by
  change D.modelNativePairCoordinates hv k
    ((D.modelWindowCoefficientEquiv hv k) ((D.modelWindowCoefficientEquiv hv k).symm (D.modelWindowClass hv k a.val)))=_
  rw [LinearEquiv.apply_symm_apply,D.modelNativePairCoordinates_class]

theorem modelWindowHankel_unit (j : Fin (D.v-1)) (a : Fin D.v) :
    D.modelPairCoordinates hv k ((MvPolynomial.X j : VariableRing k (Fin (D.v-1))) • D.modelWindowUnit hv k a)=
      hankelAction k D.residueDefect (D.v-D.residueDefect) j.val
        (D.modelPairCoordinates hv k (D.modelWindowUnit hv k a)) := by
  change D.modelNativePairCoordinates hv k
    (D.modelWindowCoefficientEquiv hv k ((MvPolynomial.X j : VariableRing k (Fin (D.v-1))) • D.modelWindowUnit hv k a))=_
  rw [D.modelWindowVariable]
  change D.modelNativePairCoordinates hv k (D.modelMonomial hv k (j.val+1) •
    ((D.modelWindowCoefficientEquiv hv k) ((D.modelWindowCoefficientEquiv hv k).symm (D.modelWindowClass hv k a.val))))=_
  rw [LinearEquiv.apply_symm_apply,D.modelWindowClass_twoStep hv k a.val (j.val+1) a.isLt (by omega) (by have := j.isLt;omega),
    D.modelPairCoordinates_unit]
  apply Prod.ext
  · funext b
    change (D.modelNativePairCoordinates hv k
      (if a.val<D.residueDefect ∧ D.residueDefect≤a.val+(j.val+1) ∧ a.val+(j.val+1)<D.v
       then D.modelWindowClass hv k (a.val+(j.val+1)) else 0)).1 b=0
    split_ifs with h
    · rw [D.modelNativePairCoordinates_class]
      change (if a.val+(j.val+1)=D.residueDefect-1-b.val then (1:k) else 0)=0
      rw [ite_eq_right (by have := b.isLt;omega)]
    · rw [map_zero]
      rfl
  · funext b
    rw [hankel_delta_upper]
    by_cases hc : a.val<D.residueDefect ∧ D.residueDefect≤a.val+(j.val+1) ∧ a.val+(j.val+1)<D.v
    · rw [ite_eq_left hc,D.modelNativePairCoordinates_class]
      change (if a.val+(j.val+1)=D.residueDefect+b.val then (1:k) else 0)=_
      have he : (a.val+(j.val+1)=D.residueDefect+b.val) ↔
        (a.val<D.residueDefect ∧ j.val+a.val+1=D.residueDefect+b.val) := by omega
      simp only [he]
    · rw [ite_eq_right hc,map_zero]
      change (0:k)=(if a.val<D.residueDefect ∧ j.val+a.val+1=D.residueDefect+b.val then 1 else 0)
      have hb := b.isLt
      have hd := D.residueDefect_le
      rw [ite_eq_right (by omega)]

/-- Hankel action on every linear combination in the actual quotient,
not just on its numerical basis labels. -/
theorem modelWindowHankel (j : Fin (D.v-1))
    (a : coefficientModule k (Fin (D.v-1)) (D.modelWindowModule hv k)) :
    D.modelPairCoordinates hv k ((MvPolynomial.X j : VariableRing k (Fin (D.v-1))) • a)=
      hankelAction k D.residueDefect (D.v-D.residueDefect) j.val (D.modelPairCoordinates hv k a) := by
  let L := (D.modelPairCoordinates hv k).toLinearMap.comp
    (coefficientMap k (Fin (D.v-1)) ((MvPolynomial.X j : VariableRing k (Fin (D.v-1))) • 𝟙 (D.modelWindowModule hv k)))
  let R := (hankelAction k D.residueDefect (D.v-D.residueDefect) j.val).comp (D.modelPairCoordinates hv k).toLinearMap
  have he : L=R := by
    apply (D.modelWindowBasis hv k).ext
    intro b
    change D.modelPairCoordinates hv k ((MvPolynomial.X j : VariableRing k (Fin (D.v-1))) • D.modelWindowBasis hv k b)=_
    rw [D.modelWindowBasis_unit]
    exact D.modelWindowHankel_unit hv k j b
  exact LinearMap.congr_fun he a
end NSP14.ArithmeticSequence.Data
