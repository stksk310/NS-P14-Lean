module
public import NSP14.Semigroup.HeadFirstOrderAlgebra
public import NSP14.Homological.SquareZeroBetti
public import NSP14.Homological.RestrictedScalars
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
open scoped Classical
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]

noncomputable abbrev headPolynomialModule : ModuleCat (S.PolynomialRing k) :=
  ModuleCat.of (S.PolynomialRing k) (S.HeadAlgebra k)

noncomputable def headCoefficientEquiv : coefficientModule k S.NonXAtom (S.headPolynomialModule k) ≃ₗ[k] S.HeadAlgebra k :=
  originalCoefficientEquiv k S.NonXAtom (S.HeadAlgebra k)

noncomputable def headCoefficientUnit : coefficientModule k S.NonXAtom (S.headPolynomialModule k) :=
  (S.headCoefficientEquiv k).symm 1
noncomputable def headCoefficientConstant : coefficientModule k S.NonXAtom (S.headPolynomialModule k) →ₗ[k] k :=
  (S.headConstant k).comp (S.headCoefficientEquiv k).toLinearMap
noncomputable def headCoefficientCoordinate (v : S.NonXAtom) :
    coefficientModule k S.NonXAtom (S.headPolynomialModule k) →ₗ[k] k :=
  (LinearMap.proj v).comp ((S.headLinearCoordinates k).toLinearMap.comp
    ((S.headLinearPart k).comp (S.headCoefficientEquiv k).toLinearMap))

theorem headCoefficient_variable (v : S.NonXAtom) (a : coefficientModule k S.NonXAtom (S.headPolynomialModule k)) :
    S.headCoefficientEquiv k ((MvPolynomial.X v : S.PolynomialRing k) • a)=
      S.headMonomial k v.val*S.headCoefficientEquiv k a := by
  change S.polynomialToA k (MvPolynomial.X v)*(show S.HeadAlgebra k from a)=_
  rw [S.polynomialToA_X]
  rfl

theorem headCoefficient_independent (v w : S.NonXAtom) :
    S.headCoefficientCoordinate k v ((MvPolynomial.X w : S.PolynomialRing k) • S.headCoefficientUnit k)=
      if v=w then 1 else 0 := by
  change S.headLinearCoordinates k (S.headLinearPart k (S.headCoefficientEquiv k
    ((MvPolynomial.X w : S.PolynomialRing k) • S.headCoefficientUnit k))) v=_
  rw [S.headCoefficient_variable]
  change S.headLinearCoordinates k (S.headLinearPart k (S.headMonomial k w.val*1)) v=_
  rw [mul_one]
  change S.headLinearCoordinates k (S.headLinearPart k (S.linearAtom k w).val) v=_
  rw [S.headLinearPart_self,S.headLinearCoordinates_linearAtom]
  simp [Pi.single_apply]

theorem headCoefficient_rankOne (hz : S.highIdeal k 2=⊥) (v : S.NonXAtom)
    (a : coefficientModule k S.NonXAtom (S.headPolynomialModule k)) :
    (MvPolynomial.X v : S.PolynomialRing k) • a=S.headCoefficientConstant k a •
      ((MvPolynomial.X v : S.PolynomialRing k) • S.headCoefficientUnit k) := by
  apply (S.headCoefficientEquiv k).injective
  rw [S.headCoefficient_variable,map_smul,S.headCoefficient_variable]
  change S.headMonomial k v.val*S.headCoefficientEquiv k a=
    S.headConstant k (S.headCoefficientEquiv k a) • (S.headMonomial k v.val*1)
  rw [mul_one]
  have h := S.headLinear_mul_mod_high k (S.linearAtom k v) (S.headCoefficientEquiv k a)
  rw [← map_smul] at h
  have hm := Ideal.Quotient.eq.mp h
  rw [hz] at hm
  exact sub_eq_zero.mp hm

noncomputable instance headCoefficient_finite :
    Module.Finite k (coefficientModule k S.NonXAtom (S.headPolynomialModule k)) :=
  Module.Finite.equiv (S.headCoefficientEquiv k).symm

theorem headSquareZero_length (hz : S.highIdeal k 2=⊥) :
    Module.finrank k (coefficientModule k S.NonXAtom (S.headPolynomialModule k))=1+Fintype.card S.NonXAtom := by
  have hi : Function.Injective (Ideal.Quotient.mkₐ k (S.highIdeal k 2)) := by
    intro a b h
    have hm := Ideal.Quotient.eq.mp h
    rw [hz] at hm
    exact sub_eq_zero.mp hm
  let e : S.HeadAlgebra k ≃ₗ[k] S.FirstOrderHead k :=
    LinearEquiv.ofBijective (Ideal.Quotient.mkₐ k (S.highIdeal k 2)).toLinearMap ⟨hi,Ideal.Quotient.mk_surjective⟩
  rw [(S.headCoefficientEquiv k).finrank_eq,e.finrank_eq,S.firstOrderHead_finrank,S.nonXAtom_card]
  have := S.embeddingDimension_pos
  omega

theorem headSquareZero_betti_zero (hz : S.highIdeal k 2=⊥) :
    totalBetti k S.NonXAtom (S.headPolynomialModule k) 0=1 :=
  squareZero_totalBetti_zero k S.NonXAtom (S.headPolynomialModule k) (S.headCoefficientUnit k)
    (S.headCoefficientConstant k) (S.headCoefficient_rankOne k hz) (S.headCoefficientCoordinate k)
    (S.headCoefficient_independent k) (S.headSquareZero_length k hz)

theorem headSquareZero_betti (hz : S.highIdeal k 2=⊥) (i : ℕ) (hi : 1 ≤ i) :
    totalBetti k S.NonXAtom (S.headPolynomialModule k) i=i*S.embeddingDimension.choose (i+1) := by
  have h := squareZero_ordinary_betti k S.NonXAtom (S.headPolynomialModule k) (S.headCoefficientUnit k)
    (S.headCoefficientConstant k) (S.headCoefficient_rankOne k hz) (S.headCoefficientCoordinate k)
    (S.headCoefficient_independent k) (S.headSquareZero_length k hz) i hi
  rw [S.nonXAtom_card,Nat.sub_add_cancel (show 1 ≤ S.embeddingDimension from S.embeddingDimension_pos)] at h
  exact h
end NSP14.NumericalSemigroup
