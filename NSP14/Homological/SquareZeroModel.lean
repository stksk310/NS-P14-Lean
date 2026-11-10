module
public import NSP14.Homological.SquareZeroEuler
public import NSP14.Homological.RestrictedScalars
public import Mathlib.Algebra.TrivSqZeroExt.Basic
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
open scoped Classical
namespace NSP14.Homological
variable (k : Type) [Field k] (r f : ℕ)

abbrev FirstOrderRing := TrivSqZeroExt k (Fin (r+f) → k)
noncomputable def firstOrderPolynomial : VariableRing k (Fin r) →ₐ[k] FirstOrderRing k r f :=
  MvPolynomial.aeval (fun v => TrivSqZeroExt.inr (Pi.single (Fin.castAdd f v) 1))
noncomputable def firstOrderModule : ModuleCat (VariableRing k (Fin r)) :=
  (ModuleCat.restrictScalars (firstOrderPolynomial k r f).toRingHom).obj
    (ModuleCat.of (FirstOrderRing k r f) (FirstOrderRing k r f))

noncomputable def firstOrderCoefficientEquiv :
    coefficientModule k (Fin r) (firstOrderModule k r f) ≃ₗ[k] FirstOrderRing k r f where
  toFun a := a
  invFun a := a
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c a := by
    change firstOrderPolynomial k r f (algebraMap k (VariableRing k (Fin r)) c)*(show FirstOrderRing k r f from a)=
      c • (show FirstOrderRing k r f from a)
    rw [(firstOrderPolynomial k r f).commutes,← Algebra.smul_def]

noncomputable def firstOrderUnit : coefficientModule k (Fin r) (firstOrderModule k r f) :=
  (firstOrderCoefficientEquiv k r f).symm 1
noncomputable def firstOrderConstant : coefficientModule k (Fin r) (firstOrderModule k r f) →ₗ[k] k :=
  (TrivSqZeroExt.fstHom k k (Fin (r+f) → k)).toLinearMap.comp (firstOrderCoefficientEquiv k r f).toLinearMap
noncomputable def firstOrderCoordinate (v : Fin r) : coefficientModule k (Fin r) (firstOrderModule k r f) →ₗ[k] k :=
  ((LinearMap.proj (Fin.castAdd f v)).comp (TrivSqZeroExt.sndHom k (Fin (r+f) → k))).comp
    (firstOrderCoefficientEquiv k r f).toLinearMap

theorem firstOrder_variable (v : Fin r) (a : coefficientModule k (Fin r) (firstOrderModule k r f)) :
    firstOrderCoefficientEquiv k r f ((MvPolynomial.X v : VariableRing k (Fin r)) • a)=
      TrivSqZeroExt.inr (Pi.single (Fin.castAdd f v) 1)*firstOrderCoefficientEquiv k r f a := by
  change firstOrderPolynomial k r f (MvPolynomial.X v)*(show FirstOrderRing k r f from a)=_
  rw [firstOrderPolynomial,MvPolynomial.aeval_X]
  rfl

theorem firstOrder_rankOne (v : Fin r) (a : coefficientModule k (Fin r) (firstOrderModule k r f)) :
    (MvPolynomial.X v : VariableRing k (Fin r)) • a=
      firstOrderConstant k r f a • ((MvPolynomial.X v : VariableRing k (Fin r)) • firstOrderUnit k r f) := by
  apply (firstOrderCoefficientEquiv k r f).injective
  rw [firstOrder_variable,map_smul,firstOrder_variable]
  change TrivSqZeroExt.inr (Pi.single (Fin.castAdd f v) 1)*firstOrderCoefficientEquiv k r f a=
    (firstOrderCoefficientEquiv k r f a).fst •
      (TrivSqZeroExt.inr (Pi.single (Fin.castAdd f v) 1)*(1 : FirstOrderRing k r f))
  rw [mul_one]
  apply TrivSqZeroExt.ext
  · simp
  · simp [TrivSqZeroExt.snd_mul,op_smul_eq_smul]

theorem firstOrder_independent (v w : Fin r) :
    firstOrderCoordinate k r f v ((MvPolynomial.X w : VariableRing k (Fin r)) • firstOrderUnit k r f)=
      if v=w then 1 else 0 := by
  change (firstOrderCoefficientEquiv k r f ((MvPolynomial.X w : VariableRing k (Fin r)) • firstOrderUnit k r f)).snd
      (Fin.castAdd f v)=_
  rw [firstOrder_variable]
  change (TrivSqZeroExt.inr (Pi.single (Fin.castAdd f w) 1)*(1 : FirstOrderRing k r f)).snd (Fin.castAdd f v)=_
  simp only [mul_one,TrivSqZeroExt.snd_inr,Pi.single_apply]
  by_cases he : v=w
  · subst w;simp
  · have hn : Fin.castAdd f v ≠ Fin.castAdd f w := fun h => he (Fin.ext (congrArg (fun z : Fin (r+f) => z.val) h))
    simp [he,hn]

noncomputable instance firstOrder_coefficientFinite :
    Module.Finite k (coefficientModule k (Fin r) (firstOrderModule k r f)) := by
  let : Module.Finite k (FirstOrderRing k r f) := by
    change Module.Finite k (k × (Fin (r+f) → k))
    infer_instance
  exact Module.Finite.equiv (firstOrderCoefficientEquiv k r f).symm
noncomputable instance firstOrder_finite : Module.Finite (VariableRing k (Fin r)) (firstOrderModule k r f) :=
  polynomialFinite_of_coefficientFinite _

theorem firstOrder_length : Module.finrank k (coefficientModule k (Fin r) (firstOrderModule k r f))=1+r+f := by
  rw [(firstOrderCoefficientEquiv k r f).finrank_eq]
  change Module.finrank k (k × (Fin (r+f) → k))=_
  rw [Module.finrank_prod,Module.finrank_self,Module.finrank_pi]
  simp [Nat.add_assoc]

theorem firstOrder_boundaryRank (j : ℕ) :
    koszulBoundaryRank k (Fin r) (firstOrderModule k r f) (j+1)=r.choose (j+1) := by
  have h := koszulBoundaryRank_rankOne_eq k (Fin r) (firstOrderModule k r f) (firstOrderUnit k r f)
    (firstOrderConstant k r f) (firstOrder_rankOne k r f) (firstOrderCoordinate k r f)
    (by intro v w;by_cases h : v=w <;> simpa [h] using firstOrder_independent k r f v w) j
  simpa only [Fintype.card_fin] using h

theorem firstOrder_Euler (hr : 1 ≤ r) (j : ℕ) :
    bettiEuler k (Fin r) (firstOrderModule k r f) j=
      ((r-1).choose j : ℤ)*(1+r+f)-(r.choose (j+1) : ℤ) := by
  rw [squareZero_bettiEuler k (Fin r) (firstOrderModule k r f) (firstOrderUnit k r f)
    (firstOrderConstant k r f) (firstOrder_rankOne k r f) (firstOrderCoordinate k r f)
    (by intro v w;by_cases h : v=w <;> simpa [h] using firstOrder_independent k r f v w)
    (by simpa using hr),firstOrder_length,Fintype.card_fin]
  push_cast
  rfl
end NSP14.Homological
