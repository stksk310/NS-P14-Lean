module
public import NSP14.Semigroup.AtomVariableOrder
public import NSP14.Semigroup.HeadSquareZeroBetti
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]

noncomputable def scalarHeadPolynomialIso :
    scalarQuotientPolynomialModule k (S.TangentAlgebra k) S.NonXAtom (S.xElement k) (S.polynomialToG k) ≅
      S.headPolynomialModule k := by
  let e : scalarQuotientPolynomialModule k (S.TangentAlgebra k) S.NonXAtom (S.xElement k) (S.polynomialToG k) ≃ₗ[S.PolynomialRing k]
      S.headPolynomialModule k :=
    { toFun a := a
      invFun a := a
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  exact e.toModuleIso

/-- Actual regularity of x reduces all intrinsic Betti rows to the
actual non-x action on A. The rings and variable sets remain distinct. -/
theorem xRegular_totalBetti (hx : Function.Injective (S.xMultiply k)) (i : ℕ) :
    totalBetti k S.AtomExponent (ModuleCat.of (S.FullPolynomialRing k) (S.TangentAlgebra k)) i=
      totalBetti k S.NonXAtom (S.headPolynomialModule k) i := by
  have hr : Function.Injective (fun a : S.TangentAlgebra k => S.xElement k*a) := by
    intro a b h
    apply hx
    change a*S.xElement k=b*S.xElement k
    simpa only [mul_comm] using h
  have e := regularElementPolynomialReductionIso k (S.TangentAlgebra k) S.NonXAtom
    (S.xElement k) (S.polynomialToG k) hr i
  have hR := e.toLinearEquiv.finrank_eq
  exact (S.nativeFullAtom_betti k i).symm.trans (hR.trans
    (koszulHomologyKIso k S.NonXAtom (S.scalarHeadPolynomialIso k) i).toLinearEquiv.finrank_eq)

theorem xRegular_squareZero_betti_zero (hx : Function.Injective (S.xMultiply k))
    (hz : S.highIdeal k 2=⊥) :
    totalBetti k S.AtomExponent (ModuleCat.of (S.FullPolynomialRing k) (S.TangentAlgebra k)) 0=1 := by
  rw [S.xRegular_totalBetti k hx,S.headSquareZero_betti_zero k hz]

theorem xRegular_squareZero_betti (hx : Function.Injective (S.xMultiply k))
    (hz : S.highIdeal k 2=⊥) (i : ℕ) (hi : 1 ≤ i) :
    totalBetti k S.AtomExponent (ModuleCat.of (S.FullPolynomialRing k) (S.TangentAlgebra k)) i=
      i*S.embeddingDimension.choose (i+1) := by
  rw [S.xRegular_totalBetti k hx,S.headSquareZero_betti k hz i hi]
end NSP14.NumericalSemigroup
