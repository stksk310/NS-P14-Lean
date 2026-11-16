module
public import NSP14.ArithmeticSequence.HeadQuotientMap
public import NSP14.Semigroup.AlgebraVariableOrder
public import NSP14.Semigroup.RegularHeadBetti
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological NSP14.NumericalSemigroup
namespace NSP14.ArithmeticSequence.Data
variable (D : NSP14.ArithmeticSequence.Data) (k : Type) [Field k]

noncomputable def semigroupHeadAlgEquiv :
    (D.source.SemigroupRing k ⧸ D.source.semigroupXIdeal k) ≃ₐ[k] D.source.HeadAlgebra k :=
  (Ideal.quotientEquivAlgOfEq k (D.semigroupToHead_ker k).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (D.semigroupToHead_surjective k))

theorem semigroupHeadAlgEquiv_mk (a : D.source.SemigroupRing k) :
    D.semigroupHeadAlgEquiv k (Ideal.Quotient.mk (D.source.semigroupXIdeal k) a)=D.semigroupToHead k a := by
  rfl

theorem semigroupToHead_polynomial (p : D.source.PolynomialRing k) :
    D.semigroupToHead k (D.source.polynomialToSemigroupRing k p)=D.source.polynomialToA k p := by
  have he : (D.semigroupToHead k).comp (D.source.polynomialToSemigroupRing k)=D.source.polynomialToA k := by
    ext a
    simp only [AlgHom.comp_apply,polynomialToSemigroupRing,MvPolynomial.aeval_X,
      D.semigroupToHead_single,one_smul,D.source.polynomialToA_X]
  exact AlgHom.congr_fun he p

noncomputable def semigroupHeadPolynomialIso :
    scalarQuotientPolynomialModule k (D.source.SemigroupRing k) D.source.NonXAtom
      (D.source.semigroupX k) (D.source.polynomialToSemigroupRing k) ≅
        D.source.headPolynomialModule k := by
  let e := D.semigroupHeadAlgEquiv k
  have hc (p : D.source.PolynomialRing k) :
      e (Ideal.Quotient.mk (D.source.semigroupXIdeal k) (D.source.polynomialToSemigroupRing k p))=
        D.source.polynomialToA k p :=
    (D.semigroupHeadAlgEquiv_mk k _).trans (D.semigroupToHead_polynomial k p)
  let f : scalarQuotientPolynomialModule k (D.source.SemigroupRing k) D.source.NonXAtom
      (D.source.semigroupX k) (D.source.polynomialToSemigroupRing k) ≃ₗ[D.source.PolynomialRing k]
        D.source.headPolynomialModule k :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := fun p a => by
        change e (Ideal.Quotient.mk (D.source.semigroupXIdeal k)
          (D.source.polynomialToSemigroupRing k p)*(show D.source.SemigroupRing k ⧸ D.source.semigroupXIdeal k from a))=D.source.polynomialToA k p*e a
        rw [map_mul,hc] }
  exact f.toModuleIso

/-- The equality is between ordinary Tor on two actual minimal polynomial
presentations. The rings themselves are not identified. -/
theorem semigroup_cone_totalBetti (i : ℕ) :
    totalBetti k D.source.AtomExponent
      (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.SemigroupRing k)) i=
    totalBetti k D.source.AtomExponent
      (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.TangentAlgebra k)) i := by
  have e := regularElementPolynomialReductionIso k (D.source.SemigroupRing k) D.source.NonXAtom
    (D.source.semigroupX k) (D.source.polynomialToSemigroupRing k) (D.source.semigroupX_regular k) i
  have hr := (D.source.nativeFullAtom_semigroup_betti k i).symm.trans e.toLinearEquiv.finrank_eq
  have hq := (koszulHomologyKIso k D.source.NonXAtom (D.semigroupHeadPolynomialIso k) i).toLinearEquiv.finrank_eq
  exact (hr.trans hq).trans (D.source.xRegular_totalBetti k (D.xMultiply_injective k) i).symm
end NSP14.ArithmeticSequence.Data
