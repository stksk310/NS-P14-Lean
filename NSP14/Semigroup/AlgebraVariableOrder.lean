module
public import NSP14.Semigroup.AlgebraHeadQuotient
public import NSP14.Semigroup.AtomVariableOrder
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]

noncomputable def polynomialToSemigroupRing : S.PolynomialRing k →ₐ[k] S.SemigroupRing k :=
  MvPolynomial.aeval (fun a => AddMonoidAlgebra.single a.val (1 : k))

noncomputable def semigroupNonXVariables : List (S.SemigroupRing k) :=
  (variableList k S.NonXAtom).map (fun a => S.polynomialToSemigroupRing k (MvPolynomial.X a))

theorem fullAtomOrder_semigroupAction :
    (S.fullAtomOrder k).map (fun a => S.fullPolynomialToSemigroupRing k (MvPolynomial.X a))=
      S.semigroupX k::S.semigroupNonXVariables k := by
  unfold fullAtomOrder fullOptionOrder semigroupNonXVariables
  rw [List.map_map,List.map_cons]
  apply congrArg₂ List.cons
  · change S.fullPolynomialToSemigroupRing k (MvPolynomial.X (⟨S.multiplicityExponent,S.multiplicity_atom⟩ : S.AtomExponent))=_
    exact MvPolynomial.aeval_X _ _
  · rw [List.map_map]
    apply List.map_congr_left
    intro a _
    change S.fullPolynomialToSemigroupRing k (MvPolynomial.X (⟨a.val,a.property.1⟩ : S.AtomExponent))=_
    simp only [fullPolynomialToSemigroupRing,polynomialToSemigroupRing,MvPolynomial.aeval_X]

noncomputable def regularSemigroupFullModuleIso :
    polynomialRegularModule k S.AtomExponent (S.SemigroupRing k) (S.fullPolynomialToSemigroupRing k) ≅
      ModuleCat.of (S.FullPolynomialRing k) (S.SemigroupRing k) := by
  let e : polynomialRegularModule k S.AtomExponent (S.SemigroupRing k) (S.fullPolynomialToSemigroupRing k) ≃ₗ[S.FullPolynomialRing k]
      ModuleCat.of (S.FullPolynomialRing k) (S.SemigroupRing k) :=
    { toFun a := a
      invFun a := a
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  exact e.toModuleIso

theorem nativeFullAtom_semigroup_betti (i : ℕ) :
    Module.finrank k ((regularPartialCoefficientComplex k (S.SemigroupRing k)
      (S.semigroupX k::S.semigroupNonXVariables k)).homology i)=
        totalBetti k S.AtomExponent (ModuleCat.of (S.FullPolynomialRing k) (S.SemigroupRing k)) i := by
  have e := regularPartialPolynomialHomologyIso k (S.SemigroupRing k) S.AtomExponent
    (S.fullPolynomialToSemigroupRing k) (S.fullAtomOrder k) (S.fullAtomOrder_all k) (S.fullAtomOrder_nodup k) i
  rw [S.fullAtomOrder_semigroupAction k] at e
  exact e.toLinearEquiv.finrank_eq.trans
    (koszulHomologyKIso k S.AtomExponent (S.regularSemigroupFullModuleIso k) i).toLinearEquiv.finrank_eq

end NSP14.NumericalSemigroup
