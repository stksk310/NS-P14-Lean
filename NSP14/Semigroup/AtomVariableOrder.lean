module
public import NSP14.Semigroup.AtomSplit
public import NSP14.Homological.OptionVariableOrder
public import NSP14.Homological.RegularPolynomialReduction
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]

noncomputable def fullAtomOrder : List S.AtomExponent :=
  (fullOptionOrder k S.NonXAtom).map S.optionNonXAtomEquiv

noncomputable def nonXNativeVariables : List (S.TangentAlgebra k) :=
  (variableList k S.NonXAtom).map (fun a => S.polynomialToG k (MvPolynomial.X a))

omit [Field k] in
theorem fullAtomOrder_all (a : S.AtomExponent) : a∈S.fullAtomOrder k := by
  obtain ⟨b,rfl⟩ := S.optionNonXAtomEquiv.surjective a
  exact List.mem_map.mpr ⟨b,fullOptionOrder_all k S.NonXAtom b,rfl⟩

omit [Field k] in
theorem fullAtomOrder_nodup : (S.fullAtomOrder k).Nodup :=
  (fullOptionOrder_nodup k S.NonXAtom).map S.optionNonXAtomEquiv.injective

theorem fullAtomOrder_action :
    (S.fullAtomOrder k).map (fun a => S.fullPolynomialToG k (MvPolynomial.X a))=
      S.xElement k :: S.nonXNativeVariables k := by
  unfold fullAtomOrder fullOptionOrder nonXNativeVariables
  rw [List.map_map,List.map_cons]
  apply congrArg₂ List.cons
  · change S.fullPolynomialToG k (MvPolynomial.X (⟨S.multiplicityExponent,S.multiplicity_atom⟩ : S.AtomExponent))=_
    rw [S.fullPolynomialToG_X]
    rfl
  · rw [List.map_map]
    apply List.map_congr_left
    intro a _
    change S.fullPolynomialToG k (MvPolynomial.X (⟨a.val,a.property.1⟩ : S.AtomExponent))=_
    rw [S.fullPolynomialToG_X,S.polynomialToG_X]

noncomputable def regularFullModuleIso :
    polynomialRegularModule k S.AtomExponent (S.TangentAlgebra k) (S.fullPolynomialToG k) ≅
      ModuleCat.of (S.FullPolynomialRing k) (S.TangentAlgebra k) := by
  let e : polynomialRegularModule k S.AtomExponent (S.TangentAlgebra k) (S.fullPolynomialToG k) ≃ₗ[S.FullPolynomialRing k]
      ModuleCat.of (S.FullPolynomialRing k) (S.TangentAlgebra k) :=
    { toFun a := a
      invFun a := a
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  exact e.toModuleIso

theorem nativeFullAtom_betti (i : ℕ) :
    Module.finrank k ((regularPartialCoefficientComplex k (S.TangentAlgebra k)
      (S.xElement k :: S.nonXNativeVariables k)).homology i)=
        totalBetti k S.AtomExponent (ModuleCat.of (S.FullPolynomialRing k) (S.TangentAlgebra k)) i := by
  have e := regularPartialPolynomialHomologyIso k (S.TangentAlgebra k) S.AtomExponent
    (S.fullPolynomialToG k) (S.fullAtomOrder k) (S.fullAtomOrder_all k) (S.fullAtomOrder_nodup k) i
  rw [S.fullAtomOrder_action k] at e
  exact e.toLinearEquiv.finrank_eq.trans (koszulHomologyKIso k S.AtomExponent (S.regularFullModuleIso k) i).toLinearEquiv.finrank_eq
end NSP14.NumericalSemigroup
