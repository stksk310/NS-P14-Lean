module
public import NSP14.Ordinary.RelativePresentation
public import NSP14.Semigroup.CutRetraction
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Ordinary.ActualWitness
variable {k : Type} [Field k] (W : ActualWitness k)

noncomputable def nonXRetraction : W.source.PolynomialRing (ScalarField (k:=k)) →ₐ[ScalarField (k:=k)] W.RelativeRing :=
  (MvPolynomial.rename Option.some).comp W.cut.polynomialRetraction

noncomputable def fullRelativeRetraction :
    W.source.FullPolynomialRing (ScalarField (k:=k)) →ₐ[ScalarField (k:=k)] W.RelativeRing :=
  MvPolynomial.aeval (fun a => if h : a.val.val=W.source.multiplicity then MvPolynomial.X none else
    W.nonXRetraction (MvPolynomial.X (⟨a.val,a.property,h⟩ : W.source.NonXAtom)))

theorem fullRelativeRetraction_nonX :
    W.fullRelativeRetraction.comp (W.source.nonXPolynomialInclusion _)=W.nonXRetraction := by
  apply MvPolynomial.algHom_ext
  intro a
  change W.fullRelativeRetraction (MvPolynomial.rename _ (MvPolynomial.X a))=W.nonXRetraction (MvPolynomial.X a)
  rw [MvPolynomial.rename_X,fullRelativeRetraction,MvPolynomial.aeval_X]
  simp only [dite_eq_right a.property.2]
  apply congrArg W.nonXRetraction
  apply congrArg MvPolynomial.X
  exact Subtype.ext rfl

theorem fullRelativeRetraction_comp : W.fullRelativeRetraction.comp W.relativeToFull=
    AlgHom.id (ScalarField (k:=k)) W.RelativeRing := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | none =>
    change W.fullRelativeRetraction (W.relativeToFull (MvPolynomial.X none))=MvPolynomial.X none
    rw [relativeToFull,MvPolynomial.aeval_X,fullRelativeRetraction,MvPolynomial.aeval_X]
    split
    · rfl
    · rename_i h
      exact (h rfl).elim
  | some i =>
    change W.fullRelativeRetraction (W.relativeToFull (MvPolynomial.X (some i)))=MvPolynomial.X (some i)
    rw [relativeToFull,MvPolynomial.aeval_X]
    have h := AlgHom.congr_fun W.fullRelativeRetraction_nonX (W.cut.polynomialForm i)
    change W.fullRelativeRetraction (W.source.nonXPolynomialInclusion _ (W.cut.polynomialForm i))=_ at h
    rw [h]
    change MvPolynomial.rename Option.some (W.cut.polynomialRetraction (W.cut.polynomialForm i))=_
    rw [W.cut.polynomialRetraction_form,MvPolynomial.rename_X]

/-- x and the literal selected lambdas are independent formal variables in
the full e-variable presentation. No independence in the actual quotient G
or A is inferred from this split embedding. -/
theorem relativeToFull_injective : Function.Injective W.relativeToFull :=
  (show Function.LeftInverse W.fullRelativeRetraction W.relativeToFull from
    fun p => AlgHom.congr_fun W.fullRelativeRetraction_comp p).injective
end NSP14.Ordinary.ActualWitness
