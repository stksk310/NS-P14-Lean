module
public import NSP14.Ordinary.ActualWitness
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Ordinary.ActualWitness
variable {k : Type} [Field k] (W : ActualWitness k)
abbrev ScalarField := NSP14.Homological.InfiniteScalarField k
/-- r+1 variables: none is the actual x; some i is the already selected cut.
This ring is distinct from P and the full e-variable minimal presentation. -/
abbrev RelativeRing := MvPolynomial (Option (Fin W.source.actualCutRank)) (ScalarField (k:=k))

noncomputable def relativeToFull : W.RelativeRing →ₐ[ScalarField (k:=k)]
    W.source.FullPolynomialRing (ScalarField (k:=k)) :=
  MvPolynomial.aeval (fun a => match a with
    | none => MvPolynomial.X ⟨W.source.multiplicityExponent,W.source.multiplicity_atom⟩
    | some i => W.source.nonXPolynomialInclusion _ (W.cut.polynomialForm i))

noncomputable def relativeToG : W.RelativeRing →ₐ[ScalarField (k:=k)]
    W.source.TangentAlgebra (ScalarField (k:=k)) :=
  (W.source.fullPolynomialToG _).comp W.relativeToFull

theorem relativeToG_X_none : W.relativeToG (MvPolynomial.X none)=W.source.xElement (ScalarField (k:=k)) := by
  change W.source.fullPolynomialToG _ (W.relativeToFull (MvPolynomial.X none))=_
  rw [relativeToFull,MvPolynomial.aeval_X]
  change W.source.fullPolynomialToG _ (MvPolynomial.X (⟨W.source.multiplicityExponent,W.source.multiplicity_atom⟩ : W.source.AtomExponent))=_
  rw [W.source.fullPolynomialToG_X]
  rfl

theorem relativeToG_X_some (i : Fin W.source.actualCutRank) :
    W.relativeToG (MvPolynomial.X (some i))=W.source.polynomialToG _ (W.cut.polynomialForm i) := by
  change W.source.fullPolynomialToG _ (W.relativeToFull (MvPolynomial.X (some i)))=_
  rw [relativeToFull,MvPolynomial.aeval_X]
  exact AlgHom.congr_fun (W.source.fullPolynomial_nonX_compat _) _

/-- The inherited action of the actual relative polynomial ring. No P-finite
or k-finite instance on G is asserted here. -/
noncomputable def relativeG : ModuleCat W.RelativeRing := by
  letI := W.relativeToG.toRingHom.toAlgebra
  exact ModuleCat.of W.RelativeRing (W.source.TangentAlgebra (ScalarField (k:=k)))
end NSP14.Ordinary.ActualWitness
