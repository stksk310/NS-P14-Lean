module
public import NSP14.Ordinary.RelativePresentation
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.Ordinary.ActualWitness
variable {k : Type} [Field k] (W : ActualWitness k)

noncomputable def relativeHeadSpan : Submodule W.RelativeRing W.relativeG :=
  Submodule.span W.RelativeRing (Set.range (fun h : W.source.HeadExponent =>
    (show W.relativeG from W.source.initialMonomial (ScalarField (k:=k)) h.val)))

theorem relativeG_X_none_smul (a : W.relativeG) :
    ((MvPolynomial.X none : W.RelativeRing) • a : W.relativeG) =
      (show W.relativeG from W.source.xElement (ScalarField (k:=k))*(show W.source.TangentAlgebra (ScalarField (k:=k)) from a)) := by
  change W.relativeToG (MvPolynomial.X none)*(show W.source.TangentAlgebra (ScalarField (k:=k)) from a)=_
  rw [W.relativeToG_X_none]

theorem relative_initial_mem_span (x : W.source.carrier) :
    (show W.relativeG from W.source.initialMonomial (ScalarField (k:=k)) x) ∈ W.relativeHeadSpan := by
  have h : ∀ n,∀ hn : n∈W.source,
      (show W.relativeG from W.source.initialMonomial (ScalarField (k:=k)) ⟨n,hn⟩) ∈ W.relativeHeadSpan := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro hn
      by_cases hh : W.source.XHead n
      · exact Submodule.subset_span ⟨⟨⟨n,hn⟩,hh⟩,rfl⟩
      · obtain ⟨y,hy,he,ho⟩ : ∃ y∈W.source,n=y+W.source.multiplicity ∧
            W.source.order n=W.source.order y+1 := by
          by_contra hs
          exact hh ⟨hn,hs⟩
        have hlt : y<n := by have := W.source.multiplicity_pos; omega
        have hm := (W.relativeHeadSpan).smul_mem (MvPolynomial.X none : W.RelativeRing) (ih y hlt hy)
        rw [W.relativeG_X_none_smul] at hm
        change W.source.initialMonomial (ScalarField (k:=k)) W.source.multiplicityExponent *
          W.source.initialMonomial (ScalarField (k:=k)) ⟨y,hy⟩ ∈ W.relativeHeadSpan at hm
        have hl : W.source.order (W.source.multiplicity+y)=W.source.order W.source.multiplicity+W.source.order y := by
          rw [W.source.order_multiplicity, Nat.add_comm W.source.multiplicity y,← he,ho]
          omega
        rw [W.source.initialMonomial_mul_live _ _ _ hl] at hm
        have hv : W.source.multiplicityExponent+(⟨y,hy⟩ : W.source.carrier)=⟨n,hn⟩ := by
          apply Subtype.ext
          change W.source.multiplicity+y=n
          omega
        exact hv ▸ hm
  exact h x.val x.property

theorem relativeHeadSpan_top : W.relativeHeadSpan=⊤ := by
  apply top_unique
  intro a _
  change (show W.source.TangentAlgebra (ScalarField (k:=k)) from a) ∈ W.relativeHeadSpan
  rw [← W.source.tangent_expansion (ScalarField (k:=k)) (show W.source.TangentAlgebra (ScalarField (k:=k)) from a),Finsupp.sum]
  apply (W.relativeHeadSpan).sum_mem
  intro x _
  have h := (W.relativeHeadSpan).smul_mem (MvPolynomial.C
    (W.source.tangentCoordinates (ScalarField (k:=k)) (show W.source.TangentAlgebra (ScalarField (k:=k)) from a) x) : W.RelativeRing)
    (W.relative_initial_mem_span x)
  change W.relativeToG (MvPolynomial.C _)*W.source.initialMonomial (ScalarField (k:=k)) x ∈ W.relativeHeadSpan at h
  rw [MvPolynomial.algHom_C,← Algebra.smul_def] at h
  exact h

/-- G is finite over R because its actual finite head basis generates it by
powers of the actual x. This does not claim that G is finite over P or k. -/
theorem relativeG_finite : Module.Finite W.RelativeRing W.relativeG := by
  have hf := Module.Finite.span_of_finite (R:=W.RelativeRing)
    (Set.finite_range (fun h : W.source.HeadExponent =>
      (show W.relativeG from W.source.initialMonomial (ScalarField (k:=k)) h.val)))
  change Module.Finite W.RelativeRing W.relativeHeadSpan at hf
  rw [W.relativeHeadSpan_top] at hf
  exact Module.Finite.of_surjective (⊤ : Submodule W.RelativeRing W.relativeG).subtype
    (by intro a;exact ⟨⟨a,Submodule.mem_top⟩,rfl⟩)
end NSP14.Ordinary.ActualWitness
