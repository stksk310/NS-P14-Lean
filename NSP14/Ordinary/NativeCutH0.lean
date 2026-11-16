module
public import NSP14.Homological.ActionH0Ideal
public import NSP14.Ordinary.CutResidualModule
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
open scoped Classical
namespace NSP14.NumericalSemigroup.LinearCutData
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)

noncomputable def nativeLambda (i : Fin S.actualCutRank) : S.TangentAlgebra k :=
  S.polynomialToG k (C.polynomialForm i)

noncomputable def nativeCutVariables : List (S.TangentAlgebra k) :=
  S.xElement k :: (variableList k (Fin S.actualCutRank)).map C.nativeLambda

noncomputable def nativeCutComplex : ChainComplex (ModuleCat (S.TangentAlgebra k)) ℕ :=
  actionRegularComplex (S.TangentAlgebra k) C.nativeCutVariables

noncomputable def nativeCutIdeal : Ideal (S.TangentAlgebra k) :=
  Ideal.span {a | a∈C.nativeCutVariables}

theorem nativeCutVariable_set : {a | a∈C.nativeCutVariables}=
    insert (S.xElement k) (Set.range C.nativeLambda) := by
  ext a
  simp only [nativeCutVariables,List.mem_cons,List.mem_map,Set.mem_ofPred_eq,Set.mem_insert_iff,Set.mem_range]
  constructor
  · rintro (h|⟨i,_,hi⟩)
    · exact Or.inl h
    · exact Or.inr ⟨i,hi⟩
  · rintro (h|⟨i,hi⟩)
    · exact Or.inl h
    · exact Or.inr ⟨i,mem_variableList k _ i,hi⟩

theorem nativeLambda_head (i : Fin S.actualCutRank) :
    S.toHeadAlgebra k (C.nativeLambda i)=(C.forms i).val := C.polynomialForm_image i

theorem nativeCutIdeal_head : C.nativeCutIdeal.map (S.toHeadAlgebra k).toRingHom=
    S.linearCutIdeal k C.forms S.actualCutRank := by
  rw [nativeCutIdeal,C.nativeCutVariable_set,Ideal.map_span,Set.image_insert_eq,← Set.range_comp]
  have hx : (S.toHeadAlgebra k).toRingHom (S.xElement k)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [hx,Ideal.span_insert_zero]
  have hfun : (⇑(S.toHeadAlgebra k).toRingHom ∘ C.nativeLambda)=(fun i => (C.forms i).val) :=
    funext C.nativeLambda_head
  rw [hfun]
  unfold linearCutIdeal
  congr 1
  ext a
  simp only [Set.mem_range,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨i,i.isLt,rfl⟩
  · rintro ⟨i,_,rfl⟩
    exact ⟨i,rfl⟩

noncomputable def nativeToResidual : S.TangentAlgebra k →ₐ[k] TrivSqZeroExt k (Fin C.complementRank → k) :=
  C.headToResidual.comp (S.toHeadAlgebra k)

theorem nativeToResidual_surjective : Function.Surjective C.nativeToResidual :=
  C.headToResidual_surjective.comp Ideal.Quotient.mk_surjective

theorem nativeToResidual_ker : RingHom.ker C.nativeToResidual.toRingHom=C.nativeCutIdeal := by
  have hx : S.xIdeal k ≤ C.nativeCutIdeal := by
    rw [xIdeal,nativeCutIdeal,C.nativeCutVariable_set,Ideal.span_insert]
    exact le_sup_left
  change RingHom.ker (C.headToResidual.toRingHom.comp (S.toHeadAlgebra k).toRingHom)=_
  rw [← RingHom.comap_ker,C.headToResidual_ker,← C.nativeCutIdeal_head]
  rw [Ideal.comap_map_of_surjective (S.toHeadAlgebra k).toRingHom
    (show Function.Surjective (S.toHeadAlgebra k).toRingHom from Ideal.Quotient.mk_surjective) C.nativeCutIdeal]
  have hker : Ideal.comap (S.toHeadAlgebra k).toRingHom ⊥=S.xIdeal k := Ideal.mk_ker
  rw [hker,sup_eq_left.mpr hx]

noncomputable def nativeCutResidualEquiv :
    (S.TangentAlgebra k ⧸ C.nativeCutIdeal) ≃ₐ[k] TrivSqZeroExt k (Fin C.complementRank → k) :=
  (Ideal.quotientEquivAlgOfEq k C.nativeToResidual_ker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective C.nativeToResidual_surjective)

/-- This H0 equivalence is linear over the entire actual G, before
restricting to any polynomial subring. -/
noncomputable def nativeCutH0Equiv :=
  actionRegularH0Equiv (S.TangentAlgebra k) C.nativeCutVariables
end NSP14.NumericalSemigroup.LinearCutData
