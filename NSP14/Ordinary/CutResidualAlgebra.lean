module
public import NSP14.Ordinary.CutBFullAction
public import NSP14.Homological.FirstOrderResidual
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open NSP14.Homological
open scoped Classical BigOperators
namespace NSP14.NumericalSemigroup.LinearCutData
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)

theorem firstOrderHeadExtendedEquiv_fst (a : S.FirstOrderHead k) :
    (C.firstOrderHeadExtendedEquiv a).fst=S.firstOrderConstant k a := rfl

theorem firstOrderHeadExtendedEquiv_snd (a : S.FirstOrderHead k) :
    (C.firstOrderHeadExtendedEquiv a).snd=C.extendedHeadBasis.equivFun (S.firstOrderLinearPart k a) := by
  change C.extendedCoefficientEquiv.symm (S.headLinearCoordinates k (S.firstOrderLinearPart k a))=_
  simp [extendedCoefficientEquiv]

noncomputable def headToResidual : S.HeadAlgebra k →ₐ[k] TrivSqZeroExt k (Fin C.complementRank → k) :=
  (firstOrderDropPrefix k S.actualCutRank C.complementRank).comp
    (C.firstOrderHeadExtendedEquiv.toAlgHom.comp (Ideal.Quotient.mkₐ k (S.highIdeal k 2)))

theorem headToResidual_fst (a : S.HeadAlgebra k) : (C.headToResidual a).fst=S.headConstant k a := by
  change (TrivSqZeroExt.map (complementCoordinates k S.actualCutRank C.complementRank)
    (C.firstOrderHeadExtendedEquiv (Ideal.Quotient.mk (S.highIdeal k 2) a))).fst=_
  rw [TrivSqZeroExt.fst_map,C.firstOrderHeadExtendedEquiv_fst,S.firstOrderConstant_mk]

theorem headToResidual_snd (a : S.HeadAlgebra k) (i : Fin C.complementRank) :
    (C.headToResidual a).snd i=C.extendedHeadBasis.equivFun (S.headLinearPart k a) (Fin.natAdd S.actualCutRank i) := by
  change (TrivSqZeroExt.map (complementCoordinates k S.actualCutRank C.complementRank)
    (C.firstOrderHeadExtendedEquiv (Ideal.Quotient.mk (S.highIdeal k 2) a))).snd i=_
  rw [TrivSqZeroExt.snd_map,C.firstOrderHeadExtendedEquiv_snd,S.firstOrderLinearPart_mk]
  rfl

theorem headToResidual_form (v : Fin S.actualCutRank) : C.headToResidual (C.forms v).val=0 := by
  change firstOrderDropPrefix k S.actualCutRank C.complementRank
    (C.firstOrderHeadExtendedEquiv (Ideal.Quotient.mk (S.highIdeal k 2) (C.forms v).val))=0
  rw [C.firstOrderHeadExtendedEquiv_lambda,firstOrderDropPrefix_lambda]

theorem headToResidual_surjective : Function.Surjective C.headToResidual := by
  have hq : Function.Surjective (Ideal.Quotient.mk (S.highIdeal k 2)) := Ideal.Quotient.mk_surjective
  exact (firstOrderDropPrefix_surjective k S.actualCutRank C.complementRank).comp
    (C.firstOrderHeadExtendedEquiv.surjective.comp hq)

theorem highIdeal_le_cut : S.highIdeal k 2 ≤ S.linearCutIdeal k C.forms S.actualCutRank := by
  intro a ha
  have hs : ∀ h ∈ (S.headQuotientEquiv k a).support,2 ≤ S.order h.val.val :=
    (Finsupp.mem_supported k _).mp ha
  rw [← S.head_expansion k a,Finsupp.sum]
  apply ((S.linearCutIdeal k C.forms S.actualCutRank).restrictScalars k).sum_mem
  intro h hh
  apply ((S.linearCutIdeal k C.forms S.actualCutRank).restrictScalars k).smul_mem
  apply NSP14.NumericalSemigroup.LinearCutData.high_mem S k C (S.order h.val.val) (hs h hh)
  rw [← S.headMonomial_eq_basis k h]
  exact S.headMonomial_mem_degree k h.val _ rfl

theorem linearPart_mem_cut (c : S.headDegree k 1)
    (hc : ∀ i : Fin C.complementRank,C.extendedHeadBasis.equivFun c (Fin.natAdd S.actualCutRank i)=0) :
    c.val ∈ S.linearCutIdeal k C.forms S.actualCutRank := by
  have he : c=∑ v : Fin S.actualCutRank,
      C.extendedHeadBasis.equivFun c (Fin.castAdd C.complementRank v) • C.forms v := by
    calc
      c = ∑ i,C.extendedHeadBasis.equivFun c i • C.extendedHeadBasis i := (C.extendedHeadBasis.sum_equivFun c).symm
      _ = _ := by
        rw [Fin.sum_univ_add]
        simp only [hc,zero_smul,Finset.sum_const_zero,add_zero,C.extendedHeadBasis_prefix]
  rw [he]
  change (S.headDegree k 1).subtype (∑ v : Fin S.actualCutRank,
    C.extendedHeadBasis.equivFun c (Fin.castAdd C.complementRank v) • C.forms v) ∈ S.linearCutIdeal k C.forms S.actualCutRank
  rw [map_sum]
  apply ((S.linearCutIdeal k C.forms S.actualCutRank).restrictScalars k).sum_mem
  intro v _
  rw [map_smul]
  apply ((S.linearCutIdeal k C.forms S.actualCutRank).restrictScalars k).smul_mem
  exact Ideal.subset_span ⟨v,v.isLt,rfl⟩

theorem headToResidual_ker : RingHom.ker C.headToResidual.toRingHom=S.linearCutIdeal k C.forms S.actualCutRank := by
  apply le_antisymm
  · intro a ha
    have hz : C.headToResidual a=0 := ha
    have h0 : S.headConstant k a=0 := by
      have h := congrArg (fun x : TrivSqZeroExt k (Fin C.complementRank → k) => x.fst) hz
      rw [C.headToResidual_fst] at h
      exact h
    have hlin : (S.headLinearPart k a).val ∈ S.linearCutIdeal k C.forms S.actualCutRank := by
      apply C.linearPart_mem_cut
      intro i
      have h := congrArg (fun x : TrivSqZeroExt k (Fin C.complementRank → k) => x.snd i) hz
      rw [C.headToResidual_snd] at h
      exact h
    have hr := C.highIdeal_le_cut (S.head_remainder_high k a)
    rw [S.headGradeProject_zero_eq,h0] at hr
    rw [zero_smul k (1 : S.HeadAlgebra k)] at hr
    rw [sub_zero] at hr
    have he := (S.linearCutIdeal k C.forms S.actualCutRank).add_mem hr hlin
    change a-S.headGradeProject k 1 a+S.headGradeProject k 1 a ∈ S.linearCutIdeal k C.forms S.actualCutRank at he
    rw [sub_add_cancel] at he
    exact he
  · apply Ideal.span_le.mpr
    rintro a ⟨i,hi,he⟩
    change C.headToResidual a=0
    rw [he,C.headToResidual_form]

/-- The actual square-zero cut quotient, as an algebra with complement
coordinates. Its omitted lambda coordinates are exactly the cut ideal. -/
noncomputable def cutResidualEquiv :
    (S.HeadAlgebra k ⧸ S.linearCutIdeal k C.forms S.actualCutRank) ≃ₐ[k]
      TrivSqZeroExt k (Fin C.complementRank → k) :=
  (Ideal.quotientEquivAlgOfEq k C.headToResidual_ker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective C.headToResidual_surjective)
end NSP14.NumericalSemigroup.LinearCutData
