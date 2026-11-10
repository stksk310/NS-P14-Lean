module
public import NSP14.Semigroup.HighIdeal
public import NSP14.Semigroup.CutBasis
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup)

abbrev LowHeadExponent := {h : S.HeadExponent //S.order h.val.val < 2}
noncomputable def zeroHeadExponent : S.HeadExponent :=
  ⟨⟨0,S.zero_mem⟩,S.apery_head S.zero_mem_apery⟩
noncomputable def lowHeadOfOption : Option S.NonXAtom → S.LowHeadExponent
  | none => ⟨S.zeroHeadExponent,by change S.order 0<2;rw [S.order_zero];decide⟩
  | some a => ⟨⟨a.val,S.apery_head (S.atom_apery a.property.1 a.property.2)⟩,
      by change S.order a.val.val<2;rw [S.atom_order a.property.1];decide⟩

noncomputable def lowHeadToOption (h : S.LowHeadExponent) : Option S.NonXAtom :=
  if hz : h.val.val.val=0 then none else some
    ⟨h.val.val,(S.order_one_iff_atom h.val.val.property).mp (by
      have hp := S.order_pos h.val.val.property (by omega)
      have ht := h.property
      omega),by
      intro hm
      apply h.val.property.2
      refine ⟨0,S.zero_mem,?_,?_⟩
      · omega
      · rw [hm,S.order_zero,S.order_multiplicity]⟩

noncomputable def lowHeadIndexEquiv : Option S.NonXAtom ≃ S.LowHeadExponent where
  toFun := S.lowHeadOfOption
  invFun := S.lowHeadToOption
  left_inv a := by
    cases a with
    | none => simp [lowHeadToOption,lowHeadOfOption,zeroHeadExponent]
    | some a =>
      have hn : a.val.val ≠ 0 := by have hp := a.property.1.2.1;omega
      simp only [lowHeadOfOption,lowHeadToOption,hn,dite_false]
      exact congrArg some (Subtype.ext rfl)
  right_inv h := by
    by_cases hz : h.val.val.val=0
    · simp only [lowHeadToOption,hz,dite_true,lowHeadOfOption]
      apply Subtype.ext
      apply Subtype.ext
      exact Subtype.ext hz.symm
    · simp only [lowHeadToOption,hz,dite_false,lowHeadOfOption]
      exact Subtype.ext (Subtype.ext rfl)

theorem lowHeadExponent_card : Fintype.card S.LowHeadExponent=S.embeddingDimension := by
  rw [← Fintype.card_congr S.lowHeadIndexEquiv,Fintype.card_option,S.nonXAtom_card]
  have := S.embeddingDimension_pos
  omega

variable (k : Type) [Field k]

/-- Actual quotient A/A_{>=2}, before any numerical profile is assigned. -/
abbrev FirstOrderHead := S.HeadAlgebra k ⧸ S.highIdeal k 2

noncomputable def headLowProjection : S.HeadAlgebra k →ₗ[k] (S.LowHeadExponent →₀ k) :=
  (Finsupp.lsubtypeDomain {h : S.HeadExponent | S.order h.val.val < 2}).comp
    (S.headQuotientEquiv k).toLinearMap

theorem headLowProjection_ker : (S.headLowProjection k).ker=(S.highIdeal k 2).restrictScalars k := by
  ext a
  rw [LinearMap.mem_ker]
  change Finsupp.subtypeDomain _ (S.headQuotientEquiv k a)=0 ↔
    S.headQuotientEquiv k a ∈ Finsupp.supported k k {h : S.HeadExponent | 2 ≤ S.order h.val.val}
  rw [Finsupp.subtypeDomain_eq_zero_iff',Finsupp.mem_supported']
  simp only [Set.mem_ofPred_eq,not_le]

theorem headLowProjection_surjective : Function.Surjective (S.headLowProjection k) := by
  intro f
  refine ⟨(S.headQuotientEquiv k).symm f.extendDomain,?_⟩
  change Finsupp.subtypeDomain _ ((S.headQuotientEquiv k) ((S.headQuotientEquiv k).symm f.extendDomain))=f
  rw [LinearEquiv.apply_symm_apply,Finsupp.subtypeDomain_extendDomain]

noncomputable def firstOrderHeadCoordinates :
    S.FirstOrderHead k ≃ₗ[k] (S.LowHeadExponent →₀ k) :=
  (Submodule.quotEquivOfEq _ _ (S.headLowProjection_ker k).symm).trans
    ((S.headLowProjection k).quotKerEquivOfSurjective (S.headLowProjection_surjective k))

theorem firstOrderHeadCoordinates_mk (a : S.HeadAlgebra k) :
    S.firstOrderHeadCoordinates k (Ideal.Quotient.mk (S.highIdeal k 2) a)=S.headLowProjection k a := rfl

noncomputable def firstOrderHeadBasis : Module.Basis S.LowHeadExponent k (S.FirstOrderHead k) :=
  Finsupp.basisSingleOne.map (S.firstOrderHeadCoordinates k).symm

noncomputable instance firstOrderHeadFinite : Module.Finite k (S.FirstOrderHead k) :=
  Module.Finite.of_basis (S.firstOrderHeadBasis k)

theorem firstOrderHead_finrank : Module.finrank k (S.FirstOrderHead k)=S.embeddingDimension := by
  rw [Module.finrank_eq_card_basis (S.firstOrderHeadBasis k),S.lowHeadExponent_card]
end NSP14.NumericalSemigroup
