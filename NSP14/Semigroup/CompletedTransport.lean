module

public import NSP14.Semigroup.CompletedComparison

@[expose] public section

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k] [Nontrivial k]

noncomputable def formalXElement : S.FormalTangentAlgebra k := S.formalInitialMonomial k S.multiplicityExponent

noncomputable def formalXMultiply : S.FormalTangentAlgebra k →ₗ[k] S.FormalTangentAlgebra k :=
  (LinearMap.mul k (S.FormalTangentAlgebra k)).flip (S.formalXElement k)

omit [Nontrivial k] in
theorem completedGradedAlgEquiv_x : S.completedGradedAlgEquiv k (S.xElement k) = S.formalXElement k :=
  S.completedGradedAlgEquiv_initial k S.multiplicityExponent

omit [Nontrivial k] in
theorem completedGradedAlgEquiv_xMultiply (a : S.TangentAlgebra k) :
    S.completedGradedAlgEquiv k (S.xMultiply k a) =
      S.formalXMultiply k (S.completedGradedAlgEquiv k a) := by
  change S.completedGradedAlgEquiv k (a*S.xElement k) = _
  rw [map_mul,S.completedGradedAlgEquiv_x]
  rfl

noncomputable def completedKernelEquiv : (S.xMultiply k).ker ≃ₗ[k] (S.formalXMultiply k).ker where
  toFun a := ⟨S.completedGradedAlgEquiv k a.val, by
    change S.formalXMultiply k (S.completedGradedAlgEquiv k a.val) = 0
    rw [← S.completedGradedAlgEquiv_xMultiply, show S.xMultiply k a.val=0 from a.property, map_zero]⟩
  invFun b := ⟨(S.completedGradedAlgEquiv k).symm b.val, by
    apply (S.completedGradedAlgEquiv k).injective
    rw [S.completedGradedAlgEquiv_xMultiply, AlgEquiv.apply_symm_apply, map_zero]
    exact b.property⟩
  left_inv a := Subtype.ext ((S.completedGradedAlgEquiv k).symm_apply_apply a.val)
  right_inv b := Subtype.ext ((S.completedGradedAlgEquiv k).apply_symm_apply b.val)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

noncomputable def formalXIdeal : Ideal (S.FormalTangentAlgebra k) := Ideal.span {S.formalXElement k}

omit [Nontrivial k] in
theorem formalXIdeal_eq_map : S.formalXIdeal k =
    (S.xIdeal k).map (S.completedGradedAlgEquiv k).toRingEquiv.toRingHom := by
  rw [xIdeal,Ideal.map_span,Set.image_singleton]
  change Ideal.span {S.formalXElement k} = Ideal.span {S.completedGradedAlgEquiv k (S.xElement k)}
  rw [S.completedGradedAlgEquiv_x]

abbrev FormalHeadAlgebra := S.FormalTangentAlgebra k ⧸ S.formalXIdeal k

noncomputable def completedHeadAlgEquiv : S.HeadAlgebra k ≃ₐ[k] S.FormalHeadAlgebra k :=
  Ideal.quotientEquivAlg (S.xIdeal k) (S.formalXIdeal k) (S.completedGradedAlgEquiv k)
    (S.formalXIdeal_eq_map k)

/-- N transported through the natural actual quotient comparison. -/
noncomputable def formalNonAperyIdeal : Ideal (S.FormalHeadAlgebra k) :=
  (S.nonAperyIdeal k).map (S.completedHeadAlgEquiv k).toRingEquiv.toRingHom

abbrev FormalAperyAlgebra := S.FormalHeadAlgebra k ⧸ S.formalNonAperyIdeal k

noncomputable def completedAperyAlgEquiv : S.AperyAlgebra k ≃ₐ[k] S.FormalAperyAlgebra k :=
  Ideal.quotientEquivAlg (S.nonAperyIdeal k) (S.formalNonAperyIdeal k) (S.completedHeadAlgEquiv k) rfl

omit [Nontrivial k] in
theorem completedHeadAlgEquiv_mk (a : S.TangentAlgebra k) :
    S.completedHeadAlgEquiv k (S.toHeadAlgebra k a) =
      Ideal.Quotient.mk (S.formalXIdeal k) (S.completedGradedAlgEquiv k a) := rfl

theorem completedAperyAlgEquiv_mk (a : S.HeadAlgebra k) :
    S.completedAperyAlgEquiv k (Ideal.Quotient.mk (S.nonAperyIdeal k) a) =
      Ideal.Quotient.mk (S.formalNonAperyIdeal k) (S.completedHeadAlgEquiv k a) := rfl

end NSP14.NumericalSemigroup
