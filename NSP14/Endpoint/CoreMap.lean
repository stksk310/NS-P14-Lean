module
public import NSP14.Endpoint.Core
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

noncomputable def coreAtomPoint (a : D.source.AtomExponent) : D.corePoints :=
  D.coreGeneratorPoint (D.atomVariableEquiv.symm a)

theorem coreAtomPoint_degree (a : D.source.AtomExponent) : D.coreDegree (D.coreAtomPoint a)=1 := rfl

theorem coreGeneratorPoint_value (b : D.Variables) :
    D.coreValue (D.coreGeneratorPoint b)=(D.atomVariable b).val := by
  apply Subtype.ext
  change 1*D.m+b.val*D.d=D.m+b.val*D.d
  rw [one_mul]

theorem coreAtomPoint_value (a : D.source.AtomExponent) : D.coreValue (D.coreAtomPoint a)=a.val := by
  rw [coreAtomPoint,D.coreGeneratorPoint_value]
  change (D.atomVariableEquiv (D.atomVariableEquiv.symm a)).val=a.val
  rw [Equiv.apply_symm_apply]

variable (k : Type) [Field k]

theorem exists_coreInitial (a : D.source.carrier) :
    ∃ p : D.corePoints,D.coreInitial k p=D.source.initialMonomial k a := by
  obtain ⟨f,hf,hs⟩ := D.source.order_realized_by_atoms a.property
  let pts : Fin (D.source.order a.val) → D.corePoints :=
    fun i => D.coreAtomPoint ⟨⟨f i,(hf i).1⟩,hf i⟩
  let p : D.corePoints := ∑ i,pts i
  have hpd : D.coreDegree p=D.source.order a.val := by
    simp only [p,map_sum,pts,D.coreAtomPoint_degree,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,smul_eq_mul,mul_one]
  have hpv : D.coreValue p=a := by
    apply Subtype.ext
    simp only [p,map_sum,pts,D.coreAtomPoint_value]
    change D.source.carrier.subtype (∑ i,(⟨f i,(hf i).1⟩ : D.source.carrier))=a.val
    rw [map_sum]
    exact hs
  refine ⟨p,?_⟩
  unfold coreInitial NumericalSemigroup.initialMonomial
  apply DirectSum.of_eq_of_gradedMonoid_eq
  apply D.source.homogeneous_mk_eq k hpd
  change AddMonoidAlgebra.single (D.coreValue p) (1:k)=AddMonoidAlgebra.single a (1:k)
  rw [hpv]

/-- Surjectivity onto the original actual graded algebra, from maximal
minimal-atom representations and its genuine monomial basis. -/
theorem coreToG_surjective : Function.Surjective (D.coreToG k) := by
  have hr : (D.coreToG k).toLinearMap.range=⊤ := by
    apply top_unique
    rw [← (D.source.tangentBasis k).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    rw [D.source.tangentBasis_eq_initial]
    obtain ⟨p,hp⟩ := D.exists_coreInitial k a
    exact ⟨D.coreMonomial k p,(D.coreToG_monomial k p).trans hp⟩
  exact LinearMap.range_eq_top.mp hr

noncomputable def fullToCore : D.FullRing k →ₐ[k] D.Core k :=
  MvPolynomial.aeval (fun b => D.coreMonomial k (D.coreGeneratorPoint b))

theorem coreInitial_generator (b : D.Variables) :
    D.coreInitial k (D.coreGeneratorPoint b)=D.source.initialMonomial k (D.atomVariable b).val := by
  have ho : D.source.order (D.atomVariable b).val.val=1 := D.source.atom_order (D.atomVariable b).property
  unfold coreInitial NumericalSemigroup.initialMonomial
  apply DirectSum.of_eq_of_gradedMonoid_eq
  apply D.source.homogeneous_mk_eq k (show D.coreDegree (D.coreGeneratorPoint b)=D.source.order (D.atomVariable b).val.val from ho.symm)
  change AddMonoidAlgebra.single (D.coreValue (D.coreGeneratorPoint b)) (1:k)=AddMonoidAlgebra.single (D.atomVariable b).val (1:k)
  rw [D.coreGeneratorPoint_value]

theorem coreToG_fullToCore : (D.coreToG k).comp (D.fullToCore k)=D.fullToG k := by
  apply MvPolynomial.algHom_ext
  intro b
  simp only [AlgHom.comp_apply,fullToCore,MvPolynomial.aeval_X,D.coreToG_monomial,
    D.coreInitial_generator,D.fullToG_X]
end NSP14.Endpoint.Data
