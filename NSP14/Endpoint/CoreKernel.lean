module
public import NSP14.Endpoint.CoreMap
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

theorem liveValue_injective (p q : D.corePoints)
    (hp : D.coreDegree p=D.source.order (D.coreValue p).val)
    (hq : D.coreDegree q=D.source.order (D.coreValue q).val)
    (hv : D.coreValue p=D.coreValue q) : p=q := by
  have hn : p.val.1=q.val.1 := hp.trans ((congrArg (fun a : D.source.carrier => D.source.order a.val) hv).trans hq.symm)
  have he := congrArg Subtype.val hv
  change p.val.1*D.m+p.val.2*D.d=q.val.1*D.m+q.val.2*D.d at he
  have hB : p.val.2=q.val.2 := by have := D.d_pos;rw [hn] at he;nlinarith
  exact Subtype.ext (Prod.ext hn hB)

variable (k : Type) [Field k]

theorem coreInitial_live (p : D.corePoints) (hp : D.coreDegree p=D.source.order (D.coreValue p).val) :
    D.coreInitial k p=D.source.initialMonomial k (D.coreValue p) := by
  unfold coreInitial NumericalSemigroup.initialMonomial
  apply DirectSum.of_eq_of_gradedMonoid_eq
  apply D.source.homogeneous_mk_eq k hp
  rfl

theorem coreToG_live_coefficient (p : D.corePoints)
    (hp : D.coreDegree p=D.source.order (D.coreValue p).val) (f : D.Core k) :
    D.source.tangentCoordinates k (D.coreToG k f) (D.coreValue p)=f.coeff p := by
  induction f using AddMonoidAlgebra.induction_on with
  | of q =>
    change D.source.tangentCoordinates k (D.coreToG k (D.coreMonomial k q)) (D.coreValue p)=_
    by_cases hq : D.coreDegree q=D.source.order (D.coreValue q).val
    · rw [D.coreToG_monomial,D.coreInitial_live k q hq,D.source.tangentCoordinates_initial]
      have hi : D.coreValue q=D.coreValue p ↔ q=p :=
        ⟨D.liveValue_injective q p hq hp,fun h => congrArg D.coreValue h⟩
      simp only [Finsupp.single_apply,AddMonoidAlgebra.of_apply,toAdd_ofAdd,AddMonoidAlgebra.coeff_single,hi]
    · have hlt : D.coreDegree q<D.source.order (D.coreValue q).val := by have := D.coreDegree_le_order q;omega
      rw [(D.coreToG_monomial_zero_iff k q).mpr hlt,map_zero,Finsupp.zero_apply]
      have hqp : q≠p := by rintro rfl;exact hq hp
      simp only [AddMonoidAlgebra.of_apply,toAdd_ofAdd,AddMonoidAlgebra.coeff_single,Finsupp.single_apply,hqp,ite_false]
  | add a b ha hb =>
    simp only [map_add,Finsupp.add_apply,AddMonoidAlgebra.coeff_add]
    rw [ha,hb]
  | smul c a ha =>
    simp only [map_smul,Finsupp.smul_apply,AddMonoidAlgebra.coeff_smul]
    rw [ha]

/-- Exact linear kernel of the actual graded ring surjection: only the
core monomials killed by a genuinely longer representation occur. -/
theorem coreToG_kernel_span : (D.coreToG k).toLinearMap.ker=
    Submodule.span k ((D.coreMonomial k) '' {p | D.coreDegree p<D.source.order (D.coreValue p).val}) := by
  apply le_antisymm
  · change (D.coreToG k).toLinearMap.ker ≤
      Submodule.span k ((fun p => AddMonoidAlgebra.single p (1:k)) '' {p | D.coreDegree p<D.source.order (D.coreValue p).val})
    rw [← AddMonoidAlgebra.supported_eq_span_single]
    intro f hf
    rw [AddMonoidAlgebra.mem_supported']
    intro p hp
    have he : D.coreDegree p=D.source.order (D.coreValue p).val := by
      have := D.coreDegree_le_order p
      change ¬D.coreDegree p<D.source.order (D.coreValue p).val at hp
      omega
    have hc := D.coreToG_live_coefficient k p he f
    change D.coreToG k f=0 at hf
    rw [hf,map_zero,Finsupp.zero_apply] at hc
    exact hc.symm
  · apply Submodule.span_le.mpr
    rintro _ ⟨p,hp,rfl⟩
    exact (D.coreToG_monomial_zero_iff k p).mpr hp
end NSP14.Endpoint.Data
