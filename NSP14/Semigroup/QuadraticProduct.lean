module

public import NSP14.Semigroup.ActualFinite
public import NSP14.Semigroup.LiveSplit
public import NSP14.Semigroup.HeadGradedAlgebra
public import NSP14.Green.HyperplaneFlag

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open scoped Classical BigOperators

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [Field k]

/-- Actual multiplication A₁×A₁→A₂. -/
noncomputable def quadraticProduct : S.headDegree k 1 →ₗ[k] S.headDegree k 1 →ₗ[k] S.headDegree k 2 where
  toFun (a : S.headDegree k 1) :=
    { toFun := fun (b : S.headDegree k 1) => ⟨a.val * b.val, S.headDegree_mul_mem k (n := 1) (p := 1) a.property b.property⟩
      map_add' := by intro b c; apply Subtype.ext; exact mul_add _ _ _
      map_smul' := by
        intro r b
        apply Subtype.ext
        change a.val * (r • b.val) = r • (a.val * b.val)
        exact mul_smul_comm _ _ _ }
  map_add' a b := by apply LinearMap.ext; intro c; apply Subtype.ext; exact add_mul _ _ _
  map_smul' r a := by apply LinearMap.ext; intro b; apply Subtype.ext; exact smul_mul_assoc _ _ _

theorem quadraticProduct_symmetric (a b : S.headDegree k 1) :
    S.quadraticProduct k a b = S.quadraticProduct k b a := Subtype.ext (mul_comm _ _)

theorem headDegree_two_basis_product (h : S.HeadExponent) (hh : S.order h.val.val = 2) :
    ∃ a b : S.headDegree k 1, a.val * b.val = S.headBasis k h := by
  obtain ⟨u,v,he,hu,hv⟩ := S.order_live_split h.val 1 (by omega)
  have hv1 : S.order v.val = 1 := by rw [hh] at hv; exact hv
  let a : S.headDegree k 1 := ⟨S.headMonomial k u,S.headMonomial_mem_degree k u 1 hu⟩
  let b : S.headDegree k 1 := ⟨S.headMonomial k v,S.headMonomial_mem_degree k v 1 hv1⟩
  refine ⟨a,b,?_⟩
  change S.headMonomial k u * S.headMonomial k v = S.headBasis k h
  have hlive : S.order (u.val+v.val) = S.order u.val + S.order v.val := by
    have heval : h.val.val = u.val + v.val := congrArg Subtype.val he
    rw [← heval, hh, hu, hv1]
  rw [S.headMonomial_mul_live k u v hlive, ← he, S.headMonomial_eq_basis]

/-- Every actual degree-two vector lies in the span of actual products. -/
theorem quadraticProduct_spans : NSP14.Green.bilinearSpan (S.quadraticProduct k) = ⊤ := by
  let U := (NSP14.Green.bilinearSpan (S.quadraticProduct k)).map (S.headDegree k 2).subtype
  have hle : S.headDegree k 2 ≤ U := by
    intro a ha
    have hs : ∀ h ∈ (S.headQuotientEquiv k a).support, S.order h.val.val = 2 :=
      (Finsupp.mem_supported k _).1 ((S.mem_headDegree_coordinates k 2 a).1 ha)
    rw [← S.head_expansion k a, Finsupp.sum]
    apply U.sum_mem
    intro h hh
    apply U.smul_mem
    obtain ⟨b,c,hbc⟩ := S.headDegree_two_basis_product k h (hs h hh)
    exact ⟨S.quadraticProduct k b c, Submodule.subset_span ⟨b,c,rfl⟩, hbc⟩
  apply top_unique
  intro a _
  obtain ⟨b,hb,he⟩ := hle a.property
  have heq : b = a := Subtype.ext he
  exact heq ▸ hb

theorem headDegree_one_finrank : Module.finrank k (S.headDegree k 1) = S.embeddingDimension - 1 := by
  rw [S.headDegree_low_finrank k 1 (by decide), S.degree_one_card]

theorem headDegree_two_finrank : Module.finrank k (S.headDegree k 2) = (S.degreeSet 2).card :=
  S.headDegree_low_finrank k 2 le_rfl

end NSP14.NumericalSemigroup
