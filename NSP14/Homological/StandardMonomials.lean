module

public import Mathlib.RingTheory.MvPolynomial.Groebner
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

open scoped Classical

namespace NSP14.Homological

variable {k σ : Type*} [Field k] (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ k))

/-- Standards are defined using every nonzero ideal element, not just a proposed generating family. -/
def StandardExponent : Set (σ →₀ ℕ) :=
  {d | ∀ p ∈ I, p≠0 → ¬m.degree p≤d}

noncomputable def normalSpace : Submodule k (MvPolynomial σ k) :=
  (Finsupp.supported k k (StandardExponent m I)).comap
    (AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap

theorem normal_form_exists (f : MvPolynomial σ k) :
    ∃ r : MvPolynomial σ k, r∈normalSpace m I ∧ f-r∈I := by
  let B : Set (MvPolynomial σ k) := {p | p∈I ∧ p≠0}
  obtain ⟨g,r,he,_,hr⟩ := m.div_set (B := B)
    (fun b hb => isUnit_iff_ne_zero.mpr (m.leadingCoeff_ne_zero_iff.mpr hb.2)) f
  refine ⟨r,?_,?_⟩
  · change r.coeff ∈ Finsupp.supported k k (StandardExponent m I)
    rw [Finsupp.mem_supported]
    intro d hd p hp hp0
    exact hr d hd p ⟨hp,hp0⟩
  · have hg : Finsupp.linearCombination (MvPolynomial σ k) (fun b : B => b.val) g ∈ I := by
      change g.sum (fun b c => c*b.val) ∈ I
      exact I.sum_mem (fun b _ => I.mul_mem_left _ b.property.1)
    have he' : f-r=Finsupp.linearCombination (MvPolynomial σ k) (fun b : B => b.val) g := by
      rw [he]; abel
    exact he' ▸ hg

theorem normal_in_ideal_eq_zero (r : MvPolynomial σ k) (hr : r∈normalSpace m I) (hi : r∈I) : r=0 := by
  by_contra hne
  have hs : r.coeff ∈ Finsupp.supported k k (StandardExponent m I) := hr
  have hd : m.degree r∈r.support := m.degree_mem_support hne
  exact ((Finsupp.mem_supported k _).1 hs hd) r hi hne le_rfl

noncomputable def normalQuotientMap : normalSpace m I →ₗ[k] (MvPolynomial σ k ⧸ I) :=
  (Ideal.Quotient.mkₐ k I).toLinearMap.comp (normalSpace m I).subtype

theorem normalQuotientMap_injective : Function.Injective (normalQuotientMap m I) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro a ha
  have hi : a.val∈I := (Ideal.Quotient.eq_zero_iff_mem).1 ha
  have hz := normal_in_ideal_eq_zero m I a.val a.property hi
  exact Subtype.ext hz

theorem normalQuotientMap_surjective : Function.Surjective (normalQuotientMap m I) := by
  intro a
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mkₐ_surjective k I a
  obtain ⟨r,hr,hfr⟩ := normal_form_exists m I f
  refine ⟨⟨r,hr⟩,?_⟩
  change Ideal.Quotient.mk I r=Ideal.Quotient.mk I f
  rw [Ideal.Quotient.eq]
  simpa only [neg_sub] using I.neg_mem hfr

/-- Actual quotient classes have unique standard-supported normal forms. -/
noncomputable def standardMonomialQuotientEquiv : normalSpace m I ≃ₗ[k] (MvPolynomial σ k ⧸ I) :=
  LinearEquiv.ofBijective (normalQuotientMap m I)
    ⟨normalQuotientMap_injective m I,normalQuotientMap_surjective m I⟩

noncomputable def normalCoordinates : normalSpace m I ≃ₗ[k] (StandardExponent m I →₀ k) where
  toFun a := Finsupp.subtypeDomain _ a.val.coeff
  invFun f := ⟨AddMonoidAlgebra.ofCoeff f.extendDomain,f.support_extendDomain_subset⟩
  left_inv a := by
    apply Subtype.ext
    apply AddMonoidAlgebra.coeff_injective
    rw [AddMonoidAlgebra.coeff_ofCoeff,Finsupp.extendDomain_subtypeDomain]
    exact (Finsupp.mem_supported k _).1 a.property
  right_inv f := by
    change Finsupp.subtypeDomain _ f.extendDomain=f
    exact Finsupp.subtypeDomain_extendDomain f
  map_add' a b := Finsupp.subtypeDomain_add
  map_smul' c a := by ext d; rfl

noncomputable def standardMonomialBasis :
    Module.Basis (StandardExponent m I) k (MvPolynomial σ k ⧸ I) :=
  Finsupp.basisSingleOne.map ((normalCoordinates m I).symm.trans (standardMonomialQuotientEquiv m I))

/-- The quotient basis consists of the actual standard monomial classes. -/
theorem standardMonomialBasis_apply (d : StandardExponent m I) :
    standardMonomialBasis m I d = Ideal.Quotient.mk I (MvPolynomial.monomial d.val (1 : k)) := by
  change Ideal.Quotient.mk I (AddMonoidAlgebra.ofCoeff (Finsupp.single d (1 : k)).extendDomain) = _
  rw [Finsupp.extendDomain_single]
  rfl

end NSP14.Homological
