module
public import NSP14.Endpoint.StandardArtinFinite
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Sym.NatCard
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open NSP14.Homological
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Endpoint
variable (σ : Type) [Fintype σ] [LinearOrder σ]

omit [Fintype σ] in
theorem degree_two_pair (β : σ →₀ ℕ) (hβ : β.degree=2) :
    ∃ x y : σ,β=Finsupp.single x 1+Finsupp.single y 1 := by
  have hc : β.toMultiset.card=2 := by
    rw [Finsupp.card_toMultiset]
    exact hβ
  obtain ⟨x,y,hxy⟩ := Multiset.card_eq_two.mp hc
  refine ⟨x,y,?_⟩
  apply Multiset.toFinsupp.symm.injective
  change β.toMultiset=(Finsupp.single x 1+Finsupp.single y 1).toMultiset
  rw [Finsupp.toMultiset_add,Finsupp.toMultiset_single,Finsupp.toMultiset_single]
  simpa using hxy

variable (k : Type) [Field k] (I : Ideal (MvPolynomial σ k))
abbrev ArtinQuadraticIndex := {p : StandardExponent MonomialOrder.degLex I // p.val.degree=2}
noncomputable def artinQuadraticPair (p : ArtinQuadraticIndex σ k I) : σ×σ :=
  ⟨(degree_two_pair σ p.val.val p.property).choose,
    (degree_two_pair σ p.val.val p.property).choose_spec.choose⟩
theorem artinQuadraticPair_sum (p : ArtinQuadraticIndex σ k I) :
    p.val.val=Finsupp.single (artinQuadraticPair σ k I p).1 1+
      Finsupp.single (artinQuadraticPair σ k I p).2 1 :=
  (degree_two_pair σ p.val.val p.property).choose_spec.choose_spec
noncomputable def artinQuadraticLabel (p : ArtinQuadraticIndex σ k I) : Sym2 σ :=
  s((artinQuadraticPair σ k I p).1,(artinQuadraticPair σ k I p).2)
theorem artinQuadraticLabel_injective : Function.Injective (artinQuadraticLabel σ k I) := by
  intro a b h
  have he := Sym2.rel_iff.mp (Sym2.exact h)
  apply Subtype.ext
  apply Subtype.ext
  rw [artinQuadraticPair_sum σ k I a,artinQuadraticPair_sum σ k I b]
  rcases he with ⟨h1,h2⟩|⟨h1,h2⟩
  · rw [h1,h2]
  · rw [h1,h2,add_comm]

variable [Module.Finite k (MvPolynomial σ k ⧸ I)]
  (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
theorem artinHilbert_two_bound : artinHilbert k σ I hI 2≤(Fintype.card σ+1).choose 2 := by
  rw [artinHilbert_card]
  have h := Nat.card_le_card_of_injective (artinQuadraticLabel σ k I) (artinQuadraticLabel_injective σ k I)
  rw [Sym2.natCard,show Nat.card σ=Fintype.card σ from Nat.card_eq_fintype_card] at h
  exact h
end NSP14.Endpoint
