module

public import NSP14.Semigroup.GradedProduct
public import NSP14.Semigroup.Heads

@[expose] public section

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k]

noncomputable def multiplicityExponent : S.carrier := ⟨S.multiplicity, S.multiplicity_mem⟩

/-- Multiplication by the initial class of t^m on homogeneous pieces. -/
noncomputable def xAction (n : ℕ) : S.GradedPiece k n →ₗ[k] S.GradedPiece k (n + 1) :=
  (S.gradedMul k n 1).flip
    (S.monomialClass k 1 S.multiplicityExponent (by exact le_of_eq S.order_multiplicity.symm))

theorem xAction_monomial_eq_zero_iff [Nontrivial k] (x : S.carrier) :
    S.xAction k (S.order x.val) (S.monomialClass k _ x le_rfl) = 0 ↔
      S.Terminal x.val := by
  change S.gradedMul k (S.order x.val) 1 (S.monomialClass k _ x le_rfl)
    (S.monomialClass k 1 S.multiplicityExponent
      (by exact le_of_eq S.order_multiplicity.symm)) = 0 ↔ _
  rw [S.gradedMul_monomial_layers, S.monomialClass_eq_zero_iff]
  exact ⟨fun h => ⟨x.property, h⟩, fun h => h.2⟩

theorem xAction_monomial_ne_zero_iff [Nontrivial k] (x : S.carrier) :
    S.xAction k (S.order x.val) (S.monomialClass k _ x le_rfl) ≠ 0 ↔
      S.order (x.val + S.multiplicity) = S.order x.val + 1 := by
  simp only [ne_eq, S.xAction_monomial_eq_zero_iff, Terminal,
    show x.val ∈ S from x.property, true_and]
  have := S.order_add_multiplicity x.property
  omega

theorem monomial_mem_xKernel_iff [Nontrivial k] (x : S.carrier) :
    S.monomialClass k (S.order x.val) x le_rfl ∈ (S.xAction k (S.order x.val)).ker ↔
      S.Terminal x.val := S.xAction_monomial_eq_zero_iff k x

end NSP14.NumericalSemigroup
