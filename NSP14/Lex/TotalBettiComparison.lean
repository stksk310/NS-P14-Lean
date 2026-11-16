module
public import NSP14.Lex.BettiComparison
@[expose] public section
open scoped Classical BigOperators
open NSP14.Homological
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)

theorem quotientTotalBetti_le_lex (I L : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hL : L.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hlL : IsLex k q L) (hH : ∀ n,quotientHilbert k q I hI n=quotientHilbert k q L hL n)
    (i : ℕ) (hi : 1 ≤ i) :
    totalBetti k (Fin q) (NSP14.Endpoint.artinModule k (Fin q) I) i≤
      totalBetti k (Fin q) (NSP14.Endpoint.artinModule k (Fin q) L) i := by
  obtain ⟨s,hs,heI⟩ := quotient_total_eq_graded_sum k q I hI i
  obtain ⟨t,ht,heL⟩ := quotient_total_eq_graded_sum k q L hL i
  have hext (u : Finset ℤ) (v : Finset ℤ) (f : ℤ → ℕ) (hf : ∀ j∉u,f j=0) :
      (∑ j∈u,f j)=∑ j∈u∪v,f j := by
    apply Finset.sum_subset (Finset.subset_union_left)
    intro j _ hj
    exact hf j hj
  rw [heI,heL,hext s t _ hs,hext t s _ ht,Finset.union_comm t s]
  apply Finset.sum_le_sum
  intro j _
  exact quotientGradedBetti_le_lex k q I L hI hL hlL hH i hi j
end NSP14.Lex
