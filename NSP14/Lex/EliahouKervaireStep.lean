module
public import NSP14.Lex.LinearQuotients
public import NSP14.Homological.IdealAdjoiningKoszul
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open NSP14.Homological
namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)

theorem IsLex.predecessor_factor_colon {L : Ideal (MvPolynomial (Fin q) k)}
    (hL : IsLex k q L) (w : Fin q →₀ ℕ) (hw : MinimalGenerator k q L w)
    (r : Fin q) (hr : 0 < w r) (hmax : ∀ i, r < i → w i=0) :
    (predecessorIdeal k q L w).colon {MvPolynomial.monomial w (1:k)} ≤
      (predecessorIdeal k q L w).colon {MvPolynomial.monomial (w-Finsupp.single r 1) (1:k)} := by
  rw [hL.predecessor_colon k q w hw r hr hmax]
  apply Ideal.span_le.mpr
  rintro _ ⟨i,hi,rfl⟩
  apply Submodule.mem_colon_singleton.mpr
  change MvPolynomial.X i * MvPolynomial.monomial (w-Finsupp.single r 1) (1:k) ∈ predecessorIdeal k q L w
  rw [MvPolynomial.X,MvPolynomial.monomial_mul_monomial,one_mul,add_comm]
  exact Ideal.subset_span ⟨raisedExponent q w i r,
    ⟨hL.raise k q w hw.1 i r hr hi,
      Or.inr ⟨raisedExponent_degree q w i r hr,raisedExponent_lex q w i r hi⟩⟩,rfl⟩

theorem exponent_remove_max_factor (w : Fin q →₀ ℕ) (r : Fin q) (hr : 0 < w r) :
    MvPolynomial.monomial w (1:k)=
      MvPolynomial.X r * MvPolynomial.monomial (w-Finsupp.single r 1) (1:k) := by
  rw [MvPolynomial.X,MvPolynomial.monomial_mul_monomial,one_mul]
  have hs : Finsupp.single r 1 ≤ w := by
    intro i
    by_cases hri : r=i
    · subst i
      simpa only [Finsupp.single_eq_same] using (Nat.succ_le_of_lt hr)
    · simp only [Finsupp.single_eq_of_ne' hri]
      exact Nat.zero_le _
  rw [add_comm,tsub_add_cancel_of_le hs]

/-- An actual EK recursion step. The source map factors through a
variable, so its actual homology map is zero. No Tor comparison or
minimal-resolution assertion is supplied as an input. -/
theorem IsLex.predecessor_betti_step {L : Ideal (MvPolynomial (Fin q) k)}
    (hL : IsLex k q L) (w : Fin q →₀ ℕ) (hw : MinimalGenerator k q L w)
    (r : Fin q) (hr : 0 < w r) (hmax : ∀ j, r < j → w j=0) (i : ℕ) :
    let J := predecessorIdeal k q L w
    totalBetti k (Fin q)
      (ModuleCat.of (MvPolynomial (Fin q) k) ((MvPolynomial (Fin q) k) ⧸ (J ⊔ Ideal.span {MvPolynomial.monomial w (1:k)}))) (i+1)=
      totalBetti k (Fin q)
        (ModuleCat.of (MvPolynomial (Fin q) k) ((MvPolynomial (Fin q) k) ⧸ J)) (i+1)+
      totalBetti k (Fin q)
        (ModuleCat.of (MvPolynomial (Fin q) k)
          ((MvPolynomial (Fin q) k) ⧸ Ideal.span ((MvPolynomial.X : Fin q → MvPolynomial (Fin q) k) '' {j : Fin q | j < r}))) i := by
  have h := idealAdjoin_betti_additivity k (Fin q) (predecessorIdeal k q L w)
    (MvPolynomial.monomial w (1:k)) (MvPolynomial.monomial (w-Finsupp.single r 1) (1:k)) r
    (exponent_remove_max_factor k q w r hr) (hL.predecessor_factor_colon k q w hw r hr hmax) i
  rw [hL.predecessor_colon k q w hw r hr hmax] at h
  exact h

end NSP14.Lex
