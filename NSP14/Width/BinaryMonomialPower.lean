module
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Tactic.NormNum
public import Lean.Elab.Tactic.Omega
@[expose] public section
open scoped Classical Pointwise
namespace NSP14.Width
variable (k : Type) [Field k] {σ : Type} (a b : σ)
noncomputable def binaryCutoffIdeal (n : ℕ) : Ideal (MvPolynomial σ k) :=
  Ideal.span ((fun β : σ →₀ ℕ => MvPolynomial.monomial β (1:k)) ''
    {β | n ≤ β a+β b})

/-- The monomial cutoff is the literal ideal power (X_a,X_b)^n. -/
theorem binaryCutoffIdeal_eq_power (hab : a≠b) (n : ℕ) :
    binaryCutoffIdeal k a b n=(Ideal.span ({MvPolynomial.X a,MvPolynomial.X b} : Set (MvPolynomial σ k)))^n := by
  induction n with
  | zero =>
    rw [pow_zero,Ideal.one_eq_top]
    apply Ideal.eq_top_of_isUnit_mem (x:=1)
    · apply Ideal.subset_span
      exact ⟨0,by simp,by simp⟩
    · exact isUnit_one
  | succ n ih =>
    rw [pow_succ',←ih]
    unfold binaryCutoffIdeal
    rw [Ideal.span_mul_span]
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro _ ⟨β,hβ,rfl⟩
      change n+1 ≤ β a+β b at hβ
      by_cases ha : 1 ≤ β a
      · let δ := β-Finsupp.single a 1
        have hs : Finsupp.single a 1 ≤ β := Finsupp.single_le_iff.mpr ha
        have hδ : n ≤ δ a+δ b := by
          dsimp [δ]
          simp only [Finsupp.single_eq_same,Finsupp.single_eq_of_ne hab.symm,Nat.sub_zero]
          omega
        apply Ideal.subset_span
        refine ⟨MvPolynomial.X a,by simp,MvPolynomial.monomial δ (1:k),⟨δ,hδ,rfl⟩,?_⟩
        change MvPolynomial.monomial (Finsupp.single a 1) (1:k)*MvPolynomial.monomial δ 1=MvPolynomial.monomial β 1
        rw [MvPolynomial.monomial_mul_monomial,one_mul]
        exact congrArg (fun v => MvPolynomial.monomial v (1:k)) (add_tsub_cancel_of_le hs)
      · have hb : 1 ≤ β b := by omega
        let δ := β-Finsupp.single b 1
        have hs : Finsupp.single b 1 ≤ β := Finsupp.single_le_iff.mpr hb
        have hδ : n ≤ δ a+δ b := by
          dsimp [δ]
          simp only [Finsupp.single_eq_same,Finsupp.single_eq_of_ne hab,Nat.sub_zero]
          omega
        apply Ideal.subset_span
        refine ⟨MvPolynomial.X b,by simp,MvPolynomial.monomial δ (1:k),⟨δ,hδ,rfl⟩,?_⟩
        change MvPolynomial.monomial (Finsupp.single b 1) (1:k)*MvPolynomial.monomial δ 1=MvPolynomial.monomial β 1
        rw [MvPolynomial.monomial_mul_monomial,one_mul]
        exact congrArg (fun v => MvPolynomial.monomial v (1:k)) (add_tsub_cancel_of_le hs)
    · apply Ideal.span_le.mpr
      rintro _ ⟨f,hf,g,hg,rfl⟩
      obtain ⟨β,hβ,rfl⟩ := hg
      change n ≤ β a+β b at hβ
      rcases (show f=MvPolynomial.X a ∨ f=MvPolynomial.X b from by simpa using hf) with rfl|rfl
      · change MvPolynomial.monomial (Finsupp.single a 1) (1:k)*MvPolynomial.monomial β 1∈_
        rw [MvPolynomial.monomial_mul_monomial,one_mul]
        apply Ideal.subset_span
        refine ⟨Finsupp.single a 1+β,?_,rfl⟩
        simp only [Set.mem_ofPred_eq,Finsupp.add_apply,Finsupp.single_eq_same,Finsupp.single_eq_of_ne hab.symm]
        omega
      · change MvPolynomial.monomial (Finsupp.single b 1) (1:k)*MvPolynomial.monomial β 1∈_
        rw [MvPolynomial.monomial_mul_monomial,one_mul]
        apply Ideal.subset_span
        refine ⟨Finsupp.single b 1+β,?_,rfl⟩
        simp only [Set.mem_ofPred_eq,Finsupp.add_apply,Finsupp.single_eq_same,Finsupp.single_eq_of_ne hab]
        omega
end NSP14.Width
