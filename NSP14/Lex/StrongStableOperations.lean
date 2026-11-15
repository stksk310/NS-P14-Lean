module
public import NSP14.Lex.GenericDistractionStable
public import Mathlib.Combinatorics.SetFamily.Shadow
@[expose] public section
open scoped Classical BigOperators FinsetFamily
open Finset
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)

theorem IsStronglyStable.replace_factor (I : Ideal (MvPolynomial (Fin q) k))
    (hI : IsStronglyStable k q I) (α : Fin q →₀ ℕ) (a b : Fin q) (hab : a≤b)
    (hm : MvPolynomial.monomial (α+Finsupp.single b 1) (1:k)∈I) :
    MvPolynomial.monomial (α+Finsupp.single a 1) (1:k)∈I := by
  rcases hab.eq_or_lt with rfl|hab
  · exact hm
  have hp : 0<(α+Finsupp.single b 1 : Fin q →₀ ℕ) b := by simp
  have hh := hI.2 _ hm a b hp hab
  simpa only [raisedExponent,add_tsub_cancel_right] using hh

theorem IsStronglyStable.replace_power (I : Ideal (MvPolynomial (Fin q) k))
    (hI : IsStronglyStable k q I) (a b : Fin q) (hab : a≤b) (n : ℕ) :
    ∀ α : Fin q →₀ ℕ,MvPolynomial.monomial (α+Finsupp.single b n) (1:k)∈I →
      MvPolynomial.monomial (α+Finsupp.single a n) (1:k)∈I := by
  induction n with
  | zero => intro α hm; simpa only [Finsupp.single_zero,add_zero] using hm
  | succ n ih =>
    intro α hm
    have hm' : MvPolynomial.monomial ((α+Finsupp.single b n)+Finsupp.single b 1) (1:k)∈I := by
      simpa only [Finsupp.single_add,add_assoc] using hm
    have hh := hI.replace_factor k q I (α+Finsupp.single b n) a b hab hm'
    have hz : MvPolynomial.monomial ((α+Finsupp.single a 1)+Finsupp.single b n) (1:k)∈I := by
      simpa only [add_assoc,add_comm,add_left_comm] using hh
    have hout := ih (α+Finsupp.single a 1) hz
    simpa only [Finsupp.single_add,add_assoc,add_comm,add_left_comm] using hout

/-- Every actual regressive variable substitution preserves a strongly stable ideal.
Only membership-preserving elementary raising moves are used. -/
theorem IsStronglyStable.regressive_substitution (I : Ideal (MvPolynomial (Fin q) k))
    (hI : IsStronglyStable k q I) (f : Fin q → Fin q) (hf : ∀ i, f i ≤ i)
    (α : Fin q →₀ ℕ) : ∀ γ : Fin q →₀ ℕ,
      MvPolynomial.monomial (γ+α) (1:k)∈I →
        MvPolynomial.monomial (γ+α.mapDomain f) (1:k)∈I := by
  induction α using Finsupp.induction with
  | zero => intro γ hm; simpa only [Finsupp.mapDomain_zero] using hm
  | single_add i n α _ _ ih =>
    intro γ hm
    have hm' : MvPolynomial.monomial ((γ+α)+Finsupp.single i n) (1:k)∈I := by
      simpa only [add_assoc,add_comm,add_left_comm] using hm
    have hh := hI.replace_power k q I (f i) i (hf i) n (γ+α) hm'
    have hz : MvPolynomial.monomial ((γ+Finsupp.single (f i) n)+α) (1:k)∈I := by
      simpa only [add_assoc,add_comm,add_left_comm] using hh
    have hout := ih (γ+Finsupp.single (f i) n) hz
    simpa only [Finsupp.mapDomain_add,Finsupp.mapDomain_single,add_assoc] using hout
end NSP14.Lex
