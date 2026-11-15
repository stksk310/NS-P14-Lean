module
public import NSP14.Lex.Ideal
public import Mathlib.Algebra.MvPolynomial.Division
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)

noncomputable def raisedExponent (v : Fin q →₀ ℕ) (i j : Fin q) : Fin q →₀ ℕ :=
  v-Finsupp.single j 1+Finsupp.single i 1

theorem raisedExponent_degree (v : Fin q →₀ ℕ) (i j : Fin q) (hj : 0<v j) :
    (raisedExponent q v i j).degree=v.degree := by
  have hle : Finsupp.single j 1 ≤ v := by
    intro t
    by_cases ht : j=t
    · subst t
      simpa only [Finsupp.single_eq_same] using (Nat.succ_le_of_lt hj)
    · simp only [Finsupp.single_eq_of_ne' ht]
      exact Nat.zero_le _
  have he := tsub_add_cancel_of_le hle
  have hd := congrArg Finsupp.degree he
  rw [map_add,Finsupp.degree_single] at hd
  unfold raisedExponent
  rw [map_add,Finsupp.degree_single]
  exact hd

theorem raisedExponent_lex (v : Fin q →₀ ℕ) (i j : Fin q) (hij : i<j) :
    MonomialOrder.lex.toSyn v<MonomialOrder.lex.toSyn (raisedExponent q v i j) := by
  change Finsupp.Lex (· < ·) (· < ·) v (raisedExponent q v i j)
  refine ⟨i,?_,?_⟩
  · intro t ht
    have htj : j≠t := (ne_of_lt (ht.trans hij)).symm
    have hti : i≠t := (ne_of_lt ht).symm
    simp only [raisedExponent,Finsupp.add_apply,Finsupp.tsub_apply,Finsupp.single_eq_of_ne' htj,
      Finsupp.single_eq_of_ne' hti,Nat.sub_zero,add_zero]
  · have hji : j≠i := (ne_of_lt hij).symm
    simp only [raisedExponent,Finsupp.add_apply,Finsupp.tsub_apply,Finsupp.single_eq_of_ne' hji,
      Finsupp.single_eq_same,Nat.sub_zero]
    omega

/-- Every actual lex ideal is strongly stable in the fixed variable order,
with no characteristic-zero argument. -/
theorem IsLex.raise {L : Ideal (MvPolynomial (Fin q) k)} (hL : IsLex k q L)
    (v : Fin q →₀ ℕ) (hv : MvPolynomial.monomial v (1:k)∈L)
    (i j : Fin q) (hj : 0<v j) (hij : i<j) :
    MvPolynomial.monomial (raisedExponent q v i j) (1:k)∈L :=
  hL.2 v (raisedExponent q v i j) (raisedExponent_degree q v i j hj).symm
    (le_of_lt (raisedExponent_lex q v i j hij)) hv
end NSP14.Lex
