module
public import NSP14.Lex.DegreeSeparator
public import NSP14.Lex.StrongStableOperations
@[expose] public section
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Lex

theorem reversedPrefix_add (q : ℕ) (α β : Fin (q+1) →₀ ℕ) (t : ℕ) :
    reversedPrefix q (α+β) t=reversedPrefix q α t+reversedPrefix q β t := by
  unfold reversedPrefix
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold reversedCoefficient
  split_ifs <;> simp only [Finsupp.add_apply,add_zero]

theorem reversedCoefficient_single (q : ℕ) (i : Fin (q+1)) (n j : ℕ) :
    reversedCoefficient q (Finsupp.single i n) j=if j=(Fin.rev i).val then n else 0 := by
  by_cases hj : j<q+1
  · rw [reversedCoefficient,dite_eq_left hj]
    by_cases hji : j=(Fin.rev i).val
    · have he : (⟨j,hj⟩ : Fin (q+1))=Fin.rev i := Fin.ext hji
      rw [he,Fin.rev_rev,Finsupp.single_eq_same,ite_eq_left hji]
    · have hne : Fin.rev (⟨j,hj⟩ : Fin (q+1))≠i := by
        intro he
        have hh := congrArg (fun x : Fin (q+1) => (Fin.rev x).val) he
        simp only [Fin.rev_rev] at hh
        exact hji hh
      rw [Finsupp.single_eq_of_ne hne,ite_eq_right hji]
  · have hji : j≠(Fin.rev i).val := by have := (Fin.rev i).isLt; omega
    rw [reversedCoefficient,dite_eq_right hj,ite_eq_right hji]

theorem reversedPrefix_single (q : ℕ) (i : Fin (q+1)) (n t : ℕ) :
    reversedPrefix q (Finsupp.single i n) t=if (Fin.rev i).val<t then n else 0 := by
  simp only [reversedPrefix,reversedCoefficient_single,Finset.sum_ite_eq',Finset.mem_range]

theorem raisedExponent_add_source (q : ℕ) (α : Fin (q+1) →₀ ℕ)
    (a b : Fin (q+1)) (hb : 0<α b) :
    raisedExponent (q+1) α a b+Finsupp.single b 1=α+Finsupp.single a 1 := by
  have hle : Finsupp.single b 1≤α := by
    intro i
    by_cases hbi : b=i
    · subst i; simp only [Finsupp.single_eq_same]; omega
    · simp only [Finsupp.single_eq_of_ne' hbi]; exact Nat.zero_le _
  calc
    raisedExponent (q+1) α a b+Finsupp.single b 1=
        (α-Finsupp.single b 1+Finsupp.single b 1)+Finsupp.single a 1 := by
      unfold raisedExponent
      ac_rfl
    _=α+Finsupp.single a 1 := by rw [tsub_add_cancel_of_le hle]

theorem reversedPrefix_raised_balance (q : ℕ) (α : Fin (q+1) →₀ ℕ)
    (a b : Fin (q+1)) (hb : 0<α b) (t : ℕ) :
    reversedPrefix q (raisedExponent (q+1) α a b) t+(if (Fin.rev b).val<t then 1 else 0)=
      reversedPrefix q α t+(if (Fin.rev a).val<t then 1 else 0) := by
  have he := congrArg (fun γ => reversedPrefix q γ t) (raisedExponent_add_source q α a b hb)
  simpa only [reversedPrefix_add,reversedPrefix_single] using he
end NSP14.Lex

namespace NSP14.Lex

theorem reversedCoefficient_ext (q : ℕ) (α β : Fin (q+1) →₀ ℕ)
    (h : ∀ j,j<q+1 → reversedCoefficient q α j=reversedCoefficient q β j) : α=β := by
  ext i
  have hh := h (Fin.rev i).val (Fin.rev i).isLt
  simp only [reversedCoefficient,dite_eq_left (Fin.rev i).isLt] at hh
  change α (Fin.rev (Fin.rev i))=β (Fin.rev (Fin.rev i)) at hh
  simpa only [Fin.rev_rev] using hh

def tailPrefixMass (q : ℕ) (α : Fin (q+1) →₀ ℕ) : ℕ :=
  ∑ t∈Finset.range (q+2),reversedPrefix q α t

theorem IsStronglyStable.mem_of_tail_le (k : Type) [Field k] (q : ℕ)
    (I : Ideal (MvPolynomial (Fin (q+1)) k)) (hI : IsStronglyStable k (q+1) I)
    (α β : Fin (q+1) →₀ ℕ) (hdeg : α.degree=β.degree)
    (hdom : ∀ t,t≤q+1 → reversedPrefix q β t≤reversedPrefix q α t)
    (hmem : MvPolynomial.monomial α (1:k)∈I) : MvPolynomial.monomial β (1:k)∈I := by
  have haux : ∀ N : ℕ,∀ γ : Fin (q+1) →₀ ℕ,tailPrefixMass q γ=N →
      γ.degree=β.degree → (∀ t,t≤q+1 → reversedPrefix q β t≤reversedPrefix q γ t) →
      MvPolynomial.monomial γ (1:k)∈I → MvPolynomial.monomial β (1:k)∈I := by
    intro N
    induction N using Nat.strong_induction_on with
    | ind N ih =>
      intro γ hN hdeg hdom hmem
      by_cases he : γ=β
      · simpa only [he] using hmem
      have hex : ∃ a : ℕ,a<q+1 ∧ reversedCoefficient q γ a≠reversedCoefficient q β a := by
        by_contra hn
        apply he
        apply reversedCoefficient_ext q γ β
        intro a ha
        by_contra hne
        exact hn ⟨a,ha,hne⟩
      let a := Nat.find hex
      have ha : a<q+1 ∧ reversedCoefficient q γ a≠reversedCoefficient q β a := Nat.find_spec hex
      have hbefore (j : ℕ) (hj : j<a) : reversedCoefficient q γ j=reversedCoefficient q β j := by
        by_contra hn
        have hh := Nat.find_min' hex ⟨by omega,hn⟩
        change a≤j at hh
        omega
      have hpa : reversedPrefix q γ a=reversedPrefix q β a := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hbefore j (Finset.mem_range.mp hj)
      have hpgt : reversedPrefix q β (a+1)<reversedPrefix q γ (a+1) := by
        have hh := hdom (a+1) (by omega)
        rw [reversedPrefix_succ,reversedPrefix_succ,hpa] at hh ⊢
        omega
      have hca : 0<reversedCoefficient q γ a := by
        rw [reversedPrefix_succ,reversedPrefix_succ,hpa] at hpgt
        omega
      have hlast : a+1<q+1 := by
        have hh : reversedPrefix q γ (q+1)=reversedPrefix q β (q+1) := by
          rw [reversedPrefix_total,reversedPrefix_total,hdeg]
        by_contra hn
        have heq : a+1=q+1 := by omega
        rw [heq,hh] at hpgt
        exact lt_irrefl _ hpgt
      have hret : ∃ t : ℕ,a+1<t ∧ t≤q+1 ∧ reversedPrefix q γ t=reversedPrefix q β t :=
        ⟨q+1,hlast,le_rfl,by rw [reversedPrefix_total,reversedPrefix_total,hdeg]⟩
      let T := Nat.find hret
      have hT : a+1<T ∧ T≤q+1 ∧ reversedPrefix q γ T=reversedPrefix q β T := Nat.find_spec hret
      let b := T-1
      have hab : a<b := by dsimp only [b]; omega
      have hb : b<q+1 := by dsimp only [b]; omega
      have hgap (u : ℕ) (hau : a<u) (huT : u<T) :
          reversedPrefix q β u<reversedPrefix q γ u := by
        have hle := hdom u (by omega)
        by_cases hue : u=a+1
        · simpa only [hue] using hpgt
        · have hne : reversedPrefix q γ u≠reversedPrefix q β u := by
            intro heq
            have hh := Nat.find_min' hret ⟨by omega,by omega,heq⟩
            change T≤u at hh
            omega
          omega
      let ia : Fin (q+1) := ⟨a,ha.1⟩
      let ib : Fin (q+1) := ⟨b,hb⟩
      let γ' := raisedExponent (q+1) γ (Fin.rev ib) (Fin.rev ia)
      have hsrc : 0<γ (Fin.rev ia) := by
        simpa only [reversedCoefficient,dite_eq_left ha.1,ia] using hca
      have hlt : Fin.rev ib<Fin.rev ia := by
        change q+1-(b+1)<q+1-(a+1)
        omega
      have hmem' : MvPolynomial.monomial γ' (1:k)∈I := hI.2 γ hmem _ _ hsrc hlt
      have hbal (u : ℕ) : reversedPrefix q γ' u+(if a<u then 1 else 0)=
          reversedPrefix q γ u+(if b<u then 1 else 0) := by
        simpa only [γ',Fin.rev_rev,ia,ib] using
          reversedPrefix_raised_balance q γ (Fin.rev ib) (Fin.rev ia) hsrc u
      have hle (u : ℕ) : reversedPrefix q γ' u≤reversedPrefix q γ u := by
        have hh := hbal u
        by_cases hau : a<u <;> by_cases hbu : b<u <;>
          simp only [hau,hbu,ite_true,ite_false,add_zero] at hh <;> omega
      have hdom' (u : ℕ) (hu : u≤q+1) : reversedPrefix q β u≤reversedPrefix q γ' u := by
        have hh := hbal u
        have hdu := hdom u hu
        by_cases hau : a<u
        · by_cases hbu : b<u
          · simp only [hau,hbu,ite_true] at hh
            omega
          · have hg := hgap u hau (by dsimp only [b] at hbu; omega)
            simp only [hau,hbu,ite_true,ite_false,add_zero] at hh
            omega
        · have hbu : ¬b<u := by omega
          simp only [hau,hbu,ite_false,add_zero] at hh
          omega
      have hmass : tailPrefixMass q γ'<tailPrefixMass q γ := by
        apply Finset.sum_lt_sum
        · intro u _
          exact hle u
        · refine ⟨a+1,Finset.mem_range.mpr (by omega),?_⟩
          have hh := hbal (a+1)
          have hau : a<a+1 := by omega
          have hbu : ¬b<a+1 := by omega
          simp only [hau,hbu,ite_true,ite_false,add_zero] at hh
          omega
      have hdeg' : γ'.degree=β.degree := (raisedExponent_degree (q+1) γ _ _ hsrc).trans hdeg
      exact ih (tailPrefixMass q γ') (by omega) γ' rfl hdeg' hdom' hmem'
  exact haux (tailPrefixMass q α) α rfl hdeg hdom hmem
end NSP14.Lex
