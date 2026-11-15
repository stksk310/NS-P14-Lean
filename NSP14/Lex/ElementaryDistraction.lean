module
public import NSP14.Lex.GenericDistractionPrincipal
public import NSP14.Lex.Stable
@[expose] public section
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)

def elementaryLinear (a b : Fin q) (m : ℕ) (i : Fin q) (n : ℕ) : MvPolynomial (Fin q) k :=
  if i=b ∧ n=m then MvPolynomial.X b+MvPolynomial.X a else MvPolynomial.X i

theorem elementaryDistraction_inactive (a b : Fin q) (m : ℕ) (α : Fin q →₀ ℕ)
    (hm : α b≤m) : distractionMonomial k q (elementaryLinear k q a b m) α=MvPolynomial.monomial α 1 := by
  rw [← distractionMonomial_variables k q α]
  unfold distractionMonomial
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j hj
  have hjm : ¬(i=b ∧ j=m) := by
    rintro ⟨rfl,rfl⟩
    have := Finset.mem_range.mp hj
    omega
  simp only [elementaryLinear,ite_eq_right hjm]

theorem elementaryDistraction_active (a b : Fin q) (m : ℕ) (α : Fin q →₀ ℕ)
    (hm : m<α b) : distractionMonomial k q (elementaryLinear k q a b m) α=
      MvPolynomial.monomial α 1+MvPolynomial.monomial (raisedExponent q α a b) 1 := by
  let β := α-Finsupp.single b 1
  have hmono (γ : Fin q →₀ ℕ) : (∏ i : Fin q,(MvPolynomial.X i : MvPolynomial (Fin q) k)^(γ i))=
      MvPolynomial.monomial γ 1 := by
    simpa only [distractionMonomial,Finset.prod_const,Finset.card_range] using
      distractionMonomial_variables k q γ
  have hi (i : Fin q) : (∏ j∈Finset.range (α i),elementaryLinear k q a b m i j)=
      (if i=b then MvPolynomial.X b+MvPolynomial.X a else 1)*MvPolynomial.X i^(β i) := by
    by_cases hib : i=b
    · subst i
      have hfun : elementaryLinear k q a b m b=
          Function.update (fun _ : ℕ => (MvPolynomial.X b : MvPolynomial (Fin q) k)) m
            (MvPolynomial.X b+MvPolynomial.X a) := by
        funext j
        simp only [elementaryLinear,true_and,Function.update_apply,eq_comm]
      rw [hfun,Finset.prod_update_of_mem (Finset.mem_range.mpr hm),Finset.sdiff_singleton_eq_erase]
      simp only [Finset.prod_const,Finset.card_erase_of_mem (Finset.mem_range.mpr hm),Finset.card_range,
        β,Finsupp.tsub_apply,Finsupp.single_eq_same,ite_true]
    · simp only [elementaryLinear,hib,false_and,ite_false,Finset.prod_const,Finset.card_range,
        β,Finsupp.tsub_apply,Finsupp.single_eq_of_ne hib,Nat.sub_zero,one_mul]
  have hD : distractionMonomial k q (elementaryLinear k q a b m) α=
      (MvPolynomial.X b+MvPolynomial.X a)*MvPolynomial.monomial β 1 := by
    unfold distractionMonomial
    simp_rw [hi]
    rw [Finset.prod_mul_distrib,hmono]
    simp
  have hb : Finsupp.single b 1+β=α := by
    apply add_tsub_cancel_of_le
    intro i
    by_cases hib : b=i
    · subst i
      simp only [Finsupp.single_eq_same]
      omega
    · simp only [Finsupp.single_eq_of_ne' hib]
      exact Nat.zero_le _
  rw [hD,add_mul]
  have hmul (i : Fin q) : MvPolynomial.X i*MvPolynomial.monomial β (1:k)=
      MvPolynomial.monomial (Finsupp.single i 1+β) 1 := by
    rw [MvPolynomial.X,MvPolynomial.monomial_mul_monomial,one_mul]
  rw [hmul,hmul,hb]
  congr 1
  exact congrArg (fun γ => MvPolynomial.monomial γ (1:k)) (add_comm _ _)
end NSP14.Lex

namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)

def elementaryParameterMap (a b : Fin q) (m : ℕ) : GenericCoefficientRing k q →+* k :=
  MvPolynomial.eval₂Hom (RingHom.id k) (fun p =>
    (if p.1=p.2.2 then 1 else 0)+(if p.1=b ∧ p.2.1=m ∧ p.2.2=a then 1 else 0))

theorem genericLinearRaw_elementary_specialize (a b : Fin q) (m : ℕ) (i : Fin q) (n : ℕ) :
    MvPolynomial.map (elementaryParameterMap k q a b m) (genericLinearRaw k q i n)=
      elementaryLinear k q a b m i n := by
  by_cases hi : i=b
  · subst i
    by_cases hn : n=m
    · subst n
      simp [genericLinearRaw,elementaryParameterMap,elementaryLinear,map_add,add_mul,
        Finset.sum_add_distrib,eq_comm]
    · simp [genericLinearRaw,elementaryParameterMap,elementaryLinear,hn]
  · simp [genericLinearRaw,elementaryParameterMap,elementaryLinear,hi]

theorem genericRawDistraction_elementary_specialize (a b : Fin q) (m : ℕ) (α : Fin q →₀ ℕ) :
    MvPolynomial.map (elementaryParameterMap k q a b m) (genericRawDistraction k q α)=
      distractionMonomial k q (elementaryLinear k q a b m) α := by
  simp only [genericRawDistraction,distractionMonomial,map_prod,genericLinearRaw_elementary_specialize]

theorem genericRawDegreeMatrix_elementary_entry (a b : Fin q) (m n : ℕ)
    (ρ α : PolynomialDegreeIndex q n) :
    elementaryParameterMap k q a b m (genericRawDegreeMatrix k q n ρ α)=
      (if α.val=ρ.val then 1 else 0)+
        if m<α.val b then if raisedExponent q α.val a b=ρ.val then 1 else 0 else 0 := by
  have he := congrArg (fun p : MvPolynomial (Fin q) k => p.coeff ρ.val)
    (genericRawDistraction_elementary_specialize k q a b m α.val)
  rw [MvPolynomial.coeff_map] at he
  change elementaryParameterMap k q a b m ((genericRawDistraction k q α.val).coeff ρ.val)=_ at he
  change elementaryParameterMap k q a b m ((genericRawDistraction k q α.val).coeff ρ.val)=_
  rw [he]
  by_cases hm : m<α.val b
  · rw [elementaryDistraction_active k q a b m α.val hm]
    simp only [AddMonoidAlgebra.coeff_add,Finsupp.add_apply,MvPolynomial.coeff_monomial,hm,ite_true]
  · rw [elementaryDistraction_inactive k q a b m α.val (Nat.le_of_not_gt hm)]
    simp only [MvPolynomial.coeff_monomial,hm,ite_false,add_zero]
end NSP14.Lex
