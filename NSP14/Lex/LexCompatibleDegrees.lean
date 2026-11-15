module
public import NSP14.Lex.LexDegreeIdeal
@[expose] public section
open scoped Classical BigOperators
open NSP14.Homological
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Lex
variable (k : Type) [Field k] (q d : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
theorem degreeGeneratedIdeal_no_higher_minimal (S : Finset (PolynomialDegreeIndex q d))
    (α : PolynomialDegreeIndex q (d+1)) : ¬MinimalGenerator k q (degreeGeneratedIdeal k q d S) α.val := by
  intro hmin
  obtain ⟨v,⟨β,hβ,hv⟩,hle⟩ := (monomial_mem_span_iff k q (degreeSupport q d S) α.val).mp hmin.1
  subst v
  have hmem : MvPolynomial.monomial β.val (1:k)∈degreeGeneratedIdeal k q d S :=
    (degreeGeneratedIdeal_degree_mem k q d S β).mpr hβ
  have he := hmin.2 β.val hle hmem
  have hd := congrArg Finsupp.degree he
  rw [β.property,α.property] at hd
  omega

theorem degreeGeneratedIdeal_growth (S : Finset (PolynomialDegreeIndex q d))
    (hupper : ∀ a∈S,∀ b : PolynomialDegreeIndex q d,
      MonomialOrder.lex.toSyn a.val≤MonomialOrder.lex.toSyn b.val → b∈S) :
    idealDegreeCard k q (degreeGeneratedIdeal k q d S) (d+1)+
      degreeBinomialSum k q (degreeGeneratedIdeal k q d S) d 1=S.card*q := by
  have hLex := degreeGeneratedIdeal_isLex k q d S hupper
  have hStable : IsStronglyStable k q (degreeGeneratedIdeal k q d S) :=
    ⟨hLex.1,fun v hv a b hp hab => hLex.raise k q v hv a b hp hab⟩
  have hi := hStable.degree_binomial_identity k q _ d 0
  have hempty : IsEmpty (MinimalDegreeMonomial k q (degreeGeneratedIdeal k q d S) (d+1)) :=
    ⟨fun α => degreeGeneratedIdeal_no_higher_minimal k q d S α.val α.property⟩
  let := hempty
  have hz : (∑ α : MinimalDegreeMonomial k q (degreeGeneratedIdeal k q d S) (d+1),
      (maxVariable q α.val.val-1).choose 0)=0 := Finset.sum_of_isEmpty _
  have hcount : idealDegreeCard k q (degreeGeneratedIdeal k q d S) d=S.card := by
    simp only [idealDegreeCard,Fintype.card_subtype,degreeGeneratedIdeal_degree_mem]
    rw [Finset.filter_mem_eq_inter,Finset.univ_inter]
  have hw0 : degreeBinomialSum k q (degreeGeneratedIdeal k q d S) (d+1) 0=
      idealDegreeCard k q (degreeGeneratedIdeal k q d S) (d+1) := by
    simp only [degreeBinomialSum,Nat.choose_zero_right,Finset.sum_const,nsmul_eq_mul,Nat.cast_id,mul_one,
      idealDegreeCard,Fintype.card_subtype]
  simpa only [hw0,hz,zero_add,hcount,Nat.choose_one_right] using hi



variable (I : Ideal (MvPolynomial (Fin q) k))
noncomputable def lexDegreeSet (n : ℕ) : Finset (PolynomialDegreeIndex q n) :=
  (exists_upper_finset_card (fun α : PolynomialDegreeIndex q n => MonomialOrder.lex.toSyn α.val)
    (fun _a _b he => Subtype.ext (MonomialOrder.lex.toSyn.injective he))
    (idealDegreeCard k q I n) (Fintype.card_subtype_le _)).choose

theorem lexDegreeSet_card (n : ℕ) : (lexDegreeSet k q I n).card=idealDegreeCard k q I n :=
  (exists_upper_finset_card (fun α : PolynomialDegreeIndex q n => MonomialOrder.lex.toSyn α.val)
    (fun _a _b he => Subtype.ext (MonomialOrder.lex.toSyn.injective he))
    (idealDegreeCard k q I n) (Fintype.card_subtype_le _)).choose_spec.1

theorem lexDegreeSet_upper (n : ℕ) : ∀ a∈lexDegreeSet k q I n,∀ b : PolynomialDegreeIndex q n,
    MonomialOrder.lex.toSyn a.val≤MonomialOrder.lex.toSyn b.val → b∈lexDegreeSet k q I n :=
  (exists_upper_finset_card (fun α : PolynomialDegreeIndex q n => MonomialOrder.lex.toSyn α.val)
    (fun _a _b he => Subtype.ext (MonomialOrder.lex.toSyn.injective he))
    (idealDegreeCard k q I n) (Fintype.card_subtype_le _)).choose_spec.2

theorem degreeGeneratedIdeal_degreeCard (S : Finset (PolynomialDegreeIndex q d)) :
    idealDegreeCard k q (degreeGeneratedIdeal k q d S) d=S.card := by
  simp only [idealDegreeCard,Fintype.card_subtype,degreeGeneratedIdeal_degree_mem]
  rw [Finset.filter_mem_eq_inter,Finset.univ_inter]

theorem degreeBinomialSum_zero (J : Ideal (MvPolynomial (Fin q) k)) (n : ℕ) :
    degreeBinomialSum k q J n 0=idealDegreeCard k q J n := by
  simp only [degreeBinomialSum,Nat.choose_zero_right,Finset.sum_const,nsmul_eq_mul,Nat.cast_id,mul_one,
    idealDegreeCard,Fintype.card_subtype]

theorem IsStronglyStable.lexDegreeSet_growth (hI : IsStronglyStable k q I) (n : ℕ) :
    idealDegreeCard k q (degreeGeneratedIdeal k q n (lexDegreeSet k q I n)) (n+1)≤ idealDegreeCard k q I (n+1) := by
  let S := lexDegreeSet k q I n
  let L := degreeGeneratedIdeal k q n S
  have hlL : IsLex k q L := degreeGeneratedIdeal_isLex k q n S (lexDegreeSet_upper k q I n)
  have hc : idealDegreeCard k q I n=idealDegreeCard k q L n := by
    rw [degreeGeneratedIdeal_degreeCard,lexDegreeSet_card]
  have hw := hI.binomial_degree_sum_le_lex k q I L hlL n 1 hc
  have hgl := degreeGeneratedIdeal_growth k q n S (lexDegreeSet_upper k q I n)
  have hgi := hI.degree_binomial_identity k q I n 0
  rw [degreeBinomialSum_zero,Nat.choose_one_right] at hgi
  have hSc : S.card=idealDegreeCard k q I n := lexDegreeSet_card k q I n
  change idealDegreeCard k q L (n+1)+degreeBinomialSum k q L n 1=S.card*q at hgl
  rw [hSc] at hgl
  simp only [Nat.zero_add] at hgi
  change idealDegreeCard k q L (n+1)≤ idealDegreeCard k q I (n+1)
  omega

theorem IsStronglyStable.lexDegreeSet_next_mem (hI : IsStronglyStable k q I) (n : ℕ)
    (α : PolynomialDegreeIndex q n) (hα : α∈lexDegreeSet k q I n) (r : Fin q) :
    (⟨α.val+Finsupp.single r 1,by simp only [map_add,Finsupp.degree_single,α.property]⟩ : PolynomialDegreeIndex q (n+1))∈lexDegreeSet k q I (n+1) := by
  let S := lexDegreeSet k q I n
  let L := degreeGeneratedIdeal k q n S
  let T := Finset.univ.filter (fun β : PolynomialDegreeIndex q (n+1) => MvPolynomial.monomial β.val (1:k)∈L)
  have hlL : IsLex k q L := degreeGeneratedIdeal_isLex k q n S (lexDegreeSet_upper k q I n)
  have hsub : T⊆lexDegreeSet k q I (n+1) := by
    apply upper_finset_subset_of_card_le (fun β : PolynomialDegreeIndex q (n+1) => MonomialOrder.lex.toSyn β.val)
    · intro a ha b hab
      simp only [T,Finset.mem_filter,Finset.mem_univ,true_and] at ha ⊢
      exact hlL.2 _ _ (a.property.trans b.property.symm) hab ha
    · exact lexDegreeSet_upper k q I (n+1)
    · rw [lexDegreeSet_card]
      have hg := hI.lexDegreeSet_growth k q I n
      simpa only [idealDegreeCard,Fintype.card_subtype] using hg
  apply hsub
  simp only [T,Finset.mem_filter,Finset.mem_univ,true_and]
  exact monomial_mem_of_le k q L α.val _ ((degreeGeneratedIdeal_degree_mem k q n S α).mpr hα)
    (by intro l; simp only [Finsupp.add_apply]; omega)



end NSP14.Lex
