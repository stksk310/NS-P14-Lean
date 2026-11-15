module
public import NSP14.Lex.StableBinomialWeights
public import NSP14.Lex.StrongStableEK
@[expose] public section
open scoped Classical BigOperators
open NSP14.Homological
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Lex

theorem maxVariable_le_iff (q : ℕ) (α : Fin q →₀ ℕ) (r : ℕ) :
    maxVariable q α≤r ↔ ∀ j, r≤j.val → α j=0 := by
  constructor
  · intro h j hj
    by_contra hn
    have hh := Finset.le_sup (f:=fun i : Fin q => i.val+1) (Finsupp.mem_support_iff.mpr hn)
    change j.val+1≤maxVariable q α at hh
    omega
  · intro h
    apply Finset.sup_le
    intro j hj
    have hn := Finsupp.mem_support_iff.mp hj
    by_contra hh
    have hz := h j (by omega)
    exact hn hz

theorem maxVariable_add_single (q : ℕ) (β : Fin q →₀ ℕ) (r : Fin q)
    (hb : maxVariable q β≤r.val+1) :
    maxVariable q (β+Finsupp.single r 1)=r.val+1 := by
  apply le_antisymm
  · apply (maxVariable_le_iff q _ _).mpr
    intro j hj
    have hrj : r≠j := by intro he; subst j; omega
    simp only [Finsupp.add_apply,Finsupp.single_eq_of_ne' hrj,add_zero]
    exact (maxVariable_le_iff q β _).mp hb j hj
  · apply Finset.le_sup (f:=fun i : Fin q => i.val+1)
    apply Finsupp.mem_support_iff.mpr
    simp only [Finsupp.add_apply,Finsupp.single_eq_same]
    omega

theorem IsStronglyStable.remove_max_not_mem_iff_minimal (k : Type) [Field k] (q : ℕ)
    (I : Ideal (MvPolynomial (Fin q) k)) (hI : IsStronglyStable k q I)
    (α : Fin q →₀ ℕ) (hα : MvPolynomial.monomial α (1:k)∈I)
    (r : Fin q) (hr : 0<α r) (hm : ∀ j,r<j → α j=0) :
    MinimalGenerator k q I α ↔ MvPolynomial.monomial (α-Finsupp.single r 1) (1:k)∉I := by
  have hsingle : Finsupp.single r 1≤α := by
    intro j
    by_cases he : r=j
    · subst j; simpa using (Nat.succ_le_of_lt hr)
    · simp only [Finsupp.single_eq_of_ne' he]; exact Nat.zero_le _
  have hadd : α-Finsupp.single r 1+Finsupp.single r 1=α := tsub_add_cancel_of_le hsingle
  constructor
  · intro hgen hmem
    have hh := hgen.2 (α-Finsupp.single r 1) (tsub_le_self) hmem
    have hd := congrArg Finsupp.degree hadd
    rw [hh] at hd
    simp only [map_add,Finsupp.degree_single] at hd
    omega
  · intro hnot
    refine ⟨hα,?_⟩
    intro β hβα hβ
    by_contra hne
    have hdif : ∃ j,β j<α j := by
      by_contra! hn
      apply hne
      ext j
      exact le_antisymm (hβα j) (hn j)
    obtain ⟨j,hj⟩ := hdif
    have hβj : β≤α-Finsupp.single j 1 := by
      intro l
      by_cases he : j=l
      · subst l; simp only [Finsupp.tsub_apply,Finsupp.single_eq_same]; omega
      · simpa only [Finsupp.tsub_apply,Finsupp.single_eq_of_ne' he,Nat.sub_zero] using hβα l
    have hmem : MvPolynomial.monomial (α-Finsupp.single j 1) (1:k)∈I :=
      monomial_mem_of_le k q I β _ hβ hβj
    apply hnot
    by_cases he : j=r
    · simpa only [he] using hmem
    have hjr : j<r := by
      by_contra hn
      have hz := hm j (lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm he))
      omega
    have hpos : 0<((α-Finsupp.single j 1 : Fin q →₀ ℕ) r) := by
      simpa only [Finsupp.tsub_apply,Finsupp.single_eq_of_ne' he,Nat.sub_zero] using hr
    have hh := hI.raise k q (α-Finsupp.single j 1) hmem j r hpos hjr
    have heq : raisedExponent q (α-Finsupp.single j 1) j r=α-Finsupp.single r 1 := by
      ext l
      by_cases hjl : j=l
      · subst l
        simp only [raisedExponent,Finsupp.add_apply,Finsupp.tsub_apply,Finsupp.single_eq_same,
          Finsupp.single_eq_of_ne' (Ne.symm he),Nat.sub_zero]
        omega
      · by_cases hrl : r=l
        · subst l
          simp only [raisedExponent,Finsupp.add_apply,Finsupp.tsub_apply,
            Finsupp.single_eq_of_ne' he,Finsupp.single_eq_same,Nat.sub_zero,add_zero]
        · simp only [raisedExponent,Finsupp.add_apply,Finsupp.tsub_apply,
            Finsupp.single_eq_of_ne' hjl,Finsupp.single_eq_of_ne' hrl,Nat.sub_zero,add_zero]
    simpa only [heq] using hh


variable (k : Type) [Field k] (q : ℕ) (I : Ideal (MvPolynomial (Fin q) k))
abbrev IdealDegreeMonomial (d : ℕ) :=
  {α : PolynomialDegreeIndex q d // MvPolynomial.monomial α.val (1:k)∈I}
abbrev MinimalDegreeMonomial (d : ℕ) :=
  {α : PolynomialDegreeIndex q d // MinimalGenerator k q I α.val}
abbrev AdjoinDegreeIndex (d : ℕ) :=
  (β : IdealDegreeMonomial k q I d) × {r : Fin q // maxVariable q β.val.val≤r.val+1}

def degreeAdjoin (d : ℕ) (β : AdjoinDegreeIndex k q I d) : IdealDegreeMonomial k q I (d+1) :=
  ⟨⟨β.1.val.val+Finsupp.single β.2.val 1,by
    simp only [map_add,Finsupp.degree_single,β.1.val.property]⟩,
    monomial_mem_of_le k q I _ _ β.1.property (by intro j; simp only [Finsupp.add_apply]; omega)⟩

theorem degreeAdjoin_not_minimal (d : ℕ) (β : AdjoinDegreeIndex k q I d) :
    ¬MinimalGenerator k q I (degreeAdjoin k q I d β).val.val := by
  intro h
  have he := h.2 β.1.val.val (by intro j; simp only [degreeAdjoin,Finsupp.add_apply]; omega) β.1.property
  have hh := congrArg Finsupp.degree he
  rw [β.1.val.property,(degreeAdjoin k q I d β).val.property] at hh
  omega

def degreeDecompositionMap (d : ℕ) :
    MinimalDegreeMonomial k q I (d+1) ⊕ AdjoinDegreeIndex k q I d → IdealDegreeMonomial k q I (d+1)
  | .inl α => ⟨α.val,α.property.1⟩
  | .inr β => degreeAdjoin k q I d β

theorem degreeDecompositionMap_injective (d : ℕ) :
    Function.Injective (degreeDecompositionMap k q I d) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      congr 1
      apply Subtype.ext
      exact congrArg (fun z : IdealDegreeMonomial k q I (d+1) => z.val) hab
    | inr b =>
      have he := congrArg (fun z : IdealDegreeMonomial k q I (d+1) => z.val.val) hab
      exact False.elim (degreeAdjoin_not_minimal k q I d b (he ▸ a.property))
  | inr a =>
    cases b with
    | inl b =>
      have he := congrArg (fun z : IdealDegreeMonomial k q I (d+1) => z.val.val) hab
      exact False.elim (degreeAdjoin_not_minimal k q I d a (he.symm ▸ b.property))
    | inr b =>
      have he := congrArg (fun z : IdealDegreeMonomial k q I (d+1) => z.val.val) hab
      have hm := congrArg (maxVariable q) he
      change maxVariable q (a.1.val.val+Finsupp.single a.2.val 1)=
        maxVariable q (b.1.val.val+Finsupp.single b.2.val 1) at hm
      rw [maxVariable_add_single q _ _ a.2.property,maxVariable_add_single q _ _ b.2.property] at hm
      have hr : a.2.val=b.2.val := Fin.ext (by omega)
      have heβ : a.1.val.val=b.1.val.val := by
        change a.1.val.val+Finsupp.single a.2.val 1=b.1.val.val+Finsupp.single b.2.val 1 at he
        rw [hr] at he
        exact add_right_cancel he
      have hβ : a.1=b.1 := Subtype.ext (Subtype.ext heβ)
      cases a with | mk a r =>
        cases b with | mk b s =>
          dsimp at hβ hr
          subst b
          have hrs : r=s := Subtype.ext hr
          subst s
          rfl

theorem degreeDecompositionMap_surjective (hI : IsStronglyStable k q I) (d : ℕ) :
    Function.Surjective (degreeDecompositionMap k q I d) := by
  intro α
  by_cases hmin : MinimalGenerator k q I α.val.val
  · exact ⟨.inl ⟨α.val,hmin⟩,rfl⟩
  have hne : α.val.val≠0 := by
    intro hz
    have hd := α.val.property
    rw [hz,map_zero] at hd
    omega
  obtain ⟨r,hr,hm,hmax⟩ := maxVariable_spec q α.val.val hne
  have hmem : MvPolynomial.monomial (α.val.val-Finsupp.single r 1) (1:k)∈I := by
    by_contra hn
    exact hmin ((hI.remove_max_not_mem_iff_minimal k q I α.val.val α.property r hr hmax).mpr hn)
  let β := α.val.val-Finsupp.single r 1
  have hsingle : Finsupp.single r 1≤α.val.val := by
    intro j
    by_cases he : r=j
    · subst j; simpa using (Nat.succ_le_of_lt hr)
    · simp only [Finsupp.single_eq_of_ne' he]; exact Nat.zero_le _
  have hadd : β+Finsupp.single r 1=α.val.val := tsub_add_cancel_of_le hsingle
  have hdeg : β.degree=d := by
    have hd := congrArg Finsupp.degree hadd
    simp only [map_add,Finsupp.degree_single,α.val.property] at hd
    omega
  have hbmax : maxVariable q β≤r.val+1 := by
    apply (maxVariable_le_iff q β _).mpr
    intro j hj
    have hz := hmax j (by change r.val<j.val; omega)
    simp only [β,Finsupp.tsub_apply,hz,Nat.zero_sub]
  refine ⟨.inr ⟨⟨⟨β,hdeg⟩,hmem⟩,⟨r,hbmax⟩⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hadd

noncomputable def degreeDecompositionEquiv (hI : IsStronglyStable k q I) (d : ℕ) :
    MinimalDegreeMonomial k q I (d+1) ⊕ AdjoinDegreeIndex k q I d ≃ IdealDegreeMonomial k q I (d+1) :=
  Equiv.ofBijective (degreeDecompositionMap k q I d)
    ⟨degreeDecompositionMap_injective k q I d,degreeDecompositionMap_surjective k q I hI d⟩

end NSP14.Lex

namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ) (I : Ideal (MvPolynomial (Fin q) k))

theorem degreeBinomialSum_eq_sum (d i : ℕ) : degreeBinomialSum k q I d i=
    ∑ α : IdealDegreeMonomial k q I d,(maxVariable q α.val.val-1).choose i := by
  exact Finset.sum_subtype _ (by simp) _

theorem adjoin_binomial_identity (q m i : ℕ) (hm : m≤q) :
    (∑ r : {r : Fin q // m≤r.val+1},r.val.val.choose i)+(m-1).choose (i+1)=q.choose (i+1) := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun r : Fin q => m≤r.val+1)) (by simp) (fun r : Fin q => r.val.choose i),Finset.sum_filter,
    Fin.sum_univ_eq_sum_range (fun r => if m≤r+1 then r.choose i else 0),choose_as_max_sum q m i hm,
    ← Finset.sum_add_distrib,← sum_choose_column]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> omega

theorem IsStronglyStable.degree_binomial_identity (hI : IsStronglyStable k q I) (d i : ℕ) :
    degreeBinomialSum k q I (d+1) i+degreeBinomialSum k q I d (i+1)=
      (∑ α : MinimalDegreeMonomial k q I (d+1),(maxVariable q α.val.val-1).choose i)+
      idealDegreeCard k q I d*q.choose (i+1) := by
  rw [degreeBinomialSum_eq_sum,degreeBinomialSum_eq_sum]
  have he := (degreeDecompositionEquiv k q I hI d).sum_comp
    (fun α : IdealDegreeMonomial k q I (d+1) => (maxVariable q α.val.val-1).choose i)
  rw [← he,Fintype.sum_sum_type]
  change ((∑ α : MinimalDegreeMonomial k q I (d+1),(maxVariable q α.val.val-1).choose i)+
    ∑ β : AdjoinDegreeIndex k q I d,(maxVariable q (β.1.val.val+Finsupp.single β.2.val 1)-1).choose i)+
    (∑ α : IdealDegreeMonomial k q I d,(maxVariable q α.val.val-1).choose (i+1))=_
  have hadj (β : AdjoinDegreeIndex k q I d) :
      (maxVariable q (β.1.val.val+Finsupp.single β.2.val 1)-1).choose i=β.2.val.val.choose i := by
    rw [maxVariable_add_single q _ _ β.2.property,Nat.add_sub_cancel]
  simp_rw [hadj]
  rw [Fintype.sum_sigma,add_assoc,← Finset.sum_add_distrib]
  apply congrArg (_+·)
  calc
    (∑ β : IdealDegreeMonomial k q I d,
      ((∑ r : {r : Fin q // maxVariable q β.val.val≤r.val+1},r.val.val.choose i)+
        (maxVariable q β.val.val-1).choose (i+1)))=
      ∑ _β : IdealDegreeMonomial k q I d,q.choose (i+1) := by
        apply Finset.sum_congr rfl
        intro β _
        exact adjoin_binomial_identity q _ i (maxVariable_le_variables q β.val.val)
    _=idealDegreeCard k q I d*q.choose (i+1) := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,idealDegreeCard,IdealDegreeMonomial]
end NSP14.Lex

