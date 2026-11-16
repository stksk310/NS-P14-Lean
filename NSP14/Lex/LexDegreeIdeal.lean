module
public import NSP14.Lex.BettiComparison
@[expose] public section
open scoped Classical BigOperators
open NSP14.Homological
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Lex

theorem remove_max_lex_ge_divisor (q : ℕ) (u v : Fin q →₀ ℕ) (r j : Fin q)
    (hr : 0<u r) (hm : ∀ l,r<l → u l=0)
    (hdeg : u.degree=v.degree+1)
    (hle : MonomialOrder.lex.toSyn (v+Finsupp.single j 1)≤MonomialOrder.lex.toSyn u) :
    MonomialOrder.lex.toSyn v≤MonomialOrder.lex.toSyn (u-Finsupp.single r 1) := by
  let β := u-Finsupp.single r 1
  have hsingle : Finsupp.single r 1≤u := by
    intro l
    by_cases he : r=l
    · subst l; simpa using (Nat.succ_le_of_lt hr)
    · simp only [Finsupp.single_eq_of_ne' he]; exact Nat.zero_le _
  have hadd : β+Finsupp.single r 1=u := tsub_add_cancel_of_le hsingle
  have hdegβ : v.degree=β.degree := by
    have hh := congrArg Finsupp.degree hadd
    simp only [map_add,Finsupp.degree_single] at hh
    omega
  have hmaxβ : ∀ l,r<l → β l=0 := by
    intro l hl
    simp only [β,Finsupp.tsub_apply,hm l hl,Nat.zero_sub]
  have hβ (l : Fin q) (hl : l<r) : β l=u l := by
    simp only [β,Finsupp.tsub_apply,Finsupp.single_eq_of_ne' (ne_of_gt hl),Nat.sub_zero]
  by_contra hn
  have hlt : MonomialOrder.lex.toSyn β<MonomialOrder.lex.toSyn v := lt_of_not_ge hn
  have hlex := hlt
  change Finsupp.Lex (· < ·) (· < ·) β v at hlex
  obtain ⟨a,ha,hav⟩ := hlex
  have har : a<r := by
    by_contra hnot
    have hp (l : Fin q) (hl : l<r) : v l≤β l := (ha l (hl.trans_le (le_of_not_gt hnot))).symm.le
    exact not_lt_of_ge (lex_le_of_prefix q v β r hdegβ hp hmaxβ) hlt
  apply not_lt_of_ge hle
  change Finsupp.Lex (· < ·) (· < ·) u (v+Finsupp.single j 1)
  by_cases hja : j<a
  · refine ⟨j,?_,?_⟩
    · intro l hl
      have hlr := hl.trans (hja.trans har)
      rw [Finsupp.add_apply,Finsupp.single_eq_of_ne' (ne_of_gt hl),add_zero]
      exact ((hβ l hlr).symm.trans (ha l (hl.trans hja)))
    · rw [Finsupp.add_apply,Finsupp.single_eq_same]
      have he := (hβ j (hja.trans har)).symm.trans (ha j hja)
      omega
  · refine ⟨a,?_,?_⟩
    · intro l hl
      have hjl : j≠l := by intro he; subst l; exact hja hl
      rw [Finsupp.add_apply,Finsupp.single_eq_of_ne' hjl,add_zero]
      exact ((hβ l (hl.trans har)).symm.trans (ha l hl))
    · rw [Finsupp.add_apply]
      have hh := hβ a har
      omega

theorem exists_upper_finset_card {A B : Type*} [Fintype A] [LinearOrder B]
    (f : A → B) (hf : Function.Injective f) :
    ∀ m : ℕ,m≤Fintype.card A → ∃ S : Finset A,S.card=m ∧ ∀ a∈S,∀ b,f a≤f b → b∈S := by
  intro m
  induction m with
  | zero => intro _; exact ⟨∅,rfl,by simp⟩
  | succ m ih =>
    intro hm
    obtain ⟨S,hcard,hupper⟩ := ih (by omega)
    let T := Finset.univ\S
    have hT : T.Nonempty := by
      by_contra hn
      have he := Finset.not_nonempty_iff_eq_empty.mp hn
      have hs : Finset.univ⊆S := Finset.sdiff_eq_empty_iff_subset.mp he
      have hh := Finset.card_le_card hs
      simp only [Finset.card_univ] at hh
      omega
    let D := T.image f
    obtain ⟨a,ha,hea⟩ := Finset.mem_image.mp (Finset.max'_mem D (hT.image f))
    have han : a∉S := (Finset.mem_sdiff.mp ha).2
    refine ⟨insert a S,by rw [Finset.card_insert_of_notMem han,hcard],?_⟩
    intro b hb c hbc
    rcases Finset.mem_insert.mp hb with rfl|hb
    · by_cases hc : c∈S
      · exact Finset.mem_insert_of_mem hc
      · have hcT : c∈T := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hc⟩
        have hca : f c≤f b := by
          rw [hea]
          exact Finset.le_max' D _ (Finset.mem_image.mpr ⟨c,hcT,rfl⟩)
        exact Finset.mem_insert.mpr (Or.inl (hf (le_antisymm hca hbc)))
    · exact Finset.mem_insert_of_mem (hupper b hb c hbc)

variable (k : Type) [Field k] (q d : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

def degreeSupport (S : Finset (PolynomialDegreeIndex q d)) : Set (Fin q →₀ ℕ) :=
  Subtype.val '' (S : Set (PolynomialDegreeIndex q d))
def degreeGeneratedIdeal (S : Finset (PolynomialDegreeIndex q d)) : Ideal (MvPolynomial (Fin q) k) :=
  Ideal.span ((fun v => MvPolynomial.monomial v (1:k)) '' degreeSupport q d S)

theorem degreeGeneratedIdeal_isMonomial (S : Finset (PolynomialDegreeIndex q d)) :
    IsMonomial k q (degreeGeneratedIdeal k q d S) := by
  intro f hf v hv
  obtain ⟨w,hw,hle⟩ := MvPolynomial.mem_ideal_span_monomial_image.mp hf v hv
  exact (monomial_mem_span_iff k q _ v).mpr ⟨w,hw,hle⟩

theorem degreeGeneratedIdeal_homogeneous (S : Finset (PolynomialDegreeIndex q d)) :
    (degreeGeneratedIdeal k q d S).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k) := by
  apply Ideal.homogeneous_span
  rintro _ ⟨v,_,rfl⟩
  exact ⟨v.degree,MvPolynomial.isHomogeneous_monomial (1:k) rfl⟩

theorem degreeGeneratedIdeal_degree_mem (S : Finset (PolynomialDegreeIndex q d))
    (α : PolynomialDegreeIndex q d) :
    MvPolynomial.monomial α.val (1:k)∈degreeGeneratedIdeal k q d S ↔ α∈S := by
  rw [degreeGeneratedIdeal,monomial_mem_span_iff]
  constructor
  · rintro ⟨v,⟨β,hβ,rfl⟩,hle⟩
    have he : β.val=α.val := by
      by_contra hn
      have hh := exponent_degree_strict q hle hn
      rw [β.property,α.property] at hh
      omega
    exact (Subtype.ext he : β=α) ▸ hβ
  · intro hα
    exact ⟨α.val,⟨α,hα,rfl⟩,le_rfl⟩

theorem degreeGeneratedIdeal_isLex (S : Finset (PolynomialDegreeIndex q d))
    (hupper : ∀ a∈S,∀ b : PolynomialDegreeIndex q d,
      MonomialOrder.lex.toSyn a.val≤MonomialOrder.lex.toSyn b.val → b∈S) :
    IsLex k q (degreeGeneratedIdeal k q d S) := by
  refine ⟨degreeGeneratedIdeal_isMonomial k q d S,?_⟩
  have hmain : ∀ n : ℕ,∀ α β : Fin q →₀ ℕ,α.degree=n → β.degree=n →
      MonomialOrder.lex.toSyn α≤MonomialOrder.lex.toSyn β →
      MvPolynomial.monomial α (1:k)∈degreeGeneratedIdeal k q d S →
      MvPolynomial.monomial β (1:k)∈degreeGeneratedIdeal k q d S := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro α β hα hβ hlex hmem
      obtain ⟨v,⟨a,ha,hav⟩,hle⟩ := (monomial_mem_span_iff k q (degreeSupport q d S) α).mp hmem
      subst v
      have hdn : d≤n := by
        by_cases he : a.val=α
        · have hh := congrArg Finsupp.degree he; omega
        · have hh := exponent_degree_strict q hle he; omega
      by_cases hnd : n=d
      · have hαd : α.degree=d := hα.trans hnd
        have hβd : β.degree=d := hβ.trans hnd
        apply (degreeGeneratedIdeal_degree_mem k q d S ⟨β,hβd⟩).mpr
        apply hupper ⟨α,hαd⟩ ((degreeGeneratedIdeal_degree_mem k q d S ⟨α,hαd⟩).mp hmem) ⟨β,hβd⟩ hlex
      have hex : ∃ j,a.val j<α j := by
        by_contra! hn
        have he : a.val=α := by ext j; exact le_antisymm (hle j) (hn j)
        have hh := congrArg Finsupp.degree he
        omega
      obtain ⟨j,hj⟩ := hex
      let α' := α-Finsupp.single j 1
      have hasingle : Finsupp.single j 1≤α := by
        intro l
        by_cases he : j=l
        · subst l; simpa using (show 1≤α j by omega)
        · simp only [Finsupp.single_eq_of_ne' he]; exact Nat.zero_le _
      have haadd : α'+Finsupp.single j 1=α := tsub_add_cancel_of_le hasingle
      have hα'd : α'.degree+1=n := by have hh:=congrArg Finsupp.degree haadd; simpa only [map_add,Finsupp.degree_single,hα] using hh
      have hα'mem : MvPolynomial.monomial α' (1:k)∈degreeGeneratedIdeal k q d S := by
        apply (monomial_mem_span_iff k q _ _).mpr
        refine ⟨a.val,⟨a,ha,rfl⟩,?_⟩
        intro l
        by_cases he : j=l
        · subst l; simp only [α',Finsupp.tsub_apply,Finsupp.single_eq_same]; omega
        · simpa only [α',Finsupp.tsub_apply,Finsupp.single_eq_of_ne' he,Nat.sub_zero] using hle l
      have hβne : β≠0 := by intro he; rw [he,map_zero] at hβ; omega
      obtain ⟨r,hr,_,hmax⟩ := maxVariable_spec q β hβne
      let β' := β-Finsupp.single r 1
      have hbsingle : Finsupp.single r 1≤β := by
        intro l
        by_cases he : r=l
        · subst l; simpa using (Nat.succ_le_of_lt hr)
        · simp only [Finsupp.single_eq_of_ne' he]; exact Nat.zero_le _
      have hbadd : β'+Finsupp.single r 1=β := tsub_add_cancel_of_le hbsingle
      have hβ'd : β'.degree=α'.degree := by have hh:=congrArg Finsupp.degree hbadd; simp only [map_add,Finsupp.degree_single,hβ] at hh; omega
      have hle' : MonomialOrder.lex.toSyn α'≤MonomialOrder.lex.toSyn β' :=
        remove_max_lex_ge_divisor q β α' r j hr hmax (by omega) (by simpa only [haadd] using hlex)
      have hbmem := ih α'.degree (by omega) α' β' rfl hβ'd hle' hα'mem
      apply monomial_mem_of_le k q _ β' β hbmem
      intro l
      exact Nat.sub_le _ _
  intro α β hdeg hlex hmem
  exact hmain α.degree α β rfl hdeg.symm hlex hmem


end NSP14.Lex
