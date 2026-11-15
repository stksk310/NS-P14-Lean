module
public import NSP14.Lex.BettiComparison
public import NSP14.Lex.EliahouKervaireOrdinary
@[expose] public section
open scoped Classical BigOperators
open NSP14.Homological
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)

def standardDegreeBinomialSum (I : Ideal (MvPolynomial (Fin q) k)) (d i : ℕ) : ℕ :=
  ∑ α∈Finset.univ.filter (fun α : PolynomialDegreeIndex q d => MvPolynomial.monomial α.val (1:k)∉I),
    (maxVariable q α.val-1).choose i

def fullDegreeBinomialSum (d i : ℕ) : ℕ :=
  ∑ α : PolynomialDegreeIndex q d,(maxVariable q α.val-1).choose i

theorem binomialDegree_partition (I : Ideal (MvPolynomial (Fin q) k)) (d i : ℕ) :
    degreeBinomialSum k q I d i+standardDegreeBinomialSum k q I d i=fullDegreeBinomialSum q d i := by
  exact Finset.sum_filter_add_sum_filter_not _ _ _

include k in
theorem fullDegreeBinomial_identity (d i : ℕ) :
    fullDegreeBinomialSum q (d+1) i+fullDegreeBinomialSum q d (i+1)=
      Fintype.card (PolynomialDegreeIndex q d)*q.choose (i+1) := by
  have htop : IsStronglyStable k q (⊤ : Ideal (MvPolynomial (Fin q) k)) :=
    ⟨by intro _ _ _ _; trivial,by intro _ _ _ _ _ _; trivial⟩
  let : IsEmpty (MinimalDegreeMonomial k q (⊤ : Ideal (MvPolynomial (Fin q) k)) (d+1)) := by
    refine ⟨fun α => ?_⟩
    have he := α.property.2 0 (by intro j; exact Nat.zero_le _) (by trivial)
    have hd := α.val.property
    rw [← he,map_zero] at hd
    omega
  have hh := htop.degree_binomial_identity k q ⊤ d i
  simpa [degreeBinomialSum,fullDegreeBinomialSum,idealDegreeCard] using hh

theorem IsStronglyStable.standard_graded_binomial_identity
    (I : Ideal (MvPolynomial (Fin q) k)) (hI : IsStronglyStable k q I) (hproper : I≠⊤)
    (hHom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (d i : ℕ) :
    quotientGradedBetti k q I hHom (i+1) (((d+1:ℕ):ℤ)+(i:ℤ))+
      standardDegreeBinomialSum k q I (d+1) i+standardDegreeBinomialSum k q I d (i+1)=
      quotientHilbert k q I hHom d*q.choose (i+1) := by
  have hi := hI.graded_betti_binomial_identity k q I hproper hHom d i
  have ht := fullDegreeBinomial_identity k q d i
  have hp1 := binomialDegree_partition k q I (d+1) i
  have hp0 := binomialDegree_partition k q I d (i+1)
  have hc := idealDegreeCard_add_hilbert k q I hHom hI.1 d
  have hmul := congrArg (fun n => n*q.choose (i+1)) hc
  rw [Nat.add_mul] at hmul
  omega


def standardDegreeChooseSum (I : Ideal (MvPolynomial (Fin q) k)) (d i : ℕ) : ℕ :=
  ∑ α∈Finset.univ.filter (fun α : PolynomialDegreeIndex q d => MvPolynomial.monomial α.val (1:k)∉I),
    (maxVariable q α.val).choose i

theorem standardDegreeBinomial_pascal (I : Ideal (MvPolynomial (Fin q) k)) (d i : ℕ) (hd : 1≤d) :
    standardDegreeBinomialSum k q I d i+standardDegreeBinomialSum k q I d (i+1)=standardDegreeChooseSum k q I d (i+1) := by
  rw [standardDegreeBinomialSum,standardDegreeBinomialSum,standardDegreeChooseSum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro α _
  have hn : α.val≠0 := by intro he; have hh:=α.property; rw [he,map_zero] at hh; omega
  obtain ⟨r,_,hr,_⟩ := maxVariable_spec q α.val hn
  have hm : 1≤maxVariable q α.val := by omega
  rw [← Nat.choose_succ_succ]
  simp only [Nat.succ_eq_add_one,Nat.sub_add_cancel hm]

theorem standardDegreeBinomial_zero_degree (I : Ideal (MvPolynomial (Fin q) k)) (i : ℕ) :
    standardDegreeBinomialSum k q I 0 (i+1)=0 := by
  apply Finset.sum_eq_zero
  intro α _
  have he : α.val=0 := (Finsupp.degree_eq_zero_iff _).mp α.property
  simp only [he,maxVariable,Finsupp.support_zero,Finset.sup_empty]
  change (0:ℕ).choose (i+1)=0
  exact Nat.choose_eq_zero_of_lt (by omega)

theorem standardDegreeBinomial_zero_of_hilbert (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (hmono : IsMonomial k q I)
    (d i : ℕ) (hH : quotientHilbert k q I hI d=0) : standardDegreeBinomialSum k q I d i=0 := by
  rw [quotientHilbert_eq_standard_card] at hH
  simp_rw [standardExponent_iff_not_mem k q hmono] at hH
  have he : Finset.univ.filter (fun α : PolynomialDegreeIndex q d => MvPolynomial.monomial α.val (1:k)∉I)=∅ := by
    apply Finset.card_eq_zero.mp
    simpa only [Fintype.card_subtype] using hH
  rw [standardDegreeBinomialSum,he,Finset.sum_empty]

theorem IsStronglyStable.standard_finite_graded_identity
    (I : Ideal (MvPolynomial (Fin q) k)) (hI : IsStronglyStable k q I) (hproper : I≠⊤)
    (hHom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (N i : ℕ)
    (hN : quotientHilbert k q I hHom (N+1)=0) :
    (∑ d∈Finset.range (N+1),quotientGradedBetti k q I hHom (i+1) (((d+1:ℕ):ℤ)+(i:ℤ)))+
      (∑ d∈Finset.range N,standardDegreeChooseSum k q I (d+1) (i+1))=
        (∑ d∈Finset.range (N+1),quotientHilbert k q I hHom d)*q.choose (i+1) := by
  have hh := Finset.sum_congr (s₁:=Finset.range (N+1)) rfl
    (fun d _ => hI.standard_graded_binomial_identity k q I hproper hHom d i)
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.sum_mul] at hh
  have hfirst : (∑ d∈Finset.range (N+1),standardDegreeBinomialSum k q I (d+1) i)=
      ∑ d∈Finset.range N,standardDegreeBinomialSum k q I (d+1) i := by
    rw [Finset.sum_range_succ,standardDegreeBinomial_zero_of_hilbert k q I hHom hI.1 (N+1) i hN,add_zero]
  have hsecond : (∑ d∈Finset.range (N+1),standardDegreeBinomialSum k q I d (i+1))=
      ∑ d∈Finset.range N,standardDegreeBinomialSum k q I (d+1) (i+1) := by
    rw [Finset.sum_range_succ',standardDegreeBinomial_zero_degree,add_zero]
  rw [hfirst,hsecond,add_assoc,← Finset.sum_add_distrib] at hh
  have hpas (d : ℕ) := standardDegreeBinomial_pascal k q I (d+1) i (by omega)
  simp_rw [hpas] at hh
  exact hh


theorem IsStronglyStable.minimal_degree_le_cutoff
    (I : Ideal (MvPolynomial (Fin q) k)) (hI : IsStronglyStable k q I) (hproper : I≠⊤)
    (hHom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (N : ℕ)
    (hN : ∀ n,N<n → quotientHilbert k q I hHom n=0)
    (v : Fin q →₀ ℕ) (hv : MinimalGenerator k q I v) : v.degree≤N+1 := by
  obtain ⟨r,hr,_,hmax⟩ := maxVariable_spec q v (minimalGenerator_ne_zero q k I hproper v hv)
  have hnot := (hI.remove_max_not_mem_iff_minimal k q I v hv.1 r hr hmax).mp hv
  let β := v-Finsupp.single r 1
  have hsingle : Finsupp.single r 1≤v := by
    intro j
    by_cases he : r=j
    · subst j; simpa using (Nat.succ_le_of_lt hr)
    · simp only [Finsupp.single_eq_of_ne' he]; exact Nat.zero_le _
  have hadd : β+Finsupp.single r 1=v := tsub_add_cancel_of_le hsingle
  have hd : β.degree+1=v.degree := by have hh:=congrArg Finsupp.degree hadd; simpa only [map_add,Finsupp.degree_single] using hh
  have hpos : 0<quotientHilbert k q I hHom β.degree := by
    rw [quotientHilbert_eq_standard_card]
    apply Fintype.card_pos_iff.mpr
    exact ⟨⟨⟨β,rfl⟩,(standardExponent_iff_not_mem k q hI.1 MonomialOrder.degLex β).mpr hnot⟩⟩
  by_contra hn
  have hz := hN β.degree (by omega)
  omega

theorem sum_range_degree_filter {A : Type*} (g : Finset A) (n f : A → ℕ) (N : ℕ)
    (hp : ∀ a∈g,1≤n a) (hb : ∀ a∈g,n a≤N+1) :
    (∑ d∈Finset.range (N+1),∑ a∈g,if n a=d+1 then f a else 0)=∑ a∈g,f a := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  have hpos := hp a ha
  have hbound := hb a ha
  rw [Finset.sum_eq_single (n a-1)]
  · rw [ite_eq_left (by omega)]
  · intro d _ hne
    rw [ite_eq_right (by omega)]
  · intro hn
    have hh : n a-1∈Finset.range (N+1) := Finset.mem_range.mpr (by omega)
    exact False.elim (hn hh)

theorem IsLex.total_eq_finite_graded
    (I : Ideal (MvPolynomial (Fin q) k)) (hI : IsLex k q I) (hproper : I≠⊤)
    (hHom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (N i : ℕ)
    (hN : ∀ n,N<n → quotientHilbert k q I hHom n=0) :
    totalBetti k (Fin q) (NSP14.Endpoint.artinModule k (Fin q) I) (i+1)=
      ∑ d∈Finset.range (N+1),quotientGradedBetti k q I hHom (i+1) (((d+1:ℕ):ℤ)+(i:ℤ)) := by
  have hsI : IsStronglyStable k q I := ⟨hI.1,fun v hv a b hp hab => hI.raise k q v hv a b hp hab⟩
  rw [hI.ordinary_ek k q hproper (minimalGeneratorFinset k q I) (mem_minimalGeneratorFinset k q I) (i+1) (by omega)]
  simp only [Nat.add_sub_cancel]
  have hp (v) (hv : v∈minimalGeneratorFinset k q I) : 1≤v.degree := by
    have hn := minimalGenerator_ne_zero q k I hproper v ((mem_minimalGeneratorFinset k q I v).mp hv)
    have hh : v.degree≠0 := fun he => hn ((Finsupp.degree_eq_zero_iff v).mp he)
    omega
  rw [← sum_range_degree_filter (minimalGeneratorFinset k q I) Finsupp.degree (fun v => (maxVariable q v-1).choose i) N hp
    (fun v hv => hsI.minimal_degree_le_cutoff k q I hproper hHom N hN v ((mem_minimalGeneratorFinset k q I v).mp hv))]
  apply Finset.sum_congr rfl
  intro d _
  rw [hsI.graded_ek_degree k q I hproper hHom,← minimal_degree_sum_eq,Finset.sum_filter]

theorem IsLex.standard_finite_total_identity
    (I : Ideal (MvPolynomial (Fin q) k)) (hI : IsLex k q I) (hproper : I≠⊤)
    (hHom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (N i : ℕ)
    (hN : ∀ n,N<n → quotientHilbert k q I hHom n=0) :
    totalBetti k (Fin q) (NSP14.Endpoint.artinModule k (Fin q) I) (i+1)+
      (∑ d∈Finset.range N,standardDegreeChooseSum k q I (d+1) (i+1))=
        (∑ d∈Finset.range (N+1),quotientHilbert k q I hHom d)*q.choose (i+1) := by
  have hsI : IsStronglyStable k q I := ⟨hI.1,fun v hv a b hp hab => hI.raise k q v hv a b hp hab⟩
  rw [hI.total_eq_finite_graded k q I hproper hHom N i hN]
  exact hsI.standard_finite_graded_identity k q I hproper hHom N i (hN (N+1) (by omega))


def degreeOneSingle (q : ℕ) (r : Fin q) : PolynomialDegreeIndex q 1 :=
  ⟨Finsupp.single r 1,Finsupp.degree_single r 1⟩

theorem degreeOneSingle_bijective (q : ℕ) : Function.Bijective (degreeOneSingle q) := by
  constructor
  · intro a b he
    have hh := congrArg Subtype.val he
    exact Finsupp.single_left_injective (by decide : (1:ℕ)≠0) hh
  · intro α
    have hn : α.val≠0 := by intro he; have hh:=α.property; rw [he,map_zero] at hh; omega
    obtain ⟨r,hr,_,_⟩ := maxVariable_spec q α.val hn
    have hsingle : Finsupp.single r 1≤α.val := by
      intro j
      by_cases he : r=j
      · subst j; simpa using (Nat.succ_le_of_lt hr)
      · simp only [Finsupp.single_eq_of_ne' he]; exact Nat.zero_le _
    have he : Finsupp.single r 1=α.val := by
      by_contra hne
      have hd := exponent_degree_strict q hsingle hne
      rw [Finsupp.degree_single,α.property] at hd
      omega
    exact ⟨r,Subtype.ext he⟩

noncomputable def degreeOneEquiv (q : ℕ) : Fin q ≃ PolynomialDegreeIndex q 1 :=
  Equiv.ofBijective (degreeOneSingle q) (degreeOneSingle_bijective q)

theorem degreeOne_card (q : ℕ) : Fintype.card (PolynomialDegreeIndex q 1)=q := by
  rw [← Fintype.card_congr (degreeOneEquiv q),Fintype.card_fin]

theorem standardDegreeChoose_one (I : Ideal (MvPolynomial (Fin q) k))
    (hHom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (hmono : IsMonomial k q I)
    (hH1 : quotientHilbert k q I hHom 1=q) (i : ℕ) : standardDegreeChooseSum k q I 1 (i+1)=(q+1).choose (i+2) := by
  have hc := idealDegreeCard_add_hilbert k q I hHom hmono 1
  rw [hH1,degreeOne_card] at hc
  have he : Finset.univ.filter (fun α : PolynomialDegreeIndex q 1 => MvPolynomial.monomial α.val (1:k)∈I)=∅ := by
    apply Finset.card_eq_zero.mp
    have hcz : idealDegreeCard k q I 1=0 := by omega
    simpa only [idealDegreeCard,Fintype.card_subtype] using hcz
  have hn (α : PolynomialDegreeIndex q 1) : MvPolynomial.monomial α.val (1:k)∉I := by
    intro hmem
    have hh : α∈Finset.univ.filter (fun β : PolynomialDegreeIndex q 1 => MvPolynomial.monomial β.val (1:k)∈I) := by simp only [Finset.mem_filter,Finset.mem_univ,true_and]; exact hmem
    rw [he] at hh
    exact Finset.notMem_empty _ hh
  rw [standardDegreeChooseSum]
  have hf : Finset.univ.filter (fun α : PolynomialDegreeIndex q 1 => MvPolynomial.monomial α.val (1:k)∉I)=Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro α _
    exact hn α
  rw [hf]
  rw [← (degreeOneEquiv q).sum_comp]
  change (∑ r : Fin q,(maxVariable q (Finsupp.single r 1)).choose (i+1))=(q+1).choose (i+2)
  have hmax (r : Fin q) : maxVariable q (Finsupp.single r 1)=r.val+1 := by
    simpa only [zero_add] using maxVariable_add_single q 0 r (by simp [maxVariable])
  simp_rw [hmax]
  rw [Fin.sum_univ_eq_sum_range (fun r => (r+1).choose (i+1)) q]
  have hh := sum_choose_column (q+1) (i+1)
  rw [Finset.sum_range_succ'] at hh
  simpa only [Nat.choose_zero_succ,add_zero] using hh

theorem choose_gap_bound (q m i : ℕ) (hm : m≤q) :
    q.choose (i+1)≤m.choose (i+1)+(q-m)*(q-1).choose i := by
  rw [← sum_choose_column,← sum_choose_column]
  have hh := Finset.sum_range_add_sum_Ico (fun r => r.choose i) hm
  have hb : (∑ r∈Finset.Ico m q,r.choose i)≤(q-m)*(q-1).choose i := by
    calc
      (∑ r∈Finset.Ico m q,r.choose i)≤∑ _r∈Finset.Ico m q,(q-1).choose i := by
        apply Finset.sum_le_sum
        intro r hr
        exact Nat.choose_le_choose i (by have hh:=(Finset.mem_Ico.mp hr).2; omega)
      _=(q-m)*(q-1).choose i := by simp only [Finset.sum_const,Nat.card_Ico,nsmul_eq_mul,Nat.cast_id]
  omega


def standardDegreeGapSum (I : Ideal (MvPolynomial (Fin q) k)) (d : ℕ) : ℕ :=
  ∑ α∈Finset.univ.filter (fun α : PolynomialDegreeIndex q d => MvPolynomial.monomial α.val (1:k)∉I),(q-maxVariable q α.val)

def lexCorrection (I : Ideal (MvPolynomial (Fin q) k)) (N : ℕ) : ℕ :=
  ∑ d∈Finset.range N,standardDegreeGapSum k q I (d+2)

theorem standardDegree_gap_bound (I : Ideal (MvPolynomial (Fin q) k))
    (hHom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (hmono : IsMonomial k q I) (d i : ℕ) :
    quotientHilbert k q I hHom d*q.choose (i+1)≤
      standardDegreeChooseSum k q I d (i+1)+standardDegreeGapSum k q I d*(q-1).choose i := by
  have hc : quotientHilbert k q I hHom d=
      (Finset.univ.filter (fun α : PolynomialDegreeIndex q d => MvPolynomial.monomial α.val (1:k)∉I)).card := by
    rw [quotientHilbert_eq_standard_card]
    simp_rw [standardExponent_iff_not_mem k q hmono]
    exact Fintype.card_subtype _
  rw [hc]
  let S := Finset.univ.filter (fun α : PolynomialDegreeIndex q d => MvPolynomial.monomial α.val (1:k)∉I)
  calc
    S.card*q.choose (i+1)=(∑ _α∈S,q.choose (i+1)) := by
      simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id]
    _≤∑ α∈S,((maxVariable q α.val).choose (i+1)+(q-maxVariable q α.val)*(q-1).choose i) := by
      apply Finset.sum_le_sum
      intro α _
      exact choose_gap_bound q (maxVariable q α.val) i (maxVariable_le_variables q α.val)
    _=standardDegreeChooseSum k q I d (i+1)+standardDegreeGapSum k q I d*(q-1).choose i := by
      rw [Finset.sum_add_distrib,← Finset.sum_mul]
      rfl

theorem standardDegree_gap_partition (I : Ideal (MvPolynomial (Fin q) k))
    (hHom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (hmono : IsMonomial k q I) (d : ℕ) :
    quotientHilbert k q I hHom d*q=
      standardDegreeChooseSum k q I d 1+standardDegreeGapSum k q I d := by
  have hc : quotientHilbert k q I hHom d=
      (Finset.univ.filter (fun α : PolynomialDegreeIndex q d => MvPolynomial.monomial α.val (1:k)∉I)).card := by
    rw [quotientHilbert_eq_standard_card]
    simp_rw [standardExponent_iff_not_mem k q hmono]
    exact Fintype.card_subtype _
  rw [hc]
  unfold standardDegreeChooseSum standardDegreeGapSum
  rw [← Finset.sum_add_distrib]
  have hh (α : PolynomialDegreeIndex q d) : (maxVariable q α.val).choose 1+(q-maxVariable q α.val)=q := by
    rw [Nat.choose_one_right,Nat.add_sub_of_le (maxVariable_le_variables q α.val)]
  simp_rw [hh]
  simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id]

theorem IsLex.standard_tail_identity
    (I : Ideal (MvPolynomial (Fin q) k)) (hI : IsLex k q I) (hproper : I≠⊤)
    (hHom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (N i : ℕ)
    (hN : ∀ n,N+1<n → quotientHilbert k q I hHom n=0)
    (hH0 : quotientHilbert k q I hHom 0=1) (hH1 : quotientHilbert k q I hHom 1=q) :
    totalBetti k (Fin q) (NSP14.Endpoint.artinModule k (Fin q) I) (i+1)+
      (∑ d∈Finset.range N,standardDegreeChooseSum k q I (d+2) (i+1))=
        (i+1)*(q+1).choose (i+2)+(∑ d∈Finset.range N,quotientHilbert k q I hHom (d+2))*q.choose (i+1) := by
  have hh := hI.standard_finite_total_identity k q I hproper hHom (N+1) i hN
  have hS : (∑ d∈Finset.range (N+1),standardDegreeChooseSum k q I (d+1) (i+1))=
      (∑ d∈Finset.range N,standardDegreeChooseSum k q I (d+2) (i+1))+(q+1).choose (i+2) := by
    rw [Finset.sum_range_succ',standardDegreeChoose_one k q I hHom hI.1 hH1]
  have hH : (∑ d∈Finset.range (N+1+1),quotientHilbert k q I hHom d)=
      (∑ d∈Finset.range N,quotientHilbert k q I hHom (d+2))+q+1 := by
    rw [Finset.sum_range_succ',Finset.sum_range_succ',hH0,hH1]
  rw [hS,hH] at hh
  have hmul := Nat.add_one_mul_choose_eq q (i+1)
  nlinarith only [hh,hmul]

theorem IsLex.total_betti_le_correction
    (I : Ideal (MvPolynomial (Fin q) k)) (hI : IsLex k q I) (hproper : I≠⊤)
    (hHom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (N i : ℕ)
    (hN : ∀ n,N+1<n → quotientHilbert k q I hHom n=0)
    (hH0 : quotientHilbert k q I hHom 0=1) (hH1 : quotientHilbert k q I hHom 1=q) :
    totalBetti k (Fin q) (NSP14.Endpoint.artinModule k (Fin q) I) (i+1)≤
      (i+1)*(q+1).choose (i+2)+lexCorrection k q I N*(q-1).choose i := by
  have hh := hI.standard_tail_identity k q I hproper hHom N i hN hH0 hH1
  have hb := Finset.sum_le_sum (s:=Finset.range N)
    (fun d _ => standardDegree_gap_bound k q I hHom hI.1 (d+2) i)
  rw [Finset.sum_add_distrib,← Finset.sum_mul,← Finset.sum_mul] at hb
  change _≤_+lexCorrection k q I N*(q-1).choose i at hb
  omega

theorem IsLex.first_betti_eq_correction
    (I : Ideal (MvPolynomial (Fin q) k)) (hI : IsLex k q I) (hproper : I≠⊤)
    (hHom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (N : ℕ)
    (hN : ∀ n,N+1<n → quotientHilbert k q I hHom n=0)
    (hH0 : quotientHilbert k q I hHom 0=1) (hH1 : quotientHilbert k q I hHom 1=q) :
    totalBetti k (Fin q) (NSP14.Endpoint.artinModule k (Fin q) I) 1=(q+1).choose 2+lexCorrection k q I N := by
  have hh := hI.standard_tail_identity k q I hproper hHom N 0 hN hH0 hH1
  simp only [Nat.zero_add,one_mul,Nat.choose_one_right] at hh
  have hp := Finset.sum_congr (s₁:=Finset.range N) rfl (fun d _ => standardDegree_gap_partition k q I hHom hI.1 (d+2))
  rw [Finset.sum_add_distrib,← Finset.sum_mul] at hp
  change _=_+lexCorrection k q I N at hp
  omega
end NSP14.Lex
