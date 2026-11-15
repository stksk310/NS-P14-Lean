module
public import NSP14.Lex.StrongStableRestriction
public import NSP14.Lex.SmallVariableComparison
public import Mathlib.Algebra.MvPolynomial.Rename
@[expose] public section
open scoped Classical BigOperators
open NSP14.Homological
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Lex

def prefixExponent (q : ℕ) (α : Fin q →₀ ℕ) : Fin (q+1) →₀ ℕ :=
  α.embDomain Fin.castSuccEmb

@[simp] theorem prefixExponent_castSucc (q : ℕ) (α : Fin q →₀ ℕ) (i : Fin q) :
    prefixExponent q α i.castSucc=α i := Finsupp.embDomain_apply_self Fin.castSuccEmb α i

@[simp] theorem prefixExponent_last (q : ℕ) (α : Fin q →₀ ℕ) :
    prefixExponent q α (Fin.last q)=0 := by
  apply Finsupp.embDomain_of_notMem_range
  rintro ⟨i,hi⟩
  exact (Fin.castSucc_ne_last i) hi

@[simp] theorem prefixExponent_degree (q : ℕ) (α : Fin q →₀ ℕ) :
    (prefixExponent q α).degree=α.degree := by
  rw [prefixExponent,Finsupp.embDomain_eq_mapDomain,Finsupp.degree_mapDomain]

theorem prefixExponent_raised (q : ℕ) (α : Fin q →₀ ℕ) (a b : Fin q) :
    prefixExponent q (raisedExponent q α a b)=
      raisedExponent (q+1) (prefixExponent q α) a.castSucc b.castSucc := by
  ext x
  refine Fin.lastCases ?_ (fun i => ?_) x
  · simp only [prefixExponent_last,raisedExponent,Finsupp.add_apply,Finsupp.tsub_apply,
      Finsupp.single_eq_of_ne (Fin.castSucc_ne_last a).symm,
      Finsupp.single_eq_of_ne (Fin.castSucc_ne_last b).symm,Nat.sub_zero,add_zero]
  · simp only [prefixExponent_castSucc,raisedExponent,Finsupp.add_apply,Finsupp.tsub_apply,
      Finsupp.single_apply,Fin.castSucc_inj]

theorem prefixExponent_lex_lt (q : ℕ) (α β : Fin q →₀ ℕ)
    (h : MonomialOrder.lex.toSyn α<MonomialOrder.lex.toSyn β) :
    MonomialOrder.lex.toSyn (prefixExponent q α)<MonomialOrder.lex.toSyn (prefixExponent q β) := by
  change Finsupp.Lex (· < ·) (· < ·) α β at h
  change Finsupp.Lex (· < ·) (· < ·) (prefixExponent q α) (prefixExponent q β)
  obtain ⟨i,hi,hlt⟩ := h
  refine ⟨i.castSucc,?_,?_⟩
  · intro j hji
    let j' : Fin q := ⟨j.val,by have := i.isLt; change j.val < i.val at hji; omega⟩
    have he : j'.castSucc=j := Fin.ext rfl
    rw [← he,prefixExponent_castSucc,prefixExponent_castSucc]
    exact hi j' hji
  · simpa only [prefixExponent_castSucc] using hlt

theorem prefixExponent_lex_le (q : ℕ) (α β : Fin q →₀ ℕ)
    (h : MonomialOrder.lex.toSyn α≤MonomialOrder.lex.toSyn β) :
    MonomialOrder.lex.toSyn (prefixExponent q α)≤MonomialOrder.lex.toSyn (prefixExponent q β) := by
  rcases h.eq_or_lt with he|hlt
  · have hab : α=β := MonomialOrder.lex.toSyn.injective he
    subst β
    exact le_rfl
  · exact (prefixExponent_lex_lt q α β hlt).le

variable (k : Type) [Field k] (q : ℕ)

def prefixVariableIdeal (I : Ideal (MvPolynomial (Fin (q+1)) k)) : Ideal (MvPolynomial (Fin q) k) :=
  I.comap (MvPolynomial.rename (R:=k) (Fin.castSucc : Fin q → Fin (q+1))).toRingHom

theorem prefixVariableIdeal_monomial (I : Ideal (MvPolynomial (Fin (q+1)) k)) (α : Fin q →₀ ℕ) :
    MvPolynomial.monomial α (1:k)∈prefixVariableIdeal k q I ↔
      MvPolynomial.monomial (prefixExponent q α) (1:k)∈I := by
  change MvPolynomial.rename Fin.castSucc (MvPolynomial.monomial α (1:k))∈I ↔ _
  rw [MvPolynomial.rename_monomial,prefixExponent,Finsupp.embDomain_eq_mapDomain,Fin.coe_castSuccEmb]

theorem prefixVariableIdeal_isMonomial (I : Ideal (MvPolynomial (Fin (q+1)) k))
    (hI : IsMonomial k (q+1) I) : IsMonomial k q (prefixVariableIdeal k q I) := by
  intro f hf α hα
  change MvPolynomial.rename Fin.castSucc f∈I at hf
  have hs : prefixExponent q α∈(MvPolynomial.rename (R:=k) Fin.castSucc f).support := by
    rw [MvPolynomial.support_rename_of_injective (Fin.castSucc_injective q)]
    exact Finset.mem_image.mpr ⟨α,hα,(Finsupp.embDomain_eq_mapDomain Fin.castSuccEmb α).symm⟩
  exact (prefixVariableIdeal_monomial k q I α).mpr (hI _ hf _ hs)

theorem prefixVariableIdeal_isLex (I : Ideal (MvPolynomial (Fin (q+1)) k)) (hI : IsLex k (q+1) I) :
    IsLex k q (prefixVariableIdeal k q I) := by
  refine ⟨prefixVariableIdeal_isMonomial k q I hI.1,?_⟩
  intro α β hdeg hle hm
  rw [prefixVariableIdeal_monomial] at hm ⊢
  exact hI.2 _ _ (by simpa only [prefixExponent_degree] using hdeg)
    (prefixExponent_lex_le q α β hle) hm

theorem prefixVariableIdeal_isStronglyStable (I : Ideal (MvPolynomial (Fin (q+1)) k))
    (hI : IsStronglyStable k (q+1) I) : IsStronglyStable k q (prefixVariableIdeal k q I) := by
  refine ⟨prefixVariableIdeal_isMonomial k q I hI.1,?_⟩
  intro α hα a b hb hab
  rw [prefixVariableIdeal_monomial] at hα ⊢
  rw [prefixExponent_raised]
  exact hI.2 _ hα a.castSucc b.castSucc (by simpa only [prefixExponent_castSucc] using hb) hab

/-- Restricting the actual exponent function to the first variables. -/
def headExponent (α : Fin (q+1) →₀ ℕ) : Fin q →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => α i.castSucc)

@[simp] theorem headExponent_apply (α : Fin (q+1) →₀ ℕ) (i : Fin q) : headExponent q α i=α i.castSucc := rfl

@[simp] theorem headExponent_prefix (α : Fin q →₀ ℕ) : headExponent q (prefixExponent q α)=α := by
  ext i
  simp only [headExponent_apply,prefixExponent_castSucc]

theorem prefixExponent_head (α : Fin (q+1) →₀ ℕ) (hα : α (Fin.last q)=0) :
    prefixExponent q (headExponent q α)=α := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [prefixExponent_last] using hα.symm
  · simp only [prefixExponent_castSucc,headExponent_apply]

theorem headExponent_degree (α : Fin (q+1) →₀ ℕ) (hα : α (Fin.last q)=0) :
    (headExponent q α).degree=α.degree := by
  have he := congrArg Finsupp.degree (prefixExponent_head q α hα)
  simpa only [prefixExponent_degree] using he

def degreeRestrictionEquiv (d : ℕ) (I : Ideal (MvPolynomial (Fin (q+1)) k)) :
    {α : PolynomialDegreeIndex q d // MvPolynomial.monomial α.val (1:k)∈prefixVariableIdeal k q I} ≃
      {α : PolynomialDegreeIndex (q+1) d // MvPolynomial.monomial α.val (1:k)∈I ∧ α.val (Fin.last q)=0} where
  toFun α := ⟨⟨prefixExponent q α.val.val,(prefixExponent_degree q α.val.val).trans α.val.property⟩,
    (prefixVariableIdeal_monomial k q I α.val.val).mp α.property,prefixExponent_last q α.val.val⟩
  invFun α := ⟨⟨headExponent q α.val.val,(headExponent_degree q α.val.val α.property.2).trans α.val.property⟩,
    (prefixVariableIdeal_monomial k q I _).mpr (by rw [prefixExponent_head q α.val.val α.property.2]; exact α.property.1)⟩
  left_inv α := Subtype.ext (Subtype.ext (headExponent_prefix q α.val.val))
  right_inv α := Subtype.ext (Subtype.ext (prefixExponent_head q α.val.val α.property.2))
end NSP14.Lex

namespace NSP14.Lex

theorem maxVariable_le_variables (q : ℕ) (α : Fin q →₀ ℕ) : maxVariable q α≤q := by
  apply Finset.sup_le
  intro i _
  exact Nat.succ_le_of_lt i.isLt

theorem prefixExponent_maxVariable (q : ℕ) (α : Fin q →₀ ℕ) :
    maxVariable (q+1) (prefixExponent q α)=maxVariable q α := by
  simp only [maxVariable,prefixExponent,Finsupp.support_embDomain,Finset.sup_map]
  rfl

theorem maxVariable_last_zero (q : ℕ) (α : Fin (q+1) →₀ ℕ) (r : ℕ)
    (hr : r≤q) (hmax : maxVariable (q+1) α≤r) : α (Fin.last q)=0 := by
  by_contra hn
  have hm := Finset.le_sup (f:=fun i : Fin (q+1) => i.val+1) (Finsupp.mem_support_iff.mpr hn)
  change q+1≤maxVariable (q+1) α at hm
  omega

theorem headExponent_maxVariable (q : ℕ) (α : Fin (q+1) →₀ ℕ) (hα : α (Fin.last q)=0) :
    maxVariable q (headExponent q α)=maxVariable (q+1) α := by
  have he := congrArg (maxVariable (q+1)) (prefixExponent_head q α hα)
  simpa only [prefixExponent_maxVariable] using he

variable (k : Type) [Field k] (q : ℕ)

def idealDegreeCard (I : Ideal (MvPolynomial (Fin q) k)) (d : ℕ) : ℕ :=
  Fintype.card {α : PolynomialDegreeIndex q d // MvPolynomial.monomial α.val (1:k)∈I}

def cumulativeDegreeCard (I : Ideal (MvPolynomial (Fin q) k)) (d r : ℕ) : ℕ :=
  Fintype.card {α : PolynomialDegreeIndex q d // MvPolynomial.monomial α.val (1:k)∈I ∧ maxVariable q α.val≤r}

theorem cumulativeDegreeCard_full (I : Ideal (MvPolynomial (Fin q) k)) (d r : ℕ) (hr : q≤r) :
    cumulativeDegreeCard k q I d r=idealDegreeCard k q I d := by
  have hall (α : PolynomialDegreeIndex q d) : maxVariable q α.val≤r :=
    (maxVariable_le_variables q α.val).trans hr
  simp only [cumulativeDegreeCard,hall,and_true,idealDegreeCard]

theorem prefixVariableIdeal_degreeCard (d : ℕ) (I : Ideal (MvPolynomial (Fin (q+1)) k)) :
    idealDegreeCard k q (prefixVariableIdeal k q I) d=
      (Finset.univ.filter (fun α : PolynomialDegreeIndex (q+1) d =>
        MvPolynomial.monomial α.val (1:k)∈I ∧ α.val (Fin.last q)=0)).card := by
  rw [idealDegreeCard,Fintype.card_congr (degreeRestrictionEquiv k q d I),Fintype.card_subtype]

def cumulativeRestrictionEquiv (d r : ℕ) (hr : r≤q) (I : Ideal (MvPolynomial (Fin (q+1)) k)) :
    {α : PolynomialDegreeIndex q d // MvPolynomial.monomial α.val (1:k)∈prefixVariableIdeal k q I ∧ maxVariable q α.val≤r} ≃
      {α : PolynomialDegreeIndex (q+1) d // MvPolynomial.monomial α.val (1:k)∈I ∧ maxVariable (q+1) α.val≤r} where
  toFun α := ⟨⟨prefixExponent q α.val.val,(prefixExponent_degree q α.val.val).trans α.val.property⟩,
    (prefixVariableIdeal_monomial k q I α.val.val).mp α.property.1,
    (prefixExponent_maxVariable q α.val.val).trans_le α.property.2⟩
  invFun α :=
    let hz := maxVariable_last_zero q α.val.val r hr α.property.2
    ⟨⟨headExponent q α.val.val,(headExponent_degree q α.val.val hz).trans α.val.property⟩,
      (prefixVariableIdeal_monomial k q I _).mpr (by rw [prefixExponent_head q α.val.val hz]; exact α.property.1),
      (headExponent_maxVariable q α.val.val hz).trans_le α.property.2⟩
  left_inv α := Subtype.ext (Subtype.ext (headExponent_prefix q α.val.val))
  right_inv α := Subtype.ext (Subtype.ext (prefixExponent_head q α.val.val
    (maxVariable_last_zero q α.val.val r hr α.property.2)))

theorem prefixVariableIdeal_cumulativeCard (d r : ℕ) (hr : r≤q) (I : Ideal (MvPolynomial (Fin (q+1)) k)) :
    cumulativeDegreeCard k q (prefixVariableIdeal k q I) d r=cumulativeDegreeCard k (q+1) I d r :=
  Fintype.card_congr (cumulativeRestrictionEquiv k q d r hr I)
end NSP14.Lex

namespace NSP14.Lex

theorem upper_finset_subset_of_card_le {A B : Type*} [LinearOrder B]
    (f : A → B) (s t : Finset A)
    (hs : ∀ a∈s,∀ b,f a≤f b → b∈s) (ht : ∀ a∈t,∀ b,f a≤f b → b∈t)
    (hc : s.card≤t.card) : s⊆t := by
  by_contra hn
  obtain ⟨a,ha,hat⟩ := Finset.not_subset.mp hn
  have hts : t⊆s := by
    intro b hb
    rcases le_total (f a) (f b) with hab|hba
    · exact hs a ha b hab
    · exact False.elim (hat (ht b hb a hba))
  have he := Finset.eq_of_subset_of_card_le hts hc
  apply hat
  simpa only [he] using ha

variable (k : Type) [Field k]

theorem IsLex.degree_mem_of_card_le (q d : ℕ) (I L : Ideal (MvPolynomial (Fin q) k))
    (hI : IsLex k q I) (hL : IsLex k q L) (hc : idealDegreeCard k q L d≤ idealDegreeCard k q I d)
    (α : PolynomialDegreeIndex q d) (hα : MvPolynomial.monomial α.val (1:k)∈L) :
    MvPolynomial.monomial α.val (1:k)∈I := by
  let S := Finset.univ.filter (fun α : PolynomialDegreeIndex q d => MvPolynomial.monomial α.val (1:k)∈L)
  let T := Finset.univ.filter (fun α : PolynomialDegreeIndex q d => MvPolynomial.monomial α.val (1:k)∈I)
  have hcard : S.card≤T.card := by simpa only [idealDegreeCard,Fintype.card_subtype] using hc
  have hsub : S⊆T := upper_finset_subset_of_card_le (fun α => MonomialOrder.lex.toSyn α.val) S T
    (by
      intro a ha b hab
      simp only [S,Finset.mem_filter,Finset.mem_univ,true_and] at ha ⊢
      exact hL.2 a.val b.val (a.property.trans b.property.symm) hab ha)
    (by
      intro a ha b hab
      simp only [T,Finset.mem_filter,Finset.mem_univ,true_and] at ha ⊢
      exact hI.2 a.val b.val (a.property.trans b.property.symm) hab ha) hcard
  have hh := hsub (show α∈S by simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and] using hα)
  simpa only [T,Finset.mem_filter,Finset.mem_univ,true_and] using hh

theorem IsLex.cumulative_le_of_card_le (q d r : ℕ) (I L : Ideal (MvPolynomial (Fin q) k))
    (hI : IsLex k q I) (hL : IsLex k q L) (hc : idealDegreeCard k q L d≤ idealDegreeCard k q I d) :
    cumulativeDegreeCard k q L d r≤cumulativeDegreeCard k q I d r := by
  apply Fintype.card_le_of_injective
    (fun α : {α : PolynomialDegreeIndex q d // MvPolynomial.monomial α.val (1:k)∈L ∧ maxVariable q α.val≤r} =>
      (⟨α.val,hI.degree_mem_of_card_le k q d I L hL hc α.val α.property.1,α.property.2⟩ :
        {α : PolynomialDegreeIndex q d // MvPolynomial.monomial α.val (1:k)∈I ∧ maxVariable q α.val≤r}))
  intro a b he
  apply Subtype.ext
  exact congrArg (fun z : {α : PolynomialDegreeIndex q d //
    MvPolynomial.monomial α.val (1:k)∈I ∧ maxVariable q α.val≤r} => z.val) he

theorem IsStronglyStable.cumulative_le_lex : ∀ q : ℕ,∀ (I L : Ideal (MvPolynomial (Fin q) k)),
    IsStronglyStable k q I → IsLex k q L → ∀ d : ℕ,
      idealDegreeCard k q L d≤ idealDegreeCard k q I d → ∀ r : ℕ,
        cumulativeDegreeCard k q L d r≤cumulativeDegreeCard k q I d r := by
  intro q
  induction q using Nat.strong_induction_on with
  | ind q ih =>
    intro I L hI hL d hcard r
    by_cases hr : q≤r
    · rw [cumulativeDegreeCard_full k q L d r hr,cumulativeDegreeCard_full k q I d r hr]
      exact hcard
    by_cases hq : q≤2
    · exact (hI.isLex_of_le_two k q hq I).cumulative_le_of_card_le k q d r I L hL hcard
    cases q with
    | zero => omega
    | succ n =>
      cases n with
      | zero => omega
      | succ m =>
        have hrestrict : idealDegreeCard k (m+1) (prefixVariableIdeal k (m+1) L) d≤
            idealDegreeCard k (m+1) (prefixVariableIdeal k (m+1) I) d := by
          rw [prefixVariableIdeal_degreeCard,prefixVariableIdeal_degreeCard]
          exact hI.last_zero_count_le k m d I L hL hcard
        have hrec := ih (m+1) (by omega) (prefixVariableIdeal k (m+1) I) (prefixVariableIdeal k (m+1) L)
          (prefixVariableIdeal_isStronglyStable k (m+1) I hI) (prefixVariableIdeal_isLex k (m+1) L hL) d hrestrict r
        rw [prefixVariableIdeal_cumulativeCard k (m+1) d r (by omega) L,
          prefixVariableIdeal_cumulativeCard k (m+1) d r (by omega) I] at hrec
        exact hrec
end NSP14.Lex

