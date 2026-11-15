module
public import NSP14.Lex.GenericDistraction
public import NSP14.Lex.Stable
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Sym.Card
public import Mathlib.Data.Finset.Sort
public import Mathlib.Combinatorics.SetFamily.KruskalKatona
@[expose] public section
open scoped Classical BigOperators FinsetFamily
open Finset
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Lex

def degreeIndexSymEquiv (q d : ℕ) : PolynomialDegreeIndex q d ≃ Sym (Fin q) d :=
  (Sym.equivNatSum (Fin q) d).symm

theorem degreeIndex_card_choose (q d : ℕ) :
    Fintype.card (PolynomialDegreeIndex (q+1) d)=(d+q).choose q := by
  rw [Fintype.card_congr (degreeIndexSymEquiv (q+1) d),Sym.card_sym_eq_choose,Fintype.card_fin]
  have he : q+1+d-1=d+q := by omega
  rw [he]
  simpa only [Nat.add_sub_cancel_left] using (Nat.choose_symm (Nat.le_add_right d q)).symm
end NSP14.Lex

namespace NSP14.Lex

def reversedCoefficient (q : ℕ) (α : Fin (q+1) →₀ ℕ) (j : ℕ) : ℕ :=
  if h : j<q+1 then α (Fin.rev ⟨j,h⟩) else 0

def reversedPrefix (q : ℕ) (α : Fin (q+1) →₀ ℕ) (t : ℕ) : ℕ :=
  ∑ j∈Finset.range t,reversedCoefficient q α j

theorem reversedPrefix_succ (q : ℕ) (α : Fin (q+1) →₀ ℕ) (t : ℕ) :
    reversedPrefix q α (t+1)=reversedPrefix q α t+reversedCoefficient q α t :=
  Finset.sum_range_succ _ _

theorem reversedPrefix_monotone (q : ℕ) (α : Fin (q+1) →₀ ℕ) : Monotone (reversedPrefix q α) := by
  intro a b hab
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hab)

theorem reversedPrefix_total (q : ℕ) (α : Fin (q+1) →₀ ℕ) :
    reversedPrefix q α (q+1)=α.degree := by
  calc
    reversedPrefix q α (q+1)=∑ i : Fin (q+1),reversedCoefficient q α i.val :=
      (Fin.sum_univ_eq_sum_range (reversedCoefficient q α) (q+1)).symm
    _=∑ i : Fin (q+1),α (Fin.rev i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [reversedCoefficient,dite_eq_left i.isLt]
    _=∑ i : Fin (q+1),α i := Equiv.sum_comp Fin.revPerm _
    _=α.degree := (Finsupp.degree_eq_sum α).symm

def degreeSeparatorEmbedding (q d : ℕ) (α : PolynomialDegreeIndex (q+1) d) : Fin q ↪o Fin (d+q) :=
  OrderEmbedding.ofStrictMono
    (fun i => ⟨i.val+reversedPrefix q α.val (i.val+1),by
      have hh := reversedPrefix_monotone q α.val (show i.val+1≤q+1 by omega)
      rw [reversedPrefix_total,α.property] at hh
      omega⟩)
    (by
      intro i j hij
      change i.val+reversedPrefix q α.val (i.val+1)<j.val+reversedPrefix q α.val (j.val+1)
      have hh := reversedPrefix_monotone q α.val (show i.val+1≤j.val+1 by omega)
      omega)

def degreeSeparator (q d : ℕ) (α : PolynomialDegreeIndex (q+1) d) : Finset (Fin (d+q)) :=
  Finset.univ.image (degreeSeparatorEmbedding q d α)

theorem degreeSeparator_card (q d : ℕ) (α : PolynomialDegreeIndex (q+1) d) :
    (degreeSeparator q d α).card=q := by
  rw [degreeSeparator,Finset.card_image_of_injective _ (degreeSeparatorEmbedding q d α).injective,
    Finset.card_univ,Fintype.card_fin]

theorem degreeSeparator_injective (q d : ℕ) : Function.Injective (degreeSeparator q d) := by
  intro α β he
  have hα := Finset.orderEmbOfFin_unique (degreeSeparator_card q d α)
    (fun i => Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    (degreeSeparatorEmbedding q d α).strictMono
  have hβ : (degreeSeparatorEmbedding q d β : Fin q → Fin (d+q))=
      (degreeSeparator q d α).orderEmbOfFin (degreeSeparator_card q d α) :=
    Finset.orderEmbOfFin_unique (degreeSeparator_card q d α)
      (fun i => by rw [he]; exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
      (degreeSeparatorEmbedding q d β).strictMono
  have hEmb := hα.trans hβ.symm
  have hp (t : ℕ) (ht : t≤q+1) : reversedPrefix q α.val t=reversedPrefix q β.val t := by
    cases t with
    | zero => rfl
    | succ t =>
      by_cases hqt : t<q
      · have hh := congrArg Fin.val (congrFun hEmb ⟨t,hqt⟩)
        change t+reversedPrefix q α.val (t+1)=t+reversedPrefix q β.val (t+1) at hh
        omega
      · have hteq : t=q := by omega
        rw [hteq,reversedPrefix_total,reversedPrefix_total,α.property,β.property]
  have hc (j : ℕ) (hj : j<q+1) : reversedCoefficient q α.val j=reversedCoefficient q β.val j := by
    have h1 := hp (j+1) (by omega)
    have h0 := hp j (by omega)
    rw [reversedPrefix_succ,reversedPrefix_succ,h0] at h1
    omega
  apply Subtype.ext
  ext i
  have hh := hc (Fin.rev i).val (Fin.rev i).isLt
  simp only [reversedCoefficient,dite_eq_left (Fin.rev i).isLt] at hh
  change α.val (Fin.rev (Fin.rev i))=β.val (Fin.rev (Fin.rev i)) at hh
  simpa only [Fin.rev_rev] using hh
end NSP14.Lex

namespace NSP14.Lex

def degreeSeparatorMap (q d : ℕ) (α : PolynomialDegreeIndex (q+1) d) :
    {B : Finset (Fin (d+q)) // B.card=q} := ⟨degreeSeparator q d α,degreeSeparator_card q d α⟩

theorem degreeSeparatorMap_bijective (q d : ℕ) : Function.Bijective (degreeSeparatorMap q d) := by
  have hinj : Function.Injective (degreeSeparatorMap q d) := by
    intro α β he
    exact degreeSeparator_injective q d (congrArg Subtype.val he)
  have hcard : Fintype.card (PolynomialDegreeIndex (q+1) d)=
      Fintype.card {B : Finset (Fin (d+q)) // B.card=q} := by
    rw [degreeIndex_card_choose]
    symm
    calc
      Fintype.card {B : Finset (Fin (d+q)) // B.card=q}=
          ((Finset.univ : Finset (Fin (d+q))).powersetCard q).card :=
        Fintype.card_of_subtype _ (by intro B; simp)
      _=(d+q).choose q := by rw [Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin]
  refine ⟨hinj,?_⟩
  intro B
  by_contra hn
  have hc := Fintype.card_lt_of_injective_of_notMem (degreeSeparatorMap q d) hinj hn
  omega

/-- The actual reversed stars-and-bars map, not a cardinality-chosen bijection. -/
def degreeSeparatorEquiv (q d : ℕ) :
    PolynomialDegreeIndex (q+1) d ≃ {B : Finset (Fin (d+q)) // B.card=q} :=
  Equiv.ofBijective (degreeSeparatorMap q d) (degreeSeparatorMap_bijective q d)
end NSP14.Lex

namespace NSP14.Lex

theorem degreeSeparator_zero_mem (q d : ℕ) (α : PolynomialDegreeIndex (q+2) d) :
    (0 : Fin (d+(q+1)))∈degreeSeparator (q+1) d α ↔ α.val (Fin.last (q+1))=0 := by
  constructor
  · intro hz
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hz
    have he := congrArg Fin.val hi
    change i.val+reversedPrefix (q+1) α.val (i.val+1)=0 at he
    have hi0 : i=0 := Fin.ext (by change i.val=0; omega)
    subst i
    change 0+reversedPrefix (q+1) α.val 1=0 at he
    simpa [reversedPrefix,reversedCoefficient] using he
  · intro hα
    apply Finset.mem_image.mpr
    refine ⟨0,Finset.mem_univ _,?_⟩
    apply Fin.ext
    change 0+reversedPrefix (q+1) α.val 1=0
    simpa [reversedPrefix,reversedCoefficient] using hα

/-- Colex compares increasing tuples at their last different coordinate. -/
theorem colex_image_lt_of_last_difference {r : ℕ} {A : Type*} [LinearOrder A]
    (e f : Fin r ↪o A) (j : Fin r) (hj : e j<f j)
    (heq : ∀ i, j < i → e i=f i) :
    toColex (Finset.univ.image e)<toColex (Finset.univ.image f) := by
  apply Finset.Colex.lt_iff_exists_forall_lt.mpr
  refine ⟨f j,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩,?_,?_⟩
  · intro hmem
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hmem
    by_cases hij : i≤j
    · exact not_lt_of_ge (e.monotone hij) (hj.trans_eq hi.symm)
    · have hji : j < i := lt_of_not_ge hij
      rw [heq i hji] at hi
      exact (ne_of_lt (f.strictMono hji)) hi.symm
  · intro b hb hbf
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hb
    have hij : i≤j := by
      by_contra hn
      have hji : j < i := lt_of_not_ge hn
      apply hbf
      rw [heq i hji]
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    exact (e.monotone hij).trans_lt hj
end NSP14.Lex

namespace NSP14.Lex

theorem reversedPrefix_eq_of_tail (q : ℕ) (α β : Fin (q+1) →₀ ℕ)
    (hdeg : α.degree=β.degree) (t : ℕ) (ht : t≤q+1)
    (htail : ∀ j,t≤j → j<q+1 → reversedCoefficient q α j=reversedCoefficient q β j) :
    reversedPrefix q α t=reversedPrefix q β t := by
  have ha := Finset.sum_range_add_sum_Ico (reversedCoefficient q α) ht
  have hb := Finset.sum_range_add_sum_Ico (reversedCoefficient q β) ht
  change reversedPrefix q α t+∑ j∈Finset.Ico t (q+1),reversedCoefficient q α j=
    reversedPrefix q α (q+1) at ha
  change reversedPrefix q β t+∑ j∈Finset.Ico t (q+1),reversedCoefficient q β j=
    reversedPrefix q β (q+1) at hb
  have hs : (∑ j∈Finset.Ico t (q+1),reversedCoefficient q α j)=
      ∑ j∈Finset.Ico t (q+1),reversedCoefficient q β j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact htail j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2
  rw [reversedPrefix_total,hdeg,hs] at ha
  rw [reversedPrefix_total] at hb
  omega
end NSP14.Lex

namespace NSP14.Lex

theorem degreeSeparator_lex_lt (q d : ℕ) (α β : PolynomialDegreeIndex (q+1) d)
    (hlex : MonomialOrder.lex.toSyn β.val<MonomialOrder.lex.toSyn α.val) :
    toColex (degreeSeparator q d α)<toColex (degreeSeparator q d β) := by
  change Finsupp.Lex (· < ·) (· < ·) β.val α.val at hlex
  obtain ⟨i,hbefore,hdiff⟩ := hlex
  have hdeg : α.val.degree=β.val.degree := α.property.trans β.property.symm
  have hiq : i.val<q := by
    by_contra hn
    have hi : i=Fin.last q := Fin.ext (by change i.val=q; omega)
    subst i
    have hs : (∑ j : Fin q,α.val j.castSucc)=∑ j : Fin q,β.val j.castSucc := by
      apply Finset.sum_congr rfl
      intro j _
      exact (hbefore j.castSucc (by change j.val<q; exact j.isLt)).symm
    rw [Finsupp.degree_eq_sum,Finsupp.degree_eq_sum,Fin.sum_univ_castSucc,Fin.sum_univ_castSucc,hs] at hdeg
    omega
  let s := q-i.val
  have hspos : 0<s := by dsimp only [s]; omega
  have hslen : s<q+1 := by dsimp only [s]; omega
  have hri (γ : Fin (q+1) →₀ ℕ) : reversedCoefficient q γ s=γ i := by
    rw [reversedCoefficient,dite_eq_left hslen]
    congr 1
    apply Fin.ext
    simp only [Fin.val_rev]
    dsimp only [s]
    omega
  have hp (t : ℕ) (hst : s+1≤t) (ht : t≤q+1) :
      reversedPrefix q α.val t=reversedPrefix q β.val t := by
    apply reversedPrefix_eq_of_tail q α.val β.val hdeg t ht
    intro j htj hj
    have hji : Fin.rev (⟨j,hj⟩ : Fin (q+1)) < i := by
      change q+1-(j+1) < i.val
      dsimp only [s] at hst
      omega
    simp only [reversedCoefficient,dite_eq_left hj]
    exact (hbefore _ hji).symm
  have hpstrict : reversedPrefix q α.val s<reversedPrefix q β.val s := by
    have he := hp (s+1) le_rfl (by omega)
    rw [reversedPrefix_succ,reversedPrefix_succ,hri α.val,hri β.val] at he
    omega
  let j : Fin q := ⟨s-1,by dsimp only [s]; omega⟩
  have hjs : j.val+1=s := by dsimp only [j]; omega
  change toColex (Finset.univ.image (degreeSeparatorEmbedding q d α))<
    toColex (Finset.univ.image (degreeSeparatorEmbedding q d β))
  apply colex_image_lt_of_last_difference _ _ j
  · change j.val+reversedPrefix q α.val (j.val+1)<j.val+reversedPrefix q β.val (j.val+1)
    rw [hjs]
    omega
  · intro k hjk
    apply Fin.ext
    change k.val+reversedPrefix q α.val (k.val+1)=k.val+reversedPrefix q β.val (k.val+1)
    rw [hp (k.val+1) (by change j.val<k.val at hjk; omega) (by omega)]
end NSP14.Lex

namespace NSP14.Lex

theorem degreeSeparator_colex_lt_iff (q d : ℕ) (α β : PolynomialDegreeIndex (q+1) d) :
    toColex (degreeSeparator q d α)<toColex (degreeSeparator q d β) ↔
      MonomialOrder.lex.toSyn β.val<MonomialOrder.lex.toSyn α.val := by
  constructor
  · intro hsep
    rcases lt_trichotomy (MonomialOrder.lex.toSyn β.val) (MonomialOrder.lex.toSyn α.val) with h|h|h
    · exact h
    · have he : β=α := Subtype.ext (MonomialOrder.lex.toSyn.injective h)
      subst β
      exact False.elim (lt_irrefl _ hsep)
    · exact False.elim (not_lt_of_ge hsep.le (degreeSeparator_lex_lt q d β α h))
  · exact degreeSeparator_lex_lt q d α β

theorem degreeSeparator_colex_le_iff (q d : ℕ) (α β : PolynomialDegreeIndex (q+1) d) :
    toColex (degreeSeparator q d α)≤toColex (degreeSeparator q d β) ↔
      MonomialOrder.lex.toSyn β.val≤MonomialOrder.lex.toSyn α.val := by
  simp only [← not_lt,degreeSeparator_colex_lt_iff]
end NSP14.Lex
