module
public import NSP14.Lex.FiniteHilbertProfiles
@[expose] public section
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Lex

theorem finset_eq_of_prefix_card {α : Type*} [LinearOrder α] (s t : Finset α)
    (h : ∀ a,(s.filter (a≤·)).card=(t.filter (a≤·)).card) : s=t := by
  by_contra hne
  let D := (s\t)∪(t\s)
  have hD : D.Nonempty := by
    by_contra he
    apply hne
    ext a
    have hn : a∉D := fun ha => he ⟨a,ha⟩
    simp only [D,Finset.mem_union,Finset.mem_sdiff,not_or,not_and,not_not] at hn
    exact ⟨hn.1,hn.2⟩
  let a := D.max' hD
  have ha : a∈D := Finset.max'_mem D hD
  have hgt (b : α) (hb : a<b) : b∈s ↔ b∈t := by
    have hn : b∉D := fun hd => (not_lt_of_ge (Finset.le_max' D b hd)) hb
    simp only [D,Finset.mem_union,Finset.mem_sdiff,not_or,not_and,not_not] at hn
    exact ⟨hn.1,hn.2⟩
  have hlt : s.filter (a<·)=t.filter (a<·) := by
    ext b
    simp only [Finset.mem_filter]
    by_cases hab : a<b
    · exact and_congr_left (fun _ => hgt b hab)
    · simp only [hab,and_false]
  have hcard (u : Finset α) : (u.filter (a≤·)).card=(u.filter (a<·)).card+if a∈u then 1 else 0 := by
    by_cases hau : a∈u
    · have hu : u.filter (a≤·)=insert a (u.filter (a<·)) := by
        ext b
        simp only [Finset.mem_filter,Finset.mem_insert]
        constructor
        · rintro ⟨hb,hab⟩
          rcases eq_or_lt_of_le hab with rfl|hab
          · exact Or.inl rfl
          · exact Or.inr ⟨hb,hab⟩
        · rintro (rfl|⟨hb,hab⟩)
          · exact ⟨hau,le_rfl⟩
          · exact ⟨hb,hab.le⟩
      rw [hu,Finset.card_insert_of_notMem (by simp),ite_eq_left hau]
    · have hu : u.filter (a≤·)=u.filter (a<·) := by
        ext b
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hb,hab⟩
          exact ⟨hb,lt_of_le_of_ne hab (fun he => hau (he.symm ▸ hb))⟩
        · rintro ⟨hb,hab⟩
          exact ⟨hb,hab.le⟩
      rw [hu,ite_eq_right hau,add_zero]
  have hh := h a
  rw [hcard s,hcard t,hlt] at hh
  simp only [D,Finset.mem_union,Finset.mem_sdiff] at ha
  rcases ha with ⟨has,hat⟩|⟨hat,has⟩ <;> simp only [has,hat,ite_true,ite_false] at hh <;> omega
end NSP14.Lex

namespace NSP14.Lex

def profilePrefixCard (q : ℕ) (p : MonomialProfile q) (n : ℕ)
    (v : PolynomialDegreeIndex q n) : ℕ :=
  (Finset.univ.filter (fun a : PolynomialDegreeIndex q n =>
    MonomialOrder.degLex.toSyn v.val≤MonomialOrder.degLex.toSyn a.val ∧ p a.val=true)).card

def ProfileDominates (q : ℕ) (p r : MonomialProfile q) : Prop :=
  ∀ n v,profilePrefixCard q p n v≤profilePrefixCard q r n v

theorem profileDominates_refl (q : ℕ) (p : MonomialProfile q) : ProfileDominates q p p :=
  fun _ _ => le_rfl

theorem profileDominates_trans (q : ℕ) {p r s : MonomialProfile q}
    (hpr : ProfileDominates q p r) (hrs : ProfileDominates q r s) : ProfileDominates q p s :=
  fun n v => (hpr n v).trans (hrs n v)

theorem profileDominates_antisymm (q : ℕ) {p r : MonomialProfile q}
    (hpr : ProfileDominates q p r) (hrp : ProfileDominates q r p) : p=r := by
  have he (n : ℕ) :
      Finset.univ.filter (fun a : PolynomialDegreeIndex q n => p a.val=true)=
      Finset.univ.filter (fun a : PolynomialDegreeIndex q n => r a.val=true) := by
    let key (a : PolynomialDegreeIndex q n) := MonomialOrder.degLex.toSyn a.val
    have hk : Function.Injective key := by
      intro a b hab
      exact Subtype.ext (MonomialOrder.degLex.toSyn.injective hab)
    let : LinearOrder (PolynomialDegreeIndex q n) := LinearOrder.lift' key hk
    apply finset_eq_of_prefix_card
    intro a
    have hh := le_antisymm (hpr n a) (hrp n a)
    change ((Finset.univ.filter (fun x : PolynomialDegreeIndex q n => p x.val=true)).filter
      (fun x => key a≤key x)).card=((Finset.univ.filter (fun x : PolynomialDegreeIndex q n => r x.val=true)).filter
      (fun x => key a≤key x)).card
    simpa only [profilePrefixCard,Finset.filter_filter,and_comm] using hh
  funext a
  have hh := congrArg (fun s => (⟨a,rfl⟩ : PolynomialDegreeIndex q a.degree)∈s) (he a.degree)
  have ht : p a=true ↔ r a=true := by
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using Iff.of_eq hh
  cases hp : p a <;> cases hr : r a <;> simp_all

@[instance_reducible] def profileDominanceOrder (q : ℕ) : PartialOrder (MonomialProfile q) where
  le := ProfileDominates q
  lt p r := ProfileDominates q p r ∧ ¬ProfileDominates q r p
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_refl := profileDominates_refl q
  le_trans _ _ _ := profileDominates_trans q
  le_antisymm _ _ := profileDominates_antisymm q
end NSP14.Lex
