module

public import NSP14.Semigroup.PolynomialAction
public import NSP14.Semigroup.AperyStandard
public import NSP14.Ordinary.NumericalClosure
public import Mathlib.Data.Sym.Card
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

open scoped Classical BigOperators

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup)

/-- Actual numerical weight of a quadratic monomial, including squares. -/
def quadraticWeight : Sym2 S.NonXAtom → ℕ :=
  Sym2.lift ⟨fun a b => a.val.val + b.val.val, fun a b => Nat.add_comm a.val.val b.val.val⟩

@[simp] theorem quadraticWeight_pair (a b : S.NonXAtom) :
    S.quadraticWeight s(a, b) = a.val.val + b.val.val := rfl

theorem degree_two_pair_exists (x : ↥(S.degreeSet 2)) :
    ∃ p : Sym2 S.NonXAtom, S.quadraticWeight p = x.val := by
  obtain ⟨hx, ho⟩ := Finset.mem_filter.mp x.property
  let z : S.carrier := ⟨x.val, ((S.mem_aperySet_iff _).1 hx).1⟩
  have hp : 0 < z.val := by
    change 0 < x.val
    by_contra hn
    have hx0 : x.val = 0 := by omega
    rw [hx0, S.order_zero] at ho
    omega
  obtain ⟨a, v, ha, hm, hv, he, hl⟩ := S.apery_atomic_split z hx hp
  have hav := S.atom_order ha
  have hov : S.order v.val = 1 := by
    have hval := congrArg Subtype.val he
    change x.val = a.val + v.val at hval
    rw [← hval, ho, hav] at hl
    omega
  have hva := (S.order_one_iff_atom v.property).1 hov
  have hvm : v.val ≠ S.multiplicity := fun h => S.multiplicity_not_apery (h ▸ hv)
  exact ⟨s(⟨a, ha, hm⟩, ⟨v, hva, hvm⟩), (congrArg Subtype.val he).symm⟩

noncomputable def degreeTwoPair (x : ↥(S.degreeSet 2)) : Sym2 S.NonXAtom :=
  (S.degree_two_pair_exists x).choose

theorem degreeTwoPair_weight (x : ↥(S.degreeSet 2)) :
    S.quadraticWeight (S.degreeTwoPair x) = x.val := (S.degree_two_pair_exists x).choose_spec

theorem degreeTwoPair_injective : Function.Injective S.degreeTwoPair := by
  intro x y h
  apply Subtype.ext
  have he := congrArg S.quadraticWeight h
  simpa only [S.degreeTwoPair_weight] using he

theorem quadratic_pair_card : Fintype.card (Sym2 S.NonXAtom) = S.embeddingDimension.choose 2 := by
  rw [Sym2.card, S.nonXAtom_card]
  have he := S.embeddingDimension_pos
  congr 1
  omega

theorem degree_two_card_le_quadratic :
    (S.degreeSet 2).card ≤ S.embeddingDimension.choose 2 := by
  have hc := Fintype.card_le_of_injective _ S.degreeTwoPair_injective
  rwa [Fintype.card_coe, S.quadratic_pair_card] at hc

/-- Maximal Q₂ forces every actual quadratic monomial to be a distinct live
Apéry basis vector. This is a counting argument, valid in characteristic two. -/
theorem degreeTwoPair_bijective
    (ha : (S.degreeSet 2).card = S.embeddingDimension.choose 2) :
    Function.Bijective S.degreeTwoPair := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  exact ⟨S.degreeTwoPair_injective, by rw [Fintype.card_coe, ha, S.quadratic_pair_card]⟩

theorem maximal_quadratic_weight_mem
    (ha : (S.degreeSet 2).card = S.embeddingDimension.choose 2) (p : Sym2 S.NonXAtom) :
    S.quadraticWeight p ∈ S.degreeSet 2 := by
  obtain ⟨x, hx⟩ := (S.degreeTwoPair_bijective ha).2 p
  rw [← hx, S.degreeTwoPair_weight]
  exact x.property

theorem maximal_quadratic_weight_injective
    (ha : (S.degreeSet 2).card = S.embeddingDimension.choose 2) :
    Function.Injective S.quadraticWeight := by
  intro p q hpq
  obtain ⟨x, rfl⟩ := (S.degreeTwoPair_bijective ha).2 p
  obtain ⟨y, rfl⟩ := (S.degreeTwoPair_bijective ha).2 q
  have hxy : x = y := Subtype.ext (by simpa only [S.degreeTwoPair_weight] using hpq)
  exact congrArg S.degreeTwoPair hxy

theorem maximal_pair_order
    (ha : (S.degreeSet 2).card = S.embeddingDimension.choose 2) (a b : S.NonXAtom) :
    (a.val.val + b.val.val) ∈ S.aperySet ∧ S.order (a.val.val + b.val.val) = 2 :=
  Finset.mem_filter.mp (S.maximal_quadratic_weight_mem ha s(a, b))

theorem lowSet_nonzero_atom {x : ℕ} (hx : x ∈ S.lowSet) (h0 : x ≠ 0) :
    S.IsAtom x ∧ x ≠ S.multiplicity := by
  rcases Finset.mem_insert.mp hx with h | h
  · exact (h0 h).elim
  · exact ⟨(S.mem_atoms_iff _).1 (Finset.mem_erase.mp h).2, (Finset.mem_erase.mp h).1⟩

/-- All sums, including those with the zero element, are Apéry minima. -/
theorem maximal_low_pair_min
    (ha : (S.degreeSet 2).card = S.embeddingDimension.choose 2)
    {x y : ℕ} (hx : x ∈ S.lowSet) (hy : y ∈ S.lowSet) :
    IsAperyMin S.carrier S.multiplicity (x + y) := by
  by_cases hx0 : x = 0
  · subst x; simpa using (S.mem_aperySet_iff _).1 (S.lowSet_subset hy)
  by_cases hy0 : y = 0
  · subst y; simpa using (S.mem_aperySet_iff _).1 (S.lowSet_subset hx)
  obtain ⟨hxa, hxm⟩ := S.lowSet_nonzero_atom hx hx0
  obtain ⟨hya, hym⟩ := S.lowSet_nonzero_atom hy hy0
  exact (S.mem_aperySet_iff _).1 (S.maximal_pair_order ha
    ⟨⟨x, hxa.1⟩, hxa, hxm⟩ ⟨⟨y, hya.1⟩, hya, hym⟩).1

theorem low_sum_ne_atom {x y z : ℕ} (hx : x ∈ S.lowSet) (hy : y ∈ S.lowSet)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hz : S.IsAtom z) : x + y ≠ z := by
  intro he
  have hxm := ((S.mem_aperySet_iff _).1 (S.lowSet_subset hx)).1
  have hym := ((S.mem_aperySet_iff _).1 (S.lowSet_subset hy)).1
  exact (hz.2.2 x hxm y hym he.symm).elim hx0 hy0

/-- Numerical uniqueness also excludes collisions across degrees zero, one and two. -/
theorem maximal_low_pair_unique
    (ha : (S.degreeSet 2).card = S.embeddingDimension.choose 2)
    {a b c d : ℕ} (haL : a ∈ S.lowSet) (hbL : b ∈ S.lowSet)
    (hcL : c ∈ S.lowSet) (hdL : d ∈ S.lowSet) (he : a + b = c + d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  by_cases ha0 : a = 0
  · subst a
    by_cases hc0 : c = 0
    · exact Or.inl ⟨hc0.symm, by omega⟩
    by_cases hd0 : d = 0
    · exact Or.inr ⟨hd0.symm, by omega⟩
    have hb0 : b ≠ 0 := by omega
    exact (S.low_sum_ne_atom hcL hdL hc0 hd0 (S.lowSet_nonzero_atom hbL hb0).1
      (by omega)).elim
  by_cases hb0 : b = 0
  · subst b
    by_cases hc0 : c = 0
    · exact Or.inr ⟨by omega, hc0.symm⟩
    by_cases hd0 : d = 0
    · exact Or.inl ⟨by omega, hd0.symm⟩
    exact (S.low_sum_ne_atom hcL hdL hc0 hd0 (S.lowSet_nonzero_atom haL ha0).1
      (by omega)).elim
  by_cases hc0 : c = 0
  · subst c
    have hd0 : d ≠ 0 := by omega
    exact (S.low_sum_ne_atom haL hbL ha0 hb0 (S.lowSet_nonzero_atom hdL hd0).1
      (by omega)).elim
  by_cases hd0 : d = 0
  · subst d
    exact (S.low_sum_ne_atom haL hbL ha0 hb0 (S.lowSet_nonzero_atom hcL hc0).1
      (by omega)).elim
  let atom (x : ℕ) (hx : x ∈ S.lowSet) (h0 : x ≠ 0) : S.NonXAtom :=
    ⟨⟨x, (S.lowSet_nonzero_atom hx h0).1.1⟩, S.lowSet_nonzero_atom hx h0⟩
  have hp := S.maximal_quadratic_weight_injective ha
    (show S.quadraticWeight s(atom a haL ha0, atom b hbL hb0) =
      S.quadraticWeight s(atom c hcL hc0, atom d hdL hd0) from he)
  rcases Sym2.eq_iff.mp hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨congrArg (fun x : S.NonXAtom => x.val.val) h1,
      congrArg (fun x : S.NonXAtom => x.val.val) h2⟩
  · exact Or.inr ⟨congrArg (fun x : S.NonXAtom => x.val.val) h1,
      congrArg (fun x : S.NonXAtom => x.val.val) h2⟩

/-- The actual zero-plus-atoms list, indexed by Fin e. -/
noncomputable def lowValueEquiv : Fin S.embeddingDimension ≃ ↥S.lowSet :=
  (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, S.lowSet_card])).symm

noncomputable def actualAperyPairData
    (ha : (S.degreeSet 2).card = S.embeddingDimension.choose 2) :
    AperyPairData S.carrier S.multiplicity S.embeddingDimension where
  value i := (S.lowValueEquiv i).val
  injective_value := Subtype.val_injective.comp S.lowValueEquiv.injective
  value_min i := (S.mem_aperySet_iff _).1 (S.lowSet_subset (S.lowValueEquiv i).property)
  pair_min i j := S.maximal_low_pair_min ha (S.lowValueEquiv i).property (S.lowValueEquiv j).property
  pair_unique i j k l h := by
    have he := S.maximal_low_pair_unique ha (S.lowValueEquiv i).property
      (S.lowValueEquiv j).property (S.lowValueEquiv k).property (S.lowValueEquiv l).property h
    have hinj : Function.Injective (fun i => (S.lowValueEquiv i).val) :=
      Subtype.val_injective.comp S.lowValueEquiv.injective
    rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨hinj h1, hinj h2⟩
    · exact Or.inr ⟨hinj h1, hinj h2⟩

variable (k : Type*) [Field k]

noncomputable def maximalQDegreeAperyPairData
    (ha : Module.finrank k (S.qDegree k 2) = S.embeddingDimension.choose 2) :
    AperyPairData S.carrier S.multiplicity S.embeddingDimension :=
  S.actualAperyPairData (by rwa [S.qDegree_finrank] at ha)

theorem maximal_qDegree_multiplicity_bound
    (ha : Module.finrank k (S.qDegree k 2) = S.embeddingDimension.choose 2) :
    S.embeddingDimension * (S.embeddingDimension - 1) + 1 ≤ S.multiplicity := by
  have : NeZero S.multiplicity := ⟨Nat.ne_of_gt S.multiplicity_pos⟩
  exact (S.maximalQDegreeAperyPairData k ha).multiplicity_bound

theorem maximal_qDegree_deficit_bound
    (ha : Module.finrank k (S.qDegree k 2) = S.embeddingDimension.choose 2) :
    (S.embeddingDimension - 1) ^ 2 ≤ S.deficit := by
  have : NeZero S.multiplicity := ⟨Nat.ne_of_gt S.multiplicity_pos⟩
  exact (S.maximalQDegreeAperyPairData k ha).deficit_bound S.deficit
    S.embeddingDimension_pos (by
      have := S.embeddingDimension_le_multiplicity
      unfold deficit
      omega)

end NSP14.NumericalSemigroup
