module
public import NSP14.Additive.ZeroSumSequence
public import Mathlib.Data.Multiset.Powerset
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.BigOperators.Fin
@[expose] public section
open scoped BigOperators
namespace NSP14.Additive
variable {G : Type*} [AddCommGroup G] {ℓ : ℕ}
def occurrenceMultiset (seq : Fin ℓ → G) : Multiset G := Finset.univ.val.map seq
def MultisetZeroSumFree (s : Multiset G) : Prop :=
  ∀ t : Multiset G, t ≤ s → t ≠ 0 → t.sum ≠ 0

theorem zeroSumFree_multiset_iff (seq : Fin ℓ → G) :
    ZeroSumFree seq ↔ MultisetZeroSumFree (occurrenceMultiset seq) := by
  constructor
  · intro hz t ht ht0
    have hm : t ∈ Multiset.powersetCard t.card (Finset.univ.val.map seq) :=
      Multiset.mem_powersetCard.mpr ⟨ht,rfl⟩
    rw [Multiset.powersetCard_map] at hm
    obtain ⟨J,hJ,hmap⟩ := Multiset.mem_map.mp hm
    have hle := (Multiset.mem_powersetCard.mp hJ).1
    have hn : J.Nodup := (Multiset.nodup_of_le hle) Finset.univ.nodup
    have hval : J.toFinset.val=J := (Multiset.toFinset_val J).trans hn.dedup
    have hJ0 : J ≠ 0 := by intro he; rw [he,Multiset.map_zero] at hmap; exact ht0 hmap.symm
    have hne : J.toFinset.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro he
      have hv := congrArg Finset.val he
      rw [hval] at hv
      exact hJ0 hv
    have hh := hz J.toFinset hne
    have he : ∑ i ∈ J.toFinset, seq i = t.sum := by
      rw [←Finset.sum_map_val,hval,hmap]
    rwa [he] at hh
  · intro hz I hI
    have hle : I.val.map seq ≤ occurrenceMultiset seq :=
      Multiset.map_le_map (Finset.val_le_iff.mpr (Finset.subset_univ I))
    have hn : I.val.map seq ≠ 0 := by
      intro he
      have hc := congrArg Multiset.card he
      have hp := hI.card_pos
      simp only [Multiset.card_map,Multiset.card_zero] at hc
      exact Nat.ne_of_gt hp hc
    simpa only [Finset.sum_map_val] using hz _ hle hn

def ListZeroSumFree (l : List G) : Prop := MultisetZeroSumFree (l : Multiset G)
theorem zeroSumFree_ofFn_iff (seq : Fin ℓ → G) :
    ListZeroSumFree (List.ofFn seq) ↔ ZeroSumFree seq := by
  unfold ListZeroSumFree
  rw [←Fin.univ_val_map seq]
  exact (zeroSumFree_multiset_iff seq).symm
theorem listZeroSumFree_perm {l l' : List G} (hp : l.Perm l') :
    ListZeroSumFree l ↔ ListZeroSumFree l' := by
  unfold ListZeroSumFree
  rw [Multiset.coe_eq_coe.mpr hp]
theorem listZeroSumFree_get (l : List G) (hz : ListZeroSumFree l) :
    ZeroSumFree l.get := by
  apply (zeroSumFree_ofFn_iff l.get).mp
  simpa only [List.ofFn_get] using hz
end NSP14.Additive
