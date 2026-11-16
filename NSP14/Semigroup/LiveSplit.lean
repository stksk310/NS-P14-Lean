module

public import NSP14.Semigroup.AperyTopDegree

@[expose] public section

open scoped BigOperators

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup)

/-- Cut a longest atomic expression at any prescribed order; both parts remain live. -/
theorem order_live_split (x : S.carrier) (t : ℕ) (ht : t ≤ S.order x.val) :
    ∃ u v : S.carrier, x = u + v ∧ S.order u.val = t ∧
      S.order v.val = S.order x.val - t := by
  let q := S.order x.val - t
  have he : S.order x.val = t + q := by dsimp [q]; omega
  have hex := S.order_realized_by_atoms x.property
  rw [he] at hex
  obtain ⟨f, hf, hsum⟩ := hex
  let u : S.carrier := ⟨∑ i : Fin t, f (Fin.castAdd q i),
    S.sum_mem Finset.univ _ (fun i _ => (hf (Fin.castAdd q i)).1)⟩
  let v : S.carrier := ⟨∑ i : Fin q, f (Fin.natAdd t i),
    S.sum_mem Finset.univ _ (fun i _ => (hf (Fin.natAdd t i)).1)⟩
  have huv : x = u + v := by
    apply Subtype.ext
    simpa only [u, v, AddSubmonoid.coe_add, Fin.sum_univ_add] using hsum.symm
  have hu : t ≤ S.order u.val := S.atomic_length_le _ (fun i => hf (Fin.castAdd q i)) rfl
  have hv : q ≤ S.order v.val := S.atomic_length_le _ (fun i => hf (Fin.natAdd t i)) rfl
  have ha := S.order_add u.property v.property
  have hval : x.val = u.val + v.val := congrArg Subtype.val huv
  rw [← hval, he] at ha
  exact ⟨u, v, huv, by omega, by dsimp [q] at hv; omega⟩

/-- A longest expression can be peeled into an actual atom and a live remainder. -/
theorem atomic_live_split (x : S.carrier) (hpos : 0 < x.val) :
    ∃ a v : S.carrier, S.IsAtom a.val ∧ x = a + v ∧
      S.order (a.val + v.val) = S.order a.val + S.order v.val := by
  have ht : 1 ≤ S.order x.val := S.order_pos x.property hpos
  obtain ⟨a, v, he, ha, hv⟩ := S.order_live_split x 1 ht
  have hatom := (S.order_one_iff_atom a.property).1 ha
  refine ⟨a, v, hatom, he, ?_⟩
  have hval : x.val = a.val + v.val := congrArg Subtype.val he
  rw [← hval, ha, hv]
  omega

end NSP14.NumericalSemigroup
