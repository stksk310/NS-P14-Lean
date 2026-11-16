module
public import NSP14.Additive.EndpointDistance
public import NSP14.Additive.FiniteLayerCake
@[expose] public section
open scoped Pointwise BigOperators Classical
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

theorem unreached_card (n : ℕ) :
    (Finset.univ.filter (fun r : ZMod D.u => n < D.shortestDegree (D.residueIndex r))).card =
      D.u-(NSP14.Additive.iteratedSum D.residueAlphabet n).card := by
  have he : Finset.univ.filter (fun r : ZMod D.u => n < D.shortestDegree (D.residueIndex r)) =
      Finset.univ \ NSP14.Additive.iteratedSum D.residueAlphabet n := by
    ext r
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff,
      D.residue_distance_iff,not_le]
  rw [he,Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,ZMod.card]

/-- The constant 1 and n=0 layer are retained. The cutoff is the actual u. -/
theorem wordVolume_tail : D.wordVolume = 1+∑ n ∈ Finset.range D.u,
    (D.u-(NSP14.Additive.iteratedSum D.residueAlphabet n).card) := by
  unfold wordVolume
  rw [←D.residueIndexEquiv.sum_comp D.shortestDegree]
  change 1+∑ r : ZMod D.u,D.shortestDegree (D.residueIndex r) = _
  rw [NSP14.Additive.finite_layer_cake _ D.u (fun r => (D.shortestDegree_lt (D.residueIndex r)).le)]
  simp only [D.unreached_card]

theorem wordVolume_tail_shift : D.wordVolume = D.u+∑ j ∈ Finset.range D.u,
    (D.u-(NSP14.Additive.iteratedSum D.residueAlphabet (j+1)).card) := by
  let f := fun n => D.u-(NSP14.Additive.iteratedSum D.residueAlphabet n).card
  have h0 : f 0 = D.u-1 := by simp only [f,NSP14.Additive.iteratedSum_zero,Finset.card_singleton]
  have hu : f D.u = 0 := by
    dsimp only [f]
    rw [show NSP14.Additive.iteratedSum D.residueAlphabet D.u = Finset.univ from
      D.residueAlphabet_saturated D.u (Nat.sub_le _ _)]
    simp only [Finset.card_univ,ZMod.card,Nat.sub_self]
  have hs := Finset.sum_range_succ f D.u
  have ht := Finset.sum_range_succ' f D.u
  rw [hu,add_zero] at hs
  rw [h0] at ht
  have he := D.wordVolume_tail
  change D.wordVolume=1+∑ n ∈ Finset.range D.u,f n at he
  change D.wordVolume=D.u+∑ j ∈ Finset.range D.u,f (j+1)
  have hp := D.u_pos
  omega

theorem wordVolume_growth_bound : D.wordVolume ≤ D.u+∑ j ∈ Finset.range D.u,
    (D.u-(D.q+1)-((D.q+2)/2)*j) := by
  rw [D.wordVolume_tail_shift]
  apply Nat.add_le_add_left
  apply Finset.sum_le_sum
  intro j _
  have hg := NSP14.Additive.generated_sum_growth D.residueAlphabet D.zero_mem_residueAlphabet
    D.residueAlphabet_generates (j+1) (by omega)
  rw [ZMod.card,D.residueAlphabet_card,Nat.add_sub_cancel] at hg
  have he : (D.q+1+1)/2 = (D.q+2)/2 := by omega
  rw [he] at hg
  have hm : j*((D.q+2)/2)=((D.q+2)/2)*j := Nat.mul_comm _ _
  rw [hm] at hg
  omega
end NSP14.Endpoint.Data
