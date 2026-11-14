module
public import NSP14.Additive.EndpointVolume
public import NSP14.Endpoint.SocleBounds
public import NSP14.Endpoint.CoreArtinBasis
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical Pointwise BigOperators
namespace NSP14.Additive
/-- Pigeonhole in the actual finite group, with no primality hypothesis. -/
theorem two_sum_eq_univ_of_large {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (A : Finset G) (hA : Fintype.card G < 2*A.card) :
    A+A=Finset.univ := by
  apply Finset.eq_univ_iff_forall.mpr
  intro x
  let B := A.image (fun a => x-a)
  have hB : B.card=A.card := Finset.card_image_of_injective _ (by
    intro a b he
    exact sub_right_injective he)
  have hi : (A∩B).Nonempty := Finset.inter_nonempty_of_card_lt_card_add_card
    (Finset.subset_univ A) (Finset.subset_univ B) (by
      rw [Finset.card_univ,hB]
      omega)
  obtain ⟨y,hy⟩ := hi
  obtain ⟨a,ha,he⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hy).2
  exact Finset.mem_add.mpr ⟨y,(Finset.mem_inter.mp hy).1,a,ha,by rw [←he]; abel⟩
end NSP14.Additive
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)
/-- Dense alphabets cover the same normalized cyclic group in two steps. -/
theorem dense_two_sum (t : ℕ) (hu : D.u=D.q+1+t) (ht : t≤D.q) :
    NSP14.Additive.iteratedSum D.residueAlphabet 2=Finset.univ := by
  rw [show 2=1+1 from rfl,NSP14.Additive.iteratedSum_succ,
    NSP14.Additive.iteratedSum_one]
  apply NSP14.Additive.two_sum_eq_univ_of_large
  rw [ZMod.card,D.residueAlphabet_card]
  omega

theorem dense_saturated (t : ℕ) (hu : D.u=D.q+1+t) (ht : t≤D.q)
    (n : ℕ) (hn : 2≤n) :
    NSP14.Additive.iteratedSum D.residueAlphabet n=Finset.univ := by
  apply Finset.eq_univ_iff_forall.mpr
  intro r
  apply NSP14.Additive.iteratedSum_subset_of_le D.zero_mem_residueAlphabet hn
  rw [D.dense_two_sum t hu ht]
  exact Finset.mem_univ r

/-- Exact W of the original endpoint data; this is not a model profile. -/
theorem dense_wordVolume (t : ℕ) (hu : D.u=D.q+1+t) (ht : t≤D.q) :
    D.wordVolume=D.q+1+2*t := by
  rw [D.wordVolume_tail_shift]
  have hs : (∑ j ∈ Finset.range D.u,
      (D.u-(NSP14.Additive.iteratedSum D.residueAlphabet (j+1)).card))=t := by
    rw [Finset.sum_eq_single 0]
    · rw [NSP14.Additive.iteratedSum_one,D.residueAlphabet_card,hu]
      omega
    · intro j _ hj
      rw [D.dense_saturated t hu ht (j+1) (by omega),Finset.card_univ,ZMod.card]
      exact Nat.sub_self _
    · intro h
      exact False.elim (h (Finset.mem_range.mpr D.u_pos))
  rw [hs,hu]
  omega

variable (k : Type) [Field k]
theorem dense_coreP (t : ℕ) (hu : D.u=D.q+1+t) (ht : t≤D.q) :
    D.coreP k≤D.q+1+2*t := by
  rw [←D.dense_wordVolume t hu ht]
  exact D.coreP_le_wordVolume k

theorem dense_actualR (t : ℕ) (hu : D.u=D.q+1+t) (ht : t≤D.q) :
    D.actualR k≤t := by
  have h := D.actualR_le_volume k
  rw [D.dense_wordVolume t hu ht,hu] at h
  omega
end NSP14.Endpoint.Data
