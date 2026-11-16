module
public import NSP14.Additive.CyclicInterval
@[expose] public section
open scoped Pointwise BigOperators Classical
namespace NSP14.Additive
variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Finite G] {ℓ : ℕ}

/-- A single base element and positive coefficients, with an honest Nat sum
below its additive order. Defined as a proposition, proved from Connected. -/
def HasSmallRepresentatives (seq : Fin ℓ → G) (I : Finset (Fin ℓ)) : Prop :=
  ∃ a : G, ∃ w : Fin ℓ → ℕ,
    (∀ i ∈ I, 0 < w i ∧ seq i = w i • a) ∧
    (∑ i ∈ I, w i) < addOrderOf a ∧
    indexedSubsetSums seq I = cyclicInterval a (∑ i ∈ I, w i)

theorem connected_small_representatives {seq : Fin ℓ → G} (hz : ZeroSumFree seq)
    {I : Finset (Fin ℓ)} (hc : Connected seq I) : HasSmallRepresentatives seq I := by
  induction hc with
  | singleton i =>
    refine ⟨seq i,fun _ => 1,?_,?_,?_⟩
    · intro j hj
      have he : j = i := Finset.mem_singleton.mp hj
      subst j
      simp
    · simp only [Finset.sum_singleton]
      have hp := addOrderOf_pos (seq i)
      have hn : addOrderOf (seq i) ≠ 1 := fun hh => hz.term_ne_zero i
        (AddMonoid.addOrderOf_eq_one_iff.mp hh)
      omega
    · rw [Finset.sum_singleton,cyclicInterval_one]
      ext x
      simp [indexedSubsetSums,eq_comm]
  | @insert I i hi hI hvalue ih =>
    obtain ⟨a,w,hw,hS,hinterval⟩ := ih
    let S := ∑ j ∈ I, w j
    obtain ⟨x,hx,y,hy,hxy⟩ := Finset.mem_sub.mp hvalue
    rw [hinterval] at hx hy
    obtain ⟨p,hp,rfl⟩ := (mem_cyclicInterval a S x).mp hx
    obtain ⟨q,hq,rfl⟩ := (mem_cyclicInterval a S y).mp hy
    have hqp : q < p := by
      by_contra hnot
      have hpq : p ≤ q := by omega
      have hn : -seq i ∈ indexedSubsetSums seq I := by
        rw [hinterval]
        refine (mem_cyclicInterval a S _).mpr ⟨q-p,by omega,?_⟩
        rw [←hxy,sub_nsmul _ hpq,neg_sub,sub_eq_add_neg]
      exact hz.neg_not_mem_subsetSums hi hn
    let k := p-q
    have hk : 0 < k := by omega
    have hkS : k ≤ S := by omega
    have hki : seq i = k • a := by
      rw [←hxy]
      simpa only [k,sub_eq_add_neg] using (sub_nsmul a (by omega : q ≤ p)).symm
    have hnext : S+k < addOrderOf a := by
      by_contra hnot
      have hmem : -seq i ∈ indexedSubsetSums seq I := by
        rw [hinterval]
        refine (mem_cyclicInterval a S _).mpr ⟨addOrderOf a-k,by omega,?_⟩
        apply eq_neg_iff_add_eq_zero.mpr
        rw [hki,←add_nsmul,Nat.sub_add_cancel (by omega : k ≤ addOrderOf a),
          addOrderOf_nsmul_eq_zero]
      exact hz.neg_not_mem_subsetSums hi hmem
    let w' := Function.update w i k
    have hweight : ∀ j ∈ I, w' j = w j := by
      intro j hj
      exact Function.update_of_ne (show j ≠ i from fun he => hi (he ▸ hj)) k w
    have hsum : (∑ j ∈ insert i I, w' j) = S+k := by
      rw [Finset.sum_insert hi]
      have he : ∑ j ∈ I, w' j = S := Finset.sum_congr rfl hweight
      rw [he]
      change Function.update w i k i+S=S+k
      rw [Function.update_self,add_comm]
    refine ⟨a,w',?_,?_,?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa only [w',Function.update_self] using And.intro hk hki
      · rw [hweight j hj]
        exact hw j hj
    · rw [hsum]
      exact hnext
    · rw [hsum,indexedSubsetSums_insert seq I i hi,hinterval,hki]
      exact cyclicInterval_union a S k (by omega)
end NSP14.Additive
