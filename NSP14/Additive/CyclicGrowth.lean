module
public import NSP14.Additive.KneserIterated
@[expose] public section
open scoped Pointwise Classical
namespace NSP14.Additive
variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem stabilizer_ne_top_of_proper {S : Finset G} (hS : S.Nonempty)
    (hproper : S ≠ Finset.univ) : sumStabilizer S ≠ ⊤ := by
  intro he
  apply hproper
  apply Finset.eq_univ_iff_forall.mpr
  intro x
  obtain ⟨s,hs⟩ := hS
  have hg : x-s ∈ sumStabilizer S := by rw [he]; trivial
  have ht := (mem_sumStabilizer S (x-s)).mp hg
  have hm : x ∈ (x-s) +ᵥ S :=
    Finset.mem_vadd_finset.mpr ⟨s,hs,sub_add_cancel _ _⟩
  rwa [ht] at hm

omit [DecidableEq G] [Fintype G] in
theorem quotientImage_card_two (A : Finset G) (h0 : 0 ∈ A)
    (hgen : AddSubgroup.closure (A : Set G) = ⊤) (H : AddSubgroup G) (hH : H ≠ ⊤) :
    2 ≤ (quotientImage A H).card := by
  have hex : ∃ a ∈ A, a ∉ H := by
    by_contra! hh
    have hl : AddSubgroup.closure (A : Set G) ≤ H := (AddSubgroup.closure_le H).mpr hh
    rw [hgen] at hl
    exact hH (top_le_iff.mp hl)
  obtain ⟨a,ha,haH⟩ := hex
  have hπ : (QuotientAddGroup.mk a : G ⧸ H) ≠ 0 :=
    fun he => haH ((QuotientAddGroup.eq_zero_iff a).mp he)
  apply Nat.succ_le_iff.mpr
  apply Finset.one_lt_card.mpr
  exact ⟨0,Finset.mem_image.mpr ⟨0,h0,QuotientAddGroup.mk_zero H⟩,
    QuotientAddGroup.mk a,Finset.mem_image_of_mem _ ha,hπ.symm⟩

/-- Kneser pays at least half the number of generators at every proper
growth step. This uses the actual stabilizer of the next sum. -/
theorem proper_sum_growth (A : Finset G) (h0 : 0 ∈ A)
    (hgen : AddSubgroup.closure (A : Set G) = ⊤) (n : ℕ) (_hn : 1 ≤ n)
    (hproper : iteratedSum A (n+1) ≠ Finset.univ) :
    (iteratedSum A n).card + (A.card+1)/2 ≤ (iteratedSum A (n+1)).card := by
  have hA : A.Nonempty := ⟨0,h0⟩
  let H := sumStabilizer (iteratedSum A (n+1))
  let c := (quotientImage A H).card
  let h := Nat.card H
  have hH : H ≠ ⊤ := stabilizer_ne_top_of_proper
    (iteratedSum_nonempty A hA (n+1)) hproper
  have hc : 2 ≤ c := quotientImage_card_two A h0 hgen H hH
  have hA' : A.card ≤ h*c := by
    rw [←card_thicken]
    exact Finset.card_le_card (subset_thicken A H)
  have hk := kneser (iteratedSum A n) A (iteratedSum_nonempty A hA n) hA
  rw [←iteratedSum_succ] at hk
  have hfirst := Finset.card_le_card (subset_thicken (iteratedSum A n) H)
  have hsecond : (thicken A H).card = h*c := card_thicken A H
  change (thicken (iteratedSum A n) H).card+(thicken A H).card ≤
    (iteratedSum A (n+1)).card+h at hk
  rw [hsecond] at hk
  have hcsub : c ≤ 2*(c-1) := by omega
  have hhalf : A.card ≤ 2*((c-1)*h) := by
    calc
      _ ≤ h*c := hA'
      _ = c*h := mul_comm _ _
      _ ≤ (2*(c-1))*h := Nat.mul_le_mul_right h hcsub
      _ = _ := mul_assoc _ _ _
  have hprod : c*h = (c-1)*h+h := by
    have he : c=(c-1)+1 := by omega
    nth_rw 1 [he]
    rw [add_mul,one_mul]
  have hpay : (A.card+1)/2 ≤ (c-1)*h := by omega
  nlinarith

omit [Fintype G] in
theorem iteratedSum_subset_of_le {A : Finset G} (h0 : 0 ∈ A) {n m : ℕ} (hnm : n ≤ m) :
    iteratedSum A n ⊆ iteratedSum A m := by
  induction m,hnm using Nat.le_induction with
  | base => rfl
  | succ m _ ih => exact ih.trans (iteratedSum_subset_succ h0 m)

theorem generated_sum_growth (A : Finset G) (h0 : 0 ∈ A)
    (hgen : AddSubgroup.closure (A : Set G) = ⊤) (n : ℕ) (hn : 1 ≤ n) :
    min (Fintype.card G) (A.card+(n-1)*((A.card+1)/2)) ≤ (iteratedSum A n).card := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      simpa only [Nat.zero_add,Nat.sub_self,zero_mul,add_zero,iteratedSum_one] using
        (min_le_right (Fintype.card G) A.card)
    · have hn' : 1 ≤ n := by omega
      by_cases hs : iteratedSum A (n+1) = Finset.univ
      · rw [hs,Finset.card_univ]
        exact min_le_left _ _
      · have hg := proper_sum_growth A h0 hgen n hn' hs
        have hi := ih hn'
        have hcard : (iteratedSum A (n+1)).card < Fintype.card G :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _,hs⟩)
        have he : n*((A.card+1)/2) = (n-1)*((A.card+1)/2)+(A.card+1)/2 := by
          calc
            _ = (n-1+1)*((A.card+1)/2) := congrArg (· * ((A.card+1)/2)) (Nat.sub_add_cancel hn').symm
            _ = _ := by rw [add_mul,one_mul]
        simp only [Nat.add_sub_cancel] at *
        omega
end NSP14.Additive
namespace NSP14.Additive
theorem zmod_generates_of_one_mem {u : ℕ} [NeZero u] (A : Finset (ZMod u)) (h1 : 1 ∈ A) :
    AddSubgroup.closure (A : Set (ZMod u))=⊤ := by
  apply top_unique
  intro x _
  have h : (1 : ZMod u) ∈ AddSubgroup.closure (A : Set (ZMod u)) := AddSubgroup.subset_closure h1
  have hx := (AddSubgroup.closure (A : Set (ZMod u))).nsmul_mem h x.val
  simpa only [nsmul_eq_mul,mul_one,ZMod.natCast_zmod_val] using hx
end NSP14.Additive
