module
public import NSP14.Additive.CyclicGrowth
@[expose] public section
open scoped Pointwise Classical
namespace NSP14.Additive
variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

/-- The exception is a genuine subgroup of order two and its two cosets. -/
def TwoCosetException (A : Finset G) : Prop :=
  ∃ H : AddSubgroup G, Nat.card H = 2 ∧
    ∃ t : G, t ∉ H ∧ A = (H : Set G).toFinset ∪ (t +ᵥ (H : Set G).toFinset)

theorem fourPoint_small_growth (A : Finset G) (h0 : 0 ∈ A) (hA4 : A.card = 4)
    (hgen : AddSubgroup.closure (A : Set G) = ⊤) (n : ℕ)
    (hproper : iteratedSum A (n+1) ≠ Finset.univ)
    (hsmall : (iteratedSum A (n+1)).card < (iteratedSum A n).card+3) :
    Nat.card (sumStabilizer (iteratedSum A (n+1))) = 2 ∧ TwoCosetException A := by
  have hA : A.Nonempty := ⟨0,h0⟩
  let H := sumStabilizer (iteratedSum A (n+1))
  let c := (quotientImage A H).card
  let h := Nat.card H
  have hc : 2 ≤ c := quotientImage_card_two A h0 hgen H
    (stabilizer_ne_top_of_proper (iteratedSum_nonempty A hA _) hproper)
  have hp : 1 ≤ h := Nat.card_pos
  have hAc : 4 ≤ h*c := by
    have hh := Finset.card_le_card (subset_thicken A H)
    rw [hA4,card_thicken] at hh
    exact hh
  have hk := kneser (iteratedSum A n) A (iteratedSum_nonempty A hA n) hA
  rw [←iteratedSum_succ] at hk
  change (thicken (iteratedSum A n) H).card+(thicken A H).card ≤
    (iteratedSum A (n+1)).card+h at hk
  rw [card_thicken A H] at hk
  change (thicken (iteratedSum A n) H).card+h*c ≤ (iteratedSum A (n+1)).card+h at hk
  have hfirst := Finset.card_le_card (subset_thicken (iteratedSum A n) H)
  have hpay : h*c ≤ h+2 := by omega
  have hh : h = 2 := by
    have htwo := Nat.mul_le_mul_left h hc
    by_cases he : h = 1
    · rw [he,one_mul] at hAc hpay
      omega
    · omega
  have hc2 : c = 2 := by rw [hh] at hAc hpay; omega
  have hthick : A = thicken A H := Finset.eq_of_subset_of_card_le (subset_thicken A H) (by
    rw [card_thicken,hA4]
    change h*c ≤ 4
    rw [hh,hc2])
  have hex : ∃ t ∈ A, t ∉ H := by
    by_contra! he
    have hcl : AddSubgroup.closure (A : Set G) ≤ H := (AddSubgroup.closure_le H).mpr he
    rw [hgen] at hcl
    exact stabilizer_ne_top_of_proper (iteratedSum_nonempty A hA _) hproper (top_le_iff.mp hcl)
  obtain ⟨t,ht,htH⟩ := hex
  have hHt : (H : Set G).toFinset ⊆ A := by
    intro x hx
    rw [hthick]
    exact Finset.mem_add.mpr ⟨0,h0,x,hx,zero_add x⟩
  have htHt : t +ᵥ (H : Set G).toFinset ⊆ A := by
    rintro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_vadd_finset.mp hx
    rw [hthick]
    exact Finset.mem_add.mpr ⟨t,ht,y,hy,rfl⟩
  have hd : Disjoint (H : Set G).toFinset (t +ᵥ (H : Set G).toFinset) := by
    rw [Finset.disjoint_left]
    intro x hx htx
    obtain ⟨y,hy,he⟩ := Finset.mem_vadd_finset.mp htx
    apply htH
    have hs := H.sub_mem (Set.mem_toFinset.mp hx) (Set.mem_toFinset.mp hy)
    have he' : x-y=t := by rw [←he]; simp
    rwa [he'] at hs
  have hcardH : (H : Set G).toFinset.card = 2 := by
    rw [Set.toFinset_card,←Nat.card_eq_fintype_card]
    exact hh
  have heq : A = (H : Set G).toFinset ∪ (t +ᵥ (H : Set G).toFinset) :=
    (Finset.eq_of_subset_of_card_le (Finset.union_subset hHt htHt) (by
      rw [Finset.card_union_of_disjoint hd,Finset.card_vadd_finset,hcardH,hA4])).symm
  exact ⟨hh,H,hh,t,htH,heq⟩
end NSP14.Additive
