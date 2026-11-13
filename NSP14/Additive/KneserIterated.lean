module
public import NSP14.Additive.QuotientCounting
@[expose] public section
open scoped Pointwise Classical
namespace NSP14.Additive
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem stabilizer_le_add_left (A B : Finset G) :
    sumStabilizer A ≤ sumStabilizer (A+B) := by
  intro g hg
  rw [mem_sumStabilizer] at hg ⊢
  rw [←Finset.singleton_add, ←add_assoc, Finset.singleton_add, hg]

theorem stabilizer_iterated_le (A : Finset G) {j n : ℕ} (hjn : j ≤ n) :
    sumStabilizer (iteratedSum A j) ≤ sumStabilizer (iteratedSum A n) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hjn
  rw [iteratedSum_add]
  exact stabilizer_le_add_left _ _

variable [Fintype G]

theorem subset_thicken (A : Finset G) (H : AddSubgroup G) : A ⊆ thicken A H := by
  intro x hx
  exact Finset.mem_add.mpr ⟨x,hx,0,by simp,add_zero x⟩

theorem thicken_eq_of_le_stabilizer (A : Finset G) (H : AddSubgroup G)
    (hH : H ≤ sumStabilizer A) : thicken A H = A := by
  apply Finset.Subset.antisymm ?_ (subset_thicken A H)
  rintro x hx
  obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_add.mp hx
  have he := (mem_sumStabilizer A b).mp (hH (Set.mem_toFinset.mp hb))
  rw [add_comm]
  have hm : b+a ∈ b +ᵥ A := Finset.mem_vadd_finset.mpr ⟨a,ha,rfl⟩
  rwa [he] at hm

theorem subgroup_toFinset_add (H : AddSubgroup G) :
    (H : Set G).toFinset + (H : Set G).toFinset = (H : Set G).toFinset := by
  ext x
  simp only [Finset.mem_add, Set.mem_toFinset]
  constructor
  · rintro ⟨a,ha,b,hb,rfl⟩
    exact H.add_mem ha hb
  · intro hx
    exact ⟨x,hx,0,H.zero_mem,add_zero x⟩

theorem subgroup_translate (H : AddSubgroup G) (g : G) (hg : g ∈ H) :
    g +ᵥ (H : Set G).toFinset = (H : Set G).toFinset := by
  ext x
  simp only [Finset.mem_vadd_finset, Set.mem_toFinset, vadd_eq_add]
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact H.add_mem hg hy
  · intro hx
    exact ⟨x-g,H.sub_mem hx hg,add_sub_cancel _ _⟩

theorem le_stabilizer_thicken (A : Finset G) (H : AddSubgroup G) :
    H ≤ sumStabilizer (thicken A H) := by
  intro g hg
  rw [mem_sumStabilizer, ←Finset.singleton_add]
  dsimp only [thicken]
  rw [add_left_comm, Finset.singleton_add, subgroup_translate H g hg]

theorem iteratedSum_thicken (A : Finset G) (H : AddSubgroup G) (n : ℕ)
    (hn : 1 ≤ n) : iteratedSum (thicken A H) n = thicken (iteratedSum A n) H := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hz : n = 0
    · subst n
      exact (iteratedSum_one _).trans (congrArg (thicken · H) (iteratedSum_one A).symm)
    · rw [iteratedSum_succ,ih (by omega),iteratedSum_succ]
      dsimp only [thicken]
      rw [add_add_add_comm,subgroup_toFinset_add]

theorem iteratedSum_thicken_stabilizer (A : Finset G)
    (n : ℕ) (hn : 1 ≤ n) :
    iteratedSum (thicken A (sumStabilizer (iteratedSum A n))) n = iteratedSum A n := by
  rw [iteratedSum_thicken A _ n hn]
  exact thicken_eq_of_le_stabilizer _ _ le_rfl

/-- Iterated Kneser with the stabilizer of the final sum, in additive Nat form. -/
theorem kneser_iterated (A : Finset G) (hA : A.Nonempty) (n : ℕ) (hn : 1 ≤ n) :
    n * (thicken A (sumStabilizer (iteratedSum A n))).card ≤
      (iteratedSum A n).card + (n-1)*Nat.card (sumStabilizer (iteratedSum A n)) := by
  let H := sumStabilizer (iteratedSum A n)
  let B := thicken A H
  have hB : B.Nonempty := hA.mono (subset_thicken A H)
  have hlast : iteratedSum B n = iteratedSum A n := iteratedSum_thicken_stabilizer A n hn
  have hstab (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) :
      sumStabilizer (iteratedSum B j) = H := by
    apply le_antisymm
    · have hh := stabilizer_iterated_le B hjn
      rw [hlast] at hh
      exact hh
    · rw [iteratedSum_thicken A H j hj]
      exact le_stabilizer_thicken _ _
  have hbound (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) :
      j*B.card ≤ (iteratedSum B j).card + (j-1)*Nat.card H := by
    induction j with
    | zero => omega
    | succ j ih =>
      by_cases hz : j = 0
      · subst j; simp
      · have hj' : 1 ≤ j := by omega
        have hi := ih hj' (by omega)
        have hk := kneser (iteratedSum B j) B (iteratedSum_nonempty B hB j) hB
        rw [←iteratedSum_succ,hstab (j+1) (by omega) hjn] at hk
        have hs1 := Finset.card_le_card (subset_thicken (iteratedSum B j) H)
        have hs2 := Finset.card_le_card (subset_thicken B H)
        have hp : (j+1)*B.card = j*B.card+B.card := by rw [add_mul,one_mul]
        rw [hp]
        have he : j*Nat.card H = (j-1)*Nat.card H+Nat.card H := by
          calc
            j*Nat.card H = (j-1+1)*Nat.card H :=
              congrArg (· * Nat.card H) (Nat.sub_add_cancel hj').symm
            _ = (j-1)*Nat.card H+Nat.card H := by rw [add_mul,one_mul]
        simp only [Nat.add_sub_cancel] at *
        omega
  have hh := hbound n hn le_rfl
  rw [hlast] at hh
  exact hh
end NSP14.Additive
