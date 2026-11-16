module
public import NSP14.Ordinary.TowerEuler
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]

theorem towerHighIdeal_eq_bot_of_top_lt (s n : ℕ)
    (hs : S.qTopDegree+1 ≤ s) (hn : S.qTopDegree < n) : S.towerHighIdeal k s n=⊥ := by
  apply bot_unique
  intro a ha
  obtain ⟨b,hb,rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp ha
  change Ideal.Quotient.mk (S.jumpIdeal k (s-1)) b=0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hN : b ∈ S.nonAperyIdeal k :=
    S.highIdeal_top_le_nonApery k (S.highIdeal_antitone k (by omega : S.qTopDegree+1 ≤ n) hb)
  have hm := S.jumpIdeal_monotone k (by omega : S.qTopDegree ≤ s-1)
  rw [S.jumpIdeal_top k] at hm
  exact hm hN

namespace LinearCutData
variable {S k} (C : S.LinearCutData k)

theorem cutHighEuler_eq_zero_of_top_lt (s n j : ℕ)
    (hs : S.qTopDegree+1 ≤ s) (hn : S.qTopDegree < n) : C.cutHighEuler s n j=0 := by
  have : Subsingleton ↥(S.towerHighIdeal k s n) := by
    rw [S.towerHighIdeal_eq_bot_of_top_lt k s n hs hn]
    infer_instance
  have : Subsingleton (C.cutHigh s n) := inferInstanceAs (Subsingleton ↥(S.towerHighIdeal k s n))
  let := C.cutHigh_finite s n
  let := C.cutHigh_coefficientFinite s n
  exact NSP14.Homological.bettiEuler_eq_zero_of_subsingleton k (Fin S.actualCutRank) _ j
end LinearCutData
end NSP14.NumericalSemigroup
