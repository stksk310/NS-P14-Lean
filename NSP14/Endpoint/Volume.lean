module
public import NSP14.Endpoint.MinimalGenerators
public import NSP14.Endpoint.Antichains
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

theorem minimalPoints_card_eq (r : Fin D.u) : (D.minimalPoints r).card=
    Nat.card {c | Minimal (·∈D.coreFiber r) c} := by
  exact (Nat.card_eq_card_finite_toFinset (D.minimalFiber_finite r)).symm

theorem minimalPoints_card_le (r : Fin D.u) (c : ℕ×ℕ) (hc : c∈D.coreFiber r) :
    (D.minimalPoints r).card≤c.1+c.2+1 := by
  rw [D.minimalPoints_card_eq]
  simpa only [Nat.sub_zero] using NSP14.Endpoint.minimal_card_le (D.coreFiber r) c 0 hc (by simp)

theorem minimalPoints_card_zero : (D.minimalPoints ⟨0,D.u_pos⟩).card=1 := by
  have he : D.minimalPoints ⟨0,D.u_pos⟩={(0,0)} := by
    ext c
    rw [D.mem_minimalPoints,Finset.mem_singleton]
    constructor
    · exact D.minimalFiber_zero c
    · intro hc
      subst c
      exact ⟨D.coreFiber_zero (0,0),fun b _ hb => bot_le⟩
  rw [he,Finset.card_singleton]

theorem minimalPoints_shortest_bound (r : Fin D.u) :
    (D.minimalPoints r).card≤D.shortestDegree r+(if r.val=0 then 1 else 0) := by
  by_cases hr : r.val=0
  · have he : r=⟨0,D.u_pos⟩ := Fin.ext hr
    subst r
    rw [D.minimalPoints_card_zero,D.shortestDegree_zero]
    simp
  · have h := D.minimalPoints_card_le r (D.shortestPoint r) (D.shortestPoint_mem r)
    have he := D.shortestPoint_degree r
    simp only [epsilon,hr,ite_false] at he
    simp only [hr,ite_false,add_zero]
    omega

noncomputable def wordVolume : ℕ := 1+∑ r : Fin D.u,D.shortestDegree r
noncomputable def minimalCount : ℕ := ∑ r : Fin D.u,(D.minimalPoints r).card

/-- The shortest path resource controls all actual minimal fiber
points simultaneously. The unit residue contributes the single 1. -/
theorem minimalCount_volume : (∑ r : Fin D.u,(D.minimalPoints r).card)≤
    1+∑ r : Fin D.u,D.shortestDegree r := by
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun r _ => D.minimalPoints_shortest_bound r)
  rw [Finset.sum_add_distrib] at h
  have he : (∑ r : Fin D.u,if r.val=0 then 1 else 0)=1 := by
    have hh (r : Fin D.u) : r.val=0 ↔ r=⟨0,D.u_pos⟩ := ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
    simp only [hh,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [he] at h
  omega
end NSP14.Endpoint.Data
