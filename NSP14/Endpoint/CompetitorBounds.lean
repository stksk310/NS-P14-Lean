module
public import NSP14.Endpoint.CarrySums
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

theorem shiftedResidue_u (s : Fin D.u) : D.shiftedResidue s D.u=s := by
  apply Fin.ext
  change (s.val+D.u*D.m)%D.u=s.val
  rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt s.isLt]

theorem competitorFiber_nonempty (s : Fin D.u) : ∃ c : ℕ×ℕ,c∈D.competitorFiber s := by
  obtain ⟨c,hc⟩ := D.coreFiber_nonempty s
  exact ⟨D.forbiddenStart s D.u c,s,D.u,D.u_pos,c,hc,D.shiftedResidue_u s,le_rfl⟩

theorem competitorFloor_exists (s : Fin D.u) : ∃ K,∃ c : ℕ×ℕ,c∈D.competitorFiber s ∧ c.2=K := by
  obtain ⟨c,hc⟩ := D.competitorFiber_nonempty s
  exact ⟨c.2,c,hc,rfl⟩

noncomputable def competitorFloor (s : Fin D.u) : ℕ := Nat.find (D.competitorFloor_exists s)

theorem competitorFloor_le (s : Fin D.u) (c : ℕ×ℕ) (hc : c∈D.competitorFiber s) :
    D.competitorFloor s≤c.2 := Nat.find_min' _ ⟨c,hc,rfl⟩

theorem competitorMin_finite (s : Fin D.u) : Set.Finite {c | Minimal (·∈D.competitorFiber s) c} := by
  obtain ⟨c,hc⟩ := D.competitorFiber_nonempty s
  exact NSP14.Endpoint.minimal_finite_of_mem _ c hc

noncomputable def competitorZ (s : Fin D.u) : ℕ := Nat.card {c | Minimal (·∈D.competitorFiber s) c}-1

theorem competitorMin_card (s : Fin D.u) : Nat.card {c | Minimal (·∈D.competitorFiber s) c}=D.competitorZ s+1 := by
  have : Finite {c | Minimal (·∈D.competitorFiber s) c} := (D.competitorMin_finite s).to_subtype
  obtain ⟨c,hc⟩ := D.competitorFiber_nonempty s
  obtain ⟨b,_,hb⟩ := exists_minimal_le_of_wellFoundedLT (·∈D.competitorFiber s) c hc
  have : Nonempty {c | Minimal (·∈D.competitorFiber s) c} := ⟨⟨b,hb⟩⟩
  have hp : 0<Nat.card {c | Minimal (·∈D.competitorFiber s) c} := Nat.card_pos
  unfold competitorZ
  omega

theorem competitorZ_point_bound (s : Fin D.u) (c : ℕ×ℕ) (hc : c∈D.competitorFiber s) :
    D.competitorZ s≤c.1+c.2-D.competitorFloor s := by
  have h := NSP14.Endpoint.minimal_card_le (D.competitorFiber s) c (D.competitorFloor s) hc
    (D.competitorFloor_le s)
  rw [D.competitorMin_card] at h
  omega

theorem competitorMin_height (s : Fin D.u) (c : ℕ×ℕ) (hc : Minimal (·∈D.competitorFiber s) c) :
    c.1≤D.coreHeight-2 := by
  obtain ⟨r,j,hj,a,ha,hs,hstart⟩ := hc.prop
  obtain ⟨b,hba,hb⟩ := D.exists_minimalFiber_le r a ha
  have hstart' : D.forbiddenStart r j b≤c := by
    apply (D.forbiddenStart_le r j b c).mpr
    have h := (D.forbiddenStart_le r j a c).mp hstart
    obtain ⟨hL,hK⟩ := hba
    constructor <;> omega
  have hmem : D.forbiddenStart r j b∈D.competitorFiber s := ⟨r,j,hj,b,hb.prop,hs,le_rfl⟩
  have he := hc.eq_of_le hmem hstart'
  have hh := D.forbiddenStart_height r j b.1 b.2 D.coreHeight
    (D.minimalPoint_height r b ((D.mem_minimalPoints r b).mpr hb))
  change (D.forbiddenStart r j b).1≤D.coreHeight-2*j at hh
  rw [he] at hh
  omega

theorem competitorZ_height (s : Fin D.u) : D.competitorZ s≤D.coreHeight-2 := by
  let f : {c | Minimal (·∈D.competitorFiber s) c} → Fin (D.coreHeight-2+1) :=
    fun c => ⟨c.val.1,by have := D.competitorMin_height s c.val c.property;omega⟩
  have hi : Function.Injective f := by
    intro a b h
    exact Subtype.ext (NSP14.Endpoint.minimal_pair_eq_of_fst a.property b.property (congrArg Fin.val h))
  have hb := Nat.card_le_card_of_injective f hi
  rw [Nat.card_fin,D.competitorMin_card] at hb
  omega

theorem competitor_point_volume (s : Fin D.u) (c : ℕ×ℕ) (hc : c∈D.competitorFiber s) :
    D.m≤s.val+D.u*c.2 := by
  obtain ⟨r,j,hj,b,_,hs,hstart⟩ := hc
  have hK : b.2+D.carry r j≤c.2 := hstart.2
  have hcar := D.carry_eq r j
  rw [hs] at hcar
  have hm := Nat.mul_le_mul_right D.m hj
  nlinarith

theorem competitorFloor_ceiling (s : Fin D.u) : D.residueCeiling s≤D.competitorFloor s := by
  obtain ⟨c,hc,hK⟩ := Nat.find_spec (D.competitorFloor_exists s)
  have hvol := D.competitor_point_volume s c hc
  have hs := s.isLt
  have hm := D.u_lt
  have hu := D.u_pos
  unfold residueCeiling
  apply (Nat.div_le_iff_le_mul hu).mpr
  have hK' : c.2=D.competitorFloor s := hK
  rw [←hK']
  have hvol' : D.m≤s.val+c.2*D.u := by nlinarith only [hvol]
  omega

theorem competitorFloor_sum : D.m≤∑ s : Fin D.u,D.competitorFloor s := by
  rw [←D.residueCeiling_sum]
  exact Finset.sum_le_sum (fun s _ => D.competitorFloor_ceiling s)

theorem competitorZ_shortest (r : Fin D.u) :
    D.competitorZ (D.shiftedResidue r 1)+D.competitorFloor (D.shiftedResidue r 1)≤
      (D.shortestPoint r).1+(D.shortestPoint r).2+D.carry r 1 := by
  let c := D.forbiddenStart r 1 (D.shortestPoint r)
  have hc : c∈D.competitorFiber (D.shiftedResidue r 1) :=
    ⟨r,1,le_rfl,D.shortestPoint r,D.shortestPoint_mem r,rfl,le_rfl⟩
  have hz := D.competitorZ_point_bound _ c hc
  have hK := D.competitorFloor_le _ c hc
  have hL := D.forbiddenStart_height r 1 (D.shortestPoint r).1 (D.shortestPoint r).2
    (D.shortestPoint r).1 le_rfl
  change c.1≤(D.shortestPoint r).1-2*1 at hL
  have hcK : c.2=(D.shortestPoint r).2+D.carry r 1 := rfl
  omega

/-- The same shortest paths, same carries and same T_s are summed.
No reflected or separately optimized data enter this inequality. -/
theorem competitorZ_sum_bound : (∑ s : Fin D.u,D.competitorZ s)≤D.wordVolume-D.u := by
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun r _ => D.competitorZ_shortest r)
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib] at h
  have hz := D.shiftOneEquiv.sum_comp D.competitorZ
  have hκ := D.shiftOneEquiv.sum_comp D.competitorFloor
  change (∑ r : Fin D.u,D.competitorZ (D.shiftedResidue r 1))=(∑ r : Fin D.u,D.competitorZ r) at hz
  change (∑ r : Fin D.u,D.competitorFloor (D.shiftedResidue r 1))=(∑ r : Fin D.u,D.competitorFloor r) at hκ
  rw [hz,hκ,D.carry_sum_one] at h
  have hk := D.competitorFloor_sum
  rw [D.wordVolume_coordinates]
  omega
end NSP14.Endpoint.Data
