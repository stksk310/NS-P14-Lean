module
public import NSP14.Endpoint.SocleCorners
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Endpoint.Data
variable (D : Data)

theorem carry_u (r : Fin D.u) : D.carry r D.u=D.m := by
  have hc := D.carry_eq r D.u
  rw [D.shiftedResidue_u] at hc
  have := D.u_pos
  nlinarith

theorem competitor_zero_column (r : Fin D.u) : (0,D.m+D.u)∈D.competitorFiber r := by
  let c := D.shortestPoint r
  have hc := D.shortestPoint_minimal r
  have hb := D.minimalFiber_budget r c hc
  have hu := D.u_pos
  have hh := D.forbiddenStart_height r D.u c.1 c.2 D.coreHeight
    (D.minimalPoint_height r c ((D.mem_minimalPoints r c).mpr hc))
  change (D.forbiddenStart r D.u c).1≤D.coreHeight-2*D.u at hh
  have hH := D.coreHeight_le
  have hz : (D.forbiddenStart r D.u c).1=0 := by omega
  have hK : (D.forbiddenStart r D.u c).2≤D.m+D.u := by
    change c.2+D.carry r D.u≤D.m+D.u
    rw [D.carry_u]
    omega
  exact ⟨r,D.u,D.u_pos,c,hc.prop,D.shiftedResidue_u r,⟨by rw [hz],hK⟩⟩

theorem fiberSocle_competitor_corner (r : Fin D.u) (c : D.FiberSocleIndex r) :
    NSP14.Endpoint.Corner (D.competitorFiber r) c.val := by
  have hN := c.property.2
  simp only [NSP14.Endpoint.Corner,D.actualDeadFiber_eq_inter,Set.mem_inter_iff] at hN
  exact ⟨fun ht => hN.1 ⟨c.property.1,ht⟩,hN.2.1.2,hN.2.2.2⟩

theorem fiberSocle_horizontal (r : Fin D.u) (c : D.FiberSocleIndex r) : c.val.1<D.coreHeight-2 := by
  have hc := D.fiberSocle_competitor_corner r c
  let z : {c : ℕ×ℕ // NSP14.Endpoint.Corner (D.competitorFiber r) c} := ⟨c.val,hc⟩
  have hr := NSP14.Endpoint.cornerRight_fst (D.competitorFiber r) (D.competitorFiber_upward r) z
  have hh := D.competitorMin_height r (NSP14.Endpoint.cornerRight _ z).val
    (NSP14.Endpoint.cornerRight _ z).property
  rw [hr] at hh
  change c.val.1+1≤D.coreHeight-2 at hh
  omega

theorem fiberSocle_rectangle (r : Fin D.u) (c : D.FiberSocleIndex r) : c.val.1<D.u ∧ c.val.2<D.m+D.u := by
  have hc := D.fiberSocle_competitor_corner r c
  let z : {c : ℕ×ℕ // NSP14.Endpoint.Corner (D.competitorFiber r) c} := ⟨c.val,hc⟩
  have hr := NSP14.Endpoint.cornerRight_fst (D.competitorFiber r) (D.competitorFiber_upward r) z
  have hh := D.competitorMin_height r (NSP14.Endpoint.cornerRight _ z).val
    (NSP14.Endpoint.cornerRight _ z).property
  rw [hr] at hh
  change c.val.1+1≤D.coreHeight-2 at hh
  have hH := D.coreHeight_le
  constructor
  · omega
  · by_contra hn
    exact hc.1 (D.competitorFiber_upward r (D.competitor_zero_column r) ⟨Nat.zero_le _,by omega⟩)
end NSP14.Endpoint.Data
