module
public import NSP14.Endpoint.ActualKernel
public import NSP14.Endpoint.MinimalBounds
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

def carryPeriod : ℕ := D.u/Nat.gcd D.m D.u
def carryStep : ℕ := D.m/Nat.gcd D.m D.u
def stoppingStart : ℕ := (D.u-2)/2

theorem carryPeriod_pos : 0<D.carryPeriod :=
  Nat.div_pos (Nat.gcd_le_right D.m D.u_pos) (Nat.gcd_pos_of_pos_right D.m D.u_pos)

theorem carryPeriod_identity : D.carryPeriod*D.m=D.u*D.carryStep := by
  have hg := Nat.gcd_pos_of_pos_right D.m D.u_pos
  have hu := Nat.div_mul_cancel (Nat.gcd_dvd_right D.m D.u)
  have hm := Nat.div_mul_cancel (Nat.gcd_dvd_left D.m D.u)
  unfold carryPeriod carryStep
  apply Nat.eq_of_mul_eq_mul_left hg
  nlinarith only [hu,hm]

theorem shiftedResidue_period (r : Fin D.u) (j t : ℕ) :
    D.shiftedResidue r (j+D.carryPeriod*t)=D.shiftedResidue r j := by
  apply Fin.ext
  change (r.val+(j+D.carryPeriod*t)*D.m)%D.u=(r.val+j*D.m)%D.u
  have h : r.val+(j+D.carryPeriod*t)*D.m=r.val+j*D.m+D.u*(D.carryStep*t) := by
    have := D.carryPeriod_identity
    nlinarith
  rw [h,Nat.add_mul_mod_self_left]

theorem carry_period (r : Fin D.u) (j t : ℕ) :
    D.carry r (j+D.carryPeriod*t)=D.carry r j+D.carryStep*t := by
  change (r.val+(j+D.carryPeriod*t)*D.m)/D.u=(r.val+j*D.m)/D.u+D.carryStep*t
  have h : r.val+(j+D.carryPeriod*t)*D.m=r.val+j*D.m+D.u*(D.carryStep*t) := by
    have := D.carryPeriod_identity
    nlinarith
  rw [h,Nat.add_mul_div_left _ _ D.u_pos]

theorem forbiddenStart_mono (r : Fin D.u) (j : ℕ) {a b : ℕ×ℕ} (h : a≤b) :
    D.forbiddenStart r j a≤D.forbiddenStart r j b := by
  apply (D.forbiddenStart_le r j a _).mpr
  have hc := (D.forbiddenStart_le r j b (D.forbiddenStart r j b)).mp le_rfl
  exact ⟨by have := h.1;omega,by have := h.2;change a.2+D.carry r j≤b.2+D.carry r j;omega⟩

theorem forbiddenStart_tail_zero (r : Fin D.u) (j : ℕ) (c : ℕ×ℕ)
    (h : Minimal (·∈D.coreFiber r) c) (hj : D.stoppingStart<j) :
    (D.forbiddenStart r j c).1=0 := by
  have hb := D.minimalFiber_budget r c h
  have hh := D.forbiddenStart_height r j c.1 c.2 (D.u-2) (by omega)
  change (D.forbiddenStart r j c).1≤D.u-2-2*j at hh
  have hd := Nat.mod_add_div (D.u-2) 2
  have hm := Nat.mod_lt (D.u-2) (by omega : 0<2)
  unfold stoppingStart at hj
  omega

/-- All positive competitors are reduced in the same orientation,
using the actual carry period u/gcd(m,u), without assuming coprimality. -/
theorem forbiddenStart_stopping (r : Fin D.u) (j : ℕ) (c : ℕ×ℕ)
    (hj : 1≤j) (hc : Minimal (·∈D.coreFiber r) c) :
    ∃ j',1≤j' ∧ j'≤D.stoppingStart+D.carryPeriod ∧
      D.shiftedResidue r j'=D.shiftedResidue r j ∧
        D.forbiddenStart r j' c≤D.forbiddenStart r j c := by
  by_cases hsmall : j≤D.stoppingStart+D.carryPeriod
  · exact ⟨j,hj,hsmall,rfl,le_rfl⟩
  · let j' := D.stoppingStart+1+(j-(D.stoppingStart+1))%D.carryPeriod
    let t := (j-(D.stoppingStart+1))/D.carryPeriod
    have hp := D.carryPeriod_pos
    have hmod := Nat.mod_lt (j-(D.stoppingStart+1)) hp
    have hdiv := Nat.mod_add_div (j-(D.stoppingStart+1)) D.carryPeriod
    have hj' : D.stoppingStart<j' := by dsimp [j'];omega
    have he : j=j'+D.carryPeriod*t := by dsimp [j',t];omega
    refine ⟨j',by omega,by dsimp [j'];omega,?_,?_⟩
    · rw [he,D.shiftedResidue_period]
    · have hzero := D.forbiddenStart_tail_zero r j' c hc hj'
      have hzero' := D.forbiddenStart_tail_zero r j c hc (by omega)
      constructor
      · rw [hzero,hzero']
      · change c.2+D.carry r j'≤c.2+D.carry r j
        rw [he,D.carry_period]
        omega

/-- Exact finite stopping equality for T_s, still defined independently
by all long-side points and all positive j. -/
theorem competitorFiber_stopping (s : Fin D.u) (p : ℕ×ℕ) : p∈D.competitorFiber s ↔
    ∃ r : Fin D.u,∃ j : ℕ,1≤j ∧ j≤(D.u-2)/2+D.u/Nat.gcd D.m D.u ∧
      ∃ c : ℕ×ℕ,Minimal (·∈D.coreFiber r) c ∧
        D.shiftedResidue r j=s ∧ D.forbiddenStart r j c≤p := by
  constructor
  · rintro ⟨r,j,hj,c,hc,hs,hstart⟩
    obtain ⟨b,hbc,hb⟩ := D.exists_minimalFiber_le r c hc
    obtain ⟨j',hj',hbound,hres,hle⟩ := D.forbiddenStart_stopping r j b hj hb
    exact ⟨r,j',hj',hbound,b,hb,hres.trans hs,
      hle.trans ((D.forbiddenStart_mono r j hbc).trans hstart)⟩
  · rintro ⟨r,j,hj,_,c,hc,hs,hstart⟩
    exact ⟨r,j,hj,c,hc.prop,hs,hstart⟩
end NSP14.Endpoint.Data
