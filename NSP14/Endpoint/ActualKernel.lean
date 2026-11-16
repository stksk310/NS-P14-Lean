module
public import NSP14.Endpoint.Carry
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

/-- All long-side points and all positive competitors. Finite minimal
lists and stopping will be derived, rather than assumed in this set. -/
def competitorFiber (s : Fin D.u) : Set (ℕ×ℕ) :=
  {p | ∃ r : Fin D.u,∃ j : ℕ,1≤j ∧ ∃ c : ℕ×ℕ,c∈D.coreFiber r ∧
    D.shiftedResidue r j=s ∧ D.forbiddenStart r j c≤p}

/-- The real order test on the same actual numerical source. -/
def actualDeadFiber (s : Fin D.u) : Set (ℕ×ℕ) :=
  {c | c∈D.coreFiber s ∧ (D.decodeCoordinate (s,c)).1<
    D.source.order ((D.decodeCoordinate (s,c)).1*D.m+(D.decodeCoordinate (s,c)).2*D.d)}

theorem competitorFiber_upward (s : Fin D.u) {a b : ℕ×ℕ}
    (ha : a∈D.competitorFiber s) (hab : a≤b) : b∈D.competitorFiber s := by
  obtain ⟨r,j,hj,c,hc,hs,hstart⟩ := ha
  exact ⟨r,j,hj,c,hc,hs,hstart.trans hab⟩

theorem actual_dead_iff_forbidden (s : Fin D.u) (c : ℕ×ℕ) (hc : c∈D.coreFiber s) :
    (D.decodeCoordinate (s,c)).1<
      D.source.order ((D.decodeCoordinate (s,c)).1*D.m+(D.decodeCoordinate (s,c)).2*D.d) ↔
        c∈D.competitorFiber s := by
  let p : D.corePoints := ⟨D.decodeCoordinate (s,c),hc⟩
  change D.coreDegree p<D.source.order (D.coreValue p).val ↔ _
  constructor
  · intro hdead
    obtain ⟨j,hj,q,hdeg,hoff⟩ := (D.core_dead_iff_competitor p).mp hdead
    let g := D.coreCoordinates q
    let r := g.1
    let L := g.2.1
    let K := g.2.2
    have hqcoord : D.decodeCoordinate (r,(L,K))=q.val := D.decode_coreCoordinates q
    have hnq : L+K+D.epsilon r=D.coreDegree q := congrArg Prod.fst hqcoord
    have hBq : r.val+D.u*K=D.coreOffset q := congrArg Prod.snd hqcoord
    change D.coreDegree q=c.1+c.2+D.epsilon s+j*D.d at hdeg
    change s.val+D.u*c.2=D.coreOffset q+j*D.m at hoff
    have hnum : r.val+j*D.m+D.u*K=s.val+D.u*c.2 := by omega
    have hs : D.shiftedResidue r j=s := by
      apply Fin.ext
      have hmod := congrArg (fun n => n%D.u) hnum
      change (r.val+j*D.m)%D.u=s.val
      simpa only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt s.isLt] using hmod
    have hb : c.2=K+D.carry r j := by
      have hcar := D.carry_eq r j
      rw [hs] at hcar
      apply Nat.eq_of_mul_eq_mul_left D.u_pos
      nlinarith only [hnum,hcar]
    refine ⟨r,j,hj,(L,K),?_,hs,?_⟩
    · change D.decodeCoordinate (r,(L,K))∈D.corePoints
      rw [hqcoord]
      exact q.property
    · apply (D.forbiddenStart_le r j (L,K) c).mpr
      rw [hs]
      constructor <;> dsimp only
      · omega
      · omega
  · rintro ⟨r,j,hj,⟨L,K⟩,hM,hs,hstart⟩
    have hstarts := (D.forbiddenStart_le r j (L,K) c).mp hstart
    rw [hs] at hstarts
    have hε := D.epsilon_le_one r
    have hcarry := D.carry_pos r j hj
    let A := c.1+j*D.d+D.carry r j+D.epsilon s-D.epsilon r
    let B := c.2-D.carry r j
    have hA : A+D.epsilon r=c.1+j*D.d+D.carry r j+D.epsilon s :=
      Nat.sub_add_cancel (by omega)
    have hB : B+D.carry r j=c.2 := Nat.sub_add_cancel (by omega)
    have hMr : (A,B)∈D.coreFiber r := D.coreFiber_upward r hM ⟨by omega,by omega⟩
    let q : D.corePoints := ⟨D.decodeCoordinate (r,(A,B)),hMr⟩
    apply (D.core_dead_iff_competitor p).mpr
    refine ⟨j,hj,q,?_,?_⟩
    · change A+B+D.epsilon r=c.1+c.2+D.epsilon s+j*D.d
      omega
    · change s.val+D.u*c.2=r.val+D.u*B+j*D.m
      have hcar := D.carry_eq r j
      rw [hs] at hcar
      rw [← hB]
      nlinarith only [hcar]

/-- The exact actual kernel condition is M intersect T; the competitor
region alone is not the core or the kernel. -/
theorem actualDeadFiber_eq_inter (s : Fin D.u) :
    D.actualDeadFiber s=D.coreFiber s∩D.competitorFiber s := by
  ext c
  constructor
  · rintro ⟨hc,hdead⟩
    exact ⟨hc,(D.actual_dead_iff_forbidden s c hc).mp hdead⟩
  · rintro ⟨hc,hforbidden⟩
    exact ⟨hc,(D.actual_dead_iff_forbidden s c hc).mpr hforbidden⟩
end NSP14.Endpoint.Data
