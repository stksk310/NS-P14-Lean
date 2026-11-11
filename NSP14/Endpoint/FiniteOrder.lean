module
public import NSP14.Endpoint.FiniteMinima
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Endpoint.Data
variable (D : Data)

def lengthCandidates (x : ℕ) : Finset ℕ := (Finset.range (x/D.m+1)).filter
  (fun n => ∃ B∈D.offsetSums n,n*D.m+B*D.d=x)
def computedOrder (x : ℕ) : ℕ := (D.lengthCandidates x).sup id

theorem computedOrder_eq (x : D.source.carrier) : D.computedOrder x.val=D.source.order x.val := by
  apply le_antisymm
  · apply Finset.sup_le
    intro n hn
    obtain ⟨_,B,hB,hx⟩ := Finset.mem_filter.mp hn
    let p : D.corePoints := ⟨(n,B),D.offsetSums_core n B hB⟩
    have hv : D.coreValue p=x := Subtype.ext hx
    have h := D.coreDegree_le_order p
    rw [hv] at h
    exact h
  · obtain ⟨p,hp,hv⟩ := D.exists_corePoint x
    have hbound := D.source.order_bound x.property
    rw [D.multiplicity] at hbound
    have hm : 0<D.m := D.m_pos
    have hn : D.source.order x.val≤x.val/D.m := (Nat.le_div_iff_mul_le hm).mpr hbound
    have hmem : D.source.order x.val∈D.lengthCandidates x.val := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (by omega),D.coreOffset p,?_,?_⟩
      · rw [←hp]
        exact (D.corePoint_iff_offsetSums p.val.1 p.val.2).mp p.property
      · have he := congrArg Subtype.val hv
        change D.coreDegree p*D.m+D.coreOffset p*D.d=x.val at he
        rw [hp] at he
        exact he
    exact Finset.le_sup (f:=id) hmem

def computedSurvivors (r : Fin D.u) : Finset (ℕ×ℕ) := (D.computedMinima r).filter (fun c =>
  c.1+c.2+D.epsilon r=D.computedOrder ((c.1+c.2+D.epsilon r)*D.m+(r.val+D.u*c.2)*D.d))

theorem computedSurvivors_iff (r : Fin D.u) (c : ℕ×ℕ) : c∈D.computedSurvivors r ↔
    Minimal (·∈D.coreFiber r) c ∧ (D.decodeCoordinate (r,c)).1=
      D.source.order ((D.decodeCoordinate (r,c)).1*D.m+(D.decodeCoordinate (r,c)).2*D.d) := by
  rw [computedSurvivors,Finset.mem_filter,D.computedMinima_iff]
  constructor
  · rintro ⟨hm,hl⟩
    let p : D.corePoints := ⟨D.decodeCoordinate (r,c),hm.prop⟩
    have he := D.computedOrder_eq (D.coreValue p)
    change D.computedOrder ((c.1+c.2+D.epsilon r)*D.m+(r.val+D.u*c.2)*D.d)=_ at he
    exact ⟨hm,he ▸ hl⟩
  · rintro ⟨hm,hl⟩
    let p : D.corePoints := ⟨D.decodeCoordinate (r,c),hm.prop⟩
    have he := D.computedOrder_eq (D.coreValue p)
    exact ⟨hm,by change D.coreDegree p=D.computedOrder (D.coreValue p).val;rw [he];exact hl⟩
end NSP14.Endpoint.Data
