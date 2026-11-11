module
public import NSP14.Endpoint.FiniteWords
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Endpoint.Data
variable (D : Data)

def coreCoordinateTest (r : Fin D.u) (c : ℕ×ℕ) : Prop :=
  r.val+D.u*c.2∈D.offsetSums (c.1+c.2+D.epsilon r)
instance coreCoordinateTestDecidable (r : Fin D.u) (c : ℕ×ℕ) : Decidable (D.coreCoordinateTest r c) :=
  inferInstanceAs (Decidable (_∈_))

theorem coreCoordinateTest_iff (r : Fin D.u) (c : ℕ×ℕ) : D.coreCoordinateTest r c ↔ c∈D.coreFiber r :=
  (D.corePoint_iff_offsetSums _ _).symm

def computedMinima (r : Fin D.u) : Finset (ℕ×ℕ) :=
  ((Finset.range D.u).product (Finset.range D.u)).filter (fun c =>
    D.coreCoordinateTest r c ∧ (c.1=0 ∨ ¬D.coreCoordinateTest r (c.1-1,c.2)) ∧
      (c.2=0 ∨ ¬D.coreCoordinateTest r (c.1,c.2-1)))

theorem computedMinima_iff (r : Fin D.u) (c : ℕ×ℕ) :
    c∈D.computedMinima r ↔ Minimal (·∈D.coreFiber r) c := by
  have hprod : c∈(Finset.range D.u).product (Finset.range D.u) ↔ c.1<D.u ∧ c.2<D.u := by
    exact Finset.mem_product.trans (and_congr Finset.mem_range Finset.mem_range)
  rw [computedMinima,Finset.mem_filter,hprod]
  simp only [D.coreCoordinateTest_iff]
  constructor
  · rintro ⟨_,hc,hx,hv⟩
    exact (D.minimalFiber_iff_predecessors r c hc).mpr ⟨hx,hv⟩
  · intro hc
    have hb := D.minimalFiber_budget r c hc
    have hp := (D.minimalFiber_iff_predecessors r c hc.prop).mp hc
    have hu := D.u_pos
    exact ⟨⟨by omega,by omega⟩,hc.prop,hp⟩

theorem computedMinima_eq (r : Fin D.u) : D.computedMinima r=D.minimalPoints r := by
  ext c
  rw [D.computedMinima_iff,D.mem_minimalPoints]

def computedCoreHeight : ℕ := Finset.univ.sup
  (fun r : Fin D.u => (D.computedMinima r).sup Prod.fst)

variable (k : Type) [Field k]
theorem coreP_computed : D.coreP k=∑ r : Fin D.u,(D.computedMinima r).card := by
  simp only [D.computedMinima_eq,D.coreP_minimalCount]

theorem coreHeight_computed : D.coreHeight=D.computedCoreHeight := by
  simp only [computedCoreHeight,D.computedMinima_eq,coreHeight]
end NSP14.Endpoint.Data
