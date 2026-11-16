module
public import NSP14.Endpoint.FiniteSurvivors
public import NSP14.Endpoint.FiniteSocleBounds
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Endpoint.Data
variable (D : Data)

def coordinateValue (r : Fin D.u) (c : ℕ×ℕ) : ℕ :=
  (c.1+c.2+D.epsilon r)*D.m+(r.val+D.u*c.2)*D.d

def coordinateSocleTest (r : Fin D.u) (c : ℕ×ℕ) : Prop :=
  c.1+c.2+D.epsilon r=D.computedOrder (D.coordinateValue r c) ∧
    c.1+c.2+D.epsilon r+1 < D.computedOrder (D.coordinateValue r c+D.m) ∧
    c.1+c.2+D.epsilon r+1 < D.computedOrder (D.coordinateValue r c+D.m+D.u*D.d)
instance coordinateSocleTestDecidable (r : Fin D.u) (c : ℕ×ℕ) : Decidable (D.coordinateSocleTest r c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem coordinateSocleTest_iff (r : Fin D.u) (c : ℕ×ℕ) (hc : c∈D.coreFiber r) :
    D.coordinateSocleTest r c ↔ NSP14.Endpoint.Corner (D.actualDeadFiber r) c := by
  let p : D.corePoints := ⟨D.decodeCoordinate (r,c),hc⟩
  have hv0 : (D.coreValue p).val=D.coordinateValue r c := rfl
  have hv1 : (D.coreValue (p+D.coreGeneratorPoint D.xVariable)).val=D.coordinateValue r c+D.m := by
    change (c.1+c.2+D.epsilon r+1)*D.m+(r.val+D.u*c.2+0)*D.d=_
    dsimp [coordinateValue]
    ring
  have hv2 : (D.coreValue (p+D.coreGeneratorPoint D.vVariable)).val=D.coordinateValue r c+D.m+D.u*D.d := by
    change (c.1+c.2+D.epsilon r+1)*D.m+(r.val+D.u*c.2+D.u)*D.d=_
    dsimp [coordinateValue]
    ring
  have he0 := D.computedOrder_eq (D.coreValue p)
  have he1 := D.computedOrder_eq (D.coreValue (p+D.coreGeneratorPoint D.xVariable))
  have he2 := D.computedOrder_eq (D.coreValue (p+D.coreGeneratorPoint D.vVariable))
  rw [hv0] at he0
  rw [hv1] at he1
  rw [hv2] at he2
  rw [coordinateSocleTest,he0,he1,he2]
  have hcorner := D.core_socle_corner p
  rw [D.coreCoordinates_decode] at hcorner
  rw [←hcorner]
  change (_ ∧ _ ∧ _) ↔ (_ ∧ ∀ i : Fin 2,_)
  constructor
  · rintro ⟨hl,hx,hv⟩
    refine ⟨hl,?_⟩
    intro i
    fin_cases i
    · change c.1+c.2+D.epsilon r+1<D.source.order (D.coreValue (p+D.coreGeneratorPoint D.xVariable)).val
      rw [hv1]
      exact hx
    · change c.1+c.2+D.epsilon r+1<D.source.order (D.coreValue (p+D.coreGeneratorPoint D.vVariable)).val
      rw [hv2]
      exact hv
  · rintro ⟨hl,hd⟩
    have hx := hd 0
    have hv := hd 1
    change c.1+c.2+D.epsilon r+1<D.source.order (D.coreValue (p+D.coreGeneratorPoint D.xVariable)).val at hx
    change c.1+c.2+D.epsilon r+1<D.source.order (D.coreValue (p+D.coreGeneratorPoint D.vVariable)).val at hv
    rw [hv1] at hx
    rw [hv2] at hv
    exact ⟨hl,hx,hv⟩

def computedSocle (r : Fin D.u) : Finset (ℕ×ℕ) :=
  ((Finset.range (D.computedCoreHeight-2)).product (Finset.range (D.m+D.u))).filter
    (fun c => D.coreCoordinateTest r c ∧ D.coordinateSocleTest r c)

theorem computedSocle_iff (r : Fin D.u) (c : ℕ×ℕ) : c∈D.computedSocle r ↔
    c∈D.coreFiber r ∧ NSP14.Endpoint.Corner (D.actualDeadFiber r) c := by
  have hprod : c∈(Finset.range (D.computedCoreHeight-2)).product (Finset.range (D.m+D.u)) ↔ c.1<D.computedCoreHeight-2 ∧ c.2<D.m+D.u :=
    Finset.mem_product.trans (and_congr Finset.mem_range Finset.mem_range)
  rw [computedSocle,Finset.mem_filter,hprod,D.coreCoordinateTest_iff]
  constructor
  · rintro ⟨_,hc,ht⟩
    exact ⟨hc,(D.coordinateSocleTest_iff r c hc).mp ht⟩
  · intro hc
    exact ⟨⟨by rw [←D.coreHeight_computed];exact D.fiberSocle_horizontal r ⟨c,hc⟩,
      (D.fiberSocle_rectangle r ⟨c,hc⟩).2⟩,hc.1,(D.coordinateSocleTest_iff r c hc.1).mpr hc.2⟩

variable (k : Type) [Field k]
theorem actualR_computed : D.actualR k=∑ r : Fin D.u,(D.computedSocle r).card := by
  rw [D.actualR_corner_sum]
  apply Finset.sum_congr rfl
  intro r _
  calc
    Nat.card (D.FiberSocleIndex r)=Nat.card {c : ℕ×ℕ // c∈D.computedSocle r} :=
      Nat.card_congr (Equiv.subtypeEquivRight (D.computedSocle_iff r) |>.symm)
    _=(D.computedSocle r).card := by rw [Nat.card_eq_fintype_card];exact Fintype.card_coe _
end NSP14.Endpoint.Data
