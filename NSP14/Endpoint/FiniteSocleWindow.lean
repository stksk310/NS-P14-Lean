module
public import NSP14.Endpoint.FiniteSocle
public import NSP14.Endpoint.FiniteCompetitors
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Endpoint.Data
variable (D : Data)

def computedSocleWindow (K : ℕ) (r : Fin D.u) : Finset (ℕ×ℕ) :=
  ((Finset.range (D.computedCoreHeight-2)).product (Finset.range K)).filter
    (fun c => D.coreCoordinateTest r c ∧ D.coordinateSocleTest r c)

theorem computedSocleWindow_iff (K : ℕ) (hK : ∀ r : Fin D.u,(0,K)∈D.competitorFiber r)
    (r : Fin D.u) (c : ℕ×ℕ) : c∈D.computedSocleWindow K r ↔
      c∈D.coreFiber r ∧ NSP14.Endpoint.Corner (D.actualDeadFiber r) c := by
  have hprod : c∈(Finset.range (D.computedCoreHeight-2)).product (Finset.range K) ↔
      c.1<D.computedCoreHeight-2 ∧ c.2<K := Finset.mem_product.trans (and_congr Finset.mem_range Finset.mem_range)
  rw [computedSocleWindow,Finset.mem_filter,hprod,D.coreCoordinateTest_iff]
  constructor
  · rintro ⟨_,hc,ht⟩
    exact ⟨hc,(D.coordinateSocleTest_iff r c hc).mp ht⟩
  · intro hc
    have hT : NSP14.Endpoint.Corner (D.competitorFiber r) c := D.fiberSocle_competitor_corner r ⟨c,hc⟩
    have hb : c.2<K := by
      by_contra hn
      exact hT.1 (D.competitorFiber_upward r (hK r) ⟨Nat.zero_le _,by omega⟩)
    exact ⟨⟨by rw [←D.coreHeight_computed];exact D.fiberSocle_horizontal r ⟨c,hc⟩,hb⟩,
      hc.1,(D.coordinateSocleTest_iff r c hc.1).mpr hc.2⟩

variable (k : Type) [Field k]
/-- Optional smaller executable window, certified by actual competitor
membership. It changes only the computation, never the main upper bound. -/
theorem actualR_computed_window (K : ℕ) (hK : ∀ r : Fin D.u,(0,K)∈D.competitorFiber r) :
    D.actualR k=∑ r : Fin D.u,(D.computedSocleWindow K r).card := by
  rw [D.actualR_corner_sum]
  apply Finset.sum_congr rfl
  intro r _
  calc
    Nat.card (D.FiberSocleIndex r)=Nat.card {c : ℕ×ℕ // c∈D.computedSocleWindow K r} :=
      Nat.card_congr (Equiv.subtypeEquivRight (D.computedSocleWindow_iff K hK r) |>.symm)
    _=(D.computedSocleWindow K r).card := by rw [Nat.card_eq_fintype_card];exact Fintype.card_coe _
end NSP14.Endpoint.Data
