module
public import NSP14.Endpoint.EndpointCoordinateSteps
public import NSP14.Endpoint.AdjacentCorners
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Endpoint.Data
variable (D : Data)

abbrev FiberSocleIndex (r : Fin D.u) := {c : ℕ×ℕ // c∈D.coreFiber r ∧
  NSP14.Endpoint.Corner (D.actualDeadFiber r) c}

theorem core_socle_corner (p : D.corePoints) :
    (D.coreDegree p=D.source.order (D.coreValue p).val ∧
      ∀ i : Fin 2,D.coreDegree (p+D.coreGeneratorPoint (D.endpointVariable i)) <
        D.source.order (D.coreValue (p+D.coreGeneratorPoint (D.endpointVariable i))).val) ↔
    NSP14.Endpoint.Corner (D.actualDeadFiber (D.coreCoordinates p).1) (D.coreCoordinates p).2 := by
  have h0 := D.core_dead_coordinate (p+D.coreGeneratorPoint D.xVariable)
  have h1 := D.core_dead_coordinate (p+D.coreGeneratorPoint D.vVariable)
  rw [D.coreCoordinates_endpoint_x] at h0
  rw [D.coreCoordinates_endpoint_v] at h1
  have hp := D.core_dead_coordinate p
  have hle := D.coreDegree_le_order p
  constructor
  · intro h
    exact ⟨fun hd => (by omega : ¬D.coreDegree p<D.source.order (D.coreValue p).val) (hp.mp hd),
      h0.mpr (h.2 0),h1.mpr (h.2 1)⟩
  · intro h
    refine ⟨by have hn : ¬D.coreDegree p<D.source.order (D.coreValue p).val := fun hd => h.1 (hp.mpr hd);omega,?_⟩
    intro i
    fin_cases i
    · exact h0.mp h.2.1
    · exact h1.mp h.2.2

noncomputable def coreSocleFiberEquiv : D.CoreSocleIndex ≃ (Σ r : Fin D.u,D.FiberSocleIndex r) where
  toFun p := ⟨(D.coreCoordinates p.val).1,⟨(D.coreCoordinates p.val).2,
    D.coordinate_mem_fiber p.val,(D.core_socle_corner p.val).mp p.property⟩⟩
  invFun c := ⟨⟨D.decodeCoordinate (c.1,c.2.val),c.2.property.1⟩,
    (D.core_socle_corner _).mpr (by rw [D.coreCoordinates_decode];exact c.2.property.2)⟩
  left_inv p := by
    apply Subtype.ext
    exact Subtype.ext (D.decode_coreCoordinates p.val)
  right_inv c := by
    rcases c with ⟨r,c,hc⟩
    have he := D.coreCoordinates_decode r c hc.1
    exact Sigma.subtype_ext (congrArg Prod.fst he) (congrArg Prod.snd he)

variable (k : Type) [Field k]
/-- Exact point count for the actual R: all and only core points outside
N whose two endpoint neighbours lie in N. No Artin assumption on E/N. -/
theorem actualR_corner_count : D.actualR k=Nat.card (Σ r : Fin D.u,D.FiberSocleIndex r) :=
  (D.actualR_core_count k).trans (Nat.card_congr D.coreSocleFiberEquiv)

noncomputable def actualSocleCornerCoordinates : D.actualSocle k ≃ₗ[k]
    ((Σ r : Fin D.u,D.FiberSocleIndex r) →₀ k) :=
  (D.actualSocleCoordinates k).trans
    (Finsupp.domLCongr (D.coreSocleExponentEquiv.symm.trans D.coreSocleFiberEquiv))
end NSP14.Endpoint.Data
namespace NSP14.Endpoint.Data
open scoped Classical
variable (D : Data)

theorem fiberSocle_adjacent (r : Fin D.u) (c : D.FiberSocleIndex r) :
    ∃ a b : ℕ×ℕ,NSP14.Endpoint.AdjacentMinima (D.actualDeadFiber r) a b ∧ c.val=(b.1-1,a.2-1) := by
  let z : {c : ℕ×ℕ // NSP14.Endpoint.Corner (D.actualDeadFiber r) c} := ⟨c.val,c.property.2⟩
  exact ⟨(NSP14.Endpoint.cornerAbove _ z).val,(NSP14.Endpoint.cornerRight _ z).val,
    NSP14.Endpoint.corner_adjacent _ (D.actualDeadFiber_upward r) z,
    NSP14.Endpoint.corner_adjacent_formula _ (D.actualDeadFiber_upward r) z⟩

instance coreSocleIndexFinite : Finite D.CoreSocleIndex :=
  Finite.of_equiv D.EndpointSocleExponent D.coreSocleExponentEquiv.symm
instance fiberSocleSigmaFinite : Finite (Σ r : Fin D.u,D.FiberSocleIndex r) :=
  Finite.of_equiv D.CoreSocleIndex D.coreSocleFiberEquiv
instance fiberSocleFinite (r : Fin D.u) : Finite (D.FiberSocleIndex r) :=
  Finite.of_injective (fun c : D.FiberSocleIndex r => (⟨r,c⟩ : Σ s,D.FiberSocleIndex s))
    (by intro a b h;exact eq_of_heq ((Sigma.mk.inj_iff.mp h).2))

variable (k : Type) [Field k]
theorem actualR_corner_sum : D.actualR k=∑ r : Fin D.u,Nat.card (D.FiberSocleIndex r) := by
  rw [D.actualR_corner_count,Nat.card_sigma]
end NSP14.Endpoint.Data
