module
public import NSP14.Endpoint.SoclePoints
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Endpoint.Data
variable (D : Data)

abbrev CoreSocleIndex := {p : D.corePoints //
  D.coreDegree p=D.source.order (D.coreValue p).val ∧
    ∀ i : Fin 2,D.coreDegree (p+D.coreGeneratorPoint (D.endpointVariable i)) <
      D.source.order (D.coreValue (p+D.coreGeneratorPoint (D.endpointVariable i))).val}

theorem endpoint_survives_core (p : D.corePoints)
    (hp : D.coreDegree p=D.source.order (D.coreValue p).val) (i : Fin 2) :
    D.source.survivesBy (D.endpointExponent i) (D.coreValue p) ↔
      D.coreDegree (p+D.coreGeneratorPoint (D.endpointVariable i))=
        D.source.order (D.coreValue (p+D.coreGeneratorPoint (D.endpointVariable i))).val := by
  change D.source.order (D.coreValue p+D.coreValue (D.coreGeneratorPoint (D.endpointVariable i))).val=
    D.source.order (D.coreValue p).val+D.source.order (D.endpointExponent i).val ↔ _
  rw [D.endpointExponent_order,←(D.coreValue).map_add,←hp,(D.coreDegree).map_add]
  change D.source.order (D.coreValue (p+D.coreGeneratorPoint (D.endpointVariable i))).val=D.coreDegree p+1 ↔
    D.coreDegree p+1=D.source.order (D.coreValue (p+D.coreGeneratorPoint (D.endpointVariable i))).val
  exact eq_comm

theorem endpoint_dead_core (p : D.corePoints)
    (hp : D.coreDegree p=D.source.order (D.coreValue p).val) (i : Fin 2) :
    ¬D.source.survivesBy (D.endpointExponent i) (D.coreValue p) ↔
      D.coreDegree (p+D.coreGeneratorPoint (D.endpointVariable i)) <
        D.source.order (D.coreValue (p+D.coreGeneratorPoint (D.endpointVariable i))).val := by
  rw [D.endpoint_survives_core p hp i]
  have := D.coreDegree_le_order (p+D.coreGeneratorPoint (D.endpointVariable i))
  omega

noncomputable def coreSocleExponentEquiv : D.CoreSocleIndex ≃ D.EndpointSocleExponent :=
  Equiv.ofBijective (fun p => ⟨D.coreValue p.val,
    (D.endpoint_dead_core p.val p.property.1 0).mpr (p.property.2 0),
    (D.endpoint_dead_core p.val p.property.1 1).mpr (p.property.2 1)⟩) ⟨by
      intro p q h
      exact Subtype.ext (D.liveValue_injective p.val q.val p.property.1 q.property.1 (congrArg Subtype.val h)),by
      intro a
      obtain ⟨p,hp,hv⟩ := D.exists_corePoint a.val
      have hl : D.coreDegree p=D.source.order (D.coreValue p).val := by rw [hv];exact hp
      have hd (i : Fin 2) : D.coreDegree (p+D.coreGeneratorPoint (D.endpointVariable i)) <
          D.source.order (D.coreValue (p+D.coreGeneratorPoint (D.endpointVariable i))).val := by
        apply (D.endpoint_dead_core p hl i).mp
        rw [hv]
        fin_cases i
        · exact a.property.1
        · exact a.property.2
      exact ⟨⟨p,hl,hd⟩,Subtype.ext hv⟩⟩

variable (k : Type) [Field k]
theorem actualR_core_count : D.actualR k=Nat.card D.CoreSocleIndex :=
  (D.actualR_exponent_count k).trans (Nat.card_congr D.coreSocleExponentEquiv).symm
end NSP14.Endpoint.Data
