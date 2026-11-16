module
public import NSP14.Endpoint.FiniteMinima
public import NSP14.Endpoint.Stopping
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Endpoint.Data
variable (D : Data)

def competitorTest (s : Fin D.u) (p : ℕ×ℕ) : Prop :=
  ∃ r : Fin D.u,∃ j∈Finset.range ((D.u-2)/2+D.u/Nat.gcd D.m D.u+1),1≤j ∧
    ∃ c∈D.computedMinima r,D.shiftedResidue r j=s ∧ D.forbiddenStart r j c≤p
instance competitorTestDecidable (s : Fin D.u) (p : ℕ×ℕ) : Decidable (D.competitorTest s p) :=
  inferInstanceAs (Decidable (∃ _r : Fin D.u,∃ j∈_,_))

theorem competitorTest_iff (s : Fin D.u) (p : ℕ×ℕ) : D.competitorTest s p ↔ p∈D.competitorFiber s := by
  rw [D.competitorFiber_stopping]
  simp only [competitorTest,Finset.mem_range,D.computedMinima_iff]
  constructor
  · rintro ⟨r,j,hj,hpos,c,hc,hs,hle⟩
    exact ⟨r,j,hpos,by omega,c,hc,hs,hle⟩
  · rintro ⟨r,j,hpos,hj,c,hc,hs,hle⟩
    exact ⟨r,j,by omega,hpos,c,hc,hs,hle⟩
end NSP14.Endpoint.Data
