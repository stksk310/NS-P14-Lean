module
public import NSP14.Endpoint.Stopping
public import NSP14.Endpoint.ActualKernel
public import NSP14.Endpoint.MinimalBounds
@[expose] public section
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)
example (s : Fin D.u) (p : ℕ×ℕ) : p∈D.competitorFiber s ↔
    ∃ r : Fin D.u,∃ j : ℕ,1≤j ∧ j≤(D.u-2)/2+D.u/Nat.gcd D.m D.u ∧
      ∃ c : ℕ×ℕ,Minimal (·∈D.coreFiber r) c ∧
        D.shiftedResidue r j=s ∧ D.forbiddenStart r j c≤p := D.competitorFiber_stopping s p
end NSP14.Endpoint.Data
