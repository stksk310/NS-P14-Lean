module
public import NSP14.Endpoint.Data
public import Mathlib.Data.Finset.Sort
@[expose] public section
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

theorem q_add_one_le_u : D.q+1≤D.u := by
  have hs : D.offsets⊆Finset.range (D.u+1) := by
    intro b hb
    apply Finset.mem_range.mpr
    have := D.offset_le hb
    omega
  have h := Finset.card_le_card hs
  rw [D.offsets_card,Finset.card_range] at h
  omega

noncomputable def internalOffset : Fin D.q → ℕ := D.a.orderEmbOfFin rfl

theorem internalOffset_strictMono : StrictMono D.internalOffset := (D.a.orderEmbOfFin rfl).strictMono

theorem internalOffset_mem (i : Fin D.q) : D.internalOffset i∈D.a := Finset.orderEmbOfFin_mem _ _ i

theorem internalOffset_pos (i : Fin D.q) : 0 < D.internalOffset i := D.a_pos _ (D.internalOffset_mem i)

theorem internalOffset_lt (i : Fin D.q) : D.internalOffset i<D.u := D.a_lt _ (D.internalOffset_mem i)
end NSP14.Endpoint.Data
