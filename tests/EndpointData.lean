module
public import NSP14
@[expose] public section
namespace EndpointDataAcceptance
open NSP14

def noncoprime_endpoints : Endpoint.Data where
  m := 6
  d := 1
  u := 4
  a := {1,3}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide

def dilated_wide : Endpoint.Data where
  m := 7
  d := 2
  u := 4
  a := {1,3}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide

theorem original_multiplicity : noncoprime_endpoints.source.multiplicity=6 :=
  noncoprime_endpoints.multiplicity

theorem original_embedding : noncoprime_endpoints.source.embeddingDimension=4 := by
  rw [noncoprime_endpoints.embeddingDimension]
  decide

theorem du_ge_m_allowed : dilated_wide.source.width=8 := by
  rw [dilated_wide.width]
  rfl

theorem raw_source_minimal (D : Endpoint.Data) : D.source.atoms=D.generators := D.atoms
end EndpointDataAcceptance

namespace EndpointDataAcceptance
open NSP14

theorem enough_residues (D : Endpoint.Data) : D.q+1≤D.u := D.q_add_one_le_u

theorem sorted_internal (D : Endpoint.Data) : StrictMono D.internalOffset := D.internalOffset_strictMono
end EndpointDataAcceptance
