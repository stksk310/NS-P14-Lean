module
public import NSP14.Endpoint.FiniteMinima
@[expose] public section
set_option maxRecDepth 4096
namespace EndpointOrientationAcceptance
open NSP14

def left : Endpoint.Data where
  m := 8
  d := 1
  u := 5
  a := {1,2}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide

def reflected : Endpoint.Data where
  m := 8
  d := 1
  u := 5
  a := {3,4}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
theorem EndpointOrientation_acceptance_001 : left.coreHeight=1 := by rw [left.coreHeight_computed];decide
theorem EndpointOrientation_acceptance_002 : reflected.coreHeight=0 := by rw [reflected.coreHeight_computed];decide
theorem EndpointOrientation_acceptance_003 : left.coreHeight≠reflected.coreHeight := by
  have hl : left.coreHeight=1 := by rw [left.coreHeight_computed];decide
  have hr : reflected.coreHeight=0 := by rw [reflected.coreHeight_computed];decide
  omega
end EndpointOrientationAcceptance
