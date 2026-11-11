module
public import NSP14.Endpoint.FiniteMinima
public import NSP14.Endpoint.Stopping
@[expose] public section
set_option maxRecDepth 4096
namespace EndpointBoundaryAcceptance
open NSP14

def minimal : Endpoint.Data where
  m := 6
  d := 1
  u := 3
  a := {1,2}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide

def heightTwo : Endpoint.Data where
  m := 6
  d := 1
  u := 5
  a := {1,4}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
theorem EndpointBoundaryExamples_acceptance_001 : minimal.coreHeight=0 := by rw [minimal.coreHeight_computed];decide
theorem EndpointBoundaryExamples_acceptance_002 : heightTwo.coreHeight=2 := by rw [heightTwo.coreHeight_computed];decide
theorem EndpointBoundaryExamples_acceptance_003 : minimal.carryPeriod=1 := by decide
theorem EndpointBoundaryExamples_acceptance_004 : minimal.u∣minimal.m := by decide
theorem EndpointBoundaryExamples_acceptance_005 : heightTwo.stoppingStart=1 := by decide
theorem EndpointBoundaryExamples_acceptance_006 : heightTwo.carryPeriod=5 := by decide
theorem EndpointBoundaryExamples_acceptance_007 (r : Fin heightTwo.u) (c : ℕ×ℕ) (hc : Minimal (·∈heightTwo.coreFiber r) c) :
    (heightTwo.forbiddenStart r 2 c).1=0 := heightTwo.forbiddenStart_tail_zero r 2 c hc (by decide)
theorem EndpointBoundaryExamples_acceptance_008 (r : Fin heightTwo.u) (c : ℕ×ℕ) (hc : Minimal (·∈heightTwo.coreFiber r) c) :
    ∃ j,1≤j ∧ j≤heightTwo.stoppingStart+heightTwo.carryPeriod ∧
      heightTwo.shiftedResidue r j=heightTwo.shiftedResidue r 11 ∧
        heightTwo.forbiddenStart r j c≤heightTwo.forbiddenStart r 11 c :=
  heightTwo.forbiddenStart_stopping r 11 c (by decide) hc
end EndpointBoundaryAcceptance
