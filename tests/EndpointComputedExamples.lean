module
public import NSP14.Endpoint.FiniteSocleWindow
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
set_option maxRecDepth 4096
namespace EndpointComputedAcceptance
open NSP14

def A : Endpoint.Data where
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

def B : Endpoint.Data where
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

def C : Endpoint.Data where
  m := 7
  d := 1
  u := 6
  a := {1,5}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide

variable (k : Type) [Field k]
theorem A_PC : A.coreP k=5 := by rw [A.coreP_computed];decide
theorem B_PC : B.coreP k=5 := by rw [B.coreP_computed];decide
theorem C_PC : C.coreP k=9 := by rw [C.coreP_computed];decide
theorem A_PG : A.actualP k=4 := by rw [A.actualP_computed];decide
theorem B_PG : B.actualP k=5 := by rw [B.actualP_computed];decide
theorem C_PG : C.actualP k=6 := by rw [C.actualP_computed];decide
theorem A_R : A.actualR k=0 := by rw [A.actualR_computed];decide
theorem B_R : B.actualR k=0 := by rw [B.actualR_computed];decide
theorem C_competitor_cap (r : Fin C.u) : (0,2)∈C.competitorFiber r := by
  rw [←C.competitorTest_iff]
  fin_cases r <;> decide
theorem C_R : C.actualR k=1 := by rw [C.actualR_computed_window k 2 C_competitor_cap];decide
theorem EndpointComputedExamples_acceptance_001 : C.coreP (ZMod 2)=9 ∧ C.actualP (ZMod 2)=6 ∧ C.actualR (ZMod 2)=1 :=
  ⟨C_PC (ZMod 2),C_PG (ZMod 2),C_R (ZMod 2)⟩
end EndpointComputedAcceptance
