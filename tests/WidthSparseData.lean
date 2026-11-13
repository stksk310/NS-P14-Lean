module
public import NSP14.Endpoint.Data
@[expose] public section
open NSP14
namespace Run18SparseAcceptance

def six : Endpoint.Data where
  m := 12
  d := 1
  u := 10
  a := {1,2,8,9}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide

def seven : Endpoint.Data where
  m := 14
  d := 1
  u := 12
  a := {1,2,3,4,5}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide

def eight : Endpoint.Data where
  m := 16
  d := 1
  u := 14
  a := {1,2,3,4,5,6}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide

def nine : Endpoint.Data where
  m := 18
  d := 1
  u := 16
  a := {1,2,3,4,5,6,7}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide

def ten : Endpoint.Data where
  m := 20
  d := 1
  u := 18
  a := {1,2,3,4,5,6,7,8}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide

def dilated : Endpoint.Data where
  m := 32
  d := 3
  u := 10
  a := {1,2,8,9}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
end Run18SparseAcceptance
