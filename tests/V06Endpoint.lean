module
public import NSP14.Endpoint.CompetitorBounds
public import NSP14.Endpoint.FiniteSocleBounds
-- The finite computational branch intentionally retains its stopping theorem.
public import NSP14.Endpoint.FiniteCompetitors
@[expose] public section
namespace V06EndpointAcceptance
open NSP14

variable (D : Endpoint.Data)

/-- The actual competitor set still quantifies over every positive length. -/
theorem all_positive_lengths (s : Fin D.u) (p : ℕ×ℕ) :
    p∈D.competitorFiber s ↔
      ∃ r : Fin D.u,∃ j : ℕ,1≤j ∧ ∃ c : ℕ×ℕ,c∈D.coreFiber r ∧
        D.shiftedResidue r j=s ∧ D.forbiddenStart r j c≤p := Iff.rfl

theorem unrestricted_witness (r : Fin D.u) (j : ℕ) (hj : 1≤j)
    (c : ℕ×ℕ) (hc : c∈D.coreFiber r) :
    D.forbiddenStart r j c∈D.competitorFiber (D.shiftedResidue r j) :=
  ⟨r,j,hj,c,hc,rfl,le_rfl⟩

theorem minimal_height (s : Fin D.u) (c : ℕ×ℕ)
    (hc : Minimal (·∈D.competitorFiber s) c) :
    c.1≤D.coreHeight-2 := D.competitorMin_height s c hc

theorem minimal_finite (s : Fin D.u) :
    Set.Finite {c | Minimal (·∈D.competitorFiber s) c} := D.competitorMin_finite s

theorem pure_v_power (s : Fin D.u) :
    (0,D.m+D.u)∈D.competitorFiber s := D.competitor_zero_column s

theorem height_two_boundary (hH : D.coreHeight≤2) (s : Fin D.u) :
    D.competitorZ s=0 := by
  have h := D.competitorZ_height s
  omega

theorem finite_api (s : Fin D.u) (p : ℕ×ℕ) :
    D.competitorTest s p ↔ p∈D.competitorFiber s := D.competitorTest_iff s p

/-- No coprimality assumption on m and u is required by the new route. -/
def nonunit : Endpoint.Data where
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

theorem nonunit_gcd : Nat.gcd nonunit.m nonunit.u=3 := by decide

theorem length_beyond_stopping :
    (nonunit.u-2)/2+nonunit.u/Nat.gcd nonunit.m nonunit.u<37 := by decide

theorem nonunit_long_witness (r : Fin nonunit.u) :
    nonunit.forbiddenStart r 37 (nonunit.shortestPoint r)∈
      nonunit.competitorFiber (nonunit.shiftedResidue r 37) :=
  unrestricted_witness nonunit r 37 (by decide) _ (nonunit.shortestPoint_mem r)

theorem nonunit_pure_v_power (s : Fin nonunit.u) :
    (0,9)∈nonunit.competitorFiber s := nonunit.competitor_zero_column s

end V06EndpointAcceptance
