module
public import NSP14.Endpoint.MinimalBounds
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

theorem offsets_setGcd : Nat.setGcd (D.offsets : Set ℕ)=1 := by
  apply Nat.dvd_one.mp
  rw [←D.offsets_coprime]
  exact Nat.dvd_gcd (Finset.dvd_gcd (fun b hb =>
    Nat.setGcd_dvd_of_mem (show b∈(D.offsets : Set ℕ) by simp [hb])))
    (Nat.setGcd_dvd_of_mem (show D.u∈(D.offsets : Set ℕ) by simp))

theorem offsetClosure_core {B : ℕ} (h : B∈AddSubmonoid.closure (D.offsets : Set ℕ)) :
    ∃ p : D.corePoints,D.coreOffset p=B := by
  apply AddSubmonoid.closure_induction (motive:=fun B _ => ∃ p : D.corePoints,D.coreOffset p=B) ?_ ?_ ?_ h
  · intro b hb
    exact ⟨D.coreGeneratorPoint ⟨b,hb⟩,rfl⟩
  · exact ⟨0,rfl⟩
  · rintro b c _ _ ⟨p,hp⟩ ⟨q,hq⟩
    exact ⟨p+q,by rw [(D.coreOffset).map_add,hp,hq]⟩

/-- Every residue occurs in the genuine core, using the collective gcd
condition only. No individual internal offset is assumed invertible. -/
theorem coreFiber_nonempty (r : Fin D.u) : ∃ c : ℕ×ℕ,c∈D.coreFiber r := by
  obtain ⟨C,hC⟩ := Nat.exists_mem_closure_of_ge (D.offsets : Set ℕ)
  have hlarge : C≤r.val+D.u*C := by have := D.u_pos;nlinarith
  obtain ⟨p,hp⟩ := D.offsetClosure_core (hC (r.val+D.u*C) hlarge (by rw [D.offsets_setGcd];exact one_dvd _))
  have hr : (D.coreCoordinates p).1=r := by
    apply Fin.ext
    change D.coreOffset p%D.u=r.val
    rw [hp,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt r.isLt]
  exact ⟨(D.coreCoordinates p).2,by rw [←hr];exact D.coordinate_mem_fiber p⟩

theorem exists_residueDegree (r : Fin D.u) : ∃ n,∃ c : ℕ×ℕ,c∈D.coreFiber r ∧
    c.1+c.2+D.epsilon r=n := by
  obtain ⟨c,hc⟩ := D.coreFiber_nonempty r
  exact ⟨_,c,hc,rfl⟩

noncomputable def shortestDegree (r : Fin D.u) : ℕ := Nat.find (D.exists_residueDegree r)
noncomputable def shortestPoint (r : Fin D.u) : ℕ×ℕ := (Nat.find_spec (D.exists_residueDegree r)).choose

theorem shortestPoint_mem (r : Fin D.u) : D.shortestPoint r∈D.coreFiber r :=
  (Nat.find_spec (D.exists_residueDegree r)).choose_spec.1

theorem shortestPoint_degree (r : Fin D.u) :
    (D.shortestPoint r).1+(D.shortestPoint r).2+D.epsilon r=D.shortestDegree r :=
  (Nat.find_spec (D.exists_residueDegree r)).choose_spec.2

theorem shortestDegree_le (r : Fin D.u) (c : ℕ×ℕ) (hc : c∈D.coreFiber r) :
    D.shortestDegree r≤c.1+c.2+D.epsilon r := Nat.find_min' _ ⟨c,hc,rfl⟩

theorem shortestPoint_minimal (r : Fin D.u) : Minimal (·∈D.coreFiber r) (D.shortestPoint r) := by
  constructor
  · exact D.shortestPoint_mem r
  · intro b hb hle
    have hdeg := D.shortestDegree_le r b hb
    have he := D.shortestPoint_degree r
    exact ⟨by have := hle.1;have := hle.2;omega,by have := hle.1;have := hle.2;omega⟩

theorem shortestDegree_lt (r : Fin D.u) : D.shortestDegree r<D.u := by
  rw [←D.shortestPoint_degree r]
  exact D.minimalFiber_degree_lt r _ (D.shortestPoint_minimal r)

theorem shortestDegree_zero : D.shortestDegree ⟨0,D.u_pos⟩=0 := by
  have h := D.shortestDegree_le ⟨0,D.u_pos⟩ (0,0) (D.coreFiber_zero (0,0))
  simpa only [epsilon,ite_true,Nat.zero_add,Nat.le_zero] using h
end NSP14.Endpoint.Data
