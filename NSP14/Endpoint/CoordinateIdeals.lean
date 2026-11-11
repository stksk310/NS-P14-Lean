module
public import Mathlib.RingTheory.MvPolynomial.Ideal
@[expose] public section
namespace NSP14.Endpoint
variable (k : Type) [Field k]

/-- The actual polynomial ideal of an upper set of endpoint exponents. -/
noncomputable def coordinateIdeal (U : Set (ℕ×ℕ)) : Ideal (MvPolynomial (Fin 2) k) :=
  Ideal.span ((fun b => MvPolynomial.monomial b (1:k)) '' {b : Fin 2 →₀ ℕ | (b 0,b 1)∈U})

theorem coordinateIdeal_mem (U : Set (ℕ×ℕ))
    (hU : ∀ {a b},a∈U → a≤b → b∈U) (f : MvPolynomial (Fin 2) k) :
    f∈coordinateIdeal k U ↔ ∀ b∈f.support,(b 0,b 1)∈U := by
  rw [coordinateIdeal,MvPolynomial.mem_ideal_span_monomial_image]
  constructor
  · intro h b hb
    obtain ⟨c,hc,hcb⟩ := h b hb
    exact hU hc ⟨hcb 0,hcb 1⟩
  · intro h b hb
    exact ⟨b,h b hb,le_rfl⟩

theorem coordinateIdeal_inter (U V : Set (ℕ×ℕ))
    (hU : ∀ {a b},a∈U → a≤b → b∈U) (hV : ∀ {a b},a∈V → a≤b → b∈V) :
    coordinateIdeal k (U∩V)=coordinateIdeal k U⊓coordinateIdeal k V := by
  ext f
  rw [coordinateIdeal_mem k (U∩V) (fun h hab => ⟨hU h.1 hab,hV h.2 hab⟩),
    Ideal.mem_inf,coordinateIdeal_mem k U hU,coordinateIdeal_mem k V hV]
  constructor
  · intro h
    exact ⟨fun b hb => (h b hb).1,fun b hb => (h b hb).2⟩
  · rintro ⟨h1,h2⟩
    exact fun b hb => ⟨h1 b hb,h2 b hb⟩
end NSP14.Endpoint
