module
public import NSP14.Endpoint.Coordinates
public import Mathlib.RingTheory.MvPolynomial.Ideal
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

def coreFiber (r : Fin D.u) : Set (ℕ×ℕ) :=
  {c | D.decodeCoordinate (r,c)∈D.corePoints}

def coreEndpointPoint (c : ℕ×ℕ) : D.corePoints :=
  c.1 • D.coreGeneratorPoint D.xVariable+c.2 • D.coreGeneratorPoint D.vVariable

theorem coreEndpointPoint_coe (c : ℕ×ℕ) : (D.coreEndpointPoint c).val=(c.1+c.2,D.u*c.2) := by
  apply Prod.ext
  · simp [coreEndpointPoint,coreGeneratorPoint,xVariable,vVariable]
  · simp [coreEndpointPoint,coreGeneratorPoint,xVariable,vVariable,mul_comm]

theorem coreFiber_add (r : Fin D.u) {a : ℕ×ℕ} (ha : a∈D.coreFiber r) (b : ℕ×ℕ) :
    (a.1+b.1,a.2+b.2)∈D.coreFiber r := by
  have h := D.corePoints.add_mem ha (D.coreEndpointPoint b).property
  rw [D.coreEndpointPoint_coe] at h
  change D.decodeCoordinate (r,(a.1+b.1,a.2+b.2))∈D.corePoints
  convert h using 1
  apply Prod.ext
  · dsimp [decodeCoordinate];ring
  · dsimp [decodeCoordinate];ring

theorem coreFiber_upward (r : Fin D.u) {a b : ℕ×ℕ} (ha : a∈D.coreFiber r) (hab : a≤b) :
    b∈D.coreFiber r := by
  have h := D.coreFiber_add r ha (b.1-a.1,b.2-a.2)
  simpa only [Nat.add_sub_of_le hab.1,Nat.add_sub_of_le hab.2] using h

theorem coreFiber_zero (c : ℕ×ℕ) : c∈D.coreFiber ⟨0,D.u_pos⟩ := by
  have h0 : (0,0)∈D.coreFiber ⟨0,D.u_pos⟩ := by
    change D.decodeCoordinate (⟨0,D.u_pos⟩,(0,0))∈D.corePoints
    rw [show D.decodeCoordinate (⟨0,D.u_pos⟩,(0,0))=0 by simp [decodeCoordinate,epsilon]]
    exact D.corePoints.zero_mem
  exact D.coreFiber_upward _ h0 ⟨Nat.zero_le _,Nat.zero_le _⟩

def coreFiberExponents (r : Fin D.u) : Set (Fin 2 →₀ ℕ) :=
  {b | (b 0,b 1)∈D.coreFiber r}

variable (k : Type) [Field k]
noncomputable def coreFiberIdeal (r : Fin D.u) : Ideal (D.EndpointRing k) :=
  Ideal.span ((fun b => MvPolynomial.monomial b (1:k)) '' D.coreFiberExponents r)

theorem coreFiberIdeal_mem (r : Fin D.u) (f : D.EndpointRing k) :
    f∈D.coreFiberIdeal k r ↔ ∀ b∈f.support,(b 0,b 1)∈D.coreFiber r := by
  rw [coreFiberIdeal,MvPolynomial.mem_ideal_span_monomial_image]
  constructor
  · intro h b hb
    obtain ⟨c,hc,hcb⟩ := h b hb
    exact D.coreFiber_upward r hc ⟨hcb 0,hcb 1⟩
  · intro h b hb
    exact ⟨b,h b hb,le_rfl⟩

theorem coreFiberIdeal_zero : D.coreFiberIdeal k ⟨0,D.u_pos⟩=⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  rw [D.coreFiberIdeal_mem]
  intro b _
  exact D.coreFiber_zero (b 0,b 1)
end NSP14.Endpoint.Data
