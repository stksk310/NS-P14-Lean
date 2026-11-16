module
public import NSP14.Endpoint.CoreGeneration
public import NSP14.Endpoint.CoreHilbertSum
public import NSP14.Homological.Harmonic
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
open CategoryTheory CategoryTheory.Limits NSP14.Homological
namespace NSP14.Endpoint
universe u
variable (k σ : Type u) [Field k] [Fintype σ] [Nonempty σ] [LinearOrder σ]
  (M : ModuleCat.{u} (VariableRing k σ)) [Module.Finite (VariableRing k σ) M]
  [Module.Finite k (coefficientModule k σ M)] (G : GradedPolynomialModule k σ M)

/-- The first-row consequence of the already proved actual
standard-module harmonic estimate, retaining the real grading. -/
theorem cyclic_first_harmonic (N : ℕ)
    (hgen : Submodule.span (VariableRing k σ)
      (Set.range (fun a : G.piece 0 => (show M from G.inclusion 0 a)))=⊤)
    (hN : ∀ t : ℕ,N < t → IsZero (G.piece (0+t)))
    (hzero : Module.finrank k (G.piece 0)=1) (hbzero : totalBetti k σ M 0=1) :
    (totalBetti k σ M 1 : ℚ)≤(Fintype.card σ : ℚ)+
      ∑ n∈Finset.range N,((Fintype.card σ-1 : ℕ) : ℚ)*
        (Module.finrank k (G.piece (n+1)) : ℚ)/(n+2) := by
  have h := generated_harmonic_bound k σ M G MonomialOrder.degLex 0 N hgen hN 1 (by omega)
  rw [bettiEuler_succ,bettiEuler_zero,hbzero] at h
  simp only [Int.cast_sub,Int.cast_natCast,Nat.choose_one_right] at h
  rw [Finset.sum_range_succ'] at h
  simp only [Nat.cast_zero,zero_add,Nat.cast_one,one_div,div_one] at h
  rw [mul_add,Finset.mul_sum] at h
  have he : ((Fintype.card σ-1 : ℕ) : ℚ)+1=(Fintype.card σ : ℚ) := by
    exact_mod_cast Nat.sub_add_cancel (show 1≤Fintype.card σ from Fintype.card_pos)
  have hsum : (∑ n∈Finset.range N,((Fintype.card σ-1 : ℕ) : ℚ)*
      ((1:ℚ)/(↑(n+1)+1)*Module.finrank k (G.piece (0+↑(n+1)))))=
      ∑ n∈Finset.range N,((Fintype.card σ-1 : ℕ) : ℚ)*
        (Module.finrank k (G.piece (n+1)) : ℚ)/(n+2) := by
    apply Finset.sum_congr rfl
    intro n _
    rw [show (0+(↑(n+1):ℤ))=(n:ℤ)+1 by omega]
    simp only [Nat.cast_add,Nat.cast_one]
    ring
  simp only [Nat.cast_add,Nat.cast_one,one_mul,one_div] at h hsum
  rw [hsum] at h
  rw [show (0+(↑(0:ℕ):ℤ))=0 by omega,hzero] at h
  linarith
end NSP14.Endpoint
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

theorem QCore_first_harmonic : (totalBetti k D.a (D.QCoreModule k) 1 : ℚ)≤(D.q : ℚ)+
    ∑ n∈Finset.range (D.u-1),((D.q-1 : ℕ) : ℚ)*(D.coreHilbert k (n+1):ℚ)/(n+2) := by
  let : Nonempty D.a := by
    obtain ⟨b,hb⟩ := Finset.card_pos.mp (show 0<D.a.card by have := D.q_two;omega)
    exact ⟨⟨b,hb⟩⟩
  have h := NSP14.Endpoint.cyclic_first_harmonic k D.a (D.QCoreModule k) (D.QCoreGrading k)
    (D.u-1) (D.QCore_generated_degree_zero k) (by
      intro n hn
      simpa only [zero_add] using D.QCoreGrading_above k n (by omega))
    (D.QCoreGrading_zero_dim k) (D.QCore_betti_zero k)
  simpa only [Fintype.card_coe,q,coreHilbert,Int.natCast_add,Int.natCast_one] using h
end NSP14.Endpoint.Data
