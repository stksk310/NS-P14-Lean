module
public import NSP14.Additive.TwoValueSequence
public import NSP14.Additive.EndpointResidues
public import NSP14.Endpoint.CoreInternalAction
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) {ℓ : ℕ}
def indexedInternalWord (w : Fin ℓ → D.a) : D.corePoints :=
  ∑ i, D.coreGeneratorPoint (D.internalVariable (w i))
def internalWordSequence (w : Fin ℓ → D.a) : Fin ℓ → ZMod D.u :=
  fun i => ((w i).val : ZMod D.u)

theorem internal_selected_degree (w : Fin ℓ → D.a) (I : Finset (Fin ℓ)) :
    D.coreDegree (∑ i ∈ I,D.coreGeneratorPoint (D.internalVariable (w i))) = I.card := by
  rw [map_sum]
  simp only [show ∀ i, D.coreDegree (D.coreGeneratorPoint (D.internalVariable (w i)))=1 from fun _ => rfl,
    Finset.sum_const,smul_eq_mul,mul_one]
theorem internal_selected_offset (w : Fin ℓ → D.a) (I : Finset (Fin ℓ)) :
    D.coreOffset (∑ i ∈ I,D.coreGeneratorPoint (D.internalVariable (w i))) =
      ∑ i ∈ I,(w i).val := by
  rw [map_sum]
  rfl

/-- Any nonempty zero-residue selection is a genuine endpoint factor.
Its endpoint multiplicity lies strictly between zero and the selection length. -/
theorem internal_zero_selection_factor (w : Fin ℓ → D.a) (I : Finset (Fin ℓ))
    (hI : I.Nonempty) (hdiv : D.u ∣ ∑ i ∈ I,(w i).val) :
    ∃ K : ℕ, 1 ≤ K ∧ K < I.card ∧
      D.indexedInternalWord w =
        (∑ i ∈ Finset.univ \ I,D.coreGeneratorPoint (D.internalVariable (w i)))+
          D.coreEndpointPoint (I.card-K,K) := by
  let B := ∑ i ∈ I,(w i).val
  let K := B/D.u
  have hKB : K*D.u=B := Nat.div_mul_cancel hdiv
  have hBpos : 0 < B := Finset.sum_pos (fun i _ => D.a_pos _ (w i).property) hI
  have hBlt : B < I.card*D.u := by
    have hh := Finset.sum_lt_sum (fun i _ => (D.a_lt _ (w i).property).le)
      (hI.imp (fun i hi => ⟨hi,D.a_lt _ (w i).property⟩))
    simpa only [Finset.sum_const,smul_eq_mul] using hh
  have hKpos : 1 ≤ K := by have hu := D.u_pos; nlinarith
  have hKlt : K < I.card := by have hu := D.u_pos; nlinarith
  let p : D.corePoints := ∑ i ∈ I,D.coreGeneratorPoint (D.internalVariable (w i))
  have hp : p = D.coreEndpointPoint (I.card-K,K) := by
    apply Subtype.ext
    rw [D.coreEndpointPoint_coe]
    apply Prod.ext
    · change D.coreDegree p=I.card-K+K
      rw [D.internal_selected_degree]
      omega
    · change D.coreOffset p=D.u*K
      rw [D.internal_selected_offset]
      simpa only [B,mul_comm] using hKB.symm
  refine ⟨K,hKpos,hKlt,?_⟩
  rw [←hp]
  exact (Finset.sum_sdiff (Finset.subset_univ I) (f := fun i =>
    D.coreGeneratorPoint (D.internalVariable (w i)))).symm

theorem minimal_internal_word_zeroSumFree (w : Fin ℓ → D.a)
    (hmin : D.CoreMinimal (D.indexedInternalWord w)) :
    NSP14.Additive.ZeroSumFree (D.internalWordSequence w) := by
  intro I hI he
  have hdiv : D.u ∣ ∑ i ∈ I,(w i).val := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simpa only [Nat.cast_sum,internalWordSequence] using he
  obtain ⟨K,hKpos,hKlt,hfac⟩ := D.internal_zero_selection_factor w I hI hdiv
  have hh := D.minimal_endpoint_factor _ _ (I.card-K,K) hmin hfac
  have hz := congrArg Prod.snd hh
  change K=0 at hz
  omega

theorem surviving_internal_word_zeroSumFree (k : Type) [Field k] (w : Fin ℓ → D.a)
    (hn : Ideal.Quotient.mk (NSP14.Endpoint.endpointIdeal k (D.Core k) (D.endpointToCore k))
      (D.coreMonomial k (D.indexedInternalWord w)) ≠ 0) :
    NSP14.Additive.ZeroSumFree (D.internalWordSequence w) := by
  apply D.minimal_internal_word_zeroSumFree w
  by_contra hm
  have hh := D.QCore_class_monomial k (D.indexedInternalWord w)
  rw [dite_eq_right hm] at hh
  exact hn hh

/-- The actual QC survivor is fed into the general SC theorem with the
same normalized offsets and the same modulus D.u. -/
theorem surviving_internal_word_SC (k : Type) [Field k] (w : Fin ℓ → D.a)
    (hn : Ideal.Quotient.mk (NSP14.Endpoint.endpointIdeal k (D.Core k) (D.endpointToCore k))
      (D.coreMonomial k (D.indexedInternalWord w)) ≠ 0) (hl : D.u < 2*ℓ) :
    ∃ c : (ZMod D.u)ˣ, ∑ i, ((c : ZMod D.u)*D.internalWordSequence w i).val < D.u := by
  have hu : 2 ≤ D.u := by
    obtain ⟨b,hb⟩ := Finset.card_pos.mp (by have := D.q_two; omega : 0 < D.a.card)
    have hp := D.a_pos b hb
    have ht := D.a_lt b hb
    omega
  exact NSP14.Additive.savchevChen hu _ (D.surviving_internal_word_zeroSumFree k w hn) hl

/-- Typed mixed-word consumer. Labels and counts are swapped together by
the returned disjunction; the original core and field are unchanged. -/
theorem surviving_twoValue_SC (k : Type) [Field k] (R T : ℕ) (hR : 1 ≤ R) (hT : 1 ≤ T)
    (a b : D.a) (hab : a ≠ b)
    (hn : Ideal.Quotient.mk (NSP14.Endpoint.endpointIdeal k (D.Core k) (D.endpointToCore k))
      (D.coreMonomial k (D.indexedInternalWord (Fin.addCases (fun _ : Fin R => a) (fun _ : Fin T => b)))) ≠ 0)
    (hl : D.u < 2*(R+T)) :
    ∃ c : (ZMod D.u)ˣ, ∃ c₀ : ℕ, 2 ≤ c₀ ∧
      ((((c : ZMod D.u)*(a.val : ZMod D.u)).val = 1 ∧
          ((c : ZMod D.u)*(b.val : ZMod D.u)).val = c₀ ∧
          R+c₀*T ≤ D.u-1 ∧ (c₀ : ZMod D.u)*(a.val : ZMod D.u)=(b.val : ZMod D.u)) ∨
       (((c : ZMod D.u)*(b.val : ZMod D.u)).val = 1 ∧
          ((c : ZMod D.u)*(a.val : ZMod D.u)).val = c₀ ∧
          T+c₀*R ≤ D.u-1 ∧ (c₀ : ZMod D.u)*(b.val : ZMod D.u)=(a.val : ZMod D.u))) := by
  let w : Fin (R+T) → D.a := Fin.addCases (fun _ : Fin R => a) (fun _ : Fin T => b)
  have hz := D.surviving_internal_word_zeroSumFree k w hn
  have he : D.internalWordSequence w = NSP14.Additive.twoValueSequence R T (a.val : ZMod D.u) (b.val : ZMod D.u) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [internalWordSequence,w,NSP14.Additive.twoValueSequence,Fin.addCases_left,Fin.addCases_right]
  rw [he] at hz
  have hv : (a.val : ZMod D.u) ≠ (b.val : ZMod D.u) := by
    intro hh
    apply hab
    apply Subtype.ext
    have hh' := congrArg ZMod.val hh
    rwa [ZMod.val_natCast_of_lt (D.a_lt _ a.property),ZMod.val_natCast_of_lt (D.a_lt _ b.property)] at hh'
  have hu : 2 ≤ D.u := by have hp := D.a_pos _ a.property; have ht := D.a_lt _ a.property; omega
  exact NSP14.Additive.savchevChen_twoValue hu hR hT (a.val : ZMod D.u) (b.val : ZMod D.u) hv hz hl
end NSP14.Endpoint.Data
