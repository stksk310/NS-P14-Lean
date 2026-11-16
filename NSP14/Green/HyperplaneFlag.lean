module

public import NSP14.Green.HyperplaneStep
public import NSP14.Green.FlagSpan

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open scoped Classical

namespace NSP14.Green

variable {k V W : Type*} [Field k] [Infinite k]
  [AddCommGroup V] [Module k V] [Module.Finite k V]
  [AddCommGroup W] [Module k W] [Module.Finite k W]

/-- One independent flag simultaneously satisfies every degree-two Green bound.
All cut images use the same original bilinear product. -/
theorem exists_hyperplane_flag (μ : V →ₗ[k] V →ₗ[k] W)
    (hs : ∀ x y, μ x y = μ y x) (hspan : bilinearSpan μ = ⊤)
    (p b : ℕ) (hdim : p ≤ Module.finrank k V)
    (hcap : Module.finrank k W ≤ (p + 1).choose 2 + b) :
    ∃ c : Fin p → V, LinearIndependent k c ∧
      ∀ s, s ≤ p → Module.finrank k (W ⧸ cutImage μ (flagSpan (k := k) c s)) ≤
        (p + 1 - s).choose 2 + (b - s) := by
  suffices h : ∀ n, n ≤ p → ∃ c : Fin n → V, LinearIndependent k c ∧
      ∀ s, s ≤ n → Module.finrank k (W ⧸ cutImage μ (flagSpan (k := k) c s)) ≤
        (p + 1 - s).choose 2 + (b - s) from h p le_rfl
  intro n hn
  induction n with
  | zero =>
    refine ⟨Fin.elim0, linearIndependent_empty_type, ?_⟩
    intro s hs0
    have he : s = 0 := by omega
    subst s
    rw [flagSpan_zero, cutImage_bot]
    have hz := (⊥ : Submodule k W).quotEquivOfEqBot rfl |>.finrank_eq
    rw [hz]
    simpa only [Nat.sub_zero] using hcap
  | succ n ih =>
    obtain ⟨c,hLI,hc⟩ := ih (by omega)
    let E := flagSpan (k := k) c n
    have hE : Module.finrank k E = n := by
      rw [show E = Submodule.span k (Set.range c) from flagSpan_full c]
      exact (finrank_span_eq_card hLI).trans (Fintype.card_fin n)
    let μE := cutProduct μ hs E
    have hsym : ∀ x y, μE x y = μE y x := cutProduct_symmetric μ hs E
    have hsp : bilinearSpan μE = ⊤ := cutProduct_spans μ hs E hspan
    have hV : Module.finrank k (V ⧸ E) + n = Module.finrank k V := by
      have h := E.finrank_quotient_add_finrank
      rwa [hE] at h
    have hpn : (p - n) + 1 = p + 1 - n := by omega
    have hcurrent : Module.finrank k (W ⧸ cutImage μ E) ≤ ((p - n) + 1).choose 2 + (b - n) := by
      rw [hpn]
      exact hc n le_rfl
    obtain ⟨z,hz,hnext⟩ := exists_hyperplane_step μE hsym hsp (p - n) (b - n)
      (by omega) (by omega) hcurrent
    obtain ⟨x,hx⟩ := E.mkQ_surjective z
    have hxnot : x ∉ E := by
      intro hxE
      have he : E.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero E).mpr hxE
      rw [hx] at he
      exact hz he
    have hnewLI : LinearIndependent k (Fin.snoc c x) :=
      hLI.finSnoc (by simpa only [E, flagSpan_full] using hxnot)
    refine ⟨Fin.snoc c x,hnewLI,?_⟩
    intro s hsn
    by_cases hsold : s ≤ n
    · rw [flagSpan_snoc c x hsold]
      exact hc s hsold
    have he : s = n + 1 := by omega
    subst s
    rw [flagSpan_snoc_full]
    have hfin := (cutStepEquiv μ hs E x).finrank_eq
    have hdimnext : Module.finrank k (W ⧸ cutImage μ (E ⊔ Submodule.span k {x})) ≤
        (p - n).choose 2 + (b - n - 1) := by
      rw [← hfin]
      have hμ : μE z = cutProduct μ hs E (E.mkQ x) := by rw [hx]
      rw [hμ] at hnext
      exact hnext
    have hpnext : p + 1 - (n + 1) = p - n := by omega
    have hbnext : b - (n + 1) = b - n - 1 := by omega
    rw [hpnext,hbnext]
    exact hdimnext

/-- p independent forms kill the entire quadratic quotient when b≤p. -/
theorem exists_quadratic_zero_cut (μ : V →ₗ[k] V →ₗ[k] W)
    (hs : ∀ x y, μ x y = μ y x) (hspan : bilinearSpan μ = ⊤)
    (p b : ℕ) (hb : b ≤ p) (hdim : p ≤ Module.finrank k V)
    (hcap : Module.finrank k W ≤ (p + 1).choose 2 + b) :
    ∃ c : Fin p → V, LinearIndependent k c ∧ cutImage μ (flagSpan (k := k) c p) = ⊤ := by
  obtain ⟨c,hLI,hc⟩ := exists_hyperplane_flag μ hs hspan p b hdim hcap
  have hz := hc p le_rfl
  have he : p + 1 - p = 1 := by omega
  rw [he, Nat.sub_eq_zero_of_le hb] at hz
  norm_num at hz
  refine ⟨c,hLI,?_⟩
  apply Submodule.eq_top_of_finrank_eq
  have hq := (cutImage μ (flagSpan (k := k) c p)).finrank_quotient_add_finrank
  omega

end NSP14.Green
