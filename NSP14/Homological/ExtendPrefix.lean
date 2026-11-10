module
public import NSP14.Homological.LinearVariables
public import NSP14.Green.ExtendIndependent
@[expose] public section
open scoped Classical
namespace NSP14.Homological
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- Extend without moving any of the selected cut vectors. Mere inclusion of
spans is insufficient for the same-cut variable change. -/
theorem extend_independent_prefix {n t : ℕ} (c : Fin n → V) (hc : LinearIndependent k c)
    (hd : n+t ≤ Module.finrank k V) :
    ∃ d : Fin (n+t) → V, LinearIndependent k d ∧ ∀ i, d (Fin.castAdd t i)=c i := by
  induction t with
  | zero => exact ⟨c,hc,fun _ => rfl⟩
  | succ t ih =>
    obtain ⟨d,hd',hp⟩ := ih (by omega)
    have hr : Module.finrank k (Submodule.span k (Set.range d))=n+t := by
      simpa only [Fintype.card_fin] using finrank_span_eq_card hd'
    obtain ⟨x,hx⟩ : ∃ x : V,x ∉ Submodule.span k (Set.range d) := by
      by_contra hn
      push Not at hn
      have ht : Submodule.span k (Set.range d)=⊤ := top_unique (fun _ _ => hn _)
      have hdim := congrArg (fun U : Submodule k V => Module.finrank k U) ht
      rw [hr,finrank_top] at hdim
      omega
    refine ⟨Fin.snoc d x,hd'.finSnoc hx,?_⟩
    intro i
    have he : Fin.castAdd (t+1) i=(Fin.castAdd t i).castSucc := Fin.ext rfl
    rw [he,Fin.snoc_castSucc,hp]

noncomputable def basisExtendingPrefix [Module.Finite k V] {n : ℕ}
    (c : Fin n → V) (hc : LinearIndependent k c) :
    Module.Basis (Fin (n+(Module.finrank k V-n))) k V :=
  basisOfLinearIndependentOfCardEqFinrank'
    (extend_independent_prefix c hc (by
      have hle : n ≤ Module.finrank k V := by
        simpa only [Fintype.card_fin] using hc.fintype_card_le_finrank
      omega)).choose
    (extend_independent_prefix c hc (by
      have hle : n ≤ Module.finrank k V := by
        simpa only [Fintype.card_fin] using hc.fintype_card_le_finrank
      omega)).choose_spec.1
    (by
      have hle : n ≤ Module.finrank k V := by
        simpa only [Fintype.card_fin] using hc.fintype_card_le_finrank
      simp only [Fintype.card_fin]
      omega)

theorem basisExtendingPrefix_apply [Module.Finite k V] {n : ℕ}
    (c : Fin n → V) (hc : LinearIndependent k c) (i : Fin n) :
    basisExtendingPrefix c hc (Fin.castAdd (Module.finrank k V-n) i)=c i := by
  unfold basisExtendingPrefix
  rw [coe_basisOfLinearIndependentOfCardEqFinrank']
  have hb : n+(Module.finrank k V-n) ≤ Module.finrank k V := by
    have hle : n ≤ Module.finrank k V := by
      simpa only [Fintype.card_fin] using hc.fintype_card_le_finrank
    omega
  exact (extend_independent_prefix c hc hb).choose_spec.2 i
end NSP14.Homological
