module
public import Mathlib.Order.Minimal
public import Mathlib.LinearAlgebra.Dimension.Constructions
@[expose] public section
open scoped Classical
namespace NSP14.Endpoint

/-- Minimal points with a common first (or second) coordinate coincide. -/
theorem minimal_pair_eq_of_fst {U : Set (ℕ×ℕ)} {a b : ℕ×ℕ}
    (ha : Minimal (·∈U) a) (hb : Minimal (·∈U) b) (h : a.1=b.1) : a=b := by
  by_cases hK : a.2≤b.2
  · exact hb.eq_of_le ha.prop ⟨h.le,hK⟩
  · exact (ha.eq_of_le hb.prop ⟨h.ge,by omega⟩).symm

theorem minimal_pair_eq_of_snd {U : Set (ℕ×ℕ)} {a b : ℕ×ℕ}
    (ha : Minimal (·∈U) a) (hb : Minimal (·∈U) b) (h : a.2=b.2) : a=b := by
  by_cases hL : a.1≤b.1
  · exact hb.eq_of_le ha.prop ⟨hL,h.le⟩
  · exact (ha.eq_of_le hb.prop ⟨by omega,h.ge⟩).symm

/-- The small injection controlling a two-dimensional antichain. A
minimum vertical coordinate kappa is retained for the sharp T bound. -/
noncomputable def minimalIndex (U : Set (ℕ×ℕ)) (c : ℕ×ℕ) (κ : ℕ)
    (hc : c∈U) (hκ : ∀ a∈U,κ≤a.2) (a : {a | Minimal (·∈U) a}) : Fin (c.1+c.2-κ+1) :=
  if h : a.val.1≤c.1 then ⟨a.val.1,by have := hκ c hc;omega⟩
  else ⟨c.1+1+(a.val.2-κ),by
    have hK : a.val.2<c.2 := by
      by_contra hn
      have he := a.property.eq_of_le hc (show c≤a.val from ⟨by omega,by omega⟩)
      have hh := congrArg Prod.fst he
      omega
    have := hκ c hc
    have := hκ a.val a.property.prop
    omega⟩

theorem minimalIndex_val (U : Set (ℕ×ℕ)) (c : ℕ×ℕ) (κ : ℕ)
    (hc : c∈U) (hκ : ∀ a∈U,κ≤a.2) (a : {a | Minimal (·∈U) a}) :
    (minimalIndex U c κ hc hκ a).val=
      if a.val.1≤c.1 then a.val.1 else c.1+1+(a.val.2-κ) := by
  unfold minimalIndex
  split_ifs <;> rfl

theorem minimalIndex_injective (U : Set (ℕ×ℕ)) (c : ℕ×ℕ) (κ : ℕ)
    (hc : c∈U) (hκ : ∀ a∈U,κ≤a.2) : Function.Injective (minimalIndex U c κ hc hκ) := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [minimalIndex_val,minimalIndex_val] at hv
  split_ifs at hv with ha hb hb
  · exact Subtype.ext (minimal_pair_eq_of_fst a.property b.property hv)
  · omega
  · omega
  · have hκa := hκ a.val a.property.prop
    have hκb := hκ b.val b.property.prop
    exact Subtype.ext (minimal_pair_eq_of_snd a.property b.property (by omega))

theorem minimal_finite_of_mem (U : Set (ℕ×ℕ)) (c : ℕ×ℕ) (hc : c∈U) :
    Set.Finite {a | Minimal (·∈U) a} := by
  have : Finite {a | Minimal (·∈U) a} :=
    Finite.of_injective (minimalIndex U c 0 hc (by simp)) (minimalIndex_injective U c 0 hc (by simp))
  exact Set.toFinite _

theorem minimal_card_le (U : Set (ℕ×ℕ)) (c : ℕ×ℕ) (κ : ℕ)
    (hc : c∈U) (hκ : ∀ a∈U,κ≤a.2) :
    Nat.card {a | Minimal (·∈U) a}≤c.1+c.2-κ+1 := by
  have h := Nat.card_le_card_of_injective (minimalIndex U c κ hc hκ) (minimalIndex_injective U c κ hc hκ)
  simpa only [Nat.card_fin] using h
end NSP14.Endpoint
