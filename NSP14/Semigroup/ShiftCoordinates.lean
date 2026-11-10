module

public import NSP14.Semigroup.Heads
public import Mathlib.LinearAlgebra.Finsupp.Supported

@[expose] public section

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k]

/-- The exponent of multiplication by t^m, regardless of whether its initial form survives. -/
noncomputable def shiftExponent (x : S.carrier) : S.carrier :=
  ⟨x.val + S.multiplicity, S.add_mem x.property S.multiplicity_mem⟩

theorem shiftExponent_injective : Function.Injective S.shiftExponent := by
  intro x y h
  apply Subtype.ext
  have hv := congrArg Subtype.val h
  exact Nat.add_right_cancel hv

noncomputable def LiveExponent (x : S.carrier) : Prop :=
  S.order (x.val + S.multiplicity) = S.order x.val + 1

theorem not_live_iff_terminal (x : S.carrier) : ¬S.LiveExponent x ↔ S.Terminal x.val := by
  have ho := S.order_add_multiplicity x.property
  change ¬S.order (x.val + S.multiplicity) = S.order x.val + 1 ↔ _
  simp only [Terminal, show x.val ∈ S from x.property, true_and]
  omega

noncomputable def liveFilter : (S.carrier →₀ k) →ₗ[k] (S.carrier →₀ k) where
  toFun f := by classical exact f.filter S.LiveExponent
  map_add' := by classical intros; exact Finsupp.filter_add
  map_smul' := by classical intros; exact Finsupp.filter_smul

/-- Coefficient shift with all dead arrows removed. -/
noncomputable def coordinateShift : (S.carrier →₀ k) →ₗ[k] (S.carrier →₀ k) :=
  (Finsupp.lmapDomain k k S.shiftExponent).comp (S.liveFilter k)

theorem coordinateShift_single_live (x : S.carrier) (c : k) (hx : S.LiveExponent x) :
    S.coordinateShift k (Finsupp.single x c) = Finsupp.single (S.shiftExponent x) c := by
  classical
  simp [coordinateShift, liveFilter, Finsupp.filter_single_of_pos S.LiveExponent hx]

theorem coordinateShift_single_dead (x : S.carrier) (c : k) (hx : ¬S.LiveExponent x) :
    S.coordinateShift k (Finsupp.single x c) = 0 := by
  classical
  simp [coordinateShift, liveFilter, Finsupp.filter_single_of_neg S.LiveExponent hx]

/-- Injectivity of the exponent shift rules out hidden cancellation between live arrows. -/
theorem coordinateShift_eq_zero (f : S.carrier →₀ k) :
    S.coordinateShift k f = 0 ↔ ∀ x, S.LiveExponent x → f x = 0 := by
  classical
  change Finsupp.mapDomain S.shiftExponent (f.filter S.LiveExponent) = 0 ↔ _
  rw [← Finsupp.mapDomain_zero (f := S.shiftExponent),
    (Finsupp.mapDomain_injective S.shiftExponent_injective).eq_iff,
    Finsupp.filter_eq_zero_iff]

theorem coordinateShift_ker : (S.coordinateShift k).ker =
    Finsupp.supported k k {x : S.carrier | S.Terminal x.val} := by
  ext f
  rw [LinearMap.mem_ker, S.coordinateShift_eq_zero, Finsupp.mem_supported']
  constructor
  · intro h x hx
    apply h x
    by_contra hn
    exact hx ((S.not_live_iff_terminal x).1 hn)
  · intro h x hx
    apply h x
    intro ht
    exact ((S.not_live_iff_terminal x).2 ht) hx

theorem shift_live_not_head (x : S.carrier) (hx : S.LiveExponent x) :
    ¬S.XHead (S.shiftExponent x).val := by
  intro hh
  exact hh.2 ⟨x.val, x.property, rfl, hx⟩

theorem not_head_predecessor (y : S.carrier) (hy : ¬S.XHead y.val) :
    ∃ x : S.carrier, S.LiveExponent x ∧ y = S.shiftExponent x := by
  have he : ∃ x ∈ S, y.val = x + S.multiplicity ∧
      S.order y.val = S.order x + 1 := by
    by_contra hn
    exact hy ⟨y.property, hn⟩
  obtain ⟨x, hx, heq, hlive⟩ := he
  refine ⟨⟨x, hx⟩, ?_, Subtype.ext heq⟩
  change S.order (x + S.multiplicity) = S.order x + 1
  simpa only [heq] using hlive

/-- Every supported incoming coordinate is attained, with no finite-enumeration hypothesis. -/
theorem coordinateShift_range : (S.coordinateShift k).range =
    Finsupp.supported k k {y : S.carrier | ¬S.XHead y.val} := by
  classical
  apply le_antisymm
  · rintro g ⟨f, rfl⟩
    rw [Finsupp.mem_supported']
    intro y hy
    change Finsupp.mapDomain S.shiftExponent (f.filter S.LiveExponent) y = 0
    apply Finsupp.mapDomain_of_notMem_image_support
    rintro ⟨x, hx, rfl⟩
    have hlive : S.LiveExponent x := (Finset.mem_filter.mp hx).2
    exact hy (S.shift_live_not_head x hlive)
  · intro g hg
    rw [← g.sum_single]
    apply Submodule.sum_mem
    intro y hy
    have hnot : ¬S.XHead y.val := (Finsupp.mem_supported k g).1 hg hy
    obtain ⟨x, hx, rfl⟩ := S.not_head_predecessor y hnot
    exact ⟨Finsupp.single x (g (S.shiftExponent x)), S.coordinateShift_single_live k _ _ hx⟩

end NSP14.NumericalSemigroup
