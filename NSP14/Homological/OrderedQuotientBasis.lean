module
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Order.WellFounded
@[expose] public section
open scoped Classical BigOperators
namespace NSP14.Homological
variable (k : Type*) [Field k] {I V : Type*} [LinearOrder I]
  [AddCommGroup V] [Module k V] (b : I → V)

/-- Greedy standard labels in the actual quotient: the current monomial
class is not a combination of strictly earlier actual monomial classes. -/
def OrderedStandards : Set I :=
  {i | b i ∉ Submodule.span k (b '' Set.Iio i)}

theorem orderedStandards_independent :
    LinearIndependent k (fun i : OrderedStandards k b => b i.val) := by
  rw [linearIndependent_iff]
  intro c hc
  by_contra hne
  have hs : c.support.Nonempty := Finsupp.support_nonempty_iff.mpr hne
  let i := c.support.max' hs
  have hi : i ∈ c.support := Finset.max'_mem _ hs
  have hci : c i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have hrest : (∑ j ∈ c.support.erase i,c j • b j.val) ∈
      Submodule.span k (b '' Set.Iio i.val) := by
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem
    have hj' := Finset.mem_erase.mp hj
    have hle : j ≤ i := Finset.le_max' _ _ hj'.2
    have hlt : j.val < i.val := by
      have hjne : j ≠ i := hj'.1
      exact lt_of_le_of_ne hle (fun he => hjne (Subtype.ext he))
    exact Submodule.subset_span ⟨j.val,hlt,rfl⟩
  have he := Finset.sum_erase_add _ (fun j => c j • b j.val) hi
  have hsum : ∑ j ∈ c.support,c j • b j.val=0 := hc
  have hmem : c i • b i.val ∈ Submodule.span k (b '' Set.Iio i.val) := by
    have heq : c i • b i.val=-(∑ j ∈ c.support.erase i,c j • b j.val) := by
      rw [hsum] at he
      exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using he)
    rw [heq]
    exact Submodule.neg_mem _ hrest
  exact i.property ((Submodule.smul_mem_iff _ hci).mp hmem)

variable [WellFoundedLT I]

/-- Normal forms never acquire a label above the original label. -/
theorem ordered_mem_span_initial (i : I) :
    b i ∈ Submodule.span k ((fun s : OrderedStandards k b => b s.val) '' {s | s.val ≤ i}) := by
  refine (wellFounded_lt (α:=I)).induction (C:=fun i =>
    b i ∈ Submodule.span k ((fun s : OrderedStandards k b => b s.val) '' {s | s.val ≤ i})) i ?_
  intro i ih
  by_cases hs : i ∈ OrderedStandards k b
  · exact Submodule.subset_span ⟨⟨i,hs⟩,le_rfl,rfl⟩
  · have hb : b i ∈ Submodule.span k (b '' Set.Iio i) := by simpa [OrderedStandards] using hs
    apply (Submodule.span_le.mpr ?_) hb
    rintro x ⟨j,hji,rfl⟩
    change j < i at hji
    apply (Submodule.span_mono (Set.image_mono ?_)) (ih j hji)
    intro s hs
    exact hs.trans (le_of_lt hji)
theorem orderedStandards_span (hb : Submodule.span k (Set.range b)=⊤) :
    Submodule.span k (Set.range (fun s : OrderedStandards k b => b s.val))=⊤ := by
  apply top_unique
  rw [← hb]
  apply Submodule.span_le.mpr
  rintro x ⟨i,rfl⟩
  exact Submodule.span_mono (Set.image_subset_range _ _) (ordered_mem_span_initial k b i)

noncomputable def orderedStandardBasis (hb : Submodule.span k (Set.range b)=⊤) :
    Module.Basis (OrderedStandards k b) k V :=
  Module.Basis.mk (orderedStandards_independent k b)
    (by rw [orderedStandards_span k b hb])

theorem orderedStandardBasis_apply (hb : Submodule.span k (Set.range b)=⊤)
    (i : OrderedStandards k b) : orderedStandardBasis k b hb i=b i.val :=
  Module.Basis.mk_apply _ _ _

theorem ordered_nonstandard_mem_span_strict {i : I} (hi : i ∉ OrderedStandards k b) :
    b i ∈ Submodule.span k ((fun s : OrderedStandards k b => b s.val) '' {s | s.val < i}) := by
  have hb : b i ∈ Submodule.span k (b '' Set.Iio i) := by simpa [OrderedStandards] using hi
  apply (Submodule.span_le.mpr ?_) hb
  rintro x ⟨j,hj,rfl⟩
  change j < i at hj
  apply (Submodule.span_mono (Set.image_mono ?_)) (ordered_mem_span_initial k b j)
  intro s hs
  exact hs.trans_lt hj

theorem orderedStandardBasis_repr_zero_above (hb : Submodule.span k (Set.range b)=⊤)
    (i : I) (j : OrderedStandards k b) (hji : i < j.val) :
    (orderedStandardBasis k b hb).repr (b i) j=0 := by
  have h := ordered_mem_span_initial k b i
  have h' : b i ∈ Submodule.span k ((orderedStandardBasis k b hb) '' {s | s.val ≤ i}) := by
    simpa only [orderedStandardBasis,Module.Basis.coe_mk] using h
  have hs := (orderedStandardBasis k b hb).mem_span_image.mp h'
  by_contra hn
  have hj := hs (Finsupp.mem_support_iff.mpr hn)
  exact (not_le_of_gt hji) hj

theorem orderedStandardBasis_repr_zero_ge_nonstandard (hb : Submodule.span k (Set.range b)=⊤)
    (i : I) (hi : i ∉ OrderedStandards k b) (j : OrderedStandards k b) (hji : i ≤ j.val) :
    (orderedStandardBasis k b hb).repr (b i) j=0 := by
  have h := ordered_nonstandard_mem_span_strict k b hi
  have h' : b i ∈ Submodule.span k ((orderedStandardBasis k b hb) '' {s | s.val < i}) := by
    simpa only [orderedStandardBasis,Module.Basis.coe_mk] using h
  have hs := (orderedStandardBasis k b hb).mem_span_image.mp h'
  by_contra hn
  exact (not_lt_of_ge hji) (hs (Finsupp.mem_support_iff.mpr hn))

omit [WellFoundedLT I] in
/-- Nonstandard monomials stay nonstandard under an order-compatible actual
variable action; this gives divisor closure for the actual quotient module. -/
theorem orderedStandards_shift_down (T : V →ₗ[k] V) (shift : I → I)
    (hshift : StrictMono shift) (hT : ∀ i,T (b i)=b (shift i)) (i : I)
    (hi : shift i ∈ OrderedStandards k b) : i ∈ OrderedStandards k b := by
  by_contra hn
  have hmem : b i ∈ Submodule.span k (b '' Set.Iio i) := by simpa [OrderedStandards] using hn
  have him : T (b i) ∈ (Submodule.span k (b '' Set.Iio i)).map T := Submodule.mem_map_of_mem hmem
  rw [Submodule.map_span] at him
  rw [hT] at him
  apply hi
  apply (Submodule.span_le.mpr ?_) him
  rintro x ⟨y,⟨j,hj,rfl⟩,rfl⟩
  rw [hT]
  exact Submodule.subset_span ⟨shift j,hshift hj,rfl⟩
end NSP14.Homological
