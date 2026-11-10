module
public import NSP14.Homological.KoszulArrowWedge
public import NSP14.Homological.ModuleTermArithmetic
@[expose] public section
open scoped Classical BigOperators
namespace NSP14.Homological
variable {σ : Type*}

noncomputable def wedgeExponent (F : Finset σ) : σ →₀ ℕ :=
  ∑ v ∈ F,Finsupp.single v 1

theorem wedgeExponent_apply (F : Finset σ) (v : σ) :
    wedgeExponent F v=if v ∈ F then 1 else 0 := by
  simp [wedgeExponent,Finsupp.single_apply]

theorem wedgeExponent_insert (F : Finset σ) (v : σ) (hv : v ∉ F) :
    wedgeExponent (insert v F)=Finsupp.single v 1+wedgeExponent F := by
  exact Finset.sum_insert hv

theorem wedgeExponent_degree (F : Finset σ) : (wedgeExponent F).degree=F.card := by
  simp [wedgeExponent,map_sum,Finsupp.degree_single]

theorem koszulSlotArrow_exponent (xs : List σ) (hxs : xs.Nodup) (j : ℕ)
    (s : KoszulSlot xs.length (j+1)) (t : KoszulSlot xs.length j)
    {v : σ} {b : Bool} (h : koszulSlotArrow xs j s t=some (v,b)) :
    wedgeExponent (koszulSlotWedge xs j t)+Finsupp.single v 1=
      wedgeExponent (koszulSlotWedge xs (j+1) s) := by
  obtain ⟨hw,hn,_⟩ := koszulSlotArrow_wedge xs hxs j s t v b h
  rw [hw,wedgeExponent_insert _ _ hn,add_comm]

theorem wedgeExponent_injective : Function.Injective (wedgeExponent (σ:=σ)) := by
  intro F E h
  ext v
  have he := congrArg (fun d : σ →₀ ℕ => d v) h
  simp only [wedgeExponent_apply] at he
  by_cases hvF : v ∈ F <;> by_cases hvE : v ∈ E <;> simp_all
end NSP14.Homological
