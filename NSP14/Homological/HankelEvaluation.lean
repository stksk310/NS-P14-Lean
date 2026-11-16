module
public import NSP14.Homological.HankelAction
public import NSP14.Homological.VandermondeSpark
public import NSP14.Homological.TwoStepSlots
public import Mathlib.Data.Fintype.BigOperators
@[expose] public section
open scoped BigOperators Classical
namespace NSP14.Homological
variable (k : Type*) [Field k] (d n r : ℕ) (hcard : d+n=r+1)

include hcard in
/-- The actual Vandermonde linear combination of Hankel actions is
rank one. This identity uses no division, even at the point zero. -/
theorem hankel_evaluation (t : k) (p : (Fin d → k) × (Fin n → k)) :
    (∑ j : Fin r,t^j.val • hankelAction k d n j.val p)=
      (0,momentFunctional k d t p.1 • (fun b : Fin n => t^b.val)) := by
  apply Prod.ext
  · rw [finiteSum_fst]
    change (∑ j : Fin r,t^j.val • (0 : Fin d → k))=0
    simp
  · funext b
    rw [finiteSum_snd,Finset.sum_apply]
    change (∑ j : Fin r,(t^j.val •
      (fun b : Fin n => ∑ a : Fin d,(if j.val=a.val+b.val then (1:k) else 0)*p.1 a)) b)=_
    simp only [Pi.smul_apply,smul_eq_mul]
    change (∑ j : Fin r,t^j.val*(∑ a : Fin d,(if j.val=a.val+b.val then (1:k) else 0)*p.1 a))=
      momentFunctional k d t p.1*t^b.val
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have he (a : Fin d) :
        (∑ j : Fin r,t^j.val*((if j.val=a.val+b.val then (1:k) else 0)*p.1 a))=
          t^(a.val+b.val)*p.1 a := by
      let j0 : Fin r := ⟨a.val+b.val,by have := a.isLt;have := b.isLt;omega⟩
      rw [Fintype.sum_eq_single j0]
      · simp [j0]
      · intro j hj
        have hn : j.val≠a.val+b.val := fun h => hj (Fin.ext h)
        simp [hn]
    simp_rw [he,pow_add]
    change (∑ a : Fin d,t^a.val*t^b.val*p.1 a)=(∑ a : Fin d,p.1 a*t^a.val)*t^b.val
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    ring
end NSP14.Homological
