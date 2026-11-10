module
public import NSP14.Homological.WeightedPivot
@[expose] public section
open scoped Classical BigOperators
namespace NSP14.Homological

theorem finite_degree_sum {I : Type*} [Fintype I] (d : I → ℕ) (N : ℕ)
    (hN : ∀ i,d i ≤ N) (f : ℕ → ℚ) :
    (∑ i : I,f (d i))=
      ∑ t ∈ Finset.range (N+1),f t*(Nat.card {i : I // d i=t} : ℚ) := by
  rw [← Finset.sum_fiberwise_of_maps_to' (s:=(Finset.univ : Finset I))
    (t:=Finset.range (N+1)) (g:=d) (fun i _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hN i))) f]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_const,nsmul_eq_mul,Nat.card_eq_fintype_card,Fintype.card_subtype,mul_comm]
end NSP14.Homological
