module
public import NSP14.Endpoint.ActualKernel
public import NSP14.Endpoint.Volume
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

theorem shiftedResidue_one_injective : Function.Injective (fun r : Fin D.u => D.shiftedResidue r 1) := by
  intro r s h
  have hm : r.val+D.m ≡ s.val+D.m [MOD D.u] := by
    change (r.val+D.m)%D.u=(s.val+D.m)%D.u
    have hv := congrArg Fin.val h
    simpa only [shiftedResidue,one_mul] using hv
  have hc := Nat.ModEq.add_right_cancel (show D.m ≡ D.m [MOD D.u] from rfl) hm
  apply Fin.ext
  simpa only [Nat.ModEq,Nat.mod_eq_of_lt r.isLt,Nat.mod_eq_of_lt s.isLt] using hc

noncomputable def shiftOneEquiv : Fin D.u ≃ Fin D.u :=
  Equiv.ofBijective (fun r => D.shiftedResidue r 1)
    ⟨D.shiftedResidue_one_injective,Finite.surjective_of_injective D.shiftedResidue_one_injective⟩

theorem carry_sum_one : (∑ r : Fin D.u,D.carry r 1)=D.m := by
  have he := Finset.sum_congr (s₁:=Finset.univ) rfl (fun r _ => D.carry_eq r 1)
  simp only [one_mul,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    smul_eq_mul,←Finset.mul_sum] at he
  have hp := D.shiftOneEquiv.sum_comp (fun r => r.val)
  change (∑ r : Fin D.u,(D.shiftedResidue r 1).val)=(∑ r : Fin D.u,r.val) at hp
  rw [hp] at he
  apply Nat.eq_of_mul_eq_mul_left D.u_pos
  omega

/-- Natural arithmetic expression for ceil((m-s)/u), with 0<=s<u<m. -/
def residueCeiling (s : Fin D.u) : ℕ := (D.m+D.u-1-s.val)/D.u

theorem residueCeiling_shift (r : Fin D.u) : D.residueCeiling (D.shiftedResidue r 1)=D.carry r 1 := by
  have hc := D.carry_eq r 1
  simp only [one_mul] at hc
  have hr := r.isLt
  have hs := (D.shiftedResidue r 1).isLt
  have hu := D.u_pos
  have hm := D.u_lt
  have hN : D.m+D.u-1-(D.shiftedResidue r 1).val+(D.shiftedResidue r 1).val+1=D.m+D.u := by omega
  unfold residueCeiling
  apply Nat.div_eq_of_lt_le <;> nlinarith

theorem residueCeiling_sum : (∑ s : Fin D.u,D.residueCeiling s)=D.m := by
  rw [←D.shiftOneEquiv.sum_comp (D.residueCeiling)]
  change (∑ r : Fin D.u,D.residueCeiling (D.shiftedResidue r 1))=D.m
  simp_rw [D.residueCeiling_shift]
  exact D.carry_sum_one

theorem epsilon_sum_add_one : (∑ r : Fin D.u,D.epsilon r)+1=D.u := by
  have he (r : Fin D.u) : D.epsilon r+(if r.val=0 then 1 else 0)=1 := by
    unfold epsilon
    split_ifs <;> omega
  have hs := Finset.sum_congr (s₁:=Finset.univ) rfl (fun r _ => he r)
  rw [Finset.sum_add_distrib] at hs
  have hz : (∑ r : Fin D.u,if r.val=0 then 1 else 0)=1 := by
    have hh (r : Fin D.u) : r.val=0 ↔ r=⟨0,D.u_pos⟩ := ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
    simp only [hh,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simpa only [hz,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] using hs

theorem wordVolume_coordinates : D.wordVolume=
    (∑ r : Fin D.u,((D.shortestPoint r).1+(D.shortestPoint r).2))+D.u := by
  have hs := Finset.sum_congr (s₁:=Finset.univ) rfl (fun r _ => D.shortestPoint_degree r)
  rw [Finset.sum_add_distrib] at hs
  have he := D.epsilon_sum_add_one
  unfold wordVolume
  rw [←hs]
  omega
end NSP14.Endpoint.Data
