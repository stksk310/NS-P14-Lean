module
public import NSP14.Endpoint.Coordinates
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

/-- Equality of actual numerical exponents forces every longer core
representation to be one of the j-th competitors, with j>=1. -/
theorem longer_core_pair (p q : D.corePoints) (hv : D.coreValue p=D.coreValue q)
    (hl : D.coreDegree p<D.coreDegree q) :
    ∃ j : ℕ,1≤j ∧ D.coreDegree q=D.coreDegree p+j*D.d ∧
      D.coreOffset p=D.coreOffset q+j*D.m := by
  have he := congrArg Subtype.val hv
  change D.coreDegree p*D.m+D.coreOffset p*D.d=
    D.coreDegree q*D.m+D.coreOffset q*D.d at he
  have hm : D.coreDegree p*D.m ≡ D.coreDegree q*D.m [MOD D.d] := by
    have h := congrArg (fun n => n%D.d) he
    change (D.coreDegree p*D.m)%D.d=(D.coreDegree q*D.m)%D.d
    simpa only [Nat.add_mod,Nat.mul_mod_left,Nat.add_zero,Nat.mod_mod] using h
  have hc := hm.cancel_right_of_coprime D.coprime.symm.gcd_eq_one
  obtain ⟨j,hj⟩ := hc.dvd'
  have hsub := Nat.sub_add_cancel hl.le
  have hdeg : D.coreDegree q=D.coreDegree p+j*D.d := by nlinarith only [hj,hsub]
  have hjpos : 1≤j := by
    by_cases hj0 : j=0
    · simp only [hj0,zero_mul,add_zero] at hdeg
      omega
    · omega
  refine ⟨j,hjpos,hdeg,?_⟩
  rw [hdeg] at he
  apply Nat.eq_of_mul_eq_mul_left D.d_pos
  nlinarith only [he]

/-- All competitors, not merely j=1, characterize the actual kernel.
The longer pair must itself belong to the genuine core. -/
theorem core_dead_iff_competitor (p : D.corePoints) :
    D.coreDegree p<D.source.order (D.coreValue p).val ↔
      ∃ j : ℕ,1≤j ∧ ∃ q : D.corePoints,
        D.coreDegree q=D.coreDegree p+j*D.d ∧ D.coreOffset p=D.coreOffset q+j*D.m := by
  constructor
  · intro hp
    obtain ⟨q,hqd,hqv⟩ := D.exists_corePoint (D.coreValue p)
    obtain ⟨j,hj,hd,hB⟩ := D.longer_core_pair p q hqv.symm (by omega)
    exact ⟨j,hj,q,hd,hB⟩
  · rintro ⟨j,hj,q,hd,hB⟩
    have hv : D.coreValue q=D.coreValue p := by
      apply Subtype.ext
      change D.coreDegree q*D.m+D.coreOffset q*D.d=
        D.coreDegree p*D.m+D.coreOffset p*D.d
      rw [hd,hB]
      ring
    have hb := D.coreDegree_le_order q
    rw [hv] at hb
    have hpos : 0 < j*D.d := Nat.mul_pos (by omega) (by have := D.d_pos;omega)
    omega
end NSP14.Endpoint.Data
