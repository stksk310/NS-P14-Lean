module
public import NSP14.ArithmeticSequence.Apery
public import NSP14.ArithmeticSequence.ConeRegular
@[expose] public section
namespace NSP14.ArithmeticSequence.Data
variable (D : NSP14.ArithmeticSequence.Data)

/-- Every product which survives in the actual AP multiplicity quotient
has its original additive order. This includes arbitrary semigroup factors. -/
theorem order_add_of_sum_apery {x y : ℕ} (hx : x ∈ D.source) (hy : y ∈ D.source)
    (hxy : x+y ∈ D.source.aperySet) :
    D.source.order (x+y)=D.source.order x+D.source.order y := by
  obtain ⟨n,i,hi,hni,hx'⟩ := D.canonical_representation hx
  obtain ⟨p,j,hj,hpj,hy'⟩ := D.canonical_representation hy
  have hij : i+j < D.m := by
    by_contra hn
    have hm : D.m ≤ i+j := by omega
    have hd := D.d_pos
    have hc : i+j-D.m ≤ D.v*(n+p+D.d-1) := by
      have hs : i+j ≤ D.v*(n+p) := by nlinarith
      have hp' : n+p ≤ n+p+D.d-1 := by omega
      exact (Nat.sub_le _ _).trans (hs.trans (Nat.mul_le_mul_left D.v hp'))
    have hmem : (n+p+D.d-1)*D.m+(i+j-D.m)*D.d ∈ D.source :=
      ⟨n+p+D.d-1,i+j-D.m,hc,rfl⟩
    apply D.source.apery_no_predecessor hxy
    rw [D.multiplicity]
    refine ⟨_,hmem,?_⟩
    nlinarith [Nat.sub_add_cancel hm,
      Nat.sub_add_cancel (show 1 ≤ n+p+D.d by omega)]
  have hnij : i+j ≤ D.v*(n+p) := by nlinarith
  have he : x+y=(n+p)*D.m+(i+j)*D.d := by rw [hx',hy'];ring
  rw [he,D.canonical_order (n+p) (i+j) hij hnij,
    hx',hy',D.canonical_order n i hi hni,D.canonical_order p j hj hpj]
end NSP14.ArithmeticSequence.Data
