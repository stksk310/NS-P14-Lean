module
public import NSP14.ArithmeticSequence.Apery
public import NSP14.ArithmeticSequence.ConeRegular
public import NSP14.Semigroup.RegularHeadBetti
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open NSP14.Homological
namespace NSP14.ArithmeticSequence.Data
variable (D : ArithmeticSequence.Data)

theorem maximalEmbedding_head_order (hv : D.v=D.m-1) (h : D.source.HeadExponent) :
    D.source.order h.val.val≤1 := by
  have ha := (D.head_iff_apery h.val.val).mp h.property
  obtain ⟨i,hi,he⟩ := (D.mem_apery_iff h.val.val).mp ha
  rw [he,D.aperyValue_order i hi]
  apply (D.blockCount_le_iff i 1).mpr
  rw [hv,Nat.mul_one]
  omega

variable (k : Type) [Field k]

theorem maximalEmbedding_high_two (hv : D.v=D.m-1) : D.source.highIdeal k 2=⊥ := by
  apply bot_unique
  intro a ha
  change a=0
  apply (D.source.headQuotientEquiv k).injective
  ext h
  rw [map_zero,Finsupp.zero_apply]
  exact (Finsupp.mem_supported' k _).mp ha h (by change ¬2 ≤ D.source.order h.val.val;have := D.maximalEmbedding_head_order hv h;omega)

theorem maximalEmbedding_betti_zero (hv : D.v=D.m-1) :
    totalBetti k D.source.AtomExponent (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.TangentAlgebra k)) 0=1 :=
  D.source.xRegular_squareZero_betti_zero k (D.xMultiply_injective k) (D.maximalEmbedding_high_two k hv)

/-- Includes every positive common difference; this special AP case does
not claim the general AP Betti formula for smaller embedding dimension. -/
theorem maximalEmbedding_betti (hv : D.v=D.m-1) (i : ℕ) (hi : 1 ≤ i) :
    totalBetti k D.source.AtomExponent (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.TangentAlgebra k)) i=
      i*D.m.choose (i+1) := by
  rw [D.source.xRegular_squareZero_betti k (D.xMultiply_injective k) (D.maximalEmbedding_high_two k hv) i hi,
    D.embeddingDimension,hv,Nat.sub_add_cancel (by have := D.m_two;omega)]
end NSP14.ArithmeticSequence.Data
