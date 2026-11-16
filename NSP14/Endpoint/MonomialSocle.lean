module
public import NSP14.Endpoint.MonomialCoordinates
public import NSP14.Endpoint.Corners
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Endpoint
variable (k : Type) [Field k] (U : Set (ℕ×ℕ))
  (hU : ∀ {a b},a∈U → a≤b → b∈U)

noncomputable def coordinateSocle : Submodule k (MvPolynomial (Fin 2) k ⧸ coordinateIdeal k U) :=
  ((LinearMap.mul k _).flip (Ideal.Quotient.mk _ (MvPolynomial.X 0))).ker⊓
    ((LinearMap.mul k _).flip (Ideal.Quotient.mk _ (MvPolynomial.X 1))).ker

include hU in
theorem coordinateSocle_support (a : coordinateSocle k U) (c : {c : ℕ×ℕ // c∉U})
    (hc : (coordinateQuotientBasis k U hU).repr a.val c≠0) : Corner U c.val := by
  obtain ⟨p,hp⟩ := Ideal.Quotient.mkₐ_surjective k (coordinateIdeal k U) a.val
  change Ideal.Quotient.mk (coordinateIdeal k U) p=a.val at hp
  have h0 : p*MvPolynomial.X 0∈coordinateIdeal k U := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_mul,hp]
    exact a.property.1
  have h1 : p*MvPolynomial.X 1∈coordinateIdeal k U := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_mul,hp]
    exact a.property.2
  have hcoeff : p.coeff (exponentPairEquiv c.val)≠0 := by
    rw [←coordinateQuotientBasis_repr_mk k U hU c p,hp]
    exact hc
  have hs0 : exponentPairEquiv c.val+Finsupp.single 0 1∈(p*MvPolynomial.X 0).support := by
    apply Finsupp.mem_support_iff.mpr
    rwa [MvPolynomial.coeff_mul_X]
  have hs1 : exponentPairEquiv c.val+Finsupp.single 1 1∈(p*MvPolynomial.X 1).support := by
    apply Finsupp.mem_support_iff.mpr
    rwa [MvPolynomial.coeff_mul_X]
  have ht0 := (coordinateIdeal_mem k U hU _).mp h0 _ hs0
  have ht1 := (coordinateIdeal_mem k U hU _).mp h1 _ hs1
  refine ⟨c.property,?_,?_⟩
  · simpa [exponentPairEquiv] using ht0
  · simpa [exponentPairEquiv] using ht1

noncomputable def coordinateSocleMap : coordinateSocle k U →ₗ[k]
    ({c : {c : ℕ×ℕ // c∉U} // Corner U c.val} →₀ k) where
  toFun a := ((coordinateQuotientBasis k U hU).repr a.val).subtypeDomain (fun c => Corner U c.val)
  map_add' a b := by
    change (((coordinateQuotientBasis k U hU).repr (a.val+b.val)).subtypeDomain _)=_
    rw [map_add,Finsupp.subtypeDomain_add]
  map_smul' r a := by
    change (((coordinateQuotientBasis k U hU).repr (r • a.val)).subtypeDomain _)=_
    rw [map_smul]
    ext c
    rfl

theorem coordinateSocleMap_injective : Function.Injective (coordinateSocleMap k U hU) := by
  intro a b h
  apply Subtype.ext
  apply (coordinateQuotientBasis k U hU).repr.injective
  ext c
  by_cases hc : Corner U c.val
  · exact congrArg (fun f => f ⟨c,hc⟩) h
  · have ha : (coordinateQuotientBasis k U hU).repr a.val c=0 := by
      by_contra hn
      exact hc (coordinateSocle_support k U hU a c hn)
    have hb : (coordinateQuotientBasis k U hU).repr b.val c=0 := by
      by_contra hn
      exact hc (coordinateSocle_support k U hU b c hn)
    rw [ha,hb]

noncomputable def cornerLabelEquiv : {c : {c : ℕ×ℕ // c∉U} // Corner U c.val} ≃ {c : ℕ×ℕ // Corner U c} where
  toFun c := ⟨c.val.val,c.property⟩
  invFun c := ⟨⟨c.val,c.property.1⟩,c.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

include hU in
theorem coordinateSocle_finite (c : ℕ×ℕ) (hc : c∈U) : Module.Finite k (coordinateSocle k U) := by
  have : Finite {a | Corner U a} := (corner_finite U hU c hc).to_subtype
  have : Finite {a : {a : ℕ×ℕ // a∉U} // Corner U a.val} := Finite.of_equiv _ (cornerLabelEquiv U).symm
  exact Module.Finite.of_injective (coordinateSocleMap k U hU) (coordinateSocleMap_injective k U hU)

include hU in
theorem coordinateSocle_finrank_bound (c : ℕ×ℕ) (hc : c∈U) :
    Module.finrank k (coordinateSocle k U)≤Nat.card {b | Minimal (·∈U) b}-1 := by
  have : Finite {a | Corner U a} := (corner_finite U hU c hc).to_subtype
  have : Finite {a : {a : ℕ×ℕ // a∉U} // Corner U a.val} := Finite.of_equiv _ (cornerLabelEquiv U).symm
  let : Fintype {a : {a : ℕ×ℕ // a∉U} // Corner U a.val} := Fintype.ofFinite _
  have hb := LinearMap.finrank_le_finrank_of_injective (coordinateSocleMap_injective k U hU)
  rw [Module.finrank_finsupp_self,Fintype.card_eq_nat_card,Nat.card_congr (cornerLabelEquiv U)] at hb
  have hlt := corner_card_lt_minimal U hU c hc
  change Nat.card {a : ℕ×ℕ // Corner U a}<Nat.card {b : ℕ×ℕ // Minimal (·∈U) b} at hlt
  change Module.finrank k (coordinateSocle k U)≤Nat.card {a : ℕ×ℕ // Corner U a} at hb
  change Module.finrank k (coordinateSocle k U)≤Nat.card {b : ℕ×ℕ // Minimal (·∈U) b}-1
  omega
end NSP14.Endpoint
