module

public import NSP14.Semigroup.SquareZeroCut

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open scoped Classical BigOperators

namespace NSP14.NumericalSemigroup


variable (S : NSP14.NumericalSemigroup)

noncomputable def nonXAtomAperyOneEquiv : S.NonXAtom ≃ S.AperyDegreeExponent 1 where
  toFun a := ⟨⟨a.val,S.atom_apery a.property.1 a.property.2⟩,S.atom_order a.property.1⟩
  invFun a := ⟨a.val.val,(S.order_one_iff_atom a.val.val.property).1 a.property,
    fun h => S.multiplicity_not_apery (h ▸ a.val.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable (k : Type*) [Field k]

/-- Coefficients in the independent S₀ variables, not algebraic independence
of their images in A. -/
noncomputable def headLinearCoordinates : S.headDegree k 1 ≃ₗ[k] (S.NonXAtom → k) :=
  (S.lowDegreeQuotientEquiv k 1 (by decide)).trans
    ((S.qDegreeEquiv k 1).trans ((Finsupp.domLCongr S.nonXAtomAperyOneEquiv.symm).trans
      (Finsupp.linearEquivFunOnFinite k k S.NonXAtom)))

theorem headLinearCoordinates_apply (a : S.headDegree k 1) (x : S.NonXAtom) :
    S.headLinearCoordinates k a x =
      S.headQuotientEquiv k a.val ⟨x.val,S.apery_head (S.atom_apery x.property.1 x.property.2)⟩ := by
  simp only [headLinearCoordinates, LinearEquiv.trans_apply, Finsupp.linearEquivFunOnFinite_apply,
    Finsupp.domLCongr_apply, Finsupp.domCongr_apply]
  change S.aperyQuotientEquiv k (Ideal.Quotient.mk (S.nonAperyIdeal k) a.val)
    ⟨x.val,S.atom_apery x.property.1 x.property.2⟩ = _
  rw [S.aperyQuotientEquiv_mk, S.aperyProjection_apply]

noncomputable def linearFormPolynomial (c : S.NonXAtom → k) : S.PolynomialRing k :=
  ∑ x : S.NonXAtom, MvPolynomial.C (c x) * MvPolynomial.X x

noncomputable def linearAtom (x : S.NonXAtom) : S.headDegree k 1 :=
  ⟨S.headMonomial k x.val,S.headMonomial_mem_degree k x.val 1 (S.atom_order x.property.1)⟩

/-- Actual linear combinations in the degree-one space. -/
noncomputable def linearHeadMap : (S.NonXAtom → k) →ₗ[k] S.headDegree k 1 :=
  Fintype.linearCombination k (S.linearAtom k)

theorem headLinearCoordinates_linearAtom (x : S.NonXAtom) :
    S.headLinearCoordinates k (S.linearAtom k x) = Pi.single x 1 := by
  funext y
  rw [S.headLinearCoordinates_apply]
  change S.headQuotientEquiv k (S.headMonomial k x.val) _ = _
  rw [S.headMonomial_coordinates]
  by_cases h : x = y
  · subst y; simp
  · have hv : x.val ≠ y.val := fun he => h (Subtype.ext he)
    simp [h,hv]

theorem headLinearCoordinates_linearHeadMap (c : S.NonXAtom → k) :
    S.headLinearCoordinates k (S.linearHeadMap k c) = c := by
  change S.headLinearCoordinates k (∑ x : S.NonXAtom, c x • S.linearAtom k x) = c
  rw [map_sum]
  simp only [map_smul,S.headLinearCoordinates_linearAtom]
  funext y
  simp [Pi.single,Function.update_apply]

theorem linearHeadMap_val (c : S.NonXAtom → k) :
    (S.linearHeadMap k c).val = ∑ x : S.NonXAtom, c x • S.headMonomial k x.val := by
  change (S.headDegree k 1).subtype (∑ x : S.NonXAtom, c x • S.linearAtom k x) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro x _
  exact (S.headDegree k 1).subtype.map_smul (c x) (S.linearAtom k x)

theorem linearHeadMap_coordinates (a : S.headDegree k 1) :
    S.linearHeadMap k (S.headLinearCoordinates k a) = a :=
  (S.headLinearCoordinates k).injective (S.headLinearCoordinates_linearHeadMap k _)

theorem polynomialToA_linearForm (c : S.NonXAtom → k) :
    S.polynomialToA k (S.linearFormPolynomial k c) = (S.linearHeadMap k c).val := by
  rw [S.linearHeadMap_val]
  simp only [linearFormPolynomial,map_sum,map_mul,S.polynomialToA_X]
  apply Finset.sum_congr rfl
  intro x _
  change S.polynomialToA k (MvPolynomial.C (c x)) * S.headMonomial k x.val =
    c x • S.headMonomial k x.val
  erw [(S.polynomialToA k).commutes]
  exact (Algebra.smul_def (c x) (S.headMonomial k x.val)).symm

variable {S k}

/-- The same selected actual form is lifted to the non-x polynomial ring. -/
noncomputable def LinearCutData.polynomialForm (C : S.LinearCutData k) (i : Fin S.actualCutRank) :
    S.PolynomialRing k := S.linearFormPolynomial k (S.headLinearCoordinates k (C.forms i))

theorem LinearCutData.polynomialForm_image (C : S.LinearCutData k) (i : Fin S.actualCutRank) :
    S.polynomialToA k (C.polynomialForm i) = (C.forms i).val := by
  rw [LinearCutData.polynomialForm,S.polynomialToA_linearForm,S.linearHeadMap_coordinates]

end NSP14.NumericalSemigroup
