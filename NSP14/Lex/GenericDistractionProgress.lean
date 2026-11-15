module
public import NSP14.Lex.GenericDistractionStep
public import NSP14.Lex.GenericDistractionPrincipal
@[expose] public section
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)

abbrev MonomialPrefix (I : Ideal (MvPolynomial (Fin q) k)) (n : ℕ)
    (v : PolynomialDegreeIndex q n) :=
  {a : PolynomialDegreeIndex q n //
    MonomialOrder.degLex.toSyn v.val≤MonomialOrder.degLex.toSyn a.val ∧
      MvPolynomial.monomial a.val (1:k)∈I}

/-- Within a fixed homogeneous degree, the coefficients on the actual initial
ideal's prefix determine the whole prefix of an actual ideal element. -/
theorem initialPrefix_coeff_zero (J : Ideal (MvPolynomial (Fin q) k))
    (n : ℕ) (v : PolynomialDegreeIndex q n) (f : MvPolynomial (Fin q) k)
    (hf : f.IsHomogeneous n) (hmem : f∈J)
    (hz : ∀ a : MonomialPrefix k q (initialIdeal k q MonomialOrder.degLex J) n v,
      f.coeff a.val.val=0)
    (a : PolynomialDegreeIndex q n)
    (ha : MonomialOrder.degLex.toSyn v.val≤MonomialOrder.degLex.toSyn a.val) : f.coeff a.val=0 := by
  by_contra hn
  have hf0 : f≠0 := by intro h; simp [h] at hn
  let d := MonomialOrder.degLex.degree f
  have hdne : f.coeff d≠0 := MonomialOrder.degLex.coeff_degree_ne_zero_iff.mpr hf0
  have hdeg : d.degree=n := by
    by_contra he
    exact hdne (hf.coeff_eq_zero he)
  have hdle : MonomialOrder.degLex.toSyn v.val≤MonomialOrder.degLex.toSyn d :=
    ha.trans (MonomialOrder.degLex.le_degree (MvPolynomial.mem_support_iff.mpr hn))
  have hdin : MvPolynomial.monomial d (1:k)∈initialIdeal k q MonomialOrder.degLex J :=
    Ideal.subset_span ⟨d,⟨f,hmem,hf0,rfl⟩,rfl⟩
  exact hdne (hz ⟨⟨d,hdeg⟩,hdle,hdin⟩)


local notation "K" => GenericDistractionField k q

def monomialPrefixCard (I : Ideal (MvPolynomial (Fin q) k)) (n : ℕ)
    (v : PolynomialDegreeIndex q n) : ℕ := Fintype.card (MonomialPrefix k q I n v)

/-- Any actual nonzero generic degree minor bounds the actual initial prefix. -/
theorem genericMonomialStep_prefixCard_of_minor (I : Ideal (MvPolynomial (Fin q) k))
    (n : ℕ) (v : PolynomialDegreeIndex q n)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (r c : ι ↪ PolynomialDegreeIndex q n)
    (hcol : ∀ b,MvPolynomial.monomial (c b).val (1:k)∈I)
    (hrow : ∀ b,MonomialOrder.degLex.toSyn v.val≤MonomialOrder.degLex.toSyn (r b).val)
    (hdet : ((genericFieldDegreeMatrix k q n).submatrix r c).det≠0) :
    Fintype.card ι≤monomialPrefixCard K q (genericMonomialStep k q I) n v := by
  let T := MonomialPrefix K q (genericMonomialStep k q I) n v
  let A : Matrix T ι K := fun t b => (genericFieldDistraction k q (c b).val).coeff t.val.val
  let f := A.mulVecLin
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot,LinearMap.ker_eq_bot']
    intro z hz
    let p : MvPolynomial (Fin q) K := ∑ b : ι,z b • genericFieldDistraction k q (c b).val
    have hp : p.IsHomogeneous n := by
      rw [← MvPolynomial.mem_homogeneousSubmodule]
      apply Submodule.sum_mem
      intro b _
      apply Submodule.smul_mem
      rw [MvPolynomial.mem_homogeneousSubmodule]
      simpa only [(c b).property] using genericFieldDistraction_homogeneous k q (c b).val
    have hmem : p∈genericDistractionIdeal k q (monomialExtension k K q I) := by
      change p∈genericDistractionSpace k q (monomialExtension k K q I)
      apply Submodule.sum_mem
      intro b _
      apply Submodule.smul_mem
      exact genericDistractionSpace_monomial k q _ (c b).val
        ((monomialExtension_mem_iff k K q I (c b).val).mpr (hcol b))
    have hzT (t : T) : p.coeff t.val.val=0 := by
      have hh := congrFun hz t
      simpa only [f,Matrix.mulVecLin_apply,A,Matrix.mulVec,dotProduct,p,MvPolynomial.coeff_sum,
        MvPolynomial.coeff_smul,smul_eq_mul,mul_comm,Pi.zero_apply] using hh
    have hzR (b : ι) : p.coeff (r b).val=0 :=
      initialPrefix_coeff_zero K q _ n v p hp hmem hzT (r b) (hrow b)
    let E : (ι → K) ≃ₗ[K] (ι → K) :=
      Matrix.toLinearEquiv (Pi.basisFun _ _) ((genericFieldDegreeMatrix k q n).submatrix r c)
        (isUnit_iff_ne_zero.mpr hdet)
    have he (b : ι) : E z b=p.coeff (r b).val := by
      simp only [E,Matrix.toLinearEquiv_apply,Matrix.toLin_eq_toLin',
        Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Matrix.submatrix_apply,
        genericFieldDegreeMatrix_entry,p,MvPolynomial.coeff_sum,MvPolynomial.coeff_smul,smul_eq_mul,mul_comm]
    apply E.injective
    rw [map_zero]
    funext b
    exact (he b).trans (hzR b)
  have hd := LinearMap.finrank_le_finrank_of_injective hinj
  simpa only [Module.finrank_pi,monomialPrefixCard,T] using hd

/-- Actual prefix counts cannot decrease under the actual generic operation. -/
theorem genericMonomialStep_prefixCard_le (I : Ideal (MvPolynomial (Fin q) k))
    (n : ℕ) (v : PolynomialDegreeIndex q n) :
    monomialPrefixCard k q I n v≤monomialPrefixCard K q (genericMonomialStep k q I) n v := by
  let S := MonomialPrefix k q I n v
  let e : S ↪ PolynomialDegreeIndex q n := ⟨Subtype.val,Subtype.val_injective⟩
  exact genericMonomialStep_prefixCard_of_minor k q I n v e e (fun b => b.property.2)
    (fun b => b.property.1) (genericFieldDegreeMatrix_principal_det_ne_zero k q n e)

theorem genericFieldDegreeMatrix_minor_det_ne_zero_of_specialize
    (n : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (r c : ι ↪ PolynomialDegreeIndex q n) {L : Type} [CommRing L]
    (φ : GenericCoefficientRing k q →+* L)
    (hd : (((genericRawDegreeMatrix k q n).submatrix r c).map φ).det≠0) :
    ((genericFieldDegreeMatrix k q n).submatrix r c).det≠0 := by
  have hraw : ((genericRawDegreeMatrix k q n).submatrix r c).det≠0 := by
    intro he
    apply hd
    have hh := φ.map_det ((genericRawDegreeMatrix k q n).submatrix r c)
    change φ (((genericRawDegreeMatrix k q n).submatrix r c).det)=
      (((genericRawDegreeMatrix k q n).submatrix r c).map φ).det at hh
    rw [← hh,he,map_zero]
  change (((genericRawDegreeMatrix k q n).map (algebraMap _ _)).submatrix r c).det≠0
  rw [Matrix.submatrix_map]
  have he := (algebraMap (GenericCoefficientRing k q) K).map_det
    ((genericRawDegreeMatrix k q n).submatrix r c)
  change algebraMap _ _ (((genericRawDegreeMatrix k q n).submatrix r c).det)=
    (((genericRawDegreeMatrix k q n).submatrix r c).map (algebraMap _ _)).det at he
  rw [← he]
  exact fun h => hraw ((IsFractionRing.injective (GenericCoefficientRing k q) K)
    (h.trans (map_zero _).symm))
end NSP14.Lex
