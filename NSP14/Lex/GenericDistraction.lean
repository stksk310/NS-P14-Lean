module
public import NSP14.Lex.DistractionMonomial
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators

namespace NSP14.Lex
variable (k : Type) [CommRing k] (q : ℕ)
abbrev DistractionParameter := Fin q × ℕ × Fin q
abbrev GenericCoefficientRing := MvPolynomial (DistractionParameter q) k

noncomputable def genericLinearRaw (i : Fin q) (n : ℕ) : MvPolynomial (Fin q) (GenericCoefficientRing k q) :=
  ∑ j : Fin q,MvPolynomial.C (MvPolynomial.X (i,n,j))*MvPolynomial.X j

noncomputable def diagonalParameterMap : GenericCoefficientRing k q →+* k :=
  MvPolynomial.eval₂Hom (RingHom.id k) (fun p => if p.1=p.2.2 then 1 else 0)

theorem genericLinearRaw_specialize (i : Fin q) (n : ℕ) :
    MvPolynomial.map (diagonalParameterMap k q) (genericLinearRaw k q i n)=MvPolynomial.X i := by
  simp [genericLinearRaw,diagonalParameterMap,apply_ite]

theorem genericLinearRaw_homogeneous (i : Fin q) (n : ℕ) :
    (genericLinearRaw k q i n).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

noncomputable def genericRawMatrix (a : Fin q →₀ ℕ) : Matrix (Fin q) (Fin q) (GenericCoefficientRing k q) :=
  fun r i => MvPolynomial.X (i,a i,r)

theorem genericRawMatrix_specialize (a : Fin q →₀ ℕ) :
    (genericRawMatrix k q a).map (diagonalParameterMap k q)=1 := by
  ext r i
  simp [genericRawMatrix,diagonalParameterMap,Matrix.one_apply,eq_comm]

variable [Nontrivial k]
theorem genericRawMatrix_det_ne_zero (a : Fin q →₀ ℕ) : (genericRawMatrix k q a).det ≠ 0 := by
  have hd : diagonalParameterMap k q ((genericRawMatrix k q a).det)=1 := by
    rw [(diagonalParameterMap k q).map_det]
    change ((genericRawMatrix k q a).map (diagonalParameterMap k q)).det=1
    rw [genericRawMatrix_specialize,Matrix.det_one]
  intro he
  rw [he,map_zero] at hd
  exact zero_ne_one hd
end NSP14.Lex

namespace NSP14.Lex
variable (k : Type) [CommRing k] (q : ℕ)

noncomputable def genericRawDistraction (a : Fin q →₀ ℕ) : MvPolynomial (Fin q) (GenericCoefficientRing k q) :=
  distractionMonomial (GenericCoefficientRing k q) q (genericLinearRaw k q) a

theorem genericRawDistraction_specialize (a : Fin q →₀ ℕ) :
    MvPolynomial.map (diagonalParameterMap k q) (genericRawDistraction k q a)=MvPolynomial.monomial a 1 := by
  unfold genericRawDistraction distractionMonomial
  simp only [map_prod,genericLinearRaw_specialize]
  exact distractionMonomial_variables k q a

abbrev PolynomialDegreeIndex (n : ℕ) := {a : Fin q →₀ ℕ //a.degree=n}

noncomputable instance polynomialDegreeIndex_finite (n : ℕ) : Finite (PolynomialDegreeIndex q n) := by
  let : Finite {a : Fin q →₀ ℕ //a.degree≤n} := (Finsupp.finite_of_degree_le n).to_subtype
  let f : PolynomialDegreeIndex q n → {a : Fin q →₀ ℕ //a.degree≤n} := fun a => ⟨a.val,a.property.le⟩
  exact Finite.of_injective f (fun a b h => Subtype.ext
    (congrArg (fun z : {a : Fin q →₀ ℕ //a.degree≤n} => z.val) h))

noncomputable instance polynomialDegreeIndex_fintype (n : ℕ) : Fintype (PolynomialDegreeIndex q n) :=
  Fintype.ofFinite _

noncomputable def genericRawDegreeMatrix (n : ℕ) :
    Matrix (PolynomialDegreeIndex q n) (PolynomialDegreeIndex q n) (GenericCoefficientRing k q) :=
  fun r s => (genericRawDistraction k q s.val).coeff r.val

theorem genericRawDegreeMatrix_specialize (n : ℕ) :
    (genericRawDegreeMatrix k q n).map (diagonalParameterMap k q)=1 := by
  ext r s
  have he := congrArg (fun p : MvPolynomial (Fin q) k => p.coeff r.val)
    (genericRawDistraction_specialize k q s.val)
  rw [MvPolynomial.coeff_map,MvPolynomial.coeff_monomial] at he
  change diagonalParameterMap k q ((genericRawDistraction k q s.val).coeff r.val)=_
  rw [he]
  by_cases hrs : r=s
  · subst s
    simp only [Matrix.one_apply,ite_true]
  · have hn : s.val ≠ r.val := fun h => hrs (Subtype.ext h.symm)
    simp only [Matrix.one_apply,ite_eq_right hrs,ite_eq_right hn]

variable [Nontrivial k]
theorem genericRawDegreeMatrix_det_ne_zero (n : ℕ) : (genericRawDegreeMatrix k q n).det ≠ 0 := by
  have hd : diagonalParameterMap k q ((genericRawDegreeMatrix k q n).det)=1 := by
    rw [(diagonalParameterMap k q).map_det]
    change ((genericRawDegreeMatrix k q n).map (diagonalParameterMap k q)).det=1
    rw [genericRawDegreeMatrix_specialize,Matrix.det_one]
  intro he
  rw [he,map_zero] at hd
  exact zero_ne_one hd
end NSP14.Lex
