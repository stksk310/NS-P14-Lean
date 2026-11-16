module
public import NSP14.Lex.InitialIdeal
public import NSP14.Endpoint.InitialAction
public import NSP14.Endpoint.ArtinGradedChain
public import NSP14.Homological.CoordinateBaseChange
public import NSP14.Homological.CoordinateGradePieces
@[expose] public section
open scoped Classical TensorProduct
open CategoryTheory NSP14.Homological
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Lex
variable (k L : Type) [Field k] [Field L] (q : ℕ)

def monomialExtension (I : Ideal (MvPolynomial (Fin q) k)) : Ideal (MvPolynomial (Fin q) L) :=
  Ideal.span ((fun a => MvPolynomial.monomial a (1:L)) '' {a | MvPolynomial.monomial a (1:k)∈I})

theorem monomialExtension_mem_iff (I : Ideal (MvPolynomial (Fin q) k)) (a : Fin q →₀ ℕ) :
    MvPolynomial.monomial a (1:L)∈monomialExtension k L q I ↔ MvPolynomial.monomial a (1:k)∈I := by
  rw [monomialExtension,monomial_mem_span_iff]
  constructor
  · rintro ⟨b,hb,hle⟩
    exact monomial_mem_of_le k q I b a hb hle
  · intro ha
    exact ⟨a,ha,le_rfl⟩

theorem monomialExtension_isMonomial (I : Ideal (MvPolynomial (Fin q) k)) :
    IsMonomial L q (monomialExtension k L q I) := by
  intro f hf a ha
  obtain ⟨b,hb,hle⟩ := MvPolynomial.mem_ideal_span_monomial_image.mp hf a ha
  exact (monomialExtension_mem_iff k L q I a).mpr (monomial_mem_of_le k q I b a hb hle)

theorem monomialExtension_homogeneous (I : Ideal (MvPolynomial (Fin q) k)) :
    (monomialExtension k L q I).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) L) := by
  apply Ideal.homogeneous_span
  rintro _ ⟨a,_,rfl⟩
  exact ⟨a.degree,MvPolynomial.isHomogeneous_monomial (1:L) rfl⟩

theorem monomialExtension_standard (I : Ideal (MvPolynomial (Fin q) k))
    (hmono : IsMonomial k q I) :
    StandardExponent MonomialOrder.degLex (monomialExtension k L q I)=StandardExponent MonomialOrder.degLex I := by
  ext a
  rw [standardExponent_iff_not_mem L q (monomialExtension_isMonomial k L q I),
    monomialExtension_mem_iff,standardExponent_iff_not_mem k q hmono]

theorem monomialExtension_isLex (I : Ideal (MvPolynomial (Fin q) k)) (hlex : IsLex k q I) :
    IsLex L q (monomialExtension k L q I) := by
  refine ⟨monomialExtension_isMonomial k L q I,?_⟩
  intro v w hdeg hle hv
  rw [monomialExtension_mem_iff] at hv ⊢
  exact hlex.2 v w hdeg hle hv

theorem monomialExtension_sameHilbert (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hmono : IsMonomial k q I) (n : ℕ) :
    quotientHilbert k q I hI n=quotientHilbert L q (monomialExtension k L q I)
      (monomialExtension_homogeneous k L q I) n := by
  change Module.finrank k ({p : StandardExponent MonomialOrder.degLex I // (p.val.degree:ℤ)=(n:ℤ)} →₀ k)=
    Module.finrank L ({p : StandardExponent MonomialOrder.degLex (monomialExtension k L q I) //
      (p.val.degree:ℤ)=(n:ℤ)} →₀ L)
  rw [monomialExtension_standard k L q I hmono]
  let : Finite {p : StandardExponent MonomialOrder.degLex I // (p.val.degree:ℤ)=(n:ℤ)} :=
    standard_degree_finite k q I n
  let : Fintype {p : StandardExponent MonomialOrder.degLex I // (p.val.degree:ℤ)=(n:ℤ)} := Fintype.ofFinite _
  rw [Module.finrank_finsupp_self,Module.finrank_finsupp_self]

def monomialExtensionIndexEquiv (I : Ideal (MvPolynomial (Fin q) k)) (hmono : IsMonomial k q I) :
    StandardExponent MonomialOrder.degLex (monomialExtension k L q I) ≃
      StandardExponent MonomialOrder.degLex I :=
  Set.equivOfEq (monomialExtension_standard k L q I hmono)

def monomialExtensionCoordinates (I : Ideal (MvPolynomial (Fin q) k)) (hmono : IsMonomial k q I) :
    coefficientModule L (Fin q) (Endpoint.artinModule L (Fin q) (monomialExtension k L q I)) ≃ₗ[L]
      (StandardExponent MonomialOrder.degLex I →₀ L) :=
  (Endpoint.artinCoordinates L (Fin q) (monomialExtension k L q I)).trans
    (Finsupp.domLCongr (monomialExtensionIndexEquiv k L q I hmono))

theorem monomialExtensionCoordinates_apply (I : Ideal (MvPolynomial (Fin q) k)) (hmono : IsMonomial k q I)
    (z : coefficientModule L (Fin q) (Endpoint.artinModule L (Fin q) (monomialExtension k L q I)))
    (p : StandardExponent MonomialOrder.degLex I) :
    monomialExtensionCoordinates k L q I hmono z p=
      Endpoint.artinCoordinates L (Fin q) (monomialExtension k L q I) z
        ((monomialExtensionIndexEquiv k L q I hmono).symm p) := by
  exact Finsupp.equivMapDomain_apply _ _ _

theorem monomialExtensionCoordinates_single (I : Ideal (MvPolynomial (Fin q) k)) (hmono : IsMonomial k q I)
    (p : StandardExponent MonomialOrder.degLex I) :
    (monomialExtensionCoordinates k L q I hmono).symm (Finsupp.single p 1)=
      Ideal.Quotient.mk (monomialExtension k L q I) (MvPolynomial.monomial p.val 1) := by
  change (Endpoint.artinCoordinates L (Fin q) (monomialExtension k L q I)).symm
    ((Finsupp.domLCongr (R:=L) (M:=L) (monomialExtensionIndexEquiv k L q I hmono)).symm (Finsupp.single p 1))=_
  rw [Finsupp.domLCongr_symm,Finsupp.domLCongr_single]
  exact Endpoint.artinCoordinates_single L (Fin q) (monomialExtension k L q I)
    ((monomialExtensionIndexEquiv k L q I hmono).symm p)

theorem monomialExtension_variable (I : Ideal (MvPolynomial (Fin q) k)) (hmono : IsMonomial k q I)
    (x : Fin q) (p j : StandardExponent MonomialOrder.degLex I) :
    monomialExtensionCoordinates k L q I hmono
      ((MvPolynomial.X x : VariableRing L (Fin q)) •
        (monomialExtensionCoordinates k L q I hmono).symm (Finsupp.single p 1)) j=
      if p.val+Finsupp.single x 1=j.val then 1 else 0 := by
  rw [monomialExtensionCoordinates_apply]
  change Endpoint.artinCoordinates L (Fin q) (monomialExtension k L q I)
    ((MvPolynomial.X x : VariableRing L (Fin q)) •
      (Endpoint.artinCoordinates L (Fin q) (monomialExtension k L q I)).symm
        ((Finsupp.domLCongr (R:=L) (M:=L) (monomialExtensionIndexEquiv k L q I hmono)).symm (Finsupp.single p 1)))
          ((monomialExtensionIndexEquiv k L q I hmono).symm j)=_
  rw [Finsupp.domLCongr_symm,Finsupp.domLCongr_single,
    Endpoint.artin_variable_monomial L q _ (monomialExtension_isMonomial k L q I)]
  rfl

def monomialExtensionBasis (I : Ideal (MvPolynomial (Fin q) k)) (hmono : IsMonomial k q I) :
    Module.Basis (StandardExponent MonomialOrder.degLex I) L
      (coefficientModule L (Fin q) (Endpoint.artinModule L (Fin q) (monomialExtension k L q I))) :=
  Finsupp.basisSingleOne.map (monomialExtensionCoordinates k L q I hmono).symm

theorem monomialExtensionBasis_apply (I : Ideal (MvPolynomial (Fin q) k)) (hmono : IsMonomial k q I)
    (p : StandardExponent MonomialOrder.degLex I) :
    monomialExtensionBasis k L q I hmono p=
      Ideal.Quotient.mk (monomialExtension k L q I) (MvPolynomial.monomial p.val 1) :=
  monomialExtensionCoordinates_single k L q I hmono p

theorem monomialExtensionBasis_homogeneous (I : Ideal (MvPolynomial (Fin q) k)) (hmono : IsMonomial k q I)
    (p : StandardExponent MonomialOrder.degLex I) :
    monomialExtensionBasis k L q I hmono p∈
      (Endpoint.artinGrading L (Fin q) (monomialExtension k L q I)
        (monomialExtension_homogeneous k L q I)).degreeSpace (p.val.degree:ℤ) := by
  rw [monomialExtensionBasis_apply]
  exact Endpoint.artin_mk_homogeneous L (Fin q) _ _ _ _ (MvPolynomial.isHomogeneous_monomial 1 rfl)

variable [Algebra k L]
theorem monomialExtension_eq_map (I : Ideal (MvPolynomial (Fin q) k)) (hmono : IsMonomial k q I) :
    monomialExtension k L q I=I.map (MvPolynomial.map (algebraMap k L)) := by
  conv_rhs => rw [hmono.span k q,Ideal.map_span]
  simp only [monomialExtension,Set.image_image,MvPolynomial.map_monomial,map_one]

theorem monomialExtension_scalar_matrix (I : Ideal (MvPolynomial (Fin q) k))
    (hmono : IsMonomial k q I) (x : Fin q) (p j : StandardExponent MonomialOrder.degLex I) :
    monomialExtensionCoordinates k L q I hmono
      ((MvPolynomial.X x : VariableRing L (Fin q)) •
        (monomialExtensionCoordinates k L q I hmono).symm (Finsupp.single p 1)) j=
      algebraMap k L (Endpoint.artinCoordinates k (Fin q) I
        ((MvPolynomial.X x : VariableRing k (Fin q)) •
          (Endpoint.artinCoordinates k (Fin q) I).symm (Finsupp.single p 1)) j) := by
  rw [monomialExtension_variable,Endpoint.artin_variable_monomial k q I hmono]
  by_cases h : p.val+Finsupp.single x 1=j.val <;> simp [h]

def monomialExtensionBaseChangeIso (I : Ideal (MvPolynomial (Fin q) k)) (hmono : IsMonomial k q I) :
    polynomialBaseChangeModule k L (Fin q) (Endpoint.artinModule k (Fin q) I) ≅
      Endpoint.artinModule L (Fin q) (monomialExtension k L q I) :=
  coordinateBaseChangePolynomialIso k L (Fin q) (StandardExponent MonomialOrder.degLex I)
    (Endpoint.artinModule k (Fin q) I) (Endpoint.artinModule L (Fin q) (monomialExtension k L q I))
    (Endpoint.artinCoordinates k (Fin q) I) (monomialExtensionCoordinates k L q I hmono)
    (monomialExtension_scalar_matrix k L q I hmono)

theorem monomialExtensionBaseChangeIso_basis (I : Ideal (MvPolynomial (Fin q) k))
    (hmono : IsMonomial k q I) (p : StandardExponent MonomialOrder.degLex I) :
    (show coefficientModule L (Fin q) (Endpoint.artinModule L (Fin q) (monomialExtension k L q I)) from
      (monomialExtensionBaseChangeIso k L q I hmono).hom
        ((1:L) ⊗ₜ[k] Endpoint.artinMonomialBasis k q I p))=
      monomialExtensionBasis k L q I hmono p := by
  apply (monomialExtensionCoordinates k L q I hmono).injective
  ext j
  have hbk : Endpoint.artinCoordinates k (Fin q) I (Endpoint.artinMonomialBasis k q I p)=Finsupp.single p 1 := by
    change (Endpoint.artinCoordinates k (Fin q) I)
      ((Endpoint.artinCoordinates k (Fin q) I).symm (Finsupp.single p 1))=_
    exact LinearEquiv.apply_symm_apply _ _
  have hbL : monomialExtensionCoordinates k L q I hmono (monomialExtensionBasis k L q I hmono p)=
      Finsupp.single p 1 := by
    change (monomialExtensionCoordinates k L q I hmono)
      ((monomialExtensionCoordinates k L q I hmono).symm (Finsupp.single p 1))=_
    exact LinearEquiv.apply_symm_apply _ _
  dsimp only [monomialExtensionBaseChangeIso]
  rw [coordinateBaseChangePolynomialIso_tmul,hbk,hbL,mul_one]
  by_cases hp : p=j <;> simp only [Finsupp.single_apply,hp,ite_true,ite_false,map_one,map_zero]
end NSP14.Lex
