module
public import NSP14.Endpoint.CoreGeneration
public import NSP14.Homological.GradedCyclicPresentation
public import NSP14.Homological.RelabelRegularGrading
public import NSP14.Lex.LexExistence
public import NSP14.Lex.TotalBettiComparison
@[expose] public section
open scoped Classical BigOperators
open CategoryTheory CategoryTheory.Limits NSP14.Homological
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

def coreFinVariables : Fin D.q ≃ D.a := Fintype.equivOfCardEq (by
  simp only [Fintype.card_fin,Fintype.card_coe]
  rfl)
def coreFinMap : MvPolynomial (Fin D.q) k →ₐ[k] D.QCore k :=
  relabeledRegularMap k (Fin D.q) D.a (D.QCore k) (D.internalToQCore k) D.coreFinVariables

def coreFinGrading : GradedPolynomialModule k (Fin D.q) (polynomialRegularModule k (Fin D.q) (D.QCore k) (D.coreFinMap k)) :=
  relabeledRegularGrading k (Fin D.q) D.a (D.QCore k) (D.internalToQCore k) D.coreFinVariables (D.QCoreGrading k)

theorem coreFinMap_surjective : Function.Surjective (D.coreFinMap k) :=
  (D.internalToQCore_surjective k).comp (MvPolynomial.renameEquiv k D.coreFinVariables).surjective

theorem coreFinUnit_degree :
    (regularRestrictionCoefficientEquiv k (Fin D.q) (D.QCore k) (D.coreFinMap k)).symm 1∈(D.coreFinGrading k).degreeSpace 0 := by
  apply relabeledRegularGrading_unit k (Fin D.q) D.a (D.QCore k) (D.internalToQCore k) D.coreFinVariables (D.QCoreGrading k)
  exact D.QCoreUnit_degree_zero k

def coreFinKernel : Ideal (MvPolynomial (Fin D.q) k) := RingHom.ker (D.coreFinMap k).toRingHom

theorem coreFinKernel_homogeneous :
    (D.coreFinKernel k).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin D.q) k) :=
  NSP14.Endpoint.gradedUnit_kernel_homogeneous k (Fin D.q) (D.QCore k) (D.coreFinMap k) (D.coreFinGrading k) (D.coreFinUnit_degree k)

theorem coreFinKernel_Hilbert (n : ℕ) :
    Lex.quotientHilbert k D.q (D.coreFinKernel k) (D.coreFinKernel_homogeneous k) n=D.coreHilbert k n := by
  exact NSP14.Endpoint.gradedUnit_quotientHilbert k (Fin D.q) (D.QCore k) (D.coreFinMap k) (D.coreFinGrading k)
    (D.coreFinMap_surjective k) (D.coreFinUnit_degree k) n

theorem coreFinKernel_totalBetti (i : ℕ) :
    totalBetti k (Fin D.q) (NSP14.Endpoint.artinModule k (Fin D.q) (D.coreFinKernel k)) i=
      totalBetti k D.a (D.QCoreModule k) i := by
  have hb := totalBetti_iso k (Fin D.q)
    (NSP14.Endpoint.cyclicQuotientModuleIso k (Fin D.q) (D.QCore k) (D.coreFinMap k) (D.coreFinMap_surjective k)) i
  have hr := relabeledRegular_totalBetti k (Fin D.q) D.a (D.QCore k) (D.internalToQCore k) D.coreFinVariables i
  exact hb.trans hr

/-- One actual lex quotient over the original field, with the entire actual QC Hilbert function and actual total comparison. -/
theorem exists_core_lex : ∃ (L : Ideal (MvPolynomial (Fin D.q) k))
    (hL : L.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin D.q) k)),
    Lex.IsLex k D.q L ∧
    (∀ n,Lex.quotientHilbert k D.q L hL n=D.coreHilbert k n) ∧
    ∀ i : ℕ,1 ≤ i → totalBetti k D.a (D.QCoreModule k) i≤
      totalBetti k (Fin D.q) (NSP14.Endpoint.artinModule k (Fin D.q) L) i := by
  obtain ⟨L,hL,hlex,hHF⟩ := Lex.exists_lex_sameHilbert k D.q (D.coreFinKernel k) (D.coreFinKernel_homogeneous k)
  refine ⟨L,hL,hlex,fun n => (hHF n).symm.trans (D.coreFinKernel_Hilbert k n),?_⟩
  intro i hi
  rw [← D.coreFinKernel_totalBetti k i]
  exact Lex.quotientTotalBetti_le_lex k D.q (D.coreFinKernel k) L (D.coreFinKernel_homogeneous k) hL hlex hHF i hi
end NSP14.Endpoint.Data

