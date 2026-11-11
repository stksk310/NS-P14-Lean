module
public import NSP14.Endpoint.CoreInternalAction
public import NSP14.Endpoint.BasisGrading
public import NSP14.Endpoint.Compensation
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open CategoryTheory CategoryTheory.Limits NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

noncomputable def QCoreModuleCoordinates : coefficientModule k D.a (D.QCoreModule k) ≃ₗ[k]
    (D.CoreMinimalIndex →₀ k) := (D.QCoreCoefficientEquiv k).trans (D.QCoreCoordinates k)

def QCoreDegree (p : D.CoreMinimalIndex) : ℤ := D.coreDegree p.val

theorem QCoreCoordinates_basis (p : D.CoreMinimalIndex) :
    D.QCoreCoordinates k (D.QCoreBasis k p)=Finsupp.single p 1 := by
  change D.QCoreCoordinates k ((D.QCoreCoordinates k).symm (Finsupp.single p 1))=Finsupp.single p 1
  exact LinearEquiv.apply_symm_apply _ _

theorem QCore_basis_variable_homogeneous (b : D.a) (p j : D.CoreMinimalIndex)
    (hj : D.QCoreDegree j≠D.QCoreDegree p+1) :
    D.QCoreModuleCoordinates k ((MvPolynomial.X b : D.InternalRing k) •
      (D.QCoreModuleCoordinates k).symm (Finsupp.single p 1)) j=0 := by
  change D.QCoreCoordinates k (D.internalToQCore k (MvPolynomial.X b)*D.QCoreBasis k p) j=0
  rw [D.QCore_internal_basis]
  split_ifs with h
  · rw [D.QCoreCoordinates_basis]
    apply Finsupp.single_eq_of_ne
    intro he
    subst j
    apply hj
    change (D.coreDegree (p.val+D.coreGeneratorPoint (D.internalVariable b)) : ℤ)=(D.coreDegree p.val : ℤ)+1
    rw [(D.coreDegree).map_add]
    change ((D.coreDegree p.val+1 : ℕ) : ℤ)=(D.coreDegree p.val : ℤ)+1
    exact Nat.cast_add _ _
  · rw [map_zero,Finsupp.zero_apply]

noncomputable def QCoreGrading : GradedPolynomialModule k D.a (D.QCoreModule k) :=
  NSP14.Endpoint.basisGrading k D.a D.CoreMinimalIndex (D.QCoreModule k)
    (D.QCoreModuleCoordinates k) D.QCoreDegree (D.QCore_basis_variable_homogeneous k)

theorem QCoreGrading_above (n : ℕ) (hn : D.u≤n) : IsZero ((D.QCoreGrading k).piece n) := by
  have hno : IsEmpty {p : D.CoreMinimalIndex // D.QCoreDegree p=(n:ℤ)} := by
    refine ⟨fun p => ?_⟩
    have hdeg := D.coreMinimal_degree_lt p.val
    have hx : (D.coreDegree p.val.val : ℤ)=(n:ℤ) := p.property
    have he : D.coreDegree p.val.val=n := by exact_mod_cast hx
    omega
  have : Subsingleton ((D.QCoreGrading k).piece n) :=
    inferInstanceAs (Subsingleton ({p : D.CoreMinimalIndex // D.QCoreDegree p=(n:ℤ)} →₀ k))
  exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance
end NSP14.Endpoint.Data
