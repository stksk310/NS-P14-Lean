module
public import NSP14.Endpoint.CoreHilbert
public import NSP14.Endpoint.ArtinRank
public import NSP14.Homological.GeneratedDegreePresentation
public import NSP14.Homological.CoordinateGradePieces
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open CategoryTheory NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

theorem QCoreBasis_zero : D.QCoreBasis k D.zeroMinimalIndex=1 := by
  rw [D.QCoreBasis_apply]
  change Ideal.Quotient.mk _ (1 : D.Core k)=1
  exact map_one _

theorem QCoreUnit_coordinates : D.QCoreModuleCoordinates k (D.QCoreUnit k)=Finsupp.single D.zeroMinimalIndex 1 := by
  change D.QCoreCoordinates k 1=Finsupp.single D.zeroMinimalIndex 1
  rw [←D.QCoreBasis_zero k,D.QCoreCoordinates_basis]

theorem QCoreUnit_degree_zero : D.QCoreUnit k∈(D.QCoreGrading k).degreeSpace 0 := by
  change D.QCoreUnit k∈(coordinateDegreeInclusion k D.CoreMinimalIndex D.QCoreDegree D.a
    (D.QCoreModule k) (D.QCoreModuleCoordinates k) 0).range
  rw [coordinateDegreeInclusion_range]
  intro p hp
  rw [D.QCoreUnit_coordinates]
  apply Finsupp.single_eq_of_ne
  intro he
  subst p
  exact hp rfl

/-- Generation in degree zero is derived from the actual surjective
internal polynomial presentation and the actual degree-zero unit. -/
theorem QCore_generated_degree_zero : Submodule.span (D.InternalRing k)
    (Set.range (fun a : (D.QCoreGrading k).piece 0 =>
      (show D.QCoreModule k from (D.QCoreGrading k).inclusion 0 a)))=⊤ := by
  let U := Submodule.span (D.InternalRing k)
    (Set.range (fun a : (D.QCoreGrading k).piece 0 =>
      (show D.QCoreModule k from (D.QCoreGrading k).inclusion 0 a)))
  have hunit : (show D.QCoreModule k from D.QCoreUnit k)∈U :=
    Submodule.subset_span (D.QCoreUnit_degree_zero k)
  apply top_unique
  intro a _
  obtain ⟨p,hp⟩ := D.internalToQCore_surjective k (D.QCoreCoefficientEquiv k a)
  have hm := U.smul_mem p hunit
  have he : p • (show D.QCoreModule k from D.QCoreUnit k)=a := by
    apply (D.QCoreCoefficientEquiv k).injective
    change D.internalToQCore k p*1=D.QCoreCoefficientEquiv k a
    rw [mul_one,hp]
  rw [he] at hm
  exact hm
end NSP14.Endpoint.Data
