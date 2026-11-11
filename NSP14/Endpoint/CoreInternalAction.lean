module
public import NSP14.Endpoint.CoreArtinBasis
public import NSP14.Endpoint.FiberAction
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

theorem internalToCore_X (b : D.a) : D.internalToCore k (MvPolynomial.X b)=
    D.coreMonomial k (D.coreGeneratorPoint (D.internalVariable b)) := by
  simp only [internalToCore,AlgHom.comp_apply,internalToFull,MvPolynomial.rename_X,
    fullToCore,MvPolynomial.aeval_X]

theorem QCore_class_monomial (p : D.corePoints) :
    Ideal.Quotient.mk (NSP14.Endpoint.endpointIdeal k (D.Core k) (D.endpointToCore k)) (D.coreMonomial k p)=
      if h : D.CoreMinimal p then D.QCoreBasis k ⟨p,h⟩ else 0 := by
  split_ifs with h
  · exact (D.QCoreBasis_apply k ⟨p,h⟩).symm
  · apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [D.coreEndpointIdeal_mem]
    intro q hq
    have he : p=q := by
      by_contra hn
      have hz : (D.coreMonomial k p).coeff q=0 := by
        change (Finsupp.single p (1:k)) q=0
        exact Finsupp.single_eq_of_ne (Ne.symm hn)
      exact (Finsupp.mem_support_iff.mp hq) hz
    simpa only [←he] using h

/-- Actual internal multiplication on QC. A nonminimal destination is
zero; a minimal destination is precisely its genuine basis class. -/
theorem QCore_internal_basis (b : D.a) (p : D.CoreMinimalIndex) :
    D.internalToQCore k (MvPolynomial.X b)*D.QCoreBasis k p=
      if h : D.CoreMinimal (p.val+D.coreGeneratorPoint (D.internalVariable b)) then
        D.QCoreBasis k ⟨p.val+D.coreGeneratorPoint (D.internalVariable b),h⟩ else 0 := by
  rw [D.QCoreBasis_apply]
  change Ideal.Quotient.mk _ (D.internalToCore k (MvPolynomial.X b))*
    Ideal.Quotient.mk _ (D.coreMonomial k p.val)=_
  rw [←map_mul,D.internalToCore_X,D.coreMonomial_mul,add_comm,D.QCore_class_monomial]

theorem coreMinimal_degree_lt (p : D.CoreMinimalIndex) : D.coreDegree p.val<D.u := by
  have h := D.minimalFiber_degree_lt (D.coreCoordinates p.val).1 (D.coreCoordinates p.val).2 p.property
  have hd := congrArg Prod.fst (D.decode_coreCoordinates p.val)
  change (D.coreCoordinates p.val).2.1+(D.coreCoordinates p.val).2.2+D.epsilon (D.coreCoordinates p.val).1=D.coreDegree p.val at hd
  omega
end NSP14.Endpoint.Data
