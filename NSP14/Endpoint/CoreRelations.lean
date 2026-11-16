module
public import NSP14.Endpoint.CoreInternalAction
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Endpoint.Data
variable (D : Data) (k : Type) [Field k]

theorem QCore_quadratic_relation (a b c d : D.a) (h : a.val+b.val=c.val+d.val) :
    D.internalToQCore k (MvPolynomial.X a)*D.internalToQCore k (MvPolynomial.X b)=
      D.internalToQCore k (MvPolynomial.X c)*D.internalToQCore k (MvPolynomial.X d) := by
  change Ideal.Quotient.mk _ (D.internalToCore k (MvPolynomial.X a))*
    Ideal.Quotient.mk _ (D.internalToCore k (MvPolynomial.X b))=_
  rw [←map_mul,D.internalToCore_X,D.internalToCore_X,D.coreMonomial_mul]
  change _=Ideal.Quotient.mk _ (D.internalToCore k (MvPolynomial.X c))*
    Ideal.Quotient.mk _ (D.internalToCore k (MvPolynomial.X d))
  rw [←map_mul,D.internalToCore_X,D.internalToCore_X,D.coreMonomial_mul]
  congr 2
  apply Subtype.ext
  exact Prod.ext rfl h

theorem QCore_minimal_monomial_nonzero (p : D.corePoints) (hp : D.CoreMinimal p) :
    (Ideal.Quotient.mk _ (D.coreMonomial k p) : D.QCore k)≠0 := by
  intro hz
  have hc := (D.coreEndpointIdeal_coeff_zero k _).mp (Ideal.Quotient.eq_zero_iff_mem.mp hz) p hp
  change (Finsupp.single p (1:k)) p=0 at hc
  rw [Finsupp.single_eq_same] at hc
  exact one_ne_zero hc
end NSP14.Endpoint.Data
