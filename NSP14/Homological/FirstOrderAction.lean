module
public import NSP14.Homological.SquareZeroModel
@[expose] public section
namespace NSP14.Homological
variable (k : Type) [Field k] (r f : ℕ)

theorem firstOrderPolynomial_X (v : Fin r) :
    firstOrderPolynomial k r f (MvPolynomial.X v)=
      (TrivSqZeroExt.inr (Pi.single (Fin.castAdd f v) (1:k)) : FirstOrderRing k r f) :=
  MvPolynomial.aeval_X _ v
end NSP14.Homological
