module
public import NSP14.Lex.StandardBettiWeights
@[expose] public section
namespace NSP14.Tests.StandardBettiWeights
variable (k : Type) [Field k] (q N i : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
theorem actual_total_K_bound (I : Ideal (MvPolynomial (Fin q) k)) (hI : Lex.IsLex k q I) (hp : I≠⊤)
    (hHom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hN : ∀ n,N+1<n → Lex.quotientHilbert k q I hHom n=0)
    (h0 : Lex.quotientHilbert k q I hHom 0=1) (h1 : Lex.quotientHilbert k q I hHom 1=q) :
    Homological.totalBetti k (Fin q) (Endpoint.artinModule k (Fin q) I) (i+1)≤
      (i+1)*(q+1).choose (i+2)+Lex.lexCorrection k q I N*(q-1).choose i :=
  Lex.IsLex.total_betti_le_correction k q I hI hp hHom N i hN h0 h1
end NSP14.Tests.StandardBettiWeights
