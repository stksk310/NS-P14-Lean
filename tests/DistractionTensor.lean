module
public import NSP14.Lex.DistractionTensor
public import NSP14.Lex.GenericDistractionExterior
public import NSP14.Homological.BasiswiseTensor
@[expose] public section
open scoped Classical TensorProduct
open NSP14.Homological
namespace NSP14.Tests.DistractionTensor
variable (k : Type) [Field k] (q : ℕ)
local notation "K" => Lex.GenericDistractionField k q

theorem actual_all_monomial_tensor_images
    (I : Ideal (MvPolynomial (Fin q) K)) (hmono : Lex.IsMonomial K q I) (j : ℕ) :
    ∃ e : coefficientModule K (Fin q) (Endpoint.artinModule K (Fin q) I) ⊗[K] (⋀[K]^j (Fin q → K)) ≃ₗ[K]
      coefficientModule K (Fin q) (Endpoint.artinModule K (Fin q) (Lex.genericDistractionIdeal k q I)) ⊗[K]
        (⋀[K]^j (Fin q → K)),
      ∀ (a : Fin q →₀ ℕ) (w : ⋀[K]^j (Fin q → K)),
        e ((show coefficientModule K (Fin q) (Endpoint.artinModule K (Fin q) I) from
          Ideal.Quotient.mk I (MvPolynomial.monomial a 1)) ⊗ₜ[K] w)=
        (show coefficientModule K (Fin q) (Endpoint.artinModule K (Fin q) (Lex.genericDistractionIdeal k q I)) from
          Ideal.Quotient.mk (Lex.genericDistractionIdeal k q I) (Lex.genericFieldDistraction k q a)) ⊗ₜ[K]
            Lex.genericDistractionWedgeEquiv k q j a w :=
  ⟨Lex.genericDistractionTensorEquiv k q I hmono j,
    Lex.genericDistractionTensorEquiv_monomial k q I hmono j⟩
end NSP14.Tests.DistractionTensor
