module
public import NSP14.Lex.DistractionChain
@[expose] public section
open scoped Classical TensorProduct
open CategoryTheory NSP14.Homological
namespace NSP14.Tests.DistractionChain
variable (k : Type) [Field k] (q : ℕ)
local notation "K" => Lex.GenericDistractionField k q

theorem actual_boundary_commutation (I : Ideal (MvPolynomial (Fin q) K))
    (hmono : Lex.IsMonomial K q I) (j : ℕ)
    (z : coefficientModule K (Fin q) (Endpoint.artinModule K (Fin q) I) ⊗[K]
      (⋀[K]^(j+1) (Fin q → K))) :
    koszulExteriorBoundary K (Fin q) (Endpoint.artinModule K (Fin q) (Lex.genericDistractionIdeal k q I))
      (Lex.genericDistractionBasis k q I hmono) j (Lex.genericDistractionTensorEquiv k q I hmono (j+1) z)=
    Lex.genericDistractionTensorEquiv k q I hmono j
      (koszulExteriorBoundary K (Fin q) (Endpoint.artinModule K (Fin q) I)
        (Endpoint.artinMonomialBasis K q I) j z) :=
  Lex.genericDistractionTensorEquiv_comm k q I hmono j z

theorem actual_koszul_chain_isomorphism (I : Ideal (MvPolynomial (Fin q) K))
    (hmono : Lex.IsMonomial K q I) :
    Nonempty (coefficientKoszulComplex K (Fin q) (Endpoint.artinModule K (Fin q) I) ≅
      coefficientKoszulComplex K (Fin q)
        (Endpoint.artinModule K (Fin q) (Lex.genericDistractionIdeal k q I))) :=
  ⟨Lex.genericDistractionChainIso k q I hmono⟩

theorem actual_all_ordinary_betti_numbers (I : Ideal (MvPolynomial (Fin q) K))
    (hmono : Lex.IsMonomial K q I) (i : ℕ) :
    totalBetti K (Fin q) (Endpoint.artinModule K (Fin q) I) i=
      totalBetti K (Fin q) (Endpoint.artinModule K (Fin q) (Lex.genericDistractionIdeal k q I)) i :=
  Lex.genericDistraction_totalBetti k q I hmono i
end NSP14.Tests.DistractionChain
