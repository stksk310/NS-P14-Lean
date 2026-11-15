module
public import NSP14.Homological.HomogeneousBasisPieces
@[expose] public section
namespace NSP14.Tests.HomogeneousBasisPieces
theorem actual_piece_dimension (k σ J : Type) [Field k]
    (M : ModuleCat (Homological.VariableRing k σ)) (G : Homological.GradedPolynomialModule k σ M)
    (b : Module.Basis J k (Homological.coefficientModule k σ M)) (deg : J → ℤ)
    (hb : ∀ a,b a ∈ G.degreeSpace (deg a)) (q : ℤ) [Finite {a : J //deg a=q}] :
    Module.finrank k (G.piece q)=Nat.card {a : J //deg a=q} :=
  Homological.homogeneous_piece_finrank k σ M G b deg hb q
end NSP14.Tests.HomogeneousBasisPieces
