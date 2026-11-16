module

public import NSP14.Homological.PolynomialBaseChangeFunctor

@[expose] public section

open CategoryTheory
open scoped TensorProduct

namespace NSP14.Homological

universe u
variable (k L σ : Type u) [Field k] [Field L] [Algebra k L]

theorem polynomialFieldExtension_symm_map (p : VariableRing k σ) :
    (polynomialFieldExtension k L σ).symm (MvPolynomial.map (algebraMap k L) p)=1 ⊗ₜ[k] p := by
  apply (polynomialFieldExtension k L σ).injective
  rw [AlgEquiv.apply_symm_apply]
  change _ = MvPolynomial.algebraTensorAlgEquiv k L (1 ⊗ₜ[k] p)
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul,one_smul]

theorem polynomialBaseChange_original_action (M : ModuleCat.{u} (VariableRing k σ))
    (p : VariableRing k σ) (c : L) (m : coefficientModule k σ M) :
    extendedPolynomialRepresentation k L σ M (MvPolynomial.map (algebraMap k L) p) (c ⊗ₜ[k] m) =
      c ⊗ₜ[k] (p • m) := by
  change ((AlgHom.liftEquiv k L (VariableRing k σ) _)
    ((Module.End.baseChangeHom k L (coefficientModule k σ M)).comp
      (Algebra.lsmul k k (coefficientModule k σ M))))
        ((polynomialFieldExtension k L σ).symm (MvPolynomial.map (algebraMap k L) p)) (c ⊗ₜ[k] m) = _
  rw [polynomialFieldExtension_symm_map,AlgHom.liftEquiv_tmul,one_smul]
  rfl

theorem polynomialBaseChange_constant_action (M : ModuleCat.{u} (VariableRing k σ))
    (c : L) (m : coefficientModule k σ M) :
    extendedPolynomialRepresentation k L σ M (MvPolynomial.C c) (1 ⊗ₜ[k] m) = c ⊗ₜ[k] m := by
  have he := (extendedPolynomialRepresentation k L σ M).commutes c
  change extendedPolynomialRepresentation k L σ M (algebraMap L (VariableRing L σ) c) _ = _
  rw [he]
  change c • (1 ⊗ₜ[k] m) = c ⊗ₜ[k] m
  simp only [TensorProduct.smul_tmul',smul_eq_mul,mul_one]

/-- Actual changed-ring finite generation, from generators of M over the original polynomial ring. -/
noncomputable instance polynomialBaseChange_finite (M : ModuleCat.{u} (VariableRing k σ))
    [Module.Finite (VariableRing k σ) M] :
    Module.Finite (VariableRing L σ) (polynomialBaseChangeModule k L σ M) := by
  classical
  let : Module.Finite (VariableRing k σ) (coefficientModule k σ M) :=
    inferInstanceAs (Module.Finite (VariableRing k σ) M)
  obtain ⟨s,hs⟩ := Module.Finite.fg_top (R := VariableRing k σ) (M := coefficientModule k σ M)
  let v : coefficientModule k σ M → polynomialBaseChangeModule k L σ M := fun m => 1 ⊗ₜ[k] m
  let W := Submodule.span (VariableRing L σ) (↑(s.image v) : Set (polynomialBaseChangeModule k L σ M))
  have ht : ∀ m : coefficientModule k σ M, ∀ c : L,
      (show polynomialBaseChangeModule k L σ M from c ⊗ₜ[k] m) ∈ W := by
    intro m
    have hm : m ∈ Submodule.span (VariableRing k σ) (s : Set (coefficientModule k σ M)) := by rw [hs]; trivial
    induction hm using Submodule.span_induction with
    | mem m hm =>
      intro c
      have hv : v m∈W := Submodule.subset_span (Finset.mem_image.mpr ⟨m,hm,rfl⟩)
      have hc := W.smul_mem (MvPolynomial.C c) hv
      change extendedPolynomialRepresentation k L σ M (MvPolynomial.C c) (1 ⊗ₜ[k] m) ∈ W at hc
      rwa [polynomialBaseChange_constant_action] at hc
    | zero =>
      intro c
      rw [TensorProduct.tmul_zero]
      exact W.zero_mem
    | add a b _ _ ha hb =>
      intro c
      erw [TensorProduct.tmul_add]
      exact W.add_mem (ha c) (hb c)
    | smul p m _ hm =>
      intro c
      have hp := W.smul_mem (MvPolynomial.map (algebraMap k L) p) (hm c)
      change extendedPolynomialRepresentation k L σ M (MvPolynomial.map (algebraMap k L) p) (c ⊗ₜ[k] m) ∈ W at hp
      rwa [polynomialBaseChange_original_action] at hp
  refine ⟨s.image v,?_⟩
  apply top_unique
  intro a _
  change a∈W
  change (show polynomialBaseChangeModule k L σ M from (show L ⊗[k] coefficientModule k σ M from a)) ∈ W
  generalize (show L ⊗[k] coefficientModule k σ M from a)=z
  induction z using TensorProduct.inductionOn with
  | tmul c m => exact ht m c
  | add a b ha hb => exact W.add_mem ha hb

end NSP14.Homological
