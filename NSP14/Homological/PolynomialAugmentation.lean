module
public import NSP14.Homological.LinearVariableBetti
@[expose] public section
namespace NSP14.Homological
variable (k τ σ : Type*) [Field k]

theorem augmentation_rename (f : τ → σ) :
    (augmentation k σ).comp (MvPolynomial.rename f)=augmentation k τ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply,MvPolynomial.rename_X,augmentation_X]
end NSP14.Homological
