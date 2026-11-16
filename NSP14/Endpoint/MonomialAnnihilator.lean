module
public import NSP14.Endpoint.Socle
public import NSP14.Semigroup.TangentCoordinates
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]

def shiftBy (g a : S.carrier) : S.carrier := a+g
noncomputable def survivesBy (g a : S.carrier) : Prop := S.order (a+g).val=S.order a.val+S.order g.val
noncomputable def monomialLiveFilter (g : S.carrier) : (S.carrier →₀ k) →ₗ[k] (S.carrier →₀ k) where
  toFun f := f.filter (S.survivesBy g)
  map_add' := by intros;exact Finsupp.filter_add
  map_smul' := by intros;exact Finsupp.filter_smul
noncomputable def coordinateMultiplyBy (g : S.carrier) : (S.carrier →₀ k) →ₗ[k] (S.carrier →₀ k) :=
  (Finsupp.lmapDomain k k (S.shiftBy g)).comp (S.monomialLiveFilter k g)
noncomputable def multiplyBy (g : S.carrier) : S.TangentAlgebra k →ₗ[k] S.TangentAlgebra k :=
  (LinearMap.mul k _).flip (S.initialMonomial k g)

theorem multiplyBy_coordinates (g : S.carrier) (a : S.TangentAlgebra k) :
    S.tangentCoordinates k (S.multiplyBy k g a)=S.coordinateMultiplyBy k g (S.tangentCoordinates k a) := by
  have he : (S.tangentCoordinates k).toLinearMap.comp (S.multiplyBy k g)=
      (S.coordinateMultiplyBy k g).comp (S.tangentCoordinates k).toLinearMap := by
    apply (S.tangentBasis k).ext
    intro x
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,S.tangentBasis_eq_initial]
    change S.tangentCoordinates k (S.initialMonomial k x*S.initialMonomial k g)=_
    rw [S.tangentCoordinates_initial]
    by_cases hx : S.survivesBy g x
    · rw [S.initialMonomial_mul_live k x g hx,S.tangentCoordinates_initial]
      simp [coordinateMultiplyBy,monomialLiveFilter,Finsupp.filter_single_of_pos _ hx,shiftBy]
    · have ht : S.order x.val+S.order g.val < S.order (x.val+g.val) := by
        have hle := S.order_add x.property g.property
        change ¬S.order (x.val+g.val)=S.order x.val+S.order g.val at hx
        omega
      rw [(S.initialMonomial_mul_eq_zero_iff k x g).mpr ht,map_zero]
      simp [coordinateMultiplyBy,monomialLiveFilter,Finsupp.filter_single_of_neg _ hx]
  exact LinearMap.congr_fun he a

theorem multiplyBy_zero_coeff (g : S.carrier) (a : S.TangentAlgebra k) :
    S.multiplyBy k g a=0 ↔ ∀ x,S.survivesBy g x → S.tangentCoordinates k a x=0 := by
  have hinj : Function.Injective (S.shiftBy g) := by
    intro x y h
    exact add_right_cancel h
  rw [←(map_eq_zero_iff (S.tangentCoordinates k) (S.tangentCoordinates k).injective),S.multiplyBy_coordinates]
  change Finsupp.mapDomain (S.shiftBy g) ((S.tangentCoordinates k a).filter (S.survivesBy g))=0 ↔ _
  rw [←Finsupp.mapDomain_zero (f:=S.shiftBy g),(Finsupp.mapDomain_injective hinj).eq_iff,Finsupp.filter_eq_zero_iff]

noncomputable def twoMonomialSocle (g h : S.carrier) : Submodule k (S.TangentAlgebra k) :=
  (S.multiplyBy k g).ker⊓(S.multiplyBy k h).ker

noncomputable def twoMonomialSocleCoordinates (g h : S.carrier) : S.twoMonomialSocle k g h ≃ₗ[k]
    ({a : S.carrier // ¬S.survivesBy g a ∧ ¬S.survivesBy h a} →₀ k) := by
  let U := Finsupp.supported k k {a : S.carrier | ¬S.survivesBy g a ∧ ¬S.survivesBy h a}
  have he (a : S.TangentAlgebra k) : a∈S.twoMonomialSocle k g h ↔ S.tangentCoordinates k a∈U := by
    rw [Finsupp.mem_supported']
    change (S.multiplyBy k g a=0 ∧ S.multiplyBy k h a=0) ↔ _
    rw [S.multiplyBy_zero_coeff,S.multiplyBy_zero_coeff]
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro ha x hx
      by_cases hg : S.survivesBy g x
      · exact ha.1 x hg
      · exact ha.2 x (by tauto)
    · intro ha
      exact ⟨fun x hx => ha x (by tauto),fun x hx => ha x (by tauto)⟩
  exact ((S.tangentCoordinates k).submoduleMap (S.twoMonomialSocle k g h)).trans
    ((LinearEquiv.ofEq _ _ (by
      ext f
      constructor
      · rintro ⟨a,ha,rfl⟩
        exact (he a).mp ha
      · intro hf
        exact ⟨(S.tangentCoordinates k).symm f,(he _).mpr (by simpa only [LinearEquiv.apply_symm_apply] using hf),
          (S.tangentCoordinates k).apply_symm_apply f⟩)).trans (Finsupp.supportedEquivFinsupp (R:=k) {a : S.carrier | ¬S.survivesBy g a ∧ ¬S.survivesBy h a}))
end NSP14.NumericalSemigroup
