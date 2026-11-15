module
public import NSP14.Homological.TriangularBlockRank
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.Homological
variable (k : Type) [Field k] {I Γ X : Type} [AddCommGroup X] [Module k X]
  (b : Module.Basis I k X) (key : I → Γ)

noncomputable def basisBlockSpace (a : Γ) : Submodule k X :=
  Submodule.span k (b '' {i | key i=a})

noncomputable def basisBlockProjection (a : Γ) : X →ₗ[k] X :=
  b.constr k (fun i => if key i=a then b i else 0)

theorem basisBlockProjection_basis (a : Γ) (i : I) :
    basisBlockProjection k b key a (b i)=if key i=a then b i else 0 :=
  b.constr_basis k _ i

theorem basisBlockProjection_coord (a : Γ) (x : X) (j : I) :
    b.repr (basisBlockProjection k b key a x) j=if key j=a then b.repr x j else 0 := by
  have hf : (b.coord j).comp (basisBlockProjection k b key a)=if key j=a then b.coord j else 0 := by
    apply b.ext
    intro i
    by_cases hi : key i=a
    · by_cases hj : key j=a
      · simp only [LinearMap.comp_apply,basisBlockProjection_basis,ite_eq_left hi,ite_eq_left hj]
      · have hn : i ≠ j := fun he => hj (he ▸ hi)
        simp only [LinearMap.comp_apply,basisBlockProjection_basis,ite_eq_left hi,ite_eq_right hj,LinearMap.zero_apply]
        exact (b.repr_self_apply i j).trans (ite_eq_right hn)
    · by_cases hj : key j=a
      · have hn : i ≠ j := fun he => hi (he.symm ▸ hj)
        simp only [LinearMap.comp_apply,basisBlockProjection_basis,ite_eq_right hi,ite_eq_left hj,map_zero]
        exact ((b.repr_self_apply i j).trans (ite_eq_right hn)).symm
      · simp only [LinearMap.comp_apply,basisBlockProjection_basis,ite_eq_right hi,ite_eq_right hj,map_zero,LinearMap.zero_apply]
  change (b.coord j) (basisBlockProjection k b key a x)=if key j=a then (b.coord j) x else 0
  have he := LinearMap.congr_fun hf x
  by_cases hj : key j=a
  · simpa only [LinearMap.comp_apply,ite_eq_left hj] using he
  · simpa only [LinearMap.comp_apply,ite_eq_right hj,LinearMap.zero_apply] using he

variable [Fintype I]
theorem basisBlockProjection_mem (a : Γ) (x : X) :
    basisBlockProjection k b key a x ∈ basisBlockSpace k b key a := by
  rw [←b.sum_repr x,map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [map_smul,basisBlockProjection_basis]
  by_cases hi : key i=a
  · rw [ite_eq_left hi]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,hi,rfl⟩)
  · rw [ite_eq_right hi,smul_zero]
    exact Submodule.zero_mem _

section Diagonal
variable {J Y : Type} [Fintype J] [Fintype Γ] [LinearOrder Γ]
  [AddCommGroup Y] [Module k Y]
  (c : Module.Basis J k Y) (v : J → Γ) (d : X →ₗ[k] Y)

/-- The actual sum of coordinate projections of one actual map. -/
noncomputable def basisDiagonalMap : X →ₗ[k] Y :=
  ∑ a,(basisBlockProjection k c v a).comp (d.comp (basisBlockProjection k b key a))

omit [Fintype I] [Fintype J] in
theorem basisDiagonalMap_basis (i : I) :
    basisDiagonalMap k b key c v d (b i)=basisBlockProjection k c v (key i) (d (b i)) := by
  unfold basisDiagonalMap
  rw [LinearMap.sum_apply]
  have he (a : Γ) : (basisBlockProjection k c v a).comp
      (d.comp (basisBlockProjection k b key a)) (b i)=
      if key i=a then basisBlockProjection k c v a (d (b i)) else 0 := by
    simp only [LinearMap.comp_apply,basisBlockProjection_basis]
    by_cases hi : key i=a
    · rw [ite_eq_left hi,ite_eq_left hi]
    · rw [ite_eq_right hi,ite_eq_right hi,map_zero,map_zero]
  simp only [he]
  simp

omit [Fintype I] [Fintype J] in
theorem basisDiagonalMap_coord (i : I) (j : J) :
    c.repr (basisDiagonalMap k b key c v d (b i)) j=
      if v j=key i then c.repr (d (b i)) j else 0 := by
  rw [basisDiagonalMap_basis,basisBlockProjection_coord]
  split_ifs <;> rfl

/-- Ordered coefficient triangularity of the actual map discharges the
triangular-block hypotheses, yielding an actual diagonal rank comparison. -/
theorem basisDiagonalMap_rank
    (htri : ∀ i j,key i<v j → c.repr (d (b i)) j=0) :
    Module.finrank k (basisDiagonalMap k b key c v d).range ≤ Module.finrank k d.range := by
  let : Module.Finite k Y := Module.Finite.of_basis c
  apply triangular_diagonal_rank k d (basisBlockSpace k b key)
    (basisBlockProjection k c v) (basisBlockProjection k b key) (basisBlockProjection_mem k b key)
  intro a e hea x
  have hu : basisBlockSpace k b key e ≤ (basisBlockProjection k c v a |>.comp d).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    change key i=e at hi
    change basisBlockProjection k c v a (d (b i))=0
    apply c.repr.injective
    ext j
    rw [basisBlockProjection_coord,map_zero,Finsupp.zero_apply]
    by_cases hj : v j=a
    · rw [ite_eq_left hj]
      apply htri i j
      simpa only [hi,hj] using hea
    · rw [ite_eq_right hj]
  exact hu x.property
end Diagonal
end NSP14.Homological
