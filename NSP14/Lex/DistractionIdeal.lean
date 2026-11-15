module
public import NSP14.Lex.DistractionLinearEquiv
public import NSP14.Lex.Ideal
@[expose] public section
open scoped Classical BigOperators Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)
def variableLinearCombination : (Fin q → GenericDistractionField k q) →ₗ[GenericDistractionField k q]
    MvPolynomial (Fin q) (GenericDistractionField k q) where
  toFun v := ∑ r, v r • MvPolynomial.X r
  map_add' v w := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.smul_sum,smul_smul]

theorem genericFieldLinearEquiv_single (a : Fin q →₀ ℕ) (i r : Fin q) :
    genericFieldLinearEquiv k q a (Pi.single i 1) r = genericFieldMatrix k q a r i := by
  unfold genericFieldLinearEquiv
  rw [Matrix.toLinearEquiv_apply,Matrix.toLin_eq_toLin',Matrix.toLin'_apply]
  simp only [Matrix.mulVec_single_one,Matrix.col_apply]

theorem variableLinearCombination_generic (a : Fin q →₀ ℕ) (i : Fin q) :
    variableLinearCombination k q (genericFieldLinearEquiv k q a (Pi.single i 1))=
      genericFieldLinear k q i (a i) := by
  simp only [variableLinearCombination,LinearMap.coe_mk,AddHom.coe_mk,
    genericFieldLinearEquiv_single]
  simp [genericFieldLinear,genericLinearRaw,genericFieldMatrix,genericRawMatrix,
    Algebra.smul_def]

theorem genericFieldLinearCombination (a : Fin q →₀ ℕ) (r : Fin q) :
    ∃ c : Fin q → GenericDistractionField k q,
      MvPolynomial.X r = ∑ i,c i • genericFieldLinear k q i (a i) := by
  let E := genericFieldLinearEquiv k q a
  let c := E.symm (Pi.single r 1)
  have hc : (∑ i,c i • Pi.single i (1 : GenericDistractionField k q))=c := by
    ext j
    simp [Pi.single_apply]
  refine ⟨c,?_⟩
  calc
    MvPolynomial.X r = variableLinearCombination k q (Pi.single r 1) := by
      simp [variableLinearCombination,Pi.single_apply]
    _ = variableLinearCombination k q (E c) := by rw [LinearEquiv.apply_symm_apply]
    _ = variableLinearCombination k q (E (∑ i,c i • Pi.single i 1)) := by rw [hc]
    _ = ∑ i,c i • genericFieldLinear k q i (a i) := by
      simp only [map_sum,map_smul,E,variableLinearCombination_generic]

def genericDistractionSpace (I : Ideal (MvPolynomial (Fin q) (GenericDistractionField k q))) :
    Submodule (GenericDistractionField k q) (MvPolynomial (Fin q) (GenericDistractionField k q)) :=
  Submodule.span _ (genericFieldDistraction k q '' {a | MvPolynomial.monomial a 1∈I})

theorem genericDistractionSpace_monomial
    (I : Ideal (MvPolynomial (Fin q) (GenericDistractionField k q)))
    (a : Fin q →₀ ℕ) (ha : MvPolynomial.monomial a 1∈I) :
    genericFieldDistraction k q a ∈ genericDistractionSpace k q I :=
  Submodule.subset_span ⟨a,ha,rfl⟩

theorem genericDistractionSpace_variable_monomial
    (I : Ideal (MvPolynomial (Fin q) (GenericDistractionField k q)))
    (a : Fin q →₀ ℕ) (ha : MvPolynomial.monomial a 1∈I) (r : Fin q) :
    MvPolynomial.X r*genericFieldDistraction k q a∈genericDistractionSpace k q I := by
  obtain ⟨c,hc⟩ := genericFieldLinearCombination k q a r
  rw [hc,Finset.sum_mul]
  apply Submodule.sum_mem
  intro i _
  have hai : MvPolynomial.monomial (a+Finsupp.single i 1) (1:GenericDistractionField k q)∈I := by
    have h := I.mul_mem_left (MvPolynomial.X i) ha
    simpa only [MvPolynomial.X,MvPolynomial.monomial_mul_monomial,one_mul,add_comm] using h
  have h := (genericDistractionSpace k q I).smul_mem (c i)
    (genericDistractionSpace_monomial k q I _ hai)
  rw [genericFieldDistraction_step] at h
  simpa only [smul_mul_assoc] using h

theorem genericDistractionSpace_variable
    (I : Ideal (MvPolynomial (Fin q) (GenericDistractionField k q)))
    (f : MvPolynomial (Fin q) (GenericDistractionField k q))
    (hf : f∈genericDistractionSpace k q I) (r : Fin q) :
    MvPolynomial.X r*f∈genericDistractionSpace k q I := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a,ha,rfl⟩ := hx
    exact genericDistractionSpace_variable_monomial k q I a ha r
  | zero => simpa only [mul_zero] using (genericDistractionSpace k q I).zero_mem
  | add x y _ _ hx hy =>
    simpa only [mul_add] using (genericDistractionSpace k q I).add_mem hx hy
  | smul c x _ hx =>
    simpa only [mul_smul_comm] using (genericDistractionSpace k q I).smul_mem c hx

theorem genericDistractionSpace_mul
    (I : Ideal (MvPolynomial (Fin q) (GenericDistractionField k q)))
    (p f : MvPolynomial (Fin q) (GenericDistractionField k q))
    (hf : f∈genericDistractionSpace k q I) :
    p*f∈genericDistractionSpace k q I := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    simpa only [MvPolynomial.smul_eq_C_mul] using (genericDistractionSpace k q I).smul_mem c hf
  | add p s hp hs =>
    simpa only [add_mul] using (genericDistractionSpace k q I).add_mem hp hs
  | mul_X p r hp =>
    simpa only [mul_assoc,mul_comm] using genericDistractionSpace_variable k q I (p*f) hp r

def genericDistractionIdeal (I : Ideal (MvPolynomial (Fin q) (GenericDistractionField k q))) :
    Ideal (MvPolynomial (Fin q) (GenericDistractionField k q)) where
  carrier := genericDistractionSpace k q I
  zero_mem' := (genericDistractionSpace k q I).zero_mem
  add_mem' := (genericDistractionSpace k q I).add_mem
  smul_mem' p f hf := genericDistractionSpace_mul k q I p f hf

theorem mem_genericDistractionIdeal
    (I : Ideal (MvPolynomial (Fin q) (GenericDistractionField k q)))
    (hI : IsMonomial (GenericDistractionField k q) q I)
    (f : MvPolynomial (Fin q) (GenericDistractionField k q)) :
    f∈genericDistractionIdeal k q I ↔ (genericPolynomialEquiv k q).symm f∈I := by
  constructor
  · intro hf
    change f∈genericDistractionSpace k q I at hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a,ha,rfl⟩ := hx
      rw [← genericPolynomialEquiv_monomial,LinearEquiv.symm_apply_apply]
      exact ha
    | zero => simpa only [map_zero] using I.zero_mem
    | add x y _ _ hx hy => simpa only [map_add] using I.add_mem hx hy
    | smul c x _ hx =>
      rw [map_smul]
      exact (I.restrictScalars (GenericDistractionField k q)).smul_mem c hx
  · intro hf
    let g := (genericPolynomialEquiv k q).symm f
    have hg : genericPolynomialEquiv k q g ∈ genericDistractionSpace k q I := by
      rw [g.as_sum,map_sum]
      apply Submodule.sum_mem
      intro a ha
      have hm : MvPolynomial.monomial a (g.coeff a)=g.coeff a • MvPolynomial.monomial a (1:GenericDistractionField k q) := by
        simp only [MvPolynomial.smul_monomial,smul_eq_mul,mul_one]
      rw [hm,map_smul,genericPolynomialEquiv_monomial]
      exact (genericDistractionSpace k q I).smul_mem _
        (genericDistractionSpace_monomial k q I a (hI g hf a ha))
    change f∈genericDistractionSpace k q I
    simpa only [g,LinearEquiv.apply_symm_apply] using hg

theorem genericDistractionIdeal_eq_span
    (I : Ideal (MvPolynomial (Fin q) (GenericDistractionField k q))) :
    genericDistractionIdeal k q I = Ideal.span
      (genericFieldDistraction k q '' {a | MvPolynomial.monomial a 1∈I}) := by
  apply le_antisymm
  · intro f hf
    change f∈genericDistractionSpace k q I at hf
    induction hf using Submodule.span_induction with
    | mem x hx => exact Ideal.subset_span hx
    | zero => exact Ideal.zero_mem _
    | add x y _ _ hx hy => exact Ideal.add_mem _ hx hy
    | smul c x _ hx =>
      exact (Ideal.span (genericFieldDistraction k q '' {a | MvPolynomial.monomial a 1∈I})).restrictScalars
        (GenericDistractionField k q) |>.smul_mem c hx
  · apply Ideal.span_le.mpr
    rintro _ ⟨a,ha,rfl⟩
    exact genericDistractionSpace_monomial k q I a ha

attribute [local instance] MvPolynomial.gradedAlgebra

theorem genericDistractionIdeal_homogeneous
    (I : Ideal (MvPolynomial (Fin q) (GenericDistractionField k q))) :
    (genericDistractionIdeal k q I).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin q) (GenericDistractionField k q)) := by
  rw [genericDistractionIdeal_eq_span]
  apply Ideal.homogeneous_span
  rintro _ ⟨a,_,rfl⟩
  exact ⟨a.degree,genericFieldDistraction_homogeneous k q a⟩

theorem genericDistractionIdeal_map
    (I : Ideal (MvPolynomial (Fin q) (GenericDistractionField k q)))
    (hI : IsMonomial (GenericDistractionField k q) q I) :
    (I.restrictScalars (GenericDistractionField k q)).map (genericPolynomialEquiv k q).toLinearMap =
      (genericDistractionIdeal k q I).restrictScalars (GenericDistractionField k q) := by
  ext f
  rw [Submodule.mem_map]
  change (∃ g,g∈I ∧ genericPolynomialEquiv k q g=f) ↔ f∈genericDistractionIdeal k q I
  rw [mem_genericDistractionIdeal k q I hI]
  constructor
  · rintro ⟨g,hg,rfl⟩
    simpa only [LinearEquiv.symm_apply_apply] using hg
  · intro hf
    exact ⟨(genericPolynomialEquiv k q).symm f,hf,(genericPolynomialEquiv k q).apply_symm_apply f⟩

def genericDistractionQuotientEquiv
    (I : Ideal (MvPolynomial (Fin q) (GenericDistractionField k q)))
    (hI : IsMonomial (GenericDistractionField k q) q I) :
    (MvPolynomial (Fin q) (GenericDistractionField k q) ⧸ I) ≃ₗ[GenericDistractionField k q]
      (MvPolynomial (Fin q) (GenericDistractionField k q) ⧸ genericDistractionIdeal k q I) :=
  Submodule.Quotient.equiv (I.restrictScalars (GenericDistractionField k q))
    ((genericDistractionIdeal k q I).restrictScalars (GenericDistractionField k q))
    (genericPolynomialEquiv k q) (genericDistractionIdeal_map k q I hI)

theorem genericDistractionQuotientEquiv_mk
    (I : Ideal (MvPolynomial (Fin q) (GenericDistractionField k q)))
    (hI : IsMonomial (GenericDistractionField k q) q I)
    (f : MvPolynomial (Fin q) (GenericDistractionField k q)) :
    genericDistractionQuotientEquiv k q I hI (Ideal.Quotient.mk I f)=
      Ideal.Quotient.mk (genericDistractionIdeal k q I) (genericPolynomialEquiv k q f) := rfl
end NSP14.Lex
