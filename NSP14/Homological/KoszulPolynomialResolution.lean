module

public import NSP14.Homological.ConeExactness
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.Algebra.Category.ModuleCat.Projective

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace NSP14.Homological

universe u v
variable (k : Type u) (σ : Type v) [Field k]

/-- The ideal of the actual variables occurring in the list. -/
noncomputable def variablesIdeal (xs : List σ) : Ideal (VariableRing k σ) :=
  Ideal.span (MvPolynomial.X '' {x | x ∈ xs})

theorem variablesIdeal_nil : variablesIdeal k σ [] = ⊥ := by
  simp [variablesIdeal]

theorem variablesIdeal_cons (x : σ) (xs : List σ) :
    variablesIdeal k σ (x::xs) = Ideal.span {MvPolynomial.X x} ⊔ variablesIdeal k σ xs := by
  classical
  have he : {y : σ | y ∈ x::xs} = {x} ∪ {y | y ∈ xs} := by ext y; simp
  simp only [variablesIdeal, he, Set.image_union, Set.image_singleton, Ideal.span_union]

theorem polynomial_variable_submodule (xs : List σ) :
    koszulVariableSubmodule k σ xs (ModuleCat.of (VariableRing k σ) (VariableRing k σ)) =
      variablesIdeal k σ xs := by
  induction xs with
  | nil => exact (variablesIdeal_nil k σ).symm
  | cons x xs ih =>
    rw [koszulVariableSubmodule, ih, variablesIdeal_cons]
    congr 1
    exact Ideal.range_mul' (MvPolynomial.X x)

theorem variable_not_mem_variablesIdeal (xs : List σ) (x : σ) (hx : x ∉ xs) :
    (MvPolynomial.X x : VariableRing k σ) ∉ variablesIdeal k σ xs := by
  classical
  intro h
  have hm : Finsupp.single x 1 ∈ (MvPolynomial.X x : VariableRing k σ).support := by
    simp [MvPolynomial.X]
  obtain ⟨y,hy,hne⟩ := MvPolynomial.mem_ideal_span_X_image.mp h _ hm
  have : y=x := by
    by_contra hn
    simp [Ne.symm hn] at hne
  subst y
  exact hx hy

theorem zero_boundary_membership (xs : List σ)
    (a : (koszulList k σ xs (ModuleCat.of (VariableRing k σ) (VariableRing k σ))).X 0) :
    (koszulZeroIso k σ xs _).hom a ∈ variablesIdeal k σ xs ↔
      a ∈ ((koszulList k σ xs _).d 1 0).hom.range := by
  rw [← polynomial_variable_submodule, ← koszul_zero_boundary]
  constructor
  · rintro ⟨z,hz⟩
    refine ⟨z,?_⟩
    exact (koszulZeroIso k σ xs _).toLinearEquiv.injective hz
  · rintro ⟨z,rfl⟩
    exact ⟨z,rfl⟩

/-- Each new variable acts injectively modulo all previously processed variables. -/
theorem polynomial_variable_regular (xs : List σ) (x : σ) (hx : x ∉ xs)
    (a : (koszulList k σ xs (ModuleCat.of (VariableRing k σ) (VariableRing k σ))).X 0)
    (ha : (MvPolynomial.X x : VariableRing k σ) • a ∈
      ((koszulList k σ xs _).d 1 0).hom.range) :
    a ∈ ((koszulList k σ xs _).d 1 0).hom.range := by
  apply (zero_boundary_membership k σ xs a).mp
  have hp : (variablesIdeal k σ xs).IsPrime := MvPolynomial.span_X_image_isPrime _
  have hh := (zero_boundary_membership k σ xs _).mpr ha
  rw [map_smul] at hh
  exact (hp.mem_or_mem hh).resolve_left (variable_not_mem_variablesIdeal k σ xs x hx)

/-- Positive exactness is proved for a list of distinct polynomial variables. -/
theorem koszul_polynomial_exact_positive (xs : List σ) (hxs : xs.Nodup) :
    ∀ i, (koszulList k σ xs (ModuleCat.of (VariableRing k σ) (VariableRing k σ))).ExactAt (i+1) := by
  induction xs with
  | nil =>
    intro i
    exact HomologicalComplex.ExactAt.of_isZero
      (koszul_piece_isZero_of_gt k σ [] _ (i+1) (by simp))
  | cons x xs ih =>
    exact scalarCone_exact_positive _ (MvPolynomial.X x)
      (ih (List.nodup_cons.mp hxs).2)
      (polynomial_variable_regular k σ xs x (List.nodup_cons.mp hxs).1)

/-- The chain groups are free over P, including the zero groups above the list length. -/
theorem koszul_chain_free (xs : List σ) (M : ModuleCat (VariableRing k σ))
    [Module.Free (VariableRing k σ) M] (i : ℕ) :
    Module.Free (VariableRing k σ) ((koszulList k σ xs M).X i) := by
  induction xs generalizing i with
  | nil =>
    by_cases hi : i=0
    · subst i
      exact inferInstanceAs (Module.Free (VariableRing k σ) M)
    · have : Subsingleton ((koszulList k σ [] M).X i) :=
        ModuleCat.subsingleton_of_isZero (koszul_piece_isZero_of_gt k σ [] M i (by simp; omega))
      infer_instance
  | cons x xs ih =>
    cases i with
    | zero => exact Module.Free.of_equiv (koszulZeroIso k σ (x::xs) M).symm.toLinearEquiv
    | succ i =>
      let : Module.Free (VariableRing k σ) ((koszulList k σ xs M).X i) := ih i
      let : Module.Free (VariableRing k σ) ((koszulList k σ xs M).X (i+1)) := ih (i+1)
      let e := koszulConsPieceIso k σ x xs M i ≪≫ ModuleCat.biprodIsoProd _ _
      exact Module.Free.of_equiv
        (M := (koszulList k σ xs M).X i × (koszulList k σ xs M).X (i+1)) e.symm.toLinearEquiv

end NSP14.Homological
