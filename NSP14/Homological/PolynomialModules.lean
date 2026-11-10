module

public import NSP14.Homological.Presentation
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Polynomial.Basic

@[expose] public section

open scoped Classical

namespace NSP14.Homological

/-- Transfer finite generation when every scalar action has an explicit smaller-ring representative. -/
theorem finite_of_action_reduction (R A M : Type*) [Semiring R] [Semiring A] [AddCommMonoid M]
    [Module R M] [Module A M] [Module.Finite R M] (reduce : R → A)
    (hreduce : ∀ (r : R) (m : M), r • m = reduce r • m) : Module.Finite A M := by
  obtain ⟨s,hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  let U : Submodule R M :=
    { carrier := Submodule.span A (s : Set M)
      zero_mem' := (Submodule.span A (s : Set M)).zero_mem
      add_mem' := (Submodule.span A (s : Set M)).add_mem
      smul_mem' r m hm := by
        rw [hreduce]
        exact (Submodule.span A (s : Set M)).smul_mem _ hm }
  have hu : Submodule.span R (s : Set M) ≤ U := Submodule.span_le.mpr (fun m hm => Submodule.subset_span hm)
  rw [hs] at hu
  refine Module.Finite.of_fg_top ⟨s,?_⟩
  apply top_unique
  intro m _
  exact hu (Submodule.mem_top : m∈(⊤ : Submodule R M))

end NSP14.Homological

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k] [Nontrivial k]

noncomputable def nonXPolynomialInclusion : S.PolynomialRing k →ₐ[k] S.FullPolynomialRing k :=
  MvPolynomial.rename (fun a : S.NonXAtom => (⟨a.val,a.property.1⟩ : S.AtomExponent))

omit [Nontrivial k] in
theorem fullPolynomial_nonX_compat :
    (S.fullPolynomialToG k).comp (S.nonXPolynomialInclusion k)=S.polynomialToG k := by
  apply MvPolynomial.algHom_ext
  intro a
  change S.fullPolynomialToG k (MvPolynomial.rename _ (MvPolynomial.X a))=S.polynomialToG k (MvPolynomial.X a)
  exact (congrArg (S.fullPolynomialToG k)
    (MvPolynomial.rename_X (fun a : S.NonXAtom => (⟨a.val,a.property.1⟩ : S.AtomExponent)) a)).trans
      ((S.fullPolynomialToG_X k ⟨a.val,a.property.1⟩).trans (S.polynomialToG_X k a).symm)

noncomputable instance fullPolynomialModuleT : Module (S.FullPolynomialRing k) ((S.xMultiply k).ker) :=
  inferInstanceAs (Module (S.FullPolynomialRing k) (S.terminalIdeal k))

noncomputable instance fullPolynomialScalarTowerT : IsScalarTower k (S.FullPolynomialRing k) ((S.xMultiply k).ker) where
  smul_assoc r p a := Subtype.ext (smul_assoc r p a.val)

/-- Delete the x variable algebraically. It acts as zero on the actual T, not on G. -/
noncomputable def removeXPolynomial : S.FullPolynomialRing k →ₐ[k] S.PolynomialRing k :=
  MvPolynomial.aeval (fun a => if h : a.val.val=S.multiplicity then 0 else
    MvPolynomial.X (⟨a.val,a.property,h⟩ : S.NonXAtom))

omit [Nontrivial k] in
theorem terminal_full_variable_action (x : S.AtomExponent) (a : (S.xMultiply k).ker) :
    (MvPolynomial.X x : S.FullPolynomialRing k) • a = S.removeXPolynomial k (MvPolynomial.X x) • a := by
  rw [removeXPolynomial,MvPolynomial.aeval_X]
  by_cases hm : x.val.val=S.multiplicity
  · simp only [dite_eq_left hm,zero_smul]
    apply Subtype.ext
    change S.fullPolynomialToG k (MvPolynomial.X x)*a.val=0
    rw [S.fullPolynomialToG_X]
    have he : x.val=S.multiplicityExponent := Subtype.ext hm
    rw [he,mul_comm]
    exact a.property
  · simp only [dite_eq_right hm]
    apply Subtype.ext
    change S.fullPolynomialToG k (MvPolynomial.X x)*a.val=
      S.polynomialToG k (MvPolynomial.X (⟨x.val,x.property,hm⟩ : S.NonXAtom))*a.val
    rw [S.fullPolynomialToG_X]
    exact congrArg (fun b => b*a.val) (S.polynomialToG_X k ⟨x.val,x.property,hm⟩).symm

omit [Nontrivial k] in
theorem terminal_removeX_action (p : S.FullPolynomialRing k) (a : (S.xMultiply k).ker) :
    p • a=S.removeXPolynomial k p • a := by
  have hp : ∀ a : (S.xMultiply k).ker, p • a=S.removeXPolynomial k p • a := by
    induction p using MvPolynomial.induction_on with
    | C c =>
      intro a
      rw [show S.removeXPolynomial k (MvPolynomial.C c) = MvPolynomial.C c from
        (S.removeXPolynomial k).commutes c]
      change (algebraMap k (S.FullPolynomialRing k) c) • a =
        (algebraMap k (S.PolynomialRing k) c) • a
      rw [algebraMap_smul,algebraMap_smul]
    | add p q hp hq =>
      intro a
      rw [map_add,add_smul,add_smul,hp,hq]
    | mul_X p x hp =>
      intro a
      rw [map_mul,mul_smul,mul_smul,hp,S.terminal_full_variable_action]
  exact hp a

noncomputable instance fullPolynomialGFinite : Module.Finite (S.FullPolynomialRing k) (S.TangentAlgebra k) :=
  Module.Finite.of_surjective (Algebra.linearMap (S.FullPolynomialRing k) (S.TangentAlgebra k))
    (S.fullPolynomialToG_surjective k)

noncomputable instance nonXPolynomialAFinite : Module.Finite (S.PolynomialRing k) (S.HeadAlgebra k) :=
  Module.Finite.of_surjective (Algebra.linearMap (S.PolynomialRing k) (S.HeadAlgebra k))
    (S.polynomialToA_surjective k)

noncomputable instance nonXPolynomialQFinite : Module.Finite (S.PolynomialRing k) (S.AperyAlgebra k) :=
  Module.Finite.of_surjective (Algebra.linearMap (S.PolynomialRing k) (S.AperyAlgebra k))
    (S.polynomialToQ_surjective k)

noncomputable def nonXPolynomialToFormalG : S.PolynomialRing k →ₐ[k] S.FormalTangentAlgebra k :=
  (S.completedGradedAlgEquiv k).toAlgHom.comp (S.polynomialToG k)

noncomputable instance nonXPolynomialAlgebraFormalG : Algebra (S.PolynomialRing k) (S.FormalTangentAlgebra k) :=
  (S.nonXPolynomialToFormalG k).toRingHom.toAlgebra

noncomputable def completedNonXPolynomialLinearEquiv :
    S.TangentAlgebra k ≃ₗ[S.PolynomialRing k] S.FormalTangentAlgebra k where
  toEquiv := (S.completedGradedAlgEquiv k).toEquiv
  map_add' := (S.completedGradedAlgEquiv k).map_add
  map_smul' p a := by
    change S.completedGradedAlgEquiv k (S.polynomialToG k p*a) =
      S.completedGradedAlgEquiv k (S.polynomialToG k p)*S.completedGradedAlgEquiv k a
    exact map_mul _ _ _

variable [IsNoetherianRing k]

noncomputable instance fullPolynomialTFinite : Module.Finite (S.FullPolynomialRing k) ((S.xMultiply k).ker) :=
  inferInstanceAs (Module.Finite (S.FullPolynomialRing k) ((S.terminalIdeal k).restrictScalars (S.FullPolynomialRing k)))

noncomputable instance nonXPolynomialTFinite : Module.Finite (S.PolynomialRing k) ((S.xMultiply k).ker) :=
  NSP14.Homological.finite_of_action_reduction (S.FullPolynomialRing k) (S.PolynomialRing k)
    ((S.xMultiply k).ker) (S.removeXPolynomial k) (S.terminal_removeX_action k)

noncomputable instance nonXPolynomialNFinite :
    Module.Finite (S.PolynomialRing k) ((S.nonAperyIdeal k).restrictScalars k) :=
  inferInstanceAs (Module.Finite (S.PolynomialRing k)
    ((S.nonAperyIdeal k).restrictScalars (S.PolynomialRing k)))

end NSP14.NumericalSemigroup
