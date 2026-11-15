module
public import NSP14.Homological.KoszulChainBasis
public import NSP14.Homological.GradedBasis
public import NSP14.Homological.KoszulCoefficientSlots
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
open scoped Classical
namespace NSP14.Homological
variable (k σ : Type) [Field k] {J : Type}
  (M : ModuleCat (VariableRing k σ)) (G : GradedPolynomialModule k σ M)
  (b : Module.Basis J k (coefficientModule k σ M)) (deg : J → ℤ)
  (hb : ∀ a,b a ∈ G.degreeSpace (deg a))

include hb in
theorem gradedBasis_transport (N : ModuleCat (VariableRing k σ)) (e : M ≅ N) (a : J) :
    (b.map (((ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapIso e).toLinearEquiv)) a ∈
      (G.transport e).degreeSpace (deg a) := by
  rw [GradedPolynomialModule.transport_mem]
  change e.inv (e.hom (b a)) ∈ G.degreeSpace (deg a)
  have he : e.inv (e.hom (b a))=b a := by
    change (e.hom ≫ e.inv) (b a)=b a
    rw [e.hom_inv_id]
    rfl
  rw [he]
  exact hb a

include hb in
theorem koszulSlotBasis_homogeneous (xs : List σ) (i : ℕ)
    (a : KoszulSlot xs.length i × J) :
    koszulSlotBasis k σ M b xs i a ∈ (koszulChainGrading k σ M G xs i).degreeSpace (deg a.2) := by
  induction xs generalizing i with
  | nil =>
    cases i with
    | zero =>
      change (b.reindex (Equiv.punitProd J).symm) a ∈ G.degreeSpace (deg a.2)
      erw [Module.Basis.reindex_apply]
      exact hb a.2
    | succ i => exact a.1.elim
  | cons x xs ih =>
    cases i with
    | zero =>
      exact gradedBasis_transport k σ _ (koszulChainGrading k σ M G xs 0)
        (koszulSlotBasis k σ M b xs 0) (fun a => deg a.2) (ih 0) _
        (scalarConeZeroIso (VariableRing k σ) (MvPolynomial.X x) (koszulList k σ xs M)).symm a
    | succ i =>
      apply gradedBasis_transport k σ _
        ((koszulChainGrading k σ M G xs i).prod (koszulChainGrading k σ M G xs (i+1)))
        (((koszulSlotBasis k σ M b xs i).prod (koszulSlotBasis k σ M b xs (i+1))).reindex
          (Equiv.sumProdDistrib (KoszulSlot xs.length i) (KoszulSlot xs.length (i+1)) J).symm)
        (fun a => deg a.2) ?_ _
        (scalarConePieceEquiv (koszulList k σ xs M) (MvPolynomial.X x) i).symm.toModuleIso a
      intro a
      rcases a with ⟨s,j⟩
      cases s with
      | inl s =>
        erw [Module.Basis.reindex_apply]
        change ((koszulSlotBasis k σ M b xs i).prod (koszulSlotBasis k σ M b xs (i+1))) (.inl (s,j)) ∈ _
        erw [GradedPolynomialModule.prod_mem]
        rw [Module.Basis.prod_apply_inl_fst (koszulSlotBasis k σ M b xs i)
          (koszulSlotBasis k σ M b xs (i+1)) (s,j),
          Module.Basis.prod_apply_inl_snd (koszulSlotBasis k σ M b xs i)
          (koszulSlotBasis k σ M b xs (i+1)) (s,j)]
        exact ⟨ih i (s,j),Submodule.zero_mem _⟩
      | inr s =>
        erw [Module.Basis.reindex_apply]
        change ((koszulSlotBasis k σ M b xs i).prod (koszulSlotBasis k σ M b xs (i+1))) (.inr (s,j)) ∈ _
        erw [GradedPolynomialModule.prod_mem]
        rw [Module.Basis.prod_apply_inr_fst (koszulSlotBasis k σ M b xs i)
          (koszulSlotBasis k σ M b xs (i+1)) (s,j),
          Module.Basis.prod_apply_inr_snd (koszulSlotBasis k σ M b xs i)
          (koszulSlotBasis k σ M b xs (i+1)) (s,j)]
        exact ⟨Submodule.zero_mem _,ih (i+1) (s,j)⟩
/-- Coordinates of the actual recursive chain basis are exactly the
actual slot projection followed by the original coefficient coordinates. -/
theorem koszulSlotBasis_repr (xs : List σ) (i : ℕ)
    (a : coefficientModule k σ ((koszulList k σ xs M).X i))
    (s : KoszulSlot xs.length i) (j : J) :
    (koszulSlotBasis k σ M b xs i).repr a (s,j)=b.repr (coefficientSlotOut k σ M xs i s a) j := by
  induction xs generalizing i with
  | nil =>
    cases i with
    | zero =>
      erw [Module.Basis.repr_reindex_apply]
    | succ i => exact s.elim
  | cons x xs ih =>
    cases i with
    | zero =>
      rw [koszulSlotBasis,Module.Basis.map_repr]
      change (koszulSlotBasis k σ M b xs 0).repr
        ((scalarConeZeroIso (VariableRing k σ) (MvPolynomial.X x) (koszulList k σ xs M)).hom a) (s,j)=
        b.repr (coefficientSlotOut k σ M xs 0 s
          ((scalarConeZeroIso (VariableRing k σ) (MvPolynomial.X x) (koszulList k σ xs M)).hom a)) j
      exact ih 0 _ s
    | succ i =>
      cases s with
      | inl s =>
        rw [koszulSlotBasis,Module.Basis.map_repr]
        erw [Module.Basis.repr_reindex_apply]
        change ((koszulSlotBasis k σ M b xs i).prod (koszulSlotBasis k σ M b xs (i+1))).repr
          (scalarConePieceEquiv (koszulList k σ xs M) (MvPolynomial.X x) i a) (.inl (s,j))=_
        rw [Module.Basis.prod_repr_inl]
        change (koszulSlotBasis k σ M b xs i).repr
          (scalarConePieceEquiv (koszulList k σ xs M) (MvPolynomial.X x) i a).1 (s,j)=
          b.repr (coefficientSlotOut k σ M xs i s
            (scalarConePieceEquiv (koszulList k σ xs M) (MvPolynomial.X x) i a).1) j
        exact ih i _ s
      | inr s =>
        rw [koszulSlotBasis,Module.Basis.map_repr]
        erw [Module.Basis.repr_reindex_apply]
        change ((koszulSlotBasis k σ M b xs i).prod (koszulSlotBasis k σ M b xs (i+1))).repr
          (scalarConePieceEquiv (koszulList k σ xs M) (MvPolynomial.X x) i a) (.inr (s,j))=_
        rw [Module.Basis.prod_repr_inr]
        change (koszulSlotBasis k σ M b xs (i+1)).repr
          (scalarConePieceEquiv (koszulList k σ xs M) (MvPolynomial.X x) i a).2 (s,j)=
          b.repr (coefficientSlotOut k σ M xs (i+1) s
            (scalarConePieceEquiv (koszulList k σ xs M) (MvPolynomial.X x) i a).2) j
        exact ih (i+1) _ s

theorem coefficientSlotOut_In (xs : List σ) (i : ℕ) (s t : KoszulSlot xs.length i)
    (a : coefficientModule k σ M) :
    coefficientSlotOut k σ M xs i t (coefficientSlotIn k σ M xs i s a)=if s=t then a else 0 := by
  change (koszulSlotIn k σ M xs i s ≫ koszulSlotOut k σ M xs i t) a=_
  rw [koszulSlotIn_Out]
  by_cases he : s=t <;> simp only [he,ite_true,ite_false,ModuleCat.id_apply,
    ModuleCat.hom_zero,LinearMap.zero_apply]

theorem koszulSlotBasis_apply (xs : List σ) (i : ℕ) (s : KoszulSlot xs.length i) (j : J) :
    koszulSlotBasis k σ M b xs i (s,j)=coefficientSlotIn k σ M xs i s (b j) := by
  apply (koszulSlotBasis k σ M b xs i).repr.injective
  ext a
  rcases a with ⟨t,l⟩
  rw [Module.Basis.repr_self,koszulSlotBasis_repr,coefficientSlotOut_In]
  by_cases he : s=t
  · subst t
    simp only [ite_true,Module.Basis.repr_self,Finsupp.single_apply,Prod.mk.injEq,true_and]
  · simp only [map_zero,Finsupp.zero_apply,Finsupp.single_apply,
      Prod.mk.injEq,he,false_and,ite_false]
end NSP14.Homological
