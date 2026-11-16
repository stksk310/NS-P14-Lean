module

public import NSP14.Homological.GradedBetti

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory HomologicalComplex

namespace NSP14.Homological

universe u
variable (k σ : Type u) [Field k]
variable {M N : ModuleCat.{u} (VariableRing k σ)}
variable (G : GradedPolynomialModule k σ M) (H : GradedPolynomialModule k σ N)

/-- The actual chain map inherits the same coefficient-degree shift as the module map. -/
theorem koszulMap_homogeneous (f : M ⟶ N) (s : ℤ)
    (hf : ∀ q (a : coefficientModule k σ M),a∈G.degreeSpace q → f a∈H.degreeSpace (q+s))
    (xs : List σ) (i : ℕ) (q : ℤ) (a : coefficientModule k σ ((koszulList k σ xs M).X i))
    (ha : a∈(koszulChainGrading k σ M G xs i).degreeSpace q) :
    (koszulMap k σ xs f).f i a ∈ (koszulChainGrading k σ N H xs i).degreeSpace (q+s) := by
  induction xs generalizing i with
  | nil =>
    cases i with
    | zero => exact hf q a ha
    | succ i =>
      have hz : a=0 := (ModuleCat.subsingleton_of_isZero
        (koszul_piece_isZero_of_gt k σ [] M (i+1) (by simp))).elim _ _
      rw [hz,map_zero]
      exact Submodule.zero_mem _
  | cons x xs ih =>
    cases i with
    | zero =>
      rw [koszulChainGrading,GradedPolynomialModule.transport_mem] at ha ⊢
      have hn := congrArg (fun g => g.hom a)
        (scalarCone_map_snd (VariableRing k σ) (MvPolynomial.X x) (koszulMap k σ xs f) 0)
      simp only [ModuleCat.hom_comp,LinearMap.comp_apply] at hn
      change koszulSecondProjection k σ x xs N 0 ((koszulMap k σ (x::xs) f).f 0 a)∈_
      erw [hn]
      exact ih 0 _ ha
    | succ i =>
      rw [koszulChainGrading,GradedPolynomialModule.transport_mem] at ha ⊢
      have ha' := (GradedPolynomialModule.prod_mem _ _ _ _).mp ha
      apply (GradedPolynomialModule.prod_mem _ _ _ _).mpr
      have hn := scalarConePieceEquiv_natural (VariableRing k σ) (MvPolynomial.X x) (koszulMap k σ xs f) i a
      change scalarConePieceEquiv (koszulList k σ xs N) (MvPolynomial.X x) i
        ((koszulMap k σ (x::xs) f).f (i+1) a) = _ at hn
      change _∈(koszulChainGrading k σ N H xs i).degreeSpace (q+s) ∧
        _∈(koszulChainGrading k σ N H xs (i+1)).degreeSpace (q+s)
      erw [congrArg Prod.fst hn,congrArg Prod.snd hn]
      exact ⟨ih i _ ha'.1,ih (i+1) _ ha'.2⟩

noncomputable def gradedKoszulPieceEquiv (e : M ≅ N) (s : ℤ)
    (hf : ∀ q (a : coefficientModule k σ M),e.hom a∈H.degreeSpace (q+s) ↔ a∈G.degreeSpace q)
    (xs : List σ) (t : ℤ) (i : ℕ) :
    gradedKoszulSpace k σ M G xs t i ≃ₗ[k] gradedKoszulSpace k σ N H xs (t+s) i := by
  have hf' : ∀ q (b : coefficientModule k σ N),b∈H.degreeSpace q → e.inv b∈G.degreeSpace (q-s) := by
    intro q b hb
    apply (hf (q-s) (e.inv b)).mp
    simpa only [sub_add_cancel,← ModuleCat.comp_apply,Iso.inv_hom_id,ModuleCat.id_apply] using hb
  let f := (koszulFunctor k σ xs).mapIso e
  exact {
    toFun := fun a => ⟨f.hom.f i a.val,by
      have h := koszulMap_homogeneous k σ G H e.hom s (fun q a ha => (hf q a).mpr ha) xs i
        (t-(i:ℤ)) a.val a.property
      change (koszulMap k σ xs e.hom).f i a.val ∈
        (koszulChainGrading k σ N H xs i).degreeSpace ((t+s)-(i:ℤ))
      have he : t-(i:ℤ)+s=(t+s)-(i:ℤ) := by omega
      rw [← he]
      exact h⟩
    invFun := fun b => ⟨f.inv.f i b.val,by
      have h := koszulMap_homogeneous k σ H G e.inv (-s) (by simpa only [sub_eq_add_neg] using hf') xs i
        ((t+s)-(i:ℤ)) b.val b.property
      change (koszulMap k σ xs e.inv).f i b.val ∈
        (koszulChainGrading k σ M G xs i).degreeSpace (t-(i:ℤ))
      have he : (t+s)-(i:ℤ)+(-s)=t-(i:ℤ) := by omega
      rw [← he]
      exact h⟩
    left_inv := fun a => by
      apply Subtype.ext
      have he := congrArg (fun g => g.f i) f.hom_inv_id
      exact congrArg (fun g => g.hom a.val) he
    right_inv := fun b => by
      apply Subtype.ext
      have he := congrArg (fun g => g.f i) f.inv_hom_id
      exact congrArg (fun g => g.hom b.val) he
    map_add' := fun a b => by
      apply Subtype.ext
      exact (f.hom.f i).hom.map_add a.val b.val
    map_smul' := fun c a => by
      apply Subtype.ext
      exact (coefficientMap k σ (f.hom.f i)).map_smul c a.val }

/-- The same actual module isomorphism, with its proved internal-degree shift. -/
noncomputable def gradedKoszulIso (e : M ≅ N) (s : ℤ)
    (hf : ∀ q (a : coefficientModule k σ M),e.hom a∈H.degreeSpace (q+s) ↔ a∈G.degreeSpace q)
    (xs : List σ) (t : ℤ) :
    gradedKoszulComplex k σ M G xs t ≅ gradedKoszulComplex k σ N H xs (t+s) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (gradedKoszulPieceEquiv k σ G H e s hf xs t i).toModuleIso) (by
      intro i j hij
      change j+1=i at hij
      subst i
      simp only [gradedKoszulComplex,ChainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      apply Subtype.ext
      have he := congrArg (fun g => g.hom a.val) ((koszulMap k σ xs e.hom).comm (j+1) j)
      exact he)

end NSP14.Homological
