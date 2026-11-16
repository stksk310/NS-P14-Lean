module
public import NSP14.Homological.VariableIdealReduction
public import NSP14.Homological.ResidueBetti
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] [Fintype σ]

omit [Fintype σ] in
theorem residue_list_homology_finrank (xs : List σ) (i : ℕ) :
    Module.finrank k (((coefficientKoszulListFunctor k σ xs).obj (residueField k σ)).homology i)=
      xs.length.choose i := by
  let e := koszulHomologyZeroActionIso k σ xs (residueField k σ)
    (fun x _ a => residueField_variable k σ x a) i
  let F := ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))
  let eC := (((koszulList k σ xs (residueField k σ)).sc i).mapHomologyIso F) ≪≫ F.mapIso e
  have hh := eC.toLinearEquiv.finrank_eq
  change Module.finrank k (((coefficientKoszulListFunctor k σ xs).obj (residueField k σ)).homology i)=
    Module.finrank k (coefficientModule k σ ((koszulList k σ xs (residueField k σ)).X i)) at hh
  rw [hh,koszul_chain_finrank]
  have he := (residueCoefficientIso k σ).toLinearEquiv.finrank_eq
  change Module.finrank k (coefficientModule k σ (residueField k σ))=Module.finrank k k at he
  rw [he,Module.finrank_self,Nat.one_mul]

/-- Remove every complementary live variable from the same actual
quotient, then identify the full variable quotient with its residue field. -/
noncomputable def variableIdealHomologyIso (xs : List σ) (hx : xs.Nodup) (i : ℕ) :
    koszulHomologyK k σ (variableQuotientModule k σ xs) i ≅
      ((coefficientKoszulListFunctor k σ xs).obj (residueField k σ)).homology i := by
  let ys := (variableList k σ).filter (fun x => decide (x ∉ xs))
  have hyn : ys.Nodup := List.Nodup.filter _ (variableList_nodup k σ)
  have hdy : ∀ x ∈ ys,x ∉ xs := by
    intro x hx
    have h := (List.mem_filter.mp hx).2
    simpa only [decide_eq_true_eq] using h
  have hall : ∀ x : σ,x ∈ ys++xs := by
    intro x
    by_cases h : x ∈ xs
    · exact List.mem_append.mpr (Or.inr h)
    · apply List.mem_append.mpr
      left
      simp only [ys,List.mem_filter,decide_eq_true_eq]
      exact ⟨mem_variableList k σ x,h⟩
  have hn : (ys++xs).Nodup := List.nodup_append.mpr ⟨hyn,hx,by
    intro a ha b hb he
    exact hdy a ha (he.symm ▸ hb)⟩
  have hall' : ∀ x : σ,x ∈ ys.reverse++xs := by
    intro x
    rcases List.mem_append.mp (hall x) with h|h
    · exact List.mem_append.mpr (Or.inl (List.mem_reverse.mpr h))
    · exact List.mem_append.mpr (Or.inr h)
  let e1 := (actionFullPolynomialHomologyIso (VariableRing k σ) (variableQuotientModule k σ xs)
    k σ (AlgHom.id k (VariableRing k σ)) (ys++xs) hall hn i).symm
  let e2 := removeVariableListHomologyIso k σ xs ys xs hyn hdy i
  let e3 := (homologyFunctor _ (ComplexShape.down ℕ) i).mapIso
    ((actionCoefficientFunctor (VariableRing k σ) k (xs.map (fun x => MvPolynomial.X x))).mapIso
      (fullVariableQuotientIso k σ (ys.reverse++xs) hall'))
  let e4 := coefficientComplexHomologyIso k
    (polynomialActionCoefficientIso k (VariableRing k σ) σ (AlgHom.id k (VariableRing k σ)) xs (residueField k σ)) i
  exact e1 ≪≫ e2 ≪≫ e3 ≪≫ e4

/-- Actual ordinary Betti numbers of a quotient by distinct coordinate
variables, including the empty ideal and all homological rows. -/
theorem variable_ideal_betti (xs : List σ) (hx : xs.Nodup) (i : ℕ) :
    totalBetti k σ (ModuleCat.of (VariableRing k σ) ((VariableRing k σ) ⧸ variablesIdeal k σ xs)) i=
      xs.length.choose i := by
  have h := (variableIdealHomologyIso k σ xs hx i).toLinearEquiv.finrank_eq
  change totalBetti k σ (ModuleCat.of (VariableRing k σ)
    ((VariableRing k σ) ⧸ variablesIdeal k σ xs)) i=_ at h
  exact h.trans (residue_list_homology_finrank k σ xs i)

end NSP14.Homological
