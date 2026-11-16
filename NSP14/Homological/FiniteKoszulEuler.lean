module
public import NSP14.Homological.BettiEuler
public import NSP14.Homological.KoszulChainDimension
@[expose] public section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace NSP14.Homological
universe u
variable (k : Type u) [Field k]

theorem shortComplex_homology_rank (S : ShortComplex (ModuleCat.{u} k))
    [Module.Finite k S.X₂] :
    Module.finrank k S.homology + Module.finrank k S.f.hom.range +
      Module.finrank k S.g.hom.range = Module.finrank k S.X₂ := by
  have hq := S.moduleCatToCycles.range.finrank_quotient_add_finrank
  have he := (S.moduleCatHomologyIso).toLinearEquiv.finrank_eq
  change Module.finrank k S.homology = Module.finrank k (S.g.hom.ker ⧸ S.moduleCatToCycles.range) at he
  have hr := (Submodule.equivMapOfInjective S.g.hom.ker.subtype
    (Submodule.injective_subtype _) S.moduleCatToCycles.range).finrank_eq
  have hm : S.moduleCatToCycles.range.map S.g.hom.ker.subtype=S.f.hom.range := by
    rw [← LinearMap.range_comp]
    congr 1
  rw [hm] at hr
  have hn := S.g.hom.finrank_range_add_finrank_ker
  omega

noncomputable def chainBoundaryRank (K : ChainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) : ℕ :=
  Module.finrank k (K.d i (i-1)).hom.range

theorem chainBoundaryRank_zero (K : ChainComplex (ModuleCat.{u} k) ℕ) : chainBoundaryRank k K 0=0 := by
  unfold chainBoundaryRank
  rw [K.shape 0 0 (by simp [ComplexShape.down])]
  change Module.finrank k (0 : K.X 0 →ₗ[k] K.X 0).range=0
  rw [LinearMap.range_zero,finrank_bot]

theorem chainBoundaryRank_succ (K : ChainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :
    chainBoundaryRank k K (i+1)=Module.finrank k (K.d (i+1) i).hom.range :=
  congrArg (fun n : ℕ => Module.finrank k (K.d (i+1) n).hom.range) (show i+1-1=i by omega)

theorem chain_homology_rank (K : ChainComplex (ModuleCat.{u} k) ℕ)
    [∀ i,Module.Finite k (K.X i)] (i : ℕ) :
    Module.finrank k (K.homology i)+chainBoundaryRank k K i+chainBoundaryRank k K (i+1)=
      Module.finrank k (K.X i) := by
  have : Module.Finite k (K.sc i).X₂ := inferInstanceAs (Module.Finite k (K.X i))
  have h := shortComplex_homology_rank k (K.sc i)
  change Module.finrank k (K.homology i)+
    Module.finrank k (K.d ((ComplexShape.down ℕ).prev i) i).hom.range+
    Module.finrank k (K.d i ((ComplexShape.down ℕ).next i)).hom.range = _ at h
  have hp : (ComplexShape.down ℕ).prev i=i+1 := by simp
  have hn : (ComplexShape.down ℕ).next i=i-1 := by cases i <;> simp
  rw [hp,hn] at h
  change Module.finrank k (K.homology i)+Module.finrank k (K.d (i+1) i).hom.range+
    Module.finrank k (K.d i (i-1)).hom.range=Module.finrank k (K.X i) at h
  rw [chainBoundaryRank_succ]
  change Module.finrank k (K.homology i)+Module.finrank k (K.d i (i-1)).hom.range+
    Module.finrank k (K.d (i+1) i).hom.range=Module.finrank k (K.X i)
  omega

variable (σ : Type u) [Fintype σ]
noncomputable def koszulBoundaryRank (M : ModuleCat.{u} (VariableRing k σ)) (i : ℕ) : ℕ :=
  chainBoundaryRank k (coefficientKoszulComplex k σ M) i

theorem koszulBoundaryRank_eq_zero_of_gt (M : ModuleCat.{u} (VariableRing k σ))
    (i : ℕ) (hi : Fintype.card σ < i) : koszulBoundaryRank k σ M i=0 := by
  have hz := koszul_piece_isZero_of_gt k σ (variableList k σ) M i
    (by simpa only [variableList_length] using hi)
  have : Subsingleton ((coefficientKoszulComplex k σ M).X i) :=
    (show Subsingleton ((koszulList k σ (variableList k σ) M).X i) from
      ModuleCat.subsingleton_of_isZero hz)
  unfold koszulBoundaryRank chainBoundaryRank
  have hd : ((coefficientKoszulComplex k σ M).d i (i-1)).hom=0 := by
    ext a
    have ha : a=0 := Subsingleton.elim _ _
    simp only [ha,map_zero]
  rw [hd,LinearMap.range_zero,finrank_bot]

variable (M : ModuleCat.{u} (VariableRing k σ))
  [Module.Finite (VariableRing k σ) M] [Module.Finite k (coefficientModule k σ M)]

noncomputable instance coefficientKoszulChainFinite (i : ℕ) :
    Module.Finite k ((coefficientKoszulComplex k σ M).X i) :=
  koszul_chain_coefficient_finite k σ (variableList k σ) M i

theorem koszul_betti_chain_rank (i : ℕ) :
    totalBetti k σ M i+koszulBoundaryRank k σ M i+koszulBoundaryRank k σ M (i+1)=
      Module.finrank k (coefficientModule k σ M)*(Fintype.card σ).choose i := by
  have h := chain_homology_rank k (coefficientKoszulComplex k σ M) i
  rw [(coefficientKoszulHomologyIso k σ M i).toLinearEquiv.finrank_eq] at h
  change totalBetti k σ M i+koszulBoundaryRank k σ M i+koszulBoundaryRank k σ M (i+1)=_ at h
  have hc := koszul_chain_finrank k σ (variableList k σ) M i
  change Module.finrank k ((coefficientKoszulComplex k σ M).X i)=_ at hc
  rw [variableList_length] at hc
  rw [hc] at h
  exact h

theorem totalBetti_eq_zero_of_subsingleton [Subsingleton M] (i : ℕ) : totalBetti k σ M i=0 := by
  have : Subsingleton (coefficientModule k σ M) := inferInstanceAs (Subsingleton M)
  have h := koszul_betti_chain_rank k σ M i
  rw [Module.finrank_zero_of_subsingleton,Nat.zero_mul] at h
  omega

theorem bettiEuler_eq_zero_of_subsingleton [Subsingleton M] (j : ℕ) : bettiEuler k σ M j=0 := by
  induction j with
  | zero => simp only [bettiEuler_zero,totalBetti_eq_zero_of_subsingleton,Nat.cast_zero]
  | succ j ih => rw [bettiEuler_succ,totalBetti_eq_zero_of_subsingleton,ih];simp

/-- The actual finite-chain Euler formula, not an application of exact-complex
Euler to an unconstructed minimal resolution. -/
theorem finite_koszul_bettiEuler (hr : 1 ≤ Fintype.card σ) (j : ℕ) :
    bettiEuler k σ M j = ((Fintype.card σ-1).choose j : ℤ)*
      Module.finrank k (coefficientModule k σ M) - (koszulBoundaryRank k σ M (j+1) : ℤ) := by
  induction j with
  | zero =>
    have h := koszul_betti_chain_rank k σ M 0
    have hz := chainBoundaryRank_zero k (coefficientKoszulComplex k σ M)
    change koszulBoundaryRank k σ M 0=0 at hz
    simp only [bettiEuler_zero,Nat.choose_zero_right,Nat.mul_one,Nat.cast_one,one_mul] at h ⊢
    omega
  | succ j ih =>
    have h := koszul_betti_chain_rank k σ M (j+1)
    have hc := Nat.choose_succ_succ (Fintype.card σ-1) j
    change (Fintype.card σ-1+1).choose (j+1)=_ at hc
    rw [Nat.sub_add_cancel hr] at hc
    rw [bettiEuler_succ,ih]
    have hq : (totalBetti k σ M (j+1) : ℤ)+(koszulBoundaryRank k σ M (j+1) : ℤ)+
        koszulBoundaryRank k σ M (j+2) =
        (Module.finrank k (coefficientModule k σ M) : ℤ)*((Fintype.card σ).choose (j+1) : ℕ) := by exact_mod_cast h
    push_cast [hc] at hq
    nlinarith
/-- The terminal Euler sum vanishes for finite-length P modules.
The source G over r+1 variables is not among these finite-k modules. -/
theorem finite_koszul_bettiEuler_top (hr : 1 ≤ Fintype.card σ) :
    bettiEuler k σ M (Fintype.card σ)=0 := by
  rw [finite_koszul_bettiEuler k σ M hr,
    koszulBoundaryRank_eq_zero_of_gt k σ M _ (Nat.lt_succ_self _),
    Nat.choose_eq_zero_of_lt (by omega : Fintype.card σ-1 < Fintype.card σ)]
  simp
end NSP14.Homological
