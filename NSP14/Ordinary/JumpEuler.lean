module
public import NSP14.Ordinary.TowerEuler
public import NSP14.Homological.FiniteKoszulEuler
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open CategoryTheory
open scoped BigOperators Classical
namespace NSP14.NumericalSemigroup.LinearCutData
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)

noncomputable def cutDescending (s : ℕ) : ModuleCat (S.CutPolynomialRing k) :=
  C.restrictFunctor.obj (ModuleCat.of (S.PolynomialRing k) (S.descendingJump k s))

theorem descending_coefficient_finite (s : ℕ) : Module.Finite k (S.descendingJump k s) := by
  let f : S.descendingJump k s →ₗ[k] (S.xMultiply k).ker :=
    { toFun a := a.val
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  exact Module.Finite.of_injective f Subtype.val_injective

theorem cutDescending_finite (s : ℕ) : Module.Finite (S.CutPolynomialRing k) (C.cutDescending s) := by
  have := descending_coefficient_finite (S:=S) (k:=k) s
  exact C.cut_finite (S.descendingJump k s)

noncomputable def descendingEuler (s j : ℕ) : ℤ := by
  let := C.cutDescending_finite s
  exact NSP14.Homological.bettiEuler k (Fin S.actualCutRank) (C.cutDescending s) j

noncomputable def descendingInclusion (s : ℕ) : C.cutDescending (s+1) ⟶ C.cutDescending s :=
  C.restrictFunctor.map (ModuleCat.ofHom
    (Submodule.inclusion (S.descendingJump_antitone k (Nat.le_succ s))))

noncomputable def descendingProjection (s : ℕ) : C.cutDescending s ⟶
    C.restrictFunctor.obj (ModuleCat.of (S.PolynomialRing k) (S.DescendingJumpStratum k s)) :=
  C.restrictFunctor.map (ModuleCat.ofHom (S.nextDescendingJump k s).mkQ)

noncomputable def descendingSequence (s : ℕ) : ShortComplex (ModuleCat (S.CutPolynomialRing k)) :=
  ShortComplex.mk (C.descendingInclusion s) (C.descendingProjection s) (by
    ext a
    change (Submodule.Quotient.mk (⟨a.val,_⟩ : S.descendingJump k s) : S.DescendingJumpStratum k s)=0
    exact (Submodule.Quotient.mk_eq_zero _).mpr a.property)

theorem descendingSequence_shortExact (s : ℕ) : (C.descendingSequence s).ShortExact where
  mono_f := by
    apply (ModuleCat.mono_iff_injective _).mpr
    change Function.Injective (Submodule.inclusion (S.descendingJump_antitone k (Nat.le_succ s)))
    intro a b he
    exact Subtype.ext (congrArg (fun z : S.descendingJump k s => z.val) he)
  epi_g := by
    apply (ModuleCat.epi_iff_surjective _).mpr
    change Function.Surjective (S.nextDescendingJump k s).mkQ
    exact Submodule.mkQ_surjective _
  exact := by
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    intro a
    change (Submodule.Quotient.mk a : S.DescendingJumpStratum k s)=0 ↔
      ∃ b : S.descendingJump k (s+1), (⟨b.val,_⟩ : S.descendingJump k s)=a
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · intro ha
      exact ⟨⟨a.val,ha⟩,Subtype.ext rfl⟩
    · rintro ⟨b,rfl⟩
      exact b.property

/-- One actual filtration step with the connecting-rank subtraction retained
inside bettiEuler_middle_le. The quotient is then transported by the proved
same-jump isomorphism to this same tower's K_s. -/
theorem descendingEuler_step (s : ℕ) (hs : 0 < s) (j : ℕ) :
    C.descendingEuler s j ≤ C.descendingEuler (s+1) j+C.cutKEuler s j := by
  let : Module.Finite (S.CutPolynomialRing k) (C.descendingSequence s).X₁ := C.cutDescending_finite (s+1)
  let : Module.Finite (S.CutPolynomialRing k) (C.descendingSequence s).X₂ := C.cutDescending_finite s
  let : Module.Finite (S.CutPolynomialRing k) (C.descendingSequence s).X₃ := C.descendingStratumCut_finite s hs
  have h := NSP14.Homological.bettiEuler_middle_le k (Fin S.actualCutRank)
    (C.descendingSequence s) (C.descendingSequence_shortExact s) j
  change C.descendingEuler s j ≤ C.descendingEuler (s+1) j+C.descendingStratumEuler s hs j at h
  rwa [C.descendingStratumEuler_eq s hs j] at h

theorem descendingEuler_telescope (n j : ℕ) :
    C.descendingEuler 2 j ≤ C.descendingEuler (2+n) j+
      ∑ t ∈ Finset.range n,C.cutKEuler (2+t) j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := C.descendingEuler_step (2+n) (by omega) j
    rw [Finset.sum_range_succ]
    have he : 2+(n+1)=(2+n)+1 := by omega
    rw [he]
    omega

noncomputable def cutTEuler (j : ℕ) : ℤ := by
  let := C.cutT_finite
  exact NSP14.Homological.bettiEuler k (Fin S.actualCutRank) C.cutT j

noncomputable def cutDescendingTwoIso : C.cutDescending 2 ≅ C.cutT := by
  let e : S.descendingJump k 2 ≃ₗ[S.PolynomialRing k] (S.xMultiply k).ker :=
    { toFun a := a.val
      invFun a := ⟨a,by rw [S.descendingJump_two];trivial⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  exact C.restrictFunctor.mapIso e.toModuleIso

theorem descendingEuler_two (j : ℕ) : C.descendingEuler 2 j=C.cutTEuler j := by
  let := C.cutDescending_finite 2
  let := C.cutT_finite
  have hb := NSP14.Homological.totalBetti_iso k (Fin S.actualCutRank) C.cutDescendingTwoIso
  exact congrArg (fun b : ℕ → ℕ => NSP14.Homological.partialEuler b j) (funext hb)

theorem descendingEuler_eq_zero (s j : ℕ) (hs : S.qTopDegree+1 ≤ s) :
    C.descendingEuler s j=0 := by
  have hb : S.descendingJump k s=⊥ := by
    apply bot_unique
    have h := S.descendingJump_antitone k hs
    rwa [S.descendingJump_top_succ k] at h
  have : Subsingleton (S.descendingJump k s) := by rw [hb];infer_instance
  have : Subsingleton (C.cutDescending s) :=
    inferInstanceAs (Subsingleton (S.descendingJump k s))
  let := C.cutDescending_finite s
  have : Subsingleton (NSP14.Homological.coefficientModule k (Fin S.actualCutRank) (C.cutDescending s)) :=
    inferInstanceAs (Subsingleton (C.cutDescending s))
  have : Module.Finite k (NSP14.Homological.coefficientModule k (Fin S.actualCutRank) (C.cutDescending s)) :=
    inferInstance
  exact NSP14.Homological.bettiEuler_eq_zero_of_subsingleton k (Fin S.actualCutRank) _ j

/-- The actual descending T filtration, exhausted by the proved terminal-jump
bounds, gives the second Tor inequality over the same selected P.
The range parametrizes s=2,...,nu, including the empty nu≤1 case. -/
theorem cutTEuler_le_sum (j : ℕ) :
    C.cutTEuler j ≤ ∑ t ∈ Finset.range (S.qTopDegree-1),C.cutKEuler (2+t) j := by
  have h := C.descendingEuler_telescope (S.qTopDegree-1) j
  rw [C.descendingEuler_two,C.descendingEuler_eq_zero _ j (by omega),zero_add] at h
  exact h
end NSP14.NumericalSemigroup.LinearCutData
