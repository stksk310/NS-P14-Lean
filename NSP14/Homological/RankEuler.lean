module

public import NSP14.Homological.FilteredComparison

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators

namespace NSP14.Homological

universe u
variable (k : Type u) [Field k]

/-- Reversed partial alternating sum, in integers so no truncation is hidden. -/
def partialEuler (b : ℕ → ℕ) : ℕ → ℤ
  | 0 => b 0
  | j+1 => (b (j+1) : ℤ)-partialEuler b j

theorem partialEuler_sum (b : ℕ → ℕ) (j : ℕ) :
    partialEuler b j = (-1 : ℤ)^j * ∑ i∈Finset.range (j+1),(-1 : ℤ)^i * b i := by
  induction j with
  | zero => simp [partialEuler]
  | succ j ih =>
    rw [partialEuler,ih]
    have hsum := Finset.sum_range_succ (fun i => (-1 : ℤ)^i * (b i : ℤ)) (j+1)
    rw [hsum,pow_succ]
    have hs : ((-1 : ℤ)^j)^2=1 := by rw [← pow_mul]; simp
    nlinarith [congrArg (fun z : ℤ => z*(b (j+1) : ℤ)) hs]

/-- An actual exact chain complex of finite vector spaces has the expected syzygy rank Euler. -/
theorem partialEuler_syzygy (K : ChainComplex (ModuleCat.{u} k) ℕ)
    [∀ i,Module.Finite k (K.X i)] (hK : ∀ i,K.ExactAt i) (j : ℕ) :
    partialEuler (fun i => Module.finrank k (K.X i)) j =
      (Module.finrank k (K.d (j+1) j).hom.range : ℤ) := by
  induction j with
  | zero =>
    have hs := (K.exactAt_iff' 1 0 0 (by simp) (by simp)).mp (hK 0)
    have he := (ShortComplex.moduleCat_exact_iff_range_eq_ker (K.sc' 1 0 0)).mp hs
    change (K.d 1 0).hom.range=(K.d 0 0).hom.ker at he
    rw [K.shape 0 0 (by simp [ComplexShape.down])] at he
    change (K.d 1 0).hom.range=(0 : K.X 0 →ₗ[k] K.X 0).ker at he
    rw [LinearMap.ker_zero] at he
    dsimp only [partialEuler]
    rw [he,finrank_top]
  | succ j ih =>
    have hs := (K.exactAt_iff' (j+2) (j+1) j (by simp) (by simp)).mp (hK (j+1))
    have he := exact_rank_sum k (ShortComplex.mk (K.d (j+2) (j+1)) (K.d (j+1) j)
      (K.d_comp_d (j+2) (j+1) j)) hs
    change Module.finrank k (K.d (j+2) (j+1)).hom.range +
      Module.finrank k (K.d (j+1) j).hom.range = Module.finrank k (K.X (j+1)) at he
    rw [partialEuler,ih]
    change (Module.finrank k (K.X (j+1)) : ℤ) - (Module.finrank k (K.d (j+1) j).hom.range : ℤ) =
      (Module.finrank k (K.d (j+2) (j+1)).hom.range : ℤ)
    omega

theorem partialEuler_nonnegative (K : ChainComplex (ModuleCat.{u} k) ℕ)
    [∀ i,Module.Finite k (K.X i)] (hK : ∀ i,K.ExactAt i) (j : ℕ) :
    0 ≤ partialEuler (fun i => Module.finrank k (K.X i)) j := by
  rw [partialEuler_syzygy k K hK j]
  exact_mod_cast Nat.zero_le _

theorem partialEuler_terminal (K : ChainComplex (ModuleCat.{u} k) ℕ)
    [∀ i,Module.Finite k (K.X i)] (hK : ∀ i,K.ExactAt i) (n : ℕ)
    (htop : IsZero (K.X (n+1))) : partialEuler (fun i => Module.finrank k (K.X i)) n=0 := by
  rw [partialEuler_syzygy k K hK n]
  have hz : K.d (n+1) n=0 := htop.eq_of_src _ _
  simp [hz]

end NSP14.Homological
