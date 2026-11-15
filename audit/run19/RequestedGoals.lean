module
public import audit.run18.RequestedGoals
public import NSP14.NarrowFour.CoreWords
public import NSP14.Semigroup.IntervalCompletionAll
@[expose] public section
open scoped Classical
open NSP14.Homological
namespace NSP14.Run19.Requested

/-- Same actual completed source and each target's own minimal variables. -/
def Row (S : NumericalSemigroup) (k : Type) [Field k]
    (he : 2 ≤ S.embeddingDimension) (i : ℕ) : Prop :=
  totalBetti k S.AtomExponent
    (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i ≤
  totalBetti k (S.intervalCompletion he).AtomExponent
    (ModuleCat.of ((S.intervalCompletion he).FullPolynomialRing k)
      ((S.intervalCompletion he).FormalTangentAlgebra k)) i

def ComparisonAll (S : NumericalSemigroup) (k : Type) [Field k] : Prop :=
  ∀ i : ℕ, totalBetti k S.AtomExponent
    (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i ≤
  totalBetti k S.intervalCompletionAll.AtomExponent
    (ModuleCat.of (S.intervalCompletionAll.FullPolynomialRing k)
      (S.intervalCompletionAll.FormalTangentAlgebra k)) i

/-- V06 N2: actual standard-word downset, distance resource and full socle triangle. -/
def N_DISTANCE : Prop := ∀ (D : Endpoint.Data) (k : Type) [Field k]
    (hq : D.q=2) (a b : D.a), NarrowFour.OrderedPair D a b →
  4*(D.wordVolume-1) ≤ D.u^2 ∧
  (D.internalSigma k hq+1).choose 2 ≤ D.coreP k ∧
  D.internalSigma k hq ≤ D.u-1 ∧
  D.coreP k=(NarrowFour.standardWords D a b).card ∧
  (∀ p q : ℕ×ℕ, NarrowFour.Standard D a b p → q≤p → NarrowFour.Standard D a b q) ∧
  (∀ s t : ℕ, s+t≤D.internalSigma k hq-1 → NarrowFour.Standard D a b (s,t))

/-- V06 N3: pure and mixed lengths, original height and original actual R. -/
def N_WORDS : Prop := ∀ (D : Endpoint.Data) (k : Type) [Field k]
    (_hq : D.q=2) (a b : D.a), NarrowFour.OrderedPair D a b →
  (∀ s, NarrowFour.Standard D a b (s,0) → s≤D.u-2) ∧
  (∀ t, NarrowFour.Standard D a b (0,t) → t≤D.u-2) ∧
  (∀ s t, 0<s → 0<t → NarrowFour.Standard D a b (s,t) → 2*(s+t)≤D.u) ∧
  D.coreHeight≤D.u-3 ∧ (D.u≤4 → D.actualR k=0)

def N_HIGH : Prop := ∀ (S : NumericalSemigroup) (k : Type) [Field k]
    (he : S.embeddingDimension=4) (hw : S.width≤S.multiplicity-2)
    (i : ℕ), 2 ≤ i → Row S k (by omega) i

/-- V06 N5b/c resource counts, including the guard on the removed triangle. -/
def FirstCount : Prop := ∀ (D : Endpoint.Data) (k : Type) [Field k]
    (hq : D.q=2) (a b : D.a), NarrowFour.OrderedPair D a b →
  let h := D.u/2
  let k₀ := D.u-b.val+a.val
  let E := if k₀≤h then (h-k₀+2).choose 2 else 0
  D.coreP k≤2*D.u-k₀-1+h.choose 2-E ∧
  D.coreP k≤2*D.u-h-2+h.choose 2 ∧ D.internalSigma k hq≤min (h+1) k₀

def N_FIRST : Prop := FirstCount ∧
  ∀ (S : NumericalSemigroup) (k : Type) [Field k]
    (he : S.embeddingDimension=4) (hw : S.width≤S.multiplicity-2),
    S.normalizedWidth=5 ∨ 9≤S.normalizedWidth → Row S k (by omega) 1

def N_SMALL : Prop := ∀ (S : NumericalSemigroup) (k : Type) [Field k]
    (he : S.embeddingDimension=4) (hw : S.width≤S.multiplicity-2),
  let D := S.endpointData (by omega) hw
  (D.u=3 ∨ D.u=5 ∨ D.u=6 ∨ D.u=7 ∨ D.u=8 ∨
    (D.u=4 ∧ (D.d≠1 ∨ D.a≠{1,3}))) → Run18.Requested.Comparison S k (by omega)

def N_WIDTH4 : Prop := ∀ (D : Endpoint.Data) (k : Type) [Field k]
    (hq : D.q=2), D.d*D.u+2≤D.m → D.d=1 → D.u=4 → D.a={1,3} →
    Run18.Requested.Comparison D.source k (by rw [D.embeddingDimension]; omega)

def N_CLOSE : Prop := ∀ (S : NumericalSemigroup) (k : Type) [Field k]
    (he : S.embeddingDimension=4), S.width≤S.multiplicity-2 →
    Run18.Requested.Comparison S k (by omega)

/-- Includes the literal width-zero target, not an undefined interval API. -/
def I_BASE : Prop := ∀ (S : NumericalSemigroup) (k : Type) [Field k],
  S.embeddingDimension≤2 → ComparisonAll S k

/-- Necessary LTV comparison contract, shifted from ideals to quotient positive rows.
The stronger three numerical estimates in the paper are not claimed by this contract. -/
def X_LTV : Prop := ∀ (S : NumericalSemigroup) (k : Type) [Field k]
    (he : S.embeddingDimension=3) (i : ℕ), Row S k (by omega) (i+1)

def I_THREE : Prop := ∀ (S : NumericalSemigroup) (k : Type) [Field k]
    (he : S.embeddingDimension=3), Run18.Requested.Comparison S k (by omega)

end NSP14.Run19.Requested
