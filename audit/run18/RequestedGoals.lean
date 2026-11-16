module
public import NSP14.Lex.Ideal
public import NSP14.Endpoint.RowPackage
public import NSP14.Target.IntervalAPBetti
@[expose] public section
attribute [local instance] MvPolynomial.gradedAlgebra
open NSP14.Homological
namespace NSP14.Run18.Requested

/-- Frozen arbitrary-characteristic graded comparison, for general homogeneous quotients. -/
def BHP : Prop :=
  ∀ (k : Type) [Field k] (q : ℕ) (I L : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hL : L.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)),
    Lex.IsLex k q L →
    (∀ n, Lex.quotientHilbert k q I hI n=Lex.quotientHilbert k q L hL n) →
    ∀ i : ℕ, 1 ≤ i → ∀ j : ℤ,
      Lex.quotientGradedBetti k q I hI i j≤Lex.quotientGradedBetti k q L hL i j

/-- The quotient's EK formula, with internal-degree shift and an actual minimal generator set. -/
def EK : Prop :=
  ∀ (k : Type) [Field k] (q : ℕ) (L : Ideal (MvPolynomial (Fin q) k))
    (hL : L.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)),
    L≠⊤ → Lex.IsLex k q L →
    ∀ g : Finset (Fin q →₀ ℕ), (∀ v, v∈g ↔ Lex.MinimalGenerator k q L v) →
    ∀ i : ℕ, 1 ≤ i → ∀ j : ℤ,
      Lex.quotientGradedBetti k q L hL i j=
        ∑ v ∈ g, if (v.degree : ℤ)+(i:ℤ)-1=j then
          (Lex.maxVariable q v-1).choose (i-1) else 0

def X_BHP_EK : Prop := BHP ∧ EK

/-- Literal completed source and literal interval target, each with its own minimal variables. -/
def Comparison (S : NumericalSemigroup) (k : Type) [Field k]
    (he : 2≤S.embeddingDimension) : Prop :=
  ∀ i : ℕ, totalBetti k S.AtomExponent
    (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i ≤
    totalBetti k (S.intervalCompletion he).AtomExponent
      (ModuleCat.of ((S.intervalCompletion he).FullPolynomialRing k)
        ((S.intervalCompletion he).FormalTangentAlgebra k)) i

def W_EDGE : Prop := ∀ (S : NumericalSemigroup) (k : Type) [Field k]
    (he : 5≤S.embeddingDimension) (hw : S.width≤S.multiplicity-2),
    let D := S.endpointData (by omega) hw
    D.u=D.q+1 ∨ D.u=D.q+2 → Comparison S k (by omega)

def DenseResources : Prop := ∀ (D : Endpoint.Data) (k : Type) [Field k]
    (t : ℕ), 3≤D.q → D.u=D.q+1+t → t≤D.q →
    D.wordVolume=D.q+1+2*t ∧ D.coreP k≤D.q+1+2*t ∧ D.actualR k≤t ∧
    (t≤2 → D.actualR k=0) ∧ D.coreHeight≤t

def DenseClosure : Prop := ∀ (S : NumericalSemigroup) (k : Type) [Field k]
    (he : 6≤S.embeddingDimension) (hw : S.width≤S.multiplicity-2),
    let D := S.endpointData (by omega) hw
    ∀ t : ℕ, D.u=D.q+1+t → 2≤t → t≤D.q →
      (∀ i : ℕ, 1 ≤ i → totalBetti k S.AtomExponent
        (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i≤
          i*D.u.choose (i+1)) ∧ Comparison S k (by omega)

def W_DENSE : Prop := DenseResources ∧ DenseClosure

def W_SPARSE : Prop := ∀ (S : NumericalSemigroup) (k : Type) [Field k]
    (he : 6≤S.embeddingDimension) (hw : S.width≤S.multiplicity-2),
    let D := S.endpointData (by omega) hw
    2*S.embeddingDimension-2≤D.u → Comparison S k (by omega)

def W_FIVE : Prop := ∀ (S : NumericalSemigroup) (k : Type) [Field k]
    (he : S.embeddingDimension=5) (hw : S.width≤S.multiplicity-2),
    Comparison S k (by omega)

def W_CLOSE : Prop := ∀ (S : NumericalSemigroup) (k : Type) [Field k]
    (he : 5≤S.embeddingDimension) (hw : S.width≤S.multiplicity-2),
    Comparison S k (by omega)
end NSP14.Run18.Requested
