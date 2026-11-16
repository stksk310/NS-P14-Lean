module
public import NSP14.Semigroup.ActualCutRank
public import NSP14.Semigroup.AperyGrading
public import NSP14.Semigroup.WidthNormalization
@[expose] public section
open scoped Classical
namespace NSP14.NumericalSemigroup

/-- The six mutually exclusive regions; index 3 contains the ordinary boundary. -/
def parameterRegion (S : NumericalSemigroup) (j : Fin 6) : Prop :=
  match j.val with
  | 0 => S.embeddingDimension=1
  | 1 => S.embeddingDimension=2
  | 2 => S.embeddingDimension=3
  | 3 => 4 ≤ S.embeddingDimension ∧ S.multiplicity-1 ≤ S.width
  | 4 => S.embeddingDimension=4 ∧ S.width ≤ S.multiplicity-2
  | _ => 5 ≤ S.embeddingDimension ∧ S.width ≤ S.multiplicity-2

def cutRegime (r : ℕ) : Prop := r=2 ∨ r=3 ∨ (4 ≤ r ∧ r ≤ 8) ∨ 9 ≤ r

/-- Actual rank and deficit, including the exceptional rank-two case. -/
def cutParameters (S : NumericalSemigroup) : Prop :=
  2 ≤ S.actualCutRank ∧ S.actualCutRank ≤ S.embeddingDimension-1 ∧
  cutRegime S.actualCutRank ∧ (9 ≤ S.actualCutRank → 10 ≤ S.embeddingDimension) ∧
  (3 ≤ S.actualCutRank → (S.actualCutRank+1).choose 2 ≤ S.deficit) ∧
  (S.deficit=0 → S.actualCutRank=2)

/-- The edge / dense / sparse intervals in the normalized, not physical, width. -/
def narrowRegime (e u : ℕ) : Prop :=
  u=e-1 ∨ u=e ∨ (e+1 ≤ u ∧ u ≤ 2*e-3) ∨ 2*e-2 ≤ u

def narrowParameters (S : NumericalSemigroup) (he : 4 ≤ S.embeddingDimension)
    (hw : S.width ≤ S.multiplicity-2) : Prop :=
  let D := S.endpointData he hw
  D.q+2=S.embeddingDimension ∧ D.q+1 ≤ D.u ∧ 1 ≤ D.d ∧
  D.d*D.u=S.width ∧ D.d*D.u+2 ≤ D.m ∧ D.m=S.multiplicity ∧
  Nat.gcd (D.a.gcd id) D.u=1 ∧ Nat.Coprime D.m D.d ∧
  D.generators=S.atoms ∧ D.source.carrier=S.carrier ∧
  (S.embeddingDimension=4 → 3 ≤ D.u) ∧ (S.embeddingDimension=5 → 4 ≤ D.u) ∧
  (6 ≤ S.embeddingDimension → narrowRegime S.embeddingDimension D.u)
end NSP14.NumericalSemigroup
