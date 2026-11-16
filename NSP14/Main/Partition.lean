module
public import NSP14.Semigroup.ActualCutRank
public import NSP14.Semigroup.AperyGrading
public import NSP14.Semigroup.WidthNormalization
public import NSP14.Endpoint.OffsetOrder
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

namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup)

theorem parameter_partition : ∃! j : Fin 6, S.parameterRegion j := by
  have he := S.embeddingDimension_pos
  have hm := S.embeddingDimension_le_multiplicity
  have hex : ∃ j : Fin 6, S.parameterRegion j := by
    by_cases h1 : S.embeddingDimension=1
    · exact ⟨0,h1⟩
    by_cases h2 : S.embeddingDimension=2
    · exact ⟨1,h2⟩
    by_cases h3 : S.embeddingDimension=3
    · exact ⟨2,h3⟩
    by_cases hw : S.multiplicity-1 ≤ S.width
    · exact ⟨3,by constructor <;> omega⟩
    by_cases h4 : S.embeddingDimension=4
    · exact ⟨4,by constructor <;> omega⟩
    · exact ⟨5,by constructor <;> omega⟩
  obtain ⟨j,hj⟩ := hex
  refine ⟨j,hj,?_⟩
  intro j' hj'
  fin_cases j <;> fin_cases j' <;> simp only [parameterRegion] at hj hj' <;>
    first | rfl | omega

theorem cut_parameters (he : 4 ≤ S.embeddingDimension) : S.cutParameters := by
  have hlo := S.actualCutRank_two_le
  have hhi := S.actualCutRank_le (by omega)
  have htri : 3 ≤ S.actualCutRank → (S.actualCutRank+1).choose 2 ≤ S.deficit :=
    fun hr => (S.actualCutRank_triangular hr).trans S.degree_two_le_deficit
  refine ⟨hlo,hhi,by unfold cutRegime;omega,by omega,htri,?_⟩
  intro hz
  by_contra hr
  have h3 : 3 ≤ S.actualCutRank := by omega
  have hp : 0 < (S.actualCutRank+1).choose 2 := Nat.choose_pos (by omega)
  have ht := htri h3
  omega

theorem narrow_parameters (he : 4 ≤ S.embeddingDimension) (hw : S.width ≤ S.multiplicity-2) :
    S.narrowParameters he hw := by
  let D := S.endpointData he hw
  have hq : D.q+2=S.embeddingDimension := S.endpointData_embedding he hw
  have hu := D.q_add_one_le_u
  have hwid : D.d*D.u=S.width := by
    change S.offsetGcd*S.normalizedWidth=S.width
    rw [Nat.mul_comm,S.width_factor]
  refine ⟨hq,hu,D.d_pos,hwid,S.endpointData_narrow he hw,rfl,
    D.offsets_coprime,D.coprime,S.endpointData_generators he hw,S.endpointData_carrier he hw,
    ?_,?_,?_⟩
  · change S.embeddingDimension=4 → 3 ≤ D.u
    omega
  · change S.embeddingDimension=5 → 4 ≤ D.u
    omega
  · change 6 ≤ S.embeddingDimension → narrowRegime S.embeddingDimension D.u
    intro he6
    unfold narrowRegime
    omega
end NSP14.NumericalSemigroup
