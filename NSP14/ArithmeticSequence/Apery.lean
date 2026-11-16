module
public import NSP14.ArithmeticSequence.Order
public import NSP14.Semigroup.Apery
public import Mathlib.Algebra.Order.Floor.Div
@[expose] public section
open scoped Classical
namespace NSP14.ArithmeticSequence.Data
variable (D : NSP14.ArithmeticSequence.Data)

/-- Number of AP blocks needed for the canonical index, independently of d. -/
def blockCount (i : ℕ) : ℕ := i ⌈/⌉ D.v

theorem blockCount_le_iff (i n : ℕ) : D.blockCount i ≤ n ↔ i ≤ D.v*n :=
  ceilDiv_le_iff_le_mul (by have := D.v_pos;omega)

theorem index_le_blocks (i : ℕ) : i ≤ D.v*D.blockCount i :=
  (D.blockCount_le_iff i _).mp le_rfl

def aperyValue (i : ℕ) : ℕ := D.blockCount i*D.m+i*D.d

theorem aperyValue_mem_source (i : ℕ) : D.aperyValue i ∈ D.source :=
  ⟨D.blockCount i,i,D.index_le_blocks i,rfl⟩

theorem aperyValue_order (i : ℕ) (hi : i < D.m) :
    D.source.order (D.aperyValue i)=D.blockCount i :=
  D.canonical_order _ _ hi (D.index_le_blocks i)

theorem aperyValue_min (i : ℕ) (hi : i < D.m) :
    NSP14.IsAperyMin D.source.carrier D.source.multiplicity (D.aperyValue i) := by
  refine ⟨D.aperyValue_mem_source i,?_⟩
  intro y hy hm
  rw [D.multiplicity] at hm
  obtain ⟨n,j,hj,hjn,he⟩ := D.canonical_representation hy
  have hmod : j*D.d ≡ i*D.d [MOD D.m] := by
    change (j*D.d)%D.m=(i*D.d)%D.m
    simpa only [he,aperyValue,Nat.add_mod,Nat.mul_mod_left,Nat.zero_add,Nat.mod_mod] using hm
  have hc := hmod.cancel_right_of_coprime D.coprime.gcd_eq_one
  change j%D.m=i%D.m at hc
  have hji : j=i := by simpa only [Nat.mod_eq_of_lt hj,Nat.mod_eq_of_lt hi] using hc
  subst j
  have hb := (D.blockCount_le_iff i n).mpr hjn
  unfold aperyValue
  rw [he]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right D.m hb) _

theorem aperyValue_mem {i : ℕ} (hi : i < D.m) : D.aperyValue i ∈ D.source.aperySet :=
  (D.source.mem_aperySet_iff _).mpr (D.aperyValue_min i hi)

/-- Every actual Apéry element occurs in the canonical list, including zero. -/
theorem mem_apery_iff (x : ℕ) :
    x ∈ D.source.aperySet ↔ ∃ i, i < D.m ∧ x=D.aperyValue i := by
  constructor
  · intro hx
    obtain ⟨n,i,hi,hni,he⟩ := D.canonical_representation
      ((D.source.mem_aperySet_iff _).mp hx).1
    have hm : x%D.source.multiplicity=D.aperyValue i%D.source.multiplicity := by
      rw [D.multiplicity,he]
      simp only [aperyValue,Nat.add_mod,Nat.mul_mod_left,Nat.zero_add]
    exact ⟨i,hi,NSP14.apery_min_unique ((D.source.mem_aperySet_iff _).mp hx)
      (D.aperyValue_min i hi) hm⟩
  · rintro ⟨i,hi,rfl⟩
    exact D.aperyValue_mem hi
end NSP14.ArithmeticSequence.Data
