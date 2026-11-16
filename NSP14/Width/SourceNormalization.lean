module
public import NSP14.Endpoint.Normalization
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

theorem source_atomOffsets : D.source.atomOffsets=D.offsets.image (fun b => b*D.d) := by
  rw [NSP14.NumericalSemigroup.atomOffsets,D.atoms,generators,D.multiplicity,Finset.image_image]
  congr 1
  funext b
  change D.m+b*D.d-D.m=b*D.d
  omega

theorem offsets_gcd : D.offsets.gcd id=1 := by
  simp only [offsets,Finset.gcd_insert,id_eq,gcd_eq_nat_gcd,Nat.gcd_zero_left]
  exact (Nat.gcd_comm D.u (D.a.gcd id)).trans D.offsets_coprime

theorem source_offsetGcd : D.source.offsetGcd=D.d := by
  rw [NSP14.NumericalSemigroup.offsetGcd,D.source_atomOffsets,Finset.gcd_image]
  change (D.offsets.gcd (fun b => b*D.d))=D.d
  rw [Finset.gcd_mul_right]
  change (D.offsets.gcd id)*normalize D.d=D.d
  rw [D.offsets_gcd]
  simp only [normalize_eq,one_mul]

theorem source_normalizedWidth : D.source.normalizedWidth=D.u := by
  rw [NSP14.NumericalSemigroup.normalizedWidth,D.width,D.source_offsetGcd,Nat.mul_comm]
  exact Nat.mul_div_cancel _ (Nat.zero_lt_of_lt D.d_pos)
end NSP14.Endpoint.Data
