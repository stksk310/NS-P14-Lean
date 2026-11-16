module
public import NSP14.Width.FiveNonAntipodal
public import tests.WidthFiveHigher
@[expose] public section
set_option synthInstance.maxHeartbeats 200000
open NSP14.Homological
namespace NSP14.Tests.FiveNonAntipodal
theorem actual_all_rows (S : NumericalSemigroup) (k : Type) [Field k]
    (he : S.embeddingDimension=5) (hw : S.width ≤ S.multiplicity-2)
    (hu : 8 ≤ S.normalizedWidth)
    (ha : ¬NSP14.Additive.CyclicAntipodal (S.endpointData (by omega) hw).u
      (S.endpointData (by omega) hw).residueAlphabet) (i : ℕ) :
    totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i ≤ 
    totalBetti k (S.intervalCompletion (by omega)).AtomExponent
      (ModuleCat.of ((S.intervalCompletion (by omega)).FullPolynomialRing k)
        ((S.intervalCompletion (by omega)).FormalTangentAlgebra k)) i :=
  S.narrow_five_nonAntipodal_comparison k he hw hu ha i


theorem eight_not_antipodal : ¬NSP14.Additive.CyclicAntipodal NSP14.Tests.FiveHigher.eight.u NSP14.Tests.FiveHigher.eight.residueAlphabet := by
  rintro ⟨h,t,hu,ht0,hth,_,hA⟩
  have hh : h=4 := by change 8=2*h at hu; omega
  subst h
  interval_cases t <;> exact (by decide : NSP14.Tests.FiveHigher.eight.residueAlphabet≠_) hA
theorem eight_first_Q :
    totalBetti (ℚ) NSP14.Tests.FiveHigher.eight.Variables (NSP14.Tests.FiveHigher.eight.fullG (ℚ)) 1 ≤ NSP14.Tests.FiveHigher.eight.u.choose 2+1 :=
  NSP14.Tests.FiveHigher.eight.actual_five_nonAntipodal_first (ℚ) rfl (by decide) eight_not_antipodal
theorem eight_first_char2 :
    totalBetti (ZMod 2) NSP14.Tests.FiveHigher.eight.Variables (NSP14.Tests.FiveHigher.eight.fullG (ZMod 2)) 1 ≤ NSP14.Tests.FiveHigher.eight.u.choose 2+1 :=
  NSP14.Tests.FiveHigher.eight.actual_five_nonAntipodal_first (ZMod 2) rfl (by decide) eight_not_antipodal
theorem eight_first_char3 :
    totalBetti (ZMod 3) NSP14.Tests.FiveHigher.eight.Variables (NSP14.Tests.FiveHigher.eight.fullG (ZMod 3)) 1 ≤ NSP14.Tests.FiveHigher.eight.u.choose 2+1 :=
  NSP14.Tests.FiveHigher.eight.actual_five_nonAntipodal_first (ZMod 3) rfl (by decide) eight_not_antipodal

theorem nine_not_antipodal : ¬NSP14.Additive.CyclicAntipodal NSP14.Tests.FiveHigher.nine.u NSP14.Tests.FiveHigher.nine.residueAlphabet := by
  rintro ⟨h,t,hu,ht0,hth,_,hA⟩
  have hh : h=4 := by change 9=2*h at hu; omega
  change 9=2*h at hu
  omega
theorem nine_first_Q :
    totalBetti (ℚ) NSP14.Tests.FiveHigher.nine.Variables (NSP14.Tests.FiveHigher.nine.fullG (ℚ)) 1 ≤ NSP14.Tests.FiveHigher.nine.u.choose 2+1 :=
  NSP14.Tests.FiveHigher.nine.actual_five_nonAntipodal_first (ℚ) rfl (by decide) nine_not_antipodal
theorem nine_first_char2 :
    totalBetti (ZMod 2) NSP14.Tests.FiveHigher.nine.Variables (NSP14.Tests.FiveHigher.nine.fullG (ZMod 2)) 1 ≤ NSP14.Tests.FiveHigher.nine.u.choose 2+1 :=
  NSP14.Tests.FiveHigher.nine.actual_five_nonAntipodal_first (ZMod 2) rfl (by decide) nine_not_antipodal
theorem nine_first_char3 :
    totalBetti (ZMod 3) NSP14.Tests.FiveHigher.nine.Variables (NSP14.Tests.FiveHigher.nine.fullG (ZMod 3)) 1 ≤ NSP14.Tests.FiveHigher.nine.u.choose 2+1 :=
  NSP14.Tests.FiveHigher.nine.actual_five_nonAntipodal_first (ZMod 3) rfl (by decide) nine_not_antipodal

theorem ten_not_antipodal : ¬NSP14.Additive.CyclicAntipodal NSP14.Tests.FiveHigher.ten.u NSP14.Tests.FiveHigher.ten.residueAlphabet := by
  rintro ⟨h,t,hu,ht0,hth,_,hA⟩
  have hh : h=5 := by change 10=2*h at hu; omega
  subst h
  interval_cases t <;> exact (by decide : NSP14.Tests.FiveHigher.ten.residueAlphabet≠_) hA
theorem ten_first_Q :
    totalBetti (ℚ) NSP14.Tests.FiveHigher.ten.Variables (NSP14.Tests.FiveHigher.ten.fullG (ℚ)) 1 ≤ NSP14.Tests.FiveHigher.ten.u.choose 2+1 :=
  NSP14.Tests.FiveHigher.ten.actual_five_nonAntipodal_first (ℚ) rfl (by decide) ten_not_antipodal
theorem ten_first_char2 :
    totalBetti (ZMod 2) NSP14.Tests.FiveHigher.ten.Variables (NSP14.Tests.FiveHigher.ten.fullG (ZMod 2)) 1 ≤ NSP14.Tests.FiveHigher.ten.u.choose 2+1 :=
  NSP14.Tests.FiveHigher.ten.actual_five_nonAntipodal_first (ZMod 2) rfl (by decide) ten_not_antipodal
theorem ten_first_char3 :
    totalBetti (ZMod 3) NSP14.Tests.FiveHigher.ten.Variables (NSP14.Tests.FiveHigher.ten.fullG (ZMod 3)) 1 ≤ NSP14.Tests.FiveHigher.ten.u.choose 2+1 :=
  NSP14.Tests.FiveHigher.ten.actual_five_nonAntipodal_first (ZMod 3) rfl (by decide) ten_not_antipodal
end NSP14.Tests.FiveNonAntipodal
