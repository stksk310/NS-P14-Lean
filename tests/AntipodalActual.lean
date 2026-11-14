module
public import NSP14.Width.AntipodalIdeal
public import NSP14.Width.AntipodalVolume
public import tests.WidthFiveHigher
@[expose] public section
open NSP14.Homological
namespace NSP14.Tests.Antipodal
variable (D : Endpoint.Data) (k : Type) [Field k]
/-- Actual QC and original distances, with coprimality only modulo h. -/
theorem actual_resources (h t : ℕ) (hu : D.u=2*h) (hh : 4 ≤ h)
    (ht : 0<t) (hth : t<h) (hc : Nat.Coprime t h) (ha : D.a={t,h,t+h}) :
    D.coreP k=(h+1).choose 2+1 ∧ D.wordVolume=h^2-h+2 :=
  ⟨D.antipodal_coreP k h t hu hh ht hth hc ha,
    D.antipodal_wordVolume h t hu hh hc ha⟩

theorem actual_Tor_transport (h t : ℕ) (hu : D.u=2*h) (hh : 4 ≤ h)
    (ht : 0<t) (hth : t<h) (hc : Nat.Coprime t h) (ha : D.a={t,h,t+h}) (i : ℕ) :
    totalBetti k D.a (D.QCoreModule k) i=
      totalBetti k D.a (Endpoint.artinModule k D.a (D.antipodalPresentationIdeal k h t ha)) i :=
  D.antipodal_actual_betti k h t ha hu hh ht hth hc i

/-- t=2 is a nonunit modulo u=10, so no gcd(t,u)=1 assumption is hidden. -/
theorem nonunit : ¬Nat.Coprime 2 FiveHigher.antipodal_nonunit.u := by decide

theorem nonunit_resources (k : Type) [Field k] :
    FiveHigher.antipodal_nonunit.coreP k=16 ∧ FiveHigher.antipodal_nonunit.wordVolume=22 := by
  simpa [Nat.choose] using actual_resources FiveHigher.antipodal_nonunit k 5 2 rfl (by decide)
    (by decide) (by decide) (by decide) rfl

theorem nonunit_Q : FiveHigher.antipodal_nonunit.coreP ℚ=16 := (nonunit_resources ℚ).1
theorem nonunit_char2 : FiveHigher.antipodal_nonunit.coreP (ZMod 2)=16 := (nonunit_resources (ZMod 2)).1
theorem nonunit_char3 : FiveHigher.antipodal_nonunit.coreP (ZMod 3)=16 := (nonunit_resources (ZMod 3)).1
end NSP14.Tests.Antipodal
