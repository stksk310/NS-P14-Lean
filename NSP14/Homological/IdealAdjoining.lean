module
public import NSP14.Homological.QuotientBettiAdditivity
public import Mathlib.RingTheory.Ideal.Colon
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
namespace NSP14.Homological
universe u
variable (R : Type u) [CommRing R] (J : Ideal R) (g : R)

noncomputable def idealAdjoinLeft :
    ModuleCat.of R (R ⧸ J.colon {g}) ⟶ ModuleCat.of R (R ⧸ J) :=
  ModuleCat.ofHom ((J.colon {g}).mapQ J (LinearMap.mulLeft R g) (by
    intro x hx
    change g*x ∈ J
    simpa only [smul_eq_mul,mul_comm] using (Submodule.mem_colon_singleton.mp hx)))

noncomputable def idealAdjoinRight :
    ModuleCat.of R (R ⧸ J) ⟶ ModuleCat.of R (R ⧸ (J ⊔ Ideal.span {g})) :=
  ModuleCat.ofHom (J.mapQ (J ⊔ Ideal.span {g}) LinearMap.id (by
    intro x hx
    exact (show J ≤ J ⊔ Ideal.span {g} from le_sup_left) hx))

theorem idealAdjoin_comp : idealAdjoinLeft R J g ≫ idealAdjoinRight R J g=0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  obtain ⟨x,rfl⟩ := Submodule.mkQ_surjective (J.colon {g}) a
  change (Submodule.Quotient.mk (g*x) : R ⧸ (J ⊔ Ideal.span {g}))=0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply (show Ideal.span {g} ≤ J ⊔ Ideal.span {g} from le_sup_right)
  exact Ideal.mul_mem_right x _ (Ideal.subset_span (Set.mem_singleton g))

/-- Adjoining any element gives the actual colon-compensated sequence.
The element need not be regular on either the ring or the quotient. -/
noncomputable def idealAdjoinSequence : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (idealAdjoinLeft R J g) (idealAdjoinRight R J g) (idealAdjoin_comp R J g)

theorem idealAdjoinSequence_shortExact : (idealAdjoinSequence R J g).ShortExact := by
  unfold idealAdjoinSequence
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro a ha
    obtain ⟨x,rfl⟩ := Submodule.mkQ_surjective J a
    change (Submodule.Quotient.mk x : R ⧸ (J ⊔ Ideal.span {g}))=0 at ha
    have hx := (Submodule.Quotient.mk_eq_zero _).mp ha
    obtain ⟨j,hj,b,hb,he⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c,hc⟩ := Ideal.mem_span_singleton'.mp hb
    refine ⟨Submodule.Quotient.mk c,?_⟩
    change (Ideal.Quotient.mk J) (g*c)=(Ideal.Quotient.mk J) x
    rw [←he,←hc,map_add,Ideal.Quotient.eq_zero_iff_mem.mpr hj,zero_add,mul_comm]
  · rw [ModuleCat.mono_iff_injective]
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    intro a ha
    change a=0
    obtain ⟨x,rfl⟩ := Submodule.mkQ_surjective (J.colon {g}) a
    change (Submodule.Quotient.mk (g*x) : R ⧸ J)=0 at ha
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    apply Submodule.mem_colon_singleton.mpr
    change x*g ∈ J
    rw [mul_comm]
    exact (Submodule.Quotient.mk_eq_zero J).mp ha
  · rw [ModuleCat.epi_iff_surjective]
    intro a
    obtain ⟨x,rfl⟩ := Submodule.mkQ_surjective (J ⊔ Ideal.span {g}) a
    exact ⟨Submodule.Quotient.mk x,rfl⟩

noncomputable def idealAdjoinFactor (h : R) (hc : J.colon {g} ≤ J.colon {h}) :
    ModuleCat.of R (R ⧸ J.colon {g}) ⟶ ModuleCat.of R (R ⧸ J) :=
  ModuleCat.ofHom ((J.colon {g}).mapQ J (LinearMap.mulLeft R h) (by
    intro x hx
    change h*x ∈ J
    simpa only [smul_eq_mul,mul_comm] using (Submodule.mem_colon_singleton.mp (hc hx))))

theorem idealAdjoinLeft_factor (a h : R) (he : g=a*h)
    (hc : J.colon {g} ≤ J.colon {h}) :
    idealAdjoinLeft R J g=a • idealAdjoinFactor R J g h hc := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  obtain ⟨x,rfl⟩ := Submodule.mkQ_surjective (J.colon {g}) z
  change (Submodule.Quotient.mk (g*x) : R ⧸ J)=a • Submodule.Quotient.mk (h*x)
  change (Submodule.Quotient.mk (g*x) : R ⧸ J)=Submodule.Quotient.mk (a*(h*x))
  rw [he,mul_assoc]

end NSP14.Homological
