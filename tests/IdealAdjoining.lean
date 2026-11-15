module
public import NSP14.Homological.IdealAdjoining
@[expose] public section
namespace NSP14.Tests.IdealAdjoining
theorem actual_short_exact (R : Type) [CommRing R] (J : Ideal R) (g : R) :
    (Homological.idealAdjoinSequence R J g).ShortExact :=
  Homological.idealAdjoinSequence_shortExact R J g

theorem actual_factored_left (R : Type) [CommRing R] (J : Ideal R) (g a h : R)
    (he : g=a*h) (hc : J.colon {g} ≤ J.colon {h}) :
    Homological.idealAdjoinLeft R J g =
      a • Homological.idealAdjoinFactor R J g h hc :=
  Homological.idealAdjoinLeft_factor R J g a h he hc
end NSP14.Tests.IdealAdjoining
