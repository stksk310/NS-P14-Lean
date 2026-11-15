module
public import audit.run19.RequestedGoals
public import NSP14.NarrowFour.SmallWidths
@[expose] public section
namespace NSP14.Run19

theorem distance_closed : Requested.N_DISTANCE := by
  intro D k _ hq a b hab
  exact ⟨NarrowFour.distance_volume_four D hq,
    NarrowFour.socle_triangle_card D k hq a b hab,
    NarrowFour.sigma_le_width D k hq a b hab,
    NarrowFour.coreP_card D k a b hab,
    fun p q hp hqp => NarrowFour.standard_downward D a b p q hp hqp,
    fun s t hst => NarrowFour.standard_of_degree_lt_sigma D k hq a b hab s t hst⟩

theorem words_closed : Requested.N_WORDS := by
  intro D k _ hq a b hab
  have hne : a≠b := fun h => (ne_of_lt hab.1) (congrArg (fun x : D.a => x.val) h)
  exact ⟨fun s hp => NarrowFour.standard_pure_bound D a b hne s hp,
    fun t hp => NarrowFour.standard_pure_bound D b a hne.symm t
      ((NarrowFour.standard_swap D a b 0 t).mpr hp),
    fun s t hs ht hp => NarrowFour.standard_mixed_bound D a b hne s t hs ht hp,
    NarrowFour.coreHeight_two_bound D hq a b hab,
    fun hu => NarrowFour.actualR_zero_small D k hq a b hab (by omega)⟩

theorem high_closed : Requested.N_HIGH := by
  intro S k _ he hw i hi
  exact NarrowFour.narrow_four_higher S k he hw i hi

theorem first_closed : Requested.N_FIRST := by
  constructor
  · intro D k _ hq a b hab
    exact NarrowFour.first_count D k hq a b hab
  · intro S k _ he hw hu
    exact NarrowFour.narrow_four_first_large k S he hw hu

theorem small_closed : Requested.N_SMALL := by
  intro S k _ he hw
  dsimp only
  intro hu
  exact NarrowFour.narrow_four_small S k he hw hu
end NSP14.Run19
