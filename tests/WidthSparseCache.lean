module
public import tests.WidthSparseData
public import NSP14.Endpoint.FiniteSocleWindow
public import Mathlib.Tactic.IntervalCases
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 0
open NSP14
namespace Run18SparseAcceptance

theorem six_m : six.m=12 := rfl
theorem six_d : six.d=1 := rfl
theorem six_u : six.u=10 := rfl

/-- The concrete four-fold sum is already an interval, and it stays an interval. -/
theorem six_offset_full (n : ℕ) (hn : 4≤n) : six.offsetSums n=Finset.range (10*n+1) := by
  induction n,hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [Endpoint.Data.offsetSums,ih]
    ext B
    simp only [Finset.mem_biUnion,Finset.mem_image,Finset.mem_range]
    constructor
    · rintro ⟨b,hb,C,hC,rfl⟩
      have hb' : b≤10 := six.offset_le hb
      omega
    · intro hB
      by_cases h : B<10*n+1
      · exact ⟨0,by decide,B,h,by omega⟩
      · exact ⟨10,by decide,B-10,by omega,by omega⟩

/-- Test-only evaluation table. Its equality to the actual offset sums is proved below. -/
def cachedOffsets (n : ℕ) : Finset ℕ :=
  if n=0 then {0} else if n=1 then {0,1,2,8,9,10} else
  if n=2 then Finset.range 5 ∪ Finset.Icc 8 12 ∪ Finset.Icc 16 20 else
  if n=3 then Finset.range 7 ∪ Finset.Icc 8 14 ∪ Finset.Icc 16 22 ∪ Finset.Icc 24 30 else
    Finset.range (10*n+1)

theorem six_offsets_cached (n : ℕ) : six.offsetSums n=cachedOffsets n := by
  by_cases hn : n<4
  · interval_cases n <;> decide
  · simp only [cachedOffsets,ite_eq_right (show n≠0 by omega),ite_eq_right (show n≠1 by omega),
      ite_eq_right (show n≠2 by omega),ite_eq_right (show n≠3 by omega)]
    exact six_offset_full n (by omega)

def cachedCoordinate (r : Fin six.u) (c : ℕ×ℕ) : Prop :=
  r.val+10*c.2∈cachedOffsets (c.1+c.2+six.epsilon r)
instance cachedCoordinateDecidable (r : Fin six.u) (c : ℕ×ℕ) : Decidable (cachedCoordinate r c) :=
  inferInstanceAs (Decidable (_∈_))

def cachedMinima (r : Fin six.u) : Finset (ℕ×ℕ) :=
  ((Finset.range 10).product (Finset.range 10)).filter (fun c =>
    cachedCoordinate r c ∧ (c.1=0 ∨ ¬cachedCoordinate r (c.1-1,c.2)) ∧
      (c.2=0 ∨ ¬cachedCoordinate r (c.1,c.2-1)))

theorem six_minima_cached (r : Fin six.u) : six.computedMinima r=cachedMinima r := by
  unfold Endpoint.Data.computedMinima cachedMinima
  apply Finset.filter_congr
  intro c _
  simp only [Endpoint.Data.coreCoordinateTest,cachedCoordinate,six_offsets_cached,six_u]

def cachedOrder (x : ℕ) : ℕ := ((Finset.range (x/12+1)).filter
    (fun n => ∃ B∈cachedOffsets n,n*12+B=x)).sup id

theorem six_order_cached (x : ℕ) : six.computedOrder x=cachedOrder x := by
  unfold Endpoint.Data.computedOrder Endpoint.Data.lengthCandidates cachedOrder
  simp only [six_offsets_cached,six_m,six_d,mul_one]

def cachedSurvivors (r : Fin six.u) : Finset (ℕ×ℕ) := (cachedMinima r).filter (fun c =>
  c.1+c.2+six.epsilon r=cachedOrder ((c.1+c.2+six.epsilon r)*12+(r.val+10*c.2)))

theorem six_survivors_cached (r : Fin six.u) : six.computedSurvivors r=cachedSurvivors r := by
  unfold Endpoint.Data.computedSurvivors cachedSurvivors
  rw [six_minima_cached]
  apply Finset.filter_congr
  intro c _
  rw [six_order_cached]
  simp only [six_m,six_u,six_d,mul_one]

def cachedHeight : ℕ := Finset.univ.sup (fun r : Fin six.u => (cachedMinima r).sup Prod.fst)

theorem six_height_cached : six.computedCoreHeight=cachedHeight := by
  unfold Endpoint.Data.computedCoreHeight cachedHeight
  simp only [six_minima_cached]

def cachedSocleTest (r : Fin six.u) (c : ℕ×ℕ) : Prop :=
  let v := (c.1+c.2+six.epsilon r)*12+(r.val+10*c.2)
  c.1+c.2+six.epsilon r=cachedOrder v ∧
    c.1+c.2+six.epsilon r+1<cachedOrder (v+12) ∧
    c.1+c.2+six.epsilon r+1<cachedOrder (v+22)
instance cachedSocleTestDecidable (r : Fin six.u) (c : ℕ×ℕ) : Decidable (cachedSocleTest r c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def cachedWindow (K : ℕ) (r : Fin six.u) : Finset (ℕ×ℕ) :=
  ((Finset.range (cachedHeight-2)).product (Finset.range K)).filter
    (fun c => cachedCoordinate r c ∧ cachedSocleTest r c)

theorem six_window_cached (K : ℕ) (r : Fin six.u) :
    six.computedSocleWindow K r=cachedWindow K r := by
  unfold Endpoint.Data.computedSocleWindow cachedWindow
  rw [six_height_cached]
  apply Finset.filter_congr
  intro c _
  simp only [Endpoint.Data.coreCoordinateTest,six_offsets_cached,cachedCoordinate,
    Endpoint.Data.coordinateSocleTest,six_order_cached,Endpoint.Data.coordinateValue,cachedSocleTest,
    six_m,six_u,six_d,mul_one,add_assoc,show (12:ℕ)+10=22 from rfl]
end Run18SparseAcceptance
