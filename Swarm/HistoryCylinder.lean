/-
Adaptive finite histories of coordinate/value observations, and the exact
conditional product law for fresh coordinates.
-/
import Swarm.UniformArray
import Swarm.FreshIndependence
import Swarm.Trajectory

namespace Swarming.History

open MeasureTheory Set
open Swarming.Uniform

variable {N : ℕ}

/-- One observed coordinate and its value. -/
abbrev Record (N : ℕ) := (Fin N × ℤ × ℕ) × ℝ

/-- The finite set of coordinates appearing in a record. -/
noncomputable def used {N : ℕ} (hs : List (Record N)) : Finset (Fin N × ℤ × ℕ) :=
  hs.map Prod.fst |>.toFinset

lemma mem_used {hs : List (Record N)} {r : Record N}
    (hr : r ∈ hs) : r.1 ∈ used hs := by
  unfold used
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  exact ⟨r, hr, rfl⟩

/-- A history prescribes the value of each of its finitely many coordinates. -/
def historyEvent {N : ℕ} (hs : List (Record N)) : Set (Array N) :=
  {ω | ∀ r ∈ hs, ω r.1 = r.2}

/-- The same history viewed as a constraint on the coordinates used by the record. -/
noncomputable def compatible {N : ℕ} (hs : List (Record N)) :
    Set (used hs → ℝ) :=
  {g | ∀ r (hr : r ∈ hs), g ⟨r.1, mem_used hr⟩ = r.2}

lemma compatible_measurable {N : ℕ} (hs : List (Record N)) :
    MeasurableSet (compatible hs) := by
  rw [compatible]
  have heq : {g : used hs → ℝ | ∀ r (hr : r ∈ hs), g ⟨r.1, mem_used hr⟩ = r.2} =
      ⋂ r : {r // r ∈ hs.toFinset}, {g : used hs → ℝ |
        g ⟨r.1.1, by exact mem_used (List.mem_toFinset.mp r.2)⟩ = r.1.2} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro h r
      exact h r.1 (List.mem_toFinset.mp r.2)
    · intro h r hr
      exact h ⟨r, List.mem_toFinset.mpr hr⟩
  rw [heq]
  exact MeasurableSet.iInter fun r => (measurableSet_singleton r.1.2).preimage
    (measurable_pi_apply (⟨r.1.1, mem_used (List.mem_toFinset.mp r.2)⟩ : used hs))

lemma preimage_compatible {N : ℕ} (hs : List (Record N)) :
    (fun ω (j : used hs) => ω j) ⁻¹' compatible hs = historyEvent hs := by
  ext ω
  simp only [Set.mem_preimage, compatible, historyEvent, Set.mem_ofPred_eq]

/-- Product formula for a fixed exact coordinate/value history and fresh coordinates.
This identity may have both sides zero; conditional laws for the revealed
sigma-algebra are proved separately in `Swarm.EnlLaw`. -/
theorem measure_history_and_fresh {N : ℕ} (hs : List (Record N))
    {c : Fin N → Fin N × ℤ × ℕ} (hc : Function.Injective c)
    (hfresh : ∀ i, c i ∉ used hs) {u : Fin N → ℝ}
    (_hu0 : ∀ i, 0 ≤ u i) (hu1 : ∀ i, u i ≤ 1) :
    arrayMeasure N (historyEvent hs ∩ ⋂ i, (fun ω : Array N => ω (c i)) ⁻¹' Iio (u i)) =
      arrayMeasure N (historyEvent hs) * ∏ i, ENNReal.ofReal (u i) := by
  have hm := SwarmIID.indep_fresh_finset (array_independent N) (fun c => measurable_pi_apply c)
    hc hfresh (compatible hs) (compatible_measurable hs) (fun i => Iio (u i))
    (fun i => measurableSet_Iio)
  rw [preimage_compatible] at hm
  calc
    arrayMeasure N (historyEvent hs ∩ ⋂ i, (fun ω : Array N => ω (c i)) ⁻¹' Iio (u i)) =
        arrayMeasure N (historyEvent hs) *
          ∏ i, arrayMeasure N ((fun ω : Array N => ω (c i)) ⁻¹' Iio (u i)) := hm
    _ = arrayMeasure N (historyEvent hs) * ∏ i, ENNReal.ofReal (u i) := by
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      exact arrayMeasure_preimage_Iio N (c i) (hu1 i)

/-- All coordinates consumed by the recursive trajectory strictly before time `n`,
with their observed values. -/
noncomputable def actualHistory {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) :
    List (Record N) :=
  (List.range n).flatMap (fun t : ℕ => List.ofFn (fun i : Fin N =>
    let c := Trajectory.departureCoord p m U t i
    (c, U c)))

lemma next_not_mem_used_actualHistory {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ)
    (i : Fin N) :
    Trajectory.departureCoord p m U n i ∉ used (actualHistory p m U n) := by
  intro hmem
  unfold used at hmem
  have hlist := List.mem_toFinset.mp hmem
  rcases List.mem_map.mp hlist with ⟨r, hr, hrcoord⟩
  rcases List.mem_flatMap.mp hr with ⟨t, ht, hrinner⟩
  have htlt : t < n := List.mem_range.mp ht
  rcases List.mem_ofFn.mp hrinner with ⟨j, hj⟩
  have hcoord : Trajectory.departureCoord p m U n i =
      Trajectory.departureCoord p m U t j := by
    simpa only [← hj] using hrcoord.symm
  have hpair : (i, n) = (j, t) := Trajectory.allDepartures_injective p m U hcoord
  have htn : n = t := congrArg Prod.snd hpair
  exact (Nat.lt_irrefl n (htn ▸ htlt))

lemma nextCoords_injective {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) :
    Function.Injective (fun i : Fin N => Trajectory.departureCoord p m U n i) := by
  intro i j hij
  exact congrArg Prod.fst hij

/-- Conditional law of the next coordinate vector given the complete used-coordinate
history of the actual recursive trajectory. -/
theorem measure_actualHistory_and_next {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ)
    {u : Fin N → ℝ} (hu0 : ∀ i, 0 ≤ u i) (hu1 : ∀ i, u i ≤ 1) :
    arrayMeasure N (historyEvent (actualHistory p m U n) ∩
      ⋂ i, (fun ω : Array N => ω (Trajectory.departureCoord p m U n i)) ⁻¹' Iio (u i)) =
      arrayMeasure N (historyEvent (actualHistory p m U n)) *
        ∏ i, ENNReal.ofReal (u i) := by
  exact measure_history_and_fresh (actualHistory p m U n) (nextCoords_injective p m U n)
    (fun i => next_not_mem_used_actualHistory p m U n i) hu0 hu1


/-- The same conditional product law for arbitrary measurable threshold sets. -/
theorem measure_actualHistory_and_next_sets {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ)
    (I : Fin N → Set ℝ) (hI : ∀ i, MeasurableSet (I i)) :
    arrayMeasure N (historyEvent (actualHistory p m U n) ∩
      ⋂ i, (fun ω : Array N => ω (Trajectory.departureCoord p m U n i)) ⁻¹' I i) =
      arrayMeasure N (historyEvent (actualHistory p m U n)) *
        ∏ i, arrayMeasure N ((fun ω : Array N => ω (Trajectory.departureCoord p m U n i)) ⁻¹' I i) := by
  have hm := SwarmIID.indep_fresh_finset (array_independent N) (fun c => measurable_pi_apply c)
    (nextCoords_injective p m U n) (fun i => next_not_mem_used_actualHistory p m U n i)
    (compatible (actualHistory p m U n)) (compatible_measurable (actualHistory p m U n)) I hI
  exact (preimage_compatible (actualHistory p m U n)) ▸ hm


end Swarming.History


