/-
# State-independence of the fresh future law, per past event

`Swarm/FreshLaw.lean` proves the paper's `(freshlaw)` in the *total* form

  `P(RegenAt p m · t d ∧ relFuture ∈ B) = P(recordSet p m t d) * P(posPath ∈ nonnegPath ∩ B)`,

a factorization of the regeneration mass.  That form is compatible with the future law depending
on the past: `MassSharp.lean` shows that stationarity of a record kernel alone does **not** give a
constant future mass, so `StationaryMass.mass_identity` needs the per-state identity `κ y C = pv`
on the whole record set `F`, not only a global product.

This file supplies the per-past-event form **in the actual array model** (`arrayMeasure N`, the
i.i.d. array law of the model): for *every* measurable set `A` of the strict past (the
coordinates below the record level `d`), the fresh future law is the same.  No invariant
measure, stopped kernel or stationary record process is constructed here.

Main results.

* `freshlaw_regen_past` — for every measurable past event `A` and every measurable `B`,
  `P(A ∧ RegenAt ∧ relFuture ∈ B) = P(A ∧ RecordAt) * P(posPath ∈ nonnegPath ∩ B)`.
  `A = univ` recovers `FreshLaw.freshlaw`; the added content is independence from the
  *particular* past configuration, which `(freshlaw)` alone does not give.
* `freshlaw_record_past_of_subset` — the same for `RecordAt` with an arbitrary measurable
  `S ⊆ nonnegPath` (recovers `FreshLaw.freshlaw_of_subset` at `A = univ`).
* `regen_mass_past` — `P(A ∧ Regen) = P(A ∧ Record) · P(fresh ∈ nonnegPath)`.
* `map_restrict_past` — the conditional-law form: for every past event `A`,
  `(P ↾ (A ∧ Regen)).map relFuture = P(A ∧ Record) • ν`, with the **same** measure `ν` for
  every `A`.  This is state-independence of the fresh law, stated without dividing.
* `cond_indep_past` — the conditional probability of a future event is the same from every past
  event (cross-multiplied form, no side conditions).

Explicitly not proved or claimed: a stationary past law `π` on `F`, the identification of the
array's low block with the compact record state `RecState N m`, the stopped recorded kernel
`hitW` / `hitKernel`, `Swarm.Ballistic`, `RegenAvailable`, `MainClaim`.
-/
import Swarm.FreshLaw
import Swarm.SeedPos

open MeasureTheory Set ProbabilityTheory
open Swarming Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmFresh
open scoped ENNReal

namespace SwarmFreshPast

variable {N : ℕ}

/-! ### Past events -/

/-- A **past event**: a set of arrays that only reads the coordinates strictly below level `d`.
Every measurable function of the strict past is of this form. -/
def pastSet (d : ℤ) (A : Set (lowSet (N := N) d → ℝ)) : Set (Array N) :=
  (lowSet d).domRestrict ⁻¹' A

theorem measurableSet_pastSet (d : ℤ) {A : Set (lowSet (N := N) d → ℝ)} (hA : MeasurableSet A) :
    MeasurableSet (pastSet (N := N) d A) :=
  (Set.measurable_restrict (lowSet (N := N) d)) hA

/-- A past event given by a measurable statistic of the low block (e.g. any record-state
observable, whenever the record state is a function of the strict past). -/
theorem measurableSet_pastStat {α : Type*} [MeasurableSpace α] (d : ℤ)
    {f : (lowSet (N := N) d → ℝ) → α} (hf : Measurable f) {D : Set α} (hD : MeasurableSet D) :
    MeasurableSet {U : Array N | f ((lowSet d).domRestrict U) ∈ D} := by
  have hEq : {U : Array N | f ((lowSet d).domRestrict U) ∈ D}
      = (lowSet d).domRestrict ⁻¹' (f ⁻¹' D) := rfl
  rw [hEq]
  exact (Set.measurable_restrict (lowSet (N := N) d)) (hf hD)

/-- **Calling the event a regeneration by its record form**, with an arbitrary past event.
`RegenAt` differs from `RecordAt` only by the no-return condition, which is a condition on the
future path; on `relFuture ∈ S ⊆ nonnegPath` the two agree. -/
theorem regen_iff_record_past (p : ℝ) (m t : ℕ) (d : ℤ)
    {A : Set (lowSet (N := N) d → ℝ)} {S B : Set (ℕ → Fin N → ℤ)}
    (hSsub : S ⊆ nonnegPath (N := N)) :
    {U : Array N | (lowSet d).domRestrict U ∈ A ∧ RegenAt p m U t d ∧
        relFuture p m U t d ∈ S ∩ B}
      = {U : Array N | (lowSet d).domRestrict U ∈ A ∧ RecordAt p m U t d ∧
          relFuture p m U t d ∈ S ∩ B} := by
  ext U
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨hA, hreg, hin, hB⟩
    exact ⟨hA, regenAt_recordAt hreg, hin, hB⟩
  · rintro ⟨hA, hrec, hin, hB⟩
    have hnon : relFuture p m U t d ∈ nonnegPath (N := N) := hSsub hin
    have hstay : ∀ n i, d ≤ (trajectory p m U (t + n)).pos i := by
      intro n i
      have h := hnon n i
      simp only [relFuture] at h
      omega
    have heq := relFuture_eq p m U ⟨hrec.1, hrec.2, hstay⟩
    refine ⟨hA, (regenAt_iff p m U t d).mpr ⟨hrec, ?_⟩, hin, hB⟩
    rw [← heq]
    exact hSsub hin

/-! ### The regeneration event with an arbitrary past event -/

/-- **Block decomposition with a past event.**  "The past lies in `A`, a regeneration occurs at
`(t,d)`, and the relative future lies in `B`" is the intersection of the low-block set
`A ∩ lowRecordSet` and the high-block future set. -/
theorem regenSet_past_eq (p : ℝ) (m t : ℕ) (d : ℤ) {A : Set (lowSet (N := N) d → ℝ)}
    (B : Set (ℕ → Fin N → ℤ)) :
    {U : Array N | (lowSet d).domRestrict U ∈ A ∧ RegenAt p m U t d ∧
        relFuture p m U t d ∈ B}
      = (lowSet d).domRestrict ⁻¹' (A ∩ lowRecordSet (N := N) p m t d)
        ∩ (highSet d).domRestrict ⁻¹' highFutureSet (N := N) p m d B := by
  have hsplit : {U : Array N | (lowSet d).domRestrict U ∈ A ∧ RegenAt p m U t d ∧
        relFuture p m U t d ∈ B}
      = (lowSet d).domRestrict ⁻¹' A ∩
          {U : Array N | RegenAt p m U t d ∧ relFuture p m U t d ∈ B} := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
  rw [hsplit, regenSet_eq p m t d B, ← Set.inter_assoc, ← Set.preimage_inter]

/-- **`(freshlaw)` with an arbitrary past event.**  For every measurable set `A` of the strict
past and every measurable `B`, the mass of "past in `A`, regeneration at `(t,d)`, relative
future in `B`" is the product of the record mass of `A` and the fresh mass of
`nonnegPath ∩ B`: the future does not depend on which past configuration occurred. -/
theorem freshlaw_regen_past (p : ℝ) (m t : ℕ) (d : ℤ)
    {A : Set (lowSet (N := N) d → ℝ)} (hA : MeasurableSet A)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (arrayMeasure N) {U : Array N | (lowSet d).domRestrict U ∈ A ∧
        RegenAt p m U t d ∧ relFuture p m U t d ∈ B}
      = (arrayMeasure N) {U : Array N | (lowSet d).domRestrict U ∈ A ∧ RecordAt p m U t d}
        * (arrayMeasure N) {U : Array N | posPath p m U ∈ nonnegPath (N := N) ∩ B} := by
  have hP : (arrayMeasure N) = Measure.infinitePi (fun _ : Fin N × ℤ × ℕ => uniform01) := rfl
  have hblock := SwarmBlock.block_measure_inter (fun _ : Fin N × ℤ × ℕ => uniform01)
    (disjoint_lowSet_highSet (N := N) d) (hA.inter (measurableSet_lowRecordSet p m t d))
    (measurableSet_highFutureSet (N := N) p m d hB)
  have hrec : {U : Array N | (lowSet d).domRestrict U ∈ A ∧ RecordAt p m U t d}
      = (lowSet d).domRestrict ⁻¹' (A ∩ lowRecordSet (N := N) p m t d) := by
    rw [Set.preimage_inter, ← recordSet_eq_low]
    rfl
  rw [regenSet_past_eq p m t d B, hP, hblock, ← hP,
    highFuture_measure p m d hB, hrec]

/-- **`(freshlaw)` with an arbitrary past event**, record form with `S ⊆ nonnegPath`.  With
`A = univ` this is exactly `FreshLaw.freshlaw_of_subset`. -/
theorem freshlaw_record_past_of_subset (p : ℝ) (m t : ℕ) (d : ℤ)
    {A : Set (lowSet (N := N) d → ℝ)} (hA : MeasurableSet A)
    {S B : Set (ℕ → Fin N → ℤ)} (hS : MeasurableSet S)
    (hSsub : S ⊆ nonnegPath (N := N)) (hB : MeasurableSet B) :
    (arrayMeasure N) {U : Array N | (lowSet d).domRestrict U ∈ A ∧
        RecordAt p m U t d ∧ relFuture p m U t d ∈ S ∩ B}
      = (arrayMeasure N) {U : Array N | (lowSet d).domRestrict U ∈ A ∧ RecordAt p m U t d}
        * (arrayMeasure N) {U : Array N | posPath p m U ∈ S ∩ B} := by
  have hP : (arrayMeasure N) = Measure.infinitePi (fun _ : Fin N × ℤ × ℕ => uniform01) := rfl
  have hblock := SwarmBlock.block_measure_inter (fun _ : Fin N × ℤ × ℕ => uniform01)
    (disjoint_lowSet_highSet (N := N) d) (hA.inter (measurableSet_lowRecordSet p m t d))
    (measurableSet_highFutureSet (N := N) p m d (hS.inter hB))
  have hrec : {U : Array N | (lowSet d).domRestrict U ∈ A ∧ RecordAt p m U t d}
      = (lowSet d).domRestrict ⁻¹' (A ∩ lowRecordSet (N := N) p m t d) := by
    rw [Set.preimage_inter, ← recordSet_eq_low]
    rfl
  have hSset : {U : Array N | posPath p m U ∈ nonnegPath (N := N) ∩ (S ∩ B)}
      = {U : Array N | posPath p m U ∈ S ∩ B} := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨-, h⟩; exact h
    · rintro ⟨hS', hB'⟩; exact ⟨hSsub hS', hS', hB'⟩
  rw [← regen_iff_record_past (N := N) p m t d (A := A) (S := S) (B := B) hSsub,
    regenSet_past_eq p m t d (S ∩ B), hP, hblock, ← hP,
    highFuture_measure p m d (hS.inter hB), hrec, hSset]

/-- The strict version: the paper's `(freshlaw)` for `V = strictPos` with an arbitrary past
event. -/
theorem freshlawStrict_record_past (p : ℝ) (m t : ℕ) (d : ℤ)
    {A : Set (lowSet (N := N) d → ℝ)} (hA : MeasurableSet A)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (arrayMeasure N) {U : Array N | (lowSet d).domRestrict U ∈ A ∧
        RecordAt p m U t d ∧ relFuture p m U t d ∈ strictPos (N := N) ∩ B}
      = (arrayMeasure N) {U : Array N | (lowSet d).domRestrict U ∈ A ∧ RecordAt p m U t d}
        * (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N) ∩ B} :=
  freshlaw_record_past_of_subset (N := N) p m t d hA measurableSet_strictPos
    strictPos_subset_nonnegPath hB

/-- **The past-mass factorization of the regeneration event.** -/
theorem regen_mass_past (p : ℝ) (m t : ℕ) (d : ℤ)
    {A : Set (lowSet (N := N) d → ℝ)} (hA : MeasurableSet A) :
    (arrayMeasure N) {U : Array N | (lowSet d).domRestrict U ∈ A ∧ RegenAt p m U t d}
      = (arrayMeasure N) {U : Array N | (lowSet d).domRestrict U ∈ A ∧ RecordAt p m U t d}
        * (arrayMeasure N) {U : Array N | posPath p m U ∈ nonnegPath (N := N)} := by
  have h := freshlaw_regen_past (N := N) p m t d hA (B := univ) MeasurableSet.univ
  simpa using h

/-- The strict past-mass factorization of the strict regeneration event. -/
theorem regenStrict_mass_past (p : ℝ) (m t : ℕ) (d : ℤ)
    {A : Set (lowSet (N := N) d → ℝ)} (hA : MeasurableSet A) :
    (arrayMeasure N) {U : Array N | (lowSet d).domRestrict U ∈ A ∧ RegenAtStrict p m U t d}
      = (arrayMeasure N) {U : Array N | (lowSet d).domRestrict U ∈ A ∧ RecordAt p m U t d}
        * (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} := by
  have h := freshlawStrict_record_past (N := N) p m t d hA (B := univ) MeasurableSet.univ
  have hset : {U : Array N | (lowSet d).domRestrict U ∈ A ∧ RegenAtStrict p m U t d}
      = {U : Array N | (lowSet d).domRestrict U ∈ A ∧ RecordAt p m U t d ∧
          relFuture p m U t d ∈ strictPos (N := N) ∩ univ} := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_univ, and_true]
    rw [regenAtStrict_iff]
  rw [hset, h, Set.inter_univ]

/-! ### Restart at a random record time

For a fixed level `d` and `N ≥ 1` the record times are unique, so the regeneration events over
`t` are pairwise disjoint; summing `freshlaw_regen_past` over `t` gives the fresh law at the
*random* record time, and a summability bound for the record probabilities. -/

/-- **The relative future after the (unique) regeneration at level `d` is fresh.**  Summing the
per-time identity over the times: the mass of "past in `A` and, at the unique `t` with a
regeneration at level `d`, the relative future in `B`" is the total record mass of `A`
(summed over `t`) times the fresh mass of `nonnegPath ∩ B`. -/
theorem restart_fresh (p : ℝ) (m : ℕ) (d : ℤ) (hN : 0 < N)
    {A : Set (lowSet (N := N) d → ℝ)} (hA : MeasurableSet A)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (arrayMeasure N) {U : Array N | (lowSet d).domRestrict U ∈ A ∧
        ∃ t, RegenAt p m U t d ∧ relFuture p m U t d ∈ B}
      = (∑' t : ℕ, (arrayMeasure N) {U : Array N | (lowSet d).domRestrict U ∈ A ∧
          RecordAt p m U t d})
        * (arrayMeasure N) {U : Array N | posPath p m U ∈ nonnegPath (N := N) ∩ B} := by
  have hmeas : ∀ t : ℕ, MeasurableSet {U : Array N | (lowSet d).domRestrict U ∈ A ∧
      RegenAt p m U t d ∧ relFuture p m U t d ∈ B} :=
    fun t => (measurableSet_pastSet d hA).inter
      ((measurableSet_regenSet p m t d).inter ((measurable_relFuture p m t d N) hB))
  have hdisj : Pairwise (fun t₁ t₂ : ℕ => Disjoint
      ({U : Array N | (lowSet d).domRestrict U ∈ A ∧ RegenAt p m U t₁ d ∧
        relFuture p m U t₁ d ∈ B} : Set (Array N))
      {U : Array N | (lowSet d).domRestrict U ∈ A ∧ RegenAt p m U t₂ d ∧
        relFuture p m U t₂ d ∈ B}) := by
    have hi : Fin N := ⟨0, hN⟩
    intro t₁ t₂ hne
    rw [Set.disjoint_left]
    rintro U ⟨-, hreg1, -⟩ ⟨-, hreg2, -⟩
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hlt' : (trajectory p m U t₁).pos hi < d := hreg2.1 t₁ hlt hi
      have heq : (trajectory p m U t₁).pos hi = d := hreg1.2.1 hi
      omega
    · have hlt' : (trajectory p m U t₂).pos hi < d := hreg1.1 t₂ hlt hi
      have heq : (trajectory p m U t₂).pos hi = d := hreg2.2.1 hi
      omega
  have hunion : {U : Array N | (lowSet d).domRestrict U ∈ A ∧
        ∃ t, RegenAt p m U t d ∧ relFuture p m U t d ∈ B}
      = ⋃ t, {U : Array N | (lowSet d).domRestrict U ∈ A ∧ RegenAt p m U t d ∧
          relFuture p m U t d ∈ B} := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨hA', t, hreg, hB'⟩; exact ⟨t, hA', hreg, hB'⟩
    · rintro ⟨t, hA', hreg, hB'⟩; exact ⟨hA', t, hreg, hB'⟩
  rw [hunion, MeasureTheory.measure_iUnion hdisj hmeas,
    tsum_congr fun t => freshlaw_regen_past p m t d hA hB, ENNReal.tsum_mul_right]

/-- **Summability of the record probabilities at a fixed level**, with the explicit bound
`1/P(fresh ∈ nonnegPath)`: the total record mass over all times, weighted by the fresh mass, is at
most `1`.  In the divided form (`ENNReal.le_inv_iff_mul_le`) this is
`∑' t, P(recordSet t d) ≤ P(fresh ∈ nonnegPath)⁻¹`. -/
theorem record_mass_mul_le_one (p : ℝ) (m : ℕ) (d : ℤ) (hN : 0 < N) :
    (∑' t : ℕ, (arrayMeasure N) (recordSet (N := N) p m t d))
        * (arrayMeasure N) {U : Array N | posPath p m U ∈ nonnegPath (N := N)} ≤ 1 := by
  have h := restart_fresh (N := N) p m d hN (A := univ) MeasurableSet.univ
    (B := univ) MeasurableSet.univ
  have hν : (arrayMeasure N) {U : Array N |
        posPath p m U ∈ nonnegPath (N := N) ∩ univ}
      = (arrayMeasure N) {U : Array N | posPath p m U ∈ nonnegPath (N := N)} := by
    congr 1
    ext U; simp
  have hrec : ∀ t : ℕ, (arrayMeasure N) {U : Array N |
        (lowSet d).domRestrict U ∈ (univ : Set (lowSet (N := N) d → ℝ)) ∧
        RecordAt p m U t d} = (arrayMeasure N) (recordSet (N := N) p m t d) :=
    fun t => by simp [recordSet]
  rw [hν, tsum_congr hrec] at h
  have h1 : (arrayMeasure N) {U : Array N |
        (lowSet d).domRestrict U ∈ (univ : Set (lowSet (N := N) d → ℝ)) ∧
        ∃ t, RegenAt p m U t d ∧ relFuture p m U t d ∈ (univ : Set (ℕ → Fin N → ℤ))} ≤ 1 := by
    have := measure_mono (μ := arrayMeasure N) (Set.subset_univ ({U : Array N |
      (lowSet d).domRestrict U ∈ (univ : Set (lowSet (N := N) d → ℝ)) ∧
      ∃ t, RegenAt p m U t d ∧ relFuture p m U t d ∈ (univ : Set (ℕ → Fin N → ℤ))} : Set (Array N)))
    simpa using this
  rw [h] at h1
  exact h1

/-- The divided form of the summability bound. -/
theorem record_mass_tsum_le (p : ℝ) (m : ℕ) (d : ℤ) (hN : 0 < N) :
    (∑' t : ℕ, (arrayMeasure N) (recordSet (N := N) p m t d))
      ≤ ((arrayMeasure N) {U : Array N | posPath p m U ∈ nonnegPath (N := N)})⁻¹ :=
  ENNReal.le_inv_iff_mul_le.mpr (record_mass_mul_le_one p m d hN)

/-! ### The conditional law of the fresh future is the same from every past event -/

/-- The fresh law `ν`: the law of the position path conditioned to stay nonnegative.  This is the
`P^*` of the paper. -/
noncomputable def freshLaw (p : ℝ) (m : ℕ) (N : ℕ) : Measure (ℕ → Fin N → ℤ) :=
  (Measure.restrict (arrayMeasure N) {U : Array N | posPath p m U ∈ nonnegPath (N := N)}).map
    (fun U => posPath p m U)

theorem freshLaw_apply (p : ℝ) (m : ℕ) {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    freshLaw p m N B
      = (arrayMeasure N) {U : Array N | posPath p m U ∈ nonnegPath (N := N) ∩ B} := by
  rw [freshLaw, Measure.map_apply (measurable_posPath p m N) hB,
    Measure.restrict_apply ((measurable_posPath p m N) hB)]
  congr 1
  ext U; simp [and_comm]

/-- **The conditional law of the relative future given any past event.**  For every measurable
past event `A` the conditional law of the relative future on "past in `A` and a regeneration at
`(t,d)`" is the *same* measure `freshLaw` times the mass `P(A ∧ RecordAt)`. -/
theorem map_restrict_past (p : ℝ) (m t : ℕ) (d : ℤ)
    {A : Set (lowSet (N := N) d → ℝ)} (hA : MeasurableSet A) :
    (Measure.restrict (arrayMeasure N) {U : Array N | (lowSet d).domRestrict U ∈ A ∧
        RegenAt p m U t d}).map (fun U => relFuture p m U t d)
      = (arrayMeasure N) {U : Array N | (lowSet d).domRestrict U ∈ A ∧ RecordAt p m U t d}
        • freshLaw p m N := by
  refine Measure.ext fun B hB => ?_
  have hΦ : Measurable fun U : Array N => relFuture p m U t d := measurable_relFuture p m t d N
  have hset : (fun U => relFuture p m U t d) ⁻¹' B ∩
      {U : Array N | (lowSet d).domRestrict U ∈ A ∧ RegenAt p m U t d}
      = {U : Array N | (lowSet d).domRestrict U ∈ A ∧ RegenAt p m U t d ∧
          relFuture p m U t d ∈ B} := by
    ext U; simp [and_assoc, and_left_comm, and_comm]
  rw [Measure.map_apply hΦ hB, Measure.restrict_apply (hΦ hB), hset, Measure.smul_apply,
    smul_eq_mul, freshLaw_apply p m hB]
  exact freshlaw_regen_past p m t d hA hB

/-- **Conditional independence of the future from the past**, in cross-multiplied form: the
conditional probability of a future event on the regeneration event does not depend on the past
event it is conditioned on. -/
theorem cond_indep_past (p : ℝ) (m t : ℕ) (d : ℤ)
    {A₁ A₂ : Set (lowSet (N := N) d → ℝ)} (h₁ : MeasurableSet A₁) (h₂ : MeasurableSet A₂)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (arrayMeasure N) {U : Array N | (lowSet d).domRestrict U ∈ A₁ ∧
        RegenAt p m U t d ∧ relFuture p m U t d ∈ B}
      * (arrayMeasure N) {U : Array N | (lowSet d).domRestrict U ∈ A₂ ∧ RegenAt p m U t d}
      = (arrayMeasure N) {U : Array N | (lowSet d).domRestrict U ∈ A₂ ∧
          RegenAt p m U t d ∧ relFuture p m U t d ∈ B}
        * (arrayMeasure N) {U : Array N | (lowSet d).domRestrict U ∈ A₁ ∧
          RegenAt p m U t d} := by
  rw [freshlaw_regen_past p m t d h₁ hB, freshlaw_regen_past p m t d h₂ hB,
    regen_mass_past p m t d h₂, regen_mass_past p m t d h₁]
  ring

/-- **The paper's display for the actual array model, with an arbitrary past statistic.**
For every measurable statistic `f` of the strict past (in particular for any record-state
observable, whenever the record state is a function of the strict past), the joint law of
"(past state, relative future)" on the regeneration event puts mass

  `P(past state ∈ F and record at (t,d)) · P^*(C)`

on `F × C`, with the *same* `P^* = freshLaw` for every `F`.  This is the array-model form of the
paper's `P_π(A) = π(F) P(V)` / `P_π(X ∈ B | A) = P^*(B)`. -/
theorem joint_factor {α : Type*} [MeasurableSpace α] (p : ℝ) (m t : ℕ) (d : ℤ)
    {f : (lowSet (N := N) d → ℝ) → α} (hf : Measurable f)
    {F : Set α} (hF : MeasurableSet F) {C : Set (ℕ → Fin N → ℤ)} (hC : MeasurableSet C) :
    ((Measure.restrict (arrayMeasure N) {U : Array N | f ((lowSet d).domRestrict U) ∈ F ∧
        RegenAt p m U t d}).map
        (fun U => (f ((lowSet d).domRestrict U), relFuture p m U t d))) (F ×ˢ C)
      = (arrayMeasure N) {U : Array N | f ((lowSet d).domRestrict U) ∈ F ∧ RecordAt p m U t d}
        * freshLaw p m N C := by
  have hfR : Measurable fun U : Array N => f ((lowSet d).domRestrict U) :=
    hf.comp (Set.measurable_restrict (lowSet (N := N) d))
  have hΦ : Measurable fun U : Array N => (f ((lowSet d).domRestrict U), relFuture p m U t d) :=
    hfR.prod (measurable_relFuture p m t d N)
  have hset : (fun U : Array N => (f ((lowSet d).domRestrict U), relFuture p m U t d)) ⁻¹' (F ×ˢ C)
        ∩ {U : Array N | f ((lowSet d).domRestrict U) ∈ F ∧ RegenAt p m U t d}
      = {U : Array N | f ((lowSet d).domRestrict U) ∈ F ∧ RegenAt p m U t d ∧
          relFuture p m U t d ∈ C} := by
    ext U; simp [and_assoc, and_left_comm, and_comm]
  rw [Measure.map_apply hΦ (hF.prod hC), Measure.restrict_apply (hΦ (hF.prod hC)), hset]
  have hmain := freshlaw_regen_past (N := N) p m t d (A := f ⁻¹' F) (hf hF) hC
  simpa [freshLaw_apply p m hC] using hmain

/-- The fresh law restricted to `strictPos` (the paper's `P^*`), evaluated on a measurable set. -/
theorem strictLaw_apply (p : ℝ) (m : ℕ) {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    ((Measure.restrict (arrayMeasure N)
        {U : Array N | posPath p m U ∈ strictPos (N := N)}).map
        (fun U => posPath p m U)) B
      = (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N) ∩ B} := by
  rw [Measure.map_apply (measurable_posPath p m N) hB,
    Measure.restrict_apply ((measurable_posPath p m N) hB)]
  congr 1
  ext U; simp [and_comm]

/-- **The paper's `(factor)` with an arbitrary past event.**  For `S = strictPos`, every
measurable past event `A` and every measurable `B`:
`μ(A ∧ Regen ∧ Φ⁻¹ B) = μ(A ∧ Regen) · P(V)⁻¹ · P^*(B)`, where `P(V) = P(posPath ∈ strictPos)`
and `P^*` is the fresh law restricted to `strictPos`.  This is the `hfac` shape consumed by
`KacFormula.kac_paper_bound`, now available from every state of the record set. -/
theorem hfac_strict_past (p : ℝ) (m t : ℕ) (d : ℤ)
    {A : Set (lowSet (N := N) d → ℝ)} (hA : MeasurableSet A)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B)
    (hV : (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} ≠ 0)
    (hVtop : (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} ≠ ⊤) :
    (arrayMeasure N) {U : Array N | (lowSet d).domRestrict U ∈ A ∧
        RegenAtStrict p m U t d ∧ relFuture p m U t d ∈ B}
      = (arrayMeasure N) {U : Array N | (lowSet d).domRestrict U ∈ A ∧
          RegenAtStrict p m U t d}
        * (((arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)})⁻¹
          * (((Measure.restrict (arrayMeasure N)
              {U : Array N | posPath p m U ∈ strictPos (N := N)}).map
              (fun U => posPath p m U)) B)) := by
  have h1 : {U : Array N | (lowSet d).domRestrict U ∈ A ∧ RegenAtStrict p m U t d ∧
        relFuture p m U t d ∈ B}
      = {U : Array N | (lowSet d).domRestrict U ∈ A ∧ RecordAt p m U t d ∧
          relFuture p m U t d ∈ strictPos (N := N) ∩ B} := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    rw [regenAtStrict_iff]
    constructor
    · rintro ⟨hA', ⟨hrec, hin⟩, hB'⟩
      exact ⟨hA', hrec, hin, hB'⟩
    · rintro ⟨hA', hrec, hin, hB'⟩
      exact ⟨hA', ⟨hrec, hin⟩, hB'⟩
  rw [h1, freshlawStrict_record_past p m t d hA hB, regenStrict_mass_past p m t d hA,
    strictLaw_apply p m hB, mul_assoc, ENNReal.mul_inv_cancel_left hV hVtop]

/-- **The conditional probability is the fresh one, from every past event.**  For a past event
`A` of positive regeneration mass, the conditional probability of a future event `B` on the
regeneration event is `P(fresh ∈ nonnegPath ∩ B) / P(fresh ∈ nonnegPath)` — independently of
which past configuration `A` describes. -/
theorem cond_prob_eq_past (p : ℝ) (m t : ℕ) (d : ℤ)
    {A : Set (lowSet (N := N) d → ℝ)} (hA : MeasurableSet A)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B)
    (hmass : (arrayMeasure N) {U : Array N | (lowSet d).domRestrict U ∈ A ∧
      RegenAt p m U t d} ≠ 0) :
    (arrayMeasure N) {U : Array N | (lowSet d).domRestrict U ∈ A ∧
        RegenAt p m U t d ∧ relFuture p m U t d ∈ B}
        / (arrayMeasure N) {U : Array N | (lowSet d).domRestrict U ∈ A ∧ RegenAt p m U t d}
      = (arrayMeasure N) {U : Array N | posPath p m U ∈ nonnegPath (N := N) ∩ B}
        / (arrayMeasure N) {U : Array N | posPath p m U ∈ nonnegPath (N := N)} := by
  have hm : (arrayMeasure N) {U : Array N | (lowSet d).domRestrict U ∈ A ∧
      RecordAt p m U t d} ≠ 0 := by
    intro h0
    exact hmass (by rw [regen_mass_past p m t d hA, h0, zero_mul])
  have hm_top : (arrayMeasure N) {U : Array N | (lowSet d).domRestrict U ∈ A ∧
      RecordAt p m U t d} ≠ ⊤ := measure_ne_top _ _
  rw [freshlaw_regen_past p m t d hA hB, regen_mass_past p m t d hA,
    ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
    ENNReal.mul_inv (Or.inl hm) (Or.inl hm_top), mul_mul_mul_comm,
    ENNReal.inv_mul_cancel hm hm_top, one_mul]

/-- Consistency: with `A = univ` the past-event form is exactly `FreshLaw.freshlaw`. -/
theorem freshlaw_regen_past_univ (p : ℝ) (m t : ℕ) (d : ℤ)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (arrayMeasure N) {U : Array N | RegenAt p m U t d ∧ relFuture p m U t d ∈ B}
      = (arrayMeasure N) (recordSet (N := N) p m t d)
        * (arrayMeasure N) {U : Array N | posPath p m U ∈ nonnegPath (N := N) ∩ B} := by
  have h := freshlaw_regen_past (N := N) p m t d (A := univ) MeasurableSet.univ hB
  simpa [recordSet] using h

/-- Non-vacuity of the `strictPos` forms: the seed probability is positive for the model's
parameter range, so the strict identities are not conditional on an unprovable premise. -/
theorem strictPos_measure_pos {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (hN : 2 ≤ N) :
    (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} ≠ 0 :=
  SwarmSeed.strictPos_measure_ne_zero hp0 hp1 hm hN

theorem strictPos_measure_ne_top {p : ℝ} (m : ℕ) :
    (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} ≠ ⊤ :=
  measure_ne_top _ _

end SwarmFreshPast
