/-
# The `P*` segment law: the future after a regeneration is independent of the *whole* past

`Swarm/FreshLaw.lean` proves the paper's `(freshlaw)` in the form

  `P(RegenAt t d ∧ relFuture ∈ B) = P(RecordAt t d) * P(posPath ∈ S ∩ B)`,

i.e. the post-regeneration segment is independent of the *record event*.  The paper
(`main_1d_revised.tex`, §3.2) states strictly more:

  "the translated future after `τ_D` has law `P^*` and is independent of
   `(D, τ_D, (X_n^i)_{0 ≤ n ≤ τ_D})`",

and this full-past form is what "by iteration, the successive distance and duration
increments are independent and identically distributed" uses.  The two statements are not
the same: the record event is one particular low-block set, whereas the past is the whole
prefix *path*, an infinite family of low-block sets.

This file proves the full-past form for the actual i.i.d.-uniform array, and isolates the
resulting object `Pstar` as a single law on path space that does not depend on the
regeneration time `t`, on the regeneration level `d`, or on the starting configuration.

## Main results

* `freshlaw_past_of_subset` — the factorisation for an arbitrary allowed set
  `S ⊆ nonnegPath` of fresh paths;
* `freshlaw_past` — `S = nonnegPath`;
* `freshlawStrict_past` — `S = strictPos` (the paper's strict `V`);
* `Pstar` — the paper's `P^*`;
* `Pstar_self` — `P*(nonnegPath) = 1`: the post-regeneration process never returns below
  its level (the first clause of `Swarm.Sandwich` at `k ≥ 1`).

Residual hypothesis, stated exactly as an argument: `0 < P(posPath ∈ nonnegPath)` (the
paper's `P(V) > 0`), exactly as in `FreshLaw.freshlaw_hfac`.  Nothing else is assumed.
-/
import Swarm.FreshLaw

open MeasureTheory Set ProbabilityTheory
open Swarming Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmFresh
open scoped ENNReal

set_option warn.classDefReducibility false

namespace SwarmSeg

variable {N : ℕ}

/-! ### The prefix of the position path -/

/-- The position path up to time `t` — the paper's `(X_n^i)_{0 ≤ n ≤ τ_D}` with `τ_D = t`. -/
noncomputable def pastProj (p : ℝ) (m : ℕ) (t : ℕ) (U : Array N) :
    Fin (t + 1) → Fin N → ℤ :=
  fun s i => (trajectory p m U s).pos i

theorem measurable_pastProj (p : ℝ) (m : ℕ) (t : ℕ) (N : ℕ) :
    Measurable (fun U : Array N => pastProj p m t U) := by
  refine measurable_pi_iff.mpr (fun s => measurable_pi_iff.mpr (fun i => ?_))
  exact (Swarming.Fair.measurable_trajectory p m (s : ℕ)).1 i

/-- **The prefix path below the record level reads only the low block.** -/
theorem pastProj_congr_of_low {p : ℝ} {m : ℕ} {t : ℕ} {d : ℤ} {U U' : Array N}
    (harr : ∀ (i : Fin N) (x : ℤ) (k : ℕ), x < d → U (i, x, k) = U' (i, x, k))
    (hU : RecordAt p m U t d) :
    pastProj p m t U = pastProj p m t U' := by
  funext s i
  have hs : (s : ℕ) ≤ t := Nat.lt_succ_iff.mp s.2
  have h := (agreeBelow_traj (p := p) (m := m) (d := d) (U := U) (U' := U') harr (s : ℕ)
    (fun k hk i => hU.1 k (lt_of_lt_of_le hk hs) i)).1 i
  exact h

/-! ### The record event with the past in a measurable set: a low-block set -/

/-- The record event together with a condition on the prefix path, as a set of arrays. -/
def recordPastSet (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ)
    (A : Set (Fin (t + 1) → Fin N → ℤ)) : Set (Array N) :=
  {U | RecordAt p m U t d ∧ pastProj p m t U ∈ A}

/-- The same event as a condition on the low block. -/
def lowRecordPastSet (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ)
    (A : Set (Fin (t + 1) → Fin N → ℤ)) : Set (lowSet (N := N) d → ℝ) :=
  {V | RecordAt p m (lowExtend (N := N) d V) t d ∧
    pastProj p m t (lowExtend (N := N) d V) ∈ A}

theorem mem_lowRecordPastSet {p : ℝ} {m : ℕ} {t : ℕ} {d : ℤ}
    {A : Set (Fin (t + 1) → Fin N → ℤ)} {U : Array N} :
    (lowSet d).domRestrict U ∈ lowRecordPastSet (N := N) p m t d A ↔
      RecordAt p m U t d ∧ pastProj p m t U ∈ A := by
  have hle := lowExtend_domRestrict_agree (N := N) d U
  have hles : ∀ (i : Fin N) (x : ℤ) (k : ℕ), x < d →
      U (i, x, k) = lowExtend (N := N) d ((lowSet d).domRestrict U) (i, x, k) :=
    fun i x k hx => (hle i x k hx).symm
  constructor
  · rintro ⟨hrec, hA⟩
    refine ⟨(recordAt_congr (p := p) (m := m) (t := t) (d := d)
      (U := lowExtend (N := N) d ((lowSet d).domRestrict U)) (U' := U) hle).mp hrec, ?_⟩
    rw [← pastProj_congr_of_low (U := lowExtend (N := N) d ((lowSet d).domRestrict U))
      (U' := U) hle hrec]
    exact hA
  · rintro ⟨hrec, hA⟩
    refine ⟨(recordAt_congr (p := p) (m := m) (t := t) (d := d)
      (U := U) (U' := lowExtend (N := N) d ((lowSet d).domRestrict U)) hles).mp hrec, ?_⟩
    rw [← pastProj_congr_of_low (U := U) (U' := lowExtend (N := N) d ((lowSet d).domRestrict U))
      hles hrec]
    exact hA

theorem recordPastSet_eq_low (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ)
    (A : Set (Fin (t + 1) → Fin N → ℤ)) :
    recordPastSet (N := N) p m t d A =
      (lowSet d).domRestrict ⁻¹' lowRecordPastSet (N := N) p m t d A := by
  ext U
  simp only [recordPastSet, Set.mem_ofPred_eq, Set.mem_preimage]
  exact (mem_lowRecordPastSet (p := p) (m := m) (t := t) (d := d) (A := A)).symm

theorem measurableSet_recordPastSet (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ)
    {A : Set (Fin (t + 1) → Fin N → ℤ)} (hA : MeasurableSet A) :
    MeasurableSet (recordPastSet (N := N) p m t d A) :=
  (measurableSet_recordSet p m t d).inter ((measurable_pastProj p m t N) hA)

theorem measurableSet_lowRecordPastSet (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ)
    {A : Set (Fin (t + 1) → Fin N → ℤ)} (hA : MeasurableSet A) :
    MeasurableSet (lowRecordPastSet (N := N) p m t d A) :=
  (measurable_lowExtend d) (measurableSet_recordPastSet p m t d hA)

/-! ### The factorisation with a free past -/

/-- **`(freshlaw)` with the whole past path on the past side.**  The set identity: the event
"record at `(t,d)`, past path in `A`, segment in `S ∩ B`" is a low-block set intersected with
a high-block set. -/
theorem regenPast_eq (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ) {S : Set (ℕ → Fin N → ℤ)}
    (hSsub : S ⊆ nonnegPath (N := N)) (A : Set (Fin (t + 1) → Fin N → ℤ))
    (B : Set (ℕ → Fin N → ℤ)) :
    {U : Array N | RecordAt p m U t d ∧ pastProj p m t U ∈ A ∧ relFuture p m U t d ∈ S ∩ B}
      = (lowSet d).domRestrict ⁻¹' lowRecordPastSet (N := N) p m t d A
        ∩ (highSet d).domRestrict ⁻¹' highFutureSet (N := N) p m d (S ∩ B) := by
  rw [highFuture_eq p m d (S ∩ B)]
  ext U
  have hL : ((lowSet d).domRestrict U ∈ lowRecordPastSet (N := N) p m t d A) ↔
      (RecordAt p m U t d ∧ pastProj p m t U ∈ A) := mem_lowRecordPastSet
  constructor
  · intro h
    obtain ⟨hrec, hA, hS1, hB1⟩ := h
    have hnon : relFuture p m U t d ∈ nonnegPath (N := N) := hSsub hS1
    simp only [nonnegPath, Set.mem_ofPred_eq, relFuture] at hnon
    have hstay : ∀ n i, d ≤ (trajectory p m U (t + n)).pos i := by
      intro n i; have := hnon n i; omega
    have heq : relFuture p m U t d = posPath p m (levelShift d U) :=
      relFuture_eq p m U ⟨hrec.1, hrec.2, hstay⟩
    rw [heq] at hS1 hB1
    exact ⟨hL.mpr ⟨hrec, hA⟩, hSsub hS1, hS1, hB1⟩
  · intro h
    obtain ⟨hLh, hnon, hS1, hB1⟩ := h
    obtain ⟨hrec, hA⟩ := hL.mp hLh
    have hreg : RegenAt p m U t d := (regenAt_iff p m U t d).mpr ⟨hrec, hnon⟩
    have heq : relFuture p m U t d = posPath p m (levelShift d U) := relFuture_eq p m U hreg
    refine ⟨hrec, hA, ?_⟩
    rw [heq]
    exact ⟨hS1, hB1⟩

/-- **`(freshlaw)` with the whole past path**: for every regeneration point `(t,d)`, every
measurable set `A` of prefix paths and every allowed set `S ⊆ nonnegPath` of fresh paths, the
joint law of (past, segment) factorises. -/
theorem freshlaw_past_of_subset (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ)
    {S : Set (ℕ → Fin N → ℤ)} (hS : MeasurableSet S) (hSsub : S ⊆ nonnegPath (N := N))
    {A : Set (Fin (t + 1) → Fin N → ℤ)} (hA : MeasurableSet A)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (arrayMeasure N) {U : Array N | RecordAt p m U t d ∧ pastProj p m t U ∈ A ∧
        relFuture p m U t d ∈ S ∩ B}
      = (arrayMeasure N) (recordPastSet (N := N) p m t d A)
        * (arrayMeasure N) {U : Array N | posPath p m U ∈ S ∩ B} := by
  have hP : (arrayMeasure N) = Measure.infinitePi (fun _ : Fin N × ℤ × ℕ => uniform01) := rfl
  have hstep : {U : Array N | RecordAt p m U t d ∧ pastProj p m t U ∈ A ∧
        relFuture p m U t d ∈ S ∩ B}
      = (lowSet d).domRestrict ⁻¹' lowRecordPastSet (N := N) p m t d A
        ∩ (highSet d).domRestrict ⁻¹' highFutureSet (N := N) p m d (S ∩ B) :=
    regenPast_eq p m t d hSsub A B
  have hblock := SwarmBlock.block_measure_inter (fun _ : Fin N × ℤ × ℕ => uniform01)
    (disjoint_lowSet_highSet (N := N) d) (measurableSet_lowRecordPastSet p m t d hA)
    (measurableSet_highFutureSet (N := N) p m d (hS.inter hB))
  have hhigh := highFuture_measure p m d (hS.inter hB)
  have hset : {U : Array N | posPath p m U ∈ nonnegPath (N := N) ∩ (S ∩ B)}
      = {U : Array N | posPath p m U ∈ S ∩ B} := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨-, h⟩; exact h
    · rintro ⟨h1, h2⟩; exact ⟨hSsub h1, h1, h2⟩
  rw [hP, hstep, hblock, ← recordPastSet_eq_low, ← hP, hhigh, hset]

/-- **The paper's `(freshlaw)`, full-past form**: the post-regeneration segment is independent
of the entire prefix path, with the fresh law conditioned on never returning below the level. -/
theorem freshlaw_past (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ)
    {A : Set (Fin (t + 1) → Fin N → ℤ)} (hA : MeasurableSet A)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (arrayMeasure N) {U : Array N | RecordAt p m U t d ∧ pastProj p m t U ∈ A ∧
        relFuture p m U t d ∈ nonnegPath (N := N) ∩ B}
      = (arrayMeasure N) (recordPastSet (N := N) p m t d A)
        * (arrayMeasure N) {U : Array N | posPath p m U ∈ nonnegPath (N := N) ∩ B} :=
  freshlaw_past_of_subset p m t d measurableSet_nonnegPath (subset_refl _) hA hB

/-- **The paper's strict `V`, full-past form.** -/
theorem freshlawStrict_past (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ)
    {A : Set (Fin (t + 1) → Fin N → ℤ)} (hA : MeasurableSet A)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (arrayMeasure N) {U : Array N | RecordAt p m U t d ∧ pastProj p m t U ∈ A ∧
        relFuture p m U t d ∈ strictPos (N := N) ∩ B}
      = (arrayMeasure N) (recordPastSet (N := N) p m t d A)
        * (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N) ∩ B} :=
  freshlaw_past_of_subset p m t d measurableSet_strictPos strictPos_subset_nonnegPath hA hB


/-! ### The paper's `P^*` -/

/-- The array event "the fresh path never returns below its starting level". -/
def seedSet (p : ℝ) (m : ℕ) (N : ℕ) : Set (Array N) :=
  {U | posPath p m U ∈ nonnegPath (N := N)}

theorem measurableSet_seedSet (p : ℝ) (m : ℕ) (N : ℕ) : MeasurableSet (seedSet p m N) :=
  (measurable_posPath p m N) measurableSet_nonnegPath

theorem seedSet_ne_top (p : ℝ) (m : ℕ) (N : ℕ) : (arrayMeasure N) (seedSet p m N) ≠ ⊤ :=
  measure_ne_top _ _

/-- The law of the fresh path, conditioned on `V` — but written without the division. -/
noncomputable def freshLaw (p : ℝ) (m : ℕ) (N : ℕ) : Measure (ℕ → Fin N → ℤ) :=
  (Measure.restrict (arrayMeasure N) (seedSet p m N)).map (fun U => posPath p m U)

/-- **The paper's `P^*`**: the law of the process started at a regeneration, i.e. of the fresh
model conditioned on never returning below the regeneration level. -/
noncomputable def Pstar (p : ℝ) (m : ℕ) (N : ℕ) : Measure (ℕ → Fin N → ℤ) :=
  ((arrayMeasure N) (seedSet p m N))⁻¹ • freshLaw p m N

/-- The fresh conditioned law, evaluated by transfer. -/
theorem freshLaw_apply (p : ℝ) (m : ℕ) (N : ℕ) {B : Set (ℕ → Fin N → ℤ)}
    (hB : MeasurableSet B) :
    freshLaw p m N B = (arrayMeasure N) {U : Array N | posPath p m U ∈ nonnegPath (N := N) ∩ B} := by
  rw [freshLaw, Measure.map_apply (measurable_posPath p m N) hB, Measure.restrict_apply
    ((measurable_posPath p m N) hB)]
  congr 1
  ext U
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, seedSet]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

theorem freshLaw_univ (p : ℝ) (m : ℕ) (N : ℕ) :
    freshLaw p m N univ = (arrayMeasure N) (seedSet p m N) := by
  rw [freshLaw_apply p m N MeasurableSet.univ]
  congr 1
  ext U
  simp [seedSet]

/-- **`P^*` is concentrated on `V`**: the process started at a regeneration never returns below
its level.  This is the path structure that `Swarm.Sandwich`'s lower clause records for
`k ≥ 1`. -/
theorem Pstar_self (p : ℝ) (m : ℕ) (N : ℕ)
    (hV : (arrayMeasure N) (seedSet p m N) ≠ 0) :
    Pstar p m N (nonnegPath (N := N)) = 1 := by
  have htop := seedSet_ne_top p m N
  have hmap : freshLaw p m N (nonnegPath (N := N)) = (arrayMeasure N) (seedSet p m N) := by
    rw [freshLaw_apply p m N measurableSet_nonnegPath]
    congr 1
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, seedSet]
    exact ⟨fun h => h.2, fun h => ⟨h, h⟩⟩
  rw [Pstar, Measure.smul_apply, hmap, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hV htop

/-- **`P^*` is a probability measure** as soon as the seed event has positive mass. -/
theorem Pstar_isProbabilityMeasure (p : ℝ) (m : ℕ) (N : ℕ)
    (hV : (arrayMeasure N) (seedSet p m N) ≠ 0) :
    IsProbabilityMeasure (Pstar p m N) := by
  refine ⟨?_⟩
  have htop := seedSet_ne_top p m N
  rw [Pstar, Measure.smul_apply, freshLaw_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hV htop

/-- Evaluation of a conditioned measure, kept in `mul` form to avoid division. -/
theorem cond_apply {T : Set (Array N)} (hT : MeasurableSet T) {A : Set (Array N)}
    {c : ℝ≥0∞} :
    (c⁻¹ • (Measure.restrict (arrayMeasure N) A)) T = c⁻¹ * (arrayMeasure N) (T ∩ A) := by
  rw [Measure.smul_apply, Measure.restrict_apply hT, smul_eq_mul]

/-! ### The conditional law of the segment is `P^*`, for every regeneration point -/

/-- The event "a regeneration, past in `A`, segment in `B`" differs from the event of
`freshlaw_past` only by the no-return clause, which `RegenAt` already contains. -/
theorem regenPast_set_eq (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ)
    (A : Set (Fin (t + 1) → Fin N → ℤ)) (B : Set (ℕ → Fin N → ℤ)) :
    {U : Array N | RegenAt p m U t d ∧ pastProj p m t U ∈ A ∧ relFuture p m U t d ∈ B}
      = {U : Array N | RecordAt p m U t d ∧ pastProj p m t U ∈ A ∧
          relFuture p m U t d ∈ nonnegPath (N := N) ∩ B} := by
  ext U
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨hreg, hA, hB⟩
    refine ⟨regenAt_recordAt hreg, hA, ?_, hB⟩
    have hiff := (regenAt_iff p m U t d).mp hreg
    have heq : relFuture p m U t d = posPath p m (levelShift d U) := relFuture_eq p m U hreg
    rw [heq]
    exact hiff.2
  · rintro ⟨hrec, hA, hnon', hB⟩
    have hstay : ∀ n i, d ≤ (trajectory p m U (t + n)).pos i := by
      intro n i
      have h := hnon' n i
      simp only [relFuture] at h
      omega
    have heq : relFuture p m U t d = posPath p m (levelShift d U) :=
      relFuture_eq p m U ⟨hrec.1, hrec.2, hstay⟩
    have hnon2 : posPath p m (levelShift d U) ∈ nonnegPath (N := N) := by
      rw [← heq]; exact hnon'
    exact ⟨(regenAt_iff p m U t d).mpr ⟨hrec, hnon2⟩, hA, hB⟩

/-- **The conditional law of the post-regeneration segment is `P^*`**, for every regeneration
point `(t,d)`.  This is the paper's "the translated future after `τ_D` has law `P^*`". -/
theorem cond_regen_map_relFuture (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ)
    (hreg : (arrayMeasure N) {U : Array N | RegenAt p m U t d} ≠ 0) :
    ((arrayMeasure N) {U : Array N | RegenAt p m U t d})⁻¹ •
        (Measure.restrict (arrayMeasure N) {U : Array N | RegenAt p m U t d}).map
          (fun U => relFuture p m U t d)
      = Pstar p m N := by
  have hfac := regenAt_measure_factor (N := N) p m t d
  have hrec0 : (arrayMeasure N) (recordSet (N := N) p m t d) ≠ 0 := by
    intro h0
    exact hreg (by rw [hfac, h0]; simp)
  have hrectop : (arrayMeasure N) (recordSet (N := N) p m t d) ≠ ⊤ := measure_ne_top _ _
  set r := (arrayMeasure N) (recordSet (N := N) p m t d) with hr
  set s := (arrayMeasure N) (seedSet p m N) with hs
  have hc : (arrayMeasure N) {U : Array N | RegenAt p m U t d} = r * s := hfac
  have hkey : (r * s)⁻¹ * r = s⁻¹ := by
    calc (r * s)⁻¹ * r = (r⁻¹ * s⁻¹) * r := by
          rw [ENNReal.mul_inv (Or.inl hrec0) (Or.inl hrectop)]
      _ = r⁻¹ * (s⁻¹ * r) := mul_assoc _ _ _
      _ = r⁻¹ * (r * s⁻¹) := by rw [mul_comm s⁻¹ r]
      _ = (r⁻¹ * r) * s⁻¹ := (mul_assoc _ _ _).symm
      _ = 1 * s⁻¹ := by rw [ENNReal.inv_mul_cancel hrec0 hrectop]
      _ = s⁻¹ := one_mul _
  rw [hc, restrict_regen_map, smul_smul, hkey, Pstar, freshLaw, hs]
  rfl

/-- **`P^*` does not depend on the start configuration**: the conditional law of the segment is
the same at every regeneration point of positive mass. -/
theorem cond_regen_map_relFuture_eq (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ) (t' : ℕ) (d' : ℤ)
    (h1 : (arrayMeasure N) {U : Array N | RegenAt p m U t d} ≠ 0)
    (h2 : (arrayMeasure N) {U : Array N | RegenAt p m U t' d'} ≠ 0) :
    ((arrayMeasure N) {U : Array N | RegenAt p m U t d})⁻¹ •
        (Measure.restrict (arrayMeasure N) {U : Array N | RegenAt p m U t d}).map
          (fun U => relFuture p m U t d)
      = ((arrayMeasure N) {U : Array N | RegenAt p m U t' d'})⁻¹ •
        (Measure.restrict (arrayMeasure N) {U : Array N | RegenAt p m U t' d'}).map
          (fun U => relFuture p m U t' d') := by
  rw [cond_regen_map_relFuture p m t d h1, cond_regen_map_relFuture p m t' d' h2]


/-! ### Conditional independence of the segment from the whole past -/

/-- Mass of "past in `A` and a regeneration", factorised. -/
theorem measure_regen_inter_past (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ)
    {A : Set (Fin (t + 1) → Fin N → ℤ)} (hA : MeasurableSet A) :
    (arrayMeasure N) ((fun U : Array N => pastProj p m t U) ⁻¹' A ∩
        {U : Array N | RegenAt p m U t d})
      = (arrayMeasure N) (recordPastSet (N := N) p m t d A)
        * (arrayMeasure N) (seedSet p m N) := by
  have hset : ((fun U : Array N => pastProj p m t U) ⁻¹' A ∩
      {U : Array N | RegenAt p m U t d})
      = {U : Array N | RecordAt p m U t d ∧ pastProj p m t U ∈ A ∧
          relFuture p m U t d ∈ nonnegPath (N := N) ∩ univ} := by
    rw [← regenPast_set_eq p m t d A univ]
    ext U
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_univ, and_true]
    tauto
  rw [hset, freshlaw_past p m t d hA MeasurableSet.univ]
  rw [show {U : Array N | posPath p m U ∈ nonnegPath (N := N) ∩ univ} = seedSet p m N from by
    ext U; simp [seedSet]]

/-- Mass of "segment in `B` and a regeneration", factorised. -/
theorem measure_regen_inter_fut (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (arrayMeasure N) ((fun U : Array N => relFuture p m U t d) ⁻¹' B ∩
        {U : Array N | RegenAt p m U t d})
      = (arrayMeasure N) (recordSet (N := N) p m t d)
        * (arrayMeasure N) (seedSet p m N ∩ (fun U : Array N => posPath p m U) ⁻¹' B) := by
  have hset : ((fun U : Array N => relFuture p m U t d) ⁻¹' B ∩
      {U : Array N | RegenAt p m U t d})
      = {U : Array N | RecordAt p m U t d ∧ pastProj p m t U ∈ univ ∧
          relFuture p m U t d ∈ nonnegPath (N := N) ∩ B} := by
    rw [← regenPast_set_eq p m t d univ B]
    ext U
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_univ, true_and]
    tauto
  have hrec : recordPastSet (N := N) p m t d univ = recordSet (N := N) p m t d := by
    ext U; simp [recordPastSet, recordSet]
  have hseed : {U : Array N | posPath p m U ∈ nonnegPath (N := N) ∩ B}
      = seedSet p m N ∩ (fun U : Array N => posPath p m U) ⁻¹' B := by
    ext U; simp [seedSet]
  rw [hset, freshlaw_past p m t d MeasurableSet.univ hB, hrec, hseed]

/-- Mass of "past in `A`, segment in `B`, and a regeneration", factorised. -/
theorem measure_regen_inter_past_fut (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ)
    {A : Set (Fin (t + 1) → Fin N → ℤ)} (hA : MeasurableSet A)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (arrayMeasure N) ((fun U : Array N => pastProj p m t U) ⁻¹' A ∩
        (fun U : Array N => relFuture p m U t d) ⁻¹' B ∩ {U : Array N | RegenAt p m U t d})
      = (arrayMeasure N) (recordPastSet (N := N) p m t d A)
        * (arrayMeasure N) (seedSet p m N ∩ (fun U : Array N => posPath p m U) ⁻¹' B) := by
  have hset : ((fun U : Array N => pastProj p m t U) ⁻¹' A ∩
      (fun U : Array N => relFuture p m U t d) ⁻¹' B ∩ {U : Array N | RegenAt p m U t d})
      = {U : Array N | RecordAt p m U t d ∧ pastProj p m t U ∈ A ∧
          relFuture p m U t d ∈ nonnegPath (N := N) ∩ B} := by
    rw [← regenPast_set_eq p m t d A B]
    ext U
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
    tauto
  have hseed : {U : Array N | posPath p m U ∈ nonnegPath (N := N) ∩ B}
      = seedSet p m N ∩ (fun U : Array N => posPath p m U) ⁻¹' B := by
    ext U; simp [seedSet]
  rw [hset, freshlaw_past p m t d hA hB, hseed]

/-- **Conditional independence in unnormalised form**: multiplying by the mass of the
regeneration event turns the conditional-independence identity into a pure product identity. -/
theorem rect_unnorm (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ)
    {A : Set (Fin (t + 1) → Fin N → ℤ)} (hA : MeasurableSet A)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (arrayMeasure N) {U : Array N | RegenAt p m U t d}
        * (arrayMeasure N) ((fun U : Array N => pastProj p m t U) ⁻¹' A ∩
          (fun U : Array N => relFuture p m U t d) ⁻¹' B ∩ {U : Array N | RegenAt p m U t d})
      = (arrayMeasure N) ((fun U : Array N => pastProj p m t U) ⁻¹' A ∩
          {U : Array N | RegenAt p m U t d})
        * (arrayMeasure N) ((fun U : Array N => relFuture p m U t d) ⁻¹' B ∩
          {U : Array N | RegenAt p m U t d}) := by
  rw [measure_regen_inter_past_fut p m t d hA hB, measure_regen_inter_past p m t d hA,
    measure_regen_inter_fut p m t d hB, regenAt_measure_factor (N := N) p m t d]
  ac_rfl

/-- **The post-regeneration segment is independent of the entire past path** (Mathlib's
`IndepFun` form), under the law conditioned on a regeneration at `(t,d)`. -/
theorem indepFun_past_relFuture (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ)
    (hreg : (arrayMeasure N) {U : Array N | RegenAt p m U t d} ≠ 0) :
    IndepFun (fun U : Array N => pastProj p m t U) (fun U : Array N => relFuture p m U t d)
      (((arrayMeasure N) {U : Array N | RegenAt p m U t d})⁻¹ •
        Measure.restrict (arrayMeasure N) {U : Array N | RegenAt p m U t d}) := by
  set c := (arrayMeasure N) {U : Array N | RegenAt p m U t d} with hc
  have hctop : c ≠ ⊤ := measure_ne_top _ _
  have hc0 : c ≠ 0 := hreg
  refine indepFun_iff_measure_inter_preimage_eq_mul.mpr ?_
  intro A B hA hB
  have hXY := rect_unnorm p m t d hA hB
  have e1 : ((c⁻¹ • Measure.restrict (arrayMeasure N) {U : Array N | RegenAt p m U t d})
        ((fun U : Array N => pastProj p m t U) ⁻¹' A ∩
          (fun U : Array N => relFuture p m U t d) ⁻¹' B))
      = c⁻¹ * (arrayMeasure N) ((fun U : Array N => pastProj p m t U) ⁻¹' A ∩
          (fun U : Array N => relFuture p m U t d) ⁻¹' B ∩ {U : Array N | RegenAt p m U t d}) :=
    cond_apply (hA.preimage (measurable_pastProj p m t N) |>.inter
      (hB.preimage (measurable_relFuture p m t d N)))
  have e2 : ((c⁻¹ • Measure.restrict (arrayMeasure N) {U : Array N | RegenAt p m U t d})
        ((fun U : Array N => pastProj p m t U) ⁻¹' A))
      = c⁻¹ * (arrayMeasure N) ((fun U : Array N => pastProj p m t U) ⁻¹' A ∩
          {U : Array N | RegenAt p m U t d}) :=
    cond_apply ((measurable_pastProj p m t N) hA)
  have e3 : ((c⁻¹ • Measure.restrict (arrayMeasure N) {U : Array N | RegenAt p m U t d})
        ((fun U : Array N => relFuture p m U t d) ⁻¹' B))
      = c⁻¹ * (arrayMeasure N) ((fun U : Array N => relFuture p m U t d) ⁻¹' B ∩
          {U : Array N | RegenAt p m U t d}) :=
    cond_apply ((measurable_relFuture p m t d N) hB)
  rw [e1, e2, e3]
  have hZ : (arrayMeasure N) ((fun U : Array N => pastProj p m t U) ⁻¹' A ∩
        (fun U : Array N => relFuture p m U t d) ⁻¹' B ∩ {U : Array N | RegenAt p m U t d})
      = c⁻¹ * ((arrayMeasure N) ((fun U : Array N => pastProj p m t U) ⁻¹' A ∩
            {U : Array N | RegenAt p m U t d})
          * (arrayMeasure N) ((fun U : Array N => relFuture p m U t d) ⁻¹' B ∩
            {U : Array N | RegenAt p m U t d})) := by
    rw [← hXY, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, one_mul]
  rw [hZ]
  ac_rfl

end SwarmSeg
