/-
# `(locgroup)` at the literal actual record clock -- no union over clock values

## The gap being attacked

`LocGroupSimul.exists_locgroup_record_window` proves the paper's display `(locgroup)` at a
**deterministic** clock `n0`, under the paper's own record hypothesis `RecHyp p m r n0 L`
(`{d_r <= L}` at `n0` plus "every running record is at most `r`").  The display of
Proposition `local` is stated instead at the *random* record time `n0 = tau_r(U)`.
Substituting `n0 = tau_r` in a deterministic-clock estimate is not permitted: the bad set is
indexed by the clock, so the naive route costs one factor per candidate clock and there is no
bound on the number of candidate clocks (`tau_r` is unbounded on `ReachAll`).  This is the
record-time truncation / clock-uniformity gap.

## What this file does

The truncation is removed by the exact-adapted-fibre method, with **no union over clocks**:

* `recordCarrier`, `recordBand` -- the genuine first-passage fibres `{tau_r = a}` cut by the
  paper's defect carrier `{d_r <= L}`.  `recordBand a` is `posFilt a`-measurable (adapted, not
  merely `enlFilt`-measurable: only positions up to time `a` occur), the family is *pairwise
  disjoint*, and it covers the carrier.  On the carrier, `recordBand (sigma U)` contains `U`
  and `sigma` reads off the band index -- so the weight `1_{recordBand a}` sums to `<= 1`.
* `recHyp_at_record` -- the deterministic-clock hypothesis `RecHyp` of `winTrunc_of_record` is
  *derived* at `a = tau_r` from the carrier: nothing is assumed.
* `dQtr`, `Qtr` -- the windowed `(locgroup)` martingale of `WinTrunc` as a single global
  martingale on `posFilt`, with a **pointwise** increment envelope: `dQtr` is `dQTW` truncated
  at the a.e. envelope `2 * stepEnv`.  Truncation is legitimate because `dQtr t = dQTW t`
  almost surely for each `t` (so the martingale-difference property survives) and the two
  processes differ only on a null set for *all* `t` at once.
* `measureReal_recordClock_groupDev_le` -- the count-free stopped maximal bound at the random
  clock: the deviation of `Qtr` from its value at `sigma = tau_r` over every window of length
  `<= T*L`, measured by *band masses charged once*.
* `measureReal_recordClock_locgroup_le` -- the paper's display `(locgroup)` at `tau_r` itself:
  the set of trajectories on which the carrier holds, `(locmax)` and the a.e. inputs hold, and
  yet some window `[s,t) ⊆ [tau_r, tau_r + T*L]` with `(sep)` on `[s,t)` has
  `W_t - W_s > L^{3/4}`, has `arrayMeasure`-measure at most `C_T exp (-c_T * xOf L)`.
  No union over clock values, no stationarity, no independence of the future, no truncation.

Not claimed here: `(lococc)`, `(loccoord)`, `(locmove)`, the survival of `(sep)`, the halving /
lag input, `MainClaim`, or any velocity statement.  `(sep)` on `[s,t)` and the carrier
`{d_r <= L}` remain the paper's own hypotheses, exactly as in Proposition `local`.
-/
import Swarm.StoppedMartingaleWindow
import Swarm.LocGroupSimultaneous
import Swarm.ActualRecordFiltration
import Swarm.RecordMeas
import Swarm.ActualRecordGeometry

noncomputable section

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance LocGroupQ
open SwarmMarks SwarmLogRatio LocSumAct LocSumR1
open RecordDefect RecordoSupply SwarmRecordMeas SwarmRecordMeas.Actual
open ActualRecordFiltration LocGroupSimul

namespace RecClockLG

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. The record clock as an adapted band family -/

/-- The swarm's running spatial maximum `M_n = max_i X_n^i` of the actual trajectory. -/
noncomputable def maxtraj (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) : ℤ :=
  runMax (actX p m U) n

/-- The paper's defect carrier `{d_r <= L}` at the record clock `tau_r`, written as
`r - min_i X^i_{tau_r} <= L` (definitionally `RecordDefect.defect`). -/
def recordCarrier (p : ℝ) (m : ℕ) (r L : ℕ) : Set (Array N) :=
  ReachAll (N := N) p m ∩
    {U : Array N | ((r : ℤ) - runMin (actX p m U) (recTimeA p m U r)).toNat ≤ L}

/-- The record band: the exact first-passage fibre `{tau_r = a}` cut by the defect carrier.

It is written out in terms of the band index `a` only (no occurrence of the clock `recTimeA`), so
that every clause is a statement about the finite position prefix up to time `a`; on the
reachable set it is exactly `recordPrefixBand p m r a L`. -/
def recordBand (p : ℝ) (m : ℕ) (r L a : ℕ) : Set (Array N) :=
  {U : Array N | runMax (actX p m U) a = (r : ℤ) ∧
    (∀ t : ℕ, t < a → runMax (actX p m U) t ≠ (r : ℤ)) ∧
    ((r : ℤ) - runMin (actX p m U) a).toNat ≤ L}

/-- Adapted measurability of the running spatial maximum, in the position filtration. -/
theorem measurable_maxtraj_posFilt (p : ℝ) (m : ℕ) {n n0 : ℕ} (hn : n ≤ n0) :
    Measurable[posFilt N p m n0] (fun U : Array N => maxtraj p m U n) :=
  @SwarmRecordMeas.measurable_runMax (Array N) (posFilt N p m n0) (Fin N) _ _
    (fun i (U : Array N) => actX p m U i n)
    (fun i => (Swarming.Trajectory.measurable_pos_posFilt p m i hn).stronglyMeasurable.measurable)
    n

/-- Adapted measurability of the running spatial minimum, in the position filtration. -/
theorem measurable_mintraj_posFilt (p : ℝ) (m : ℕ) {n n0 : ℕ} (hn : n ≤ n0) :
    Measurable[posFilt N p m n0] (fun U : Array N => runMin (actX p m U) n) :=
  @SwarmRecordMeas.measurable_runMin (Array N) (posFilt N p m n0) (Fin N) _ _
    (fun i (U : Array N) => actX p m U i n)
    (fun i => (Swarming.Trajectory.measurable_pos_posFilt p m i hn).stronglyMeasurable.measurable)
    n

/-- **The first-passage fibre is adapted in the position filtration.** -/
theorem measurableSet_firstRecordAt_posFilt (p : ℝ) (m : ℕ) (r s : ℕ) :
    MeasurableSet[posFilt N p m s] (firstRecordAt (N := N) p m r s) := by
  have heq : firstRecordAt (N := N) p m r s =
      {U : Array N | runMax (actX p m U) s = (r : ℤ)} ∩
        ⋂ t ∈ Finset.range s, {U : Array N | runMax (actX p m U) t ≠ (r : ℤ)} := by
    ext U
    simp only [firstRecordAt, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
      Finset.mem_range]
  rw [heq]
  refine ((measurable_maxtraj_posFilt p m (le_refl s))
    (measurableSet_singleton (r : ℤ))).inter ?_
  refine MeasurableSet.biInter (Finset.countable_toSet _) fun t ht => ?_
  exact ((measurable_maxtraj_posFilt p m (Nat.le_of_lt (Finset.mem_range.1 ht)))
    (measurableSet_singleton (r : ℤ))).compl

/-- **The record band (fibre with defect carrier) is adapted in the position filtration.** -/
theorem measurableSet_recordBand (p : ℝ) (m : ℕ) (r L s : ℕ) :
    MeasurableSet[posFilt N p m s] (recordBand (N := N) p m r L s) := by
  have h1 : MeasurableSet[posFilt N p m s] {U : Array N | runMax (actX p m U) s = (r : ℤ)} :=
    (measurable_maxtraj_posFilt p m (le_refl s)) (measurableSet_singleton (r : ℤ))
  have h2 : MeasurableSet[posFilt N p m s]
      {U : Array N | ∀ t : ℕ, t < s → runMax (actX p m U) t ≠ (r : ℤ)} := by
    rw [show {U : Array N | ∀ t : ℕ, t < s → runMax (actX p m U) t ≠ (r : ℤ)}
        = ⋂ t ∈ Finset.range s, {U : Array N | runMax (actX p m U) t ≠ (r : ℤ)} by
      ext U
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range]]
    refine MeasurableSet.biInter (Finset.countable_toSet _) fun t ht => ?_
    exact ((measurable_maxtraj_posFilt p m (Nat.le_of_lt (Finset.mem_range.1 ht)))
      (measurableSet_singleton (r : ℤ))).compl
  have h3 : MeasurableSet[posFilt N p m s]
      {U : Array N | ((r : ℤ) - runMin (actX p m U) s).toNat ≤ L} := by
    refine measurableSet_le ?_ measurable_const
    exact measurable_toNat_of_measurable
      (measurable_const.sub (measurable_mintraj_posFilt p m (le_refl s)))
  exact h1.inter (h2.inter h3)

/-- On the reachable set the explicit band is the public band `recordPrefixBand`. -/
theorem recordBand_eq_recordPrefixBand (p : ℝ) (m : ℕ) (r L s : ℕ) :
    recordBand (N := N) p m r L s = recordPrefixBand (N := N) p m r s L := by
  ext U
  simp only [recordBand, recordPrefixBand, firstRecordAt, Set.mem_ofPred_eq,
    Set.mem_inter_iff]
  tauto

/-- Different band indices give disjoint bands. -/
theorem disjoint_recordBand {p : ℝ} {m r L a b : ℕ} (hab : a ≠ b) :
    Disjoint (recordBand (N := N) p m r L a) (recordBand (N := N) p m r L b) := by
  rw [Set.disjoint_left]
  intro U ha hb
  simp only [recordBand, Set.mem_ofPred_eq] at ha hb
  rcases lt_or_gt_of_ne hab with h | h
  · exact (hb.2.1 a h) ha.1
  · exact (ha.2.1 b h) hb.1

/-- On the reachable part of a band, the record clock *is* the band index. -/
theorem recTimeA_eq_of_mem_band {p : ℝ} {m r L a : ℕ} {U : Array N}
    (hreach : U ∈ ReachAll (N := N) p m)
    (hU : U ∈ recordBand (N := N) p m r L a) : recTimeA p m U r = a := by
  obtain ⟨h1, h2, -⟩ : runMax (actX p m U) a = (r : ℤ) ∧
      (∀ t : ℕ, t < a → runMax (actX p m U) t ≠ (r : ℤ)) ∧
      ((r : ℤ) - runMin (actX p m U) a).toNat ≤ L := hU
  exact (recTimeA_eq_iff p m U r a hreach).2 ⟨h1, h2⟩

/-- The carrier is covered by the record bands. -/
theorem subset_iUnion_recordBand (p : ℝ) (m : ℕ) (r L : ℕ) :
    recordCarrier (N := N) p m r L ⊆ ⋃ a, recordBand (N := N) p m r L a := by
  intro U hU
  obtain ⟨hreach, hband⟩ := hU
  have hspec : runMax (actX p m U) (recTimeA p m U r) = (r : ℤ) :=
    (recTimeA_spec p m U r).resolve_left (fun hc => hc hreach)
  have hmin : ∀ t : ℕ, t < recTimeA p m U r → runMax (actX p m U) t ≠ (r : ℤ) := by
    intro t ht hEq
    exact recTimeA_min p m U r t ht (Or.inr hEq)
  refine Set.mem_iUnion.2 ⟨recTimeA p m U r, ?_⟩
  exact ⟨hspec, hmin, hband⟩

/-- The carrier refines the fibre of the clock: on the carrier intersected with a band, the
clock equals the band index.  This is the exact weight identity that replaces the union over
clock values. -/
theorem carrier_inter_band_subset_clock_eq (p : ℝ) (m : ℕ) (r L a : ℕ) :
    recordCarrier (N := N) p m r L ∩ recordBand (N := N) p m r L a
      ⊆ {U : Array N | recTimeA p m U r = a} := by
  rintro U ⟨⟨hreach, -⟩, hU⟩
  exact recTimeA_eq_of_mem_band hreach hU

/-! ## 2. The deterministic-clock record hypothesis, derived at the record clock -/

/-- **`RecHyp` at the record clock, from the defect carrier.**  On `{d_r <= L}` the paper's
record localisation holds at the *actual* record time: every position is at least `r - L` and
every running record is at most `r`.  The deterministic-clock hypothesis of
`LocGroupSimul.winTrunc_of_record` is therefore derived, not assumed. -/
theorem recHyp_at_record {p : ℝ} {m r L : ℕ} {U : Array N}
    (hU : U ∈ recordCarrier (N := N) p m r L) :
    LocGroupSimul.RecHyp p m r (recTimeA p m U r) L U := by
  obtain ⟨hreach, hband⟩ := hU
  have hτ : IsRecord (actX p m U) (recTimeA p m U) :=
    isRecord_recTimeA p m U (fun r' => hreach r')
  have hspec : runMax (actX p m U) (recTimeA p m U r) = (r : ℤ) := (hτ r).2
  have hnonneg : (0 : ℤ) ≤ (r : ℤ) - runMin (actX p m U) (recTimeA p m U r) := by
    rw [← hspec]
    linarith [runMin_le_runMax (X := actX p m U) (recTimeA p m U r)]
  have hcast : (r : ℤ) - runMin (actX p m U) (recTimeA p m U r) ≤ (L : ℤ) := by
    have h2 : (((r : ℤ) - runMin (actX p m U) (recTimeA p m U r)).toNat : ℤ)
        = (r : ℤ) - runMin (actX p m U) (recTimeA p m U r) := Int.toNat_of_nonneg hnonneg
    have h1 : (((r : ℤ) - runMin (actX p m U) (recTimeA p m U r)).toNat : ℤ) ≤ (L : ℤ) := by
      exact_mod_cast hband
    rw [h2] at h1
    exact h1
  constructor
  · -- every position at the record time is at least `r - L`
    intro i
    have h1 : runMin (actX p m U) (recTimeA p m U r)
        ≤ (trajectory p m U (recTimeA p m U r)).pos i := runMin_le _ i
    have h2 : (r : ℤ) - (L : ℤ)
        ≤ runMin (actX p m U) (recTimeA p m U r) := by linarith
    linarith
  · -- every *per-walker* running record up to the record time is at most `r`
    intro k
    refine Finset.sup'_le _ _ fun t ht => ?_
    rw [Finset.mem_range] at ht
    have hb : (trajectory p m U t).pos k ≤ runMax (actX p m U) t :=
      le_runMax (X := actX p m U) t k
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp ht) with hlt | heq
    · have h1 : runMax (actX p m U) t < (r : ℤ) := (hτ r).1 t hlt
      linarith
    · rw [heq] at hb ⊢
      rw [hspec] at hb
      exact hb


/-! ## 3. The windowed `(locgroup)` martingale as a single global martingale

`WinTrunc.dQTW` is centred with respect to `posFilt t` but is only `posFilt (t+1)`-measurable, and
its envelope `2 * stepEnv p B` holds only almost surely.  For a *pointwise* increment bound at the
random clock we truncate it at the envelope.  This is legitimate: for each `t` the truncated and
untruncated increments agree almost surely, so the martingale-difference property survives
(`condExp_dQtr`), and the two partial-sum processes differ only on the null set where the envelope
fails for some `t` (`goodSet`). -/

/-- The windowed `(locgroup)` increment, truncated at its a.e. envelope `2 * stepEnv p B`. -/
noncomputable def dQtr (p : ℝ) (m : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty)
    (hJ : J.Nonempty) (B : ℝ) (A : ℕ) (t : ℕ) (U : Array N) : ℝ :=
  if |dQTW p m t I J hI hJ B A U| ≤ 2 * LocGroupWindow.stepEnv (N := N) p B
    then dQTW p m t I J hI hJ B A U else 0

/-- The truncated increment is adapted one step ahead, in the position filtration. -/
theorem stronglyMeasurable_dQtr (p : ℝ) (m : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty)
    (hJ : J.Nonempty) (B : ℝ) (A : ℕ) (t : ℕ) :
    StronglyMeasurable[posFilt N p m (t + 1)] (dQtr p m I J hI hJ B A t) := by
  letI : MeasurableSpace (Array N) := posFilt N p m (t + 1)
  have hmeas : Measurable (dQTW p m t I J hI hJ B A) :=
    (stronglyMeasurable_dQTW p m t I J hI hJ B A).measurable
  have hset : MeasurableSet
      {U : Array N | |dQTW p m t I J hI hJ B A U| ≤ 2 * LocGroupWindow.stepEnv (N := N) p B} :=
    measurableSet_le hmeas.abs measurable_const
  exact (Measurable.ite hset hmeas measurable_const).stronglyMeasurable

/-- **The truncated increment is bounded pointwise**, everywhere, by the envelope. -/
theorem abs_dQtr_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p ≤ 1) {m : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) {B : ℝ} (hB : 0 ≤ B)
    (A : ℕ) (t : ℕ) (U : Array N) :
    |dQtr p m I J hI hJ B A t U| ≤ 2 * LocGroupWindow.stepEnv (N := N) p B := by
  have hE0 : 0 ≤ LocGroupWindow.stepEnv (N := N) p B :=
    LocGroupWindow.stepEnv_nonneg hp0 hp1 hB
  unfold dQtr
  split_ifs with h
  · exact h
  · rw [abs_zero]; linarith

/-- The truncated increment agrees almost surely with the windowed martingale difference. -/
theorem ae_dQtr_eq {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p ≤ 1) {m : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {B : ℝ} (hB : 0 ≤ B) (A : ℕ) (t : ℕ) :
    dQtr p m I J hI hJ B A t =ᵐ[arrayMeasure N] dQTW p m t I J hI hJ B A := by
  filter_upwards [ae_abs_dQTW_le (N := N) hp0 hp1 I J hI hJ hid hB (A := A) (n := t)]
    with U hU
  unfold dQtr
  rw [if_pos hU]

/-- The truncated increment is integrable. -/
theorem integrable_dQtr {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p ≤ 1) {m : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {B : ℝ} (hB : 0 ≤ B) (A : ℕ) (t : ℕ) :
    Integrable (dQtr p m I J hI hJ B A t) (arrayMeasure N) :=
  (integrable_dQTW (N := N) hp0.le hp1 m t I J hI hJ B A).congr
    (ae_dQtr_eq hp0 hp1 I J hI hJ hid hB A t).symm

/-- **The truncated increment is a `posFilt`-martingale difference.** -/
theorem condExp_dQtr {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p ≤ 1) {m : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {B : ℝ} (hB : 0 ≤ B) (A : ℕ) (t : ℕ) :
    (arrayMeasure N)[dQtr p m I J hI hJ B A t | posFilt N p m t] =ᵐ[arrayMeasure N] 0 :=
  (condExp_congr_ae (ae_dQtr_eq hp0 hp1 I J hI hJ hid hB A t)).trans
    (condExp_dQTW hp0.le hp1 m t I J hI hJ B A)

/-- The global windowed `(locgroup)` martingale: partial sums of the truncated increments. -/
noncomputable def Qtr (p : ℝ) (m : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty)
    (hJ : J.Nonempty) (B : ℝ) (A : ℕ) (t : ℕ) (U : Array N) : ℝ :=
  LocMart.psum (fun j => dQtr p m I J hI hJ B A j) t U

theorem Qtr_succ (p : ℝ) (m : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty)
    (hJ : J.Nonempty) (B : ℝ) (A : ℕ) (t : ℕ) (U : Array N) :
    Qtr p m I J hI hJ B A (t + 1) U
      = Qtr p m I J hI hJ B A t U + dQtr p m I J hI hJ B A t U :=
  LocMart.psum_succ _ t U

/-- `Qtr` is adapted to the position filtration. -/
theorem stronglyMeasurable_Qtr (p : ℝ) (m : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty)
    (hJ : J.Nonempty) (B : ℝ) (A : ℕ) (t : ℕ) :
    StronglyMeasurable[posFilt N p m t] (Qtr p m I J hI hJ B A t) :=
  LocMart.stronglyMeasurable_psum (ℱ := posFilt N p m)
    (fun k => stronglyMeasurable_dQtr p m I J hI hJ B A k) t

/-- `Qtr` is integrable at every time. -/
theorem integrable_Qtr {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p ≤ 1) {m : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {B : ℝ} (hB : 0 ≤ B) (A : ℕ) (t : ℕ) :
    Integrable (Qtr p m I J hI hJ B A t) (arrayMeasure N) := by
  induction t with
  | zero =>
      have h0 : Qtr p m I J hI hJ B A 0 = fun _ => (0 : ℝ) := LocMart.psum_zero _
      rw [h0]
      exact integrable_const 0
  | succ t ih =>
      have hgoal : Qtr p m I J hI hJ B A (t + 1)
          = fun U => Qtr p m I J hI hJ B A t U + dQtr p m I J hI hJ B A t U := by
        funext U
        exact Qtr_succ p m I J hI hJ B A t U
      rw [hgoal]
      exact ih.add (integrable_dQtr hp0 hp1 I J hI hJ hid hB A t)

/-- The increments of `Qtr` are the truncated windowed increments. -/
theorem increments_Qtr (p : ℝ) (m : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty)
    (hJ : J.Nonempty) (B : ℝ) (A : ℕ) (t : ℕ) :
    StoppedWindow.increments (Qtr p m I J hI hJ B A) t = dQtr p m I J hI hJ B A t := by
  funext U
  rw [StoppedWindow.increments, Qtr_succ]
  ring

/-- The conditional means of the increments of `Qtr` vanish. -/
theorem condExp_increments_Qtr {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p ≤ 1) {m : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {B : ℝ} (hB : 0 ≤ B) (A : ℕ) (t : ℕ) :
    (arrayMeasure N)[StoppedWindow.increments (Qtr p m I J hI hJ B A) t
      | posFilt N p m t] =ᵐ[arrayMeasure N] 0 := by
  rw [increments_Qtr]
  exact condExp_dQtr hp0 hp1 I J hI hJ hid hB A t

/-! ## 4. The count-free stopped maximal bound at the literal record clock

The random clock enters only through the adapted disjoint band family `recordBand`; the mass of
each band is charged exactly once.  There is no union over the values of the clock. -/

/-- **The increments of `Qtr` obey the envelope pointwise**, everywhere. -/
theorem abs_increments_Qtr {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p ≤ 1) {m : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {B : ℝ} (hB : 0 ≤ B) (A : ℕ) (t : ℕ) (U : Array N) :
    |Qtr p m I J hI hJ B A (t + 1) U - Qtr p m I J hI hJ B A t U|
      ≤ 2 * LocGroupWindow.stepEnv (N := N) p B := by
  have hdiff : Qtr p m I J hI hJ B A (t + 1) U - Qtr p m I J hI hJ B A t U
      = dQtr p m I J hI hJ B A t U := by
    rw [Qtr_succ]; ring
  rw [hdiff]
  exact abs_dQtr_le hp0 hp1 I J hI hJ hB A t U

/-- **Count-free maximal deviation bound at the actual record clock.** -/
theorem measureReal_recordClock_groupDev_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {B : ℝ} (hB : 0 < B) (A : ℕ) (r L : ℕ) {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    (arrayMeasure N).real
        (recordCarrier (N := N) p m r L ∩
          StoppedWindow.stoppedMax (Qtr p m I J hI hJ B A)
            (fun U : Array N => recTimeA p m U r) n ε)
      ≤ 2 * ((n : ℝ) + 1) *
          Real.exp (-(ε ^ 2) /
            (4 * (n : ℝ) * (2 * LocGroupWindow.stepEnv (N := N) p B) ^ 2)) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hEpos : 0 < LocGroupWindow.stepEnv (N := N) p B :=
    LocGroupWindow.stepEnv_pos (N := N) hp0 hp1.le hB
  have hC : (0 : ℝ) < 2 * LocGroupWindow.stepEnv (N := N) p B := by linarith
  exact StoppedWindow.measureReal_band_stoppedMax_le
    (μ := arrayMeasure N) (ℱ := posFilt N p m)
    (Q := Qtr p m I J hI hJ B A) (σ := fun U : Array N => recTimeA p m U r)
    (B := fun a => recordBand (N := N) p m r L a)
    (G := recordCarrier (N := N) p m r L)
    (fun t => stronglyMeasurable_Qtr p m I J hI hJ B A t)
    (fun t => integrable_Qtr hp0 hp1.le I J hI hJ hid hB.le A t)
    (fun t => condExp_increments_Qtr hp0 hp1.le I J hI hJ hid hB.le A t)
    hC (fun t U => abs_increments_Qtr hp0 hp1.le I J hI hJ hid hB.le A t U)
    (fun a => measurableSet_recordBand p m r L a)
    (fun a b hab => disjoint_recordBand hab)
    (subset_iUnion_recordBand p m r L)
    (fun a => carrier_inter_band_subset_clock_eq p m r L a) hn hε


/-! ## 5. The scale of the record window -/

/-- The common level of the windowed envelopes at the record scale. -/
noncomputable def Bstar (L : ℕ) : ℝ := max (2 * xOf L + 6) (2 * (xOf L + 1))

/-- The left edge of the `(locgroup)` level window at the record scale. -/
def Astar (r T L : ℕ) : ℕ := r - ((T + 2) * L + 1)

/-- `Bstar` is the truncation level `2 L^{1/16} + 6`. -/
theorem Bstar_eq_truncLevel {L : ℕ} (hL : 1 ≤ L) :
    Bstar L = LocScaleArithmetic.truncLevel (L : ℝ) := by
  rw [Bstar, LocScaleArithmetic.truncLevel, LocSumAct.xOf]
  have hLr : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have h2 : (1 : ℝ) ≤ (L : ℝ) ^ ((1 : ℝ) / 16) := Real.one_le_rpow hLr (by norm_num)
  have h1 : 2 * (L : ℝ) ^ ((1 : ℝ) / 16) ≤ 2 * (L : ℝ) ^ ((1 : ℝ) / 16) + 6 := by linarith
  have h1' : 2 * ((L : ℝ) ^ ((1 : ℝ) / 16) + 1) ≤ 2 * (L : ℝ) ^ ((1 : ℝ) / 16) + 6 := by
    linarith
  rw [max_eq_left h1, max_eq_left h1']

theorem Bstar_pos {L : ℕ} (hL : 1 ≤ L) : 0 < Bstar L := by
  rw [Bstar_eq_truncLevel hL, LocScaleArithmetic.truncLevel_eq (by exact_mod_cast hL :
    (1 : ℝ) ≤ (L : ℝ))]
  have h2 : (0 : ℝ) < (L : ℝ) ^ ((1 : ℝ) / 16) :=
    Real.rpow_pos_of_pos (by linarith [show (1:ℝ) ≤ (L:ℝ) by exact_mod_cast hL]) _
  linarith

theorem Bstar_nonneg {L : ℕ} (hL : 1 ≤ L) : 0 ≤ Bstar L := (Bstar_pos hL).le

/-! ## 6. The a.e. inputs of the bridge -/

/-- The three almost-sure inputs of the record-clock `(locgroup)` bridge: the truncation never
bites (all times at once), the forward potential truncations are bounded above at every site, and
the paper's chaining inequality `W_t - W_s ≤ |psum_t| + |psum_s|` holds for every window. -/
def goodSet (p : ℝ) (m : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty)
    (B : ℝ) (A : ℕ) : Set (Array N) :=
  {U : Array N |
    (∀ t : ℕ, dQtr p m I J hI hJ B A t U = dQTW p m t I J hI hJ B A U) ∧
    (∀ j : Fin N, ∀ u : ℕ,
      BddAbove (Set.range fun n' => Gtrunc p (siteMarks p m U j) n' (u + 1))) ∧
    (∀ (n0 s t K : ℕ), n0 ≤ s → s ≤ t → t ≤ n0 + K →
      (∀ k, s ≤ k → k < t → winTrunc p m k I J hI B A U) →
      WA p m U t I J hI hJ - WA p m U s I J hI hJ
        ≤ |LocMart.psum (fun j => dQTW p m (n0 + j) I J hI hJ B A) (t - n0) U|
          + |LocMart.psum (fun j => dQTW p m (n0 + j) I J hI hJ B A) (s - n0) U|)}

/-- **The good set is conull.**  No new probabilistic input: this is the a.e. envelope of
`WinTrunc.ae_abs_dQTW_le` (for all `t` at once), the a.e. bound of the forward potential
(`LocGroupSimul.ae_bddAbove_Gtrunc_arrayMeasure`) and the a.e. chaining inequality
(`WinTrunc.WA_sub_le_psum_abs`). -/
theorem measureReal_goodSet_compl {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty)
    (hid : Disjoint I J) {B : ℝ} (hB : 0 ≤ B) (A : ℕ) :
    (arrayMeasure N).real (goodSet (N := N) p m I J hI hJ B A)ᶜ = 0 := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  -- (1) the truncation never bites, for all `t` at once
  have h1 : (arrayMeasure N)
      {U : Array N | ¬ ∀ t : ℕ, dQtr p m I J hI hJ B A t U = dQTW p m t I J hI hJ B A U} = 0 := by
    have hsingle : ∀ t : ℕ,
        (arrayMeasure N) {U : Array N | dQtr p m I J hI hJ B A t U
          ≠ dQTW p m t I J hI hJ B A U} = 0 := by
      intro t
      have h := ae_dQtr_eq (m := m) hp0 hp1.le I J hI hJ hid hB A t
      rw [Filter.EventuallyEq, ae_iff] at h
      simpa only [ne_eq] using h
    have hunion : {U : Array N | ¬ ∀ t : ℕ,
          dQtr p m I J hI hJ B A t U = dQTW p m t I J hI hJ B A U}
        = ⋃ t : ℕ, {U : Array N | dQtr p m I J hI hJ B A t U
            ≠ dQTW p m t I J hI hJ B A U} := by
      ext U
      simp only [Set.mem_ofPred_eq, not_forall, Set.mem_iUnion, ne_eq]
    rw [hunion]
    exact measure_iUnion_null hsingle
  -- (2) the forward potential is a.e. bounded above
  have h2 : (arrayMeasure N) {U : Array N | ¬ (∀ j : Fin N, ∀ u : ℕ,
      BddAbove (Set.range fun n' => Gtrunc p (siteMarks p m U j) n' (u + 1)))} = 0 :=
    ae_iff.mp (ae_bddAbove_Gtrunc_arrayMeasure (N := N) hp0 hp1 hm)
  -- (3) the chaining inequality
  have h3 : (arrayMeasure N) {U : Array N | ¬ (∀ (n0 s t K : ℕ), n0 ≤ s → s ≤ t → t ≤ n0 + K →
      (∀ k, s ≤ k → k < t → winTrunc p m k I J hI B A U) →
      WA p m U t I J hI hJ - WA p m U s I J hI hJ
        ≤ |LocMart.psum (fun j => dQTW p m (n0 + j) I J hI hJ B A) (t - n0) U|
          + |LocMart.psum (fun j => dQTW p m (n0 + j) I J hI hJ B A) (s - n0) U|)} = 0 :=
    ae_iff.mp (WA_sub_le_psum_abs (N := N) hp0 hp1 I J hI hJ hid B A)
  -- the union of the three null sets contains the complement
  have hsub : (goodSet (N := N) p m I J hI hJ B A)ᶜ ⊆
      {U : Array N | ¬ ∀ t : ℕ, dQtr p m I J hI hJ B A t U = dQTW p m t I J hI hJ B A U}
      ∪ {U : Array N | ¬ (∀ j : Fin N, ∀ u : ℕ,
          BddAbove (Set.range fun n' => Gtrunc p (siteMarks p m U j) n' (u + 1)))}
      ∪ {U : Array N | ¬ (∀ (n0 s t K : ℕ), n0 ≤ s → s ≤ t → t ≤ n0 + K →
          (∀ k, s ≤ k → k < t → winTrunc p m k I J hI B A U) →
          WA p m U t I J hI hJ - WA p m U s I J hI hJ
            ≤ abs (LocMart.psum (fun j => dQTW p m (n0 + j) I J hI hJ B A) (t - n0) U)
              + abs (LocMart.psum (fun j => dQTW p m (n0 + j) I J hI hJ B A) (s - n0) U))} := by
    intro U hU
    simp only [goodSet, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and_or] at hU
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    tauto
  have h0 : (arrayMeasure N)
      ({U : Array N | ¬ ∀ t : ℕ, dQtr p m I J hI hJ B A t U = dQTW p m t I J hI hJ B A U}
      ∪ {U : Array N | ¬ (∀ j : Fin N, ∀ u : ℕ,
          BddAbove (Set.range fun n' => Gtrunc p (siteMarks p m U j) n' (u + 1)))}
      ∪ {U : Array N | ¬ (∀ (n0 s t K : ℕ), n0 ≤ s → s ≤ t → t ≤ n0 + K →
          (∀ k, s ≤ k → k < t → winTrunc p m k I J hI B A U) →
          WA p m U t I J hI hJ - WA p m U s I J hI hJ
            ≤ abs (LocMart.psum (fun j => dQTW p m (n0 + j) I J hI hJ B A) (t - n0) U)
              + abs (LocMart.psum (fun j => dQTW p m (n0 + j) I J hI hJ B A) (s - n0) U))})
      = 0 := by
    exact measure_union_null (measure_union_null h1 h2) h3
  have hnull := measure_mono_null hsub h0
  rw [measureReal_def, hnull, ENNReal.toReal_zero]


/-! ## 7. The bridge: a display failure is a clock-relative deviation -/

/-- **A failure of the display `(locgroup)` at the record clock forces a deviation of the
windowed martingale measured from the record clock.**  The chaining inequality
`WA_sub_le_psum_abs` writes `W_t - W_s` as the sum of the two partial sums measured from the start
of the window, and each partial sum is a one-start deviation from the clock value. -/
theorem dev_of_displayFailure {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {T : ℕ} (hT : 1 ≤ T) {L : ℕ} (hL : 2 ≤ L) {r : ℕ} (hr : (T + 3) * L ≤ r)
    {U : Array N} (hcarr : U ∈ recordCarrier (N := N) p m r L)
    (hgood : U ∈ goodSet (N := N) p m I J hI hJ (Bstar L) (Astar r T L))
    (hlm : U ∉ LocMaxBad (N := N) p m r T L)
    (hdisp : ∃ s t : ℕ, recTimeA p m U r ≤ s ∧ s ≤ t ∧ t ≤ recTimeA p m U r + T * L ∧
      (∀ u ∈ Finset.Ico s t, SepSet p m u I J U) ∧
      (L : ℝ) ^ ((3 : ℝ) / 4) < WA p m U t I J hI hJ - WA p m U s I J hI hJ) :
    U ∈ StoppedWindow.stoppedMax (Qtr p m I J hI hJ (Bstar L) (Astar r T L))
      (fun U : Array N => recTimeA p m U r) (T * L) ((L : ℝ) ^ ((3 : ℝ) / 4) / 2) := by
  simp only [goodSet, Set.mem_ofPred_eq] at hgood
  obtain ⟨hgood1, hgood2, hgood3⟩ := hgood
  obtain ⟨s, t, hsσ, hst, htK, hsep, hadv⟩ := hdisp
  have hε0 : (0 : ℝ) < (L : ℝ) ^ ((3 : ℝ) / 4) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < L) : (0 : ℝ) < (L : ℝ)) _
  -- the record hypothesis at the actual clock, and the truncation on the whole window
  have hrec : LocGroupSimul.RecHyp p m r (recTimeA p m U r) L U := recHyp_at_record hcarr
  have hwin : ∀ k : ℕ, s ≤ k → k < t →
      winTrunc p m k I J hI (Bstar L) (Astar r T L) U := by
    intro k hk hkt
    exact winTrunc_of_record (N := N) hp0 hp1.le I J hI hJ hid hT hL hr
      (n0 := recTimeA p m U r) (n := k) (by omega) (by omega) hrec hlm hgood2
      (hsep k (Finset.mem_Ico.mpr ⟨hk, hkt⟩))
  -- the chaining inequality from the start of the window
  have hchain := hgood3 (recTimeA p m U r) s t (T * L) hsσ hst htK hwin
  -- partial sums from the clock are differences of the global martingale
  have hpse : ∀ k : ℕ,
      LocMart.psum (fun j => dQTW p m (recTimeA p m U r + j) I J hI hJ (Bstar L) (Astar r T L)) k U
        = Qtr p m I J hI hJ (Bstar L) (Astar r T L) (recTimeA p m U r + k) U
          - Qtr p m I J hI hJ (Bstar L) (Astar r T L) (recTimeA p m U r) U := by
    intro k
    have h := congrFun (LocGroupSimul.psum_sub_eq
      (ξ := fun j => dQTW p m j I J hI hJ (Bstar L) (Astar r T L))
      (a := recTimeA p m U r) k) U
    have hp : ∀ n : ℕ,
        LocMart.psum (fun j => dQTW p m j I J hI hJ (Bstar L) (Astar r T L)) n U
          = Qtr p m I J hI hJ (Bstar L) (Astar r T L) n U := by
      intro n
      simp only [Qtr, LocMart.psum]
      exact Finset.sum_congr rfl fun j _ => (hgood1 j).symm
    rw [h, hp, hp]
  rw [hpse (t - recTimeA p m U r), hpse (s - recTimeA p m U r),
    Nat.add_sub_cancel' (le_trans hsσ hst), Nat.add_sub_cancel' hsσ] at hchain
  have hsum : (L : ℝ) ^ ((3 : ℝ) / 4)
      < |Qtr p m I J hI hJ (Bstar L) (Astar r T L) t U
          - Qtr p m I J hI hJ (Bstar L) (Astar r T L) (recTimeA p m U r) U|
        + |Qtr p m I J hI hJ (Bstar L) (Astar r T L) s U
          - Qtr p m I J hI hJ (Bstar L) (Astar r T L) (recTimeA p m U r) U| :=
    lt_of_lt_of_le hadv hchain
  rcases lt_or_ge ((L : ℝ) ^ ((3 : ℝ) / 4) / 2)
      |Qtr p m I J hI hJ (Bstar L) (Astar r T L) t U
        - Qtr p m I J hI hJ (Bstar L) (Astar r T L) (recTimeA p m U r) U| with hcase | hcase
  · refine ⟨t - recTimeA p m U r, by omega, ?_⟩
    rw [Nat.add_sub_cancel' (le_trans hsσ hst)]
    exact le_of_lt hcase
  · have hcase' : (L : ℝ) ^ ((3 : ℝ) / 4) / 2
        < |Qtr p m I J hI hJ (Bstar L) (Astar r T L) s U
            - Qtr p m I J hI hJ (Bstar L) (Astar r T L) (recTimeA p m U r) U| := by
      by_contra hc
      push Not at hc
      linarith
    refine ⟨s - recTimeA p m U r, by omega, ?_⟩
    rw [Nat.add_sub_cancel' hsσ]
    exact le_of_lt hcase'


/-! ## 8. The measured failure event of the display at the record clock -/

/-- The record-clock failure event of the display `(locgroup)`, with the a.e. inputs of the bridge
still exhibited as a memberhip in `goodSet`. -/
def locGroupFail (p : ℝ) (m : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty)
    (r T L : ℕ) : Set (Array N) :=
  recordCarrier (N := N) p m r L ∩ goodSet (N := N) p m I J hI hJ (Bstar L) (Astar r T L) ∩
    {U : Array N | U ∉ LocMaxBad (N := N) p m r T L ∧
      (∃ s t : ℕ, recTimeA p m U r ≤ s ∧ s ≤ t ∧ t ≤ recTimeA p m U r + T * L ∧
        (∀ u ∈ Finset.Ico s t, SepSet p m u I J U) ∧
        (L : ℝ) ^ ((3 : ℝ) / 4) < WA p m U t I J hI hJ - WA p m U s I J hI hJ)}

/-- The same failure event with the a.e. inputs absorbed into its definition (the form of the
paper's event: the carrier, the failure of `(locmax)`, the forward-potential a.e. bound, and a
window on which `(sep)` holds but the display fails). -/
def locGroupBad (p : ℝ) (m : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty)
    (r T L : ℕ) : Set (Array N) :=
  recordCarrier (N := N) p m r L ∩
    {U : Array N | U ∉ LocMaxBad (N := N) p m r T L ∧
      (∀ j : Fin N, ∀ u : ℕ,
        BddAbove (Set.range fun n' => Gtrunc p (siteMarks p m U j) n' (u + 1))) ∧
      (∃ s t : ℕ, recTimeA p m U r ≤ s ∧ s ≤ t ∧ t ≤ recTimeA p m U r + T * L ∧
        (∀ u ∈ Finset.Ico s t, SepSet p m u I J U) ∧
        (L : ℝ) ^ ((3 : ℝ) / 4) < WA p m U t I J hI hJ - WA p m U s I J hI hJ)}

/-- **The two forms differ only on a null set**: the second is contained in the first together
with the complement of `goodSet`. -/
theorem locGroupBad_subset (p : ℝ) (m : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty)
    (hJ : J.Nonempty) (r T L : ℕ) :
    locGroupBad (N := N) p m I J hI hJ r T L
      ⊆ locGroupFail (N := N) p m I J hI hJ r T L
        ∪ (goodSet (N := N) p m I J hI hJ (Bstar L) (Astar r T L))ᶜ := by
  rintro U ⟨hcarr, hlm, hbd, hdisp⟩
  by_cases hg : U ∈ goodSet (N := N) p m I J hI hJ (Bstar L) (Astar r T L)
  · exact Or.inl ⟨⟨hcarr, hg⟩, hlm, hdisp⟩
  · exact Or.inr hg

/-- **The measured bound for the display failure at the record clock.**  The bound is the
count-free stopped maximal estimate (mass charged once per record band) plus the `(locmax)`
budget `δ`, and nothing else: there is no factor for the number of clock values. -/
theorem measureReal_locGroupFail_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {T : ℕ} (hT : 1 ≤ T) {L : ℕ} (hL : 2 ≤ L) {r : ℕ} (hr : (T + 3) * L ≤ r)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hlm : (arrayMeasure N).real (LocMaxBad (N := N) p m r T L) ≤ δ) :
    (arrayMeasure N).real (locGroupFail (N := N) p m I J hI hJ r T L)
      ≤ 2 * ((T : ℝ) * (L : ℝ) + 1) *
          Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4) / 2) ^ 2) /
            (4 * (((T * L : ℕ)) : ℝ) *
              (2 * LocGroupWindow.stepEnv (N := N) p (Bstar L)) ^ 2))
        + δ := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hn : 1 ≤ T * L := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hL1 : 1 ≤ L := by omega
  have hε : (0 : ℝ) < (L : ℝ) ^ ((3 : ℝ) / 4) / 2 := by
    have h := Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < L) : (0 : ℝ) < (L : ℝ))
      ((3 : ℝ) / 4)
    linarith
  have hbdd := measureReal_recordClock_groupDev_le (N := N) (m := m) hp0 hp1 I J hI hJ hid
    (Bstar_pos hL1) (Astar r T L) r L hn hε
  have hTC : (((T * L : ℕ)) : ℝ) + 1 = (T : ℝ) * (L : ℝ) + 1 := by push_cast; ring
  rw [hTC] at hbdd
  have hsub : locGroupFail (N := N) p m I J hI hJ r T L
      ⊆ recordCarrier (N := N) p m r L ∩
          StoppedWindow.stoppedMax (Qtr p m I J hI hJ (Bstar L) (Astar r T L))
            (fun U : Array N => recTimeA p m U r) (T * L) ((L : ℝ) ^ ((3 : ℝ) / 4) / 2) := by
    rintro U ⟨⟨hcarr, hg⟩, hlmU, hdisp⟩
    exact ⟨hcarr, dev_of_displayFailure (N := N) hp0 hp1 I J hI hJ hid hT hL hr hcarr hg hlmU hdisp⟩
  refine le_trans (measureReal_mono hsub (measure_ne_top _ _)) ?_
  · linarith [hbdd, hδ]

/-- **The measured bound for the paper's own form of the failure event** (a.e. inputs absorbed):
the same count-free bound plus `δ`. -/
theorem measureReal_locGroupBad_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty)
    (hid : Disjoint I J) {T : ℕ} (hT : 1 ≤ T) {L : ℕ} (hL : 2 ≤ L) {r : ℕ}
    (hr : (T + 3) * L ≤ r)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hlm : (arrayMeasure N).real (LocMaxBad (N := N) p m r T L) ≤ δ) :
    (arrayMeasure N).real (locGroupBad (N := N) p m I J hI hJ r T L)
      ≤ 2 * ((T : ℝ) * (L : ℝ) + 1) *
          Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4) / 2) ^ 2) /
            (4 * (((T * L : ℕ)) : ℝ) *
              (2 * LocGroupWindow.stepEnv (N := N) p (Bstar L)) ^ 2))
        + δ := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hL1 : 1 ≤ L := by omega
  have hfail := measureReal_locGroupFail_le (N := N) hp0 hp1 I J hI hJ hid hT hL hr hδ hlm
  have hnull : (arrayMeasure N).real
      (goodSet (N := N) p m I J hI hJ (Bstar L) (Astar r T L))ᶜ = 0 :=
    measureReal_goodSet_compl hp0 hp1 hm I J hI hJ hid (Bstar_nonneg hL1) (Astar r T L)
  have hsub := locGroupBad_subset (N := N) p m I J hI hJ r T L
  calc (arrayMeasure N).real (locGroupBad (N := N) p m I J hI hJ r T L)
      ≤ (arrayMeasure N).real
          (locGroupFail (N := N) p m I J hI hJ r T L
            ∪ (goodSet (N := N) p m I J hI hJ (Bstar L) (Astar r T L))ᶜ) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (arrayMeasure N).real (locGroupFail (N := N) p m I J hI hJ r T L)
          + (arrayMeasure N).real
              (goodSet (N := N) p m I J hI hJ (Bstar L) (Astar r T L))ᶜ :=
        measureReal_union_le _ _
    _ = (arrayMeasure N).real (locGroupFail (N := N) p m I J hI hJ r T L) := by
        rw [hnull, add_zero]
    _ ≤ _ := hfail


/-! ## 9. The paper's profile `C_T exp (-c_T * xOf L)` -/

/-- The `(locgroup)` envelope at the record scale is at most `321 N L^{1/8}`. -/
theorem two_stepEnv_Bstar_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p ≤ 1) {N : ℕ}
    (hN : 1 ≤ N) {L : ℕ} (hL : 1 ≤ L) :
    2 * LocGroupWindow.stepEnv (N := N) p (Bstar L) ≤ 321 * (N : ℝ) * (L : ℝ) ^ ((1 : ℝ) / 8) := by
  have hLr : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  rw [Bstar_eq_truncLevel hL]
  have hC := LocScaleArithmetic.two_envB_truncLevel_le (N := N) hp0 hp1 hN hLr
  have hE0 : (0 : ℝ) ≤ 2 * LocGroupWindow.stepEnv (N := N) p
      (LocScaleArithmetic.truncLevel (L : ℝ)) := by
    have h0 : (0 : ℝ) ≤ LocScaleArithmetic.truncLevel (L : ℝ) := by
      rw [LocScaleArithmetic.truncLevel_eq hLr]
      have : (0 : ℝ) < (L : ℝ) ^ ((1 : ℝ) / 16) :=
        Real.rpow_pos_of_pos (by linarith) _
      linarith
    have h1 := LocGroupWindow.stepEnv_nonneg (N := N) hp0 hp1 h0
    linarith
  simp only [LocGroupWindow.stepEnv] at hC ⊢
  linarith

/-- **The exponent comparison**: the Azuma exponent at the record scale is at least
`locRate N T * L^{1/4}`. -/
theorem exp_compare {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p ≤ 1) {N : ℕ} (hN : 1 ≤ N)
    {T : ℕ} (hT : 1 ≤ T) {L : ℕ} (hL : 1 ≤ L) :
    -(((L : ℝ) ^ ((3 : ℝ) / 4) / 2) ^ 2) /
        (4 * (((T * L : ℕ)) : ℝ) * (2 * LocGroupWindow.stepEnv (N := N) p (Bstar L)) ^ 2)
      ≤ -locRate N T * Lq L := by
  have hLr : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < (L : ℝ) := by linarith
  have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hu : (0 : ℝ) < Lq L := Real.rpow_pos_of_pos hLpos _
  have hLq4 : Lq L ^ 4 = (L : ℝ) := Lq_pow_four hL
  have hu2 : Lq L ^ 2 = (L : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [Lq, ← Real.rpow_natCast ((L : ℝ) ^ ((1 : ℝ) / 4)) 2, ← Real.rpow_mul hLpos.le]
    norm_num
  have hTLcast : (((T * L : ℕ)) : ℝ) = (T : ℝ) * (L : ℝ) := by push_cast; ring
  have hEpos : (0 : ℝ) < 2 * LocGroupWindow.stepEnv (N := N) p (Bstar L) := by
    have := LocGroupWindow.stepEnv_pos (N := N) hp0 hp1 (Bstar_pos hL)
    linarith
  have hnum : ((L : ℝ) ^ ((3 : ℝ) / 4) / 2) ^ 2 = (L : ℝ) * Lq L ^ 2 / 4 := by
    have h34 : ((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2 = (L : ℝ) ^ ((3 : ℝ) / 2) := by
      rw [← Real.rpow_natCast ((L : ℝ) ^ ((3 : ℝ) / 4)) 2]
      rw [← Real.rpow_mul hLpos.le]
      norm_num
    have h32 : (L : ℝ) ^ ((3 : ℝ) / 2) = (L : ℝ) * Lq L ^ 2 := by
      rw [show ((3 : ℝ) / 2) = (1 : ℝ) + 1 / 2 from by norm_num, Real.rpow_add hLpos,
        Real.rpow_one, ← hu2]
    rw [div_pow, h34, h32]
    norm_num
  have hE := two_stepEnv_Bstar_le (N := N) hp0 hp1 hN hL
  have hEsq : (2 * LocGroupWindow.stepEnv (N := N) p (Bstar L)) ^ 2
      ≤ (321 * (N : ℝ)) ^ 2 * Lq L := by
    have h1 : (0 : ℝ) ≤ 2 * LocGroupWindow.stepEnv (N := N) p (Bstar L) := hEpos.le
    have h2 : (0 : ℝ) ≤ 321 * (N : ℝ) * (L : ℝ) ^ ((1 : ℝ) / 8) := by positivity
    have h3 : (2 * LocGroupWindow.stepEnv (N := N) p (Bstar L)) ^ 2
        ≤ (321 * (N : ℝ) * (L : ℝ) ^ ((1 : ℝ) / 8)) ^ 2 :=
      pow_le_pow_left₀ h1 hE 2
    have h4 : (321 * (N : ℝ) * (L : ℝ) ^ ((1 : ℝ) / 8)) ^ 2 = (321 * (N : ℝ)) ^ 2 * Lq L := by
      rw [mul_pow, mul_pow, Lq]
      congr 1
      rw [show ((1 : ℝ) / 4) = (1 : ℝ) / 8 + (1 : ℝ) / 8 by norm_num,
        Real.rpow_add hLpos]
      ring
    rw [h4] at h3
    exact h3
  rw [hnum, hTLcast]
  have hden : (0 : ℝ) < 4 * ((T : ℝ) * (L : ℝ)) *
      (2 * LocGroupWindow.stepEnv (N := N) p (Bstar L)) ^ 2 := by positivity
  have key : locRate N T * Lq L ≤ ((L : ℝ) * Lq L ^ 2 / 4) /
      (4 * ((T : ℝ) * (L : ℝ)) * (2 * LocGroupWindow.stepEnv (N := N) p (Bstar L)) ^ 2) := by
    rw [le_div_iff₀ hden, locRate]
    have hE2 : (0 : ℝ) < (321 * (N : ℝ)) ^ 2 := by positivity
    have hkey2 : Lq L * (2 * LocGroupWindow.stepEnv (N := N) p (Bstar L)) ^ 2
        ≤ Lq L * ((321 * (N : ℝ)) ^ 2 * Lq L) :=
      mul_le_mul_of_nonneg_left hEsq hu.le
    have hrhs : Lq L * ((321 * (N : ℝ)) ^ 2 * Lq L) = (321 * (N : ℝ)) ^ 2 * Lq L ^ 2 := by ring
    rw [hrhs] at hkey2
    have hden2 : (0 : ℝ) < 16 * (T : ℝ) * (321 * (N : ℝ)) ^ 2 := by positivity
    field_simp
    nlinarith [hkey2, hu, hLpos, hT0, hN0, hE2, mul_pos hT0 hLpos]
  have hneg := neg_le_neg key
  calc -((L : ℝ) * Lq L ^ 2 / 4) /
        (4 * ((T : ℝ) * (L : ℝ)) * (2 * LocGroupWindow.stepEnv (N := N) p (Bstar L)) ^ 2)
      = -(((L : ℝ) * Lq L ^ 2 / 4) /
        (4 * ((T : ℝ) * (L : ℝ)) * (2 * LocGroupWindow.stepEnv (N := N) p (Bstar L)) ^ 2)) := by
        ring
    _ ≤ -(locRate N T * Lq L) := hneg
    _ = -locRate N T * Lq L := by ring


/-- **The paper's display `(locgroup)` at the literal actual record clock, in the paper's
profile.**  For `1/2 < p < 1`, `2 ≤ m`, disjoint nonempty `I J` and every fixed `T ≥ 1` there are
`c_T > 0` and `L₀` such that for every `L ≥ L₀` and **every** record level `r ≥ (T+3)L`:

the set of trajectories on which

* the paper's carrier `{d_r ≤ L}` holds (`recordCarrier`, which also pins `ReachAll`),
* the `(locmax)` window event fails to occur,
* the forward-potential truncations are bounded above at every site (an a.e. condition),
* and yet some window `τ_r ≤ s ≤ t ≤ τ_r + T*L` on which `(sep)` holds at every integer time has
  `W_t^{I,J} - W_s^{I,J} > L^{3/4}`,

has `arrayMeasure`-measure at most `C_T exp (-c_T * L^{1/16})` with `C_T = locConst N T`, i.e. the
display `(locgroup)` holds off that set with the constant `1`.  The clock is the actual
`SwarmRecordMeas.Actual.recTimeA`, the measure is the actual `Swarm.Uniform.arrayMeasure N`, and
there is no union over clock values and no cutoff on the clock. -/
theorem exists_recordClock_locgroup {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty)
    (hid : Disjoint I J) {T : ℕ} (hT : 1 ≤ T) :
    ∃ c_T : ℝ, 0 < c_T ∧ ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∀ r : ℕ, (T + 3) * L ≤ r →
      (arrayMeasure N).real (locGroupBad (N := N) p m I J hI hJ r T L)
        ≤ locConst N T * Real.exp (-c_T * xOf L) := by
  obtain ⟨c_lm, hc_lm, L₀_lm, hlm⟩ := exists_locMaxBad_le (N := N) hp0 hp1 hm T hT
  have hN : 1 ≤ N := by
    obtain ⟨i, hi⟩ := hI
    have := i.isLt
    omega
  have hapos : 0 < locRate N T := locRate_pos hN hT
  refine ⟨min (locRate N T / 2) c_lm, lt_min (by linarith) hc_lm, max (max L₀_lm 2) 1, ?_⟩
  intro L hLbig r hr
  have hL0 : L₀_lm ≤ L := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hLbig)
  have hL2 : 2 ≤ L := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hLbig)
  have hL1 : 1 ≤ L := by omega
  have hx0 : 0 ≤ xOf L := le_trans zero_le_one (LocSumAct.one_le_xOf hL1)
  -- the `(locmax)` budget
  have hδpos : 0 < Real.exp (-c_lm * xOf L) := Real.exp_pos _
  have hlmL : (arrayMeasure N).real (LocMaxBad (N := N) p m r T L)
      ≤ Real.exp (-c_lm * xOf L) := by
    have h := hlm L hL0 r hr
    rw [measureReal_def]
    refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top h) ?_
    rw [ENNReal.toReal_ofReal hδpos.le]
  have hbase := measureReal_locGroupBad_le (N := N) hp0 hp1 hm I J hI hJ hid hT hL2 hr
    hδpos.le hlmL
  -- exponent comparison and absorption
  have hexp := exp_compare (N := N) hp0 hp1.le hN hT hL1
  have habs := absorb_le (locRate N T) hapos T hL1
  have hstep1 : 2 * ((T : ℝ) * (L : ℝ) + 1) *
        Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4) / 2) ^ 2) /
          (4 * (((T * L : ℕ)) : ℝ) *
            (2 * LocGroupWindow.stepEnv (N := N) p (Bstar L)) ^ 2))
      ≤ 2 * ((T : ℝ) * (L : ℝ) + 1) * Real.exp (-(locRate N T) * Lq L) := by
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) ?_
    positivity
  have hE1 : Real.exp (-(locRate N T / 2) * xOf L)
      ≤ Real.exp (-(min (locRate N T / 2) c_lm) * xOf L) := by
    refine Real.exp_le_exp.mpr ?_
    have hmin : min (locRate N T / 2) c_lm ≤ locRate N T / 2 := min_le_left _ _
    nlinarith [hx0, hmin]
  have hE2 : Real.exp (-c_lm * xOf L)
      ≤ Real.exp (-(min (locRate N T / 2) c_lm) * xOf L) := by
    refine Real.exp_le_exp.mpr ?_
    have hmin : min (locRate N T / 2) c_lm ≤ c_lm := min_le_right _ _
    nlinarith [hx0, hmin]
  have hcoef : (0 : ℝ) ≤ 2 * ((T : ℝ) + 1) *
      ((4 / (Real.exp 1 * (locRate N T / 2))) ^ 4 + 1) := by
    have h1 : (0 : ℝ) < Real.exp 1 * (locRate N T / 2) := by positivity
    have h2 : (0 : ℝ) ≤ 4 / (Real.exp 1 * (locRate N T / 2)) := by positivity
    have h3 : (0 : ℝ) ≤ (4 / (Real.exp 1 * (locRate N T / 2))) ^ 4 := by positivity
    have h4 : (0 : ℝ) ≤ (T : ℝ) + 1 := by positivity
    nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ (4 / (Real.exp 1 * (locRate N T / 2))) ^ 4 + 1)]
  have hfin : 2 * ((T : ℝ) * (L : ℝ) + 1) *
        Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4) / 2) ^ 2) /
          (4 * (((T * L : ℕ)) : ℝ) *
            (2 * LocGroupWindow.stepEnv (N := N) p (Bstar L)) ^ 2))
        + Real.exp (-c_lm * xOf L)
      ≤ locConst N T * Real.exp (-(min (locRate N T / 2) c_lm) * xOf L) := by
    have hmid : 2 * ((T : ℝ) * (L : ℝ) + 1) * Real.exp (-(locRate N T) * Lq L)
        ≤ 2 * ((T : ℝ) + 1) * ((4 / (Real.exp 1 * (locRate N T / 2))) ^ 4 + 1)
          * Real.exp (-(locRate N T / 2) * xOf L) := habs
    have hstep2 : 2 * ((T : ℝ) + 1) * ((4 / (Real.exp 1 * (locRate N T / 2))) ^ 4 + 1)
          * Real.exp (-(locRate N T / 2) * xOf L)
        ≤ 2 * ((T : ℝ) + 1) * ((4 / (Real.exp 1 * (locRate N T / 2))) ^ 4 + 1)
          * Real.exp (-(min (locRate N T / 2) c_lm) * xOf L) :=
      mul_le_mul_of_nonneg_left hE1 hcoef
    have hstep3 : Real.exp (-c_lm * xOf L)
        ≤ Real.exp (-(min (locRate N T / 2) c_lm) * xOf L) := hE2
    have hconst : locConst N T
        = 2 * ((T : ℝ) + 1) * ((4 / (Real.exp 1 * (locRate N T / 2))) ^ 4 + 1) + 1 := rfl
    calc 2 * ((T : ℝ) * (L : ℝ) + 1) *
          Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4) / 2) ^ 2) /
            (4 * (((T * L : ℕ)) : ℝ) *
              (2 * LocGroupWindow.stepEnv (N := N) p (Bstar L)) ^ 2))
          + Real.exp (-c_lm * xOf L)
        ≤ 2 * ((T : ℝ) * (L : ℝ) + 1) * Real.exp (-(locRate N T) * Lq L)
          + Real.exp (-c_lm * xOf L) := by linarith [hstep1]
      _ ≤ 2 * ((T : ℝ) + 1) * ((4 / (Real.exp 1 * (locRate N T / 2))) ^ 4 + 1)
            * Real.exp (-(min (locRate N T / 2) c_lm) * xOf L)
          + Real.exp (-(min (locRate N T / 2) c_lm) * xOf L) := by
          linarith [hmid, hstep2, hstep3]
      _ = locConst N T * Real.exp (-(min (locRate N T / 2) c_lm) * xOf L) := by
          rw [hconst]; ring
  calc (arrayMeasure N).real (locGroupBad (N := N) p m I J hI hJ r T L)
      ≤ 2 * ((T : ℝ) * (L : ℝ) + 1) *
          Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4) / 2) ^ 2) /
            (4 * (((T * L : ℕ)) : ℝ) *
              (2 * LocGroupWindow.stepEnv (N := N) p (Bstar L)) ^ 2))
        + Real.exp (-c_lm * xOf L) := hbase
    _ ≤ locConst N T * Real.exp (-(min (locRate N T / 2) c_lm) * xOf L) := hfin


/-- **The display `(locgroup)` itself, at the literal actual record clock.**  Same constants as
`exists_recordClock_locgroup`; on the carrier `{d_r ≤ L}`, off `(locmax)` and off the measured bad
set, the increment of `W^{I,J}` over *every* sub-window of `[τ_r, τ_r + T*L]` on which `(sep)`
holds is at most `L^{3/4}`.  This is display `(locgroup)` of Proposition `local` with the clock
`τ_r` and the measure `arrayMeasure N`; `(sep)` remains a hypothesis of the display, as in the
paper. -/
theorem locgroup_at_recordClock {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty)
    (hid : Disjoint I J) {T : ℕ} (hT : 1 ≤ T) :
    ∃ c_T : ℝ, 0 < c_T ∧ ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∀ r : ℕ, (T + 3) * L ≤ r →
      ∀ U : Array N, U ∈ recordCarrier (N := N) p m r L →
        U ∉ LocMaxBad (N := N) p m r T L →
        (∀ j : Fin N, ∀ u : ℕ,
          BddAbove (Set.range fun n' => Gtrunc p (siteMarks p m U j) n' (u + 1))) →
        U ∉ locGroupBad (N := N) p m I J hI hJ r T L →
        ∀ s t : ℕ, recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
          (∀ u ∈ Finset.Ico s t, SepSet p m u I J U) →
          WA p m U t I J hI hJ - WA p m U s I J hI hJ ≤ (L : ℝ) ^ ((3 : ℝ) / 4) := by
  obtain ⟨c_T, hc_T, L₀, hL₀⟩ := exists_recordClock_locgroup (N := N) hp0 hp1 hm I J hI hJ hid hT
  refine ⟨c_T, hc_T, L₀, ?_⟩
  intro L hL r hr U hcarr hlm hbd hnb s t hsσ hst htK hsep
  by_contra hcon
  push Not at hcon
  exact hnb ⟨hcarr, hlm, hbd, ⟨s, t, hsσ, hst, htK, hsep, hcon⟩⟩


/-! ## 10. Simultaneity over a record range: the exact loss -/

/-- **The record levels whose clock falls in the first `n` steps are at most `n+1`.**  On the
reachable set `τ_r ≥ r`, so `{r | τ_r ≤ n} ⊆ {0, …, n}`: a time window of length `n` contains at
most `n+1` record levels, whatever the values of the clocks.  This is the exact count that
replaces "one union factor per candidate clock". -/
theorem recordLevels_subset_range {p : ℝ} {m n : ℕ} {U : Array N}
    (hreach : U ∈ ReachAll (N := N) p m) :
    {r : ℕ | recTimeA p m U r ≤ n} ⊆ (Finset.range (n + 1) : Set ℕ) := by
  intro r hr
  change recTimeA p m U r ≤ n at hr
  have hge : r ≤ recTimeA p m U r := M4RecordGeom.recTimeA_ge_level hreach r
  simp only [Finset.coe_range, Set.mem_Iio]
  exact Nat.lt_succ_of_le (le_trans hge hr)

/-- **Simultaneous-in-`r` bound over a range of record levels, with the explicit loss `R+1`.**
The per-record profile of `exists_recordClock_locgroup` is *uniform in the record level*, so the
simultaneous statement over `R+1` consecutive levels costs exactly one factor `R+1` and nothing
else: no union over clock values, no truncation, no per-clock loss.  (Reducing the factor `R+1`
further would require a time-indexed estimate, not a record-indexed one; the count
`recordLevels_subset_range` shows that `R ≤ n` is automatic inside `n` steps.) -/
theorem measureReal_locGroupBad_iUnion_range_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty)
    (hid : Disjoint I J) {T : ℕ} (hT : 1 ≤ T) {L r₀ R : ℕ} (hL : 2 ≤ L) (hr₀ : (T + 3) * L ≤ r₀) :
    ∃ c_T : ℝ, 0 < c_T ∧
      (arrayMeasure N).real
          (⋃ r ∈ Finset.Icc r₀ (r₀ + R), locGroupBad (N := N) p m I J hI hJ r T L)
        ≤ ((R : ℝ) + 1) * (locConst N T * Real.exp (-c_T * xOf L)) := by
  obtain ⟨c_T, hc_T, L₀, hL₀⟩ := exists_recordClock_locgroup (N := N) hp0 hp1 hm I J hI hJ hid hT
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hN : 1 ≤ N := by
    obtain ⟨i, hi⟩ := hI
    have := i.isLt
    omega
  have hrate : 0 < locRate N T := locRate_pos hN hT
  have hQgt : 1 < locConst N T := by
    unfold locConst
    have hpos : 0 < 2 * ((T : ℝ) + 1) *
        ((4 / (Real.exp 1 * (locRate N T / 2))) ^ 4 + 1) := by positivity
    linarith
  have hQpos : 0 < locConst N T := lt_trans zero_lt_one hQgt
  have hQzero : 0 ≤ locConst N T := hQpos.le
  have hL1 : 1 ≤ L := by omega
  have hxL : 0 ≤ xOf L := le_trans zero_le_one (LocSumAct.one_le_xOf hL1)
  -- The old draft silently assumed `L₀ ≤ L`. Instead, use the original profile
  -- above `max L₀ 1` and reduce the rate so that the RHS is at least one below it.
  let L₁ : ℕ := max L₀ 1
  have hL₁x : 1 ≤ xOf L₁ := LocSumAct.one_le_xOf (Nat.le_max_right L₀ 1)
  have hxL₁ : 0 < xOf L₁ := lt_of_lt_of_le zero_lt_one hL₁x
  have hlogpos : 0 < Real.log (locConst N T) := Real.log_pos hQgt
  let c : ℝ := min c_T (Real.log (locConst N T) / xOf L₁)
  have hcpos : 0 < c := lt_min hc_T (div_pos hlogpos hxL₁)
  refine ⟨c, hcpos, ?_⟩
  have hterm : ∀ r ∈ Finset.Icc r₀ (r₀ + R),
      (arrayMeasure N).real (locGroupBad (N := N) p m I J hI hJ r T L)
        ≤ locConst N T * Real.exp (-c * xOf L) := by
    intro r hr
    have hrr : (T + 3) * L ≤ r := le_trans hr₀ (Finset.mem_Icc.mp hr).1
    by_cases hbig : L₁ ≤ L
    · have hL0 : L₀ ≤ L := le_trans (Nat.le_max_left L₀ 1) hbig
      have hbase := hL₀ L hL0 r hrr
      have hExp : Real.exp (-c_T * xOf L) ≤ Real.exp (-c * xOf L) := by
        apply Real.exp_le_exp.mpr
        have hc : c ≤ c_T := min_le_left _ _
        have hmul := mul_le_mul_of_nonneg_right hc hxL
        linarith
      exact le_trans hbase (mul_le_mul_of_nonneg_left hExp hQzero)
    · have hsingle : (arrayMeasure N).real (locGroupBad (N := N) p m I J hI hJ r T L) ≤ 1 :=
        measureReal_le_one
      refine le_trans hsingle ?_
      have hLL₁ : L ≤ L₁ := by omega
      have hnat : (L : ℝ) ≤ (L₁ : ℝ) := by exact_mod_cast hLL₁
      have hxmono : xOf L ≤ xOf L₁ := by
        unfold LocSumAct.xOf
        exact Real.rpow_le_rpow (Nat.cast_nonneg L) hnat (by norm_num)
      have hdivnonneg : 0 ≤ Real.log (locConst N T) / xOf L₁ := div_nonneg hlogpos.le hxL₁.le
      have h1 : c * xOf L ≤ (Real.log (locConst N T) / xOf L₁) * xOf L :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hxL
      have h2 : (Real.log (locConst N T) / xOf L₁) * xOf L
          ≤ (Real.log (locConst N T) / xOf L₁) * xOf L₁ :=
        mul_le_mul_of_nonneg_left hxmono hdivnonneg
      have h3 : (Real.log (locConst N T) / xOf L₁) * xOf L₁ = Real.log (locConst N T) :=
        div_mul_cancel₀ _ hxL₁.ne'
      have hcx : c * xOf L ≤ Real.log (locConst N T) := le_trans h1 (le_trans h2 h3.le)
      calc
        1 = Real.exp 0 := by simp
        _ ≤ Real.exp (Real.log (locConst N T) - c * xOf L) := Real.exp_le_exp.mpr (by linarith)
        _ = locConst N T / Real.exp (c * xOf L) := by
            rw [Real.exp_sub, Real.exp_log hQpos]
        _ = locConst N T * Real.exp (-c * xOf L) := by
            rw [div_eq_mul_inv, ← Real.exp_neg, neg_mul]
  refine le_trans (measureReal_biUnion_finset_le _ _) ?_
  have hcard : ((Finset.Icc r₀ (r₀ + R)).card : ℝ) ≤ (R : ℝ) + 1 := by
    have h1 : (Finset.Icc r₀ (r₀ + R)).card ≤ R + 1 := by
      rw [Nat.card_Icc]
      omega
    exact_mod_cast h1
  calc ∑ r ∈ Finset.Icc r₀ (r₀ + R),
        (arrayMeasure N).real (locGroupBad (N := N) p m I J hI hJ r T L)
      ≤ ∑ _r ∈ Finset.Icc r₀ (r₀ + R),
          (locConst N T * Real.exp (-c * xOf L)) := Finset.sum_le_sum hterm
    _ = ((Finset.Icc r₀ (r₀ + R)).card : ℝ) * (locConst N T * Real.exp (-c * xOf L)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((R : ℝ) + 1) * (locConst N T * Real.exp (-c * xOf L)) := by
        exact mul_le_mul_of_nonneg_right hcard (mul_nonneg hQzero (Real.exp_pos _).le)

end RecClockLG
