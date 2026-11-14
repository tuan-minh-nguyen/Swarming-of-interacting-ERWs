/-
# The *local* forward-run carrier: `RunsOK` restricted to the record window

## The obstruction this removes

`WindowPos.runWindowPos` (`RunPosCarrier`) is the event

    ∀ i, SwarmRun.RunsOK (siteMarks p m U i) (r + T·L + 1) K ,

a **documented prefix** condition: a marked site in every `K`-block of *positions*
`[0, r + T·L + 1]`.  Its measured complement is `N·(r + T·L + 1)·(1-q)^K`
(`RunPosMeas.arrayMeasure_runWindowPos_compl_le`).  The factor `r` is not an artefact of the
proof: the constant `r` is the record *level*, and the block-clause profile has to be uniform in
`r ≥ (T+3)·L`.  That is exactly why `RunPosWindow.exists_badEventPos_le` and
`RunPosFinal.exists_badEventPos_blockClauses` carry the extra restriction `r ≤ L²`: it is the
degree-two polynomial absorption `r + T·L + 1 ≤ (T+3)(L+1)²` of that one lane, and it is the
*only* place `r ≤ L²` is used.  The prefix-run lane therefore obstructs a `∀r` profile
(`RunLow.no_full_range_profile`, `RunPosObstruct.no_profile_only_full_range`), and no numerical
strengthening of `K` recovers it, because the demanded constant would have to grow with `log r`.

## The observation

`Gtail` is a **forward** potential.  The only `Gtail` facts the movement carrier consumes are

    Gtail p m U i u ((runMax p m U i n).toNat + 1) ≤ G ,      u ∈ [Astar, xTop] ,

and `Gtail p m U i u (R+1) = 1 + Gtrunc p (siteMarks … i) (R-u) (u+1)` uses the site marks at
positions `u+1, u+2, …, R` only (`SiteWindow.Gsum_eq_Gtrunc`).  On `recordCarrier` the leader's
running maximum satisfies `R ≤ r + T·L` (`WindowPos.runMax_toNat_le_of_carrier`) and the level
window starts at `Astar r T L = r - ((T+2)L + 1)`.  Hence **only positions
`[Astar r T L, r + T·L + 1]` are ever inspected**, an interval of length `(2T+2)L + 3` that does
not grow with `r`.  Measuring the run event there gives

    N · ((2T+2)L + 3) · (1-q)^K ,

with **no `r` at all**.  With `K = Kc p L = ⌊L^{1/16}(1-ρ)⌋₊` this is `exp(-c·L^{1/16})` uniformly
in `r`, which is the missing `∀r` profile of the finite-run lane.

## Contents

* `SwarmRunLoc.RunsOn` — `RunsOK` on a window `[a,b)`; `RunsOn.of_runsOK` shows the prefix event
  implies it, so the new bad event is a **subset** of `badEventPos` (nothing is weakened on the
  deterministic side).
* `SwarmRunLoc.runsOn_cnt`, `Gtrunc_le_of_runsOn` — the forward-potential bound from window data.
* `WindowPosLocal.Gtail_le_of_runsOn_target` — `Gtail` at the leader's running maximum from the
  window run event (the local replacement of `WindowPos.Gtail_le_of_runs_target`).
* `WindowPosLocal.measurableSet_runsOn`, `measure_not_runsOn_le`,
  `arrayMeasure_runWindowLocal_compl_le` — the measured window event at `arrayMeasure N`, every
  `N` (no `2m < N`), with the `r`-free bound.
-/
import Swarm.RunPosFinal

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance LocGroupQ LocGroupWindow
open SwarmMarks SwarmLogRatio LocSumAct LocSumR1 LocOccCarrier LocOccAllStarts
open RecordDefect RecordoSupply SwarmRecordMeas SwarmRecordMeas.Actual
open ActualRecordFiltration LocGroupSimul LocMoveCompose LocMoveLocal LocMoveMart
open Loccoord Swarming.Enl ClockLocMove LocMovePaper LocalGoodFamily PaperBlock
open LocCoordGeomCarrier

namespace SwarmRunLoc

/-! ## 1. The window run predicate -/

/-- **No run of `K` consecutive unmarked sites inside the window `[a,b)`.**

`SwarmRun.RunsOK ω b K` is the case `a = 0`; the window version is strictly weaker for `a > 0`. -/
def RunsOn (ω : ℕ → Bool) (a b K : ℕ) : Prop :=
  ∀ y : ℕ, a ≤ y → y + K ≤ b → ∃ z ∈ Finset.Ico y (y + K), ω z = true

/-- The prefix event implies the window event: the new carrier is a *subset* of the old one. -/
theorem RunsOn.of_runsOK {ω : ℕ → Bool} {b K : ℕ} (h : SwarmRun.RunsOK ω b K) (a : ℕ) :
    RunsOn ω a b K :=
  fun y _ hyK => h y hyK

/-- Windows are inherited: a run-free window is run-free on every sub-window. -/
theorem RunsOn.mono {ω : ℕ → Bool} {a a' b' b K : ℕ} (h : RunsOn ω a b K) (ha : a ≤ a')
    (hb : b' ≤ b) : RunsOn ω a' b' K :=
  fun y hy hyK => h y (le_trans ha hy) (le_trans hyK hb)

/-- The pointwise failure form of the window predicate. -/
theorem not_runsOn_iff {ω : ℕ → Bool} {a b K : ℕ} :
    ¬ RunsOn ω a b K ↔
      ∃ y : ℕ, a ≤ y ∧ y + K ≤ b ∧ ∀ z ∈ Finset.Ico y (y + K), ω z = false := by
  constructor
  · intro h
    by_contra hcon
    apply h
    intro y hya hyK
    by_contra hno
    exact hcon ⟨y, hya, hyK, fun z hz => by
      cases hb : ω z with
      | false => rfl
      | true => exact absurd ⟨z, hz, hb⟩ hno⟩
  · rintro ⟨y, hya, hyK, hy⟩ hrun
    obtain ⟨z, hz, hztrue⟩ := hrun y hya hyK
    have := hy z hz
    rw [this] at hztrue
    exact Bool.noConfusion hztrue

/-! ## 2. The counting core on a window -/

/-- **A run-free window has `L / K` marked sites in every stretch of `L` positions**, provided the
stretch starts inside the window.  `SwarmRun.runsOK_cnt` with the hypothesis weakened to `RunsOn`. -/
theorem runsOn_cnt {ω : ℕ → Bool} {a b K : ℕ} (h : RunsOn ω a b K) (hK : 1 ≤ K) {y L : ℕ}
    (hay : a ≤ y) (hyL : y + L ≤ b) : L / K ≤ SwarmRun.cnt ω y L := by
  have hblock : ∀ t : ℕ, t ≤ L / K → t ≤ SwarmRun.cnt ω y (t * K) := by
    intro t ht
    induction t with
    | zero => simp
    | succ s ih =>
        have hs : s ≤ L / K := le_trans (Nat.le_succ s) ht
        have hih := ih hs
        have hle : (s + 1) * K ≤ L :=
          (Nat.le_div_iff_mul_le (by omega : 0 < K)).mp ht
        have hle' : s * K + K ≤ L := by rw [← Nat.succ_mul]; exact hle
        have hrun : 1 ≤ SwarmRun.cnt ω (y + s * K) K := by
          have hb : y + s * K + K ≤ b := by omega
          obtain ⟨z, hz, hztrue⟩ := h (y + s * K) (by omega) hb
          exact SwarmRun.one_le_cnt_of_true hz hztrue
        rw [Nat.succ_mul, SwarmRun.cnt_split]
        omega
  have hmono : SwarmRun.cnt ω y (L / K * K) ≤ SwarmRun.cnt ω y L :=
    SwarmRun.cnt_mono (Nat.div_mul_le_self L K)
  have := hblock (L / K) le_rfl
  omega

/-! ## 3. The forward potential from window data -/

/-- **The `G` bound on a run-free *window*.**  `SwarmRun.Gtrunc_le_of_runs` with `RunsOK ω b K`
replaced by `RunsOn ω a b K` (plus `a ≤ x`, which is automatic in the record geometry). -/
theorem Gtrunc_le_of_runsOn {p : ℝ} {ω : ℕ → Bool} {a b K : ℕ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hK : 1 ≤ K) (h : RunsOn ω a b K) {M x : ℕ}
    (hax : a ≤ x) (hxM : x + M ≤ b) :
    Gtrunc p ω M x ≤ 1 + (K : ℝ) / (1 - (1 - p) / p) := by
  rw [SwarmRun.Gtrunc_eq_sum]
  have hc0 : (0 : ℝ) ≤ (1 - p) / p := by positivity
  have hc1 : (1 - p) / p < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hterm : ∀ l ∈ Finset.range M,
      ∏ u ∈ Finset.range (l + 1), rhoOf p (ω (x + u)) ≤ ((1 - p) / p) ^ ((l + 1) / K) := by
    intro l hl
    rw [Finset.mem_range] at hl
    refine le_trans (SwarmRun.prod_rho_le hp1 hp2 x (l + 1))
      (pow_le_pow_of_le_one hc0 hc1.le ?_)
    exact runsOn_cnt h hK hax (by omega)
  have hsum : ∑ l ∈ Finset.range M, ((1 - p) / p) ^ ((l + 1) / K)
      ≤ ∑ q ∈ Finset.range (M + 1), ((1 - p) / p) ^ (q / K) := by
    rw [Finset.sum_range_succ' (f := fun q => ((1 - p) / p) ^ (q / K)) (n := M)]
    have h0 : (0 : ℝ) ≤ ((1 - p) / p) ^ ((0 : ℕ) / K) := by positivity
    linarith
  have hgeo := SwarmRun.sum_pow_div_le (c := (1 - p) / p) (K := K) hK hc0 hc1 (M + 1)
  calc 1 + ∑ l ∈ Finset.range M, ∏ u ∈ Finset.range (l + 1), rhoOf p (ω (x + u))
      ≤ 1 + ∑ l ∈ Finset.range M, ((1 - p) / p) ^ ((l + 1) / K) := by
        have := Finset.sum_le_sum hterm
        linarith
    _ ≤ 1 + ∑ q ∈ Finset.range (M + 1), ((1 - p) / p) ^ (q / K) := by linarith
    _ ≤ 1 + (K : ℝ) / (1 - (1 - p) / p) := by linarith

end SwarmRunLoc

namespace WindowPosLocal

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 4. `Gtail` at the leader's running maximum, from the window event -/

/-- **`Gtail` at the leader's running maximum from the window run event.**

`WindowPos.Gtail_le_of_runs_target` with `RunsOK … Lrun K` (a prefix condition) replaced by
`RunsOn … A B K` (a window condition).  The truncation of the forward sum only ever inspects
positions `u+1, …, R`, so a run-free window containing `[u+1, R]` is all that is needed. -/
theorem Gtail_le_of_runsOn_target {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (U : Array N) (i : Fin N) {A B R K u : ℕ} (hK : 1 ≤ K)
    (hrun : SwarmRunLoc.RunsOn (siteMarks p m U i) A B K)
    (hA : A ≤ u + 1) (hRB : R + 1 ≤ B) :
    Gtail p m U i u (R + 1) ≤ 2 + (K : ℝ) / (1 - (1 - p) / p) := by
  have hden : (0 : ℝ) < 1 - (1 - p) / p := by
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  have hnn : (0 : ℝ) ≤ (K : ℝ) / (1 - (1 - p) / p) := by positivity
  rcases lt_or_ge u (R + 1) with hlt | hge
  · have h1 : Gtail p m U i u (R + 1) = 1 + Gsum p m U i u (R + 1) := rfl
    rw [h1, SiteWindow.Gsum_eq_Gtrunc (by linarith : p ≠ 0) U i hlt]
    have h2 : Gtrunc p (siteMarks p m U i) (R + 1 - u - 1) (u + 1)
        ≤ 1 + (K : ℝ) / (1 - (1 - p) / p) := by
      refine SwarmRunLoc.Gtrunc_le_of_runsOn hp1 hp2 hK hrun hA ?_
      omega
    linarith
  · have hempty : Finset.Ico u (R + 1) = ∅ := Finset.Ico_eq_empty_iff.mpr (by omega)
    have h1 : Gtail p m U i u (R + 1) = 1 + Gsum p m U i u (R + 1) := rfl
    rw [h1, Gsum, hempty, Finset.sum_empty]
    linarith

/-! ## 5. The window event and its exact measure -/

/-- **The local (window) run event**: every walker's mark row is free of `K`-runs on `[A,B)`. -/
def runWindowLocal (p : ℝ) (m A B K : ℕ) (U : Array N) : Prop :=
  ∀ i : Fin N, SwarmRunLoc.RunsOn (siteMarks p m U i) A B K

/-- The record-window instance: `A = Astar r T L`, `B = r + T·L + 1`. -/
def runWindowLocalRec (p : ℝ) (m r T L K : ℕ) (U : Array N) : Prop :=
  runWindowLocal (N := N) p m (RecClockLG.Astar r T L) (r + T * L + 1) K U

/-- The prefix event of `RunPosCarrier` implies the window event (so the bad event shrinks). -/
theorem runWindowLocalRec_of_runWindowPos {p : ℝ} {m r T L K : ℕ} {U : Array N}
    (h : WindowPos.runWindowPos (N := N) p m r T L K U) :
    runWindowLocalRec (N := N) p m r T L K U :=
  fun i => SwarmRunLoc.RunsOn.of_runsOK (h i) (RecClockLG.Astar r T L)

/-- **Measurability of the window run event.** -/
theorem measurableSet_runsOn (a b K : ℕ) :
    MeasurableSet {ω : ℕ → Bool | SwarmRunLoc.RunsOn ω a b K} := by
  have h : {ω : ℕ → Bool | SwarmRunLoc.RunsOn ω a b K}
      = ⋂ y ∈ (Finset.range (b + 1)).filter (fun y => a ≤ y ∧ y + K ≤ b),
          ⋃ z ∈ Finset.Ico y (y + K), {ω : ℕ → Bool | ω z = true} := by
    ext ω
    simp only [SwarmRunLoc.RunsOn, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion,
      Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro h y ⟨hyb, hya, hyK⟩
      obtain ⟨z, hz, hztrue⟩ := h y hya hyK
      exact ⟨z, hz, hztrue⟩
    · rintro h y hya hyK
      obtain ⟨z, hz, hztrue⟩ := h y ⟨by omega, hya, hyK⟩
      exact ⟨z, hz, hztrue⟩
  rw [h]
  exact Finset.measurableSet_biInter _ (fun y _ => Finset.measurableSet_biUnion _
    (fun z _ => measurableSet_eq_fun (measurable_pi_apply z) measurable_const))

/-- **Exact measure of the window run event on one mark row.** -/
theorem measure_not_runsOn_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (a b K : ℕ) (hK : 1 ≤ K) :
    (markMeasure (boolMeasure q)) {ω : ℕ → Bool | ¬ SwarmRunLoc.RunsOn ω a b K}
      ≤ ENNReal.ofReal (((b - a + 1 : ℕ) : ℝ) * (1 - q) ^ K) := by
  have hqK : (0 : ℝ) ≤ (1 - q) ^ K := by
    have : (0 : ℝ) ≤ 1 - q := by linarith
    positivity
  by_cases hsmall : b ≤ a + K - 1
  · have hempty : {ω : ℕ → Bool | ¬ SwarmRunLoc.RunsOn ω a b K} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      intro y hya hyK
      omega
    rw [hempty, measure_empty]
    exact bot_le
  · have hsub : {ω : ℕ → Bool | ¬ SwarmRunLoc.RunsOn ω a b K}
        ⊆ ⋃ y ∈ Finset.Ico a (b - K + 1),
            {ω : ℕ → Bool | ∀ z ∈ Finset.Ico y (y + K), ω z = false} := by
      intro ω hω
      obtain ⟨y, hya, hyK, hy⟩ := SwarmRunLoc.not_runsOn_iff.mp hω
      exact Set.mem_biUnion (Finset.mem_Ico.mpr ⟨hya, by omega⟩) hy
    refine le_trans (measure_mono hsub) ?_
    refine le_trans (measure_biUnion_finset_le (Finset.Ico a (b - K + 1))
      (fun y => {ω : ℕ → Bool | ∀ z ∈ Finset.Ico y (y + K), ω z = false})) ?_
    rw [Finset.sum_congr rfl (fun y _ => SwarmRun.markMeasure_cyl_false hq0 hq1 y K),
      Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity :
        (0 : ℝ) ≤ (((Finset.Ico a (b - K + 1)).card : ℕ) : ℝ))]
    refine ENNReal.ofReal_le_ofReal ?_
    have hcard : ((Finset.Ico a (b - K + 1)).card : ℝ) ≤ ((b - a + 1 : ℕ) : ℝ) := by
      have h1 : (Finset.Ico a (b - K + 1)).card ≤ b - a + 1 := by
        rw [Nat.card_Ico]; omega
      exact_mod_cast h1
    exact mul_le_mul_of_nonneg_right hcard hqK

/-- **The window run event measured for every `N`**: `N·((B-A+1))·(1-q)^K`, with **no `r`**. -/
theorem arrayMeasure_runWindowLocal_compl_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (A B K : ℕ) (hK : 1 ≤ K) :
    (arrayMeasure N).real {U : Array N | ¬ runWindowLocal (N := N) p m A B K U}
      ≤ (N : ℝ) * (((B - A + 1 : ℕ) : ℝ) * (1 - (1 - p) ^ (m - 1)) ^ K) := by
  have hp0' : 0 < p := by linarith
  have hq0 : (0 : ℝ) ≤ (1 - p) ^ (m - 1) := by positivity
  have hq1 : (1 - p) ^ (m - 1) ≤ 1 := by
    have h1 : (0 : ℝ) ≤ 1 - p := by linarith
    exact pow_le_one₀ h1 (by linarith)
  have hmeas : MeasurableSet {ω : ℕ → Bool | ¬ SwarmRunLoc.RunsOn ω A B K} :=
    (measurableSet_runsOn A B K).compl
  have hsub : {U : Array N | ¬ runWindowLocal (N := N) p m A B K U}
      ⊆ ⋃ j ∈ (Finset.univ : Finset (Fin N)),
          {U : Array N | ¬ SwarmRunLoc.RunsOn (siteMarks p m U j) A B K} := by
    rintro U hU
    simp only [runWindowLocal, not_forall] at hU
    obtain ⟨j, hj⟩ := hU
    exact Set.mem_biUnion (Finset.mem_univ j) hj
  have hone : ∀ j : Fin N,
      (arrayMeasure N) {U : Array N | ¬ SwarmRunLoc.RunsOn (siteMarks p m U j) A B K}
        ≤ ENNReal.ofReal (((B - A + 1 : ℕ) : ℝ) * (1 - (1 - p) ^ (m - 1)) ^ K) := by
    intro j
    have hmp := measurePreserving_siteMarks (N := N) hp0' hp1 m j
    calc (arrayMeasure N) {U : Array N | ¬ SwarmRunLoc.RunsOn (siteMarks p m U j) A B K}
        = (Measure.map (fun U : Array N => siteMarks p m U j) (arrayMeasure N))
            {ω : ℕ → Bool | ¬ SwarmRunLoc.RunsOn ω A B K} :=
          (Measure.map_apply hmp.measurable hmeas).symm
      _ = (markMeasure (boolMeasure ((1 - p) ^ (m - 1))))
            {ω : ℕ → Bool | ¬ SwarmRunLoc.RunsOn ω A B K} := by rw [hmp.map_eq]
      _ ≤ ENNReal.ofReal (((B - A + 1 : ℕ) : ℝ) * (1 - (1 - p) ^ (m - 1)) ^ K) :=
          measure_not_runsOn_le hq0 hq1 A B K hK
  have hne : (arrayMeasure N) Set.univ ≠ ⊤ := by simp
  have hb : (arrayMeasure N) {U : Array N | ¬ runWindowLocal (N := N) p m A B K U}
      ≤ ENNReal.ofReal ((N : ℝ) * (((B - A + 1 : ℕ) : ℝ) * (1 - (1 - p) ^ (m - 1)) ^ K)) := by
    refine le_trans (measure_mono hsub) ?_
    refine le_trans (measure_biUnion_finset_le Finset.univ
      (fun j => {U : Array N | ¬ SwarmRunLoc.RunsOn (siteMarks p m U j) A B K})) ?_
    refine le_trans (Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hone j)) ?_
    have heq : ∑ _j ∈ (Finset.univ : Finset (Fin N)),
        ENNReal.ofReal (((B - A + 1 : ℕ) : ℝ) * (1 - (1 - p) ^ (m - 1)) ^ K)
        = ENNReal.ofReal ((N : ℝ) * (((B - A + 1 : ℕ) : ℝ)
            * (1 - (1 - p) ^ (m - 1)) ^ K)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← ENNReal.ofReal_natCast N, ← ENNReal.ofReal_mul (by positivity)]
    rw [heq]
  have hRHSnn : (0 : ℝ) ≤ (N : ℝ) *
      (((B - A + 1 : ℕ) : ℝ) * (1 - (1 - p) ^ (m - 1)) ^ K) := by
    have hqK : (0 : ℝ) ≤ (1 - (1 - p) ^ (m - 1)) ^ K := by
      have : (0 : ℝ) ≤ 1 - (1 - p) ^ (m - 1) := by linarith
      positivity
    positivity
  exact ENNReal.toReal_le_of_le_ofReal hRHSnn hb

end WindowPosLocal

namespace WindowPosLocal

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 6. The windowed good event and the movement carrier from the window run event -/

/-- **`GoodWWin` at `Bstar L` from `(locmax)`, `(sep)` and the *window* run event.**

`WindowPos.goodWWin_of_carrier_pos` with `hrun` at the window `[Astar r T L, r + T·L + 1]`
instead of the prefix `[0, r + T·L + 1]`.  Nothing else changes: the `(locmax)` `hfix` half,
`(sep)`, `ambGoodAll`, `LocMaxBad` and the position bound `Astar ≤ X` are untouched. -/
theorem goodWWin_of_carrier_local {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m r T L : ℕ} (hL : 1 ≤ L) (hr : (T + 2) * L + 2 ≤ r) {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    {A : Finset (Fin N)} (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    {n : ℕ} (hn1 : recTimeA p m U r ≤ n) (hn2 : n ≤ recTimeA p m U r + T * L)
    (hsep : Glue.Sep (PaperBlock.Xa p m U) A Aᶜ n)
    (hnb : U ∉ LocGroupSimul.LocMaxBad (N := N) p m r T L)
    {K : ℕ} (hK1 : 1 ≤ K) (hGnum : (K : ℝ) ≤ LocSumAct.xOf L * (1 - (1 - p) / p))
    (hrun : runWindowLocalRec (N := N) p m r T L K U) :
    SiteWindow.GoodWWin p m n A Aᶜ hA (RecClockLG.Bstar L) (RecClockLG.Astar r T L) U := by
  have hpne : p ≠ 0 := by linarith
  have hr1 : (T + 2) * L + 1 ≤ r := by omega
  have hx1 : (1 : ℝ) ≤ LocSumAct.xOf L := LocSumAct.one_le_xOf hL
  have hρ : (0 : ℝ) < 1 - (1 - p) / p := by
    rw [sub_pos, div_lt_one (by linarith)]
    linarith
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := by positivity
  have hGle : (K : ℝ) / (1 - (1 - p) / p) ≤ LocSumAct.xOf L := by
    rw [div_le_iff₀ hρ]
    linarith
  have hK : (A ∪ Aᶜ).Nonempty := ⟨Classical.arbitrary (Fin N), by simp⟩
  have hA' : ∀ i ∈ A, RecClockLG.Astar r T L ≤ (runMax p m U i n).toNat :=
    fun i _ => AstarPos.Astar_le_runMax_of_carrier hcarr hr1 hn1 hn2 i
  have hH : ∀ i ∈ A, ∀ v : ℕ, RecClockLG.Astar r T L ≤ v + 1 →
      v ≤ LocGroupQ.xTop p m n (A ∪ Aᶜ) hK U → hfix (omegaN p m U i) v ≤ LocSumAct.xOf L := by
    intro i _ v hv1 hv2
    rw [Loccoord.hfix_omegaN_eq_hof (p := p) hpne (m := m) (U := U) i v]
    exact AstarPos.hof_le_of_not_mem_locmax hnb
      (AstarPos.mem_locmax_window_of_carrier hcarr hr hn1 hn2 hK hv1 hv2)
  have hG : ∀ i ∈ A, ∀ u : ℕ, RecClockLG.Astar r T L ≤ u →
      u ≤ LocGroupQ.xTop p m n (A ∪ Aᶜ) hK U →
      Gtail p m U i u ((runMax p m U i n).toNat + 1) ≤
        2 + (K : ℝ) / (1 - (1 - p) / p) := by
    intro i _ u hu1 _
    refine Gtail_le_of_runsOn_target (N := N) hp0 hp1 (U := U) (i := i)
      (A := RecClockLG.Astar r T L) (B := r + T * L + 1) (R := (runMax p m U i n).toNat)
      (K := K) (u := u) hK1 (hrun i) (by omega) ?_
    have := WindowPos.runMax_toNat_le_of_carrier (N := N) hcarr hn1 hn2 i
    omega
  have hGnn : (0 : ℝ) ≤ 2 + (K : ℝ) / (1 - (1 - p) / p) := by
    have h1 : (0 : ℝ) ≤ (K : ℝ) / (1 - (1 - p) / p) := div_nonneg hKnn hρ.le
    linarith
  have hgood := WindowPos.goodWWin_of_locmax_pos (N := N) hp0 hp1.le A Aᶜ hA hAc
    disjoint_compl_right (AstarPos.sepSet_of_glueSep hcarr hr1 hn1 hn2 hsep) hx1 hGnn hA' hH hG
  refine CarrierWin.goodWWin_mono (N := N) hA ?_ hgood
  rw [AstarPos.Bstar_eq_add hL]
  refine max_le le_rfl ?_
  linarith

/-- **`MoveCarrierWin` with the window run event.**  `WindowPos.moveCarrierWin_of_carrier_pos`
with the prefix run event replaced by the window one. -/
theorem moveCarrierWin_of_carrier_local {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m r T L : ℕ} (hL : 1 ≤ L) (hr : (T + 2) * L + 2 ≤ r) {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (hamb : U ∈ Swarming.Enl.ambGoodAll (N := N) p m (r : ℤ) T L)
    (hnb : U ∉ LocGroupSimul.LocMaxBad (N := N) p m r T L)
    {K : ℕ} (hK1 : 1 ≤ K) (hGnum : (K : ℝ) ≤ LocSumAct.xOf L * (1 - (1 - p) / p))
    (hrun : runWindowLocalRec (N := N) p m r T L K U) :
    CarrierWin.MoveCarrierWin (N := N) p m r T L (RecClockLG.Astar r T L) U := by
  refine CarrierWin.moveCarrierWin_of_win (N := N) hp0 hp1 (AstarPos.one_le_Astar hr) hamb ?_ ?_
  · intro A hA hne s t hs hst ht hsepwin n hn
    have hAc : Aᶜ.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hnil
      exact hne ((Finset.compl_eq_empty_iff A).mp hnil)
    have hs1 : s ≤ n := (Finset.mem_Ico.mp hn).1
    have hs2 : n < t := (Finset.mem_Ico.mp hn).2
    have hn1 : recTimeA p m U r ≤ n := le_trans hs hs1
    have hn2 : n ≤ recTimeA p m U r + T * L := le_trans (le_of_lt hs2) ht
    exact goodWWin_of_carrier_local (n := n) hp0 hp1 hL hr hcarr hA hAc hn1 hn2
      (hsepwin n hs1 hs2) hnb hK1 hGnum hrun
  · intro n hn1 hn2 j
    exact AstarPos.Astar_le_X_of_carrier hcarr (by omega) hn1 hn2 j

/-- **The truncated movement carrier off `badAll`, with the window run event.**

`WindowPos.moveCarrierWinTrunc_of_badAll_pos` with `moveCarrierWin_of_carrier_pos` replaced by
`moveCarrierWin_of_carrier_local`, i.e. the run hypothesis is the single window event
`runWindowLocalRec p m r T L (Kc p L)` instead of the prefix event. -/
theorem moveCarrierWinTrunc_of_badAll_local {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {L₀ : ℕ}
    (hL₀ : ∀ L : ℕ, L₀ ≤ L → 1 ≤ AstarPos.Kc p L ∧
      (AstarPos.Kc p L : ℝ) ≤ LocSumAct.xOf L * (1 - (1 - p) / p))
    {L : ℕ} (hL : L₀ ≤ L) (hL2 : 2 ≤ L)
    {T : ℕ} {Cerr : ℝ} {r : ℕ} {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (hr : (T + 3) * L ≤ r)
    (hnot : U ∉ SingleBad.badAll (N := N) p m Cerr r T L)
    (hrun : runWindowLocalRec (N := N) p m r T L (AstarPos.Kc p L) U) :
    MWin.MoveCarrierWinTrunc (N := N) p m r T L (RecClockLG.Astar r T L) U := by
  have hr2 : (T + 2) * L + 2 ≤ r := by
    refine le_trans ?_ hr
    calc (T + 2) * L + 2 ≤ (T + 2) * L + L := Nat.add_le_add_left (by omega : 2 ≤ L) _
      _ = (T + 3) * L := by ring
  have hwin : CarrierWin.MoveCarrierWin (N := N) p m r T L (RecClockLG.Astar r T L) U :=
    moveCarrierWin_of_carrier_local (N := N) hp0 hp1 (by omega : 1 ≤ L) hr2 hcarr
      (SingleBad.ambGoodAll_of_not_mem_badAll hnot)
      (AstarPos.not_mem_LocMaxBad_of_not_mem_univBad
        (SingleBad.not_mem_univBad_of_not_mem_badAll hnot))
      (hL₀ L hL).1 (hL₀ L hL).2 hrun
  intro A hA hne s t hs hst ht hsep
  obtain ⟨hamb, hgW, hstep⟩ := hwin A hA hne s t hs hst ht hsep
  exact ⟨hamb, fun n hn => MWin.winTrunc_of_goodWWin (hgW n hn) (fun k => by
    exact SingleBad.Astar_succ_le_X_of_carrier (N := N) hcarr (by omega) (by omega)
      (le_trans hs (Finset.mem_Ico.mp hn).1)
      (le_trans (le_of_lt (Finset.mem_Ico.mp hn).2) ht) k), hstep⟩

end WindowPosLocal

namespace WindowPosLocal

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 7. The measured bad event with the window run lane: a `∀r` profile -/

/-- **The single measured bad event, with the *window* run lane.**  Identical to
`WindowPosAllN.badEventPos` except that the third component is `¬ runWindowLocalRec`, a run event
on the window `[Astar r T L, r + T·L + 1]` rather than the prefix `[0, r + T·L + 1]`. -/
noncomputable def badEventLocal (p : ℝ) (m : ℕ) (Cerr : ℝ) (r T L : ℕ) : Set (Array N) :=
  SingleBad.badAll (N := N) p m Cerr r T L
    ∪ WindowMeas.moveFailCanonAll (N := N) p m r T L (RecClockLG.Bstar L)
        (LocalGoodFamily.Cmax (N := N) p m)
        (LocalGoodFamily.betaOf (N := N) p m T L Cerr)
        ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4)) (RecClockLG.Astar r T L)
    ∪ {U : Array N | ¬ runWindowLocalRec (N := N) p m r T L (AstarPos.Kc p L) U}

/-- **The new bad event is a subset of the public one**: replacing the prefix run lane by the
window lane only removes points, never adds them. -/
theorem badEventLocal_subset_badEventPos {p : ℝ} {m : ℕ} {Cerr : ℝ} {r T L : ℕ} :
    badEventLocal (N := N) p m Cerr r T L ⊆ WindowPosAllN.badEventPos (N := N) p m Cerr r T L := by
  intro U hU
  rcases hU with h | h
  · rcases h with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
  · exact Or.inr (fun hc => h (runWindowLocalRec_of_runWindowPos hc))

/-- The window length in `r`-free form: `(r + T·L + 1) - Astar r T L + 1 ≤ (2T+2)·L + 3`. -/
theorem window_level_length {r T L : ℕ} (hr : (T + 3) * L ≤ r) (hL : 1 ≤ L) :
    (r + T * L + 1) - RecClockLG.Astar r T L + 1 ≤ (2 * T + 2) * L + 3 := by
  have hAst : RecClockLG.Astar r T L = r - ((T + 1 + 1) * L + 1) := AstarPos.Astar_eq_leftEdge
  have hTL : (T + 1 + 1) * L + 1 ≤ r := by
    have h1 : (T + 3) * L = (T + 1 + 1) * L + L := by ring
    omega
  have hAsum : RecClockLG.Astar r T L + ((T + 1 + 1) * L + 1) = r := by
    rw [hAst]
    exact Nat.sub_add_cancel hTL
  have hrw : r + T * L + 1
      = RecClockLG.Astar r T L + ((T + 1 + 1) * L + 1 + T * L + 1) := by omega
  rw [hrw, Nat.add_sub_cancel_left]
  have h2 : (T + 1 + 1) * L + T * L = (2 * T + 2) * L := by ring
  omega

/-- **The measured profile of `badEventLocal`, for all `r ≥ (T+3)L`.**

This is `WindowPosAllN.exists_badEventPos_le` with the restriction `r ≤ L²` **removed**: the run
lane's `r`-dependence is gone, and the lane is absorbed as a *degree-one* polynomial in `L`

    N·((2T+2)L + 3)·(1-q)^{Kc p L} ≤ N·(2T+4)·(L+1)·exf cQ L ,

with no reference to `r`.  The other two lanes (`badAll`, `moveFailCanonAll`) were already
`r`-free. -/
theorem exists_badEventLocal_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) {T : ℕ} (hT : 1 ≤ T) :
    ∃ Cerr : ℝ, 1 ≤ Cerr ∧ ∃ CT cT : ℝ, 0 < CT ∧ 0 < cT ∧ ∃ L₀ : ℕ,
      ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
        (arrayMeasure N).real (badEventLocal (N := N) p m Cerr r T L)
          ≤ CT * LocalGoodAll.exf cT L := by
  classical
  obtain ⟨Cerr, cL, hCerr1, hcL, L₁, hbadLS, hccLS⟩ :=
    LocalGoodFamily.commonLocsumFacts (N := N) hp0 hp1 hm T
  obtain ⟨CTb, cTb, hCTb, hcTb, Lb, hboundFam⟩ :=
    LocalGoodFamily.exists_famBad_le_at (N := N) hp0 hp1 hm hT hN
      (UniversalFamily.moveAllFam (N := N)) UniversalFamily.moveAllFam_ne
      UniversalFamily.moveAllFam_co (UniversalFamily.grpAllFam (N := N))
      UniversalFamily.grpAllFam_I UniversalFamily.grpAllFam_J UniversalFamily.grpAllFam_disj
      hCerr1 hcL hbadLS hccLS
  obtain ⟨CTa, ca, hCTa, hca, La, hboundA⟩ :=
    SingleBad.exists_measureReal_ambBadAll_le (N := N) (m := m) hp0.le hp1 (by omega) T
  obtain ⟨Lk, hLk⟩ := SingleBad.exists_Kc' hp0 hp1
  obtain ⟨cQ, hcQ, Lq, hpowQ⟩ := WindowMain.exists_pow_le_exfKc hp0 hp1 hm
  set cE : ℝ := WindowMeas.rateEnv T N with hcEdef
  have hcE : 0 < cE := WindowMeas.rateEnv_pos T N
  set cMin : ℝ := min (min (min cTb ca) (min cE cL)) cQ with hcMindef
  have hcMin : 0 < cMin := by
    rw [hcMindef]
    exact lt_min (lt_min (lt_min hcTb hca) (lt_min hcE hcL)) hcQ
  set cT : ℝ := cMin / 2 with hcTdef
  have hcT : 0 < cT := by rw [hcTdef]; linarith
  have hltT : ∀ x ∈ ({cTb, ca, cE, cL, cQ} : Finset ℝ), cT < x := by
    intro x hx
    have hx' : x = cTb ∨ x = ca ∨ x = cE ∨ x = cL ∨ x = cQ := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hx
    have hx0 : 0 < x := by
      rcases hx' with rfl | rfl | rfl | rfl | rfl
      · exact hcTb
      · exact hca
      · exact hcE
      · exact hcL
      · exact hcQ
    have hmin : cMin ≤ x := by
      rw [hcMindef]
      rcases hx' with h | h | h | h | h
      · subst h; simp
      · subst h; simp
      · subst h; simp
      · subst h; simp
      · subst h; simp
    rw [hcTdef]; linarith
  have hcTb' : cT < cTb := hltT cTb (by simp)
  have hca' : cT < ca := hltT ca (by simp)
  have hcE' : cT < cE := hltT cE (by simp)
  have hcL' : cT < cL := hltT cL (by simp)
  have hcQ' : cT < cQ := hltT cQ (by simp)
  obtain ⟨M1, hM1, hM1ge, Lm1, hm1⟩ := WindowAbsorb.exists_poly_mul_exf_le
    (C₁ := CTb + CTa) (c₀ := min cTb ca) (cT := cT) (by linarith) hcT
    (lt_min hcTb' hca') 0
  obtain ⟨M2, hM2, hM2ge, Lm2, hm2⟩ := WindowAbsorb.exists_poly_mul_exf_le
    (C₁ := (2 : ℝ) ^ N * 4 * ((T : ℝ) + 4) ^ 2) (c₀ := cE) (cT := cT)
    (by positivity) hcT hcE' 2
  obtain ⟨M3, hM3, hM3ge, Lm3, hm3⟩ := WindowAbsorb.exists_poly_mul_exf_le
    (C₁ := (2 : ℝ) ^ N * Cerr) (c₀ := cL) (cT := cT) (by positivity) hcT hcL' 0
  obtain ⟨M4, hM4, hM4ge, Lm4, hm4⟩ := WindowAbsorb.exists_poly_mul_exf_le
    (C₁ := (N : ℝ) * (2 * (T : ℝ) + 4)) (c₀ := cQ) (cT := cT)
    (by positivity) hcT hcQ' 1
  refine ⟨Cerr, hCerr1, M1 + M2 + M3 + M4, cT, by positivity, hcT,
    L₁ + Lb + La + Lk + Lq + Lm1 + Lm2 + Lm3 + Lm4 + 3, ?_⟩
  intro L hL r hr
  have hL₁ : L₁ ≤ L := by omega
  have hLb : Lb ≤ L := by omega
  have hLa : La ≤ L := by omega
  have hLk' : Lk ≤ L := by omega
  have hLq : Lq ≤ L := by omega
  have hLm1 : Lm1 ≤ L := by omega
  have hLm2 : Lm2 ≤ L := by omega
  have hLm3 : Lm3 ≤ L := by omega
  have hLm4 : Lm4 ≤ L := by omega
  have hL2 : 2 ≤ L := by omega
  have hL1 : 1 ≤ L := by omega
  have hTnn : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
  -- (1) `badAll`
  have h1 : (arrayMeasure N).real (SingleBad.badAll (N := N) p m Cerr r T L)
      ≤ M1 * LocalGoodAll.exf cT L := by
    refine le_trans (measureReal_union_le (μ := arrayMeasure N)
      (UniversalFamily.univBad (N := N) p m Cerr r T L)
      (Swarming.Enl.ambBadAll (N := N) p m (r : ℤ) T L)) ?_
    refine le_trans (add_le_add (hboundFam L hLb r hr) (hboundA L hLa r hr)) ?_
    refine le_trans (LocalGoodAll.exf_two hCTb.le hCTa.le hcTb hca L) ?_
    simpa only [pow_zero, mul_one] using hm1 L hLm1
  -- (2) the canonical `(locmove)` union
  have h2 : (arrayMeasure N).real
      (WindowMeas.moveFailCanonAll (N := N) p m r T L (RecClockLG.Bstar L)
        (LocalGoodFamily.Cmax (N := N) p m)
        (LocalGoodFamily.betaOf (N := N) p m T L Cerr)
        ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4)) (RecClockLG.Astar r T L))
      ≤ (M2 + M3) * LocalGoodAll.exf cT L := by
    have hmain := WindowMeas.measureReal_moveFailCanonAll_le (N := N) hp0 hp1 (m := m)
      (by omega) hT hCerr1 hcL hbadLS hccLS L (by omega) r hr
    rw [← hcEdef] at hmain
    refine le_trans hmain ?_
    have hpoly : ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2
        ≤ ((T : ℝ) + 4) ^ 2 * ((L : ℝ) + 1) ^ 2 := by
      have h := WindowMain.ofNat_cast_le T L
      have h0 : (0 : ℝ) ≤ (((T + 3) * L : ℕ) : ℝ) + 1 := by positivity
      have h0' : (0 : ℝ) ≤ ((T : ℝ) + 4) * ((L : ℝ) + 1) := by positivity
      nlinarith only [h, h0, h0']
    have hsplit : (2 : ℝ) ^ N * (4 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2
          * LocalGoodAll.exf (WindowMeas.rateEnv T N) L + Cerr * LocalGoodAll.exf cL L)
        ≤ ((2 : ℝ) ^ N * 4 * ((T : ℝ) + 4) ^ 2) * ((L : ℝ) + 1) ^ 2
            * LocalGoodAll.exf (WindowMeas.rateEnv T N) L
          + ((2 : ℝ) ^ N * Cerr) * LocalGoodAll.exf cL L := by
      have e1 : (2 : ℝ) ^ N * (4 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2
            * LocalGoodAll.exf (WindowMeas.rateEnv T N) L)
          ≤ ((2 : ℝ) ^ N * 4 * ((T : ℝ) + 4) ^ 2) * ((L : ℝ) + 1) ^ 2
            * LocalGoodAll.exf (WindowMeas.rateEnv T N) L := by
        have hpos : (0 : ℝ) < LocalGoodAll.exf (WindowMeas.rateEnv T N) L :=
          WindowAbsorb.exf_pos _ _
        have hstep : 4 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2
            ≤ 4 * (((T : ℝ) + 4) ^ 2 * ((L : ℝ) + 1) ^ 2) := by
          nlinarith only [hpoly]
        calc (2 : ℝ) ^ N * (4 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2
              * LocalGoodAll.exf (WindowMeas.rateEnv T N) L)
            = (2 : ℝ) ^ N * (4 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2)
              * LocalGoodAll.exf (WindowMeas.rateEnv T N) L := by ring
          _ ≤ (2 : ℝ) ^ N * (4 * (((T : ℝ) + 4) ^ 2 * ((L : ℝ) + 1) ^ 2))
              * LocalGoodAll.exf (WindowMeas.rateEnv T N) L := by
              apply mul_le_mul_of_nonneg_right _ hpos.le
              exact mul_le_mul_of_nonneg_left hstep (by positivity)
          _ = ((2 : ℝ) ^ N * 4 * ((T : ℝ) + 4) ^ 2) * ((L : ℝ) + 1) ^ 2
              * LocalGoodAll.exf (WindowMeas.rateEnv T N) L := by ring
      have e2 : (2 : ℝ) ^ N * (Cerr * LocalGoodAll.exf cL L)
          = ((2 : ℝ) ^ N * Cerr) * LocalGoodAll.exf cL L := by ring
      nlinarith only [e1, e2]
    refine le_trans hsplit ?_
    have hA2 := hm2 L hLm2
    have hB2 := hm3 L hLm3
    have h3' : ((2 : ℝ) ^ N * Cerr) * LocalGoodAll.exf cL L ≤ M3 * LocalGoodAll.exf cT L := by
      have := hB2
      simpa only [pow_zero, mul_one] using this
    have hpos2 : (0 : ℝ) < LocalGoodAll.exf cT L := WindowAbsorb.exf_pos _ _
    nlinarith only [hA2, h3', hpos2]
  -- (3) the *window* run lane: `r`-free
  have h3 : (arrayMeasure N).real
      {U : Array N | ¬ runWindowLocalRec (N := N) p m r T L (AstarPos.Kc p L) U}
      ≤ M4 * LocalGoodAll.exf cT L := by
    have hK : 1 ≤ AstarPos.Kc p L := (hLk L hLk').1
    have hrun := arrayMeasure_runWindowLocal_compl_le (N := N) (p := p) hp0 hp1 hm
      (RecClockLG.Astar r T L) (r + T * L + 1) (AstarPos.Kc p L) hK
    have hqnn : (0 : ℝ) ≤ (1 - (1 - p) ^ (m - 1)) ^ (AstarPos.Kc p L) := by
      have h1 : (0 : ℝ) ≤ 1 - p := by linarith
      have h2 : (1 - p) ^ (m - 1) ≤ 1 := pow_le_one₀ h1 (by linarith)
      have h3 : (0 : ℝ) ≤ 1 - (1 - p) ^ (m - 1) := by linarith
      positivity
    have hlen := window_level_length (r := r) (T := T) (L := L) hr hL1
    have hlenR : ((((r + T * L + 1) - RecClockLG.Astar r T L + 1 : ℕ)) : ℝ)
        ≤ (((2 * T + 2) * L + 3 : ℕ) : ℝ) := by exact_mod_cast hlen
    have hpow : (1 - (1 - p) ^ (m - 1)) ^ (AstarPos.Kc p L) ≤ LocalGoodAll.exf cQ L :=
      hpowQ L hLq
    have hpoly : ((N : ℝ) * ((((2 * T + 2) * L + 3 : ℕ)) : ℝ))
        ≤ ((N : ℝ) * (2 * (T : ℝ) + 4)) * ((L : ℝ) + 1) ^ 1 := by
      have hcast : ((((2 * T + 2) * L + 3 : ℕ)) : ℝ) = (2 * (T : ℝ) + 2) * (L : ℝ) + 3 := by
        push_cast
        ring
      rw [hcast, pow_one]
      have hLnn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
      have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      nlinarith only [hLnn, hNnn, hTnn]
    calc (arrayMeasure N).real
          {U : Array N | ¬ runWindowLocalRec (N := N) p m r T L (AstarPos.Kc p L) U}
        ≤ (N : ℝ) * ((((r + T * L + 1) - RecClockLG.Astar r T L + 1 : ℕ) : ℝ)
            * (1 - (1 - p) ^ (m - 1)) ^ (AstarPos.Kc p L)) := hrun
      _ ≤ (N : ℝ) * (((((2 * T + 2) * L + 3 : ℕ)) : ℝ)
            * (1 - (1 - p) ^ (m - 1)) ^ (AstarPos.Kc p L)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg N)
          exact mul_le_mul_of_nonneg_right hlenR hqnn
      _ ≤ (N : ℝ) * (((((2 * T + 2) * L + 3 : ℕ)) : ℝ) * LocalGoodAll.exf cQ L) := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg N)
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = ((N : ℝ) * ((((2 * T + 2) * L + 3 : ℕ)) : ℝ)) * LocalGoodAll.exf cQ L := by ring
      _ ≤ (((N : ℝ) * (2 * (T : ℝ) + 4)) * ((L : ℝ) + 1) ^ 1) * LocalGoodAll.exf cQ L := by
          refine mul_le_mul_of_nonneg_right hpoly (WindowAbsorb.exf_pos cQ L).le
      _ ≤ M4 * LocalGoodAll.exf cT L := hm4 L hLm4
  -- assemble
  have hbad : badEventLocal (N := N) p m Cerr r T L
      = SingleBad.badAll (N := N) p m Cerr r T L
        ∪ WindowMeas.moveFailCanonAll (N := N) p m r T L (RecClockLG.Bstar L)
            (LocalGoodFamily.Cmax (N := N) p m)
            (LocalGoodFamily.betaOf (N := N) p m T L Cerr)
            ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4)) (RecClockLG.Astar r T L)
        ∪ {U : Array N | ¬ runWindowLocalRec (N := N) p m r T L (AstarPos.Kc p L) U} := rfl
  rw [hbad]
  have h12 := measureReal_union_le (μ := arrayMeasure N)
    (SingleBad.badAll (N := N) p m Cerr r T L)
    (WindowMeas.moveFailCanonAll (N := N) p m r T L (RecClockLG.Bstar L)
      (LocalGoodFamily.Cmax (N := N) p m)
      (LocalGoodFamily.betaOf (N := N) p m T L Cerr)
      ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4)) (RecClockLG.Astar r T L))
  have h123 := measureReal_union_le (μ := arrayMeasure N)
    (SingleBad.badAll (N := N) p m Cerr r T L
      ∪ WindowMeas.moveFailCanonAll (N := N) p m r T L (RecClockLG.Bstar L)
          (LocalGoodFamily.Cmax (N := N) p m)
          (LocalGoodFamily.betaOf (N := N) p m T L Cerr)
          ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4)) (RecClockLG.Astar r T L))
    {U : Array N | ¬ runWindowLocalRec (N := N) p m r T L (AstarPos.Kc p L) U}
  have hsum1 : M1 * LocalGoodAll.exf cT L + (M2 + M3) * LocalGoodAll.exf cT L
      + M4 * LocalGoodAll.exf cT L
      = (M1 + M2 + M3 + M4) * LocalGoodAll.exf cT L := by ring
  rw [← hsum1]
  linarith [h123, h12, h1, h2, h3]

end WindowPosLocal

namespace WindowPosLocal

variable {N : ℕ} [Nonempty (Fin N)]

/-- **The same profile, written as the paper's own `(blkprob)` object**
`TightAvail.paperProfile CT cT L = ofReal (CT · e^{-cT L^{1/16}})`.

This is `exists_badEventLocal_le` transported from `μ.real` to `μ` and rewritten with
`LocSumAct.xOf L = L^{1/16}`; it is the literal shape consumed by the `(blkprob)` interface
`M4Term.PaperBadBlockProfile` (restricted here to the window bad event, not to `BadBlk`). -/
theorem exists_badEventLocal_paperProfile {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) {T : ℕ} (hT : 1 ≤ T) :
    ∃ Cerr : ℝ, 1 ≤ Cerr ∧ ∃ CT cT : ℝ, 0 < CT ∧ 0 < cT ∧ ∃ L₀ : ℕ,
      ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
        (arrayMeasure N) (badEventLocal (N := N) p m Cerr r T L)
          ≤ TightAvail.paperProfile CT cT L := by
  obtain ⟨Cerr, hCerr1, CT, cT, hCT, hcT, L₀, hbound⟩ :=
    exists_badEventLocal_le (N := N) hp0 hp1 hm hN hT
  refine ⟨Cerr, hCerr1, CT, cT, hCT, hcT, L₀, fun L hL r hr => ?_⟩
  have hne : (arrayMeasure N) (badEventLocal (N := N) p m Cerr r T L) ≠ ⊤ :=
    measure_ne_top _ _
  have h := hbound L hL r hr
  have hexp : LocalGoodAll.exf cT L = Real.exp (-(cT * (L : ℝ) ^ ((1 : ℝ) / 16))) := by
    rw [LocalGoodAll.exf, LocSumAct.xOf]
    congr 1
    ring
  rw [hexp] at h
  rw [TightAvail.paperProfile]
  calc (arrayMeasure N) (badEventLocal (N := N) p m Cerr r T L)
      = ENNReal.ofReal ((arrayMeasure N).real (badEventLocal (N := N) p m Cerr r T L)) :=
        (ENNReal.ofReal_toReal hne).symm
    _ ≤ ENNReal.ofReal (CT * Real.exp (-(cT * (L : ℝ) ^ ((1 : ℝ) / 16)))) :=
        ENNReal.ofReal_le_ofReal h

end WindowPosLocal

namespace WindowPosLocal

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 8. The paper's block clauses off the window bad event -/

/-- **The paper's local block clauses off `badEventLocal`.**

Verbatim `WindowPosAllN.blockClauses_of_not_bad_pos` with the finite-run hypothesis at the window
`[Astar r T L, r + T·L + 1]` and the movement carrier from
`moveCarrierWinTrunc_of_badAll_local`. -/
theorem blockClauses_of_not_bad_local {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) {T : ℕ} (hT : 1 ≤ T) {Cerr : ℝ} (hCerr1 : 1 ≤ Cerr) {Lk : ℕ}
    (hLk : ∀ L : ℕ, Lk ≤ L → 1 ≤ AstarPos.Kc p L ∧
      (AstarPos.Kc p L : ℝ) ≤ LocSumAct.xOf L * (1 - (1 - p) / p))
    {L : ℕ} (hL : Lk ≤ L) (hL2 : 2 ≤ L) {r : ℕ} (hr : (T + 3) * L ≤ r) {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (hnot : U ∉ SingleBad.badAll (N := N) p m Cerr r T L)
    (hrun : runWindowLocalRec (N := N) p m r T L (AstarPos.Kc p L) U)
    (hnotfail : U ∉ WindowMeas.moveFailCanonAll (N := N) p m r T L (RecClockLG.Bstar L)
      (LocalGoodFamily.Cmax (N := N) p m)
      (LocalGoodFamily.betaOf (N := N) p m T L Cerr)
      ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4)) (RecClockLG.Astar r T L))
    (hlocgroup : ∀ (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty), Disjoint I J →
      ∀ s t : ℕ, recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
      (∀ u ∈ Finset.Ico s t, SepSet p m u I J U) →
      WA p m U t I J hI hJ - WA p m U s I J hI hJ ≤ (L : ℝ) ^ ((3 : ℝ) / 4))
    (hsum : ∀ (j : Fin N) (a0 b0 : ℕ),
      LocOccCarrierAssembly.A0 r T L ≤ a0 →
      b0 ≤ LocOccCarrierAssembly.A0 r T L + LocOccCarrierAssembly.Lw T L → a0 ≤ b0 →
      ∑ x ∈ Finset.Ico a0 b0, (hof p (siteMarks p m U j) x) ^ 2
        ≤ 2 * LocOccSiteRate.Ccan p m * ((b0 : ℝ) - (a0 : ℝ))
          + 6 * LocOccSiteRate.Ccan p m
            * ((betaT (LocSumAct.xOf (LocOccCarrierAssembly.Lw T L)) : ℕ) : ℝ)) :
    BlkCoin.BlockClauses (Xa p m U) (tauA p m U) (Hc p m U)
      (Cfin (N := N) p m) (LocOccDerived.CTfin p m T Cerr) T L r := by
  have hL1 : 1 ≤ L := by omega
  have hnotu : U ∉ UniversalFamily.univBad (N := N) p m Cerr r T L :=
    SingleBad.not_mem_univBad_of_not_mem_badAll hnot
  -- the windowed move carrier, from the *window* run event
  have hcarrW : MWin.MoveCarrierWinTrunc (N := N) p m r T L (RecClockLG.Astar r T L) U :=
    moveCarrierWinTrunc_of_badAll_local (N := N) hp0 hp1 (m := m) (L₀ := Lk) hLk
      hL hL2 (T := T) (Cerr := Cerr) (r := r) (U := U) hcarr hr hnot hrun
  -- `(lococc)` derived
  have hocc : LocalFluid.LocOcc (Xa p m U) (tauA p m U) (Cfin (N := N) p m)
      (LocOccDerived.CTfin p m T Cerr) T L r :=
    LocOccDerived.locOcc_of_not_univBad (N := N) hp0 hp1 hm hT hL1 hr hcarr hnotu
  have hCTle : CTtot p m T Cerr ≤ LocOccDerived.CTfin p m T Cerr :=
    LocOccDerived.CTtot_le_CTfin p m T Cerr
  have hmono : ∀ (A : Finset (Fin N)) (n : ℕ) {x y : ℤ}, x ≤ y →
      Hc p m U A n x ≤ Hc p m U A n y :=
    fun A n _ _ hxy => Hc_mono p m U (le_of_lt hp0) (le_of_lt hp1) A n hxy
  have hunit : ∀ (A : Finset (Fin N)) (n : ℕ) {x y : ℤ}, x ≤ y →
      y - x ≤ Hc p m U A n y - Hc p m U A n x :=
    fun A n _ _ hxy => Hc_unit p m U (le_of_lt hp0) (le_of_lt hp1) A n hxy
  have hcoord : ∀ (A : Finset (Fin N)) (n : ℕ), A.Nonempty → A ≠ Finset.univ →
      tauA p m U r ≤ n → n ≤ tauA p m U r + T * L → ∀ a0 b0 : ℤ,
      (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ a0 → a0 ≤ b0 →
      b0 ≤ Glue.sMaxM (Xa p m U) A n →
      ((Hc p m U A n b0 - Hc p m U A n a0 : ℤ) : ℝ)
        ≤ Cfin (N := N) p m * ((b0 - a0 : ℤ) : ℝ)
          + LocOccDerived.CTfin p m T Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) := by
    intro A n hA _ h1 h2 a0 b0 ha hab hb
    have h := hcoord_clause_fin (N := N) hp0 hp1 hL1 hr hcarr hsum hCerr1
      A hA n h1 h2 a0 b0 ha hab hb
    have h2' := LocOccDerived.mul_CT_mono hCTle L
    linarith
  have hwmove : ∀ (A : Finset (Fin N)) (s t : ℕ), A.Nonempty → A ≠ Finset.univ →
      tauA p m U r ≤ s → s ≤ t → t ≤ tauA p m U r + T * L →
      (∀ u : ℕ, s ≤ u → u < t → Glue.Sep (Xa p m U) A (Finset.univ \ A) u) →
      Glue.Wst (Hc p m U) (Xa p m U) A (Finset.univ \ A) t
          - Glue.Wst (Hc p m U) (Xa p m U) A (Finset.univ \ A) s
        ≤ Cfin (N := N) p m
            * (((Glue.sMaxM (Xa p m U) A s : ℤ) : ℝ) - ((Glue.sMin (Xa p m U) A s : ℤ) : ℝ))
          - ((t - s : ℕ) : ℝ) / Cfin (N := N) p m
          + LocOccDerived.CTfin p m T Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) := by
    intro A s t hAn hAn' hs hst ht hsep
    have hAc : Aᶜ.Nonempty := by
      rw [UniversalFamily.compl_nonempty_iff_ne_univ]; exact hAn'
    have hgeom : ∀ s t : ℕ, recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
        U ∈ ClockLocMove.locCoordGeom p m A hAn r T L s t :=
      fun s t hs hst ht => mem_locCoordGeom_of_carrier (N := N) hcarr hr A hAn s t hs hst ht
    have hmove := WindowBlock.hmove_win_of_not_mem_win (p := p) (m := m) (A := A) (hA := hAn)
      (hAc := hAc)
      (r := r) (T := T) (L := L) (Cerr := Cerr) (ε₁ := (L : ℝ) ^ ((3 : ℝ) / 4))
      (ε₂ := (L : ℝ) ^ ((3 : ℝ) / 4)) (Aw := RecClockLG.Astar r T L)
      (geom := ClockLocMove.locCoordGeom p m A hAn r T L) hcarr
      (WindowMeas.not_mem_locMoveFailCanon_of_not_mem_moveFailCanonAll hnotfail A hAn hAc)
      (MWin.pin_of_carrier (N := N) hcarr hAn) hgeom
    have hbase := MWin.wmove_clause_win_fin (N := N) hp0 hp1 hL1 (Cerr := Cerr) hAn hAc
      (Aw := RecClockLG.Astar r T L) hmove s t hs hst ht
      (hcarrW A hAn hAn' s t hs hst ht hsep).1
      (hcarrW A hAn hAn' s t hs hst ht hsep).2.1
      (hcarrW A hAn hAn' s t hs hst ht hsep).2.2
    have h2' := LocOccDerived.mul_CT_mono hCTle L
    linarith
  refine ⟨⟨hmono, hunit, hcoord, hwmove, hocc⟩, ?_⟩
  intro I J hdisj hI hJ
  have hbase := group_clause (N := N) (Cerr := Cerr) hL1 hcarr hr hlocgroup I J hdisj hI hJ
  have h2' := LocOccDerived.mul_CT_mono hCTle L
  intro s t hs hst ht hsep
  have := hbase s t hs hst ht hsep
  linarith

/-- **One event, one `L`-only profile, block clauses off it — every `N ≥ 2`, every
`r ≥ (T+3)·L`.**

This is `WindowPosAllN.exists_badEventPos_blockClauses` with the restriction `r ≤ L²` **removed**
from the measured profile (and the finite-run lane at the window `[Astar r T L, r + T·L + 1]`).
The deterministically-quantified half is unchanged: it already held for all `r ≥ (T+3)L`. -/
theorem exists_badEventLocal_blockClauses {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) {T : ℕ} (hT : 1 ≤ T) :
    ∃ Cerr : ℝ, 1 ≤ Cerr ∧ ∃ CT cT : ℝ, 0 < CT ∧ 0 < cT ∧ ∃ L₀ : ℕ,
      (∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
        (arrayMeasure N).real (badEventLocal (N := N) p m Cerr r T L)
          ≤ CT * LocalGoodAll.exf cT L) ∧
      (∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r → ∀ U : Array N,
        U ∈ RecClockLG.recordCarrier (N := N) p m r L →
        U ∉ badEventLocal (N := N) p m Cerr r T L →
        BlkCoin.BlockClauses (Xa p m U) (tauA p m U) (Hc p m U)
          (Cfin (N := N) p m) (LocOccDerived.CTfin p m T Cerr) T L r) := by
  classical
  obtain ⟨Cerr, hCerr1, CT, cT, hCT, hcT, L₀, hmeas⟩ :=
    exists_badEventLocal_le (N := N) hp0 hp1 hm hN hT
  obtain ⟨Lk, hLk⟩ := SingleBad.exists_Kc' hp0 hp1
  obtain ⟨L₈, hL₈⟩ := LocalGoodFamily.familyGood_locgroup (N := N) hp0 hp1 hm hT
    (UniversalFamily.grpAllFam (N := N)) UniversalFamily.grpAllFam_I
    UniversalFamily.grpAllFam_J UniversalFamily.grpAllFam_disj
  obtain ⟨c₉, hc₉, L₉, h₉⟩ := LocSumR1.array_locsum_h_start (N := N) hp0 hp1 hm
    (C := LocOccSiteRate.Ccan p m) (LocOccSiteRate.one_le_Ccan p m)
    (LocOccSiteRate.Mb_lt_Ccan p m)
  obtain ⟨L₁₀, hL₁₀⟩ := LocOccCarrierAssembly.exists_two_mul_ellT_xOf_Lw_le T
  refine ⟨Cerr, hCerr1, CT, cT, hCT, hcT, L₀ + Lk + L₈ + L₉ + L₁₀ + 2, ?_, ?_⟩
  · intro L hL r hr
    exact hmeas L (by omega) r hr
  intro L hL r hr U hcarr hnot
  have hL8 : L₈ ≤ L := by omega
  have hL9 : L₉ ≤ L := by omega
  have hL10 : L₁₀ ≤ L := by omega
  have hLk' : Lk ≤ L := by omega
  have hL2 : 2 ≤ L := by omega
  have hnotbad : U ∉ SingleBad.badAll (N := N) p m Cerr r T L :=
    fun hc => hnot (Or.inl (Or.inl hc))
  have hnotfail : U ∉ WindowMeas.moveFailCanonAll (N := N) p m r T L (RecClockLG.Bstar L)
      (LocalGoodFamily.Cmax (N := N) p m)
      (LocalGoodFamily.betaOf (N := N) p m T L Cerr)
      ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4)) (RecClockLG.Astar r T L) :=
    fun hc => hnot (Or.inl (Or.inr hc))
  have hrun : runWindowLocalRec (N := N) p m r T L (AstarPos.Kc p L) U := by
    have hnotrun : ¬ ¬ runWindowLocalRec (N := N) p m r T L (AstarPos.Kc p L) U :=
      fun hc => hnot (Or.inr hc)
    exact Classical.not_not.mp hnotrun
  have hnotu : U ∉ UniversalFamily.univBad (N := N) p m Cerr r T L :=
    SingleBad.not_mem_univBad_of_not_mem_badAll hnotbad
  have hfam : U ∉ LocalGoodFamily.famBad (N := N) p m Cerr
      (UniversalFamily.moveAllFam (N := N)) UniversalFamily.moveAllFam_ne
      UniversalFamily.moveAllFam_co (UniversalFamily.grpAllFam (N := N))
      UniversalFamily.grpAllFam_I UniversalFamily.grpAllFam_J r T L := hnotu
  obtain ⟨⟨hcom, hmv⟩, hpair⟩ := LocalGoodFamily.not_mem_famBad hfam
  obtain ⟨hsumOcc, hocc, hlsC, hlocMax, hlocMart, hpot, hoccNull⟩ :=
    LocalGoodFamily.not_mem_commonBad hcom
  have hlocgroup : ∀ (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty), Disjoint I J →
      ∀ s t : ℕ, recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
      (∀ u ∈ Finset.Ico s t, SepSet p m u I J U) →
      WA p m U t I J hI hJ - WA p m U s I J hI hJ ≤ (L : ℝ) ^ ((3 : ℝ) / 4) := by
    intro I J hI hJ hdisj s t hs hst ht hsep
    have hq : (I, J) ∈ UniversalFamily.grpAllFam (N := N) :=
      UniversalFamily.mem_grpAllFam.mpr ⟨hI, hJ, hdisj⟩
    have h := hL₈ L hL8 r hr U hcarr hlocMax (LocalGoodFamily.familyGood_pot hfam) hpair
      (I, J) hq s t hs hst ht hsep
    rwa [show UniversalFamily.grpAllFam_I (I, J) hq = hI from Subsingleton.elim _ _,
      show UniversalFamily.grpAllFam_J (I, J) hq = hJ from Subsingleton.elim _ _] at h
  have hsum : ∀ (j : Fin N) (a0 b0 : ℕ),
      LocOccCarrierAssembly.A0 r T L ≤ a0 →
      b0 ≤ LocOccCarrierAssembly.A0 r T L + LocOccCarrierAssembly.Lw T L → a0 ≤ b0 →
      ∑ x ∈ Finset.Ico a0 b0, (hof p (siteMarks p m U j) x) ^ 2
        ≤ 2 * LocOccSiteRate.Ccan p m * ((b0 : ℝ) - (a0 : ℝ))
          + 6 * LocOccSiteRate.Ccan p m
            * ((betaT (LocSumAct.xOf (LocOccCarrierAssembly.Lw T L)) : ℕ) : ℝ) := by
    intro j a0 b0 ha0 hb0 hab
    have hside : 2 * ellT (LocSumAct.xOf (LocOccCarrierAssembly.Lw T L))
        ≤ LocOccCarrierAssembly.A0 r T L := by
      have hArith : L + (T + 2) * L ≤ r := by
        have hEq : L + (T + 2) * L = (T + 3) * L := by ring
        rw [hEq]; exact hr
      have hLA0 : L ≤ LocOccCarrierAssembly.A0 r T L := by
        unfold LocOccCarrierAssembly.A0
        exact Nat.le_sub_of_add_le hArith
      exact le_trans (hL₁₀ L hL10) hLA0
    exact (h₉ (LocOccCarrierAssembly.Lw T L)
      (le_trans hL9 (LocOccCarrierAssembly.le_Lw T L))
      (LocOccCarrierAssembly.A0 r T L) hside).2 U hsumOcc j a0 b0 ha0 hb0 hab
  exact blockClauses_of_not_bad_local (N := N) hp0 hp1 hm hT hCerr1 hLk hLk' hL2 hr
    hcarr hnotbad hrun hnotfail hlocgroup hsum

end WindowPosLocal
