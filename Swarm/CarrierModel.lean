/-
# The windowed `GoodWWin` carrier: an explicit probability at the actual array measure

`RunBound.lean` supplies, for the paper's mark law, an explicit combinatorial carrier on which
every site potential `h_j(x)` and every truncated forward potential `G_N(x)` inside a level window
is bounded by an explicit constant, with failure probability `N·b·(1-q)^K`
(`q = (1-p)^(m-1)`).  This file transports that carrier to the **actual array measure**
`Swarming.Uniform.arrayMeasure N` (the law of the whole interacting system) and feeds it into
`SiteWindow.goodWWin_of_locmax`, which takes the two *numeric* window hypotheses `hfix ≤ H` and
`Gtail ≤ G` and nothing else.

Two remarks on why the numeric hypotheses are the right interface.

* `SiteWindow.goodWWin_of_locmax_event` instead assumes `Gsup p ω y ≤ H` on the window, where
  `Gsup p ω y = ⨆ N, Gtrunc p ω N (y+1)` is a *real* supremum whose junk value is `0`; that
  hypothesis is therefore vacuous at an unbounded mark row and does not give
  `BddAbove (range fun N => Gtrunc …)`, which `Gtail_le_one_add_Gsup` needs.
  `goodWWin_of_locmax` avoids the issue entirely by taking the `Gtail` bound directly, and the
  `Gtail` bound is what `RunBound.Gtrunc_le_of_runs` provides in the window.
* `Gtail p m U i u (n+2) = 1 + Gsum …` is a *finite* sum over the sites `u, …, n+1`, so it is
  controlled by the run event up to level `n+2` — no global convergence statement is needed.

Main results:

* `arrayMeasure_carrier_compl_le` — the complement of the run carrier has
  `arrayMeasure`-probability at most `N·b·(1-q)^K`;
* `carrier_goodWWin` — on the carrier, `(sep)` plus the geometric hypothesis `A ≤ M_n^i`
  imply `GoodWWin` with the explicit threshold
  `B = max (2·H + 6) (2·G)`, `H = 1 + 2K + 2K/(1-ρ)`, `G = 2 + K/(1-ρ)`, `ρ = (1-p)/p`;
* `arrayMeasure_exception_le` — consequently, for every level window and every group splitting,
  the joint event `{(sep) ∧ A ≤ M_n^i ∧ ¬GoodWWin}` has `arrayMeasure`-probability at most
  `N·(n+3)·(1-q)^K`.

`(sep)` itself (equivalently `SepSet`) is the only input that is not produced here: the paper
also uses `(sep)` as a hypothesis, and `Swarm/SepWindow.lean` reduces its survival to
one-sided walker events without bounding them.

No `sorry`, no extra axiom, no `native_decide`.
-/
import Swarm.LocMaxWindow
import Swarm.RawLogRatio
import Swarm.RunBound

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance LocGroupQ SiteWindow
open SwarmMarks SwarmLogRatio

namespace SwarmCarrier

variable {N : ℕ} {p : ℝ}

/-! ### 1. Measurability of the run event -/

theorem measurableSet_runsOK (b K : ℕ) :
    MeasurableSet {ω : ℕ → Bool | SwarmRun.RunsOK ω b K} := by
  have h : {ω : ℕ → Bool | SwarmRun.RunsOK ω b K}
      = ⋂ y ∈ (Finset.range (b + 1)).filter (fun y => y + K ≤ b),
          ⋃ z ∈ Finset.Ico y (y + K), {ω : ℕ → Bool | ω z = true} := by
    ext ω
    simp only [SwarmRun.RunsOK, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion,
      Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro h y ⟨-, hyK⟩
      obtain ⟨z, hz, hztrue⟩ := h y hyK
      exact ⟨z, hz, hztrue⟩
    · rintro h y hyK
      obtain ⟨z, hz, hztrue⟩ := h y ⟨by omega, hyK⟩
      exact ⟨z, hz, hztrue⟩
  rw [h]
  refine Finset.measurableSet_biInter _ (fun y _ => ?_)
  exact Finset.measurableSet_biUnion _
    (fun z _ => measurableSet_eq_fun (measurable_pi_apply z) measurable_const)

theorem measurableSet_not_runsOK (b K : ℕ) :
    MeasurableSet {ω : ℕ → Bool | ¬ SwarmRun.RunsOK ω b K} :=
  (measurableSet_runsOK b K).compl

/-! ### 2. The carrier probability at the actual array measure -/

/-- One row of the actual array has the canonical i.i.d. mark law. -/
theorem arrayMeasure_row_compl_le (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m b K : ℕ) (hK : 1 ≤ K)
    (j : Fin N) :
    (arrayMeasure N) {U : Array N | ¬ SwarmRun.RunsOK (siteMarks p m U j) b K}
      ≤ ENNReal.ofReal ((b : ℝ) * (1 - (1 - p) ^ (m - 1)) ^ K) := by
  have hp0' : 0 < p := by linarith
  have hmp := measurePreserving_siteMarks (N := N) hp0' hp1 m j
  have hmeas := measurableSet_not_runsOK b K
  calc (arrayMeasure N) {U : Array N | ¬ SwarmRun.RunsOK (siteMarks p m U j) b K}
      = (Measure.map (fun U : Array N => siteMarks p m U j) (arrayMeasure N))
          {ω : ℕ → Bool | ¬ SwarmRun.RunsOK ω b K} :=
        (Measure.map_apply hmp.measurable hmeas).symm
    _ = (markMeasure (boolMeasure ((1 - p) ^ (m - 1))))
          {ω : ℕ → Bool | ¬ SwarmRun.RunsOK ω b K} := by rw [hmp.map_eq]
    _ ≤ ENNReal.ofReal ((b : ℝ) * (1 - (1 - p) ^ (m - 1)) ^ K) :=
        SwarmRun.measure_not_runsOK_le (q := (1 - p) ^ (m - 1))
          (by positivity)
          (pow_le_one₀ (by linarith : (0 : ℝ) ≤ 1 - p) (by linarith : 1 - p ≤ 1))
          b K hK

/-- **The carrier probability.**  The probability that some walker's mark row has a run of `K`
consecutive unmarked sites below level `b` is at most `N·b·(1-q)^K`, `q = (1-p)^(m-1)`. -/
theorem arrayMeasure_carrier_compl_le (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (b K : ℕ) (hK : 1 ≤ K) :
    (arrayMeasure N) {U : Array N | ∃ j : Fin N, ¬ SwarmRun.RunsOK (siteMarks p m U j) b K}
      ≤ ENNReal.ofReal ((N : ℝ) * ((b : ℝ) * (1 - (1 - p) ^ (m - 1)) ^ K)) := by
  have hsub : {U : Array N | ∃ j : Fin N, ¬ SwarmRun.RunsOK (siteMarks p m U j) b K}
      ⊆ ⋃ j ∈ Finset.univ,
          {U : Array N | ¬ SwarmRun.RunsOK (siteMarks p m U j) b K} := by
    intro U hU
    obtain ⟨j, hj⟩ := hU
    exact Set.mem_biUnion (Finset.mem_univ j) hj
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_biUnion_finset_le Finset.univ
    (fun j => {U : Array N | ¬ SwarmRun.RunsOK (siteMarks p m U j) b K})) ?_
  refine le_trans (Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    arrayMeasure_row_compl_le hp0 hp1 m b K hK j)) ?_
  have heq : ∑ j ∈ (Finset.univ : Finset (Fin N)),
      ENNReal.ofReal ((b : ℝ) * (1 - (1 - p) ^ (m - 1)) ^ K)
      = ENNReal.ofReal ((N : ℝ) * ((b : ℝ) * (1 - (1 - p) ^ (m - 1)) ^ K)) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast N, ← ENNReal.ofReal_mul (by positivity)]
  rw [heq]

/-! ### 3. The deterministic link to the windowed `GoodWWin` -/

/-- `Gtail` inside the record window, bounded by the run carrier. -/
theorem Gtail_le_of_runs {m : ℕ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (U : Array N) (i : Fin N) {n u K : ℕ} (hK : 1 ≤ K)
    (hrun : SwarmRun.RunsOK (siteMarks p m U i) (n + 3) K) (hu : u ≤ n + 2) :
    Gtail p m U i u (n + 2) ≤ 2 + (K : ℝ) / (1 - (1 - p) / p) := by
  have hp0 : p ≠ 0 := by linarith
  rcases lt_or_eq_of_le hu with hlt | heq
  · have h1 : Gtail p m U i u (n + 2) = 1 + Gsum p m U i u (n + 2) := rfl
    rw [h1, SiteWindow.Gsum_eq_Gtrunc hp0 U i hlt]
    have h2 : Gtrunc p (siteMarks p m U i) (n + 2 - u - 1) (u + 1)
        ≤ 1 + (K : ℝ) / (1 - (1 - p) / p) := by
      refine SwarmRun.Gtrunc_le_of_runs hp1 hp2 hK hrun ?_
      omega
    linarith
  · subst heq
    have h1 : Gtail p m U i (n + 2) (n + 2) = 1 + Gsum p m U i (n + 2) (n + 2) := rfl
    rw [h1, Gsum]
    have hempty : Finset.Ico (n + 2) (n + 2) = ∅ := by simp
    rw [hempty, Finset.sum_empty]
    have hnn : (0 : ℝ) ≤ (K : ℝ) / (1 - (1 - p) / p) := by
      have : (0 : ℝ) < 1 - (1 - p) / p := by
        rw [sub_pos, div_lt_one (by linarith)]; linarith
      positivity
    linarith

/-- **The windowed `GoodWWin` on the run carrier.**  Only the walkers of `I` need a bounded mark
row, because `goodWWin_of_locmax` quantifies over `i ∈ I`. -/
theorem carrier_goodWWin (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m n : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {U : Array N} (hsep : SepSet p m n I J U) {A K : ℕ} (hK : 1 ≤ K)
    (hrun : ∀ i ∈ I, SwarmRun.RunsOK (siteMarks p m U i) (n + 3) K)
    (hA : ∀ i ∈ I, A ≤ (runMax p m U i n).toNat) :
    GoodWWin p m n I J hI
      (max (2 * (1 + 2 * (K : ℝ) + 2 * ((K : ℝ) / (1 - (1 - p) / p))) + 6)
        (2 * (2 + (K : ℝ) / (1 - (1 - p) / p)))) A U := by
  have hp0' : (1 : ℝ) / 2 < p := hp0
  have hp1' : p ≤ 1 := le_of_lt hp1
  have hpne : p ≠ 0 := by linarith
  have hden : (0 : ℝ) < 1 - (1 - p) / p := by
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := by positivity
  have hq : (0 : ℝ) ≤ (K : ℝ) / (1 - (1 - p) / p) := by positivity
  have hH1 : (1 : ℝ) ≤ 1 + 2 * (K : ℝ) + 2 * ((K : ℝ) / (1 - (1 - p) / p)) := by
    nlinarith
  have hGnn : (0 : ℝ) ≤ 2 + (K : ℝ) / (1 - (1 - p) / p) := by linarith
  refine goodWWin_of_locmax hp0 hp1' I J hI hJ hid hsep hH1 hGnn hA ?_ ?_
  · intro i hi v hv1 hv2
    rw [Loccoord.hfix_omegaN_eq_hof hpne]
    refine SwarmRun.hof_le_of_runs hp0' hp1 hK (hrun i hi) ?_
    have hlt := xTop_lt_range p m n (I ∪ J) (hI.mono Finset.subset_union_left) U
    omega
  · intro i hi u hu1 hu2
    refine le_trans (Gtail_le_of_runs hp0' hp1 U i hK (hrun i hi) ?_) (le_refl _)
    have hlt := xTop_lt_range p m n (I ∪ J) (hI.mono Finset.subset_union_left) U
    omega

/-! ### 4. The exception profile -/

/-- **The carrier probability of the corrected `GoodWWin`, per instance.**  For every `n`, every
disjoint nonempty pair of groups and every level window edge `A`, the joint event
`{(sep) ∧ ∀ i ∈ I, A ≤ M_n^i ∧ ¬GoodWWin}` has `arrayMeasure`-probability at most
`N·(n+3)·(1-q)^K`.  Inside the record window (`xTop ≤ r+1`, `A ≥ r-(T+3)L`) the geometric
hypothesis `A ≤ M_n^i` is what `d_r ≤ L` supplies. -/
theorem arrayMeasure_exception_le (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m n : ℕ} (hm : 2 ≤ m)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J) {A K : ℕ}
    (hK : 1 ≤ K) :
    (arrayMeasure N) {U : Array N | SepSet p m n I J U ∧
        (∀ i ∈ I, A ≤ (runMax p m U i n).toNat) ∧
        ¬ GoodWWin p m n I J hI
          (max (2 * (1 + 2 * (K : ℝ) + 2 * ((K : ℝ) / (1 - (1 - p) / p))) + 6)
            (2 * (2 + (K : ℝ) / (1 - (1 - p) / p)))) A U}
      ≤ ENNReal.ofReal ((N : ℝ) * (((n + 3 : ℕ) : ℝ) * (1 - (1 - p) ^ (m - 1)) ^ K)) := by
  refine le_trans (measure_mono ?_) (arrayMeasure_carrier_compl_le hp0 hp1 hm (n + 3) K hK)
  intro U hU
  obtain ⟨hsep, hA, hng⟩ := hU
  by_contra hcon
  simp only [Set.mem_setOf_eq, not_exists, not_not] at hcon
  exact hng (carrier_goodWWin hp0 hp1 I J hI hJ hid hsep hK (fun i _ => hcon i) hA)

end SwarmCarrier
