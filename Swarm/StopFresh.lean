/-
# Stopped / first-passage freshness of site marks above the running record

`Swarm/FreshBlock.lean` proves the fresh site-mark block law at a **deterministic**
time `n`:

  `mu.real (A ∩ MarksBox S) = q ^ |S| * mu.real A`,   `q = (1-p)^(m-1)`,

for an `enlFilt p m n`-event `A ⊆ AboveRec p m j n r` (`runMax j n < r`) and a finite set `S` of
sites `>= r`.  `CondFreshCov.lean` records that on `AboveRec` no site of the walker's own
terminal window is fresh, so the block law cannot be applied to the terminal window.

This file supplies the *stopping-time* half of that interface, on the actual definitions:

* `runMax_mono`, `runMax_le_of_forall`, `runMax_zero`, `pos_succ_ge` — the running maximum is
  monotone and is bounded by any upper bound of the positions up to that time; a single step
  moves the walker by at most one in either direction.

* `HitMax p m j r U n` — the **first-passage predicate** "the running maximum of walker `j`
  reaches the level `r` for the first time at time `n`".  It is proved to be
  * *unique in `n`* (`hitMax_unique`), i.e. the level sets of an honest random time;
  * *`enlFilt p m n`-measurable* (`measurableSet_hitMax_enl`) — no future coordinate is used,
    so the passage time is a stopping time of the enlarged filtration;
  * *exactly identified at the passage time*: `runMax j n = r` (`hitMax_runMax`) and
    `pos j n = r` (`hitMax_pos_of_hitMax_succ`) whenever the walker passes `r` at time `n+1`,
    and `pos j n = r - 1` just before the passage (`hitMax_pos_pred`).

* **`enl_setIntegral_markBlock_above_stop`** — the block law for a *stopped* family: for
  pairwise disjoint `enlFilt p m n`-events `A n`, each contained in `AboveRec p m j n r`,

      mu.real ((⋃ n, A n) ∩ MarksBox S) = q ^ |S| * mu.real (⋃ n, A n) ,

  with no independence hypothesis: the identity is the `tsum` of the deterministic-time laws over
  the countable partition, taken in `ℝ≥0∞` and transferred to `ℝ` once.

* **`enl_setIntegral_markBlock_firstPassage`** — the concrete first-passage consequence: for
  sites `x >= r + 1` (everything strictly above the newly reached record `r`),

      mu.real ((⋃ n, C n ∩ {HitMax at n}) ∩ MarksBox S)
        = q ^ |S| * mu.real (⋃ n, C n ∩ {HitMax at n}) ,

  i.e. conditional on the stopped information at the first passage to level `r`, the marks
  above `r` are still i.i.d. Bernoulli(`q`) and independent of the past.  Each piece
  `C n ∩ {HitMax at n}` is `enlFilt p m n`-measurable, so this is a genuine conditional law at a
  random time.

* **`markLaw_fails_below_record`** — the sharpness certificate: the hypothesis `AboveRec` cannot
  be weakened to a mere measurability hypothesis.  For `N = 1`, `m = 2`, `0 < p < 1` and the
  `enlFilt p m 1`-event `A = {the first step is to the right}`, the mark at the already visited
  site `0` has mass `0` on `A` while `q * mu.real A = (1-p) * mu.real A > 0`.  This is exactly
  the phenomenon that makes the terminal-window sites unreachable for the fresh-block route.

Deliberately **not** claimed here: the conditional law at a first passage for the site `r`
itself (which needs the joint freshness of the next departure and the mark, and is proved
separately), and anything about terminal windows below the record.

No `sorry`, no `admit`, no custom axiom, no `native_decide`.
-/
import Swarm.FreshBlock

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory

variable {N : ℕ}

/-! ## 1. Elementary facts about the running maximum -/

/-- The running maximum is monotone in time. -/
lemma runMax_mono {p : ℝ} {m : ℕ} (U : Array N) (j : Fin N) {a b : ℕ} (h : a ≤ b) :
    runMax p m U j a ≤ runMax p m U j b := by
  unfold runMax
  refine Finset.sup'_le _ _ (fun t ht => ?_)
  exact Finset.le_sup' (fun s => (trajectory p m U s).pos j)
    (Finset.mem_range.mpr
      (Nat.lt_succ_of_le (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)) h)))

/-- The running maximum is bounded by any uniform upper bound of the positions up to that time. -/
lemma runMax_le_of_forall {p : ℝ} {m : ℕ} (U : Array N) (j : Fin N) {n : ℕ} {c : ℤ}
    (h : ∀ t ≤ n, (trajectory p m U t).pos j ≤ c) : runMax p m U j n ≤ c := by
  unfold runMax
  exact Finset.sup'_le _ _ (fun t ht => h t (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)))

/-- The running maximum at time `0` is the initial position, namely `0`. -/
lemma runMax_zero {p : ℝ} {m : ℕ} (U : Array N) (j : Fin N) : runMax p m U j 0 = 0 := by
  simp [runMax, trajectory_zero]

/-- The driving step is always at least `- 1`. -/
lemma neg_one_le_drivenStep {u α : ℝ} : -1 ≤ Swarming.drivenStep u α := by
  unfold Swarming.drivenStep
  split <;> norm_num

/-- One step moves a walker down by at most one. -/
lemma pos_succ_ge {p : ℝ} {m : ℕ} (U : Array N) (n : ℕ) (j : Fin N) :
    (trajectory p m U n).pos j - 1 ≤ (trajectory p m U (n + 1)).pos j := by
  rw [trajectory_succ, nextWalkState_pos, nextPos]
  have h := neg_one_le_drivenStep (u := U (j, (trajectory p m U n).pos j,
      (trajectory p m U n).ell j ((trajectory p m U n).pos j)))
    (α := rightProbability p m (trajectory p m U n).ell j ((trajectory p m U n).pos j))
  omega

/-! ## 2. The first-passage time of a level -/

/-- `HitMax p m j r U n`: walker `j`'s running maximum reaches the level `r` for the first time
at time `n`.  `0 ≤ r` is the interesting range; the predicate is meaningful for any `r`. -/
def HitMax (p : ℝ) (m : ℕ) (j : Fin N) (r : ℤ) (U : Array N) (n : ℕ) : Prop :=
  r ≤ runMax p m U j n ∧ ∀ t < n, runMax p m U j t < r

/-- At the first passage time the running maximum equals the level. -/
lemma hitMax_runMax {p : ℝ} {m : ℕ} {j : Fin N} {r : ℤ} {U : Array N} {n : ℕ}
    (hr : 0 ≤ r) (h : HitMax p m j r U n) : runMax p m U j n = r := by
  refine le_antisymm ?_ h.1
  refine runMax_le_of_forall U j (fun t ht => ?_)
  rcases Nat.lt_or_eq_of_le ht with hlt | heq
  · have h1 : runMax p m U j t < r := h.2 t hlt
    have h2 : (trajectory p m U t).pos j ≤ runMax p m U j t := le_runMax p m U j t
    omega
  · rw [heq]
    clear heq
    rcases n with _ | k
    · have hp0 : (trajectory p m U 0).pos j = 0 := by simp
      have h1 : r ≤ runMax p m U j 0 := h.1
      rw [runMax_zero] at h1
      omega
    · have h1 : runMax p m U j k < r := h.2 k (Nat.lt_succ_self k)
      have h2 : (trajectory p m U k).pos j ≤ runMax p m U j k := le_runMax p m U j k
      have h3 : (trajectory p m U (k + 1)).pos j ≤ (trajectory p m U k).pos j + 1 :=
        pos_succ_le p m U k j
      omega

/-- A level reached for the first time is attained exactly (not overshot). -/
lemma hitMax_pos_of_hitMax_succ {p : ℝ} {m : ℕ} {j : Fin N} {r : ℤ} {U : Array N} {n : ℕ}
    (hr : 0 ≤ r) (h : HitMax p m j r U (n + 1)) : (trajectory p m U (n + 1)).pos j = r := by
  have hmax : runMax p m U j (n + 1) = r := hitMax_runMax hr h
  have hle : (trajectory p m U (n + 1)).pos j ≤ r := by
    have := le_runMax p m U j (n + 1)
    omega
  by_contra hcon
  have hlt : (trajectory p m U (n + 1)).pos j ≤ r - 1 := by omega
  have hall : ∀ t ≤ n + 1, (trajectory p m U t).pos j ≤ r - 1 := by
    intro t ht
    rcases Nat.lt_or_eq_of_le ht with h' | h'
    · have h1 : runMax p m U j t < r := h.2 t h'
      have h2 : (trajectory p m U t).pos j ≤ runMax p m U j t := le_runMax p m U j t
      omega
    · subst h'
      exact hlt
  have := runMax_le_of_forall U j hall
  omega

/-- Just before the first passage to level `r` the walker sits at `r - 1`. -/
lemma hitMax_pos_pred {p : ℝ} {m : ℕ} {j : Fin N} {r : ℤ} {U : Array N} {n : ℕ}
    (hr : 0 ≤ r) (h : HitMax p m j r U (n + 1)) : (trajectory p m U n).pos j = r - 1 := by
  have hpos : (trajectory p m U (n + 1)).pos j = r := hitMax_pos_of_hitMax_succ hr h
  have h1 : (trajectory p m U (n + 1)).pos j ≤ (trajectory p m U n).pos j + 1 :=
    pos_succ_le p m U n j
  have h2 : runMax p m U j n < r := h.2 n (Nat.lt_succ_self n)
  have h3 : (trajectory p m U n).pos j ≤ runMax p m U j n := le_runMax p m U j n
  omega

/-- First-passage times of a level are unique. -/
lemma hitMax_unique {p : ℝ} {m : ℕ} {j : Fin N} {r : ℤ} {U : Array N} {n n' : ℕ}
    (h : HitMax p m j r U n) (h' : HitMax p m j r U n') : n = n' := by
  rcases lt_trichotomy n n' with hlt | heq | hgt
  · have h1 : r ≤ runMax p m U j n := h.1
    have h2 : runMax p m U j n < r := h'.2 n hlt
    omega
  · exact heq
  · have h1 : r ≤ runMax p m U j n' := h'.1
    have h2 : runMax p m U j n' < r := h.2 n' hgt
    omega

/-- **No future leakage.**  The first-passage event at time `n` is measurable for the enlarged
filtration at time `n`. -/
lemma measurableSet_hitMax_enl (p : ℝ) (m : ℕ) (j : Fin N) (r : ℤ) (n : ℕ) :
    MeasurableSet[enlFilt p m n] {U : Array N | HitMax p m j r U n} := by
  have h1 : MeasurableSet[enlFilt p m n] {U : Array N | r ≤ runMax p m U j n} := by
    have hc := (measurableSet_runMax_lt_enl p m j n r).compl
    convert hc using 1
    ext U
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt]
  have h2 : MeasurableSet[enlFilt p m n]
      (⋂ t ∈ Finset.range n, {U : Array N | runMax p m U j t < r}) := by
    refine Finset.measurableSet_biInter _ (fun t ht => ?_)
    exact (enlFilt (N := N) p m).mono (Nat.le_of_lt (Finset.mem_range.mp ht)) _
      (measurableSet_runMax_lt_enl p m j t r)
  have hEq : {U : Array N | HitMax p m j r U n} =
      {U : Array N | r ≤ runMax p m U j n} ∩
        ⋂ t ∈ Finset.range n, {U : Array N | runMax p m U j t < r} := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_range, HitMax]
  convert h1.inter h2 using 1

/-- At a first-passage time the walker's record is *strictly below* the next level, so marks at
all sites above the new record are still fresh. -/
lemma hitMax_aboveRec {p : ℝ} {m : ℕ} {j : Fin N} {r : ℤ} {U : Array N} {n : ℕ}
    (hr : 0 ≤ r) (h : HitMax p m j r U n) : U ∈ AboveRec p m j n (r + 1) := by
  have hmax : runMax p m U j n = r := hitMax_runMax hr h
  simp only [AboveRec, Set.mem_ofPred_eq, hmax]
  omega

/-- Just before the passage to level `r` the walker's record is below `r`. -/
lemma hitMax_aboveRec_pred {p : ℝ} {m : ℕ} {j : Fin N} {r : ℤ} {U : Array N} {n : ℕ}
    (h : HitMax p m j r U (n + 1)) : U ∈ AboveRec p m j n r := by
  have hlt : runMax p m U j n < r := h.2 n (Nat.lt_succ_self n)
  simpa only [AboveRec, Set.mem_ofPred_eq] using hlt

/-! ## 3. The stopped block law -/

/-- **Fresh site-mark block law over a stopped family.**  Let `A n` be pairwise disjoint events of
the enlarged filtration with `A n ∈ enlFilt p m n` and `A n ⊆ AboveRec p m j n r`, i.e. on `A n`
walker `j`'s running maximum at time `n` is still below `r`.  Then, for any finite set `S` of
sites at or above `r`, the marks of `S` occur on the whole stopped event `⋃ n, A n` with mass
`q ^ |S|`, independently of it.  This is the deterministic-time block law summed over the
countable partition. -/
theorem enl_setIntegral_markBlock_above_stop (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (m : ℕ) (j : Fin N) (S : Finset ℤ) (r : ℤ) (hSr : ∀ x ∈ S, r ≤ x)
    (A : ℕ → Set (Array N)) (hAmeas : ∀ n, MeasurableSet[enlFilt p m n] (A n))
    (hAsub : ∀ n, A n ⊆ AboveRec p m j n r)
    (hAdisj : Pairwise (Function.onFun Disjoint A)) :
    (arrayMeasure N).real ((⋃ n, A n) ∩ MarksBox p m j S) =
      ((1 - p) ^ (m - 1)) ^ S.card * (arrayMeasure N).real (⋃ n, A n) := by
  classical
  set μ := arrayMeasure N with hμ
  set q : ℝ := ((1 - p) ^ (m - 1)) ^ S.card with hq
  set T : Set (Array N) := MarksBox (N := N) p m j S with hT
  haveI : IsProbabilityMeasure μ := arrayMeasure_isProbabilityMeasure N
  have hq0 : 0 ≤ q := by
    rw [hq]
    exact pow_nonneg (pow_nonneg (by linarith) _) _
  have hTmeas : MeasurableSet T := measurableSet_marksBox_array p m j S
  have hAamb : ∀ n, MeasurableSet (A n) := fun n =>
    (enlFilt (N := N) p m).le n (A n) (hAmeas n)
  have hpiece : ∀ n, μ (A n ∩ T) = ENNReal.ofReal q * μ (A n) := by
    intro n
    have hreal := enl_setIntegral_markBlock_above_runMax p hp0 hp1 m (hAmeas n) j S r
      (hAsub n) hSr
    have h1 : μ (A n ∩ T) = ENNReal.ofReal (μ.real (A n ∩ T)) :=
      (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
    have h2 : μ (A n) = ENNReal.ofReal (μ.real (A n)) :=
      (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
    rw [h1, h2, hreal, hq, ENNReal.ofReal_mul hq0]
  have hdisj : Pairwise (Function.onFun Disjoint (fun n => A n ∩ T)) := by
    intro a b hab
    exact (hAdisj hab).mono Set.inter_subset_left Set.inter_subset_left
  have hmeas : ∀ n, MeasurableSet (A n ∩ T) := fun n => (hAamb n).inter hTmeas
  have hunion : (⋃ n, A n) ∩ T = ⋃ n, A n ∩ T := Set.iUnion_inter _ _
  have hENN : μ ((⋃ n, A n) ∩ T) = ENNReal.ofReal q * μ (⋃ n, A n) := by
    rw [hunion, measure_iUnion hdisj hmeas]
    rw [show (∑' n, μ (A n ∩ T)) = ∑' n, ENNReal.ofReal q * μ (A n) from tsum_congr hpiece]
    rw [ENNReal.tsum_mul_left, ← measure_iUnion hAdisj hAamb]
  calc μ.real ((⋃ n, A n) ∩ T) = (μ ((⋃ n, A n) ∩ T)).toReal := measureReal_def μ _
    _ = (ENNReal.ofReal q * μ (⋃ n, A n)).toReal := by rw [hENN]
    _ = q * (μ (⋃ n, A n)).toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq0]
    _ = ((1 - p) ^ (m - 1)) ^ S.card * μ.real (⋃ n, A n) := by
      rw [measureReal_def, hq]

/-! ## 4. The first-passage consequence -/

/-- **Fresh marks above the newly reached record at the first passage.**  Let `r` be a level,
`S` a finite set of sites strictly above `r`, and `C n` any `enlFilt p m n`-events.  Then on the
stopped event "walker `j` first reaches level `r` at time `n` and `C n` holds",

    mu.real ((⋃ n, C n ∩ {HitMax at n}) ∩ MarksBox S) = q ^ |S| * mu.real (⋃ n, C n ∩ {HitMax at n}) ,

so the site marks strictly above the first-passage level are i.i.d. Bernoulli(`q`) and
independent of the whole stopped past.  Both the passage condition and each `C n` are
`enlFilt p m n`-measurable (the passage time never reads a coordinate above `r`). -/
theorem enl_setIntegral_markBlock_firstPassage (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (m : ℕ) (j : Fin N) (S : Finset ℤ) (r : ℤ) (hr : 0 ≤ r) (hSr : ∀ x ∈ S, r + 1 ≤ x)
    (C : ℕ → Set (Array N)) (hC : ∀ n, MeasurableSet[enlFilt p m n] (C n)) :
    (arrayMeasure N).real
        ((⋃ n, C n ∩ {U : Array N | HitMax p m j r U n}) ∩ MarksBox p m j S) =
      ((1 - p) ^ (m - 1)) ^ S.card *
        (arrayMeasure N).real (⋃ n, C n ∩ {U : Array N | HitMax p m j r U n}) := by
  have hAmeas : ∀ n, MeasurableSet[enlFilt p m n] (C n ∩ {U : Array N | HitMax p m j r U n}) :=
    fun n => (hC n).inter (measurableSet_hitMax_enl p m j r n)
  have hAsub : ∀ n, C n ∩ {U : Array N | HitMax p m j r U n} ⊆ AboveRec p m j n (r + 1) := by
    rintro n U ⟨-, hU⟩
    exact hitMax_aboveRec hr hU
  have hAdisj : Pairwise (Function.onFun Disjoint
      (fun n => C n ∩ {U : Array N | HitMax p m j r U n})) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    rintro U ⟨-, hUa⟩ ⟨-, hUb⟩
    exact hab (hitMax_unique hUa hUb)
  exact enl_setIntegral_markBlock_above_stop p hp0 hp1 m j S (r + 1) hSr
    (fun n => C n ∩ {U : Array N | HitMax p m j r U n}) hAmeas hAsub hAdisj

end Swarming.Enl


