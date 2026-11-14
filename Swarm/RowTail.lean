/-
# Geometric failure continuation for the adaptive strict-attempt row tower

`Swarm/AttemptTower.lean` (namespace `SwarmAttemptTower`) supplies the tower
`S_q, T_q` of attempt rows on the literal actual array, and the row-level escape identity
`measure_T_top`:  `μ(A_q ∩ {T_q = ⊤}) = P(V) · μ(A_q)`.

`Swarm/ActualPathTransfer.lean` supplies the R1 transfer
`ae_frequently_all_walkers_at_level`: from the genuine two-block / `dT`-tightness inputs, almost
surely infinitely many record levels `r` are *simultaneous* records (every walker sits exactly at
the record level `r` at the canonical record time `recTimeA r`).

This file finishes the geometric row argument:

* `RowRecurrence` — the genuine a.e. "simultaneous records occur after every finite time"
  statement, **derived** from `ae_frequently_all_walkers_at_level` (via `ReachAll`, the
  level/time inequality `r ≤ τ_r` and the discrete intermediate value property of the running
  maximum).  It is not an assumption;
* `Aq_succ_eq` — under `RowRecurrence`, `A_{q+1} = {T_q ≠ ⊤}` exactly;
* `measure_Aq_succ`, `measure_Aq` — `μ(A_{q+1}) = (1 - P(V)) μ(A_q)`, hence
  `μ(A_q) = (1 - P(V))^q` and `μ(⋂_q A_q) = 0` for `P(V) > 0`;
* `ae_exists_completed_row` — almost surely there is a *first* row that starts and never
  returns: `∃ q, S_q < ∞ ∧ T_q = ⊤` (and all earlier rows return);
* `ae_exists_regenAtStrict` / `ae_exists_regenAtRecTime` — the paper's regeneration:
  almost surely there is a time/level `(t,d)` with `RegenAtStrict` (a record with a strictly
  positive future), in canonical form at a record time `recTimeA r` with the level `r`.

Honest scope.  There is **no** claim here of a positive-*level* canonical attempt on the
whole space: the tower's row `0` starts at level `0` (`S 0 = 0`, `levAt 0 = 0`), and if it
never returns then no later row is ever started (`S_{q+1} = ⊤`), so `r = 0` is a genuine
regeneration at the origin and the canonical positive-level attempt `StrictAttempt (r-1)`
exists only in the branch `r ≥ 1`.  See `ae_exists_strictAttempt_or_zero`.
-/
import Swarm.AttemptTower
import Swarm.ActualPathTransfer
import Swarm.RawStrictAttemptTower

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open MeasureTheory Set ProbabilityTheory Filter Topology Classical
open MeasureTheory.Filtration
open Swarming Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmFresh
open SwarmAttemptTower SwarmStoppedPast
open SwarmRecordMeas SwarmRecordMeas.Actual SwarmRecordMeas.StartLaw RecordoSupply SwarmRec
open SimJump SimJump.RecKernel
open WCJF.ActPath
open scoped ENNReal BigOperators

namespace SwarmRowTail

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. Records, rows and the canonical record clock -/

/-- Strictly below a record level before the record time. -/
theorem recordAt_runMax_lt {p : ℝ} {m : ℕ} {U : Array N} {t : ℕ} {d : ℤ}
    (h : RecordAt p m U t d) : ∀ j < t, RecordDefect.runMax (actX p m U) j < d := by
  intro j hj
  rw [RecordDefect.runMax, Finset.sup'_lt_iff]
  exact fun i _ => h.1 j hj i

/-- At a record the running maximum is the record level. -/
theorem recordAt_runMax_eq {p : ℝ} {m : ℕ} {U : Array N} {t : ℕ} {d : ℤ}
    (h : RecordAt p m U t d) : RecordDefect.runMax (actX p m U) t = d := by
  refine le_antisymm ?_ ?_
  · rw [RecordDefect.runMax, Finset.sup'_le_iff]
    exact fun i _ => le_of_eq (h.2 i)
  · obtain ⟨i⟩ := ‹Nonempty (Fin N)›
    calc d = actX p m U i t := (h.2 i).symm
      _ ≤ RecordDefect.runMax (actX p m U) t := RecordDefect.le_runMax t i

/-- The running maximum stays strictly below the level before the canonical record time of that
level.  This is the discrete intermediate value property of the running maximum: if it were
above the level, it would have had to equal the level earlier. -/
theorem recTimeA_runMax_lt (p : ℝ) (m : ℕ) (U : Array N) (hR : U ∈ ReachAll p m) (r : ℕ) :
    ∀ n < recTimeA p m U r, RecordDefect.runMax (actX p m U) n < (r : ℤ) := by
  have hne : ∀ j, j < recTimeA p m U r → RecordDefect.runMax (actX p m U) j ≠ (r : ℤ) :=
    fun j hj hjeq => recTimeA_min p m U r j hj (Or.inr hjeq)
  intro n hn
  by_contra hcon
  have hcon : (r : ℤ) ≤ RecordDefect.runMax (actX p m U) n := not_lt.mp hcon
  obtain ⟨m', hm', hval⟩ := RecordoSupply.exists_runMax_eq (actX p m U)
    (RecordoSupply.actX_step p m U) (RecordoSupply.actX_zero p m U) hcon
  exact hne m' (lt_of_le_of_lt hm' hn) hval

/-- On `ReachAll` the canonical clock is a genuine record-time sequence (paper's `τ_r`). -/
theorem isRecord_recTimeA (p : ℝ) (m : ℕ) (U : Array N) (hR : U ∈ ReachAll p m) :
    RecordDefect.IsRecord (actX p m U) (recTimeA p m U) := by
  intro r
  exact ⟨fun n hn => recTimeA_runMax_lt p m U hR r n hn,
    (recTimeA_spec p m U r).resolve_left (fun h => h hR)⟩

/-- Every walker starts at the origin, so the canonical clock of level `r` is at least `r`. -/
theorem level_le_recTimeA (p : ℝ) (m : ℕ) (U : Array N) (hR : U ∈ ReachAll p m) (r : ℕ) :
    r ≤ recTimeA p m U r :=
  RecordoSupply.tau_ge (isRecord_recTimeA p m U hR)
    (RecordoSupply.actX_step p m U) (RecordoSupply.actX_zero p m U) r

/-- **A canonical record time at which every walker sits exactly at the level is a row.**  This is
the exact `RecordAt`/`levAt` statement: the past clause is `recTimeA_runMax_lt`, the present
clause is the hypothesis, and the level is `recTimeA`'s level `r`. -/
theorem row_recTimeA {p : ℝ} {m : ℕ} {U : Array N} {r : ℕ} (hR : U ∈ ReachAll p m)
    (hall : ∀ i, actX p m U i (recTimeA p m U r) = (r : ℤ)) :
    Row p m U (recTimeA p m U r) := by
  have hbelow := recTimeA_runMax_lt p m U hR r
  have hlev : levAt p m U (recTimeA p m U r) = (r : ℤ) := by
    refine le_antisymm ?_ ?_
    · rw [levAt_le_iff]
      exact fun i => le_of_eq (hall i)
    · calc (r : ℤ) = actX p m U (Classical.arbitrary (Fin N)) (recTimeA p m U r) := (hall _).symm
        _ ≤ levAt p m U (recTimeA p m U r) := pos_le_levAt p m U _ _
  show RecordAt p m U (recTimeA p m U r) (levAt p m U (recTimeA p m U r))
  rw [hlev]
  refine ⟨fun s hs i => ?_, fun i => hall i⟩
  exact lt_of_le_of_lt (RecordDefect.le_runMax s i) (hbelow s hs)

/-! ## 2. Row recurrence: simultaneous records after every finite time, a.e. -/

/-- **Row recurrence.**  On this event, after every finite time there is a time at which all
walkers sit simultaneously at the running maximum (a record).  This is a genuine pathwise
statement about the actual array; it is derived below from the R1 transfer, not assumed. -/
def RowRecurrence (p : ℝ) (m : ℕ) : Set (Array N) :=
  {U | ∀ T : ℕ, ∃ t : ℕ, T < t ∧ Row p m U t}

theorem measurableSet_rowRecurrence (p : ℝ) (m : ℕ) :
    MeasurableSet (RowRecurrence (N := N) p m) := by
  have hset : RowRecurrence (N := N) p m
      = ⋂ T : ℕ, ⋃ t : ℕ, ⋃ (_ : T < t), {U : Array N | Row p m U t} := by
    ext U
    simp only [RowRecurrence, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion,
      exists_prop]
  rw [hset]
  exact MeasurableSet.iInter fun T =>
    MeasurableSet.iUnion fun t => MeasurableSet.iUnion fun _ => measurableSet_row p m t

/-- **The R1 transfer gives row recurrence.**  Infinitely many simultaneous records at canonical
times `recTimeA r` (with levels `r → ∞`, since `r ≤ recTimeA r`) put a row after every finite
time. -/
theorem rowRecurrence_ae {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (hN : 2 ≤ N)
    (htight : ∀ (ε : ℝ≥0∞), 0 < ε → ∃ K : ℕ, ∀ u : ℕ,
      (recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
        (Measure.dirac (zeroState (N := N) (m := m) (by omega : 1 ≤ m), (0 : ℕ))))
        {ω : ℕ → RecState N m × ℕ | K < dT ω u} ≤ ε) :
    ∀ᵐ U ∂(arrayMeasure N), U ∈ RowRecurrence (N := N) p m := by
  filter_upwards [ae_frequently_all_walkers_at_level (N := N) (m := m) p hp0 hp1 hm hN htight,
    M4RecordGeom.ae_reachAll (N := N) (p := p) (m := m) hp0 hp1 hm hN] with U hfreq hR
  intro T
  rw [Filter.frequently_atTop] at hfreq
  obtain ⟨r, hrT, hall⟩ := hfreq (T + 1)
  have hge := level_le_recTimeA p m U hR r
  exact ⟨recTimeA p m U r, by omega, row_recTimeA hR hall⟩

/-- Row recurrence in the equivalent "there is always a next row" form. -/
theorem rowAfter_ne_top_of_recurrence {p : ℝ} {m : ℕ} {U : Array N}
    (hU : U ∈ RowRecurrence p m) (t : ℕ) : rowAfter p m U t ≠ ⊤ := by
  rw [ne_eq, rowAfter_eq_top_iff]
  rintro h
  obtain ⟨n, hn, hrow⟩ := hU t
  exact h n hn hrow

/-! ## 3. `A_{q+1}` is exactly `{T_q ≠ ⊤}` -/

/-- A `WithTop ℕ`-valued time which is not `⊤` is a natural number. -/
theorem exists_coe_of_ne_top {x : WithTop ℕ} (h : x ≠ ⊤) : ∃ n : ℕ, x = (n : WithTop ℕ) := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp h
  exact ⟨n, hn.symm⟩

theorem exists_coe_S_of_ne_top {p : ℝ} {m : ℕ} {U : Array N} {q : ℕ}
    (h : S p m U q ≠ ⊤) : ∃ n : ℕ, S p m U q = (n : WithTop ℕ) := exists_coe_of_ne_top h

/-- Rows only ever appear at rows: `A_{q+1} ⊆ A_q`.  (A finite `S_{q+1}` has a finite `S_q`.) -/
theorem Aq_succ_subset_Aq (p : ℝ) (m : ℕ) (q : ℕ) :
    Aq (N := N) p m (q + 1) ⊆ Aq (N := N) p m q := by
  intro U hU
  obtain ⟨t, ht⟩ := mem_Aq_iff.mp hU
  obtain ⟨s, u, hs, -, -⟩ := S_succ_eq_iff.mp ht
  exact mem_Aq_iff.mpr ⟨s, hs⟩

/-- Under row recurrence, `A_{q+1}` is exactly the event that row `q` returns: the next row can
always be started after a finite return time, and a finite `S_{q+1}` forces `T_q` finite. -/
theorem Aq_succ_eq_T_ne_top {p : ℝ} {m : ℕ} {U : Array N} (hU : U ∈ RowRecurrence p m)
    (q : ℕ) : (U ∈ Aq (N := N) p m (q + 1) ↔ T p m U q ≠ ⊤) := by
  constructor
  · intro hA
    obtain ⟨t, ht⟩ := mem_Aq_iff.mp hA
    obtain ⟨s, u, hs, hret, hrow⟩ := S_succ_eq_iff.mp ht
    rw [T_eq_of_S_coe hs, hret]
    exact WithTop.coe_ne_top
  · intro hT
    have hTdef : T p m U q = bindTop (S p m U q) (fun t => retAfter p m U t) := rfl
    have hS : ∃ s : ℕ, S p m U q = (s : WithTop ℕ) := by
      rcases S_coe_or_top p m U q with h | h
      · exfalso
        rw [hTdef, h, bindTop_top] at hT
        exact hT rfl
      · exact h
    obtain ⟨s, hs⟩ := hS
    have hT' : T p m U q = retAfter p m U s := T_eq_of_S_coe hs
    have hu : ∃ u : ℕ, retAfter p m U s = (u : WithTop ℕ) :=
      exists_coe_of_ne_top (by rw [← hT']; exact hT)
    obtain ⟨u, hu⟩ := hu
    have ht : ∃ t : ℕ, rowAfter p m U u = (t : WithTop ℕ) :=
      exists_coe_of_ne_top (rowAfter_ne_top_of_recurrence hU u)
    obtain ⟨t, ht⟩ := ht
    exact mem_Aq_iff.mpr ⟨t, S_succ_eq_iff.mpr ⟨s, u, hs, hu, ht⟩⟩

/-- `{T_q ≠ ⊤} ⊆ A_q` unconditionally: a finite return time presupposes a started row. -/
theorem T_ne_top_subset_Aq (p : ℝ) (m : ℕ) (q : ℕ) :
    {U : Array N | T p m U q ≠ ⊤} ⊆ Aq (N := N) p m q := by
  intro U hT
  have hTne : T p m U q ≠ ⊤ := hT
  have hTdef : T p m U q = bindTop (S p m U q) (fun t => retAfter p m U t) := rfl
  have hS : ∃ s : ℕ, S p m U q = (s : WithTop ℕ) := by
    rcases S_coe_or_top p m U q with h | h
    · exfalso
      rw [hTdef, h, bindTop_top] at hTne
      exact hTne rfl
    · exact h
  obtain ⟨s, hs⟩ := hS
  exact mem_Aq_iff.mpr ⟨s, hs⟩

/-- **The row decomposition on the recurrence set**: a started row either returns — so the next
row starts — or it never returns. -/
theorem Aq_eq_union_on_recurrence {p : ℝ} {m : ℕ} (q : ℕ) :
    Aq (N := N) p m q ∩ RowRecurrence p m
      = (Aq (N := N) p m (q + 1) ∩ RowRecurrence p m)
        ∪ (Aq (N := N) p m q ∩ {U : Array N | T p m U q = ⊤} ∩ RowRecurrence p m) := by
  ext U
  constructor
  · rintro ⟨hA, hR⟩
    by_cases hT : T p m U q = ⊤
    · exact Or.inr ⟨⟨hA, hT⟩, hR⟩
    · exact Or.inl ⟨(Aq_succ_eq_T_ne_top hR q).mpr hT, hR⟩
  · rintro (⟨hA, hR⟩ | ⟨⟨hA, -⟩, hR⟩)
    · exact ⟨Aq_succ_subset_Aq p m q hA, hR⟩
    · exact ⟨hA, hR⟩

theorem disjoint_Aq_succ_T_top {p : ℝ} {m : ℕ} (q : ℕ) :
    Disjoint (Aq (N := N) p m (q + 1) ∩ RowRecurrence p m)
      (Aq (N := N) p m q ∩ {U : Array N | T p m U q = ⊤} ∩ RowRecurrence p m) := by
  rw [Set.disjoint_left]
  rintro U ⟨h1, hR⟩ ⟨⟨-, hT⟩, -⟩
  have hTeq : T p m U q = ⊤ := hT
  exact (Aq_succ_eq_T_ne_top hR q).mp h1 hTeq

/-- Dropping a null set from an intersection does not change the measure. -/
theorem measure_inter_eq_of_null_compl {R : Set (Array N)}
    (hR : (arrayMeasure N) Rᶜ = 0) (s : Set (Array N)) :
    (arrayMeasure N) (s ∩ R) = (arrayMeasure N) s := by
  refine le_antisymm (measure_mono Set.inter_subset_left) ?_
  have hsub : s ⊆ (s ∩ R) ∪ (s ∩ Rᶜ) := by
    intro U hU
    by_cases h : U ∈ R
    · exact Or.inl ⟨hU, h⟩
    · exact Or.inr ⟨hU, h⟩
  have hnull : (arrayMeasure N) (s ∩ Rᶜ) = 0 :=
    measure_mono_null Set.inter_subset_right hR
  calc (arrayMeasure N) s ≤ (arrayMeasure N) ((s ∩ R) ∪ (s ∩ Rᶜ)) := measure_mono hsub
    _ ≤ (arrayMeasure N) (s ∩ R) + (arrayMeasure N) (s ∩ Rᶜ) := measure_union_le _ _
    _ = (arrayMeasure N) (s ∩ R) := by rw [hnull, add_zero]

/-- **The geometric step.**  The mass of "row `q+1` has started" is `1 - P(V)` times the mass of
"row `q` has started". -/
theorem measure_Aq_succ {p : ℝ} {m : ℕ}
    (hae : ∀ᵐ U ∂(arrayMeasure N), U ∈ RowRecurrence p m) (q : ℕ) :
    (arrayMeasure N) (Aq (N := N) p m (q + 1))
      = (1 - (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)})
        * (arrayMeasure N) (Aq (N := N) p m q) := by
  classical
  set ν := (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} with hν
  have hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hRnull : (arrayMeasure N) (RowRecurrence (N := N) p m)ᶜ = 0 := hae
  have hAq : (arrayMeasure N) (Aq (N := N) p m q) ≠ ⊤ := measure_ne_top _ _
  have hc : (arrayMeasure N) (Aq (N := N) p m q) * ν ≠ ⊤ :=
    ENNReal.mul_ne_top hAq (measure_ne_top _ _)
  have hdecomp : (arrayMeasure N) (Aq (N := N) p m q)
      = (arrayMeasure N) (Aq (N := N) p m (q + 1))
        + (arrayMeasure N) (Aq (N := N) p m q ∩ {U : Array N | T p m U q = ⊤}) := by
    have h1 : (arrayMeasure N) (Aq (N := N) p m q)
        = (arrayMeasure N) (Aq (N := N) p m q ∩ RowRecurrence (N := N) p m) :=
      (measure_inter_eq_of_null_compl (N := N) hRnull _).symm
    have h2 : (arrayMeasure N) (Aq (N := N) p m (q + 1) ∩ RowRecurrence (N := N) p m)
        = (arrayMeasure N) (Aq (N := N) p m (q + 1)) :=
      measure_inter_eq_of_null_compl (N := N) hRnull _
    have h3 : (arrayMeasure N) (Aq (N := N) p m q ∩ {U : Array N | T p m U q = ⊤}
          ∩ RowRecurrence (N := N) p m)
        = (arrayMeasure N) (Aq (N := N) p m q ∩ {U : Array N | T p m U q = ⊤}) :=
      measure_inter_eq_of_null_compl (N := N) hRnull _
    have h4 : MeasurableSet (Aq (N := N) p m q ∩ {U : Array N | T p m U q = ⊤}
        ∩ RowRecurrence (N := N) p m) :=
      ((measurableSet_Aq p m q).inter (measurableSet_T_top p m q)).inter
        (measurableSet_rowRecurrence p m)
    rw [h1, Aq_eq_union_on_recurrence (N := N) (p := p) (m := m) q,
      measure_union (disjoint_Aq_succ_T_top q) h4, h2, h3]
  have hT : (arrayMeasure N) (Aq (N := N) p m q ∩ {U : Array N | T p m U q = ⊤})
      = (arrayMeasure N) (Aq (N := N) p m q) * ν := measure_T_top (N := N) p m q
  have hsub : (arrayMeasure N) (Aq (N := N) p m (q + 1))
      = (arrayMeasure N) (Aq (N := N) p m q)
        - (arrayMeasure N) (Aq (N := N) p m q) * ν := by
    refine ENNReal.eq_sub_of_add_eq hc ?_
    rw [← hT]
    exact hdecomp.symm
  have hmul : (arrayMeasure N) (Aq (N := N) p m q) * (1 - ν)
      = (arrayMeasure N) (Aq (N := N) p m q)
        - (arrayMeasure N) (Aq (N := N) p m q) * ν := by
    simpa using ENNReal.mul_sub (a := (arrayMeasure N) (Aq (N := N) p m q)) (b := 1) (c := ν)
      (fun _ _ => hAq)
  rw [hsub, ← hmul, mul_comm]

/-! ## 4. The geometric tail and the first completed row -/

/-- The `q`-th row is started with mass at most `(1 - P(V))^q`. -/
theorem measure_Aq {p : ℝ} {m : ℕ}
    (hae : ∀ᵐ U ∂(arrayMeasure N), U ∈ RowRecurrence p m) (q : ℕ) :
    (arrayMeasure N) (Aq (N := N) p m q)
      = (1 - (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)}) ^ q := by
  have hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  induction q with
  | zero => rw [Aq_zero, measure_univ, pow_zero]
  | succ q ih => rw [measure_Aq_succ hae q, ih, pow_succ, mul_comm]

/-- **The geometric decay of the ongoing failures.** -/
theorem tendsto_measure_Aq {p : ℝ} {m : ℕ}
    (hae : ∀ᵐ U ∂(arrayMeasure N), U ∈ RowRecurrence p m)
    (hν : 0 < (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)}) :
    Tendsto (fun q : ℕ => (arrayMeasure N) (Aq (N := N) p m q)) atTop (𝓝 0) := by
  have hlt : (1 - (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)}) < 1 :=
    ENNReal.sub_lt_self (by simp) (by simp) hν.ne'
  have h := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt
  simpa only [measure_Aq hae] using h

/-- **The ongoing-failure event is null**: almost surely some row never returns. -/
theorem measure_iInter_Aq_eq_zero {p : ℝ} {m : ℕ}
    (hae : ∀ᵐ U ∂(arrayMeasure N), U ∈ RowRecurrence p m)
    (hν : 0 < (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)}) :
    (arrayMeasure N) (⋂ q, Aq (N := N) p m q) = 0 := by
  refine le_antisymm ?_ (by simp)
  have hle := ge_of_tendsto' (tendsto_measure_Aq (N := N) hae hν)
    (fun q => measure_mono (Set.iInter_subset _ q))
  simpa using hle

/-- **A first completed row exists almost surely.**  There is a row index `q` such that row `q`
starts (`S_q < ∞`), never returns (`T_q = ⊤`), and every earlier row does return
(`T_j ≠ ⊤` for `j < q`). -/
theorem ae_exists_first_completed_row {p : ℝ} {m : ℕ}
    (hae : ∀ᵐ U ∂(arrayMeasure N), U ∈ RowRecurrence p m)
    (hν : 0 < (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)}) :
    ∀ᵐ U ∂(arrayMeasure N),
      ∃ q : ℕ, U ∈ Aq (N := N) p m q ∧ T p m U q = ⊤ ∧ ∀ j < q, T p m U j ≠ ⊤ := by
  have hnull : (arrayMeasure N) (⋂ q, Aq (N := N) p m q) = 0 :=
    measure_iInter_Aq_eq_zero (N := N) hae hν
  have hae2 : ∀ᵐ U ∂(arrayMeasure N), ∃ q : ℕ, U ∉ Aq (N := N) p m q := by
    rw [MeasureTheory.ae_iff]
    have hset : {U : Array N | ¬ ∃ q : ℕ, U ∉ Aq (N := N) p m q}
        = ⋂ q, Aq (N := N) p m q := by
      ext U
      simp only [Set.mem_ofPred_eq, not_exists, not_not, Set.mem_iInter]
    rw [hset, hnull]
  filter_upwards [hae2, hae] with U hU hR
  have hU' : ∃ q : ℕ, U ∉ Aq (N := N) p m q := hU
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, U ∉ Aq (N := N) p m Q ∧ ∀ j < Q, U ∈ Aq (N := N) p m j :=
    ⟨Nat.find hU', Nat.find_spec hU', fun j hj => by
      by_contra h
      exact Nat.find_min hU' hj h⟩
  have hQpos : 1 ≤ Q := by
    rcases Nat.eq_zero_or_pos Q with h | h
    · exfalso
      rw [h, Aq_zero] at hQ
      exact hQ.1 (Set.mem_univ U)
    · exact h
  refine ⟨Q - 1, hQ.2 (Q - 1) (by omega), ?_, ?_⟩
  · by_contra hTne
    have hsub : Q - 1 + 1 = Q := by omega
    exact hQ.1 (hsub ▸ (Aq_succ_eq_T_ne_top hR (Q - 1)).mpr hTne)
  · intro j hj
    exact (Aq_succ_eq_T_ne_top hR j).mp (hQ.2 (j + 1) (by omega))

/-! ## 5. Regeneration: a record with a strictly positive future -/

/-- At a record, the record level is non-negative: the walkers start at the origin and the level
is their common position. -/
theorem levAt_nonneg_of_recordAt {p : ℝ} {m : ℕ} {U : Array N} {t : ℕ} {d : ℤ}
    (h : RecordAt p m U t d) : 0 ≤ d := by
  obtain ⟨i⟩ := ‹Nonempty (Fin N)›
  rcases Nat.eq_zero_or_pos t with h0 | hpos
  · subst h0
    have h2 : actX p m U i 0 = d := h.2 i
    rw [actX_zero] at h2
    omega
  · have h1 : actX p m U i 0 < d := h.1 0 hpos i
    rw [actX_zero] at h1
    omega

/-- **A completed row is a regeneration.**  If row `q` starts at `t` and never returns, then the
record at `(t, levAt t)` has a strictly positive future: this is the paper's regeneration event
`RegenAtStrict` in the literal translation-invariant form. -/
theorem exists_regenAtStrict_of_completed_row {p : ℝ} {m : ℕ} {U : Array N} {q : ℕ}
    (hA : U ∈ Aq (N := N) p m q) (hT : T p m U q = ⊤) :
    ∃ t : ℕ, RegenAtStrict p m U t (levAt p m U t) := by
  obtain ⟨t, ht⟩ := mem_Aq_iff.mp hA
  have hret : retAfter p m U t = ⊤ := by
    rw [← T_eq_of_S_coe ht]; exact hT
  have hrec : RecordAt p m U t (levAt p m U t) := row_of_S_eq_coe p m q t U ht
  refine ⟨t, hrec, ?_⟩
  intro n hn i
  rw [retAfter_eq_top_iff] at hret
  have hlow : levAt p m U t < lowAt p m U (t + n) := hret (t + n) (by omega)
  exact lt_lowAt_iff.mp hlow i

/-- **Almost sure regeneration.**  From the geometric tail: almost surely there is a time at
which all walkers sit simultaneously at the running maximum and stay strictly above it forever
after. -/
theorem ae_exists_regenAtStrict {p : ℝ} {m : ℕ}
    (hae : ∀ᵐ U ∂(arrayMeasure N), U ∈ RowRecurrence p m)
    (hν : 0 < (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)}) :
    ∀ᵐ U ∂(arrayMeasure N), ∃ t : ℕ, RegenAtStrict p m U t (levAt p m U t) := by
  filter_upwards [ae_exists_first_completed_row (N := N) hae hν] with U hU
  obtain ⟨q, hA, hT, -⟩ := hU
  exact exists_regenAtStrict_of_completed_row hA hT

/-- **Almost sure regeneration at a canonical record time.**  The regeneration time of a completed
row is the first time the running maximum reaches its level, i.e. the canonical record time
`recTimeA r` of a *positive or zero* level `r`.  The level is `posPath`'s own level, so this
preserves the literal meaning of the record. -/
theorem ae_exists_regenAtRecTime {p : ℝ} {m : ℕ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hm : 2 ≤ m) (hN : 2 ≤ N)
    (hae : ∀ᵐ U ∂(arrayMeasure N), U ∈ RowRecurrence p m)
    (hν : 0 < (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)}) :
    ∀ᵐ U ∂(arrayMeasure N),
      ∃ r : ℕ, RegenAtStrict p m U (recTimeA p m U r) ((r : ℤ)) := by
  filter_upwards [ae_exists_regenAtStrict (N := N) hae hν,
    M4RecordGeom.ae_reachAll (N := N) (p := p) (m := m) hp0 hp1 hm hN] with U hreg hR
  obtain ⟨t, hrec, hstrict⟩ := hreg
  have hd0 : 0 ≤ levAt p m U t := levAt_nonneg_of_recordAt hrec
  obtain ⟨r, hr⟩ : ∃ r : ℕ, levAt p m U t = (r : ℤ) :=
    ⟨(levAt p m U t).toNat, (Int.toNat_of_nonneg hd0).symm⟩
  have ht : recTimeA p m U r = t := by
    refine (recTimeA_eq_iff p m U r t hR).mpr ⟨?_, ?_⟩
    · rw [← hr]; exact recordAt_runMax_eq hrec
    · intro j hj
      rw [← hr]
      exact ne_of_lt (recordAt_runMax_lt hrec j hj)
  refine ⟨r, ?_⟩
  rw [ht, ← hr]
  exact ⟨hrec, hstrict⟩

/-! ## 6. The canonical positive-level attempt -/

/-- **A regeneration at a positive canonical level is a literal `StrictAttempt`.**  The raw
declaration `RawStrictAttemptTower.StrictAttempt p m U r` is by definition `RegenAtStrict` at the
canonical time of level `r+1` and at level `r+1`; so a regeneration at a positive level `r`
is exactly `StrictAttempt (r-1)`.  This is the exact index link: the level is positive and the
time is the actual canonical record time. -/
theorem strictAttempt_of_pos_level {p : ℝ} {m : ℕ} {U : Array N} {r : ℕ} (h : 0 < r)
    (hreg : RegenAtStrict p m U (recTimeA p m U r) ((r : ℤ))) :
    RawStrictAttemptTower.StrictAttempt p m U (r - 1) := by
  have hsub : r - 1 + 1 = r := by omega
  show RegenAtStrict p m U (recTimeA p m U (r - 1 + 1)) (((r - 1 + 1 : ℕ)) : ℤ)
  rw [hsub]
  exact hreg

/-- **The raw dichotomy.**  Almost surely there is either a literal positive-level strict attempt
or the row at level `0` regenerates: all walkers sit at the origin at time `0` and stay strictly
above it afterwards.

The second alternative is a genuine regeneration and cannot be replaced by a positive-level
attempt: the tower's row `0` starts at level `0`, and if it never returns then `S_{q+1} = ⊤` for
every later row; a path whose swarm minimum stays at level `1` forever after time `0` has a
level-`0` regeneration and no strict attempt at any positive level. -/
theorem ae_exists_strictAttempt_or_levelZero {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N)
    (hae : ∀ᵐ U ∂(arrayMeasure N), U ∈ RowRecurrence p m)
    (hν : 0 < (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)}) :
    ∀ᵐ U ∂(arrayMeasure N),
      (∃ r : ℕ, RawStrictAttemptTower.StrictAttempt p m U r) ∨ RegenAtStrict p m U 0 0 := by
  filter_upwards [ae_exists_regenAtRecTime (N := N) hp0 hp1 hm hN hae hν] with U hU
  obtain ⟨r, hr⟩ := hU
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · refine Or.inr ?_
    rw [h0, recTimeA_zero] at hr
    exact hr
  · exact Or.inl ⟨r - 1, strictAttempt_of_pos_level hpos hr⟩

/-! ## 7. Capstones over the two genuine public inputs -/

/-- `P(V) > 0` from the strictly positive initial path measure. -/
theorem strictPos_measure_lt_top_pos {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) :
    0 < (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} :=
  pos_iff_ne_zero.mpr (SwarmFreshPast.strictPos_measure_pos hp0 hp1 hm hN)

/-- **Capstone 1 (dT tightness).**  From the literal paper `dT` tightness of the canonical
stopped-record chain at the forced Dirac start — the exact output of the two genuine block
clauses — almost surely the actual array has a row that starts and never returns, hence a
regeneration with a strictly positive future at a simultaneous record. -/
theorem ae_exists_first_completed_row_of_dT_tight {p : ℝ} (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N)
    (htight : ∀ (ε : ℝ≥0∞), 0 < ε → ∃ K : ℕ, ∀ u : ℕ,
      (recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
        (Measure.dirac (zeroState (N := N) (m := m) (by omega : 1 ≤ m), (0 : ℕ))))
        {ω : ℕ → RecState N m × ℕ | K < dT ω u} ≤ ε) :
    ∀ᵐ U ∂(arrayMeasure N),
      ∃ q : ℕ, U ∈ Aq (N := N) p m q ∧ T p m U q = ⊤ ∧ ∀ j < q, T p m U j ≠ ⊤ :=
  ae_exists_first_completed_row (N := N) (rowRecurrence_ae hp0 hp1 hm hN htight)
    (strictPos_measure_lt_top_pos hp0 hp1 hm hN)

/-- **Capstone 2 (dT tightness).**  The regeneration at a canonical record time. -/
theorem ae_regenAtRecTime_of_dT_tight {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N)
    (htight : ∀ (ε : ℝ≥0∞), 0 < ε → ∃ K : ℕ, ∀ u : ℕ,
      (recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
        (Measure.dirac (zeroState (N := N) (m := m) (by omega : 1 ≤ m), (0 : ℕ))))
        {ω : ℕ → RecState N m × ℕ | K < dT ω u} ≤ ε) :
    ∀ᵐ U ∂(arrayMeasure N), ∃ r : ℕ, RegenAtStrict p m U (recTimeA p m U r) ((r : ℤ)) :=
  ae_exists_regenAtRecTime (N := N) hp0 hp1 hm hN (rowRecurrence_ae hp0 hp1 hm hN htight)
    (strictPos_measure_lt_top_pos hp0 hp1 hm hN)

/-- **Capstone 3 (two genuine block clauses).**  From `AdvanceClause`/`HalfClause` at the constants
produced by `AuditResidual.record_tightness_of_two_actual_blocks`, almost surely the actual array
has a row that starts and never returns. -/
theorem ae_exists_first_completed_row_of_two_blocks {p : ℝ} (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) (B : ℕ) (hB : 1 ≤ B) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (p₁ p₂ : ℕ → ℝ≥0∞) (K₁ K₂ : ℝ), 0 ≤ K₁ → 0 ≤ K₂ →
      (∀ ℓ : ℕ, p₁ ℓ ≤ ENNReal.ofReal (K₁ * (((ℓ : ℝ) + 1))⁻¹ ^ 3)) →
      (∀ ℓ : ℕ, p₂ ℓ ≤ ENNReal.ofReal (K₂ * (((ℓ : ℝ) + 1))⁻¹ ^ 3)) →
      TightAvail.AdvanceClause (N := N) p m B κ p₁ →
      TightAvail.HalfClause (N := N) p m B κ p₂ →
      ∀ᵐ U ∂(arrayMeasure N),
        ∃ q : ℕ, U ∈ Aq (N := N) p m q ∧ T p m U q = ⊤ ∧ ∀ j < q, T p m U j ≠ ⊤ := by
  obtain ⟨κ, hκ, H⟩ :=
    AuditResidual.record_tightness_of_two_actual_blocks (N := N) hp0 hp1 hm hN B hB
  refine ⟨κ, hκ, fun p₁ p₂ K₁ K₂ hK₁ hK₂ hdec₁ hdec₂ h₁ h₂ => ?_⟩
  have h₁' := h₁
  have h₂' := h₂
  simp only [TightAvail.AdvanceClause] at h₁'
  simp only [TightAvail.HalfClause] at h₂'
  exact ae_exists_first_completed_row_of_dT_tight (N := N) hp0 hp1 hm hN
    (H p₁ p₂ K₁ K₂ hK₁ hK₂ hdec₁ hdec₂ h₁' h₂')

/-- **Capstone 4 (two genuine block clauses).**  The same regeneration conclusion from the two
block clauses. -/
theorem ae_regenAtRecTime_of_two_blocks {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) (B : ℕ) (hB : 1 ≤ B) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (p₁ p₂ : ℕ → ℝ≥0∞) (K₁ K₂ : ℝ), 0 ≤ K₁ → 0 ≤ K₂ →
      (∀ ℓ : ℕ, p₁ ℓ ≤ ENNReal.ofReal (K₁ * (((ℓ : ℝ) + 1))⁻¹ ^ 3)) →
      (∀ ℓ : ℕ, p₂ ℓ ≤ ENNReal.ofReal (K₂ * (((ℓ : ℝ) + 1))⁻¹ ^ 3)) →
      TightAvail.AdvanceClause (N := N) p m B κ p₁ →
      TightAvail.HalfClause (N := N) p m B κ p₂ →
      ∀ᵐ U ∂(arrayMeasure N), ∃ r : ℕ, RegenAtStrict p m U (recTimeA p m U r) ((r : ℤ)) := by
  obtain ⟨κ, hκ, H⟩ :=
    AuditResidual.record_tightness_of_two_actual_blocks (N := N) hp0 hp1 hm hN B hB
  refine ⟨κ, hκ, fun p₁ p₂ K₁ K₂ hK₁ hK₂ hdec₁ hdec₂ h₁ h₂ => ?_⟩
  have h₁' := h₁
  have h₂' := h₂
  simp only [TightAvail.AdvanceClause] at h₁'
  simp only [TightAvail.HalfClause] at h₂'
  exact ae_regenAtRecTime_of_dT_tight (N := N) hp0 hp1 hm hN
    (H p₁ p₂ K₁ K₂ hK₁ hK₂ hdec₁ hdec₂ h₁' h₂')

end SwarmRowTail
