/-
# The paper's adaptive attempt-row tower on the actual WCJF array

`main_1d_revised.tex` (proof of Proposition `regen`, the paragraph beginning
"We set `S_1 = 0` and `r_1 = 0`") runs a *row* argument:

* `S_q` — the start of attempt row `q`;
* `r_q = max_i X^i_{S_q}` — the row level (all walkers are at `r_q` at `S_q`: a simultaneous
  record, because `S_1 = 0` and, for `q ≥ 2`, `S_q` is chosen at a simultaneous record);
* `T_q = inf {n > S_q : min_i X^i_n ≤ r_q}` — the row's return time, `∞` if it never returns;
* `S_{q+1} = inf {τ_r : T_q < τ_r < ∞, Y_r ∈ F}` — the first fresh record after the return;
* `Q = inf {q ≥ 1 : T_q = ∞}` — the first row that never returns.

The quantitative content is the paper's

  `P(T_q = ∞ | F_{S_q}) = P(V)`, hence `P(Q > q) = (1 - P(V)) P(Q ≥ q)`, hence `Q < ∞` a.s.

This file supplies the measurable tower foundations for the **actual array law**
`arrayMeasure N` and the **actual trajectory** `Swarming.Trajectory.trajectory`, and proves
`measure_T_top`: the mass of rows that have started and never return is `P(V)` times the mass
of rows that have started.  The single probabilistic ingredient is
`SwarmStoppedPast.measure_record_strictFut` (the summed escape factor at a stopped record,
from the coordinator-accepted `Swarm/StoppedPast.lean` + `Swarm/RowEscape.lean`).
The formula is not yet the geometric decay of all attempt failures, nor a completed regeneration.

Deviations from the paper's letter, and why they are sound here:

* The paper conditions `S_{q+1}` on `Y_r ∈ F` (capped local times at the record level all `1`,
  above all `0`) because its `(freshlaw)` needs that local-time structure.  In this
  formalisation the escape factor is `measure_record_strictFut`, which is proved for **every**
  `RecordAt` cell (the low block below the record level is the independent block); no `F`
  condition is needed, and dropping it only enlarges the set of admissible next rows.  So
  `S_{q+1}` here is the first simultaneous record after `T_q`.
* The paper's `S_q, T_q` live in `ℕ ∪ {∞}`.  Here they are `WithTop ℕ` (`= WithTop ℕ`), with the
  paper's totalisation built into `firstAfter`.

Residual input, named: `RowRecurrence` (`records occur after every finite time, a.e.`).  It is
the paper's "simultaneous record times occur infinitely often", which is *not* proved here and
is not implied by anything in this file.  It is exactly what the R1 transfer direction produces
from record tightness.

Not claimed here: tightness, the invariant law, `E^* D < ∞`, regeneration independence, or the
common velocity.
-/
import Swarm.RowEscape
import Swarm.ActualRecordFiltration

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open MeasureTheory Set ProbabilityTheory
open Swarming Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmFresh
open SwarmStoppedPast
open scoped ENNReal

namespace SwarmAttemptTower

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## Row levels and the row predicate -/

/-- The running swarm maximum `r_q = max_i X^i_t` at a candidate row time. -/
noncomputable def levAt (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) : ℤ :=
  RecordDefect.runMax (RecordoSupply.actX p m U) n

/-- The running swarm minimum `min_i X^i_t`, used by the row's return condition. -/
noncomputable def lowAt (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) : ℤ :=
  RecordDefect.runMin (RecordoSupply.actX p m U) n

theorem measurable_levAt (p : ℝ) (m : ℕ) (n : ℕ) :
    Measurable fun U : Array N => levAt p m U n :=
  SwarmRecordMeas.measurable_runMax
    (f := fun i (U : Array N) => (trajectory p m U n).pos i)
    (fun i => (Swarming.Fair.measurable_trajectory p m n).1 i) n

theorem measurable_lowAt (p : ℝ) (m : ℕ) (n : ℕ) :
    Measurable fun U : Array N => lowAt p m U n :=
  SwarmRecordMeas.measurable_runMin
    (f := fun i (U : Array N) => (trajectory p m U n).pos i)
    (fun i => (Swarming.Fair.measurable_trajectory p m n).1 i) n

theorem lowAt_le_pos (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    lowAt p m U n ≤ (trajectory p m U n).pos i :=
  RecordDefect.runMin_le _ _

theorem pos_le_levAt (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    (trajectory p m U n).pos i ≤ levAt p m U n :=
  RecordDefect.le_runMax _ _

theorem lowAt_le_iff {p : ℝ} {m : ℕ} {U : Array N} {n : ℕ} {d : ℤ} :
    lowAt p m U n ≤ d ↔ ∃ i, (trajectory p m U n).pos i ≤ d := by
  rw [lowAt, RecordDefect.runMin, Finset.inf'_le_iff]
  exact ⟨fun ⟨i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h⟩ => ⟨i, Finset.mem_univ i, h⟩⟩

theorem lt_lowAt_iff {p : ℝ} {m : ℕ} {U : Array N} {n : ℕ} {d : ℤ} :
    d < lowAt p m U n ↔ ∀ i, d < (trajectory p m U n).pos i := by
  rw [lowAt, RecordDefect.runMin, Finset.lt_inf'_iff]
  exact ⟨fun h i => h i (Finset.mem_univ i), fun h i _ => h i⟩

theorem levAt_le_iff {p : ℝ} {m : ℕ} {U : Array N} {n : ℕ} {d : ℤ} :
    levAt p m U n ≤ d ↔ ∀ i, (trajectory p m U n).pos i ≤ d := by
  rw [levAt, RecordDefect.runMax, Finset.sup'_le_iff]
  exact ⟨fun h i => h i (Finset.mem_univ i), fun h i _ => h i⟩

theorem levAt_lt_iff {p : ℝ} {m : ℕ} {U : Array N} {n : ℕ} {d : ℤ} :
    levAt p m U n < d ↔ ∀ i, (trajectory p m U n).pos i < d := by
  rw [levAt, RecordDefect.runMax, Finset.sup'_lt_iff]
  exact ⟨fun h i => h i (Finset.mem_univ i), fun h i _ => h i⟩

theorem levAt_eq_iff {p : ℝ} {m : ℕ} {U : Array N} {n : ℕ} {d : ℤ} :
    levAt p m U n = d ↔
      (∀ i, (trajectory p m U n).pos i ≤ d) ∧ ∃ i, (trajectory p m U n).pos i = d := by
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_⟩
    · rw [← h]; exact pos_le_levAt p m U n i
    · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun i : Fin N => (trajectory p m U n).pos i)
      exact ⟨i, hi.symm.trans h⟩
  · rintro ⟨h1, i, hi⟩
    refine le_antisymm (levAt_le_iff.mpr h1) ?_
    calc d = (trajectory p m U n).pos i := hi.symm
      _ ≤ levAt p m U n := pos_le_levAt p m U n i

theorem levAt_zero (p : ℝ) (m : ℕ) (U : Array N) : levAt p m U 0 = 0 :=
  RecordoSupply.runMax_zero _ (fun i => RecordoSupply.actX_zero p m U i)

theorem levAt_congr {p : ℝ} {m : ℕ} {U U' : Array N} {n : ℕ}
    (h : ∀ i, (trajectory p m U n).pos i = (trajectory p m U' n).pos i) :
    levAt p m U n = levAt p m U' n := by
  refine le_antisymm (levAt_le_iff.mpr fun i => ?_) (levAt_le_iff.mpr fun i => ?_)
  · calc (trajectory p m U n).pos i = (trajectory p m U' n).pos i := h i
      _ ≤ levAt p m U' n := pos_le_levAt p m U' n i
  · calc (trajectory p m U' n).pos i = (trajectory p m U n).pos i := (h i).symm
      _ ≤ levAt p m U n := pos_le_levAt p m U n i

theorem lowAt_congr {p : ℝ} {m : ℕ} {U U' : Array N} {n : ℕ}
    (h : ∀ i, (trajectory p m U n).pos i = (trajectory p m U' n).pos i) :
    lowAt p m U n = lowAt p m U' n := by
  refine le_antisymm ?_ ?_
  · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
      (fun i : Fin N => (trajectory p m U' n).pos i)
    calc lowAt p m U n ≤ (trajectory p m U n).pos i := lowAt_le_pos p m U n i
      _ = (trajectory p m U' n).pos i := h i
      _ = lowAt p m U' n := hi.symm
  · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
      (fun i : Fin N => (trajectory p m U n).pos i)
    calc lowAt p m U' n ≤ (trajectory p m U' n).pos i := lowAt_le_pos p m U' n i
      _ = (trajectory p m U n).pos i := (h i).symm
      _ = lowAt p m U n := hi.symm

/-- A record at level `d` determines the row level: `levAt` is `d`. -/
theorem levAt_eq_of_recordAt {p : ℝ} {m : ℕ} {U : Array N} {n : ℕ} {d : ℤ}
    (h : RecordAt p m U n d) : levAt p m U n = d := by
  refine le_antisymm (levAt_le_iff.mpr fun i => by rw [h.2 i]) ?_
  calc d = (trajectory p m U n).pos (Classical.arbitrary (Fin N)) := (h.2 _).symm
    _ ≤ levAt p m U n := pos_le_levAt p m U n _

/-- **A simultaneous record at time `n`**: every walker sits at the running maximum `levAt`,
and every walker was strictly below it at every earlier time.  This is `RecordAt` at the
self-determined level, i.e. `min_i X^i_n = max_i X^i_n`. -/
def Row (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) : Prop :=
  RecordAt p m U n (levAt p m U n)

theorem row_iff_exists (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) :
    Row p m U n ↔ ∃ d : ℤ, RecordAt p m U n d :=
  ⟨fun h => ⟨_, h⟩, fun ⟨d, hd⟩ => by rw [Row, levAt_eq_of_recordAt hd]; exact hd⟩

theorem recordAt_of_row {p : ℝ} {m : ℕ} {U : Array N} {n : ℕ} (h : Row p m U n) :
    RecordAt p m U n (levAt p m U n) := h

theorem row_zero (p : ℝ) (m : ℕ) (U : Array N) : Row p m U 0 := by
  refine ⟨fun s hs => absurd hs (Nat.not_lt_zero s), fun i => ?_⟩
  rw [levAt_zero]
  simp

theorem measurableSet_row (p : ℝ) (m : ℕ) (n : ℕ) :
    MeasurableSet {U : Array N | Row p m U n} := by
  have hset : {U : Array N | Row p m U n}
      = ⋃ d : ℤ, ({U : Array N | levAt p m U n = d} ∩ recordSet p m n d) := by
    ext U
    constructor
    · intro h
      exact Set.mem_iUnion.mpr ⟨levAt p m U n, ⟨rfl, h⟩⟩
    · intro h
      obtain ⟨d, hd, hrec⟩ := Set.mem_iUnion.mp h
      have hd' : levAt p m U n = d := hd
      show RecordAt p m U n (levAt p m U n)
      rw [hd']
      exact hrec
  rw [hset]
  exact MeasurableSet.iUnion fun d =>
    ((measurable_levAt p m n) (measurableSet_singleton d)).inter
      (measurableSet_recordSet p m n d)


/-! ## Totalised "first time after `t`"

The paper's `S_q, T_q` take values in `ℕ ∪ {∞}`, and the definitions are totalised with
`inf ∅ = ∞`.  `firstAfter P t` is that totalisation: the least `n > t` with `P n`, or `⊤`. -/

noncomputable def firstAfter (P : Array N → ℕ → Prop) (U : Array N) (t : ℕ) : WithTop ℕ := by
  classical
  exact if h : ∃ n, t < n ∧ P U n then ((Nat.find h : ℕ) : WithTop ℕ) else ⊤

theorem firstAfter_eq_coe_iff {P : Array N → ℕ → Prop} {U : Array N} {t u : ℕ} :
    firstAfter P U t = (u : WithTop ℕ) ↔ t < u ∧ P U u ∧ ∀ v, t < v → v < u → ¬ P U v := by
  classical
  constructor
  · intro h
    by_cases hex : ∃ n, t < n ∧ P U n
    · have hfind : Nat.find hex = u := by
        have h2 : ((Nat.find hex : ℕ) : WithTop ℕ) = (u : WithTop ℕ) := by
          rw [firstAfter, dif_pos hex] at h; exact h
        exact_mod_cast h2
      refine ⟨?_, ?_, ?_⟩
      · rw [← hfind]; exact (Nat.find_spec hex).1
      · rw [← hfind]; exact (Nat.find_spec hex).2
      · intro v htv hvu hv
        exact Nat.find_min hex (by rw [hfind]; exact hvu) ⟨htv, hv⟩
    · rw [firstAfter, dif_neg hex] at h
      exact absurd h (by simp)
  · rintro ⟨htu, hPu, hmin⟩
    have hex : ∃ n, t < n ∧ P U n := ⟨u, htu, hPu⟩
    rw [firstAfter, dif_pos hex]
    have hle : Nat.find hex ≤ u := Nat.find_min' hex ⟨htu, hPu⟩
    have hge : u ≤ Nat.find hex := by
      by_contra hlt
      rw [not_le] at hlt
      exact hmin (Nat.find hex) (Nat.find_spec hex).1 hlt (Nat.find_spec hex).2
    have : Nat.find hex = u := le_antisymm hle hge
    rw [this]

theorem firstAfter_eq_top_iff {P : Array N → ℕ → Prop} {U : Array N} {t : ℕ} :
    firstAfter P U t = ⊤ ↔ ∀ n, t < n → ¬ P U n := by
  classical
  constructor
  · intro h n htn hPn
    have hex : ∃ n, t < n ∧ P U n := ⟨n, htn, hPn⟩
    rw [firstAfter, dif_pos hex] at h
    exact absurd h (by simp)
  · intro h
    rw [firstAfter, dif_neg]
    rintro ⟨n, htn, hPn⟩
    exact h n htn hPn

/-- **Prefix determinism of a time-indexed predicate from time `t₀` on**: for `n > t₀` the truth
value at time `n` is decided by the positions up to time `n` alone.  The restriction to `n > t₀`
is exactly what `firstAfter` needs (it only inspects times `> t₀`). -/
def PfxDet (p : ℝ) (m : ℕ) (t₀ : ℕ) (P : Array N → ℕ → Prop) : Prop :=
  ∀ n, t₀ < n → ∀ U U' : Array N, pfxOf p m n U = pfxOf p m n U' → (P U n ↔ P U' n)

theorem pos_congr_of_pfx {p : ℝ} {m : ℕ} {U U' : Array N} {t n : ℕ} (hnt : n ≤ t)
    (h : pfxOf p m t U = pfxOf p m t U') (i : Fin N) :
    (trajectory p m U n).pos i = (trajectory p m U' n).pos i :=
  congrFun (congrFun h ⟨n, Nat.lt_succ_of_le hnt⟩) i

/-- Two arrays with the same position prefix up to `n` agree on the record predicate at `n`. -/
theorem recordAt_congr_pfx {p : ℝ} {m : ℕ} {U U' : Array N} {n : ℕ} {d : ℤ}
    (h : pfxOf p m n U = pfxOf p m n U') :
    (RecordAt p m U n d ↔ RecordAt p m U' n d) := by
  have hpos : ∀ s, s ≤ n → ∀ i, (trajectory p m U s).pos i = (trajectory p m U' s).pos i :=
    fun s hs i => pos_congr_of_pfx hs h i
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun s hs i => ?_, fun i => ?_⟩
    · have hh := h1 s hs i
      rw [hpos s (le_of_lt hs) i] at hh
      exact hh
    · have hh := h2 i
      rw [hpos n le_rfl i] at hh
      exact hh
  · rintro ⟨h1, h2⟩
    refine ⟨fun s hs i => ?_, fun i => ?_⟩
    · have hh := h1 s hs i
      rw [← hpos s (le_of_lt hs) i] at hh
      exact hh
    · have hh := h2 i
      rw [← hpos n le_rfl i] at hh
      exact hh

theorem pfxDet_row (p : ℝ) (m : ℕ) (t₀ : ℕ) :
    PfxDet (N := N) p m t₀ (Row (N := N) p m) := by
  intro n _ U U' h
  have hlev : levAt p m U n = levAt p m U' n :=
    levAt_congr fun i => pos_congr_of_pfx le_rfl h i
  show RecordAt p m U n (levAt p m U n) ↔ RecordAt p m U' n (levAt p m U' n)
  rw [hlev]
  exact recordAt_congr_pfx h

theorem pfxDet_ret (p : ℝ) (m : ℕ) (t : ℕ) :
    PfxDet (N := N) p m t
      (fun (U : Array N) (n : ℕ) => lowAt p m U n ≤ levAt p m U t) := by
  intro n hn U U' h
  have hn' : lowAt p m U n = lowAt p m U' n :=
    lowAt_congr fun i => pos_congr_of_pfx le_rfl h i
  have ht' : levAt p m U t = levAt p m U' t :=
    levAt_congr fun i => pos_congr_of_pfx (le_of_lt hn) h i
  show lowAt p m U n ≤ levAt p m U t ↔ lowAt p m U' n ≤ levAt p m U' t
  rw [hn', ht']

theorem firstAfter_eq_of_pfxDet {p : ℝ} {m : ℕ} {P : Array N → ℕ → Prop} {t : ℕ}
    (hP : PfxDet (N := N) p m t P)
    {U U' : Array N} {u : ℕ} (hu : firstAfter P U t = (u : WithTop ℕ))
    (h : pfxOf p m u U = pfxOf p m u U') : firstAfter P U' t = (u : WithTop ℕ) := by
  rw [firstAfter_eq_coe_iff] at hu ⊢
  obtain ⟨htu, hPu, hmin⟩ := hu
  refine ⟨htu, (hP u htu U U' h).mp hPu, fun v htv hvu hv => ?_⟩
  exact hmin v htv hvu ((hP v htv U U' (pfx_nest (le_of_lt hvu) h)).mpr hv)

theorem measurableSet_firstAfter_coe {P : Array N → ℕ → Prop}
    (hP : ∀ n, MeasurableSet {U : Array N | P U n}) (t u : ℕ) :
    MeasurableSet {U : Array N | firstAfter P U t = (u : WithTop ℕ)} := by
  by_cases htu : t < u
  · have hset : {U : Array N | firstAfter P U t = (u : WithTop ℕ)}
        = {U : Array N | P U u} ∩ ⋂ v ∈ Finset.Ioo t u, {U : Array N | ¬ P U v} := by
      ext U
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq,
        firstAfter_eq_coe_iff]
      exact ⟨fun h => ⟨h.2.1, fun v hv => h.2.2 v (Finset.mem_Ioo.mp hv).1
          (Finset.mem_Ioo.mp hv).2⟩,
        fun h => ⟨htu, h.1, fun v hv1 hv2 hv => h.2 v (Finset.mem_Ioo.mpr ⟨hv1, hv2⟩) hv⟩⟩
    rw [hset]
    exact (hP u).inter (MeasurableSet.biInter (Finset.countable_toSet _)
      fun v _ => (hP v).compl)
  · have hset : {U : Array N | firstAfter P U t = (u : WithTop ℕ)} = ∅ := by
      ext U
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rw [firstAfter_eq_coe_iff]
      rintro ⟨h, -⟩
      exact htu h
    rw [hset]
    exact MeasurableSet.empty

theorem measurableSet_firstAfter_top {P : Array N → ℕ → Prop}
    (hP : ∀ n, MeasurableSet {U : Array N | P U n}) (t : ℕ) :
    MeasurableSet {U : Array N | firstAfter P U t = ⊤} := by
  have hset : {U : Array N | firstAfter P U t = ⊤}
      = ⋂ n : ℕ, {U : Array N | t < n → ¬ P U n} := by
    ext U
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, firstAfter_eq_top_iff]
  rw [hset]
  refine MeasurableSet.iInter fun n => ?_
  by_cases hn : t < n
  · have h' : {U : Array N | t < n → ¬ P U n} = {U : Array N | ¬ P U n} := by
      ext U; simp [hn]
    rw [h']
    exact (hP n).compl
  · have h' : {U : Array N | t < n → ¬ P U n} = univ := by
      ext U; simp [hn]
    rw [h']
    exact MeasurableSet.univ

/-! ## `WithTop ℕ`-bind

`bindTop x f` is `f s` on the finite value `x = s` and `⊤` on `⊤`: the paper's convention that a
totalised time which is already infinite stays infinite. -/

noncomputable def bindTop (x : WithTop ℕ) (f : ℕ → WithTop ℕ) : WithTop ℕ :=
  if h : x = ⊤ then ⊤ else f (x.untop h)

theorem bindTop_coe (u : ℕ) (f : ℕ → WithTop ℕ) : bindTop (u : WithTop ℕ) f = f u := by
  rw [bindTop, dif_neg (by simp)]
  rfl

theorem bindTop_top (f : ℕ → WithTop ℕ) : bindTop ⊤ f = ⊤ := by
  rw [bindTop, dif_pos rfl]

theorem bindTop_eq_coe_iff {x : WithTop ℕ} {f : ℕ → WithTop ℕ} {t : ℕ} :
    bindTop x f = (t : WithTop ℕ) ↔ ∃ s : ℕ, x = (s : WithTop ℕ) ∧ f s = (t : WithTop ℕ) := by
  constructor
  · intro h
    by_cases hx : x = ⊤
    · rw [bindTop, dif_pos hx] at h
      exact absurd h (by simp)
    · refine ⟨x.untop hx, ?_, ?_⟩
      · exact (WithTop.coe_untop x hx).symm
      · rw [bindTop, dif_neg hx] at h; exact h
  · rintro ⟨s, rfl, hf⟩
    rw [bindTop_coe]
    exact hf

theorem bindTop_eq_top_iff {x : WithTop ℕ} {f : ℕ → WithTop ℕ} :
    bindTop x f = ⊤ ↔ x = ⊤ ∨ ∃ s : ℕ, x = (s : WithTop ℕ) ∧ f s = ⊤ := by
  constructor
  · intro h
    by_cases hx : x = ⊤
    · exact Or.inl hx
    · exact Or.inr ⟨x.untop hx, (WithTop.coe_untop x hx).symm, by
        rw [bindTop, dif_neg hx] at h; exact h⟩
  · rintro (rfl | ⟨s, rfl, hf⟩)
    · exact bindTop_top f
    · rw [bindTop_coe]; exact hf

theorem bindTop_assoc (x : WithTop ℕ) (f : ℕ → WithTop ℕ) (g : ℕ → WithTop ℕ) :
    bindTop (bindTop x f) g = bindTop x (fun s => bindTop (f s) g) := by
  by_cases hx : x = ⊤
  · simp [hx, bindTop_top]
  · have h1 : bindTop x f = f (x.untop hx) := by rw [bindTop, dif_neg hx]
    have h2 : bindTop x (fun s => bindTop (f s) g) = bindTop (f (x.untop hx)) g := by
      rw [bindTop, dif_neg hx]
    rw [h1, h2]

/-! ## The row tower: `S_q`, `T_q` -/

/-- The return time `T_q` of the row started at finite time `t`: the first time after `t` at
which the swarm minimum is at most the row level `r_q = levAt t`.  `⊤` if the row never
returns (the paper's `T_q = ∞`). -/
noncomputable def retAfter (p : ℝ) (m : ℕ) (U : Array N) (t : ℕ) : WithTop ℕ :=
  firstAfter (fun U n => lowAt p m U n ≤ levAt p m U t) U t

/-- The next simultaneous record strictly after the finite time `t`; `⊤` if there is none. -/
noncomputable def rowAfter (p : ℝ) (m : ℕ) (U : Array N) (t : ℕ) : WithTop ℕ :=
  firstAfter (Row (N := N) p m) U t

/-- **The row start times `S_q`** (paper: `S_1 = 0`, `S_{q+1} = inf {τ_r : T_q < τ_r < ∞,
Y_r ∈ F}`).  Indexed from `0`, so `S 0` is the paper's `S_1`. -/
noncomputable def S (p : ℝ) (m : ℕ) (U : Array N) : ℕ → WithTop ℕ
  | 0 => 0
  | (q + 1) => bindTop (S p m U q)
      (fun t => bindTop (retAfter p m U t) (fun u => rowAfter p m U u))

/-- **The return times `T_q`** (paper: `T_q = inf {n > S_q : min_i X^i_n ≤ r_q}`, `∞` if the row
never returns).  `T q` is totalised at `⊤` whenever `S_q = ⊤`. -/
noncomputable def T (p : ℝ) (m : ℕ) (U : Array N) (q : ℕ) : WithTop ℕ :=
  bindTop (S p m U q) (fun t => retAfter p m U t)

theorem S_succ_eq (p : ℝ) (m : ℕ) (U : Array N) (q : ℕ) :
    S p m U (q + 1) = bindTop (T p m U q) (fun u => rowAfter p m U u) := by
  show bindTop (S p m U q)
      (fun t => bindTop (retAfter p m U t) (fun u => rowAfter p m U u)) = _
  rw [T, bindTop_assoc]

theorem S_succ_eq_iff {p : ℝ} {m : ℕ} {U : Array N} {q t : ℕ} :
    S p m U (q + 1) = (t : WithTop ℕ) ↔
      ∃ s u : ℕ, S p m U q = (s : WithTop ℕ) ∧ retAfter p m U s = (u : WithTop ℕ) ∧
        rowAfter p m U u = (t : WithTop ℕ) := by
  rw [S_succ_eq, bindTop_eq_coe_iff]
  constructor
  · rintro ⟨u, hT, hrow⟩
    rw [T, bindTop_eq_coe_iff] at hT
    obtain ⟨s, hs, hret⟩ := hT
    exact ⟨s, u, hs, hret, hrow⟩
  · rintro ⟨s, u, hs, hret, hrow⟩
    exact ⟨u, by rw [T, bindTop_eq_coe_iff]; exact ⟨s, hs, hret⟩, hrow⟩

theorem T_eq_of_S_coe {p : ℝ} {m : ℕ} {U : Array N} {q t : ℕ}
    (h : S p m U q = (t : WithTop ℕ)) : T p m U q = retAfter p m U t := by
  rw [T, h, bindTop_coe]

theorem retAfter_eq_coe_iff {p : ℝ} {m : ℕ} {U : Array N} {t u : ℕ} :
    retAfter p m U t = (u : WithTop ℕ) ↔
      t < u ∧ lowAt p m U u ≤ levAt p m U t ∧
        ∀ v, t < v → v < u → levAt p m U t < lowAt p m U v := by
  rw [retAfter, firstAfter_eq_coe_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun v a b => not_le.mp (h3 v a b)⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun v a b hle => absurd hle (not_le.mpr (h3 v a b))⟩

theorem retAfter_eq_top_iff {p : ℝ} {m : ℕ} {U : Array N} {t : ℕ} :
    retAfter p m U t = ⊤ ↔ ∀ n, t < n → levAt p m U t < lowAt p m U n := by
  rw [retAfter, firstAfter_eq_top_iff]
  constructor
  · intro h n hn
    exact not_le.mp (h n hn)
  · intro h n hn hle
    exact absurd hle (not_le.mpr (h n hn))

theorem rowAfter_eq_coe_iff {p : ℝ} {m : ℕ} {U : Array N} {t u : ℕ} :
    rowAfter p m U t = (u : WithTop ℕ) ↔
      t < u ∧ Row p m U u ∧ ∀ v, t < v → v < u → ¬ Row p m U v :=
  firstAfter_eq_coe_iff

theorem rowAfter_eq_top_iff {p : ℝ} {m : ℕ} {U : Array N} {t : ℕ} :
    rowAfter p m U t = ⊤ ↔ ∀ n, t < n → ¬ Row p m U n :=
  firstAfter_eq_top_iff

/-! ## `S_q` is a simultaneous record -/

theorem row_of_S_eq_coe (p : ℝ) (m : ℕ) : ∀ (q t : ℕ) (U : Array N),
    S p m U q = (t : WithTop ℕ) → Row p m U t
  | 0, t, U, h => by
      have h' : (0 : ℕ) = t := Nat.cast_inj.mp h
      subst h'
      exact row_zero p m U
  | (q + 1), t, U, h => by
      obtain ⟨s, u, -, -, hrow⟩ := S_succ_eq_iff.mp h
      exact (rowAfter_eq_coe_iff.mp hrow).2.1

/-! ## Prefix determinism of the tower -/

theorem S_pfx_det (p : ℝ) (m : ℕ) : ∀ (q t : ℕ) (U U' : Array N),
    pfxOf p m t U = pfxOf p m t U' →
      (S p m U q = (t : WithTop ℕ) ↔ S p m U' q = (t : WithTop ℕ)) := by
  intro q
  induction q with
  | zero =>
      intro t U U' _
      have : S p m U 0 = ((0 : ℕ) : WithTop ℕ) := rfl
      rw [this, show S p m U' 0 = ((0 : ℕ) : WithTop ℕ) from rfl]
  | succ q ih =>
      intro t U U' h
      constructor
      · intro hU
        obtain ⟨s, u, hs, hret, hrow⟩ := S_succ_eq_iff.mp hU
        have hsu : s < u := (retAfter_eq_coe_iff.mp hret).1
        have hut : u < t := (rowAfter_eq_coe_iff.mp hrow).1
        refine S_succ_eq_iff.mpr ⟨s, u, ?_, ?_, ?_⟩
        · exact (ih s U U' (pfx_nest (le_of_lt (lt_trans hsu hut)) h)).mp hs
        · exact firstAfter_eq_of_pfxDet (pfxDet_ret p m s) hret
            (pfx_nest (le_of_lt hut) h)
        · exact firstAfter_eq_of_pfxDet (pfxDet_row p m u) hrow h
      · intro hU
        obtain ⟨s, u, hs, hret, hrow⟩ := S_succ_eq_iff.mp hU
        have hsu : s < u := (retAfter_eq_coe_iff.mp hret).1
        have hut : u < t := (rowAfter_eq_coe_iff.mp hrow).1
        refine S_succ_eq_iff.mpr ⟨s, u, ?_, ?_, ?_⟩
        · exact (ih s U U' (pfx_nest (le_of_lt (lt_trans hsu hut)) h)).mpr hs
        · exact firstAfter_eq_of_pfxDet (pfxDet_ret p m s) hret
            (pfx_nest (le_of_lt hut) h).symm
        · exact firstAfter_eq_of_pfxDet (pfxDet_row p m u) hrow h.symm

/-- **`{S_q = t}` is decided by the position prefix at `t`.** -/
theorem S_preimage_pfx (p : ℝ) (m : ℕ) (q t : ℕ) :
    {U : Array N | S p m U q = (t : WithTop ℕ)}
      = {U : Array N | pfxOf p m t U ∈ (pfxOf p m t '' {V : Array N | S p m V q = (t : WithTop ℕ)})} := by
  ext U
  constructor
  · intro h
    exact ⟨U, h, rfl⟩
  · rintro ⟨V, hV, hUV⟩
    exact (S_pfx_det p m q t U V hUV.symm).mpr hV

/-! ## Measurability of the tower fibres -/

theorem measurableSet_lowLeLev (p : ℝ) (m : ℕ) (n t : ℕ) :
    MeasurableSet {U : Array N | lowAt p m U n ≤ levAt p m U t} := by
  have hset : {U : Array N | lowAt p m U n ≤ levAt p m U t}
      = (fun U : Array N => levAt p m U t - lowAt p m U n) ⁻¹' Set.Ici (0 : ℤ) := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ici]
    omega
  rw [hset]
  exact ((measurable_levAt p m t).sub (measurable_lowAt p m n)) measurableSet_Ici

theorem measurableSet_retAfter_coe (p : ℝ) (m : ℕ) (t u : ℕ) :
    MeasurableSet {U : Array N | retAfter p m U t = (u : WithTop ℕ)} :=
  measurableSet_firstAfter_coe (fun n => measurableSet_lowLeLev p m n t) t u

theorem measurableSet_rowAfter_coe (p : ℝ) (m : ℕ) (t u : ℕ) :
    MeasurableSet {U : Array N | rowAfter p m U t = (u : WithTop ℕ)} :=
  measurableSet_firstAfter_coe (fun n => measurableSet_row p m n) t u

theorem measurableSet_S_coe (p : ℝ) (m : ℕ) : ∀ (q t : ℕ),
    MeasurableSet {U : Array N | S p m U q = (t : WithTop ℕ)}
  | 0, t => by
      rcases Nat.eq_zero_or_pos t with h | h
      · subst h
        have : {U : Array N | S p m U 0 = ((0 : ℕ) : WithTop ℕ)} = univ := by
          ext U; simp [S]
        rw [this]; exact MeasurableSet.univ
      · have : {U : Array N | S p m U 0 = (t : WithTop ℕ)} = ∅ := by
          ext U
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
          intro hh
          have h' : (0 : ℕ) = t := Nat.cast_inj.mp hh
          omega
        rw [this]; exact MeasurableSet.empty
  | (q + 1), t => by
      have hset : {U : Array N | S p m U (q + 1) = (t : WithTop ℕ)}
          = ⋃ w : ℕ × ℕ, ({U : Array N | S p m U q = (w.1 : WithTop ℕ)}
              ∩ {U : Array N | retAfter p m U w.1 = (w.2 : WithTop ℕ)}
              ∩ {U : Array N | rowAfter p m U w.2 = (t : WithTop ℕ)}) := by
        ext U
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
        constructor
        · intro h
          obtain ⟨s, u, hs, hret, hrow⟩ := S_succ_eq_iff.mp h
          exact ⟨(s, u), ⟨hs, hret⟩, hrow⟩
        · rintro ⟨⟨s, u⟩, ⟨hs, hret⟩, hrow⟩
          exact S_succ_eq_iff.mpr ⟨s, u, hs, hret, hrow⟩
      rw [hset]
      exact MeasurableSet.iUnion fun w =>
        ((measurableSet_S_coe p m q w.1).inter
          (measurableSet_retAfter_coe p m w.1 w.2)).inter
          (measurableSet_rowAfter_coe p m w.2 t)

/-- `A_q = {S_q < ∞}`: the event on which row `q` has started.  (The paper's `{Q ≥ q}` is
`{S_q < ∞}` under record recurrence; see `Aq_eq_Qrow_ge`.) -/
def Aq (p : ℝ) (m : ℕ) (q : ℕ) : Set (Array N) :=
  ⋃ t : ℕ, {U : Array N | S p m U q = (t : WithTop ℕ)}

theorem mem_Aq_iff {p : ℝ} {m : ℕ} {q : ℕ} {U : Array N} :
    U ∈ Aq (N := N) p m q ↔ ∃ t : ℕ, S p m U q = (t : WithTop ℕ) :=
  Set.mem_iUnion

theorem measurableSet_Aq (p : ℝ) (m : ℕ) (q : ℕ) : MeasurableSet (Aq (N := N) p m q) :=
  MeasurableSet.iUnion fun t => measurableSet_S_coe p m q t

theorem Aq_zero (p : ℝ) (m : ℕ) : Aq (N := N) p m 0 = univ := by
  ext U
  simp only [mem_Aq_iff, Set.mem_univ, iff_true]
  exact ⟨0, rfl⟩

theorem S_coe_or_top (p : ℝ) (m : ℕ) (U : Array N) (q : ℕ) :
    S p m U q = ⊤ ∨ ∃ t : ℕ, S p m U q = (t : WithTop ℕ) :=
  WithTop.recTopCoe (Or.inl rfl) (fun t => Or.inr ⟨t, rfl⟩) (S p m U q)

/-! ## Row levels and the summed escape factor

`Adf q d` is the event "row `q` starts, at a record of level `d`".  On every record cell
`recordSet t d` it coincides with `{S_q = t}`, which is prefix-decided at `t`; that is exactly
the `hpin` hypothesis of `SwarmStoppedPast.measure_record_strictFut`. -/

/-- The level `d` of row `q`. -/
def Adf (p : ℝ) (m : ℕ) (q : ℕ) (d : ℤ) : Set (Array N) :=
  ⋃ t : ℕ, ({U : Array N | S p m U q = (t : WithTop ℕ)} ∩ {U : Array N | levAt p m U t = d})

theorem mem_Adf_iff {p : ℝ} {m : ℕ} {q : ℕ} {d : ℤ} {U : Array N} :
    U ∈ Adf (N := N) p m q d ↔ ∃ t : ℕ, S p m U q = (t : WithTop ℕ) ∧ levAt p m U t = d :=
  Set.mem_iUnion

theorem measurableSet_Adf (p : ℝ) (m : ℕ) (q : ℕ) (d : ℤ) :
    MeasurableSet (Adf (N := N) p m q d) :=
  MeasurableSet.iUnion fun t =>
    (measurableSet_S_coe p m q t).inter ((measurable_levAt p m t) (measurableSet_singleton d))

theorem iUnion_Adf (p : ℝ) (m : ℕ) (q : ℕ) :
    (⋃ d : ℤ, Adf (N := N) p m q d) = Aq (N := N) p m q := by
  ext U
  simp only [Set.mem_iUnion, mem_Adf_iff, mem_Aq_iff]
  constructor
  · rintro ⟨d, t, h, -⟩
    exact ⟨t, h⟩
  · rintro ⟨t, h⟩
    exact ⟨levAt p m U t, t, h, rfl⟩

theorem pairwiseDisjoint_Adf (p : ℝ) (m : ℕ) (q : ℕ) :
    Pairwise (fun d d' => Disjoint (Adf (N := N) p m q d) (Adf (N := N) p m q d')) := by
  intro d d' hne
  rw [Set.disjoint_left]
  intro U h1 h2
  obtain ⟨t1, hS1, hlv1⟩ := mem_Adf_iff.mp h1
  obtain ⟨t2, hS2, hlv2⟩ := mem_Adf_iff.mp h2
  have h12 : t1 = t2 := Nat.cast_inj.mp (hS1.symm.trans hS2)
  subst h12
  exact hne (hlv1.symm.trans hlv2)

/-- **On a record cell of level `d`, the event "row `q` has level `d`" is exactly `{S_q = t}`.**
The record time at a fixed level is unique (`SwarmStoppedPast.recordAt_unique`) and every `S_q` is
a simultaneous record (`row_of_S_eq_coe`). -/
theorem Adf_inter_record (p : ℝ) (m : ℕ) (q : ℕ) (d : ℤ) (t : ℕ) :
    Adf (N := N) p m q d ∩ recordSet p m t d
      = {U : Array N | S p m U q = (t : WithTop ℕ)} ∩ recordSet p m t d := by
  ext U
  simp only [Set.mem_inter_iff, mem_Adf_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨t', hS, hlv⟩, hrec⟩
    have hrow := row_of_S_eq_coe p m q t' U hS
    rw [Row] at hrow
    rw [hlv] at hrow
    exact ⟨hS.trans (by rw [recordAt_unique hrow hrec]) , hrec⟩
  · rintro ⟨hS, hrec⟩
    exact ⟨⟨t, hS, levAt_eq_of_recordAt hrec⟩, hrec⟩

theorem Adf_subset_recordUnion (p : ℝ) (m : ℕ) (q : ℕ) (d : ℤ) :
    Adf (N := N) p m q d ⊆ ⋃ t, recordSet p m t d := by
  intro U hU
  obtain ⟨t, hS, hlv⟩ := mem_Adf_iff.mp hU
  refine Set.mem_iUnion.mpr ⟨t, ?_⟩
  have hrow := row_of_S_eq_coe p m q t U hS
  rw [Row, hlv] at hrow
  exact hrow

/-- On a record at `(t,d)`, `strictFut` is "the swarm minimum stays strictly above `d`". -/
theorem mem_strictFut_iff {p : ℝ} {m : ℕ} {U : Array N} {t : ℕ} {d : ℤ}
    (hrec : RecordAt p m U t d) :
    U ∈ strictFut p m t d ↔ ∀ n, t < n → d < lowAt p m U n := by
  rw [strictFut_iff_noReturn hrec]
  exact forall_congr' fun n => forall_congr' fun _ =>
    (lt_lowAt_iff (p := p) (m := m) (U := U) (n := n) (d := d)).symm

/-- **The escape event of row `q` is the union of the strict-future cells of its record level.** -/
theorem T_top_inter (p : ℝ) (m : ℕ) (q : ℕ) (d : ℤ) :
    Adf (N := N) p m q d ∩ {U : Array N | T p m U q = ⊤}
      = Adf (N := N) p m q d
        ∩ ⋃ t, (recordSet p m t d ∩ strictFut p m t d) := by
  ext U
  constructor
  · rintro ⟨hAdf, hT⟩
    obtain ⟨t, hS, hlv⟩ := mem_Adf_iff.mp hAdf
    have hret : retAfter p m U t = ⊤ := by
      rw [← T_eq_of_S_coe (p := p) (m := m) (U := U) (q := q) hS]
      exact hT
    have hrow := row_of_S_eq_coe p m q t U hS
    rw [Row, hlv] at hrow
    refine ⟨hAdf, Set.mem_iUnion.mpr ⟨t, hrow, ?_⟩⟩
    rw [mem_strictFut_iff hrow]
    rw [retAfter_eq_top_iff] at hret
    intro n hn
    rw [← hlv]
    exact hret n hn
  · rintro ⟨hAdf, hU⟩
    obtain ⟨t, hrec, hsf⟩ := Set.mem_iUnion.mp hU
    have hrec' : RecordAt p m U t d := hrec
    obtain ⟨t', hS, hlv⟩ := mem_Adf_iff.mp hAdf
    have hmem : U ∈ Adf (N := N) p m q d ∩ recordSet p m t d :=
      ⟨mem_Adf_iff.mpr ⟨t', hS, hlv⟩, hrec'⟩
    rw [Adf_inter_record] at hmem
    have htt : S p m U q = (t : WithTop ℕ) := hmem.1
    refine ⟨mem_Adf_iff.mpr ⟨t', hS, hlv⟩, ?_⟩
    show T p m U q = ⊤
    rw [T_eq_of_S_coe (p := p) (m := m) (U := U) (q := q) htt, retAfter_eq_top_iff]
    intro n hn
    have h := (mem_strictFut_iff hrec').mp hsf n hn
    simpa only [levAt_eq_of_recordAt hrec'] using h

theorem measurableSet_T_top (p : ℝ) (m : ℕ) (q : ℕ) :
    MeasurableSet {U : Array N | T p m U q = ⊤} := by
  have hset : {U : Array N | T p m U q = ⊤}
      = ({U : Array N | S p m U q = ⊤}
          ∪ ⋃ t : ℕ, ({U : Array N | S p m U q = (t : WithTop ℕ)}
            ∩ {U : Array N | retAfter p m U t = ⊤})) := by
    ext U
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    rw [show T p m U q =
        bindTop (S p m U q) (fun t => retAfter p m U t) from rfl,
      bindTop_eq_top_iff]
  rw [hset]
  refine MeasurableSet.union ?_ (MeasurableSet.iUnion fun t => ?_)
  · have : {U : Array N | S p m U q = ⊤}
        = (Aq (N := N) p m q)ᶜ := by
      ext U
      simp only [mem_Aq_iff, Set.mem_compl_iff, Set.mem_ofPred_eq]
      exact ⟨fun h ⟨t, ht⟩ => by rw [h] at ht; exact absurd ht.symm (by simp),
        fun h => by
          rcases S_coe_or_top p m U q with h' | ⟨t, ht⟩
          · exact h'
          · exact absurd ⟨t, ht⟩ h⟩
    rw [this]
    exact (measurableSet_Aq p m q).compl
  exact (measurableSet_S_coe p m q t).inter (measurableSet_firstAfter_top
    (fun n => measurableSet_lowLeLev p m n t) t)

/-- **Row-level escape (the paper's `(initfact)` with `B` the whole path space).**

For the actual array law, the mass of "row `q` has started and never returns" is `P(V)` times the
mass of "row `q` has started".  The factor is the constant `P(V) = P(posPath ∈ strictPos)` and it
does not depend on the row index or on the past.

Proof: split by the level `d` of the row start; on each level
`Adf q d ∩ ⋃_t (record_d(t) ∩ strictFut(t,d))` is exactly the strict-future of the row, and
`measure_record_strictFut` gives the factor `P(V)` for the prefix-pinned past `Adf q d`; then sum
over `d` (the `Adf q d` are pairwise disjoint and cover `A_q`). -/
theorem measure_T_top (p : ℝ) (m : ℕ) (q : ℕ) :
    (arrayMeasure N) (Aq (N := N) p m q ∩ {U : Array N | T p m U q = ⊤})
      = (arrayMeasure N) (Aq (N := N) p m q)
        * (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} := by
  classical
  set ν := (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} with hν
  have hlevel : ∀ d : ℤ,
      (arrayMeasure N) (Adf (N := N) p m q d ∩ {U : Array N | T p m U q = ⊤})
        = (arrayMeasure N) (Adf (N := N) p m q d) * ν := by
    intro d
    have hpin : ∀ t : ℕ, Adf (N := N) p m q d ∩ recordSet p m t d
        = {U : Array N | pfxOf p m t U ∈
            (pfxOf p m t '' {V : Array N | S p m V q = (t : WithTop ℕ)})}
          ∩ recordSet p m t d := by
      intro t
      have hpfx : {U : Array N | S p m U q = (t : WithTop ℕ)} =
          {U : Array N | pfxOf p m t U ∈
            (pfxOf p m t '' {V : Array N | S p m V q = (t : WithTop ℕ)})} :=
        S_preimage_pfx p m q t
      calc
        Adf (N := N) p m q d ∩ recordSet p m t d =
            {U : Array N | S p m U q = (t : WithTop ℕ)} ∩ recordSet p m t d :=
          Adf_inter_record p m q d t
        _ = {U : Array N | pfxOf p m t U ∈
            (pfxOf p m t '' {V : Array N | S p m V q = (t : WithTop ℕ)})}
            ∩ recordSet p m t d :=
          congrArg (fun E : Set (Array N) => E ∩ recordSet p m t d) hpfx
    have hmain := measure_record_strictFut (N := N) (p := p) (m := m) (d := d)
      (A := Adf (N := N) p m q d) (measurableSet_Adf p m q d)
      (fun t => pfxOf p m t '' {V : Array N | S p m V q = (t : WithTop ℕ)})
      (fun t => Set.Countable.measurableSet (Set.countable_univ.mono (subset_univ _)))
      hpin
    calc
      (arrayMeasure N) (Adf (N := N) p m q d ∩ {U : Array N | T p m U q = ⊤})
          = (arrayMeasure N) (Adf (N := N) p m q d
              ∩ ⋃ t, (recordSet p m t d ∩ strictFut p m t d)) :=
        congrArg (arrayMeasure N) (T_top_inter p m q d)
      _ = (arrayMeasure N) (Adf (N := N) p m q d ∩ ⋃ t, recordSet p m t d) * ν :=
        hmain
      _ = (arrayMeasure N) (Adf (N := N) p m q d) * ν := by
        have hset : Adf (N := N) p m q d ∩ ⋃ t, recordSet p m t d =
            Adf (N := N) p m q d :=
          Set.inter_eq_left.mpr (Adf_subset_recordUnion p m q d)
        exact congrArg (fun x : ℝ≥0∞ => x * ν) (congrArg (arrayMeasure N) hset)
  have hcover : Aq (N := N) p m q ∩ {U : Array N | T p m U q = ⊤}
      = ⋃ d : ℤ, (Adf (N := N) p m q d ∩ {U : Array N | T p m U q = ⊤}) := by
    rw [← Set.iUnion_inter, iUnion_Adf]
  have hdisj : Pairwise (fun d d' => Disjoint
      (Adf (N := N) p m q d ∩ {U : Array N | T p m U q = ⊤})
      (Adf (N := N) p m q d' ∩ {U : Array N | T p m U q = ⊤})) := by
    intro d d' hne
    exact (pairwiseDisjoint_Adf p m q hne).mono (Set.inter_subset_left) (Set.inter_subset_left)
  have hmeas : ∀ d : ℤ,
      MeasurableSet (Adf (N := N) p m q d ∩ {U : Array N | T p m U q = ⊤}) :=
    fun d => (measurableSet_Adf p m q d).inter (measurableSet_T_top p m q)
  rw [hcover, measure_iUnion hdisj hmeas, tsum_congr hlevel]
  have hsum : (∑' d : ℤ, (arrayMeasure N) (Adf (N := N) p m q d)) * ν =
      (arrayMeasure N) (⋃ d : ℤ, Adf (N := N) p m q d) * ν := by
    have hmeasure : (∑' d : ℤ, (arrayMeasure N) (Adf (N := N) p m q d)) =
        (arrayMeasure N) (⋃ d : ℤ, Adf (N := N) p m q d) :=
      (measure_iUnion (pairwiseDisjoint_Adf p m q)
        (fun d => measurableSet_Adf p m q d)).symm
    exact congrArg (fun x : ℝ≥0∞ => x * ν) hmeasure
  calc
    (∑' d : ℤ, (arrayMeasure N) (Adf (N := N) p m q d) * ν) =
        (∑' d : ℤ, (arrayMeasure N) (Adf (N := N) p m q d)) * ν := by
      rw [ENNReal.tsum_mul_right]
    _ = (arrayMeasure N) (⋃ d : ℤ, Adf (N := N) p m q d) * ν := hsum
    _ = (arrayMeasure N) (Aq (N := N) p m q) * ν :=
      congrArg (fun x : ℝ≥0∞ => x * ν) (congrArg (arrayMeasure N) (iUnion_Adf p m q))

end SwarmAttemptTower
