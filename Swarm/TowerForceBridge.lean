/-
# `{D = ⊤}` and the strict-attempt all-fail event are the same event

## What this file establishes

`TowerExhaust.D_top_subset_infiniteFailure` proves one inclusion:
`{D = ⊤} ⊆ InfiniteFailure`.  This file proves the **converse**, so on `ReachAll` the two events
are *equal*:

  `RegenPath.D (posPath p m U) = ⊤ ↔ U ∈ InfiniteFailure p m`

(`D_top_iff_infiniteFailure_of_reach`), and since `ReachAll` is almost sure for `1/2 < p < 1`,
`2 ≤ m`, `2 ≤ N` (`M4RecordGeom.ae_reachAll`), the two events have the same `arrayMeasure`
mass (`measure_D_top_eq_measure_infiniteFailure`).

The bridge is the exact equivalence between a `RegenPath` regeneration level and a successful
canonical strict attempt:

  `StrictAttempt p m U r ↔ RegenPath.Reg (posPath p m U) ((r : ℤ) + 1)`

(`reg_of_strictAttempt`, `strictAttempt_of_reg`).  The reverse direction is where `ReachAll`
enters: `recTimeA` is the zero-defaulted record clock, and a regeneration level forces the level
to be reached, hence `ReachAll`.

Combining with `TowerForceSharp.diverging_force_iff_infiniteFailure_eq_zero` gives the exact
frontier statement of the capstone:

  `(F) ⟺ μ {D = ⊤} = 0`     (`divergent_force_iff_D_top_eq_zero`),

i.e. the per-level conditional tower force is *literally* the hypothesis
`HpathFromDtopNull.hpath_of_D_top_null` consumes.  It is not a weaker input.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `opaque`, no `unsafe`.
-/
import Swarm.TowerForceSharp
import Swarm.RegenPath
import Swarm.PaperV

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open MeasureTheory Set ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace TowerForceBridge

open Swarming.Uniform Swarming.Trajectory SwarmTowerExhaust RawStrictAttemptTower
open SwarmRestart SwarmFresh SwarmRecordMeas SwarmRecordMeas.Actual

variable {N : ℕ} [Nonempty (Fin N)] {p : ℝ} {m : ℕ}

/-! ### 1. Strict attempts are exactly positive regeneration levels -/

/-- **A successful canonical strict attempt is a regeneration level.**  No reachability is
needed: the record clause of `RegenAtStrict` at the canonical record time `recTimeA (r+1)` gives
the simultaneous record, and the strict future clause gives `tau = recTimeA (r+1)`. -/
theorem reg_of_strictAttempt {U : Array N} {r : ℕ} (h : StrictAttempt p m U r) :
    RegenPath.Reg (posPath p m U) ((r : ℤ) + 1) := by
  obtain ⟨hrec, hstrict⟩ := h
  simp only [attemptTime, attemptLevel] at hrec hstrict
  have hcast : ((r + 1 : ℕ) : ℤ) = (r : ℤ) + 1 := by push_cast; ring
  have hall : ∀ i, (trajectory p m U (recTimeA p m U (r + 1))).pos i = (r : ℤ) + 1 :=
    fun i => by rw [hrec.2 i, hcast]
  have hbelow : ∀ s, s < recTimeA p m U (r + 1) → ∀ i,
      (trajectory p m U s).pos i < (r : ℤ) + 1 := fun s hs i => by
    have h1 := hrec.1 s hs i
    rwa [hcast] at h1
  have hstrict' : ∀ n, 0 < n → ∀ i,
      (r : ℤ) + 1 < (trajectory p m U (recTimeA p m U (r + 1) + n)).pos i :=
    fun n hn i => by
      have h1 := hstrict n hn i
      rwa [hcast] at h1
  refine ⟨recTimeA p m U (r + 1), ?_, hall, ?_⟩
  · rw [RegenPath.tau_eq_iff]
    exact ⟨⟨Classical.arbitrary (Fin N), hall _⟩,
      fun s hs i => ne_of_lt (hbelow s hs i)⟩
  · intro n hn i
    obtain ⟨n', rfl⟩ : ∃ n', n = recTimeA p m U (r + 1) + n' :=
      ⟨n - recTimeA p m U (r + 1), by omega⟩
    exact hstrict' n' (by omega) i

/-- **A positive regeneration level is a successful canonical strict attempt.**  This direction
uses `ReachAll`: off it the record clock `recTimeA` is the zero fallback, and a regeneration
level forces every level to be reached. -/
theorem strictAttempt_of_reg {U : Array N} {r : ℕ}
    (hreach : U ∈ ReachAll p m) (h : RegenPath.Reg (posPath p m U) ((r : ℤ) + 1)) :
    StrictAttempt p m U r := by
  obtain ⟨t, htau, hall, hafter⟩ := h
  have hcast : ((r + 1 : ℕ) : ℤ) = (r : ℤ) + 1 := by push_cast; ring
  have htau' := RegenPath.tau_eq_iff.mp htau
  -- no walker is above level `r+1` before `t`
  have hbelow : ∀ s, s < t → ∀ i, (trajectory p m U s).pos i < (r : ℤ) + 1 := by
    intro s hs i
    have hne : (posPath p m U) s i ≠ (r : ℤ) + 1 := htau'.2 s hs i
    rcases lt_or_ge ((posPath p m U) s i) ((r : ℤ) + 1) with hlt | hge
    · exact hlt
    · exfalso
      obtain ⟨n, hn, hhit⟩ := RegenPath.exists_lt_of_reaches
        (f := fun u => (posPath p m U) u i)
        (SwarmFresh.posPath_zero p m U i) (fun u => SwarmFresh.posPath_step p m U u i)
        (s := s) (d := (posPath p m U) s i) rfl (e := (r : ℤ) + 1) (by positivity)
        (lt_of_le_of_ne hge (Ne.symm hne))
      exact htau'.2 n (lt_trans hn hs) i hhit
  -- the record clock fires exactly at `t`
  have hrecTime : recTimeA p m U (r + 1) = t := by
    rw [recTimeA_eq_iff (N := N) p m U (r + 1) t hreach]
    refine ⟨?_, ?_⟩
    · rw [hcast]
      refine le_antisymm ?_ ?_
      · refine Finset.sup'_le _ _ fun i _ => ?_
        show (RecordoSupply.actX p m U) i t ≤ (r : ℤ) + 1
        simpa [RecordoSupply.actX, posPath] using le_of_eq (hall i)
      · have h := Finset.le_sup'
          (f := fun i => (RecordoSupply.actX p m U) i t) (Finset.mem_univ (Classical.arbitrary (Fin N)))
        have hx : (RecordoSupply.actX p m U) (Classical.arbitrary (Fin N)) t = (r : ℤ) + 1 := by
          simpa [RecordoSupply.actX, posPath] using hall (Classical.arbitrary (Fin N))
        rw [hx] at h
        exact h
    · intro j hj hcon
      rw [hcast] at hcon
      -- the running maximum is attained, so some walker is at level `r+1` at time `j < t`
      obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (H := Finset.univ_nonempty)
        (f := fun i => (RecordoSupply.actX p m U) i j)
      have hval : (RecordoSupply.actX p m U) i j = (r : ℤ) + 1 := by
        rw [← hi]
        exact hcon
      exact htau'.2 j hj i (by simpa [RecordoSupply.actX, posPath] using hval)
  -- rebuild the strict regeneration at the canonical record time
  have hreg : RegenAtStrict p m U (recTimeA p m U (r + 1)) (((r + 1 : ℕ)) : ℤ) := by
    rw [hrecTime, hcast]
    refine ⟨⟨fun s hs i => hbelow s hs i, hall⟩, fun n hn i => ?_⟩
    exact hafter (t + n) (by omega) i
  exact hreg

/-- **`{D = ⊤}` is exactly the strict-attempt all-fail event**, on `ReachAll`. -/
theorem D_top_iff_infiniteFailure_of_reach {U : Array N} (hreach : U ∈ ReachAll p m) :
    RegenPath.D (posPath p m U) = ⊤ ↔ U ∈ InfiniteFailure (N := N) p m := by
  constructor
  · intro hD
    rw [InfiniteFailure, Set.mem_ofPred_eq, not_exists]
    intro k hk
    have hreg := reg_of_strictAttempt (N := N) (p := p) (m := m) hk
    have hex : ∃ r : ℕ, 1 ≤ r ∧ RegenPath.Reg (posPath p m U) (r : ℤ) :=
      ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k), by simpa using hreg⟩
    rw [RegenPath.D, dif_pos hex] at hD
    exact WithTop.coe_ne_top hD
  · intro hU
    rw [InfiniteFailure, Set.mem_ofPred_eq, not_exists] at hU
    have hex : ¬ ∃ r : ℕ, 1 ≤ r ∧ RegenPath.Reg (posPath p m U) (r : ℤ) := by
      rintro ⟨r, hr, hreg⟩
      obtain ⟨e, rfl⟩ : ∃ e : ℕ, r = e + 1 := ⟨r - 1, by omega⟩
      apply hU e
      have := strictAttempt_of_reg (N := N) (p := p) (m := m) hreach hreg
      simpa using this
    rw [RegenPath.D, dif_neg hex]

/-! ### 2. Equality of the masses -/

/-- **The `{D = ⊤}` mass is the all-fail mass.**  `ReachAll` is almost sure on the raw array
(`M4RecordGeom.ae_reachAll`), so the two events agree almost everywhere. -/
theorem measure_D_top_eq_measure_infiniteFailure (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) :
    (arrayMeasure N) {U : Array N | RegenPath.D (posPath p m U) = ⊤}
      = (arrayMeasure N) (InfiniteFailure (N := N) p m) := by
  refine MeasureTheory.measure_congr (s := {U : Array N | RegenPath.D (posPath p m U) = ⊤})
    (t := InfiniteFailure (N := N) p m) ?_
  filter_upwards [M4RecordGeom.ae_reachAll (N := N) (p := p) (m := m) hp0 hp1 hm hN]
    with U hU
  exact propext (D_top_iff_infiniteFailure_of_reach (N := N) (p := p) (m := m) hU)

/-- **`{D = ⊤}` is null exactly when the tower has almost sure success.** -/
theorem D_top_measure_eq_zero_iff_infiniteFailure_eq_zero
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) :
    (arrayMeasure N) {U : Array N | RegenPath.D (posPath p m U) = ⊤} = 0
      ↔ (arrayMeasure N) (InfiniteFailure (N := N) p m) = 0 := by
  rw [measure_D_top_eq_measure_infiniteFailure (N := N) hp0 hp1 hm hN]

/-- **The capstone's per-level conditional force is *literally* the `HpathFromDtopNull`
input.**  `(F) ⟺ μ {D = ⊤} = 0`; neither side is a weaker hypothesis than the other. -/
theorem divergent_force_iff_D_top_eq_zero (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) :
    (∃ q : ℕ → ℝ, (∀ r, 0 ≤ q r) ∧ (∀ r, q r ≤ 1) ∧
      Tendsto (fun R : ℕ => ∑ r ∈ Finset.range R, q r) atTop atTop ∧
      ∀ r, q r * (arrayMeasure N).real (NoSucc (N := N) p m r)
        ≤ (arrayMeasure N).real (FirstSuccessCell (N := N) p m r))
      ↔ (arrayMeasure N) {U : Array N | RegenPath.D (posPath p m U) = ⊤} = 0 := by
  rw [TowerForceSharp.diverging_force_iff_infiniteFailure_eq_zero,
    measure_D_top_eq_measure_infiniteFailure (N := N) hp0 hp1 hm hN]

end TowerForceBridge
