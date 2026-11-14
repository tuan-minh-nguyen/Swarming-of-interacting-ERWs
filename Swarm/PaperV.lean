/-
# Bridging `SwarmFresh.strictPos` to the paper's `V`, `V_{d,t}` of `RegenPath`

`RegenPath` (accepted, verified) states the paper's first-regeneration identity
`(firstblk)` for the path vocabulary `V`, `V_{d,t}`, `C_{d,t}`, `D`, `tau`.  `FreshLaw` proves
the block factorization for the path law `posPath p m U`.  This file records that the two
vocabularies agree, so that the per-record-time factorization applies verbatim to the paper's
`(firstblk)` decomposition:

* `strictPos_iff_V`: the array-level event `posPath p m U ∈ strictPos` is the paper's `V`;
* `Vdt_iff_relFuture`: on the record event `RecordAt`, the paper's `V_{d,t}` is exactly
  `relFuture p m U t d ∈ strictPos`.

Both are organised so that the right-hand side is a *high-block* condition, which is what
`SwarmFresh.freshlaw_of_subset` consumes.
-/
import Swarm.FreshLaw
import Swarm.RegenPath

open MeasureTheory Set ProbabilityTheory
open Swarming Swarming.Uniform Swarming.Trajectory SwarmRestart
open scoped ENNReal

namespace SwarmFresh

variable {N : ℕ}

/-- The fresh path starts at the origin. -/
theorem posPath_zero (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) :
    (posPath p m U) 0 i = 0 := by
  simp [posPath]

/-- **`strictPos` is the paper's `V`** on the path of the actual trajectory. -/
theorem strictPos_iff_V (p : ℝ) (m : ℕ) (U : Array N) :
    posPath p m U ∈ strictPos (N := N) ↔ RegenPath.V (posPath p m U) := by
  rw [mem_strictPos]
  constructor
  · rintro ⟨-, h⟩ i n hn
    exact h n hn i
  · intro h
    exact ⟨fun i => posPath_zero p m U i, fun n hn i => h i n hn⟩

/-- **`V_{d,t}` is the relative future being in `strictPos`.**  The `n = 0` component of
`strictPos` is the record condition `X_t = d`, which is why `RecordAt` appears as a hypothesis. -/
theorem Vdt_iff_relFuture {p : ℝ} {m : ℕ} {U : Array N} {t : ℕ} {d : ℤ}
    (hrec : RecordAt p m U t d) :
    RegenPath.Vdt (posPath p m U) d t ↔ relFuture p m U t d ∈ strictPos (N := N) := by
  rw [mem_strictPos]
  constructor
  · intro h
    refine ⟨fun i => ?_, fun n hn i => ?_⟩
    · show (trajectory p m U (t + 0)).pos i - d = 0
      rw [Nat.add_zero, hrec.2 i, sub_self]
    · have h' : d < (trajectory p m U (t + n)).pos i := h i n hn
      show 0 < (trajectory p m U (t + n)).pos i - d
      omega
  · rintro ⟨-, h⟩ i n hn
    have h' : 0 < (trajectory p m U (t + n)).pos i - d := h n hn i
    show d < (trajectory p m U (t + n)).pos i
    omega

/-- **The factorization in the paper's `V_{d,t}` vocabulary.**  On the record event, the
probability that the paper's fresh-path event `V_{d,t}` and a further condition `B` hold after a
record at `(t, d)` factorises: it is the record mass times the probability that the fresh path
lies in `strictPos ∩ B`. -/
theorem freshlaw_Vdt (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ) {B : Set (ℕ → Fin N → ℤ)}
    (hB : MeasurableSet B) :
    (arrayMeasure N) {U : Array N | RecordAt p m U t d ∧
        RegenPath.Vdt (posPath p m U) d t ∧ relFuture p m U t d ∈ B}
      = (arrayMeasure N) (recordSet (N := N) p m t d)
        * (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N) ∩ B} := by
  have h := freshlaw_of_subset p m t d measurableSet_strictPos strictPos_subset_nonnegPath hB
  have h1 : {U : Array N | RecordAt p m U t d ∧ RegenPath.Vdt (posPath p m U) d t ∧
        relFuture p m U t d ∈ B}
      = {U : Array N | RecordAt p m U t d ∧ relFuture p m U t d ∈ strictPos (N := N) ∩ B} := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨hrec, hVdt, hB'⟩
      exact ⟨hrec, (Vdt_iff_relFuture hrec).mp hVdt, hB'⟩
    · rintro ⟨hrec, hin, hB'⟩
      exact ⟨hrec, (Vdt_iff_relFuture hrec).mpr hin, hB'⟩
  rw [h1, h]

/-! ### The nearest-neighbour property, and `C_{d,t}` implies the record condition

`RegenPath.Cdt` is the paper's every-level-strict count.  At a first hitting time of level `d`
no walker can be *above* `d` (it would have had to pass through `d`), so `C_{d,t}` implies the
"all walkers strictly below `d` before `t`" clause, i.e. `SwarmRestart.RecordAt`.  This is what
lets the per-record-time block factorization apply to `RegenPath`'s `(firstblk)` decomposition. -/

/-- The actual position path makes `±1` steps. -/
theorem posPath_step (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    |(posPath p m U) (n + 1) i - (posPath p m U) n i| = 1 := by
  simp only [posPath, trajectory_succ, nextWalkState_pos, nextPos, add_sub_cancel_left]
  simp only [drivenStep]
  split_ifs <;> norm_num

/-- **Before the first hit of level `d` every walker is strictly below `d`.** -/
theorem Cdt_pos_lt (p : ℝ) (m : ℕ) (U : Array N) {d t : ℕ}
    (h : RegenPath.Cdt (posPath p m U) d t) :
    ∀ s, s < t → ∀ i, (posPath p m U) s i < (d : ℤ) := by
  have htau := h.1
  have hne : ∀ n, n < t → ∀ i, (posPath p m U) n i ≠ (d : ℤ) := by
    intro n hn i heq
    exact (RegenPath.tau_eq_iff.mp htau).2 n hn i heq
  intro s hs i
  rcases lt_or_ge ((posPath p m U) s i) (d : ℤ) with hlt | hge
  · exact hlt
  · exfalso
    obtain ⟨n, hn, hfn⟩ := RegenPath.exists_lt_of_reaches
      (f := fun k => (posPath p m U) k i) (posPath_zero p m U i)
      (fun k => posPath_step p m U k i) (s := s) (d := (posPath p m U) s i) (e := (d : ℤ))
      rfl (by positivity) (lt_of_le_of_ne hge (Ne.symm (hne s hs i)))
    exact hne n (lt_trans hn hs) i hfn

/-- **`C_{d,t}` implies `RecordAt`.**  The paper's event `C_{d,t}` (first hit of `d` at time `t`,
all walkers at `d` at time `t`, and the earlier levels failing) already forces every walker to be
strictly below `d` before `t`, which is the hypothesis of the translated-segment theorem. -/
theorem Cdt_recordAt (p : ℝ) (m : ℕ) (U : Array N) {d t : ℕ}
    (h : RegenPath.Cdt (posPath p m U) d t) :
    RecordAt p m U t d :=
  ⟨fun s hs i => Cdt_pos_lt p m U h s hs i, fun i => h.2.1 i⟩

end SwarmFresh
