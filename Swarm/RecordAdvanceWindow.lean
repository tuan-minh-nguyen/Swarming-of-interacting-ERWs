/-
# The record-advance tail is a swarm window-stall tail at the record fibre

`QuantitativeRestrictedBand.timeLag p m B T r L` is the literal record-advance
exception `recTimeA r + T*L < recTimeA (r + B*L)`, one of the three single-level
tails of the frontier ledger
`QuantitativeRestrictedBand.advanceClauseAt_of_three_tails`.

This file proves that this tail is *exactly* a finite-window statement about the
actual swarm at the record fibre, with no reference to any other record level:

* `timeLag ⊆ swarmStall` (pointwise, unconditional: no `a.e.`, no speed input).
  Off `ReachAll` every `recTimeA` is the zero fallback, so the record-advance
  exception forces `ReachAll` (`reachAll_of_mem_timeLag`); on `ReachAll` the
  canonical clock is a genuine first-hitting clock (`isRecord_recTimeA`), and the
  running maximum cannot reach level `r + B*L` before `recTimeA (r + B*L)`.  Hence
  if the advance takes more than `T*L` steps, then **every** walker's position
  `T*L` steps after the fibre `recTimeA r` is still strictly below `r + B*L`.

* Consequently the ledger can be rewritten with the record-advance tail replaced
  by this swarm-stall tail: `advanceClauseAt_of_defect_and_swarmStall` and
  `halfClauseAt_of_defect_and_swarmStall`.  This is a genuine sharpening of the
  frontier: the new third tail is a fixed-window object.

* `actX_window_eq` is the exact telescoping identity
  `X i (n+W) = X i n + 2 * upCount - W` for the number of up-jumps of walker `i`
  in the window `[n, n+W)`; on the stall event every argmax walker therefore
  satisfies `2 * upCount < (T + B) * L` (`stall_upCount`,
  `swarmStall_exists_argmax_upCount`).

* Each window step of walker `i` is driven by the *fresh* array coordinate
  `departureCoord p m U (n+t) i`, and the right-jump probability at that step is
  `rightProbability p m …`, which is `p` when the walker is excited and `1/2`
  otherwise; in particular it is always `≥ 1/2` (`one_half_le_rightProbability`).
  Hence the up-jump count dominates the count of fresh coins `≤ 1/2`
  (`coinCount_le_upCount`), and the window's coordinates are pairwise distinct
  (`window_coords_injective`, from `Trajectory.departureCoord_injective`), i.e.
  they are `W` distinct independent coordinates of the product array.

Scoped statement of what is *not* proved here.  The remaining estimate is a
single, fixed-window, actual-array statement: a uniform-in-level bound on the mass
of `swarmStall` (equivalently of the coin-deficiency event of
`swarmStall_exists_argmax_upCount`).  The `≥ 1/2` lower bound on the right-jump
probability is *not* enough to bound that mass: a walker whose steps are all
non-excited makes a fair symmetric walk, whose window displacement is only of
order `√(T*L)`, so the event `upCount ≥ (T + B)*L/2` (which the stall event
excludes) has probability close to `0` for a fair walker, not close to `1`.  The
missing input must therefore be a lower bound on the *excitation surplus* of the
record-fibre walker, i.e. on the number of its window steps that are excited, and
no such bound is proved or assumed here.

No invariant law, no tightness, no nullity, no `MainClaim` is asserted.
-/
import Swarm.QuantitativeRestrictedBand
import Swarm.Trajectory

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped ENNReal BigOperators

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory
open SwarmRecordMeas SwarmRecordMeas.Actual
open RecordDefect RecordoSupply QuantitativeRestrictedBand

namespace RecordAdvanceWindow

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. `ReachAll` is forced by the record-advance exception -/

/-- Off `ReachAll` every level of the defaulted canonical clock is the zero
fallback, so the record-advance exception is empty there. -/
theorem reachAll_of_mem_timeLag {p : ℝ} {m B T r L : ℕ} {U : Array N}
    (h : U ∈ timeLag p m B T r L) : U ∈ ReachAll p m := by
  by_contra hU
  have h0r : recTimeA p m U r = 0 := recTimeA_eq_zero_of_not_reach hU r
  have h0b : recTimeA p m U (r + B * L) = 0 := recTimeA_eq_zero_of_not_reach hU _
  simp only [timeLag, Set.mem_ofPred_eq, h0r, h0b] at h
  exact absurd h (Nat.not_lt_zero _)

/-! ## 2. The swarm window-stall set and the containment -/

/-- **The swarm window-stall set.**  Every walker's position `T*L` steps after the
record fibre of level `r` is still strictly below level `r + B*L`. -/
def swarmStall (p : ℝ) (m B T r L : ℕ) : Set (Array N) :=
  {U | U ∈ ReachAll p m ∧ ∀ i : Fin N,
      actX p m U i (recTimeA p m U r + T * L) < ((r + B * L : ℕ) : ℤ)}

/-- **The record-advance exception is a swarm window stall.**  Pointwise, with no
almost-sure qualifier, no speed hypothesis and no other record level. -/
theorem timeLag_subset_swarmStall {p : ℝ} {m B T r L : ℕ} :
    timeLag p m B T r L ⊆ swarmStall (N := N) p m B T r L := by
  intro U hU
  have hreach : U ∈ ReachAll p m := reachAll_of_mem_timeLag hU
  have hτ : IsRecord (actX p m U) (recTimeA p m U) := isRecord_recTimeA p m U hreach
  refine ⟨hreach, fun i => ?_⟩
  by_contra hcon
  rw [not_lt] at hcon
  have hmax : ((r + B * L : ℕ) : ℤ) ≤ runMax (actX p m U) (recTimeA p m U r + T * L) :=
    le_trans hcon (le_runMax (X := actX p m U) _ i)
  have hlt : recTimeA p m U r + T * L < recTimeA p m U (r + B * L) := hU
  have hrec : runMax (actX p m U) (recTimeA p m U r + T * L) < ((r + B * L : ℕ) : ℤ) :=
    (hτ (r + B * L)).1 _ hlt
  linarith

/-- The measure form: the record-advance mass is at most the swarm window-stall
mass. -/
theorem measure_timeLag_le_swarmStall {p : ℝ} {m B T r L : ℕ} :
    (arrayMeasure N) (timeLag p m B T r L) ≤
      (arrayMeasure N) (swarmStall (N := N) p m B T r L) :=
  measure_mono (timeLag_subset_swarmStall (N := N))

/-! ## 3. The frontier ledger with the sharpened third tail -/

/-- **The source advance clause from two defect tails and the swarm window-stall
tail.**  Identical to `QuantitativeRestrictedBand.advanceClauseAt_of_three_tails`
except that the record-advance tail `timeLag` is replaced by the smaller,
fixed-window object `swarmStall`.  The two `defectHigh` tails are unchanged. -/
theorem advanceClauseAt_of_defect_and_swarmStall (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) (B T C₀ : ℕ) (hC₀ : B + T + 1 ≤ C₀)
    (q₁ q₂ q₃ : ℕ → ℝ≥0∞)
    (h₁ : ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ r : ℕ, C₀ * ℓ ≤ r →
      (arrayMeasure N) (defectHigh (N := N) p m r ℓ) ≤ q₁ ℓ)
    (h₂ : ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ r : ℕ, C₀ * ℓ ≤ r →
      (arrayMeasure N) (defectHigh (N := N) p m (r + B * ℓ) ℓ) ≤ q₂ ℓ)
    (h₃ : ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ r : ℕ, C₀ * ℓ ≤ r →
      (arrayMeasure N) (swarmStall (N := N) p m B T r ℓ) ≤ q₃ ℓ) :
    SourceTightAvail.AdvanceClauseAt (N := N) p m B T C₀ (q₁ + q₂ + q₃) :=
  advanceClauseAt_of_three_tails (N := N) hp0 hp1 hm hN B T C₀ hC₀ q₁ q₂ q₃ h₁ h₂
    (fun ℓ hℓ r hr =>
      (measure_timeLag_le_swarmStall (N := N) (p := p) (m := m) (B := B) (T := T)
        (r := r) (L := ℓ)).trans (h₃ ℓ hℓ r hr))

/-- **The source halving clause from two defect tails and the swarm window-stall
tail.** -/
theorem halfClauseAt_of_defect_and_swarmStall (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) (B T C₀ : ℕ) (hC₀ : B + T + 1 ≤ C₀)
    (q₁ q₂ q₃ : ℕ → ℝ≥0∞)
    (h₁ : ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ r : ℕ, C₀ * ℓ ≤ r →
      (arrayMeasure N) (defectHigh (N := N) p m r ℓ) ≤ q₁ ℓ)
    (h₂ : ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ r : ℕ, C₀ * ℓ ≤ r →
      (arrayMeasure N) (defectHigh (N := N) p m (r + B * ℓ) ℓ) ≤ q₂ ℓ)
    (h₃ : ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ r : ℕ, C₀ * ℓ ≤ r →
      (arrayMeasure N) (swarmStall (N := N) p m B T r ℓ) ≤ q₃ ℓ) :
    SourceTightAvail.HalfClauseAt (N := N) p m B C₀ (q₁ + q₂ + q₃) :=
  halfClauseAt_of_three_tails (N := N) hp0 hp1 hm hN B T C₀ hC₀ q₁ q₂ q₃ h₁ h₂
    (fun ℓ hℓ r hr =>
      (measure_timeLag_le_swarmStall (N := N) (p := p) (m := m) (B := B) (T := T)
        (r := r) (L := ℓ)).trans (h₃ ℓ hℓ r hr))

/-! ## 4. The exact window counting identity -/

/-- **Number of up-jumps of walker `i` in the window `[n, n+W)`**, as an integer
(the integer cast of the natural count of indices `t < W` with
`X i (n+t+1) = X i (n+t) + 1`). -/
noncomputable def upCount (p : ℝ) (m : ℕ) (i : Fin N) (n W : ℕ) (U : Array N) : ℤ :=
  ∑ t ∈ Finset.range W,
    if actX p m U i (n + t + 1) = actX p m U i (n + t) + 1 then (1 : ℤ) else 0

/-- **Exact telescoping identity.**  Over a window of `W` unit steps the change of
position is `2 * upCount - W`. -/
theorem actX_window_eq (p : ℝ) (m : ℕ) (i : Fin N) (U : Array N) (n W : ℕ) :
    actX p m U i (n + W) =
      actX p m U i n + 2 * upCount p m i n W U - (W : ℤ) := by
  induction W with
  | zero => simp [upCount]
  | succ W ih =>
      have hstep : |actX p m U i (n + W + 1) - actX p m U i (n + W)| = 1 :=
        actX_step p m U i (n + W)
      have hcases : actX p m U i (n + W + 1) = actX p m U i (n + W) + 1 ∨
          actX p m U i (n + W + 1) = actX p m U i (n + W) - 1 := by
        have h := (abs_eq (show (0 : ℤ) ≤ 1 by norm_num)).1 hstep
        rcases h with h | h
        · exact Or.inl (by linarith)
        · exact Or.inr (by linarith)
      have hsum : upCount p m i n (W + 1) U = upCount p m i n W U +
          (if actX p m U i (n + W + 1) = actX p m U i (n + W) + 1 then (1 : ℤ) else 0) := by
        simp only [upCount, Finset.sum_range_succ, Nat.add_assoc]
      have hnW : n + (W + 1) = n + W + 1 := by omega
      rcases hcases with h | h
      · have hl : (if actX p m U i (n + W + 1) = actX p m U i (n + W) + 1
            then (1 : ℤ) else 0) = 1 := if_pos h
        rw [hnW, hsum, hl, h, ih]
        push_cast
        ring
      · have hl : (if actX p m U i (n + W + 1) = actX p m U i (n + W) + 1
            then (1 : ℤ) else 0) = 0 := by
          rw [if_neg]
          linarith
        rw [hnW, hsum, hl, h, ih]
        push_cast
        ring

/-- **The stall bound on the up-jump count.**  If walker `i` sits at level `r` at
time `n` and is still strictly below `r + B*L` at time `n + T*L`, then in the
window `[n, n+T*L)` it has *fewer than half plus `B*L/2`* up-jumps:
`2 * upCount < (T + B) * L`. -/
theorem stall_upCount {p : ℝ} {m B T r L n : ℕ} {U : Array N} {i : Fin N}
    (hn : actX p m U i n = (r : ℤ))
    (hlt : actX p m U i (n + T * L) < ((r + B * L : ℕ) : ℤ)) :
    2 * upCount p m i n (T * L) U < (((T + B) * L : ℕ) : ℤ) := by
  have hid := actX_window_eq p m i U n (T * L)
  rw [hn] at hid
  have hlt' : actX p m U i (n + T * L) < (r : ℤ) + (B : ℤ) * (L : ℤ) := by
    have : ((r + B * L : ℕ) : ℤ) = (r : ℤ) + (B : ℤ) * (L : ℤ) := by push_cast; ring
    rw [this] at hlt
    exact hlt
  have hTL : ((T * L : ℕ) : ℤ) = (T : ℤ) * (L : ℤ) := by push_cast; ring
  rw [hTL] at hid
  have hgoal : (((T + B) * L : ℕ) : ℤ) = (T : ℤ) * (L : ℤ) + (B : ℤ) * (L : ℤ) := by
    push_cast
    ring
  rw [hgoal]
  linarith

/-- **On the swarm-stall event every argmax walker under-counts up-jumps.** -/
theorem swarmStall_exists_argmax_upCount {p : ℝ} {m B T r L : ℕ} {U : Array N}
    (h : U ∈ swarmStall (N := N) p m B T r L) :
    ∃ i : Fin N, actX p m U i (recTimeA p m U r) = (r : ℤ) ∧
      2 * upCount p m i (recTimeA p m U r) (T * L) U < ((T + B) * L : ℕ) := by
  obtain ⟨hreach, hstall⟩ := h
  have hτ : IsRecord (actX p m U) (recTimeA p m U) := isRecord_recTimeA p m U hreach
  have hmax : runMax (actX p m U) (recTimeA p m U r) = (r : ℤ) := (hτ r).2
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_mem_eq_sup' (s := Finset.univ) (H := Finset.univ_nonempty)
      (f := fun i : Fin N => actX p m U i (recTimeA p m U r))
  have hi' : actX p m U i (recTimeA p m U r) = (r : ℤ) := by
    rw [← hi]
    exact hmax
  refine ⟨i, hi', ?_⟩
  exact stall_upCount hi' (hstall i)

/-! ## 5. Fresh coordinates and the coin count -/

/-- **One step of walker `i` at time `n`** is driven by the fresh array coordinate
`departureCoord p m U n i` with right-jump probability
`rightProbability p m …`. -/
theorem actX_succ_eq (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (n : ℕ) :
    actX p m U i (n + 1) =
      actX p m U i n + drivenStep (U (departureCoord p m U n i))
        (rightProbability p m (trajectory p m U n).ell i ((trajectory p m U n).pos i)) :=
  rfl

/-- **The right-jump probability is always at least `1/2`.**  It equals `p` on
excited steps and `1/2` otherwise. -/
theorem one_half_le_rightProbability {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m : ℕ)
    (ell : LocalTimes N) (i : Fin N) (x : ℤ) :
    (1 : ℝ) / 2 ≤ rightProbability p m ell i x := by
  unfold rightProbability
  split_ifs with h
  · exact hp
  · exact le_rfl

/-- **The coin count**: the number of window steps whose fresh array coordinate is
`≤ 1/2`. -/
noncomputable def coinCount (p : ℝ) (m : ℕ) (i : Fin N) (n W : ℕ) (U : Array N) : ℤ :=
  ∑ t ∈ Finset.range W,
    if U (departureCoord p m U (n + t) i) ≤ (1 : ℝ) / 2 then (1 : ℤ) else 0

/-- At every window step the up-jump indicator is the indicator of the fresh coin
being `≤` the right-jump probability. -/
theorem upCount_eq_coinIndicator (p : ℝ) (m : ℕ) (i : Fin N) (U : Array N) (n W : ℕ) :
    upCount p m i n W U =
      ∑ t ∈ Finset.range W,
        if U (departureCoord p m U (n + t) i) ≤
            rightProbability p m (trajectory p m U (n + t)).ell i
              ((trajectory p m U (n + t)).pos i)
          then (1 : ℤ) else 0 := by
  unfold upCount
  refine Finset.sum_congr rfl (fun t _ => ?_)
  have hstep := actX_succ_eq p m U i (n + t)
  by_cases hcoin : U (departureCoord p m U (n + t) i) ≤
      rightProbability p m (trajectory p m U (n + t)).ell i
        ((trajectory p m U (n + t)).pos i)
  · have hup : actX p m U i (n + t + 1) = actX p m U i (n + t) + 1 := by
      rw [hstep]
      simp [drivenStep, hcoin]
    rw [if_pos hup, if_pos hcoin]
  · have hup : ¬ (actX p m U i (n + t + 1) = actX p m U i (n + t) + 1) := by
      rw [hstep]
      simp [drivenStep, hcoin]
    rw [if_neg hup, if_neg hcoin]

/-- **The up-jump count dominates the coin count.**  This is the only use of
excitation in the positive direction: `rightProbability ≥ 1/2`. -/
theorem coinCount_le_upCount {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m : ℕ) (i : Fin N)
    (U : Array N) (n W : ℕ) : coinCount p m i n W U ≤ upCount p m i n W U := by
  rw [upCount_eq_coinIndicator]
  refine Finset.sum_le_sum (fun t _ => ?_)
  by_cases hc : U (departureCoord p m U (n + t) i) ≤ (1 : ℝ) / 2
  · have halt : U (departureCoord p m U (n + t) i) ≤
        rightProbability p m (trajectory p m U (n + t)).ell i
          ((trajectory p m U (n + t)).pos i) :=
      le_trans hc (one_half_le_rightProbability hp m _ i _)
    rw [if_pos hc, if_pos halt]
  · rw [if_neg hc]
    split_ifs <;> norm_num

/-- **The window coordinates are pairwise distinct**, hence fresh independent
coordinates of the product array. -/
theorem window_coords_injective (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (n W : ℕ) :
    Function.Injective (fun t : Fin W => departureCoord p m U (n + t.1) i) := by
  intro a b hab
  have h := departureCoord_injective p m U i hab
  exact Fin.ext (by omega)

/-- **The stall event forces a coin deficiency.**  On the swarm window-stall event
every argmax walker's count of *fresh* coins `≤ 1/2` in the window `[n, n+T*L)` is
strictly below `(T + B) * L / 2`. -/
theorem swarmStall_exists_argmax_coinCount {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p)
    {m B T r L : ℕ} {U : Array N}
    (h : U ∈ swarmStall (N := N) p m B T r L) :
    ∃ i : Fin N, actX p m U i (recTimeA p m U r) = (r : ℤ) ∧
      2 * coinCount p m i (recTimeA p m U r) (T * L) U < ((T + B) * L : ℕ) := by
  obtain ⟨i, hi, hcount⟩ := swarmStall_exists_argmax_upCount h
  refine ⟨i, hi, ?_⟩
  have hle := coinCount_le_upCount (N := N) hp m i U (recTimeA p m U r) (T * L)
  linarith

/-! ## 6. The scalar form of the stall event and where the interaction enters -/

/-- **The stall set is a single scalar condition on the running maximum.**  On
`ReachAll`, "every walker is strictly below `r + B*L` at the fibre time `+ T*L`"
is the same as "the running maximum is strictly below `r + B*L`".  So the sharpened
third tail is the fixed-time level statement for the *actual* running maximum. -/
theorem swarmStall_eq_runMax (p : ℝ) (m B T r L : ℕ) :
    swarmStall (N := N) p m B T r L =
      {U | U ∈ ReachAll p m ∧
        RecordDefect.runMax (actX p m U) (recTimeA p m U r + T * L) <
          ((r + B * L : ℕ) : ℤ)} := by
  ext U
  constructor
  · rintro ⟨hreach, hlow⟩
    refine ⟨hreach, ?_⟩
    by_contra hcon
    rw [not_lt] at hcon
    obtain ⟨i, -, hi⟩ :=
      Finset.exists_mem_eq_sup' (s := Finset.univ) (H := Finset.univ_nonempty)
        (f := fun i : Fin N => actX p m U i (recTimeA p m U r + T * L))
    have hle : ((r + B * L : ℕ) : ℤ) ≤ actX p m U i (recTimeA p m U r + T * L) := by
      rw [show actX p m U i (recTimeA p m U r + T * L) =
        RecordDefect.runMax (actX p m U) (recTimeA p m U r + T * L) from hi.symm]
      exact hcon
    exact absurd (hlow i) (not_lt.2 hle)
  · rintro ⟨hreach, hmax⟩
    exact ⟨hreach, fun i => lt_of_le_of_lt (le_runMax (X := actX p m U) _ i) hmax⟩

/-- The right-jump probability is `p` exactly on excited steps. -/
theorem rightProbability_eq_p_of_excited {p : ℝ} {m : ℕ} {ell : LocalTimes N}
    {i : Fin N} {x : ℤ} (h : Excited m ell i x) : rightProbability p m ell i x = p := by
  unfold rightProbability
  simp [h]

/-- The right-jump probability is `1/2` exactly on non-excited steps. -/
theorem rightProbability_eq_half_of_not_excited {p : ℝ} {m : ℕ} {ell : LocalTimes N}
    {i : Fin N} {x : ℤ} (h : ¬ Excited m ell i x) : rightProbability p m ell i x = (1 : ℝ) / 2 := by
  unfold rightProbability
  simp [h]

/-- **A subsingleton swarm never excites.**  With one walker there are no "other"
visits at all, so for `m ≥ 1` the excitation predicate is identically false. -/
theorem not_excited_of_subsingleton [Subsingleton (Fin N)] {m : ℕ} (hm : 1 ≤ m)
    (ell : LocalTimes N) (i : Fin N) (x : ℤ) : ¬ Excited m ell i x := by
  intro h
  have hz : otherVisits ell i x = 0 := by
    unfold otherVisits
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [if_pos (Subsingleton.elim j i)]
  unfold Excited at h
  omega

/-- **No interaction, no excitation:** on a one-walker array with `m ≥ 1` the
right-jump probability is identically `1/2`, i.e. the walker is a fair symmetric
walk.  So the stall/record-advance tail at `N = 1` cannot be controlled by any
argument that only uses `rightProbability ≥ 1/2`; a decaying bound must use
`N ≥ 2` and genuine excitation. -/
theorem rightProbability_eq_half_of_single [Subsingleton (Fin N)] {m : ℕ} (hm : 1 ≤ m)
    (p : ℝ) (ell : LocalTimes N) (i : Fin N) (x : ℤ) :
    rightProbability p m ell i x = (1 : ℝ) / 2 :=
  rightProbability_eq_half_of_not_excited (not_excited_of_subsingleton hm ell i x)

/-- **Co-location produces excitation.**  If every walker has visited the site `x`
at least once and `m ≤ N - 1`, then each walker is excited at `x`: the other
`N - 1` walkers contribute at least one visit each.  This is the mechanism by which
the swarm (as opposed to a single walker) becomes ballistic, and it is exactly the
mechanism the stall tail needs. -/
theorem excited_of_all_visited {m : ℕ} (hm : m ≤ N - 1) {ell : LocalTimes N} {x : ℤ}
    (h : ∀ j : Fin N, 1 ≤ ell j x) (i : Fin N) : Excited m ell i x := by
  have hkey : (N - 1 : ℕ) ≤ otherVisits ell i x := by
    have h1 : otherVisits ell i x = ∑ j ∈ Finset.univ.erase i, ell j x := by
      unfold otherVisits
      have h0 : (fun j => if j = i then (0:ℕ) else ell j x) i = 0 := by simp
      rw [← Finset.sum_erase (s := Finset.univ) (a := i) h0]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj
      simp [hj]
    rw [h1]
    have hcard : (Finset.univ.erase i).card = N - 1 := by simp
    calc (N - 1 : ℕ) = (Finset.univ.erase i).card := hcard.symm
      _ = ∑ j ∈ Finset.univ.erase i, (1 : ℕ) := by simp
      _ ≤ ∑ j ∈ Finset.univ.erase i, ell j x := Finset.sum_le_sum (fun j _ => h j)
  exact le_trans hm hkey

/-- The co-located walkers jump right with probability `p`. -/
theorem rightProbability_eq_p_of_all_visited {p : ℝ} {m : ℕ} (hm : m ≤ N - 1)
    {ell : LocalTimes N} {x : ℤ} (h : ∀ j : Fin N, 1 ≤ ell j x) (i : Fin N) :
    rightProbability p m ell i x = p :=
  rightProbability_eq_p_of_excited (excited_of_all_visited hm h i)

/-! ## 7. The exact split of the window count: coin luck versus excitation surplus -/

/-- **The excitation-surplus count**: the number of window steps on which the
walker's fresh coin falls in the window `(1/2, rightProbability]`, which is possible
only on an excited step. -/
noncomputable def surplusCount (p : ℝ) (m : ℕ) (i : Fin N) (n W : ℕ) (U : Array N) : ℤ :=
  ∑ t ∈ Finset.range W,
    if U (departureCoord p m U (n + t) i) ≤
          rightProbability p m (trajectory p m U (n + t)).ell i
            ((trajectory p m U (n + t)).pos i) ∧
        ¬ (U (departureCoord p m U (n + t) i) ≤ (1 : ℝ) / 2) then (1 : ℤ) else 0

/-- Splitting the up-jump indicator at the fair-coin threshold. -/
theorem ite_split_up (u α : ℝ) (h : (1 : ℝ) / 2 ≤ α) :
    (if u ≤ α then (1 : ℤ) else 0) =
      (if u ≤ (1 : ℝ) / 2 then (1 : ℤ) else 0) +
        (if u ≤ α ∧ ¬ (u ≤ (1 : ℝ) / 2) then (1 : ℤ) else 0) := by
  by_cases h1 : u ≤ (1 : ℝ) / 2
  · have h2 : u ≤ α := le_trans h1 h
    have h3 : ¬ (u ≤ α ∧ ¬ (u ≤ (1 : ℝ) / 2)) := fun hh => hh.2 h1
    rw [if_pos h2, if_pos h1, if_neg h3]
    norm_num
  · by_cases h2 : u ≤ α
    · have h3 : u ≤ α ∧ ¬ (u ≤ (1 : ℝ) / 2) := ⟨h2, h1⟩
      rw [if_pos h2, if_neg h1, if_pos h3]
      norm_num
    · rw [if_neg h2, if_neg h1, if_neg (fun hh => h2 hh.1)]
      norm_num

/-- **Exact decomposition of the up-jump count**: every up-jump is either a coin
`≤ 1/2` or an excitation surplus. -/
theorem upCount_eq_coinCount_add_surplusCount {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m : ℕ)
    (i : Fin N) (U : Array N) (n W : ℕ) :
    upCount p m i n W U = coinCount p m i n W U + surplusCount p m i n W U := by
  rw [upCount_eq_coinIndicator]
  simp only [coinCount, surplusCount, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  exact ite_split_up _ _ (one_half_le_rightProbability hp m _ i _)

/-- **The sharpened form of the missing estimate.**  On the swarm window-stall event
some argmax walker's window `[recTimeA r, recTimeA r + T*L)` satisfies

`2 * (coinCount + surplusCount) < (T + B) * L`,

i.e. the up-jump deficit that the stall event forces is *exactly* a deficiency in
(fresh fair coins `≤ 1/2`) plus (excitation surplus).  Any proof of a decaying
swarm-stall tail must therefore lower-bound the surplus, hence the number of excited
window steps of the record-fibre walker; the `rightProbability ≥ 1/2` bound used in
`coinCount_le_upCount` is not usable for that direction. -/
theorem swarmStall_exists_argmax_coin_add_surplus {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p)
    {m B T r L : ℕ} {U : Array N} (h : U ∈ swarmStall (N := N) p m B T r L) :
    ∃ i : Fin N, actX p m U i (recTimeA p m U r) = (r : ℤ) ∧
      2 * (coinCount p m i (recTimeA p m U r) (T * L) U +
        surplusCount p m i (recTimeA p m U r) (T * L) U) < (((T + B) * L : ℕ) : ℤ) := by
  obtain ⟨i, hi, hcount⟩ := swarmStall_exists_argmax_upCount h
  refine ⟨i, hi, ?_⟩
  rw [← upCount_eq_coinCount_add_surplusCount hp]
  exact hcount

end RecordAdvanceWindow
