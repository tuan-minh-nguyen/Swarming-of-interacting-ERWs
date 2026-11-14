/-
  # The actual common record-time carrier for the literal `(lococc)`

  The accepted `LocOccQ` development states the paper's display `(lococc)` for arrays `U` lying in
  the *concrete record cell*

      recCell p m i j r s L = {records of `i` and `j` and the position of `i` all in `[r-L, r]` at
                                time `s`}

  and every one of the twelve model-side fields (`hocc`, `hZs`, `hZt`, `hMiw`, `hXMiS`, `hXtMi`,
  `hXW`, `hcont1..hcont5`, `hMjmono`, `hMjstep`, `hJstruct`) is discharged from that membership.
  What was *not* established there is that the cell is the paper's own carrier: the paper states
  `(lococc)` on `G_{r,L,T} ∩ {d_r ≤ L}` at the record time `τ_r = inf{n : max_i X_n^i = r}`, with
  `d_r = r - min_i X_{τ_r}^i`, and nothing in the accepted development relates `recCell` to that
  set.  This file supplies exactly that relation, on the actual iid uniform array; see
  `README.md` for the exact list of what remains explicit and what is not claimed.

  No `sorry`, no `axiom`, no `native_decide`; every declaration's axiom set is checked externally
  in `LocOccRecordCarrierAudit.lean`.
-/
import Swarm.LocOccQCell
import Swarm.ActualRecordFiltration

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory
open Swarming.Enl Swarming.Enl.VdriftAssembly

namespace LocOccRecordCarrier

variable {N : ℕ} [Nonempty (Fin N)]

/-! ### 1. The position maximum `max_i X_n^i` and its unit-step bounds -/

/-- One step of the actual trajectory is `±1`, in the `actX` normal form. -/
theorem actX_step_abs (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    |RecordoSupply.actX p m U i (n + 1) - RecordoSupply.actX p m U i n| = 1 := by
  have hstep : RecordoSupply.actX p m U i (n + 1) = RecordoSupply.actX p m U i n +
      drivenStep (U (i, (trajectory p m U n).pos i,
          (trajectory p m U n).ell i ((trajectory p m U n).pos i)))
        (rightProbability p m (trajectory p m U n).ell i ((trajectory p m U n).pos i)) := by
    show (trajectory p m U (n + 1)).pos i = (trajectory p m U n).pos i + _
    rw [trajectory_succ, nextWalkState_pos, nextPos]
  rw [hstep, add_sub_cancel_left]
  unfold drivenStep
  split <;> norm_num

/-- The position maximum `max_i X_n^i` rises by at most one per step. -/
theorem posMax_succ_le (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) :
    RecordDefect.runMax (RecordoSupply.actX p m U) (n + 1) ≤
      RecordDefect.runMax (RecordoSupply.actX p m U) n + 1 := by
  have h : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      RecordoSupply.actX p m U i (n + 1) ≤
        RecordDefect.runMax (RecordoSupply.actX p m U) n + 1 := by
    intro i _
    have h1 : RecordoSupply.actX p m U i (n + 1) ≤ RecordoSupply.actX p m U i n + 1 := by
      have := (abs_le.mp (le_of_eq (actX_step_abs p m U n i))).2
      omega
    have h2 := RecordDefect.le_runMax (X := RecordoSupply.actX p m U) n i
    omega
  exact Finset.sup'_le Finset.univ_nonempty
    (fun i => RecordoSupply.actX p m U i (n + 1)) h

/-- The position maximum `max_i X_n^i` falls by at most one per step. -/
theorem le_posMax_succ (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) :
    RecordDefect.runMax (RecordoSupply.actX p m U) n ≤
      RecordDefect.runMax (RecordoSupply.actX p m U) (n + 1) + 1 := by
  have h : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      RecordoSupply.actX p m U i n ≤
        RecordDefect.runMax (RecordoSupply.actX p m U) (n + 1) + 1 := by
    intro i _
    have h1 : RecordoSupply.actX p m U i n ≤ RecordoSupply.actX p m U i (n + 1) + 1 := by
      have := (abs_le.mp (le_of_eq (actX_step_abs p m U n i))).1
      omega
    have h2 := RecordDefect.le_runMax (X := RecordoSupply.actX p m U) (n + 1) i
    omega
  exact Finset.sup'_le Finset.univ_nonempty
    (fun i => RecordoSupply.actX p m U i n) h

/-- The position maximum at time zero vanishes (all walkers start at the origin). -/
theorem posMax_zero (p : ℝ) (m : ℕ) (U : Array N) :
    RecordDefect.runMax (RecordoSupply.actX p m U) 0 = 0 :=
  RecordoSupply.runMax_zero (RecordoSupply.actX p m U) (RecordoSupply.actX_zero p m U)

/-! ### 2. On the first-record prefix the maximum never exceeds the level -/

/-- **The maximum is bounded by the record level up to the record time.**  At the first time `s` at
which `max_i X_s^i = r`, unit steps force `max_i X_t^i ≤ r` for every `t ≤ s`: a first crossing
above `r` would have had to pass through `r` one step earlier. -/
theorem posMax_le_of_firstRecordAt {p : ℝ} {m r s : ℕ} {U : Array N}
    (h : U ∈ ActualRecordFiltration.firstRecordAt (N := N) p m r s) :
    ∀ t ≤ s, RecordDefect.runMax (RecordoSupply.actX p m U) t ≤ (r : ℤ) := by
  intro t
  induction t with
  | zero =>
      intro _
      rw [posMax_zero]
      show (0 : ℤ) ≤ (r : ℤ)
      omega
  | succ t ih =>
      intro ht
      have hle := ih (by omega)
      have hne : RecordDefect.runMax (RecordoSupply.actX p m U) t ≠ (r : ℤ) := h.2 t (by omega)
      have hstep := posMax_succ_le p m U t
      by_contra hbad
      have hge : (r : ℤ) + 1 ≤ RecordDefect.runMax (RecordoSupply.actX p m U) (t + 1) := by omega
      have : (r : ℤ) ≤ RecordDefect.runMax (RecordoSupply.actX p m U) t := by omega
      exact hne (le_antisymm hle this)

/-! ### 3. The record carrier is contained in the concrete record cell, for every pair -/

/-- **The adapted record carrier lies in the concrete record cell for every pair.**

`recordPrefixBand p m r s L` is the paper's `{τ_r = s} ∩ {d_r ≤ L}` in finite, adapted,
lookahead-free form (`firstRecordAt` plus the defect band at the revealed time `s`).  On it,
`max_i X_s^i = r` and `min_i X_s^i ≥ r - L`, so every walker's *record* at time `s` and the
position of `i` at time `s` lie in `[r - L, r]`; that is exactly `LocOccQ.recCell p m i j r s L`.

This is the "covered-field" step: the twelve geometric fields that
`LocOcc.lococc_window_eighth` consumes are available on the paper's own carrier, simultaneously
for all pairs, with no weakening of the cell and no promotion to `recTimeA`. -/
theorem recordPrefixBand_subset_recCell (p : ℝ) (m : ℕ)
    (i j : Fin N) (r s L : ℕ) :
    ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ⊆
      LocOccQ.recCell p m i j r s L := by
  intro U hU
  obtain ⟨hfirst, hdef⟩ := hU
  have hmax : RecordDefect.runMax (RecordoSupply.actX p m U) s = (r : ℤ) := hfirst.1
  have hle : ∀ t ≤ s, RecordDefect.runMax (RecordoSupply.actX p m U) t ≤ (r : ℤ) :=
    posMax_le_of_firstRecordAt hfirst
  -- the defect bound, in integer form
  have hminmax : RecordDefect.runMin (RecordoSupply.actX p m U) s ≤
      RecordDefect.runMax (RecordoSupply.actX p m U) s :=
    RecordDefect.runMin_le_runMax (X := RecordoSupply.actX p m U) s
  have hminle : RecordDefect.runMin (RecordoSupply.actX p m U) s ≤ (r : ℤ) := by
    rw [← hmax]; exact hminmax
  have hdef' : ((r : ℤ) - RecordDefect.runMin (RecordoSupply.actX p m U) s).toNat ≤ L := hdef
  have hdefL : (r : ℤ) - RecordDefect.runMin (RecordoSupply.actX p m U) s ≤ (L : ℤ) :=
    Int.toNat_le.1 hdef'
  have hlow : (r : ℤ) - (L : ℤ) ≤ RecordDefect.runMin (RecordoSupply.actX p m U) s := by
    linarith
  -- every walker's running record at time `s` lies in `[r-L, r]`
  have hrec_le : ∀ k : Fin N, runMax p m U k s ≤ (r : ℤ) := by
    intro k
    have h : ∀ t ∈ Finset.range (s + 1), (trajectory p m U t).pos k ≤ (r : ℤ) := by
      intro t ht
      have hts : t ≤ s := by
        have := Finset.mem_range.mp ht
        omega
      have h1 : (trajectory p m U t).pos k ≤
          RecordDefect.runMax (RecordoSupply.actX p m U) t :=
        RecordDefect.le_runMax (X := RecordoSupply.actX p m U) t k
      have h2 := hle t hts
      omega
    exact Finset.sup'_le _ _ h
  have hrec_ge : ∀ k : Fin N, (r : ℤ) - (L : ℤ) ≤ runMax p m U k s := by
    intro k
    have h1 : RecordDefect.runMin (RecordoSupply.actX p m U) s ≤
        (trajectory p m U s).pos k :=
      RecordDefect.runMin_le (X := RecordoSupply.actX p m U) s k
    have h2 : (trajectory p m U s).pos k ≤ runMax p m U k s := le_runMax p m U k s
    omega
  have hpos_le : (trajectory p m U s).pos i ≤ (r : ℤ) := by
    have h1 : (trajectory p m U s).pos i ≤
        RecordDefect.runMax (RecordoSupply.actX p m U) s :=
      RecordDefect.le_runMax (X := RecordoSupply.actX p m U) s i
    have h2 : RecordDefect.runMax (RecordoSupply.actX p m U) s = (r : ℤ) := hmax
    omega
  have hpos_ge : (r : ℤ) - (L : ℤ) ≤ (trajectory p m U s).pos i := by
    have h1 : RecordDefect.runMin (RecordoSupply.actX p m U) s ≤
        (trajectory p m U s).pos i :=
      RecordDefect.runMin_le (X := RecordoSupply.actX p m U) s i
    omega
  exact ⟨hrec_ge j, hrec_le j, hrec_ge i, hrec_le i, hpos_ge, hpos_le⟩

/-! ### 4. The carrier has strictly positive measure: the all-rise cylinder -/

/-- The finite set of array coordinates that the first `s` departures of every walker can read:
site `y` with `|y| ≤ s` and departure number `k ≤ s`. -/
noncomputable def riseCoords (N s : ℕ) : Finset (Fin N × ℤ × ℕ) :=
  (Finset.univ : Finset (Fin N)) ×ˢ
    (Finset.Icc (-(s : ℤ)) (s : ℤ) ×ˢ Finset.range (s + 1))

/-- The explicit product cylinder on which every coordinate read during the first `s` departures
is `< 1/2`.  On it every walker steps right at every one of its first `s` departures. -/
def allRise (N s : ℕ) : Set (Array N) :=
  Set.pi (riseCoords N s) (fun _ => Set.Iio (1 / 2))

/-- The local time of a walker is at most the number of departures plus one. -/
theorem ell_le_succ (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) :
    ∀ (n : ℕ) (x : ℤ), (trajectory p m U n).ell i x ≤ n + 1 := by
  intro n
  induction n with
  | zero =>
      intro x
      rw [trajectory_zero]
      show (if x = 0 then (1 : ℕ) else 0) ≤ 0 + 1
      split <;> omega
  | succ n ih =>
      intro x
      rw [trajectory_succ, nextWalkState_ell]
      have := ih x
      split <;> omega

/-- Membership in the coordinate set, in the form used below. -/
theorem mem_riseCoords {N s : ℕ} {i : Fin N} {y : ℤ} {k : ℕ}
    (h1 : -(s : ℤ) ≤ y) (h2 : y ≤ (s : ℤ)) (h3 : k ≤ s) :
    (i, y, k) ∈ riseCoords N s := by
  refine Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
  · exact Finset.mem_Icc.mpr ⟨h1, h2⟩
  · refine Finset.mem_range.mpr ?_
    show k < s + 1
    omega

/-- **The all-rise path.**  On the cylinder `allRise N s` every walker is at `n` at time `n`, for
every `n ≤ s`. -/
theorem allRise_pos_eq (p : ℝ) (hp : 1 / 2 ≤ p) (m s : ℕ) {U : Array N}
    (hU : U ∈ allRise N s) :
    ∀ n ≤ s, ∀ i : Fin N, (trajectory p m U n).pos i = (n : ℤ) := by
  intro n
  induction n with
  | zero =>
      intro _ i
      simp
  | succ n ih =>
      intro hn i
      have hpos := ih (by omega) i
      have hyleft : -((n : ℤ)) ≥ -(s : ℤ) := by
        have : (n : ℤ) ≤ (s : ℤ) := by exact_mod_cast (by omega : n ≤ s)
        omega
      have hell : (trajectory p m U n).ell i ((trajectory p m U n).pos i) ≤ s := by
        have h1 := ell_le_succ p m U i n ((trajectory p m U n).pos i)
        omega
      have hmem : (i, (trajectory p m U n).pos i,
          (trajectory p m U n).ell i ((trajectory p m U n).pos i)) ∈ riseCoords N s := by
        refine mem_riseCoords ?_ ?_ hell
        · rw [hpos]; omega
        · rw [hpos]; exact_mod_cast (by omega : n ≤ s)
      have hlt : U (i, (trajectory p m U n).pos i,
          (trajectory p m U n).ell i ((trajectory p m U n).pos i)) < 1 / 2 := hU _ hmem
      have hα : (1 / 2 : ℝ) ≤ rightProbability p m (trajectory p m U n).ell i
          ((trajectory p m U n).pos i) :=
        one_half_le_rightProbability hp m _ i _
      have hstep : drivenStep (U (i, (trajectory p m U n).pos i,
          (trajectory p m U n).ell i ((trajectory p m U n).pos i)))
          (rightProbability p m (trajectory p m U n).ell i
            ((trajectory p m U n).pos i)) = 1 :=
        drivenStep_eq_one_of_le (le_of_lt (lt_of_lt_of_le hlt hα))
      rw [trajectory_succ, nextWalkState_pos, nextPos, hstep, hpos]
      push_cast
      ring

/-- On the all-rise cylinder the position maximum at time `t ≤ s` is exactly `t`. -/
theorem allRise_runMax (p : ℝ) (hp : 1 / 2 ≤ p) (m s : ℕ) {U : Array N}
    (hU : U ∈ allRise N s) {t : ℕ} (ht : t ≤ s) :
    RecordDefect.runMax (RecordoSupply.actX p m U) t = (t : ℤ) := by
  have hpos := allRise_pos_eq p hp m s hU t ht
  refine le_antisymm ?_ ?_
  · exact Finset.sup'_le Finset.univ_nonempty _ (fun i _ => (hpos i).le)
  · obtain ⟨i⟩ := (inferInstance : Nonempty (Fin N))
    have h := Finset.le_sup' (s := (Finset.univ : Finset (Fin N)))
      (f := fun i => RecordoSupply.actX p m U i t) (Finset.mem_univ i)
    exact (hpos i) ▸ h

/-- On the all-rise cylinder the position minimum at time `t ≤ s` is exactly `t`. -/
theorem allRise_runMin (p : ℝ) (hp : 1 / 2 ≤ p) (m s : ℕ) {U : Array N}
    (hU : U ∈ allRise N s) {t : ℕ} (ht : t ≤ s) :
    RecordDefect.runMin (RecordoSupply.actX p m U) t = (t : ℤ) := by
  have hpos := allRise_pos_eq p hp m s hU t ht
  refine le_antisymm ?_ ?_
  · obtain ⟨i⟩ := (inferInstance : Nonempty (Fin N))
    have h := Finset.inf'_le (s := (Finset.univ : Finset (Fin N)))
      (f := fun i => RecordoSupply.actX p m U i t) (Finset.mem_univ i)
    exact (hpos i) ▸ h
  · exact Finset.le_inf' Finset.univ_nonempty _ (fun i _ => (hpos i).ge)

/-- **The all-rise cylinder lies in the record carrier** at `r = s`. -/
theorem allRise_subset_recordPrefixBand (p : ℝ) (hp : 1 / 2 ≤ p) (m s L : ℕ) :
    allRise N s ⊆
      ActualRecordFiltration.recordPrefixBand (N := N) p m s s L := by
  intro U hU
  have hmaxs : RecordDefect.runMax (RecordoSupply.actX p m U) s = (s : ℤ) :=
    allRise_runMax p hp m s hU le_rfl
  have hmins : RecordDefect.runMin (RecordoSupply.actX p m U) s = (s : ℤ) :=
    allRise_runMin p hp m s hU le_rfl
  refine ⟨⟨hmaxs, ?_⟩, ?_⟩
  · intro t ht
    have h := allRise_runMax p hp m s hU (le_of_lt ht)
    rw [h]
    have hne : t ≠ s := by omega
    exact fun hc => hne (by exact_mod_cast hc)
  · show ((s : ℤ) - RecordDefect.runMin (RecordoSupply.actX p m U) s).toNat ≤ L
    rw [hmins]
    simp

/-- The all-rise cylinder is a genuine product cylinder of the countable array measure. -/
theorem measure_allRise (N s : ℕ) :
    arrayMeasure N (allRise N s) = (ENNReal.ofReal (1 / 2)) ^ (riseCoords N s).card := by
  have h1 : arrayMeasure N (allRise N s) =
      ∏ c ∈ riseCoords N s, uniform01 (Set.Iio (1 / 2)) :=
    Measure.infinitePi_pi (μ := fun _ => uniform01) (s := riseCoords N s)
      (t := fun _ => Set.Iio (1 / 2)) (fun i _ => measurableSet_Iio)
  rw [h1, Finset.prod_const]
  congr 1
  exact uniform01_Iio (by norm_num)

/-- The all-rise cylinder has strictly positive measure. -/
theorem measure_allRise_pos (N s : ℕ) : 0 < arrayMeasure N (allRise N s) := by
  rw [measure_allRise]
  have h : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / 2) := by
    rw [ENNReal.ofReal_pos]
    norm_num
  exact pos_iff_ne_zero.mpr (pow_ne_zero _ h.ne')

/-- **Non-vacuity of the paper's record carrier, at the actual array law.**
For every `p ≥ 1/2`, every `m`, every level `s ≥ 1` and every defect band `L`, the adapted record
carrier `{τ_s = s} ∩ {d_s ≤ L}` has strictly positive `arrayMeasure N` measure. -/
theorem recordPrefixBand_pos (p : ℝ) (hp : 1 / 2 ≤ p) (m : ℕ) (s L : ℕ) (hs : 1 ≤ s) :
    0 < arrayMeasure N (ActualRecordFiltration.recordPrefixBand (N := N) p m s s L) :=
  lt_of_lt_of_le (measure_allRise_pos N s)
    (measure_mono (allRise_subset_recordPrefixBand p hp m s L))

/-- **Non-vacuity of the concrete record cell `LocOccQ.recCell`.**  This is the statement recorded
as missing in the accepted `LocOccQ` development: the cell on which the literal `(lococc)` display
was proved is not empty, and in fact carries a strictly positive measure coming from the explicit
all-rise cylinder of the actual iid array. -/
theorem recCell_pos (p : ℝ) (hp : 1 / 2 ≤ p) (m : ℕ) (i j : Fin N) (s L : ℕ) (hs : 1 ≤ s) :
    0 < arrayMeasure N (LocOccQ.recCell p m i j s s L) :=
  lt_of_lt_of_le (recordPrefixBand_pos p hp m s L hs)
    (measure_mono (recordPrefixBand_subset_recCell p m i j s s L))

/-- The all-rise cylinder itself is a nonempty set of arrays (the identically zero array). -/
theorem allRise_nonempty (N s : ℕ) : (allRise N s).Nonempty :=
  ⟨fun _ => 0, fun _ _ => by
    show (0 : ℝ) ∈ Set.Iio (1 / 2)
    exact Set.mem_Iio.mpr (by norm_num)⟩

/-- The record carrier is monotone in the defect band `L`. -/
theorem recordPrefixBand_mono_L (p : ℝ) (m : ℕ) (r s : ℕ) {L L' : ℕ} (h : L ≤ L') :
    ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ⊆
      ActualRecordFiltration.recordPrefixBand (N := N) p m r s L' := by
  rintro U ⟨h1, h2⟩
  exact ⟨h1, le_trans h2 h⟩

/-! ### 5. The accepted all-pairs `hQ` estimate at the record carrier -/

/-- **The accepted `hQ` window estimate instantiated at the record carrier.**

`LocOccQ.measureReal_qplDrop_le` needs an `enlFilt p m σ`-measurable start cell.  The record carrier
is one (`measurableSet_recordPrefixBand`), with `σ = s`; no `ReachAll` hypothesis, no adaptedness of
`recTimeA` and no promotion of the start time is used.  Both residuals are kept with the cell
weight: `shiftedContDefect` (the shifted compensator defect) and `harmDefect` (the harmonic-site
defect). -/
theorem measureReal_recordCarrier_qplDrop_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m : ℕ) (eps : ℝ) (i j : Fin N) (hε : 0 < eps) {r s n : ℕ} (hn : 1 ≤ n)
    {V : ℝ} (hV1 : 1 ≤ V) {w M : ℕ} (hw : 1 ≤ w)
    {KQ L34 : ℝ} (hKQ : 0 < KQ) (hL34 : 0 < L34) (L : ℕ) :
    (arrayMeasure N).real
        (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
          LocOccQ.qplDrop (ProjLedger.Qpl p m eps i j) s n (KQ * L34)) ≤
      (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L) *
          (2 * ((n : ℝ) + 1) * Real.exp (-((KQ * L34 / 2) ^ 2) /
            (4 * (n : ℝ) * (QplPredEnv.envB p m V (QplWindow.envC p m V)) ^ 2))) +
        ((arrayMeasure N).real
            (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
              ShiftedQplResidual.shiftedContDefect p m i j s w M n) +
          (arrayMeasure N).real
            (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
              QplWindow.harmDefect p m j V w M)) :=
  LocOccQ.measureReal_qplDrop_le (N := N) hp0 hp1 m eps i j hε hn
    (ActualRecordFiltration.measurableSet_recordPrefixBand p m r s L) hV1 hw hKQ hL34

/-! ### 6. The literal `(lococc)` display on the record carrier -/

/-- **The paper's `(lococc)` display in literal indicator form, on the actual record carrier.**

This is `LocOccQ.lococc_recCell_indicator` with its cell hypothesis replaced by membership in the
record carrier: by `recordPrefixBand_subset_recCell` the twelve record-geometry fields then hold
automatically and are no longer hypotheses.  What remains explicit is exactly the group of
estimates that live on the array law and on the projected potential, not on the carrier:
the step ledger `hled` (a.e., `LocOccQ.ae_hled_eighth`), the potential slopes `hslopeLo`/`hslopeHi`,
the squared-site window sum `hint` (`LocOccR1.array_locsum_h_start`), the projected oscillation
`hosc`, the compensator drop `hQd` and the two endpoint corrections `hFs`/`hFt`.  No field is
weakened and no constant is changed. -/
theorem lococc_on_recordCarrier_indicator {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {i j : Fin N} {ε : ℝ} (hε : 0 < ε) {r s t T L : ℕ} (hT : 1 ≤ T)
    (hr : (T + 3) * L ≤ r) (hst : s ≤ t) (htT : t ≤ s + T * L)
    {U : Array N} (hU : U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s L)
    {K β Kp CH KQ KF L34 : ℝ}
    (hled : ∀ u : ℕ,
      SwarmOcc.occInd (fun q => (trajectory p m U q).pos i)
          (fun q => runMax p m U j q) u - 1 / 8
        ≤ (Zproj p m ε i j U (u + 1) - Zproj p m ε i j U u)
          + VdriftAssembly.Jcorr p m ε i j U u
          - (ProjLedger.Qpl p m ε i j (u + 1) U - ProjLedger.Qpl p m ε i j u U))
    (hslopeLo : ∀ x : ℕ, x < (runMax p m U j t).toNat →
      projH p m j t U ((x : ℤ) + 1) - projH p m j t U (x : ℤ)
        = SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x)
    (hslopeHi : ∀ x : ℕ, (runMax p m U j t).toNat ≤ x →
      0 ≤ projH p m j t U ((x : ℤ) + 1) - projH p m j t U (x : ℤ) ∧
      projH p m j t U ((x : ℤ) + 1) - projH p m j t U (x : ℤ) ≤ Kp)
    (hint : ∀ a b : ℕ, r - (T + 2) * L ≤ a →
      b ≤ r - (T + 2) * L + ((2 * T + 2) * L + 1) → a ≤ b →
      ∑ x ∈ Finset.Ico a b,
          (SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x) ^ 2
        ≤ K * ((b : ℝ) - (a : ℝ)) + K * β)
    (hosc : projH p m j t U (((trajectory p m U s).pos i).toNat : ℤ)
        - projH p m j s U (((trajectory p m U s).pos i).toNat : ℤ) ≤ CH * L34)
    (hQd : U ∉ LocOccQ.qplDrop (ProjLedger.Qpl p m ε i j) s (T * L) (KQ * L34))
    (hFs : |SwarmOcc.Fcorr (aRec p m) ε (bRec p m s j U)
        ((trajectory p m U s).pos i - runMax p m U j s)| ≤ KF * L34)
    (hFt : |SwarmOcc.Fcorr (aRec p m) ε (bRec p m t j U)
        ((trajectory p m U t).pos i - runMax p m U j t)| ≤ KF * L34)
    (hK : 1 ≤ K) (hβ : 0 ≤ β) (hKp : 0 ≤ Kp) (hCH : 0 ≤ CH) (hKF : 0 ≤ KF)
    (hKQ : 0 ≤ KQ) (hL34 : 0 ≤ L34) (h1L34 : 1 ≤ L34) (hβL : β ≤ L34) :
    ∑ u ∈ Finset.Ico s t,
        (if ((trajectory p m U u).pos i).toNat ≤ (runMax p m U j u).toNat then (1 : ℝ) else 0)
      ≤ ((K + Kp) + 2 * (2 * ((p / (1 - p) + 4) ^ 2 / (ε * (1 - aRec p m) ^ 2))) * K + 1) *
          (((runMax p m U i t).toNat : ℝ) - ((runMax p m U i s).toNat : ℝ)
            + (((runMax p m U i s).toNat : ℝ) - (((trajectory p m U s).pos i).toNat : ℝ))
            + max 0 (((runMax p m U i s).toNat : ℝ) - ((runMax p m U j s).toNat : ℝ)))
        + ((t : ℝ) - (s : ℝ)) / 8
        + (K + CH + 2 * KF
            + 4 * (2 * ((p / (1 - p) + 4) ^ 2 / (ε * (1 - aRec p m) ^ 2))) * K
            + 2 * KQ + 1) * L34 :=
  LocOccQ.lococc_recCell_indicator (N := N) hp0 hp1 hε hT hr hst htT
    (recordPrefixBand_subset_recCell p m i j r s L hU) hled hslopeLo hslopeHi hint hosc hQd
    hFs hFt hK hβ hKp hCH hKF hKQ hL34 h1L34 hβL

/-! ### 7. Reconciling the window: the five containments at every time of the window -/

/-- Unit steps upwards: the position at a later time exceeds the earlier one by at most the
elapsed time. -/
theorem pos_le_add (p : ℝ) (m : ℕ) (U : Array N) (k : Fin N) :
    ∀ {s u : ℕ}, s ≤ u →
      (trajectory p m U u).pos k ≤ (trajectory p m U s).pos k + ((u - s : ℕ) : ℤ) := by
  intro s u h
  induction u, h using Nat.le_induction with
  | base => simp
  | succ u hsu ih =>
      have h1 : (trajectory p m U (u + 1)).pos k ≤ (trajectory p m U u).pos k + 1 :=
        pos_succ_le p m U u k
      have hcast : ((u + 1 - s : ℕ) : ℤ) = ((u - s : ℕ) : ℤ) + 1 := by
        have : u + 1 - s = (u - s) + 1 := by omega
        rw [this]; push_cast; ring
      rw [hcast]
      linarith

/-- Unit steps downwards: the position at a later time is at least the earlier one minus the
elapsed time. -/
theorem sub_le_pos (p : ℝ) (m : ℕ) (U : Array N) (k : Fin N) :
    ∀ {s u : ℕ}, s ≤ u →
      (trajectory p m U s).pos k - ((u - s : ℕ) : ℤ) ≤ (trajectory p m U u).pos k := by
  intro s u h
  induction u, h using Nat.le_induction with
  | base => simp
  | succ u hsu ih =>
      have h1 : (trajectory p m U u).pos k - 1 ≤ (trajectory p m U (u + 1)).pos k := by
        have := (abs_le.mp (le_of_eq (actX_step_abs p m U u k))).1
        change RecordoSupply.actX p m U k u - 1 ≤ RecordoSupply.actX p m U k (u + 1)
        omega
      have hcast : ((u + 1 - s : ℕ) : ℤ) = ((u - s : ℕ) : ℤ) + 1 := by
        have : u + 1 - s = (u - s) + 1 := by omega
        rw [this]; push_cast; ring
      rw [hcast]
      linarith

/-- The running record is monotone in time. -/
theorem runMax_mono_own (p : ℝ) (m : ℕ) (U : Array N) (k : Fin N) {s s' : ℕ} (h : s ≤ s') :
    runMax p m U k s ≤ runMax p m U k s' := by
  refine Finset.sup'_le _ _ fun t ht => ?_
  have ht' : t ∈ Finset.range (s' + 1) := by
    rw [Finset.mem_range] at ht ⊢
    omega
  exact Finset.le_sup' (fun t => (trajectory p m U t).pos k) ht'

/-- **The running record stays in the top of the window.**  From the record carrier at time `s`,
every walker's running record at any later time `u` of the window is at most `r` plus the elapsed
time. -/
theorem runMax_le_add {p : ℝ} {m r s L : ℕ} {U : Array N}
    (hU : U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s L) (k : Fin N)
    {u : ℕ} (hsu : s ≤ u) :
    runMax p m U k u ≤ (r : ℤ) + ((u - s : ℕ) : ℤ) := by
  have hband : ∀ t ≤ s, RecordDefect.runMax (RecordoSupply.actX p m U) t ≤ (r : ℤ) :=
    posMax_le_of_firstRecordAt hU.1
  have hpos := pos_le_add p m U k hsu
  refine Finset.sup'_le _ _ fun t ht => ?_
  have htu : t ≤ u := by
    have := Finset.mem_range.mp ht
    omega
  change RecordoSupply.actX p m U k t ≤ (r : ℤ) + ((u - s : ℕ) : ℤ)
  rcases le_or_gt t s with hts | hts
  · have h1 : (trajectory p m U t).pos k ≤ RecordDefect.runMax (RecordoSupply.actX p m U) t :=
      RecordDefect.le_runMax (X := RecordoSupply.actX p m U) t k
    have h2 := hband t hts
    have h3 : (0 : ℤ) ≤ ((u - s : ℕ) : ℤ) := by positivity
    change (trajectory p m U t).pos k ≤ (r : ℤ) + ((u - s : ℕ) : ℤ)
    linarith
  · have h1 : (trajectory p m U t).pos k ≤
        (trajectory p m U s).pos k + ((t - s : ℕ) : ℤ) := pos_le_add p m U k (le_of_lt hts)
    have h2 : (trajectory p m U s).pos k ≤ RecordDefect.runMax (RecordoSupply.actX p m U) s :=
      RecordDefect.le_runMax (X := RecordoSupply.actX p m U) s k
    have h3 := hband s le_rfl
    have h4 : ((t - s : ℕ) : ℤ) ≤ ((u - s : ℕ) : ℤ) := by
      have : t - s ≤ u - s := by omega
      exact_mod_cast this
    change (trajectory p m U t).pos k ≤ (r : ℤ) + ((u - s : ℕ) : ℤ)
    linarith

/-- **The paper's window at every time of the window, on the record carrier.**

On the record carrier at level `r` and time `s`, for every time `s'` with `s ≤ s' ≤ s + T*L` the
five containments that `LocOcc.lococc_window_eighth` consumes hold with the paper's
`A₀ = r - (T+2)L` and `Lw = (2T+2)L + 1`:

    A₀ ≤ X^i_{s'},   A₀ ≤ M^j_{s'},   X^i_{s'} ≤ A₀ + Lw,
    M^i_{s'} + 1 ≤ A₀ + Lw,   M^j_{s'} ≤ A₀ + Lw.

Only `hcont1..hcont5` at the *start* time are supplied by the cell (`recCell` at `s`); at later
times they are propagated by unit steps from the carrier, with no new geometric hypothesis.  This
is the reconciliation of `LocOccQ.recCell` with the window used by the projected-potential packages.
-/
theorem carrier_window_containment {p : ℝ} {m r s L T : ℕ}
    {U : Array N} (hU : U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s L)
    (i j : Fin N) {s' : ℕ} (h1 : s ≤ s') (h2 : s' ≤ s + T * L) :
    (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ (trajectory p m U s').pos i ∧
    (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ runMax p m U j s' ∧
    (trajectory p m U s').pos i ≤ (r : ℤ) + ((T * L : ℕ) : ℤ) + 1 ∧
    runMax p m U i s' + 1 ≤ (r : ℤ) + ((T * L : ℕ) : ℤ) + 1 ∧
    runMax p m U j s' ≤ (r : ℤ) + ((T * L : ℕ) : ℤ) + 1 := by
  obtain ⟨hj_low, -, hi_low, -, hpos_ge, hpos_le⟩ :=
    recordPrefixBand_subset_recCell p m i j r s L hU
  have helapsed : ((s' - s : ℕ) : ℤ) ≤ ((T * L : ℕ) : ℤ) := by
    have h : s' - s ≤ T * L := by omega
    exact_mod_cast h
  have helapsed0 : (0 : ℤ) ≤ ((s' - s : ℕ) : ℤ) := by positivity
  have hposlow : (trajectory p m U s').pos i ≥ (trajectory p m U s).pos i - ((s' - s : ℕ) : ℤ) :=
    sub_le_pos p m U i h1
  have hposhigh : (trajectory p m U s').pos i ≤ (trajectory p m U s).pos i + ((s' - s : ℕ) : ℤ) :=
    pos_le_add p m U i h1
  have hrec_i := runMax_le_add hU i h1
  have hrec_j := runMax_le_add hU j h1
  have hrecj_low : (r : ℤ) - (L : ℤ) ≤ runMax p m U j s := hj_low
  have hrec_i_low : (r : ℤ) - (L : ℤ) ≤ runMax p m U i s := hi_low
  have hTL : ((L : ℤ)) + ((s' - s : ℕ) : ℤ) ≤ ((L : ℤ)) + ((T * L : ℕ) : ℤ) := by linarith
  have hT2 : ((L : ℤ)) + ((T * L : ℕ) : ℤ) ≤ (((T + 2) * L : ℕ) : ℤ) := by
    have : L + T * L ≤ (T + 2) * L := by nlinarith
    exact_mod_cast this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `A₀ ≤ X^j_{s'}`: the position falls by at most the elapsed time
    linarith
  · -- `A₀ ≤ M^i_{s'}`: records only grow, and the record at `s` was at least `r - L`
    have h1' : runMax p m U j s ≤ runMax p m U j s' := runMax_mono_own p m U j h1
    linarith
  · linarith
  · linarith
  · linarith

/-! ### 8. The joint exception set of the step ledger and the `hQ` field -/

/-- The pointwise step ledger of `(lococc)` at `ε = 1/8`, in the exact shape consumed by
`LocOccQ.lococc_recCell_eighth`. -/
def LedgerShape (p : ℝ) (m : ℕ) (i j : Fin N) (U : Array N) : Prop :=
  ∀ u : ℕ,
    SwarmOcc.occInd (fun q => (trajectory p m U q).pos i) (fun q => runMax p m U j q) u - 1 / 8
      ≤ (Zproj p m (1 / 8) i j U (u + 1) - Zproj p m (1 / 8) i j U u)
        + VdriftAssembly.Jcorr p m (1 / 8) i j U u
        - (ProjLedger.Qpl p m (1 / 8) i j (u + 1) U - ProjLedger.Qpl p m (1 / 8) i j u U)

/-- The step ledger holds `arrayMeasure N`-almost surely (no carrier, no cell, no conditioning):
this is `LocOccQ.ae_hled_eighth` restated as a null exception set. -/
theorem ae_ledgerShape {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) :
    ∀ᵐ U ∂(arrayMeasure N), LedgerShape p m i j U :=
  LocOccQ.ae_hled_eighth (N := N) hp0 hp1 hm hij

/-- **The joint exception set of the two array-law fields, measured on the record carrier.**

On the record carrier, the set where *either* the step ledger fails *or* the adapted compensator
drops by more than `KQ * L34` somewhere in a window of length `n` carries at most the single-start
maximal Azuma price of `LocOccQ.measureReal_qplDrop_le` plus the two start-cell-weighted residuals
`shiftedContDefect` and `harmDefect`.  The ledger's own exception set is `arrayMeasure N`-null and
disappears exactly, not by an unweighted estimate. -/
theorem measureReal_recordCarrier_ledger_hQ_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) {i j : Fin N} (hij : i ≠ j) {r s n L : ℕ} (hn : 1 ≤ n)
    {V : ℝ} (hV1 : 1 ≤ V) {w M : ℕ} (hw : 1 ≤ w) {KQ L34 : ℝ} (hKQ : 0 < KQ) (hL34 : 0 < L34) :
    (arrayMeasure N).real
        ((ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
            {U | ¬ LedgerShape p m i j U}) ∪
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
            LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s n (KQ * L34))) ≤
      (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L) *
          (2 * ((n : ℝ) + 1) * Real.exp (-((KQ * L34 / 2) ^ 2) /
            (4 * (n : ℝ) * (QplPredEnv.envB p m V (QplWindow.envC p m V)) ^ 2))) +
        ((arrayMeasure N).real
            (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
              ShiftedQplResidual.shiftedContDefect p m i j s w M n) +
          (arrayMeasure N).real
            (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
              QplWindow.harmDefect p m j V w M)) := by
  have hnull : (arrayMeasure N) {U : Array N | ¬ LedgerShape p m i j U} = 0 := by
    rw [← MeasureTheory.ae_iff]
    exact ae_ledgerShape hp0 hp1 hm hij
  have hpart : (arrayMeasure N).real
      (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
        {U : Array N | ¬ LedgerShape p m i j U}) = 0 := by
    have h1 : (arrayMeasure N)
        (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
          {U : Array N | ¬ LedgerShape p m i j U}) = 0 :=
      le_antisymm (le_trans (measure_mono Set.inter_subset_right) (le_of_eq hnull))
        (by positivity)
    simp [MeasureTheory.measureReal_def, h1]
  refine (measureReal_union_le _ _).trans ?_
  rw [hpart]
  simp only [zero_add]
  exact measureReal_recordCarrier_qplDrop_le (N := N) hp0 hp1 m (1 / 8) i j (by norm_num) hn
    hV1 hw hKQ hL34 L

/-! ### 9. The explicit mass of the witness cylinder (a quantitative lower bound) -/

/-- The number of coordinates the witness cylinder constrains: `N * (2s+1) * (s+1)`. -/
theorem card_riseCoords (N s : ℕ) :
    (riseCoords N s).card = N * (2 * s + 1) * (s + 1) := by
  rw [riseCoords, Finset.card_product, Finset.card_product, Finset.card_univ,
    Fintype.card_fin, Finset.card_range, Int.card_Icc]
  have h : ((s : ℤ) + 1 - (-(s : ℤ))).toNat = 2 * s + 1 := by
    have hcast : (s : ℤ) + 1 - (-(s : ℤ)) = (((2 * s + 1 : ℕ)) : ℤ) := by
      push_cast
      ring
    rw [hcast, Int.toNat_natCast]
  rw [h]
  ring

/-- The exact measure of the witness cylinder, in closed form. -/
theorem measure_allRise_closed (N s : ℕ) :
    arrayMeasure N (allRise N s) = (ENNReal.ofReal (1 / 2)) ^ (N * (2 * s + 1) * (s + 1)) := by
  rw [measure_allRise, card_riseCoords]

/-- **An explicit lower bound for the carrier's mass.**  For every `p ≥ 1/2`, `s ≥ 1` and every
defect band `L`, the record carrier at level `s` carries at least `(1/2)^{N(2s+1)(s+1)}` of the
array measure.  The exponent is the crude one of the all-rise cylinder — it is far from the truth
(the true mass at level `s` is of order `2^{-Ns}`) but it is an explicit positive lower bound coming
from the actual iid array, which is what positivity at the start needs. -/
theorem le_measure_recordPrefixBand (p : ℝ) (hp : 1 / 2 ≤ p) (m : ℕ) (s L : ℕ) (hs : 1 ≤ s) :
    (ENNReal.ofReal (1 / 2)) ^ (N * (2 * s + 1) * (s + 1)) ≤
      arrayMeasure N (ActualRecordFiltration.recordPrefixBand (N := N) p m s s L) := by
  rw [← measure_allRise_closed N s]
  exact measure_mono (allRise_subset_recordPrefixBand p hp m s L)

/-- The same lower bound for the concrete record cell `LocOccQ.recCell`. -/
theorem le_measure_recCell (p : ℝ) (hp : 1 / 2 ≤ p) (m : ℕ) (i j : Fin N) (s L : ℕ)
    (hs : 1 ≤ s) :
    (ENNReal.ofReal (1 / 2)) ^ (N * (2 * s + 1) * (s + 1)) ≤
      arrayMeasure N (LocOccQ.recCell p m i j s s L) := by
  refine le_trans (le_measure_recordPrefixBand p hp m s L hs) ?_
  exact measure_mono (recordPrefixBand_subset_recCell p m i j s s L)

end LocOccRecordCarrier
