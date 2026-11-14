/-
# The deterministic geometry behind `ClockLocMove.locCoordGeom`

`ClockLocMove.locCoordGeom p m A hA r T L s t` is the `(loccoord)` *carrier*: the set of
trajectories on which the spatial window used by `Loccoord.loccoord_full_window` holds at
`(s,t)`, namely

  `0 ≤ min_{A} X_s`,  `r - (T+2)L ≤ (min_A X_s).toNat`,  `(max_A M_t).toNat ≤ r + (T+2)L`.

It is exported as an explicit premise of `LocalGoodFamily.familyGood_locmove` and of every
`(locmove)` statement built on `ClockLocMove`, i.e. it is *assumed*, not derived.  This file
derives it from the record carrier.

The two existing public facts that do the work are `LocCoordPaper.Rmax_le_nat` (the upper end
of the record window, from the record structure and unit steps) and `LocCoordPaper.Xmin_ge_int`
(the lower end, from the defect bound `d_r ≤ L`).  Both are stated for the window
`[τ_r, τ_r + TL]`.  Direction D asks whether the carrier really implies the window; it does,
and this file proves it, in two forms:

* `mem_locCoordGeom_of_carrier` — on `recordCarrier` and `r ≥ (T+3)L`, `locCoordGeom` holds for
  **every** window `τ_r ≤ s ≤ t ≤ τ_r + TL`, with no extra hypothesis.  This is the paper's own
  window, so on the paper's display the `(loccoord)` carrier contributes no event content: the
  premise `U ∈ locCoordGeom …` of the `(locmove)` statements is redundant there.
* `mem_locCoordGeom_of_carrier_wide` — the sharpened range that the two halves actually support:
  the minimum side reaches `s ≤ τ_r + (T+1)L`, the maximum side `t ≤ τ_r + (T+2)L`.  So the
  geometry is *one* `L` short of the `(T+3)L` window that `ClockLocMove.locMoveFailAtClock`
  quantifies over; see `RANGE_FRONTIER.md` for that exact statement.

Also proved: the level pin `runMaxA … (τ_r) = r`, which is the last conjunct of
`LocMoveCompose.locmoveGood`, is likewise automatic on the carrier (`locmoveGood_pin`).

Nothing here is probabilistic, no event is assumed nonempty, and nothing is weakened: the
conclusions are the literal conjuncts of `locCoordGeom` with the honest `ℤ`/`ℕ` casts
(`Int.toNat` handled by `Nat.cast_sub` + `omega`, never by definitional abuse).
-/
import Swarm.ClockLocMove
import Swarm.LocCoordPaper

noncomputable section

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open Swarming Swarming.Uniform Swarming.Model SepGroup.Model
open RecordDefect RecordoSupply SwarmRecordMeas SwarmRecordMeas.Actual
open ActualRecordFiltration LocGroupSimul LocMoveCompose Loccoord Swarming.Enl

namespace LocCoordGeomCarrier

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. The record structure and the defect, read off the carrier -/

/-- On the defect carrier the canonical clock is a genuine record-time sequence. -/
theorem isRecord_recTimeA_of_carrier {p : ℝ} {m r L : ℕ} {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L) :
    IsRecord (actX p m U) (recTimeA p m U) :=
  isRecord_recTimeA p m U (fun r' => hcarr.1 r')

/-- The paper's defect bound `d_r ≤ L` as an integer inequality, from the `toNat` form stored in
`recordCarrier`.  The `toNat` is harmless here because `d_r ≥ 0` at a record time
(`runMin ≤ runMax = r`). -/
theorem defect_le_of_carrier {p : ℝ} {m r L : ℕ} {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L) :
    (r : ℤ) - runMin (actX p m U) (recTimeA p m U r) ≤ (L : ℤ) := by
  have hτ := isRecord_recTimeA_of_carrier (N := N) hcarr
  have hspec : runMax (actX p m U) (recTimeA p m U r) = (r : ℤ) := (hτ r).2
  have hnonneg : (0 : ℤ) ≤ (r : ℤ) - runMin (actX p m U) (recTimeA p m U r) := by
    rw [← hspec]
    linarith [runMin_le_runMax (X := actX p m U) (recTimeA p m U r)]
  have hcast : (((r : ℤ) - runMin (actX p m U) (recTimeA p m U r)).toNat : ℤ)
      = (r : ℤ) - runMin (actX p m U) (recTimeA p m U r) := Int.toNat_of_nonneg hnonneg
  have h1 : (((r : ℤ) - runMin (actX p m U) (recTimeA p m U r)).toNat : ℤ) ≤ (L : ℤ) := by
    exact_mod_cast hcarr.2
  rw [hcast] at h1
  exact h1

/-- The defect bound at the record time also says every walker stands at or above `r - L`
there. -/
theorem X_ge_of_carrier {p : ℝ} {m r L : ℕ} {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L) (i : Fin N) :
    (r : ℤ) - (L : ℤ) ≤ actX p m U i (recTimeA p m U r) := by
  have hdef := defect_le_of_carrier (N := N) hcarr
  have h1 : runMin (actX p m U) (recTimeA p m U r)
      ≤ actX p m U i (recTimeA p m U r) := runMin_le _ i
  linarith

/-! ## 2. The two range lemmas at an arbitrary multiple `K·L` of the record window

`LocCoordPaper.Rmax_le_nat` and `LocCoordPaper.Xmin_ge_int` are the `K = T+2` resp. `K = T`
instances.  The proofs below are the same argument with the window length kept symbolic, which
is what makes the exact frontier visible. -/

/-- **Lower end of a `K·L` record window.**  If the defect at the record time is at most `L`,
then at every time `s ∈ [τ, τ+K·L]` every walker of the group stands at or above
`r - L - K·L`. -/
theorem Xmin_ge_int_window {p : ℝ} {m r L : ℕ} {U : Array N} {s τ K : ℕ}
    {B : Finset (Fin N)} (hB : B.Nonempty)
    (hdef : (r : ℤ) - runMin (actX p m U) τ ≤ (L : ℤ))
    (hτs : τ ≤ s) (hsK : s ≤ τ + K * L) :
    (r : ℤ) - (((L + K * L : ℕ)) : ℤ) ≤ Loccoord.Xmin p m U B hB s := by
  have hmin : (r : ℤ) - (L : ℤ) ≤ runMin (actX p m U) τ := by linarith
  refine Finset.le_inf' hB (fun k => SepGroup.Model.X p m U s k) (fun k _ => ?_)
  have h1 : (r : ℤ) - (L : ℤ) ≤ actX p m U k τ :=
    le_trans hmin (runMin_le τ k)
  have h2 : actX p m U k τ - ((s - τ : ℕ) : ℤ) ≤ actX p m U k s :=
    LocCoordPaper.actX_step_lower p m U k hτs
  have hsub : ((s - τ : ℕ) : ℤ) ≤ ((K * L : ℕ) : ℤ) := by
    have h : s - τ ≤ K * L := by omega
    exact_mod_cast h
  have hcast : (r : ℤ) - (((L + K * L : ℕ)) : ℤ)
      ≤ (r : ℤ) - (L : ℤ) - ((K * L : ℕ) : ℤ) := by
    have : (((L + K * L : ℕ)) : ℤ) = (L : ℤ) + ((K * L : ℕ) : ℤ) := by push_cast; ring
    linarith
  have hX : SepGroup.Model.X p m U s k = actX p m U k s := rfl
  rw [hX]
  linarith

/-- **Upper end of a `K·L` record window.**  On a record window with record level `r` at `τ`,
no walker's running maximum at time `t ≤ τ + K·L` exceeds `r + K·L`. -/
theorem Rmax_le_nat_window {p : ℝ} {m r L : ℕ} {U : Array N} {t τ K : ℕ}
    {B : Finset (Fin N)} (hB : B.Nonempty)
    (hlow : ∀ n < τ, runMax (actX p m U) n < (r : ℤ))
    (hτmax : runMax (actX p m U) τ = (r : ℤ))
    (hτt : τ ≤ t) (htK : t ≤ τ + K * L) :
    (Loccoord.Rmax p m U B hB t).toNat ≤ r + K * L := by
  have hkey : ∀ k ∈ B,
      Swarming.Trajectory.runMax p m U k t ≤ (((r + K * L : ℕ)) : ℤ) := by
    intro k _
    refine LocCoordPaper.runMax_le_of_pointwise (fun u hu => ?_)
    have hle : actX p m U k u ≤ (r : ℤ) + ((u - τ : ℕ) : ℤ) := by
      by_cases huτ : u ≤ τ
      · have h1 : actX p m U k u ≤ runMax (actX p m U) u := le_runMax u k
        have hcast : ((u - τ : ℕ) : ℤ) = 0 := by
          have : u - τ = 0 := by omega
          rw [this]; norm_num
        rw [hcast, add_zero]
        rcases lt_or_eq_of_le huτ with hlt | heq
        · have h2 := hlow u hlt
          linarith
        · subst heq
          rw [hτmax] at h1
          exact h1
      · push Not at huτ
        have hstep := LocCoordPaper.actX_step_upper p m U k (le_of_lt huτ)
        have h2 : actX p m U k τ ≤ (r : ℤ) := by
          have := le_runMax (X := actX p m U) τ k
          rw [hτmax] at this
          exact this
        linarith
    have hsub : ((u - τ : ℕ) : ℤ) ≤ ((K * L : ℕ) : ℤ) := by
      have h1 : u - τ ≤ K * L := by omega
      exact_mod_cast h1
    have hnat : (r : ℤ) + ((K * L : ℕ) : ℤ) ≤ (((r + K * L : ℕ)) : ℤ) := by
      push_cast; linarith
    linarith
  have hsup : Loccoord.Rmax p m U B hB t ≤ (((r + K * L : ℕ)) : ℤ) :=
    Finset.sup'_le hB (fun k => Swarming.Trajectory.runMax p m U k t) hkey
  have h := Int.toNat_le_toNat hsup
  rwa [Int.toNat_natCast] at h

/-! ## 2b. The same two range bounds with the *exact* elapsed time as the window

These are the sharp forms: the minimum side loses exactly the elapsed time `s - τ` from the defect
bound, and the maximum side gains exactly the elapsed time `t - τ`.  The `K·L` versions above are
the specialisations used by the paper; the sharp forms make the exact frontier of the geometric
carrier visible (`RANGE_FRONTIER.md`). -/

/-- **Sharp lower end.**  On the defect carrier, at *any* time `s ≥ τ`,
`min_A X_s ≥ r - L - (s - τ)`. -/
theorem Xmin_ge_int_step {p : ℝ} {m r L : ℕ} {U : Array N} {s τ : ℕ}
    {B : Finset (Fin N)} (hB : B.Nonempty)
    (hdef : (r : ℤ) - runMin (actX p m U) τ ≤ (L : ℤ))
    (hτs : τ ≤ s) :
    (r : ℤ) - (((L + (s - τ) : ℕ)) : ℤ) ≤ Loccoord.Xmin p m U B hB s := by
  have hmin : (r : ℤ) - (L : ℤ) ≤ runMin (actX p m U) τ := by linarith
  refine Finset.le_inf' hB (fun k => SepGroup.Model.X p m U s k) (fun k _ => ?_)
  have h1 : (r : ℤ) - (L : ℤ) ≤ actX p m U k τ :=
    le_trans hmin (runMin_le τ k)
  have h2 : actX p m U k τ - ((s - τ : ℕ) : ℤ) ≤ actX p m U k s :=
    LocCoordPaper.actX_step_lower p m U k hτs
  have hcast : (((L + (s - τ) : ℕ)) : ℤ) = (L : ℤ) + ((s - τ : ℕ) : ℤ) := by
    push_cast; ring
  have hX : SepGroup.Model.X p m U s k = actX p m U k s := rfl
  rw [hX, hcast]
  linarith

/-- **Sharp upper end.**  On a record window, at *any* time `t ≥ τ`,
`max_A M_t ≤ r + (t - τ)`. -/
theorem Rmax_le_nat_step {p : ℝ} {m r : ℕ} {U : Array N} {t τ : ℕ}
    {B : Finset (Fin N)} (hB : B.Nonempty)
    (hlow : ∀ n < τ, runMax (actX p m U) n < (r : ℤ))
    (hτmax : runMax (actX p m U) τ = (r : ℤ))
    (hτt : τ ≤ t) :
    (Loccoord.Rmax p m U B hB t).toNat ≤ r + (t - τ) := by
  have hkey : ∀ k ∈ B,
      Swarming.Trajectory.runMax p m U k t ≤ (((r + (t - τ) : ℕ)) : ℤ) := by
    intro k _
    refine LocCoordPaper.runMax_le_of_pointwise (fun u hu => ?_)
    have hle : actX p m U k u ≤ (r : ℤ) + ((u - τ : ℕ) : ℤ) := by
      by_cases huτ : u ≤ τ
      · have h1 : actX p m U k u ≤ runMax (actX p m U) u := le_runMax u k
        have hcast : ((u - τ : ℕ) : ℤ) = 0 := by
          have : u - τ = 0 := by omega
          rw [this]; norm_num
        rw [hcast, add_zero]
        rcases lt_or_eq_of_le huτ with hlt | heq
        · have h2 := hlow u hlt
          linarith
        · subst heq
          rw [hτmax] at h1
          exact h1
      · push Not at huτ
        have hstep := LocCoordPaper.actX_step_upper p m U k (le_of_lt huτ)
        have h2 : actX p m U k τ ≤ (r : ℤ) := by
          have := le_runMax (X := actX p m U) τ k
          rw [hτmax] at this
          exact this
        linarith
    have hsub : ((u - τ : ℕ) : ℤ) ≤ ((t - τ : ℕ) : ℤ) := by
      have h1 : u - τ ≤ t - τ := by omega
      exact_mod_cast h1
    have hnat : (r : ℤ) + ((t - τ : ℕ) : ℤ) ≤ (((r + (t - τ) : ℕ)) : ℤ) := by
      push_cast; linarith
    linarith
  have hsup : Loccoord.Rmax p m U B hB t ≤ (((r + (t - τ) : ℕ)) : ℤ) :=
    Finset.sup'_le hB (fun k => Swarming.Trajectory.runMax p m U k t) hkey
  have h := Int.toNat_le_toNat hsup
  rwa [Int.toNat_natCast] at h

/-! ## 3. The three conjuncts of `locCoordGeom`, from the carrier -/

/-- `min_A X_s ≥ 0`: the lower range exceeds `0` once `r ≥ (T+2)L`. -/
theorem Xmin_nonneg_of_carrier {p : ℝ} {m r T L : ℕ} {U : Array N} {s : ℕ}
    {A : Finset (Fin N)} (hA : A.Nonempty)
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (hr : (T + 2) * L ≤ r)
    (hτs : recTimeA p m U r ≤ s) (hsT : s ≤ recTimeA p m U r + T * L) :
    (0 : ℤ) ≤ Loccoord.Xmin p m U A hA s := by
  have hdef := defect_le_of_carrier (N := N) hcarr
  have h := Xmin_ge_int_window (N := N) (r := r) (L := L) (τ := recTimeA p m U r)
    (K := T + 1) hA hdef hτs (by
      have := Nat.mul_le_mul_right L (show T ≤ T + 1 by omega)
      omega)
  have heq : L + (T + 1) * L = (T + 2) * L := by ring
  rw [heq] at h
  have hcast : (((T + 2) * L : ℕ) : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
  linarith

/-- `r - (T+2)L ≤ (min_A X_s).toNat`, the second conjunct in the honest `ℤ → ℕ` direction. -/
theorem Xmin_toNat_ge_of_carrier {p : ℝ} {m r T L : ℕ} {U : Array N} {s : ℕ}
    {A : Finset (Fin N)} (hA : A.Nonempty)
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (hr : (T + 2) * L ≤ r)
    (hτs : recTimeA p m U r ≤ s) (hsT : s ≤ recTimeA p m U r + T * L) :
    r - (T + 2) * L ≤ (Loccoord.Xmin p m U A hA s).toNat := by
  have hdef := defect_le_of_carrier (N := N) hcarr
  have hint := Xmin_ge_int_window (N := N) (r := r) (L := L) (τ := recTimeA p m U r)
    (K := T + 1) hA hdef hτs (by
      have := Nat.mul_le_mul_right L (show T ≤ T + 1 by omega)
      omega)
  have heq : L + (T + 1) * L = (T + 2) * L := by ring
  rw [heq] at hint
  have hnonneg : (0 : ℤ) ≤ Loccoord.Xmin p m U A hA s :=
    Xmin_nonneg_of_carrier (N := N) hA hcarr hr hτs hsT
  have hcast : ((r - (T + 2) * L : ℕ) : ℤ) = (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) :=
    Nat.cast_sub hr
  have hge : ((r - (T + 2) * L : ℕ) : ℤ) ≤ Loccoord.Xmin p m U A hA s := by
    rw [hcast]; exact hint
  have hz : ((Loccoord.Xmin p m U A hA s).toNat : ℤ) = Loccoord.Xmin p m U A hA s :=
    Int.toNat_of_nonneg hnonneg
  have hcast2 : ((r - (T + 2) * L : ℕ) : ℤ)
      ≤ ((Loccoord.Xmin p m U A hA s).toNat : ℤ) := by
    rw [hz]; exact hge
  exact_mod_cast hcast2

/-- `(max_A M_t).toNat ≤ r + (T+2)L`, the third conjunct. -/
theorem Rmax_toNat_le_of_carrier {p : ℝ} {m r T L : ℕ} {U : Array N} {t : ℕ}
    {A : Finset (Fin N)} (hA : A.Nonempty)
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (hτt : recTimeA p m U r ≤ t) (htT : t ≤ recTimeA p m U r + T * L) :
    (runMaxA p m U hA t).toNat ≤ r + (T + 2) * L := by
  have hτ := isRecord_recTimeA_of_carrier (N := N) hcarr
  have h := Rmax_le_nat_window (N := N) (r := r) (L := L) (τ := recTimeA p m U r)
    (K := T + 2) hA (hτ r).1 (hτ r).2 hτt (by
      have : T * L ≤ (T + 2) * L := Nat.mul_le_mul_right L (by omega)
      omega)
  exact h

/-! ## 4. The carrier implies the `(loccoord)` geometric window

Both statements are membership in the *public* `ClockLocMove.locCoordGeom`, so they discharge the
premise `U ∈ locCoordGeom …` of `LocalGoodFamily.familyGood_locmove`, `ClockLocMove.locmoveGood`
consumers and the `hcc` premise of `ClockLocMove.measureReal_locMoveFailAtClock_le` on the
paper's window. -/

/-- **The paper's window: `locCoordGeom` is automatic on the record carrier.**

For `U ∈ recordCarrier`, `r ≥ (T+3)L` and *every* window `τ_r ≤ s ≤ t ≤ τ_r + TL`,
`U ∈ locCoordGeom p m A hA r T L s t`.  No hypothesis other than the carrier and the record
threshold: the `(loccoord)` carrier carries no probabilistic content on the paper's window. -/
theorem mem_locCoordGeom_of_carrier {p : ℝ} {m r T L : ℕ} {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L) (hr : (T + 3) * L ≤ r)
    (A : Finset (Fin N)) (hA : A.Nonempty) :
    ∀ s t : ℕ, recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
      U ∈ ClockLocMove.locCoordGeom p m A hA r T L s t := by
  intro s t hτs hst htT
  have hT2 : (T + 2) * L ≤ r :=
    le_trans (Nat.mul_le_mul_right L (by omega)) hr
  have hsT : s ≤ recTimeA p m U r + T * L := le_trans hst htT
  exact ⟨Xmin_nonneg_of_carrier (N := N) hA hcarr hT2 hτs hsT,
    Xmin_toNat_ge_of_carrier (N := N) hA hcarr hT2 hτs hsT,
    Rmax_toNat_le_of_carrier (N := N) hA hcarr (le_trans hτs hst) htT⟩

/-- **The sharpened range the two halves really support.**  The minimum side is valid up to
`τ_r + (T+1)L` and the maximum side up to `τ_r + (T+2)L`, so `locCoordGeom` holds on the whole
rectangle `[τ_r, τ_r+(T+1)L] × [τ_r, τ_r+(T+2)L]`.  The paper's window `[τ_r, τ_r+TL]` is well
inside it; `ClockLocMove.locMoveFailAtClock`'s window `[τ_r, τ_r+(T+3)L]` reaches one `L` past the
maximum side and two `L` past the minimum side, which is why that statement cannot get
`locCoordGeom` for free. -/
theorem mem_locCoordGeom_of_carrier_wide {p : ℝ} {m r T L : ℕ} {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L) (hr : (T + 3) * L ≤ r)
    (A : Finset (Fin N)) (hA : A.Nonempty) :
    ∀ s t : ℕ, recTimeA p m U r ≤ s → s ≤ t →
      s ≤ recTimeA p m U r + (T + 1) * L → t ≤ recTimeA p m U r + (T + 2) * L →
      U ∈ ClockLocMove.locCoordGeom p m A hA r T L s t := by
  intro s t hτs hst hsW htW
  have hT2 : (T + 2) * L ≤ r :=
    le_trans (Nat.mul_le_mul_right L (by omega)) hr
  have hdef := defect_le_of_carrier (N := N) hcarr
  have hmin := Xmin_ge_int_window (N := N) (r := r) (L := L) (τ := recTimeA p m U r)
    (K := T + 1) hA hdef hτs hsW
  have heq : L + (T + 1) * L = (T + 2) * L := by ring
  rw [heq] at hmin
  have hcast : (((T + 2) * L : ℕ) : ℤ) ≤ (r : ℤ) := by exact_mod_cast hT2
  have hnonneg : (0 : ℤ) ≤ Loccoord.Xmin p m U A hA s := by linarith
  have htoNat : r - (T + 2) * L ≤ (Loccoord.Xmin p m U A hA s).toNat := by
    have hsub : ((r - (T + 2) * L : ℕ) : ℤ) = (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) :=
      Nat.cast_sub hT2
    have hge : ((r - (T + 2) * L : ℕ) : ℤ) ≤ Loccoord.Xmin p m U A hA s := by
      rw [hsub]; exact hmin
    have hz : ((Loccoord.Xmin p m U A hA s).toNat : ℤ) = Loccoord.Xmin p m U A hA s :=
      Int.toNat_of_nonneg hnonneg
    have hcast2 : ((r - (T + 2) * L : ℕ) : ℤ)
        ≤ ((Loccoord.Xmin p m U A hA s).toNat : ℤ) := by
      rw [hz]; exact hge
    exact_mod_cast hcast2
  have hτ := isRecord_recTimeA_of_carrier (N := N) hcarr
  have hmax := Rmax_le_nat_window (N := N) (r := r) (L := L) (τ := recTimeA p m U r)
    (K := T + 2) hA (hτ r).1 (hτ r).2 (le_trans hτs hst) htW
  exact ⟨hnonneg, htoNat, hmax⟩

/-! ## 4b. The same carrier at an arbitrary spatial slack `c·L`

`ClockLocMove.locCoordGeom` uses the fixed slack `(T+2)·L`, which is the slack of the `(locsum)`
window `Lw T L = (2T+2)L+1` it is paired with.  The geometry itself is slack-parametric, and that
matters for `ClockLocMove.locMoveFailAtClock`'s window: that window reaches `τ_r + (T+3)L`, which
the `(T+2)L` slack cannot cover (see `RANGE_FRONTIER.md`).  With slack `(T+4)L` — i.e. the
`(loccoord)`/`(locsum)` chain rescaled to window `(2T+8)L+1` — the *whole* `(T+3)L` record window
is geometrically free, by `mem_locCoordGeomSlack_clockWindow` below. -/

/-- The `(loccoord)` geometric window with spatial slack `c·L`.  `c = T+2` is exactly the
published `ClockLocMove.locCoordGeom` (`locCoordGeomSlack_eq_locCoordGeom`). -/
def locCoordGeomSlack (c : ℕ) (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (r L : ℕ) : ℕ → ℕ → Set (Array N) :=
  fun s t => {U : Array N |
    0 ≤ Xmin p m U A hA s ∧ r - c * L ≤ (Xmin p m U A hA s).toNat ∧
      (runMaxA p m U hA t).toNat ≤ r + c * L}

/-- At slack `c = T+2` the slack-parametric carrier *is* the published `locCoordGeom`. -/
theorem locCoordGeomSlack_eq_locCoordGeom (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (r T L : ℕ) :
    locCoordGeomSlack (N := N) (T + 2) p m A hA r L
      = ClockLocMove.locCoordGeom p m A hA r T L := rfl

/-- **The slack-parametric geometric window is automatic on the record carrier.**  With slack
`c·L` (`1 ≤ c`, `c·L ≤ r`) it holds for every window with `s - τ_r ≤ (c-1)·L` and
`t - τ_r ≤ c·L`.  The `c = T+2` instance is `mem_locCoordGeom_of_carrier_wide`.  (No hypothesis on
`T` is needed at this level: the slack `c` is the only parameter of the geometry.) -/
theorem mem_locCoordGeomSlack_of_carrier {p : ℝ} {m r L : ℕ} {U : Array N} {c : ℕ}
    (hc1 : 1 ≤ c) (hrc : c * L ≤ r)
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (A : Finset (Fin N)) (hAn : A.Nonempty) :
    ∀ s t : ℕ, recTimeA p m U r ≤ s → s ≤ t →
      s ≤ recTimeA p m U r + (c - 1) * L → t ≤ recTimeA p m U r + c * L →
      U ∈ locCoordGeomSlack (N := N) c p m A hAn r L s t := by
  intro s t hτs hst hsW htW
  have hdef := defect_le_of_carrier (N := N) hcarr
  have hmin := Xmin_ge_int_step (N := N) (r := r) (L := L) (τ := recTimeA p m U r)
    hAn hdef hτs
  -- `L + (s - τ) ≤ c * L` from `s - τ ≤ (c-1) * L`
  have hsτ : s - recTimeA p m U r ≤ (c - 1) * L := by
    rw [Nat.sub_le_iff_le_add]
    calc s ≤ recTimeA p m U r + (c - 1) * L := hsW
      _ = (c - 1) * L + recTimeA p m U r := Nat.add_comm _ _
  have hLsum : L + (s - recTimeA p m U r) ≤ c * L := by
    have h1 : L + (s - recTimeA p m U r) ≤ L + (c - 1) * L := Nat.add_le_add_left hsτ L
    have h2 : L + (c - 1) * L = c * L := by
      rw [Nat.add_comm L ((c - 1) * L)]
      calc (c - 1) * L + L = (c - 1) * L + 1 * L := by rw [one_mul]
        _ = ((c - 1) + 1) * L := (Nat.add_mul _ _ _).symm
        _ = c * L := by rw [Nat.sub_add_cancel hc1]
    linarith
  have hminc : (r : ℤ) - (((c * L : ℕ)) : ℤ) ≤ Loccoord.Xmin p m U A hAn s := by
    have h1 : (((L + (s - recTimeA p m U r) : ℕ)) : ℤ) ≤ (((c * L : ℕ)) : ℤ) := by
      exact_mod_cast hLsum
    linarith
  have hrcast : (((c * L : ℕ)) : ℤ) ≤ (r : ℤ) := by exact_mod_cast hrc
  have hnonneg : (0 : ℤ) ≤ Loccoord.Xmin p m U A hAn s := by linarith
  have htoNat : r - c * L ≤ (Loccoord.Xmin p m U A hAn s).toNat := by
    have hsub : ((r - c * L : ℕ) : ℤ) = (r : ℤ) - (((c * L : ℕ)) : ℤ) := Nat.cast_sub hrc
    have hge : ((r - c * L : ℕ) : ℤ) ≤ Loccoord.Xmin p m U A hAn s := by
      rw [hsub]; exact hminc
    have hz : ((Loccoord.Xmin p m U A hAn s).toNat : ℤ) = Loccoord.Xmin p m U A hAn s :=
      Int.toNat_of_nonneg hnonneg
    have hcast2 : ((r - c * L : ℕ) : ℤ)
        ≤ ((Loccoord.Xmin p m U A hAn s).toNat : ℤ) := by
      rw [hz]; exact hge
    exact_mod_cast hcast2
  have hτ := isRecord_recTimeA_of_carrier (N := N) hcarr
  have hmax := Rmax_le_nat_step (N := N) (r := r) (τ := recTimeA p m U r) hAn
    (hτ r).1 (hτ r).2 (le_trans hτs hst)
  have hmax' : (runMaxA p m U hAn t).toNat ≤ r + c * L := by
    have htτ : t - recTimeA p m U r ≤ c * L := by omega
    have hle : r + (t - recTimeA p m U r) ≤ r + c * L := by omega
    exact le_trans hmax hle
  exact ⟨hnonneg, htoNat, hmax'⟩

/-- **The whole `(T+3)L` record window is geometrically free at slack `(T+4)L`.**  This is the
slack at which `ClockLocMove.locMoveFailAtClock`'s window can have `locCoordGeom` discharged rather
than assumed; the price is a `(loccoord)`/`(locsum)` chain rescaled to slack `(T+4)L`
(window `(2T+8)L+1`), not a change in the geometric content. -/
theorem mem_locCoordGeomSlack_clockWindow {p : ℝ} {m r T L : ℕ} {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L) (hr : (T + 4) * L ≤ r)
    (A : Finset (Fin N)) (hAn : A.Nonempty) :
    ∀ s t : ℕ, recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + (T + 3) * L →
      U ∈ locCoordGeomSlack (N := N) (T + 4) p m A hAn r L s t := by
  intro s t hτs hst htW
  have hsub : (T + 4) - 1 = T + 3 := by omega
  have hc3 : 1 ≤ T + 4 := by omega
  refine mem_locCoordGeomSlack_of_carrier (N := N) (c := T + 4) hc3 hr
    hcarr A hAn s t hτs hst ?_ ?_
  · calc s ≤ t := hst
      _ ≤ recTimeA p m U r + (T + 3) * L := htW
      _ = recTimeA p m U r + ((T + 4) - 1) * L := by rw [hsub]
  · have hmul : (T + 3) * L ≤ (T + 4) * L := Nat.mul_le_mul_right L (by omega)
    omega

/-! ## 5. The level pin of `locmoveGood` is automatic on the carrier -/

/-- On the record carrier the `A`-group running record at the record time is at most `r`: every
per-walker running maximum up to `τ_r` is at most the spatial maximum `r`. -/
theorem runMaxA_recTimeA_le_of_carrier {p : ℝ} {m r L : ℕ} {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    {A : Finset (Fin N)} (hAn : A.Nonempty) :
    runMaxA p m U hAn (recTimeA p m U r) ≤ (r : ℤ) := by
  have hτ := isRecord_recTimeA_of_carrier (N := N) hcarr
  have hmax : runMax (actX p m U) (recTimeA p m U r) = (r : ℤ) := (hτ r).2
  have hlow : ∀ n < recTimeA p m U r, runMax (actX p m U) n < (r : ℤ) := (hτ r).1
  refine Finset.sup'_le hAn (fun k => Swarming.Trajectory.runMax p m U k (recTimeA p m U r))
    (fun k _ => ?_)
  refine LocCoordPaper.runMax_le_of_pointwise (t := recTimeA p m U r) (a := (r : ℤ)) ?_
  intro u hu
  rcases lt_or_eq_of_le hu with hlt | heq
  · have h1 : actX p m U k u ≤ runMax (actX p m U) u := le_runMax u k
    have h2 := hlow u hlt
    linarith
  · subst heq
    have h1 : actX p m U k (recTimeA p m U r) ≤ runMax (actX p m U) (recTimeA p m U r) :=
      le_runMax _ k
    rw [hmax] at h1
    exact h1

/-- On the record carrier the `A`-group running record at the record time is at least `r - L`:
the defect bound puts *every* walker, in particular every walker of the nonempty group `A`, at or
above `r - L` at `τ_r`.  This is the half of the `(locmove)` pin that uses `d_r ≤ L`; the other
half is `runMaxA_recTimeA_le_of_carrier`.  (Equality is *false* in general: the walker attaining
the spatial record `r` need not lie in `A`.) -/
theorem runMaxA_recTimeA_ge_sub_of_carrier {p : ℝ} {m r L : ℕ} {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    {A : Finset (Fin N)} (hAn : A.Nonempty) :
    (r : ℤ) - (L : ℤ) ≤ runMaxA p m U hAn (recTimeA p m U r) := by
  have hex : ∃ k : Fin N, k ∈ A := hAn
  set k : Fin N := Classical.choose hex with hkdef
  have hkA : k ∈ A := Classical.choose_spec hex
  have h0 : (r : ℤ) - (L : ℤ) ≤ actX p m U k (recTimeA p m U r) :=
    X_ge_of_carrier (N := N) hcarr k
  have h1 : actX p m U k (recTimeA p m U r)
      ≤ Swarming.Trajectory.runMax p m U k (recTimeA p m U r) := by
    rw [LocCoordPaper.runMax_eq_sup]
    exact Finset.le_sup' (fun u => actX p m U k u) (Finset.mem_range.mpr (Nat.lt_succ_self _))
  have h2 : Swarming.Trajectory.runMax p m U k (recTimeA p m U r)
      ≤ runMaxA p m U hAn (recTimeA p m U r) :=
    Finset.le_sup' (fun j => Swarming.Trajectory.runMax p m U j (recTimeA p m U r)) hkA
  linarith

/-- The `(locmove)` pin of `LocMoveCompose.locmoveGood` at the actual record clock with `Lh = L` is
automatic on the carrier.  This is the exact conjunct
`r - (Lh:ℤ) ≤ runMaxA … n₀ ∧ runMaxA … n₀ ≤ r` of `locmoveGood`, with `n₀ = τ_r`. -/
theorem locmoveGood_pin {p : ℝ} {m r L : ℕ} {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    {A : Finset (Fin N)} (hAn : A.Nonempty) :
    (r : ℤ) - (L : ℤ) ≤ runMaxA p m U hAn (recTimeA p m U r) ∧
      runMaxA p m U hAn (recTimeA p m U r) ≤ (r : ℤ) :=
  ⟨runMaxA_recTimeA_ge_sub_of_carrier (N := N) hcarr hAn,
    runMaxA_recTimeA_le_of_carrier (N := N) hcarr hAn⟩

end LocCoordGeomCarrier

/-! ## Axiom audit (source order, including the definition) -/


