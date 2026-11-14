/-
# The `Astar` position bound: record geometry, and the windowed movement carrier from measured events

`CarrierWin.moveCarrierWin_of_win` (`Swarm/CarrierWindowRepair.lean`) reduces the
windowed movement carrier to three residuals: the measured ambient event `ambGoodAll`,
`SiteWindow.GoodWWin` at level `Bstar L` on every separated movement window, and the *position*
bound

  `Alo ≤ (X_n^j).toNat` for every walker `j` and every `n` in the movement window,

with `Alo = Astar r T L = r - ((T+2)L + 1)` in the paper.  That position bound is stated nowhere
in the public tree (the published `locCoordGeom` controls only the group infimum, at the weaker
level `r - (T+2)L`).  This file discharges it from the record carrier and re-proves the carrier
with the position residual **removed**.

## 1. Geometry

* `Astar_le_actX_of_carrier` / `Astar_le_X_of_carrier` / `Astar_le_runMax_of_carrier` — on
  `recordCarrier`, every walker is at level `≥ Astar r T L` throughout `[τ_r, τ_r + T·L]`.  Sharp:
  the defect bound `d_r ≤ L` plus the unit-step loss `s - τ_r` leaves exactly `(T+2)L + 1`.
* `leftEdge_le_actX_of_carrier` / `Astar_eq_leftEdge` — slack-parametric form: a `K·L` window
  costs level `r - (K+1)L - 1`; at the `(T+3)L` window of `locMoveFailAtClock` the left edge is
  `r - (T+4)L - 1`, not `Astar`.
* `X_nonneg_of_carrier` / `sepSet_of_glueSep` — `Glue.Sep (PaperBlock.Xa p m U) A Aᶜ n` plus
  geometry gives `SepSet`, so the `(sep)` conjunct of `GoodWWin` is not an extra residual.
* `one_le_Astar`, `Astar_window_low`, `xTop_lt_of_carrier` — `[Astar-1, xTop]` lies inside the
  `(locmax)` window `Ico (r-((T+2)L+2)) (r+(T*L+2))` of `LocGroupSimul.LocMaxBad`.

## 2. The carrier from measured events

* `goodWWin_of_carrier_locmax`, `moveCarrierWin_of_carrier_locmax`, `goodStep_of_carrier_locmax` —
  `Bstar L = 2·xOf L + 6` is `SiteWindow.goodWWin_of_locmax_event`'s threshold at `H = xOf L`, so
  on `recordCarrier \ LocMaxBad` the windowed good event holds with the paper's constants.
* `goodWWin_of_carrier_hybrid`, `moveCarrierWin_of_carrier_hybrid`,
  `exists_moveCarrierWin_of_carrier_hybrid`, `Kc`, `exists_Kc` — the same without the artefactual
  hypothesis `hbdd` (`BddAbove` of the *infinite* family of truncated potentials): `(locmax)` gives
  the `hfix` half and the *finite* run event `RunsOK (siteMarks p m U i) (n+3) K` gives `Gtail`,
  with the floor choice `Kc p L = ⌊xOf L · (1 - (1-p)/p)⌋₊`.
* `arrayMeasure_runWindow_compl_le` — the run-window complement measured, given a clock cutoff.
* `not_mem_LocMaxBad_of_not_mem_univBad`, `carrierMoveWin_of_univBad` — the same at
  `M4D.CarrierMove`'s quantifier shape, i.e. a windowed replacement for the refuted
  `PaperBlock.MoveCarrier` conclusion.

## 3. Residuals (inputs only, never proved here)

`recordCarrier`; `ambGoodAll`; `LocMaxBadᶜ` (equivalently `univBadᶜ`); the finite run event on the
record window.  Not used: `MoveCarrier`, `UniformHalfClause`, `KnotCoalesceAll`,
`FluidHalfDataAll`, any below-window envelope, any stationarity, any `GoodW` prefix supremum.
No `sorry`, no new axiom; closures are `{propext, Classical.choice, Quot.sound}` or smaller.
-/
import Swarm.CarrierWindowRepair
import Swarm.LocCoordGeomCarrier
import Swarm.CarrierModel
import Swarm.PaperBlock
import Swarm.UniversalFamily

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology
open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open LocGroupQ LocMoveLocal LocMoveMart SwarmJointDrift MoveStep RecordoSupply
open SwarmRecordMeas SwarmRecordMeas.Actual SwarmMarks SwarmLogRatio SwarmSiteDiff Finset

namespace AstarPos

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. The level of every walker inside the record window -/

/-- **Core geometric bound.**  On the record carrier with `r ≥ (T+2)L + 1`, every walker stands
at level at least `Astar r T L` at every time of the record window `[τ_r, τ_r + T·L]`. -/
theorem Astar_le_actX_of_carrier {p : ℝ} {m r T L : ℕ} {U : Swarming.Uniform.Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L) (hr : (T + 2) * L + 1 ≤ r)
    {s : ℕ} (hs1 : recTimeA p m U r ≤ s) (hs2 : s ≤ recTimeA p m U r + T * L) (j : Fin N) :
    ((RecClockLG.Astar r T L : ℕ) : ℤ) ≤ actX p m U j s := by
  have hXτ : (r : ℤ) - (L : ℤ) ≤ actX p m U j (recTimeA p m U r) :=
    LocCoordGeomCarrier.X_ge_of_carrier hcarr j
  have hstep : actX p m U j (recTimeA p m U r) - ((s - recTimeA p m U r : ℕ) : ℤ)
      ≤ actX p m U j s := LocCoordPaper.actX_step_lower p m U j hs1
  have hsτ : s - recTimeA p m U r ≤ T * L := by omega
  have h7 : ((s - recTimeA p m U r : ℕ) : ℤ) ≤ ((T * L : ℕ) : ℤ) := by exact_mod_cast hsτ
  have h8 : (L : ℤ) + ((T * L : ℕ) : ℤ) = (((T + 1) * L : ℕ) : ℤ) := by push_cast; ring
  have h9 : (((T + 1) * L : ℕ) : ℤ) ≤ (((T + 2) * L : ℕ) : ℤ) + 1 := by
    have h2 : (T + 1) * L ≤ (T + 2) * L := Nat.mul_le_mul_right L (by omega)
    have h3 : (((T + 1) * L : ℕ) : ℤ) ≤ (((T + 2) * L : ℕ) : ℤ) := by exact_mod_cast h2
    linarith
  have hAcast : ((RecClockLG.Astar r T L : ℕ) : ℤ)
      = (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) - 1 := by
    rw [RecClockLG.Astar, Nat.cast_sub hr]
    push_cast
    ring
  rw [hAcast]
  linarith

/-- Every walker's position is nonnegative throughout the record window (the `(sep)` side
condition `∀ i, 0 ≤ X_n^i`). -/
theorem X_nonneg_of_carrier {p : ℝ} {m r T L : ℕ} {U : Swarming.Uniform.Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L) (hr : (T + 2) * L + 1 ≤ r)
    {s : ℕ} (hs1 : recTimeA p m U r ≤ s) (hs2 : s ≤ recTimeA p m U r + T * L) (j : Fin N) :
    (0 : ℤ) ≤ X p m U s j := by
  have h := Astar_le_actX_of_carrier hcarr hr hs1 hs2 j
  rw [SepGroup.Model.X_apply, ← LocCoordPaper.actX_eq_pos]
  linarith [Nat.zero_le (RecClockLG.Astar r T L)]

/-- The `Astar` position bound in the `Nat`-valued form used by the carrier: for every walker
`j` and every time of the record window. -/
theorem Astar_le_X_of_carrier {p : ℝ} {m r T L : ℕ} {U : Swarming.Uniform.Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L) (hr : (T + 2) * L + 1 ≤ r)
    {s : ℕ} (hs1 : recTimeA p m U r ≤ s) (hs2 : s ≤ recTimeA p m U r + T * L) (j : Fin N) :
    RecClockLG.Astar r T L ≤ (X p m U s j).toNat := by
  have h := Astar_le_actX_of_carrier hcarr hr hs1 hs2 j
  have hnn : (0 : ℤ) ≤ actX p m U j s :=
    le_trans (by exact_mod_cast Nat.zero_le (RecClockLG.Astar r T L)) h
  rw [SepGroup.Model.X_apply, ← LocCoordPaper.actX_eq_pos, Int.le_toNat hnn]
  exact h

/-- **The running-maximum form.**  `Astar` bounds the `toNat` of every walker's running maximum
throughout the record window; this is the hypothesis `A ≤ (runMax p m U i n).toNat` of
`SwarmCarrier.carrier_goodWWin`. -/
theorem Astar_le_runMax_of_carrier {p : ℝ} {m r T L : ℕ} {U : Swarming.Uniform.Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L) (hr : (T + 2) * L + 1 ≤ r)
    {s : ℕ} (hs1 : recTimeA p m U r ≤ s) (hs2 : s ≤ recTimeA p m U r + T * L) (j : Fin N) :
    RecClockLG.Astar r T L ≤ (runMax p m U j s).toNat := by
  have h := Astar_le_actX_of_carrier hcarr hr hs1 hs2 j
  have hnn : (0 : ℤ) ≤ actX p m U j s :=
    le_trans (by exact_mod_cast Nat.zero_le (RecClockLG.Astar r T L)) h
  have hle : (trajectory p m U s).pos j ≤ runMax p m U j s := le_runMax p m U j s
  have hRnn : (0 : ℤ) ≤ runMax p m U j s := by
    refine le_trans ?_ hle
    rw [← LocCoordPaper.actX_eq_pos]
    exact hnn
  rw [Int.le_toNat hRnn]
  have h2 : ((RecClockLG.Astar r T L : ℕ) : ℤ) ≤ (trajectory p m U s).pos j := by
    rw [← LocCoordPaper.actX_eq_pos]
    exact h
  linarith

/-- The side condition `1 ≤ Alo` at `Alo = Astar r T L`. -/
theorem one_le_Astar {r T L : ℕ} (hr : (T + 2) * L + 2 ≤ r) : 1 ≤ RecClockLG.Astar r T L := by
  rw [RecClockLG.Astar]
  omega

/-! ## 2. `(sep)` from the carrier's own separation hypothesis -/

/-- **`SepSet` from `Glue.Sep` plus geometry.**  The movement-window hypothesis of
`CarrierWin.MoveCarrierWin` is `Glue.Sep (PaperBlock.Xa p m U) A Aᶜ u`, which is the paper's
`(sep)` with the nonnegativity restricted to the group `A`.  On the carrier every walker is
nonnegative (`X_nonneg_of_carrier`), so it upgrades to `SepSet`, the separation conjunct of
`SiteWindow.GoodWWin`. -/
theorem sepSet_of_glueSep {p : ℝ} {m r T L : ℕ} {U : Swarming.Uniform.Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L) (hr : (T + 2) * L + 1 ≤ r)
    {n : ℕ} (hn1 : recTimeA p m U r ≤ n) (hn2 : n ≤ recTimeA p m U r + T * L)
    {A : Finset (Fin N)} (hsep : Glue.Sep (PaperBlock.Xa p m U) A Aᶜ n) :
    SepSet p m n A Aᶜ U := by
  obtain ⟨hnn, -, -, hpair⟩ := hsep
  refine ⟨fun i => X_nonneg_of_carrier hcarr hr hn1 hn2 i, ?_⟩
  intro i hi j hj
  have h := hpair i hi j hj
  rwa [PaperBlock.runMaxI_eq] at h


/-! ## 3. The `(locmax)` window covers the `Astar` level window -/

/-- **The upper end of the level window is inside the `(locmax)` window.**  At a time `n` of the
record window, `xTop` is at most `r + T·L + 1`, while the `(locmax)` window used by
`LocGroupSimul.LocMaxBad` reaches `r + T·L + 2`., -/
theorem xTop_lt_of_carrier {p : ℝ} {m r T L : ℕ} {U : Swarming.Uniform.Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L) (hr : (T + 2) * L + 1 ≤ r)
    {n : ℕ} (hn1 : recTimeA p m U r ≤ n) (hn2 : n ≤ recTimeA p m U r + T * L)
    {A : Finset (Fin N)} (hK : (A ∪ Aᶜ).Nonempty) :
    LocGroupQ.xTop p m n (A ∪ Aᶜ) hK U < r + (T * L + 2) := by
  have hτ := LocCoordGeomCarrier.isRecord_recTimeA_of_carrier (N := N) hcarr
  have hR := LocCoordGeomCarrier.Rmax_le_nat_step (N := N) (r := r) (τ := recTimeA p m U r)
    (B := A ∪ Aᶜ) hK (hτ r).1 (hτ r).2 hn1
  have heq : LocGroupQ.Rmax p m n (A ∪ Aᶜ) hK U
      = (Loccoord.Rmax p m U (A ∪ Aᶜ) hK n).toNat := rfl
  have hxTop : LocGroupQ.xTop p m n (A ∪ Aᶜ) hK U
      ≤ LocGroupQ.Rmax p m n (A ∪ Aᶜ) hK U + 1 := by
    rw [LocGroupQ.xTop]
    exact Nat.min_le_right _ _
  rw [heq] at hxTop
  have hsub : n - recTimeA p m U r ≤ T * L := by omega
  omega

/-- **The lower end of the level window is inside the `(locmax)` window.** -/
theorem Astar_window_low {r T L : ℕ} (hr : (T + 2) * L + 2 ≤ r) {v : ℕ}
    (hv : RecClockLG.Astar r T L ≤ v + 1) :
    r - ((T + 2) * L + 2) ≤ v := by
  rw [RecClockLG.Astar] at hv
  omega

/-! ## 4. `GoodWWin` at `Bstar` from the `(locmax)` event -/

/-- **The windowed good event at the record scale from `(locmax)`.**  `Bstar L` is exactly
`max (2·xOf L + 6) (2·(xOf L + 1))`, the threshold of
`SiteWindow.goodWWin_of_locmax_event` at `H = xOf L`; the carrier's defect bound puts every
walker at level `≥ Astar`, and `xTop` lands inside the `(locmax)` window.  So on
`recordCarrier \ LocMaxBad` the windowed good event holds with the paper's own constants. -/
theorem goodWWin_of_carrier_locmax {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m r T L : ℕ} (hL : 1 ≤ L) (hr : (T + 2) * L + 2 ≤ r) {U : Swarming.Uniform.Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    {A : Finset (Fin N)} (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    {n : ℕ} (hn1 : recTimeA p m U r ≤ n) (hn2 : n ≤ recTimeA p m U r + T * L)
    (hsep : Glue.Sep (PaperBlock.Xa p m U) A Aᶜ n)
    (hnb : U ∉ LocGroupSimul.LocMaxBad (N := N) p m r T L)
    (hbdd : ∀ (j : Fin N) (u : ℕ),
      BddAbove (Set.range fun n' => Gtrunc p (SwarmLogRatio.siteMarks p m U j) n' (u + 1))) :
    SiteWindow.GoodWWin p m n A Aᶜ hA (RecClockLG.Bstar L) (RecClockLG.Astar r T L) U := by
  have hr1 : (T + 2) * L + 1 ≤ r := by omega
  have hK : (A ∪ Aᶜ).Nonempty := ⟨Classical.arbitrary (Fin N), by simp⟩
  -- the `(locmax)` threshold hypothesis
  have hLoc : ∀ j : Fin N,
      ∀ y ∈ Finset.Ico (r - ((T + 2) * L + 2)) (r + (T * L + 2)),
        hof p (SwarmLogRatio.siteMarks p m U j) y ≤ LocSumAct.xOf L ∧
          Gsup p (SwarmLogRatio.siteMarks p m U j) y ≤ LocSumAct.xOf L := by
    intro j y hy
    by_contra hcon
    apply hnb
    refine ⟨j, y, hy, ?_⟩
    rcases not_and_or.mp hcon with h1 | h2
    · exact Or.inl (le_of_lt (not_le.mp h1))
    · exact Or.inr (le_of_lt (not_le.mp h2))
  -- the cover of the level window
  have hcover : ∀ v : ℕ, RecClockLG.Astar r T L ≤ v + 1 →
      v ≤ LocGroupQ.xTop p m n (A ∪ Aᶜ) hK U → v ∈ Finset.Ico (r - ((T + 2) * L + 2)) (r + (T * L + 2)) := by
    intro v hv1 hv2
    refine Finset.mem_Ico.mpr ⟨Astar_window_low hr hv1, ?_⟩
    exact lt_of_le_of_lt hv2 (xTop_lt_of_carrier hcarr hr1 hn1 hn2 hK)
  have hA' : ∀ i ∈ A, RecClockLG.Astar r T L ≤ (runMax p m U i n).toNat :=
    fun i _ => Astar_le_runMax_of_carrier hcarr hr1 hn1 hn2 i
  have hH1 : (1 : ℝ) ≤ LocSumAct.xOf L := LocSumAct.one_le_xOf hL
  have := SiteWindow.goodWWin_of_locmax_event (N := N) hp0 hp1.le A Aᶜ hA hAc
    (disjoint_compl_right) (sepSet_of_glueSep hcarr hr1 hn1 hn2 hsep) hH1 hA' hLoc
    (fun v hv1 hv2 => hcover v hv1 hv2) hbdd
  simpa only [RecClockLG.Bstar] using this

/-! ## 5. The windowed movement carrier from the record carrier -/

/-- **`MoveCarrierWin` on `recordCarrier \ LocMaxBad`.**  The position residual of
`CarrierWin.moveCarrierWin_of_win` is gone: `Astar_le_X_of_carrier` derives it from the defect
bound, `(sep)` is the movement window's own hypothesis upgraded by geometry, and the windowed good
event comes from the measured `(locmax)` failure set.  Residuals: `recordCarrier` (the paper's
`d_r ≤ L`), `ambGoodAll` (the ambient Gamma event), `LocMaxBadᶜ` and the a.e. boundedness of the
truncated forward potentials. -/
theorem moveCarrierWin_of_carrier_locmax {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m r T L : ℕ} (hL : 1 ≤ L) (hr : (T + 2) * L + 2 ≤ r) {U : Swarming.Uniform.Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (hamb : U ∈ Swarming.Enl.ambGoodAll (N := N) p m (r : ℤ) T L)
    (hnb : U ∉ LocGroupSimul.LocMaxBad (N := N) p m r T L)
    (hbdd : ∀ (j : Fin N) (u : ℕ),
      BddAbove (Set.range fun n' => Gtrunc p (SwarmLogRatio.siteMarks p m U j) n' (u + 1))) :
    CarrierWin.MoveCarrierWin (N := N) p m r T L (RecClockLG.Astar r T L) U := by
  refine CarrierWin.moveCarrierWin_of_win (N := N) hp0 hp1 (one_le_Astar hr) hamb ?_ ?_
  · intro A hA hne s t hs hst ht hsepwin n hn
    have hAc : Aᶜ.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hnil
      exact hne ((Finset.compl_eq_empty_iff A).mp hnil)
    have hs1 : s ≤ n := (Finset.mem_Ico.mp hn).1
    have hs2 : n < t := (Finset.mem_Ico.mp hn).2
    have hn1 : recTimeA p m U r ≤ n := le_trans hs hs1
    have hn2 : n ≤ recTimeA p m U r + T * L := le_trans (le_of_lt hs2) ht
    exact goodWWin_of_carrier_locmax (n := n) hp0 hp1 hL hr hcarr hA hAc hn1 hn2
      (hsepwin n hs1 hs2) hnb hbdd
  · intro n hn1 hn2 j
    exact Astar_le_X_of_carrier hcarr (by omega) hn1 hn2 j

/-- **The `GoodStep` shape on `recordCarrier \ LocMaxBad`.**  The two frozen-potential step bounds
of the complementary group, i.e. exactly the third conjunct that `PaperBlock.MoveCarrier` supplies,
without any below-window envelope and with `Alo = Astar r T L`. -/
theorem goodStep_of_carrier_locmax {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m r T L : ℕ} (hL : 1 ≤ L) (hr : (T + 2) * L + 2 ≤ r) {U : Swarming.Uniform.Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (hamb : U ∈ Swarming.Enl.ambGoodAll (N := N) p m (r : ℤ) T L)
    (hnb : U ∉ LocGroupSimul.LocMaxBad (N := N) p m r T L)
    (hbdd : ∀ (j : Fin N) (u : ℕ),
      BddAbove (Set.range fun n' => Gtrunc p (siteMarks p m U j) n' (u + 1)))
    {A : Finset (Fin N)} (hA : A.Nonempty) (hne : A ≠ Finset.univ) {s t : ℕ}
    (hs : recTimeA p m U r ≤ s) (hst : s ≤ t) (ht : t ≤ recTimeA p m U r + T * L)
    (hsep : ∀ u : ℕ, s ≤ u → u < t → Glue.Sep (PaperBlock.Xa p m U) A Aᶜ u) :
    ∀ n ∈ Finset.Ico s t, GoodStep p m n Aᶜ (RecClockLG.Bstar L) U := by
  have hr1 : (T + 2) * L + 1 ≤ r := by omega
  refine CarrierWin.moveCarrierWin_step (N := N) hp0.le hp1.le (one_le_Astar hr)
    (moveCarrierWin_of_carrier_locmax hp0 hp1 hL hr hcarr hamb hnb hbdd) hA hne hs hst ht hsep ?_
  intro n hn j _
  exact Astar_le_X_of_carrier hcarr hr1 (le_trans hs (Finset.mem_Ico.mp hn).1)
    (le_trans (le_of_lt (Finset.mem_Ico.mp hn).2) ht) j

/-! ## 5b. A second route: `(locmax)` for `hfix`, the finite run event for `Gtail`

The hypothesis `hbdd` above (boundedness of the *infinite* family of truncated forward potentials)
is an artefact of reading `Gtail` through `Gsup`.  Reading the `hfix` half through `(locmax)` and
the `Gtail` half through the *finite* run event removes it, at the price of a floor choice
`K ≈ xOf L · (1 - (1-p)/p)`. -/

/-- `Bstar` in additive form, for `L ≥ 1`. -/
theorem Bstar_eq_add {L : ℕ} (hL : 1 ≤ L) :
    RecClockLG.Bstar L = 2 * LocSumAct.xOf L + 6 := by
  rw [RecClockLG.Bstar, max_eq_left]
  have h := LocSumAct.one_le_xOf hL
  linarith

/-- `LocMaxBadᶜ` gives the `hfix` half of `(locmax)`. -/
theorem hof_le_of_not_mem_locmax {p : ℝ} {m r T L : ℕ} {U : Swarming.Uniform.Array N}
    (hnb : U ∉ LocGroupSimul.LocMaxBad (N := N) p m r T L) {j : Fin N} {y : ℕ}
    (hy : y ∈ Finset.Ico (r - ((T + 2) * L + 2)) (r + (T * L + 2))) :
    hof p (siteMarks p m U j) y ≤ LocSumAct.xOf L := by
  by_contra hcon
  exact hnb ⟨j, y, hy, Or.inl (le_of_lt (not_le.mp hcon))⟩

/-- `LocMaxBadᶜ` gives the `G` half of `(locmax)`. -/
theorem Gsup_le_of_not_mem_locmax {p : ℝ} {m r T L : ℕ} {U : Swarming.Uniform.Array N}
    (hnb : U ∉ LocGroupSimul.LocMaxBad (N := N) p m r T L) {j : Fin N} {y : ℕ}
    (hy : y ∈ Finset.Ico (r - ((T + 2) * L + 2)) (r + (T * L + 2))) :
    Gsup p (siteMarks p m U j) y ≤ LocSumAct.xOf L := by
  by_contra hcon
  exact hnb ⟨j, y, hy, Or.inr (le_of_lt (not_le.mp hcon))⟩

/-- **The level window lies inside the `(locmax)` window.** -/
theorem mem_locmax_window_of_carrier {p : ℝ} {m r T L : ℕ} {U : Swarming.Uniform.Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L) (hr : (T + 2) * L + 2 ≤ r)
    {n : ℕ} (hn1 : recTimeA p m U r ≤ n) (hn2 : n ≤ recTimeA p m U r + T * L)
    {A : Finset (Fin N)} (hK : (A ∪ Aᶜ).Nonempty) {v : ℕ}
    (hv1 : RecClockLG.Astar r T L ≤ v + 1)
    (hv2 : v ≤ LocGroupQ.xTop p m n (A ∪ Aᶜ) hK U) :
    v ∈ Finset.Ico (r - ((T + 2) * L + 2)) (r + (T * L + 2)) := by
  have hr1 : (T + 2) * L + 1 ≤ r := by omega
  refine Finset.mem_Ico.mpr ⟨Astar_window_low hr hv1, ?_⟩
  exact lt_of_le_of_lt hv2 (xTop_lt_of_carrier hcarr hr1 hn1 hn2 hK)

/-- **`GoodWWin` at `Bstar` without any boundedness hypothesis**: `(locmax)` supplies the `hfix`
half and the finite run event supplies `Gtail`. -/
theorem goodWWin_of_carrier_hybrid {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m r T L : ℕ} (hL : 1 ≤ L) (hr : (T + 2) * L + 2 ≤ r) {U : Swarming.Uniform.Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    {A : Finset (Fin N)} (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    {n : ℕ} (hn1 : recTimeA p m U r ≤ n) (hn2 : n ≤ recTimeA p m U r + T * L)
    (hsep : Glue.Sep (PaperBlock.Xa p m U) A Aᶜ n)
    (hnb : U ∉ LocGroupSimul.LocMaxBad (N := N) p m r T L)
    {K : ℕ} (hK1 : 1 ≤ K) (hGnum : (K : ℝ) ≤ LocSumAct.xOf L * (1 - (1 - p) / p))
    (hrun : ∀ i ∈ A, SwarmRun.RunsOK (siteMarks p m U i) (n + 3) K) :
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
  have hxTop : ∀ v : ℕ, v ≤ LocGroupQ.xTop p m n (A ∪ Aᶜ) hK U → v ≤ n + 2 := by
    intro v hv
    refine le_trans hv ?_
    rw [LocGroupQ.xTop]
    exact Nat.min_le_left _ _
  have hA' : ∀ i ∈ A, RecClockLG.Astar r T L ≤ (runMax p m U i n).toNat :=
    fun i _ => Astar_le_runMax_of_carrier hcarr hr1 hn1 hn2 i
  have hH : ∀ i ∈ A, ∀ v : ℕ, RecClockLG.Astar r T L ≤ v + 1 →
      v ≤ LocGroupQ.xTop p m n (A ∪ Aᶜ) hK U → hfix (omegaN p m U i) v ≤ LocSumAct.xOf L := by
    intro i _ v hv1 hv2
    rw [Loccoord.hfix_omegaN_eq_hof (p := p) hpne (m := m) (U := U) i v]
    exact hof_le_of_not_mem_locmax hnb (mem_locmax_window_of_carrier hcarr hr hn1 hn2 hK hv1 hv2)
  have hG : ∀ i ∈ A, ∀ u : ℕ, RecClockLG.Astar r T L ≤ u →
      u ≤ LocGroupQ.xTop p m n (A ∪ Aᶜ) hK U →
      Gtail p m U i u (n + 2) ≤ 2 + (K : ℝ) / (1 - (1 - p) / p) := by
    intro i hi u _ hu2
    exact SwarmCarrier.Gtail_le_of_runs (N := N) hp0 hp1 U i hK1 (hrun i hi) (hxTop u hu2)
  have hGnn : (0 : ℝ) ≤ 2 + (K : ℝ) / (1 - (1 - p) / p) := by
    have h1 : (0 : ℝ) ≤ (K : ℝ) / (1 - (1 - p) / p) := div_nonneg hKnn hρ.le
    linarith
  have hgood := SiteWindow.goodWWin_of_locmax (N := N) hp0 hp1.le A Aᶜ hA hAc
    disjoint_compl_right (sepSet_of_glueSep hcarr hr1 hn1 hn2 hsep) hx1 hGnn hA' hH hG
  refine CarrierWin.goodWWin_mono (N := N) hA ?_ hgood
  rw [Bstar_eq_add hL]
  refine max_le le_rfl ?_
  linarith

/-- **`MoveCarrierWin` with no boundedness hypothesis.**  Same as
`moveCarrierWin_of_carrier_locmax`, with the finitely-checked run event replacing `hbdd`.
Residuals: `recordCarrier`, `ambGoodAll`, `LocMaxBadᶜ`, the run event on the record window, and the
explicit floor condition `(K : ℝ) ≤ xOf L * (1 - (1-p)/p)`. -/
theorem moveCarrierWin_of_carrier_hybrid {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m r T L : ℕ} (hL : 1 ≤ L) (hr : (T + 2) * L + 2 ≤ r) {U : Swarming.Uniform.Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (hamb : U ∈ Swarming.Enl.ambGoodAll (N := N) p m (r : ℤ) T L)
    (hnb : U ∉ LocGroupSimul.LocMaxBad (N := N) p m r T L)
    {K : ℕ} (hK1 : 1 ≤ K) (hGnum : (K : ℝ) ≤ LocSumAct.xOf L * (1 - (1 - p) / p))
    (hrun : ∀ n ∈ Finset.Ico (recTimeA p m U r) (recTimeA p m U r + T * L),
      ∀ i : Fin N, SwarmRun.RunsOK (siteMarks p m U i) (n + 3) K) :
    CarrierWin.MoveCarrierWin (N := N) p m r T L (RecClockLG.Astar r T L) U := by
  refine CarrierWin.moveCarrierWin_of_win (N := N) hp0 hp1 (one_le_Astar hr) hamb ?_ ?_
  · intro A hA hne s t hs hst ht hsepwin n hn
    have hAc : Aᶜ.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hnil
      exact hne ((Finset.compl_eq_empty_iff A).mp hnil)
    have hs1 : s ≤ n := (Finset.mem_Ico.mp hn).1
    have hs2 : n < t := (Finset.mem_Ico.mp hn).2
    have hn1 : recTimeA p m U r ≤ n := le_trans hs hs1
    have hn2 : n ≤ recTimeA p m U r + T * L := le_trans (le_of_lt hs2) ht
    exact goodWWin_of_carrier_hybrid (n := n) hp0 hp1 hL hr hcarr hA hAc hn1 hn2
      (hsepwin n hs1 hs2) hnb hK1 hGnum (fun i _ => hrun n (Finset.mem_Ico.mpr ⟨hn1, by omega⟩) i)
  · intro n hn1 hn2 j
    exact Astar_le_X_of_carrier hcarr (by omega) hn1 hn2 j

/-- The run-event length of the hybrid route: `K ≈ xOf L · (1 - (1-p)/p)`. -/
noncomputable def Kc (p : ℝ) (L : ℕ) : ℕ := ⌊LocSumAct.xOf L * (1 - (1 - p) / p)⌋₊

/-- **The floor choice is admissible from some scale on** (depending on `p`, not on `N`): the run
length is at least one and its real value stays below `xOf L · (1 - (1-p)/p)`, which is what
`goodWWin_of_carrier_hybrid` needs. -/
theorem exists_Kc {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      1 ≤ Kc p L ∧ (Kc p L : ℝ) ≤ LocSumAct.xOf L * (1 - (1 - p) / p) := by
  have hρ : (0 : ℝ) < 1 - (1 - p) / p := by
    rw [sub_pos, div_lt_one (by linarith)]
    linarith
  obtain ⟨L₀, hL₀⟩ :=
    Filter.eventually_atTop.mp
      (LocSumAct.xOf_tendsto.eventually (eventually_ge_atTop (1 / (1 - (1 - p) / p))))
  refine ⟨L₀, fun L hL => ?_⟩
  have hx : 1 / (1 - (1 - p) / p) ≤ LocSumAct.xOf L := hL₀ L hL
  have hge : (1 : ℝ) ≤ LocSumAct.xOf L * (1 - (1 - p) / p) := by
    rw [div_le_iff₀ hρ] at hx
    linarith
  have hxnn : (0 : ℝ) ≤ LocSumAct.xOf L * (1 - (1 - p) / p) := by linarith
  refine ⟨?_, ?_⟩
  · rw [Kc]
    exact Nat.le_floor (by exact_mod_cast hge : ((1 : ℕ) : ℝ) ≤ _)
  · rw [Kc]
    exact Nat.floor_le hxnn

/-- **The movement carrier at the record scale, with every residual named and explicit.**
For `1/2 < p < 1` and every `m` there is a scale `L₀` — depending on `p` only — such that for every
`L ≥ L₀`, every `T`, every record level `r ≥ (T+2)L + 2` and every trajectory in

* the record carrier `{d_r ≤ L}` (`RecClockLG.recordCarrier`),
* the ambient Gamma good event (`Swarming.Enl.ambGoodAll`),
* the `(locmax)` good event (`LocGroupSimul.LocMaxBadᶜ`),
* the finite run event on the record window at length `Kc p L`,

the windowed movement carrier `CarrierWin.MoveCarrierWin p m r T L (Astar r T L)` holds.  No
position residual, no `(sep)` residual, no below-window envelope, no boundedness hypothesis. -/
theorem exists_moveCarrierWin_of_carrier_hybrid {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∀ (T r : ℕ), (T + 2) * L + 2 ≤ r →
      ∀ {U : Swarming.Uniform.Array N},
        U ∈ RecClockLG.recordCarrier (N := N) p m r L →
        U ∈ Swarming.Enl.ambGoodAll (N := N) p m (r : ℤ) T L →
        U ∉ LocGroupSimul.LocMaxBad (N := N) p m r T L →
        (∀ n ∈ Finset.Ico (recTimeA p m U r) (recTimeA p m U r + T * L),
          ∀ i : Fin N, SwarmRun.RunsOK (siteMarks p m U i) (n + 3) (Kc p L)) →
        CarrierWin.MoveCarrierWin (N := N) p m r T L (RecClockLG.Astar r T L) U := by
  obtain ⟨L₀, hL₀⟩ := exists_Kc hp0 hp1
  refine ⟨max L₀ 1, fun L hL T r hr U hcarr hamb hnb hrun => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  have hL0 : L₀ ≤ L := le_trans (le_max_left _ _) hL
  exact moveCarrierWin_of_carrier_hybrid hp0 hp1 hL1 hr hcarr hamb hnb (hL₀ L hL0).1
    (hL₀ L hL0).2 hrun

/-- **Off the paper's universal bad event, `(locmax)` is good.**  `univBad` is
`commonBad ∪ (locmove) ∪ (locgroup)`, and `commonBad` contains `LocMaxBad`; this is the membership
step that lets the windowed carrier be stated at `M4D.CarrierMove`'s own quantifier shape. -/
theorem not_mem_LocMaxBad_of_not_mem_univBad {p : ℝ} {m : ℕ} {Cerr : ℝ} {r T L : ℕ}
    {U : Swarming.Uniform.Array N}
    (h : U ∉ UniversalFamily.univBad (N := N) p m Cerr r T L) :
    U ∉ LocGroupSimul.LocMaxBad (N := N) p m r T L := by
  intro hmem
  exact h (by
    simp only [UniversalFamily.univBad, LocalGoodFamily.famBad, LocalGoodFamily.commonBad,
      Set.mem_union]
    tauto)

/-- **The windowed `M4D.CarrierMove`, at its own quantifier shape.**  For every `N ≥ 2` there is a
scale `L₀` (independent of `N`) such that on `recordCarrier \ univBad`, with the ambient Gamma event
and the finite run event of the record window, `CarrierWin.MoveCarrierWin` holds at
`Alo = Astar r T L` for every block scale `T`, every error coefficient `Cerr` and every record
level `r ≥ (T+3)L`.

This is the statement that replaces the refuted `PaperBlock.MoveCarrier` conclusion: the two
remaining inputs `ambGoodAll` and the run event are both measured at `arrayMeasure N` with explicit
exponential complements. -/
theorem carrierMoveWin_of_univBad {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) :
    ∀ (N : ℕ) [Nonempty (Fin N)], 2 ≤ N → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      ∀ (T : ℕ) (Cerr : ℝ) (r : ℕ), (T + 3) * L ≤ r → ∀ U : Swarming.Uniform.Array N,
        U ∈ RecClockLG.recordCarrier (N := N) p m r L →
        U ∉ UniversalFamily.univBad (N := N) p m Cerr r T L →
        U ∈ Swarming.Enl.ambGoodAll (N := N) p m (r : ℤ) T L →
        (∀ n ∈ Finset.Ico (recTimeA p m U r) (recTimeA p m U r + T * L),
          ∀ i : Fin N, SwarmRun.RunsOK (siteMarks p m U i) (n + 3) (Kc p L)) →
        CarrierWin.MoveCarrierWin (N := N) p m r T L (RecClockLG.Astar r T L) U := by
  intro N _ hN
  obtain ⟨L₀, hL₀⟩ := exists_moveCarrierWin_of_carrier_hybrid (N := N) hp0 hp1 (m := m)
  refine ⟨max L₀ 2, fun L hL T Cerr r hr U hcarr huniv hamb hrun => ?_⟩
  have hL0 : L₀ ≤ L := le_trans (le_max_left _ _) hL
  have hL2 : 2 ≤ L := le_trans (le_max_right _ _) hL
  have hmul : (T + 2) * L + 2 ≤ (T + 3) * L := by
    have hEq : (T + 3) * L = (T + 2) * L + L := by ring
    omega
  exact hL₀ L hL0 T r (by omega)
    hcarr hamb (not_mem_LocMaxBad_of_not_mem_univBad huniv) hrun

/-- **Slack-parametric position bound.**  On the carrier, for *any* window multiple `K ≥ 1`, every
walker is at level at least `r - (K+1)L - 1` throughout `[τ_r, τ_r + K·L]`.

`K = T + 1` is the paper's movement window and gives `Astar r T L` (`Astar_eq_leftEdge`);
`K = T + 3` is the window of `ClockLocMove.locMoveFailAtClock`, where the correct left edge is
`r - (T+4)L - 1`, **not** `Astar` (the defect bound loses the elapsed time, so each extra `L` of
window costs one `L` of level). -/
theorem leftEdge_le_actX_of_carrier {p : ℝ} {m r T L K : ℕ} {U : Swarming.Uniform.Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L) (hr : (K + 1) * L + 1 ≤ r)
    {s : ℕ} (hs1 : recTimeA p m U r ≤ s) (hs2 : s ≤ recTimeA p m U r + K * L) (j : Fin N) :
    ((r - ((K + 1) * L + 1) : ℕ) : ℤ) ≤ actX p m U j s := by
  have hXτ : (r : ℤ) - (L : ℤ) ≤ actX p m U j (recTimeA p m U r) :=
    LocCoordGeomCarrier.X_ge_of_carrier hcarr j
  have hstep : actX p m U j (recTimeA p m U r) - ((s - recTimeA p m U r : ℕ) : ℤ)
      ≤ actX p m U j s := LocCoordPaper.actX_step_lower p m U j hs1
  have hsτ : s - recTimeA p m U r ≤ K * L := by omega
  have h7 : ((s - recTimeA p m U r : ℕ) : ℤ) ≤ ((K * L : ℕ) : ℤ) := by exact_mod_cast hsτ
  have h8 : (L : ℤ) + ((K * L : ℕ) : ℤ) = (((K + 1) * L : ℕ) : ℤ) := by push_cast; ring
  have hcast : ((r - ((K + 1) * L + 1) : ℕ) : ℤ) = (r : ℤ) - (((K + 1) * L : ℕ) : ℤ) - 1 := by
    rw [Nat.cast_sub hr]
    push_cast
    ring
  rw [hcast]
  linarith

/-- `Astar` is the left edge of the slack-parametric bound at `K = T + 1`. -/
theorem Astar_eq_leftEdge {r T L : ℕ} : RecClockLG.Astar r T L = r - ((T + 1 + 1) * L + 1) := rfl

/-- **The run-window event has an explicit `arrayMeasure` bound, given a clock cutoff.**

The window event `∀ n ∈ [τ_r, τ_r+TL], RunsOK ω (n+3) K` is a *level*-bounded event at level
`τ_r + T·L + 3`.  If the clock is known to satisfy `τ_r ≤ B`, failure on the window forces failure
at the single level `B + T·L + 3`, whose complement is the combinatorial carrier of
`SwarmCarrier.arrayMeasure_carrier_compl_le`.  No union over clock values is taken here; the clock
cutoff is the explicit hypothesis `hB`. -/
theorem arrayMeasure_runWindow_compl_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) {r T L K B : ℕ} (hK : 1 ≤ K)
    (hB : ∀ U : Swarming.Uniform.Array N,
      U ∈ RecClockLG.recordCarrier (N := N) p m r L → recTimeA p m U r ≤ B) :
    (Swarming.Uniform.arrayMeasure N)
        {U : Swarming.Uniform.Array N | U ∈ RecClockLG.recordCarrier (N := N) p m r L ∧
          ¬ (∀ n ∈ Finset.Ico (recTimeA p m U r) (recTimeA p m U r + T * L),
              ∀ i : Fin N, SwarmRun.RunsOK (siteMarks p m U i) (n + 3) K)}
      ≤ ENNReal.ofReal ((N : ℝ) *
          (((B + T * L + 3 : ℕ) : ℝ) * (1 - (1 - p) ^ (m - 1)) ^ K)) := by
  refine le_trans (measure_mono (μ := Swarming.Uniform.arrayMeasure N) ?_)
    (SwarmCarrier.arrayMeasure_carrier_compl_le (N := N) hp0 hp1 hm
      (B + T * L + 3) K hK)
  intro U hU
  obtain ⟨hcarr, hbad⟩ := hU
  simp only [not_forall] at hbad
  obtain ⟨n, hn, i, hi⟩ := hbad
  have hnB : n + 3 ≤ B + T * L + 3 := by
    have h1 : n ≤ recTimeA p m U r + T * L := le_of_lt (Finset.mem_Ico.mp hn).2
    have h2 : recTimeA p m U r ≤ B := hB U hcarr
    omega
  exact ⟨i, fun hrun => hi (fun y hy => hrun y (le_trans hy hnB))⟩

/-! ## 6. Axiom audit (source order) -/


end AstarPos
