/-
# `(locmove)` at the literal actual record clock at the paper's `(T+3)L` record threshold

## What is new here (relative to the public tree)

`ClockLocMove.exists_measureReal_locMoveFailAtClock_le` proves the paper's `(locmove)` display at
the literal actual record clock `tau_r = recTimeA p m U r`, but only under the *stronger* record
threshold `(3T+6)L <= r`, inherited from `Loccoord.loccoord_full_window`, and it carries the whole
`(loccoord)` content as two free premises (`bad`, `eb` and the pointwise window inequality `hcc`).
`ClockLocMoveExp.exists_measureReal_locMoveFailAtClock_paper` gives the single-exponential profile
of that statement, again only at `(3T+6)L <= r`.

`LocalGoodCore.loccoord_CU_explicit` proves `(loccoord)` at the *paper's* threshold `(T+3)L <= r`
and at the single explicitly named `(locsum)` constant `CU p m A`, with the explicit remainder
`CTof (CU p m A) T`.  This file feeds exactly that into the actual-clock `(locmove)` estimate, so:

* `loccoordGeom_CU` — the `hcc`/`bad`/`eb` triple of `ClockLocMove` discharged at the paper's
  `(T+3)L <= r`, `bad = LsBad N p m (CU p m A) ((2T+4)L) (r-(T+2)L)`, `C = (2 CU + 1)/2`,
  `β = betaCU ((2CU+1)/2) (CTof (CU p m A) T) L`, so that the `(locmove)` remainder is literally
  the `(loccoord)` remainder `CTof (...) T * L^{3/4}`.
* `measureReal_locMoveFailAtClock_T3_CU` — the measured `(locmove)` clause at `recTimeA` at the
  paper's record threshold `(T+3)L <= r`, at the explicit constant `CU`, with **no** rate premise
  (`1 <= gammaRate * C` is discharged by `LocalGood.gammaRate_mul_CU`) and **no** free `(loccoord)`
  premise.
* `exists_measureReal_locMoveFailAtClock_T3_paper` — the same in the paper's single-exponential
  profile `CT * exp (-(lam * xOf L))`, `lam > 0` independent of `T` and `L`.

## What is deliberately NOT claimed

No `(lococc)`, no merged single event `LocalBad`, no `(locgroup)` (that is
`RecClockLG.exists_recordClock_locgroup`), no `(locmart)` (that is `RecordClock.exists_locMartBad_le`),
no `GoodW`/`GoodStep` probability, no halving, tightness, invariant law, regeneration, common
speed or `MainClaim`.  The carriers `(sep)` on `[s,t)` (`locmoveGood`), the pinned record window
and the two step truncations stay *hypotheses* of the display, as in the paper.
-/
import Swarm.ClockLocMoveExp
import Swarm.LocalGoodCore

noncomputable section

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance LocGroupQ LocGroupWindow
open SwarmMarks SwarmLogRatio LocSumAct LocSumR1
open RecordDefect RecordoSupply SwarmRecordMeas SwarmRecordMeas.Actual
open ActualRecordFiltration LocGroupSimul LocMoveCompose LocMoveLocal LocMoveMart
open Loccoord Swarming.Enl

namespace ClockLocMove

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 10. The `(loccoord)` carrier at the paper's `(T+3)L`, at the constant `CU` -/

/-- **The three `(loccoord)` inputs of the actual-clock `(locmove)` estimate, discharged at the
paper's record threshold.**

For `1/2 < p < 1`, `2 ≤ m`, nonempty `A` and every `T` there are `c > 0` and `L₀` such that for
`L ≥ L₀` and `r ≥ (T+3)L`, at the paper's `(locsum)` bad set
`bad = LsBad N p m (CU p m A) ((2T+4)L) (r-(T+2)L)`:

* `(arrayMeasure N).real bad ≤ CTof (CU p m A) T * exp (-c * xOf L)`;
* off `bad`, on the `(loccoord)` geometric window `locCoordGeom`, the `(loccoord)` display holds
  with coefficient `(2 CU + 1)/2` and error `3 * ((2CU+1)/2) * betaCU ((2CU+1)/2) (CTof (CU p m A) T) L`,
  which is *equal* to the explicit `(loccoord)` remainder `CTof (CU p m A) T * L^{3/4}`.

This is exactly the `(bad, eb, geom, hcc)` package demanded by
`measureReal_locMoveFailAtClock_le`, but with the paper's threshold `(T+3)L ≤ r` rather than the
`(3T+6)L ≤ r` of `Loccoord.loccoord_full_window`. -/
theorem loccoordGeom_CU {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (A : Finset (Fin N)) (hA : A.Nonempty) (T : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
      (arrayMeasure N).real
          (LocSumR1.LsBad N p m (LocalGood.CU p m A) ((2 * T + 4) * L) (r - (T + 2) * L))
        ≤ LocCoordPaper.CTof (LocalGood.CU p m A) T * Real.exp (-c * LocSumAct.xOf L) ∧
      (∀ s t : ℕ, s ≤ t → ∀ U : Array N,
        U ∉ LocSumR1.LsBad N p m (LocalGood.CU p m A) ((2 * T + 4) * L) (r - (T + 2) * L) →
        U ∈ locCoordGeom p m A hA r T L s t →
        Swarming.Group.average A
          (fun k => HA p m U t A (X p m U t k) - HA p m U s A (X p m U s k))
          ≤ ((2 * LocalGood.CU p m A + 1) / 2)
              * (((runMaxA p m U hA t : ℤ) : ℝ) - ((Xmin p m U A hA s : ℤ) : ℝ))
            + 3 * ((2 * LocalGood.CU p m A + 1) / 2)
              * LocalGood.betaCU ((2 * LocalGood.CU p m A + 1) / 2)
                  (LocCoordPaper.CTof (LocalGood.CU p m A) T) L) := by
  obtain ⟨c, hc, L₀, hL⟩ := LocalGood.loccoord_CU_explicit (N := N) hp0 hp1 hm A hA T
  refine ⟨c, hc, L₀, ?_⟩
  intro L hL0 r hr
  have hCT0 : (0 : ℝ) ≤ LocCoordPaper.CTof (LocalGood.CU p m A) T :=
    le_trans zero_le_one
      (LocCoordPaper.one_le_CTof
        (le_trans zero_le_one (LocalGood.one_le_CU p m A)) T)
  constructor
  · have h1 := (hL L hL0 r hr).1
    rw [measureReal_def]
    refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top h1) ?_
    rw [ENNReal.toReal_ofReal (by positivity)]
    exact le_of_eq (by rw [LocSumAct.xOf])
  · intro s t hst U hUb hUg
    obtain ⟨hX0, hAle, hLb⟩ := hUg
    have hres := (hL L hL0 r hr).2 U hUb A hA s t hst hX0 hAle hLb
    have hRmax : ((Loccoord.Rmax p m U A hA t : ℤ) : ℝ) = ((runMaxA p m U hA t : ℤ) : ℝ) := rfl
    rw [hRmax] at hres
    have hCne : ((2 * LocalGood.CU p m A + 1) / 2) ≠ 0 := by
      have := LocalGood.one_le_CU p m A
      positivity
    rw [LocalGood.three_mul_betaCU hCne L]
    exact hres

/-! ## 11. The measured `(locmove)` clause at `tau_r` and at `(T+3)L ≤ r` -/

/-- **The measured `(locmove)` clause at the literal actual record clock, at the paper's record
threshold and at the explicit constant `CU`.**

For `1/2 < p < 1`, `2 ≤ m` and nonempty proper `A ⊂ Fin N`, there are `c > 0` and `L₀` such that
for every `L ≥ L₀`, every `T`, every `r ≥ (T+3)L`, the set of trajectories on which

* the paper's carrier `{d_r ≤ L}` holds (`RecClockLG.recordCarrier`),
* and there is a window `τ_r ≤ s ≤ t ≤ τ_r + (T+3)L` on which the paper's `(locmove)` window
  hypotheses hold *at the record clock* (`locmoveGood`, which contains `(sep)` on `[s,t)`,
  `GoodW`, `GoodStep` and the pinned record window), on which the `(loccoord)` geometric window
  holds, and yet the display
  `W_t - W_s ≤ locmoveRHS (C = (2CU+1)/2) (β = betaCU ...) (ε₁ = ε₂ = L^{3/4})` fails,

has `arrayMeasure`-measure at most the two clock-anchored two-endpoint deviation bounds plus
`CTof (CU p m A) T * exp (-c * xOf L)` — the `(loccoord)` remainder.  There is no union over
clock values, no rate premise and no free `(loccoord)` premise. -/
theorem measureReal_locMoveFailAtClock_T3_CU {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) :
    ∀ T : ℕ, ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ max L₀ 2, ∀ r : ℕ, (T + 3) * L ≤ r →
      (arrayMeasure N).real
          {U : Array N |
            locMoveFailAtClock p m A hA hAc r T L (RecClockLG.Bstar L)
              ((2 * LocalGood.CU p m A + 1) / 2)
              (LocalGood.betaCU ((2 * LocalGood.CU p m A + 1) / 2)
                (LocCoordPaper.CTof (LocalGood.CU p m A) T) L)
              ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4))
              (locCoordGeom p m A hA r T L) U}
        ≤ 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
            Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
              (4 * (((T + 3) * L : ℕ) : ℝ)
                * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2))
          + 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
            Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
              (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * RecClockLG.Bstar L) ^ 2))
          + LocCoordPaper.CTof (LocalGood.CU p m A) T * Real.exp (-c * LocSumAct.xOf L) := by
  intro T
  obtain ⟨c, hc, L₀, hL⟩ := loccoordGeom_CU (N := N) hp0 hp1 hm A hA T
  refine ⟨c, hc, L₀, ?_⟩
  intro L hLbig r hr
  have hL0 : L₀ ≤ L := le_trans (le_max_left _ _) hLbig
  have hL2 : 2 ≤ L := le_trans (le_max_right _ _) hLbig
  have hL1 : 1 ≤ L := by omega
  obtain ⟨hbad, hcc⟩ := hL L hL0 r hr
  have hC1 : (1 : ℝ) ≤ (2 * LocalGood.CU p m A + 1) / 2 := by
    have := LocalGood.one_le_CU p m A
    linarith
  have hγC : 1 ≤ gammaRate p m A * ((2 * LocalGood.CU p m A + 1) / 2) := by
    refine le_trans (LocalGood.gammaRate_mul_CU (N := N) (m := m) hp0 hp1 hA) ?_
    have hγ : (0 : ℝ) ≤ gammaRate p m A := (LocalGood.gammaRate_pos (N := N) hp0 hp1 hA).le
    have hle : LocalGood.CU p m A ≤ (2 * LocalGood.CU p m A + 1) / 2 := by linarith
    exact mul_le_mul_of_nonneg_left hle hγ
  have hε : (0 : ℝ) < (L : ℝ) ^ ((3 : ℝ) / 4) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < L)) _
  have hBpos : 0 < RecClockLG.Bstar L := RecClockLG.Bstar_pos hL1
  exact measureReal_locMoveFailAtClock_le (N := N) hp0 hp1 (by omega : 1 ≤ m) A hA hAc hL2 hr
    (B := RecClockLG.Bstar L) (ε₁ := (L : ℝ) ^ ((3 : ℝ) / 4))
    (ε₂ := (L : ℝ) ^ ((3 : ℝ) / 4))
    (C := (2 * LocalGood.CU p m A + 1) / 2)
    (β := LocalGood.betaCU ((2 * LocalGood.CU p m A + 1) / 2)
      (LocCoordPaper.CTof (LocalGood.CU p m A) T) L)
    hBpos hC1 hγC hε hε
    (bad := LocSumR1.LsBad N p m (LocalGood.CU p m A) ((2 * T + 4) * L) (r - (T + 2) * L))
    (eb := LocCoordPaper.CTof (LocalGood.CU p m A) T * Real.exp (-c * LocSumAct.xOf L))
    (geom := locCoordGeom p m A hA r T L) hcc hbad

/-! ## 12. The paper's single-exponential profile -/

/-- **The `(locmove)` actual-clock failure clause in the paper's own profile, at the paper's
record threshold `(T+3)L ≤ r`.**

For each fixed `T` there are a rate `lam > 0`, a coefficient `CT > 0` and a threshold `L₀`
with: for every `L ≥ L₀`, every `r ≥ (T+3)L`, `B = Bstar L`, `C = (2 CU + 1)/2`,
`β = betaCU C (CTof (CU p m A) T) L` and `ε₁ = ε₂ = L^{3/4}`, the actual-clock `(locmove)`
failure event has `arrayMeasure`-measure at most `CT * exp (-(lam * xOf L))`.

The probabilistic content is entirely in `ClockLocMove.measureReal_locMoveFailAtClock_le`; the
absorption is `LocalGood.absorb_rpow`; the passage from `(3T+6)L` to `(T+3)L` is
`measureReal_locMoveFailAtClock_T3_CU`. -/
theorem exists_measureReal_locMoveFailAtClock_T3_paper {p : ℝ} (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) (A : Finset (Fin N)) (hA : A.Nonempty)
    (hAc : Aᶜ.Nonempty) (hN : 1 ≤ N) :
    ∀ T : ℕ, ∃ lam CT : ℝ, 0 < lam ∧ 0 < CT ∧ ∃ L₀ : ℕ,
      ∀ L ≥ max L₀ 2, ∀ r : ℕ, (T + 3) * L ≤ r →
      (arrayMeasure N).real
          {U : Array N |
            locMoveFailAtClock p m A hA hAc r T L (RecClockLG.Bstar L)
              ((2 * LocalGood.CU p m A + 1) / 2)
              (LocalGood.betaCU ((2 * LocalGood.CU p m A + 1) / 2)
                (LocCoordPaper.CTof (LocalGood.CU p m A) T) L)
              ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4))
              (locCoordGeom p m A hA r T L) U}
        ≤ CT * Real.exp (-(lam * LocSumAct.xOf L)) := by
  intro T
  obtain ⟨c, hc, L₀, hLc⟩ :=
    measureReal_locMoveFailAtClock_T3_CU (N := N) hp0 hp1 hm A hA hAc T
  have hCT1 : (1 : ℝ) ≤ LocCoordPaper.CTof (LocalGood.CU p m A) T :=
    LocCoordPaper.one_le_CTof (le_trans zero_le_one (LocalGood.one_le_CU p m A)) T
  have hCTc : (0 : ℝ) ≤ LocCoordPaper.CTof (LocalGood.CU p m A) T := by linarith
  have hT3 : (0 : ℝ) < (T : ℝ) + 3 := by positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have h321 : (0 : ℝ) < 321 * (N : ℝ) := by linarith
  have ha₁ : (0 : ℝ) < 1 / (4 * ((T : ℝ) + 3) * (321 * (N : ℝ)) ^ 2) := by positivity
  have ha₂ : (0 : ℝ) < 1 / (1024 * ((T : ℝ) + 3)) := by positivity
  have hcT : (0 : ℝ) < c / 2 := by linarith
  obtain ⟨C₁, hC₁0, L₁, hL₁⟩ :=
    LocalGood.absorb_rpow (a := 1 / (4 * ((T : ℝ) + 3) * (321 * (N : ℝ)) ^ 2))
      (c_T := c / 2) ha₁ hcT (j := 4) (k := 2) (by norm_num) (by norm_num)
  obtain ⟨C₂, hC₂0, L₂, hL₂⟩ :=
    LocalGood.absorb_rpow (a := 1 / (1024 * ((T : ℝ) + 3)))
      (c_T := c / 2) ha₂ hcT (j := 6) (k := 2) (by norm_num) (by norm_num)
  refine ⟨c / 2,
    2 * ((T : ℝ) + 4) ^ 2 * C₁ + 2 * ((T : ℝ) + 4) ^ 2 * C₂
      + LocCoordPaper.CTof (LocalGood.CU p m A) T, by linarith, by
        have h1 : (0 : ℝ) ≤ 2 * ((T : ℝ) + 4) ^ 2 * C₁ := by positivity
        have h2 : (0 : ℝ) ≤ 2 * ((T : ℝ) + 4) ^ 2 * C₂ := by positivity
        linarith [hCT1],
    max (max L₀ L₁) L₂, ?_⟩
  intro L hLbig r hr
  have hinner : max (max L₀ L₁) L₂ ≤ L :=
    le_trans (le_max_left (max (max L₀ L₁) L₂) 2) hLbig
  have hL0 : L₀ ≤ L :=
    le_trans (le_max_left L₀ L₁) (le_trans (le_max_left (max L₀ L₁) L₂) hinner)
  have hL1 : L₁ ≤ L :=
    le_trans (le_max_right L₀ L₁) (le_trans (le_max_left (max L₀ L₁) L₂) hinner)
  have hL2 : L₂ ≤ L := le_trans (le_max_right (max L₀ L₁) L₂) hinner
  have hL2' : 2 ≤ L := le_trans (le_max_right (max (max L₀ L₁) L₂) 2) hLbig
  have hL1' : 1 ≤ L := by omega
  have hLr : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1'
  have hL0r : (0 : ℝ) ≤ (L : ℝ) := by positivity
  have hx1 : (1 : ℝ) ≤ LocSumAct.xOf L := LocSumAct.one_le_xOf hL1'
  have hx0 : (0 : ℝ) ≤ LocSumAct.xOf L := le_trans zero_le_one hx1
  have hε : (0 : ℝ) < (L : ℝ) ^ ((3 : ℝ) / 4) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hBpos : 0 < RecClockLG.Bstar L := RecClockLG.Bstar_pos hL1'
  have hLbig0 : max L₀ 2 ≤ L := max_le hL0 hL2'
  have hprev := hLc L hLbig0 r hr
  -- the polynomial prefactor at the record scale
  have hK2 : ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 ≤ ((T : ℝ) + 4) ^ 2 * (L : ℝ) ^ 2 := by
    have h1 : ((((T + 3) * L : ℕ) : ℝ) + 1) ≤ ((T : ℝ) + 4) * (L : ℝ) := by
      push_cast
      nlinarith [hLr, Nat.cast_nonneg (α := ℝ) T]
    have h2 : ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 ≤ (((T : ℝ) + 4) * (L : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    calc ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 ≤ (((T : ℝ) + 4) * (L : ℝ)) ^ 2 := h2
      _ = ((T : ℝ) + 4) ^ 2 * (L : ℝ) ^ 2 := by ring
  -- the two deviation exponents at `B = Bstar L`
  have hexp₁ : Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
        (4 * (((T + 3) * L : ℕ) : ℝ)
          * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2))
      ≤ Real.exp (-((1 / (4 * ((T : ℝ) + 3) * (321 * (N : ℝ)) ^ 2))
          * (LocSumAct.xOf L) ^ 4)) := by
    apply Real.exp_le_exp.mpr
    have h := gamma_exp_at_Bstar (N := N) (T := T) (L := L) hp0 hp1.le hN hL1'
    rw [show -(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
          (4 * (((T + 3) * L : ℕ) : ℝ)
            * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2)
        = -((((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
          (4 * (((T + 3) * L : ℕ) : ℝ)
            * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2)) from by rw [neg_div]]
    linarith
  have hexp₂ : Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
        (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * RecClockLG.Bstar L) ^ 2))
      ≤ Real.exp (-((1 / (1024 * ((T : ℝ) + 3))) * (LocSumAct.xOf L) ^ 6)) := by
    apply Real.exp_le_exp.mpr
    have h := maxgrowth_exp_at_Bstar (T := T) (L := L) hL1'
    rw [show -(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
          (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * RecClockLG.Bstar L) ^ 2)
        = -((((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
          (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * RecClockLG.Bstar L) ^ 2)) from by rw [neg_div]]
    linarith
  have hT1 : 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
        Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
          (4 * (((T + 3) * L : ℕ) : ℝ)
            * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2))
      ≤ 2 * ((T : ℝ) + 4) ^ 2 *
          ((L : ℝ) ^ 2 * Real.exp (-((1 / (4 * ((T : ℝ) + 3) * (321 * (N : ℝ)) ^ 2))
            * (LocSumAct.xOf L) ^ 4))) := by
    have h1 : 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
          Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
            (4 * (((T + 3) * L : ℕ) : ℝ)
              * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2))
        ≤ 2 * (((T : ℝ) + 4) ^ 2 * (L : ℝ) ^ 2) *
            Real.exp (-((1 / (4 * ((T : ℝ) + 3) * (321 * (N : ℝ)) ^ 2))
              * (LocSumAct.xOf L) ^ 4)) := by
      refine mul_le_mul ?_ hexp₁ (Real.exp_pos _).le (by positivity)
      linarith [hK2]
    calc 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
          Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
            (4 * (((T + 3) * L : ℕ) : ℝ)
              * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2))
        ≤ 2 * (((T : ℝ) + 4) ^ 2 * (L : ℝ) ^ 2) *
            Real.exp (-((1 / (4 * ((T : ℝ) + 3) * (321 * (N : ℝ)) ^ 2))
              * (LocSumAct.xOf L) ^ 4)) := h1
      _ = 2 * ((T : ℝ) + 4) ^ 2 *
            ((L : ℝ) ^ 2 * Real.exp (-((1 / (4 * ((T : ℝ) + 3) * (321 * (N : ℝ)) ^ 2))
              * (LocSumAct.xOf L) ^ 4))) := by ring
  have hT2 : 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
        Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
          (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * RecClockLG.Bstar L) ^ 2))
      ≤ 2 * ((T : ℝ) + 4) ^ 2 *
          ((L : ℝ) ^ 2 * Real.exp (-((1 / (1024 * ((T : ℝ) + 3)))
            * (LocSumAct.xOf L) ^ 6))) := by
    have h1 : 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
          Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
            (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * RecClockLG.Bstar L) ^ 2))
        ≤ 2 * (((T : ℝ) + 4) ^ 2 * (L : ℝ) ^ 2) *
            Real.exp (-((1 / (1024 * ((T : ℝ) + 3))) * (LocSumAct.xOf L) ^ 6)) := by
      refine mul_le_mul ?_ hexp₂ (Real.exp_pos _).le (by positivity)
      linarith [hK2]
    calc 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
          Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
            (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * RecClockLG.Bstar L) ^ 2))
        ≤ 2 * (((T : ℝ) + 4) ^ 2 * (L : ℝ) ^ 2) *
            Real.exp (-((1 / (1024 * ((T : ℝ) + 3))) * (LocSumAct.xOf L) ^ 6)) := h1
      _ = 2 * ((T : ℝ) + 4) ^ 2 *
            ((L : ℝ) ^ 2 * Real.exp (-((1 / (1024 * ((T : ℝ) + 3)))
              * (LocSumAct.xOf L) ^ 6))) := by ring
  have hT3 : LocCoordPaper.CTof (LocalGood.CU p m A) T * Real.exp (-c * LocSumAct.xOf L)
      ≤ LocCoordPaper.CTof (LocalGood.CU p m A) T
        * Real.exp (-((c / 2) * LocSumAct.xOf L)) := by
    refine mul_le_mul_of_nonneg_left ?_ hCTc
    apply Real.exp_le_exp.mpr
    nlinarith [hx0]
  have hsum : 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
        Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
          (4 * (((T + 3) * L : ℕ) : ℝ)
            * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2))
      + 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
        Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
          (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * RecClockLG.Bstar L) ^ 2))
      + LocCoordPaper.CTof (LocalGood.CU p m A) T * Real.exp (-c * LocSumAct.xOf L)
      ≤ 2 * ((T : ℝ) + 4) ^ 2 * C₁ * Real.exp (-((c / 2) * LocSumAct.xOf L))
        + 2 * ((T : ℝ) + 4) ^ 2 * C₂ * Real.exp (-((c / 2) * LocSumAct.xOf L))
        + LocCoordPaper.CTof (LocalGood.CU p m A) T
          * Real.exp (-((c / 2) * LocSumAct.xOf L)) := by
    have h1' : 2 * ((T : ℝ) + 4) ^ 2 *
          ((L : ℝ) ^ 2 * Real.exp (-((1 / (4 * ((T : ℝ) + 3) * (321 * (N : ℝ)) ^ 2))
            * (LocSumAct.xOf L) ^ 4)))
        ≤ 2 * ((T : ℝ) + 4) ^ 2 * (C₁ * Real.exp (-((c / 2) * LocSumAct.xOf L))) :=
      mul_le_mul_of_nonneg_left (hL₁ L hL1) (by positivity)
    have h2' : 2 * ((T : ℝ) + 4) ^ 2 *
          ((L : ℝ) ^ 2 * Real.exp (-((1 / (1024 * ((T : ℝ) + 3)))
            * (LocSumAct.xOf L) ^ 6)))
        ≤ 2 * ((T : ℝ) + 4) ^ 2 * (C₂ * Real.exp (-((c / 2) * LocSumAct.xOf L))) :=
      mul_le_mul_of_nonneg_left (hL₂ L hL2) (by positivity)
    have e1 : 2 * ((T : ℝ) + 4) ^ 2 * (C₁ * Real.exp (-((c / 2) * LocSumAct.xOf L)))
        = 2 * ((T : ℝ) + 4) ^ 2 * C₁ * Real.exp (-((c / 2) * LocSumAct.xOf L)) := by ring
    have e2 : 2 * ((T : ℝ) + 4) ^ 2 * (C₂ * Real.exp (-((c / 2) * LocSumAct.xOf L)))
        = 2 * ((T : ℝ) + 4) ^ 2 * C₂ * Real.exp (-((c / 2) * LocSumAct.xOf L)) := by ring
    linarith [hT1, hT2, hT3, h1', h2', e1, e2]
  have hfinal : 2 * ((T : ℝ) + 4) ^ 2 * C₁ * Real.exp (-((c / 2) * LocSumAct.xOf L))
        + 2 * ((T : ℝ) + 4) ^ 2 * C₂ * Real.exp (-((c / 2) * LocSumAct.xOf L))
        + LocCoordPaper.CTof (LocalGood.CU p m A) T
          * Real.exp (-((c / 2) * LocSumAct.xOf L))
      = (2 * ((T : ℝ) + 4) ^ 2 * C₁ + 2 * ((T : ℝ) + 4) ^ 2 * C₂
          + LocCoordPaper.CTof (LocalGood.CU p m A) T)
        * Real.exp (-((c / 2) * LocSumAct.xOf L)) := by ring
  calc (arrayMeasure N).real
        {U : Array N |
          locMoveFailAtClock p m A hA hAc r T L (RecClockLG.Bstar L)
            ((2 * LocalGood.CU p m A + 1) / 2)
            (LocalGood.betaCU ((2 * LocalGood.CU p m A + 1) / 2)
              (LocCoordPaper.CTof (LocalGood.CU p m A) T) L)
            ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4))
            (locCoordGeom p m A hA r T L) U}
      ≤ 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
            Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
              (4 * (((T + 3) * L : ℕ) : ℝ)
                * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2))
          + 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
            Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
              (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * RecClockLG.Bstar L) ^ 2))
          + LocCoordPaper.CTof (LocalGood.CU p m A) T * Real.exp (-c * LocSumAct.xOf L) :=
        hprev
    _ ≤ 2 * ((T : ℝ) + 4) ^ 2 * C₁ * Real.exp (-((c / 2) * LocSumAct.xOf L))
          + 2 * ((T : ℝ) + 4) ^ 2 * C₂ * Real.exp (-((c / 2) * LocSumAct.xOf L))
          + LocCoordPaper.CTof (LocalGood.CU p m A) T
            * Real.exp (-((c / 2) * LocSumAct.xOf L)) := hsum
    _ = (2 * ((T : ℝ) + 4) ^ 2 * C₁ + 2 * ((T : ℝ) + 4) ^ 2 * C₂
          + LocCoordPaper.CTof (LocalGood.CU p m A) T)
        * Real.exp (-((c / 2) * LocSumAct.xOf L)) := hfinal

end ClockLocMove
