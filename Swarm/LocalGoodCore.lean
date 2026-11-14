/-
# A single `(locsum)` carrier for `(loccoord)` and `(locmove)` at the paper's `(T+3)L`

## What is new here (relative to the public tree)

The public `(locmove)` results (`WCJFSharp.exists_measure_locmove_total_all`,
`..._paper_scale_all`, `LocMoveCompose.measure_locmove_le`) all carry the *undischarged*
hypothesis

  `hγC : 1 ≤ gammaRate p m A * C`

on the `(locsum)` constant `C` of the `(loccoord)` input, and they also require the *record
threshold* `(3T+6)L ≤ r` (from `Loccoord.loccoord_full_window`), not the paper's `(T+3)L ≤ r`.
`gammaRate p m A = (2p-1)(1-p)^((2m-1)|A|)/|A|` can be arbitrarily small, so the canonical
constant `Ccan = |Mb|+1` does **not** in general satisfy `hγC`: as it stands `(locmove)` is not
instantiated at any concrete `(locsum)` constant.

This file

* defines `CU p m A = max (Ccan p m) (1 / gammaRate p m A)`, a `T`-free and `L`-free constant
  which is `≥ 1`, `> Mb p (qOf p m)`, and satisfies `1 ≤ gammaRate p m A * CU p m A`
  (`gammaRate_mul_CU`), so `hγC` is *discharged*;
* re-points `(locmove)` at `LocCoordPaper.loccoord_full_window_T3`, i.e. at the paper's
  threshold `(T+3)L ≤ r` and at the single `(locsum)` bad set
  `LsBad N p m (CU) ((2T+4)L) (r-(T+2)L)` — the *same* set that carries `(loccoord)`;
* consequently the `(loccoord)` carrier term and the `(locmove)` carrier term of the merged
  local-good event are literally the same event, and the `(locmove)` error term becomes
  `C_T L^{3/4}` (the paper's `C_T L^{3/4}` shape) instead of `3 C betaT(...)`.

Nothing here asserts `(locmove)` itself unconditionally: the display still holds only on the
carrier `locmoveGood` (record window `ambGood` pinned at `r`, `(sep)` on `[s,t)`, the two step
truncations) together with the range facts `geom`.  No separation survival, no event positivity,
no invariant measure and no `MainClaim` is claimed.
-/
import Swarm.LocGroupSimultaneous
import Swarm.LocOccAllPairFibreSum
import Swarm.LocCoordPaper
import Swarm.LocMoveAllWindows

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace LocalGood

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift LocGroupQ LocGroupWindow LocMoveMart LocMoveLocal Swarming.Enl Loccoord
open RecordDefect RecordoSupply SwarmRecordMeas SwarmRecordMeas.Actual

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. The single `(locsum)` constant `CU` -/

/-- The single `(locsum)` constant used by both `(loccoord)` and `(locmove)`:
`CU = max Ccan (1 / gammaRate)`.  It is `T`- and `L`-free, `≥ 1`, `> Mb p (qOf p m)`, and large
enough that the `(locmove)` `Γ`-drift rate dominates the coefficient `1/C` of the display. -/
noncomputable def CU (p : ℝ) (m : ℕ) (A : Finset (Fin N)) : ℝ :=
  max (LocCoordPaper.Ccan p m) (1 / LocMoveCompose.gammaRate p m A)

theorem CU_pos (p : ℝ) (m : ℕ) (A : Finset (Fin N)) : 0 < CU p m A :=
  lt_of_lt_of_le zero_lt_one (LocCoordPaper.one_le_Ccan p m |>.trans (le_max_left _ _))

theorem one_le_CU (p : ℝ) (m : ℕ) (A : Finset (Fin N)) : 1 ≤ CU p m A :=
  (LocCoordPaper.one_le_Ccan p m).trans (le_max_left _ _)

theorem Mb_lt_CU (p : ℝ) (m : ℕ) (A : Finset (Fin N)) :
    LocSum.Mb p (LocSumAct.qOf p m) < CU p m A :=
  (LocCoordPaper.Mb_lt_Ccan p m).trans_le (le_max_left _ _)

/-- The paper's `Γ`-drift coefficient `(2p-1)(1-p)^((2m-1)|A|)/|A|` is positive. -/
theorem gammaRate_pos {p : ℝ} (hp : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {A : Finset (Fin N)} (hA : A.Nonempty) : 0 < LocMoveCompose.gammaRate p m A := by
  rw [LocMoveCompose.gammaRate]
  have h1 : (0 : ℝ) < 2 * p - 1 := by linarith
  have h2 : (0 : ℝ) < 1 - p := by linarith
  have h3 : (0 : ℝ) < ((A.card : ℕ) : ℝ) := by exact_mod_cast Finset.card_pos.mpr hA
  exact div_pos (mul_pos h1 (pow_pos h2 _)) h3

/-- `1 ≤ gammaRate * CU`: the hypothesis `hγC` of the `(locmove)` chain is *discharged* at the
`(locsum)` constant `CU`. -/
theorem gammaRate_mul_CU {p : ℝ} (hp : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {A : Finset (Fin N)} (hA : A.Nonempty) :
    1 ≤ LocMoveCompose.gammaRate p m A * CU p m A := by
  have hg : 0 < LocMoveCompose.gammaRate p m A := gammaRate_pos hp hp1 hA
  have hle : 1 / LocMoveCompose.gammaRate p m A ≤ CU p m A := le_max_right _ _
  have h1 : (1 / LocMoveCompose.gammaRate p m A) * LocMoveCompose.gammaRate p m A = 1 := by
    field_simp
  calc (1 : ℝ) = (1 / LocMoveCompose.gammaRate p m A) * LocMoveCompose.gammaRate p m A := h1.symm
    _ ≤ CU p m A * LocMoveCompose.gammaRate p m A :=
        mul_le_mul_of_nonneg_right hle hg.le
    _ = LocMoveCompose.gammaRate p m A * CU p m A := by ring

/-- `CU` dominates the canonical constant. -/
theorem Ccan_le_CU (p : ℝ) (m : ℕ) (A : Finset (Fin N)) :
    LocCoordPaper.Ccan p m ≤ CU p m A := le_max_left _ _

/-- The coefficient `(2 CU + 1)/2` of the `(loccoord)` display, and its size. -/
theorem one_le_coefCU (p : ℝ) (m : ℕ) (A : Finset (Fin N)) :
    1 ≤ (2 * CU p m A + 1) / 2 := by
  have h := one_le_CU p m A
  linarith

/-! ## 2. `(loccoord)` at the constant `CU`, at the paper's threshold `(T+3)L ≤ r` -/

/-- **`(loccoord)` at `CU`.**  Identical to `LocCoordPaper.loccoord_full_window_T3` at the
concrete constant `CU p m A`: one `(locsum)` bad set
`LsBad N p m (CU) ((2T+4)L) (r-(T+2)L)`, measured by `C_T exp(-c_T L^{1/16})`, and off it the
paper's `(loccoord)` estimate at the coefficient `(2 CU + 1)/2` with remainder `C_T L^{3/4}`. -/
theorem loccoord_CU {p : ℝ} (hp : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (A : Finset (Fin N)) (hA : A.Nonempty) (T : ℕ) :
    ∃ c_T C_T : ℝ, 0 < c_T ∧ 1 ≤ C_T ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
      (arrayMeasure N) (LocSumR1.LsBad N p m (CU p m A) ((2 * T + 4) * L) (r - (T + 2) * L))
        ≤ ENNReal.ofReal (C_T * Real.exp (-c_T * (L : ℝ) ^ (1 / 16 : ℝ))) ∧
      ∀ U : Array N,
      U ∉ LocSumR1.LsBad N p m (CU p m A) ((2 * T + 4) * L) (r - (T + 2) * L) →
      ∀ (B : Finset (Fin N)) (hB : B.Nonempty), ∀ s t : ℕ, s ≤ t →
      (hX0 : 0 ≤ Loccoord.Xmin p m U B hB s) →
      r - (T + 2) * L ≤ (Loccoord.Xmin p m U B hB s).toNat →
      (Loccoord.Rmax p m U B hB t).toNat ≤ r + (T + 2) * L →
      Swarming.Group.average B (fun k =>
          HA p m U t B (X p m U t k) - HA p m U s B (X p m U s k))
        ≤ ((2 * CU p m A + 1) / 2)
            * (((Loccoord.Rmax p m U B hB t : ℤ) : ℝ)
                - ((Loccoord.Xmin p m U B hB s : ℤ) : ℝ))
          + C_T * (L : ℝ) ^ (3 / 4 : ℝ) :=
  LocCoordPaper.loccoord_full_window_T3 (N := N) hp hp1 hm (one_le_CU p m A) (Mb_lt_CU p m A) T

/-- **`(loccoord)` at `CU` with the *explicit* constant `CTof CU T`.**

Same content as `loccoord_CU`, but the `T`-dependent constant is the named
`CTof (CU p m A) T = 9 CU (2T+4)^{3/4} + 1` instead of an opaque existential, so that the
`(locmove)` display's error term (and hence the merged local-good event) is a *definition* and not
a function of a proof's witness. -/
theorem loccoord_CU_explicit {p : ℝ} (hp : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (A : Finset (Fin N)) (hA : A.Nonempty) (T : ℕ) :
    ∃ c_T : ℝ, 0 < c_T ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
      (arrayMeasure N) (LocSumR1.LsBad N p m (CU p m A) ((2 * T + 4) * L) (r - (T + 2) * L))
        ≤ ENNReal.ofReal
            (LocCoordPaper.CTof (CU p m A) T * Real.exp (-c_T * (L : ℝ) ^ (1 / 16 : ℝ))) ∧
      ∀ U : Array N,
      U ∉ LocSumR1.LsBad N p m (CU p m A) ((2 * T + 4) * L) (r - (T + 2) * L) →
      ∀ (B : Finset (Fin N)) (hB : B.Nonempty), ∀ s t : ℕ, s ≤ t →
      (hX0 : 0 ≤ Loccoord.Xmin p m U B hB s) →
      r - (T + 2) * L ≤ (Loccoord.Xmin p m U B hB s).toNat →
      (Loccoord.Rmax p m U B hB t).toNat ≤ r + (T + 2) * L →
      Swarming.Group.average B (fun k =>
          HA p m U t B (X p m U t k) - HA p m U s B (X p m U s k))
        ≤ ((2 * CU p m A + 1) / 2)
            * (((Loccoord.Rmax p m U B hB t : ℤ) : ℝ)
                - ((Loccoord.Xmin p m U B hB s : ℤ) : ℝ))
          + LocCoordPaper.CTof (CU p m A) T * (L : ℝ) ^ (3 / 4 : ℝ) := by
  obtain ⟨c, hc, L₀, hL⟩ :=
    Loccoord.loccoord_full_window_concrete (N := N) hp hp1 hm
      (C := CU p m A) (one_le_CU p m A) (Mb_lt_CU p m A)
  obtain ⟨L₁, hL₁⟩ := LocCoordPaper.exists_arith_L0 T
  refine ⟨c, hc, max L₀ (max L₁ 1), ?_⟩
  intro L hLbig r hr
  have hL0 : L₀ ≤ L := le_trans (le_max_left _ _) hLbig
  have hLarith : (2 * T + 4) * 4 ^ 16 ≤ L ^ 15 :=
    hL₁ L (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLbig)
  have hL1 : 1 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hLbig
  obtain ⟨hprob, hbound⟩ := hL L hL0 T r hr hLarith
  constructor
  · -- the exponent `xOf ((2T+4)L) ≥ xOf L`
    have hMge : L ≤ (2 * T + 4) * L := by
      have hpos : 0 < 2 * T + 4 := by omega
      calc L = L * 1 := (Nat.mul_one L).symm
        _ ≤ L * (2 * T + 4) := Nat.mul_le_mul_left L (by omega)
        _ = (2 * T + 4) * L := Nat.mul_comm _ _
    have hxle : LocSumAct.xOf L ≤ LocSumAct.xOf ((2 * T + 4) * L) := by
      rw [LocSumAct.xOf, LocSumAct.xOf]
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hMge) (by norm_num)
    have hCT1 : 1 ≤ LocCoordPaper.CTof (CU p m A) T :=
      LocCoordPaper.one_le_CTof (le_trans zero_le_one (one_le_CU p m A)) T
    have hexp : Real.exp (-c * LocSumAct.xOf ((2 * T + 4) * L))
        ≤ LocCoordPaper.CTof (CU p m A) T * Real.exp (-c * (L : ℝ) ^ (1 / 16 : ℝ)) := by
      have h1 : Real.exp (-c * LocSumAct.xOf ((2 * T + 4) * L))
          ≤ Real.exp (-c * (L : ℝ) ^ (1 / 16 : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have hxx : LocSumAct.xOf L = (L : ℝ) ^ (1 / 16 : ℝ) := rfl
        have : c * (L : ℝ) ^ (1 / 16 : ℝ) ≤ c * LocSumAct.xOf ((2 * T + 4) * L) := by
          rw [hxx] at hxle
          exact mul_le_mul_of_nonneg_left hxle hc.le
        linarith
      have h2 : Real.exp (-c * (L : ℝ) ^ (1 / 16 : ℝ))
          = 1 * Real.exp (-c * (L : ℝ) ^ (1 / 16 : ℝ)) := by ring
      calc Real.exp (-c * LocSumAct.xOf ((2 * T + 4) * L))
          ≤ Real.exp (-c * (L : ℝ) ^ (1 / 16 : ℝ)) := h1
        _ = 1 * Real.exp (-c * (L : ℝ) ^ (1 / 16 : ℝ)) := h2
        _ ≤ LocCoordPaper.CTof (CU p m A) T * Real.exp (-c * (L : ℝ) ^ (1 / 16 : ℝ)) :=
            mul_le_mul_of_nonneg_right hCT1 (Real.exp_pos _).le
    refine le_trans hprob (ENNReal.ofReal_le_ofReal hexp)
  · intro U hU B hB s t hst hX0 hXmin hRmax
    have hmain := hbound U hU B hB s t hst hX0 hXmin hRmax
    have hrem := LocCoordPaper.betaT_normalise_of (C := CU p m A)
      (le_trans zero_le_one (one_le_CU p m A)) (T := T) hL1
    linarith [hmain, hrem]

/-! ## 3. `(locmove)` at the paper's threshold `(T+3)L ≤ r` and at the constant `CU` -/

/-- The `(locmove)` error coefficient `beta` chosen so that `3 C beta = C_T L^{3/4}`: the
`(loccoord)` remainder `C_T L^{3/4}` *is* the `3 C β` term of `locmoveRHS`. -/
noncomputable def betaCU (C C_T : ℝ) (L : ℕ) : ℝ :=
  C_T * (L : ℝ) ^ (3 / 4 : ℝ) / (3 * C)

theorem three_mul_betaCU {C C_T : ℝ} (hC : C ≠ 0) (L : ℕ) :
    3 * C * betaCU C C_T L = C_T * (L : ℝ) ^ (3 / 4 : ℝ) := by
  rw [betaCU]
  field_simp

/-- **`(locmove)` measured bound at the paper's record threshold, with the `(locsum)` carrier
discharged at `CU`.**

For `1/2 < p < 1`, `2 ≤ m`, nonempty proper `A ⊂ Fin N` and `T ≥ 1` there are `c_T > 0`,
`C_T ≥ 0` and `L₀` such that for every `L ≥ L₀`, every `r ≥ (T+3)L`, every clock `n0` and every
window `n0 ≤ s ≤ t ≤ n0 + (T+3)L` with `1 ≤ t-s`:

on the `(locmove)` carrier `locmoveGood` (record window `ambGood` pinned at `r`, `(sep)` on
`[s,t)`, the two step truncations) together with the range facts `geom`, the display of
`(locmove)` at the coefficient `(2 CU + 1)/2` and error `max (C_T L^{3/4} + L^{3/4})
(gammaErr + L^{3/4})` can fail only on a set of `arrayMeasure`-measure at most

  `2 (t-s+1) e^{-(xOf L)^6/(8(T+3))} + 2 (t-s+1) e^{-(xOf L)^4/(800 N² (T+3))}
     + C_T e^{-c_T L^{1/16}}`,

whose only `(locsum)` input is `loccoord_CU`.  In particular the record threshold is the paper's
`(T+3)L ≤ r` (not `(3T+6)L ≤ r`) and the previously undischarged `hγC` is gone. -/
theorem exists_measure_locmove_T3 {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    (hN : 1 ≤ N) (T : ℕ) (hT : 1 ≤ T) :
    ∃ c_T : ℝ, 0 < c_T ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
      ∀ {n0 s t : ℕ}, n0 ≤ s → s ≤ t → t ≤ n0 + (T + 3) * L → 1 ≤ t - s →
      (arrayMeasure N).real
        {U : Array N |
          LocMoveCompose.locmoveGood p m A hA (r : ℤ) T L (LocSumAct.xOf L) n0 s t U ∧
            (0 ≤ Loccoord.Xmin p m U A hA s ∧
              r - (T + 2) * L ≤ (Loccoord.Xmin p m U A hA s).toNat ∧
              (Loccoord.Rmax p m U A hA t).toNat ≤ r + (T + 2) * L) ∧
            ¬ (WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
                ≤ LocMoveCompose.locmoveRHS p m A hA L ((2 * CU p m A + 1) / 2)
                    (betaCU ((2 * CU p m A + 1) / 2) (LocCoordPaper.CTof (CU p m A) T) L)
                    ((L : ℝ) ^ (3 / 4 : ℝ)) ((L : ℝ) ^ (3 / 4 : ℝ)) s t U)}
        ≤ 2 * (((t - s : ℕ) : ℝ) + 1) *
            Real.exp (-((LocSumAct.xOf L) ^ 6 / (8 * ((T : ℝ) + 3))))
          + 2 * (((t - s : ℕ) : ℝ) + 1) *
            Real.exp (-((LocSumAct.xOf L) ^ 4 / (800 * ((N : ℝ) ^ 2 * ((T : ℝ) + 3)))))
          + LocCoordPaper.CTof (CU p m A) T * Real.exp (-c_T * (L : ℝ) ^ (1 / 16 : ℝ)) := by
  haveI hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  obtain ⟨c, hc, L₀, hLL⟩ := loccoord_CU_explicit (N := N) hp0 hp1 hm A hA T
  refine ⟨c, hc, max (max L₀ 1) 1, ?_⟩
  intro L hLbig r hr n0 s t hn0 hst hhor hK
  have hL0 : L₀ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLbig
  have hL1 : 1 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLbig
  have hCUp : 0 < CU p m A := CU_pos p m A
  set C : ℝ := (2 * CU p m A + 1) / 2 with hCdef
  have hC1 : 1 ≤ C := one_le_coefCU p m A
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hCne : C ≠ 0 := ne_of_gt hCpos
  have hγC : 1 ≤ LocMoveCompose.gammaRate p m A * C := by
    refine le_trans (gammaRate_mul_CU (N := N) (m := m) hp0 hp1 hA) ?_
    have hγ : 0 ≤ LocMoveCompose.gammaRate p m A := (gammaRate_pos hp0 hp1 hA).le
    have hle : CU p m A ≤ C := by rw [hCdef]; linarith
    exact mul_le_mul_of_nonneg_left hle hγ
  set β : ℝ := betaCU C (LocCoordPaper.CTof (CU p m A) T) L with hβdef
  have h3Cβ : 3 * C * β = LocCoordPaper.CTof (CU p m A) T * (L : ℝ) ^ (3 / 4 : ℝ) :=
    three_mul_betaCU hCne L
  have hε : (0 : ℝ) < (L : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL1)) _
  set B : ℝ := LocSumAct.xOf L with hBdef
  have hBpos : 0 < B := by
    rw [hBdef]
    exact lt_of_lt_of_le zero_lt_one (LocSumAct.one_le_xOf hL1)
  -- the `(locsum)` bad set and the range facts
  set bad : Set (Array N) :=
    LocSumR1.LsBad N p m (CU p m A) ((2 * T + 4) * L) (r - (T + 2) * L) with hbaddef
  set geom : Set (Array N) :=
    {U : Array N | 0 ≤ Loccoord.Xmin p m U A hA s ∧
      r - (T + 2) * L ≤ (Loccoord.Xmin p m U A hA s).toNat ∧
      (Loccoord.Rmax p m U A hA t).toNat ≤ r + (T + 2) * L} with hgeomdef
  have hbadmeas : (arrayMeasure N).real bad
      ≤ LocCoordPaper.CTof (CU p m A) T * Real.exp (-c * (L : ℝ) ^ (1 / 16 : ℝ)) := by
    have h1 := (hLL L hL0 r hr).1
    rw [measureReal_def]
    refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top h1) ?_
    rw [ENNReal.toReal_ofReal
      (mul_nonneg (le_trans zero_le_one
        (LocCoordPaper.one_le_CTof (le_trans zero_le_one (one_le_CU p m A)) T))
        (Real.exp_pos _).le)]
  have hcc : ∀ U : Array N, U ∉ bad → U ∈ geom →
      Swarming.Group.average A
        (fun k => HA p m U t A (X p m U t k) - HA p m U s A (X p m U s k))
        ≤ C * (((Swarming.Enl.runMaxA p m U hA t : ℤ) : ℝ)
            - ((Loccoord.Xmin p m U A hA s : ℤ) : ℝ)) + 3 * C * β := by
    intro U hUb hUg
    obtain ⟨hX0, hAle, hLb⟩ := hUg
    have hres := (hLL L hL0 r hr).2 U hUb A hA s t hst hX0 hAle hLb
    have hRmax : ((Loccoord.Rmax p m U A hA t : ℤ) : ℝ)
        = ((Swarming.Enl.runMaxA p m U hA t : ℤ) : ℝ) := rfl
    rw [hRmax] at hres
    rw [hCdef, h3Cβ]
    exact hres
  have hmain := WCJFSharp.measure_locmove_le_all (N := N) hp0 hp1 (le_trans (by norm_num : 1 ≤ 2) hm)
    A hA hAc (Th := T) (Lh := L) hL1 (r := (r : ℤ)) (by exact_mod_cast hr)
    hn0 hst hhor (B := B) (ε₁ := (L : ℝ) ^ (3 / 4 : ℝ)) (ε₂ := (L : ℝ) ^ (3 / 4 : ℝ))
    (C := C) (β := β) hBpos hC1 hγC hε hε hK (bad := bad) (geom := geom)
    (eb := LocCoordPaper.CTof (CU p m A) T * Real.exp (-c * (L : ℝ) ^ (1 / 16 : ℝ))) hcc hbadmeas
  -- the exponent comparisons, at `B = xOf L` and `ε₁ = ε₂ = L^{3/4}`
  have hKle : t - s ≤ (T + 3) * L := by omega
  have hE₁ : Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
        (2 * (((t - s : ℕ) : ℝ) * (2 * LocGroupWindow.stepEnv (N := N) p B) ^ 2)))
      ≤ Real.exp (-((LocSumAct.xOf L) ^ 4 / (800 * ((N : ℝ) ^ 2 * ((T : ℝ) + 3))))) := by
    apply Real.exp_le_exp.mpr
    have hB' : LocGroupWindow.stepEnv (N := N) p B = LocGroupWindow.stepEnv (N := N) p (LocSumAct.xOf L) := by
      rw [hBdef]
    rw [hB']
    have hassoc : (2 * (((t - s : ℕ) : ℝ)
        * (2 * LocGroupWindow.stepEnv (N := N) p (LocSumAct.xOf L)) ^ 2))
        = 2 * ((t - s : ℕ) : ℝ) * (2 * LocGroupWindow.stepEnv (N := N) p (LocSumAct.xOf L)) ^ 2 := by
      ring
    rw [hassoc]
    exact WCJFSharp.gamma_exponent_le_half (N := N) hL1 hK hKle hp0 hp1.le hN
  have hE₂ : Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
        (2 * (((t - s : ℕ) : ℝ) * (2 * B) ^ 2)))
      ≤ Real.exp (-((LocSumAct.xOf L) ^ 6 / (8 * ((T : ℝ) + 3)))) := by
    apply Real.exp_le_exp.mpr
    rw [hBdef]
    have hassoc : (2 * (((t - s : ℕ) : ℝ) * (2 * LocSumAct.xOf L) ^ 2))
        = 2 * ((t - s : ℕ) : ℝ) * (2 * LocSumAct.xOf L) ^ 2 := by ring
    rw [hassoc]
    exact WCJFSharp.maxgrowth_exponent_le_half hL1 hK hKle
  refine le_trans hmain ?_
  have h1 : 2 * (((t - s : ℕ) : ℝ) + 1) *
        Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
          (2 * (((t - s : ℕ) : ℝ) * (2 * LocGroupWindow.stepEnv (N := N) p B) ^ 2)))
      ≤ 2 * (((t - s : ℕ) : ℝ) + 1) *
        Real.exp (-((LocSumAct.xOf L) ^ 4 / (800 * ((N : ℝ) ^ 2 * ((T : ℝ) + 3))))) := by
    apply mul_le_mul_of_nonneg_left hE₁ (by positivity)
  have h2 : 2 * (((t - s : ℕ) : ℝ) + 1) *
        Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) / (2 * (((t - s : ℕ) : ℝ) * (2 * B) ^ 2)))
      ≤ 2 * (((t - s : ℕ) : ℝ) + 1) *
        Real.exp (-((LocSumAct.xOf L) ^ 6 / (8 * ((T : ℝ) + 3)))) := by
    apply mul_le_mul_of_nonneg_left hE₂ (by positivity)
  linarith [h1, h2]

end LocalGood
