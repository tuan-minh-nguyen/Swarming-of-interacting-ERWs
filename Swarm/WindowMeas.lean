/-
# The windowed `(locmove)` failure event at the canonical geometry and its group union

This file instantiates `MWin.measureReal_locMoveFailAtClockWin_le` with **canonical** inputs:

* `bad := LocalGoodFamily.locSumBadCommon` (the `(locsum)` carrier at `CUmax`), whose display
  `hcc` is `LocalGoodFamily.commonLocsumFacts` — this is *carrier-free*: the `(loccoord)` display
  is a function of `locCoordGeom` membership, not of `recordCarrier`;
* `eb := Cerr · exf c L` from the measured `(locsum)` bound;
* `geom := ClockLocMove.locCoordGeom p m A hA r T L`, the `(loccoord)` window itself, so that
  `hcc`'s hypothesis `U ∈ geom s t` is *exactly* the geometric content of the display.

The outcome is a per-group bound with the exponential terms converted to the paper's profile
(`WindowLocal.exp_env_le_exf`, `WindowLocal.exp_maxgrowth_le_exp_env`), and the union over the
`2^N - 2` nonempty proper groups at `2^N` times that bound.

The geometry family is *group-dependent* (`locCoordGeom A` depends on the walker set), so the union
is taken over the group-indexed family `moveFailCanonAll` rather than one fixed `geom`.
-/
import Swarm.WindowLocal

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance LocGroupQ LocGroupWindow
open SwarmMarks SwarmLogRatio LocSumAct LocSumR1 LocOccCarrier LocOccAllStarts
open RecordDefect RecordoSupply SwarmRecordMeas SwarmRecordMeas.Actual
open ActualRecordFiltration LocGroupSimul LocMoveCompose LocMoveLocal LocMoveMart
open Loccoord Swarming.Enl ClockLocMove LocMovePaper LocalGoodFamily PaperBlock
open LocCoordGeomCarrier

namespace WindowMeas

variable {N : ℕ} [Nonempty (Fin N)]

/-- The profile rate produced by the quadratic envelope of `stepEnv`. -/
noncomputable def rateEnv (T N : ℕ) : ℝ := 1 / (256 * ((T : ℝ) + 3) * (16 + 162 * (N : ℝ)) ^ 2)

theorem rateEnv_pos (T N : ℕ) : 0 < rateEnv T N := by
  unfold rateEnv
  positivity

theorem rateEnv_nonneg (T N : ℕ) : 0 ≤ rateEnv T N := (rateEnv_pos T N).le

/-- **The measured windowed `(locmove)` failure event at the canonical `(loccoord)` geometry.**

For `1/2 < p < 1`, `1 ≤ m`, `2 ≤ L ≤ r/(T+3)`, an error coefficient `Cerr ≥ 1`, a `(locsum)` rate
`c > 0` together with the two facts of `LocalGoodFamily.commonLocsumFacts` at that `Cerr`, the
failure event of every nonempty proper group `A` — with the *canonical* window family
`locCoordGeom p m A hA` — is bounded by the two martingale windows converted to the profile plus
the measured `(locsum)` error:

    P (locMoveFailAtClockWin A …) ≤ 4·[(T+3)L+1]^2·exf (rateEnv T N) L + Cerr·exf c L .

No probability of a good event is assumed: `hbadLS` is a *proved* measure bound and `hccLS` is a
pointwise display off the measured set. -/
theorem measureReal_locMoveFailCanon_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 1 ≤ m) {T : ℕ} (hT : 1 ≤ T) {Cerr c : ℝ} (hCerr1 : 1 ≤ Cerr) (hc : 0 < c) {L₁ : ℕ}
    (hbadLS : ∀ L ≥ L₁, ∀ r : ℕ, (T + 3) * L ≤ r →
      (arrayMeasure N).real (LocalGoodFamily.locSumBadCommon (N := N) p m r T L)
        ≤ Cerr * LocalGoodAll.exf c L)
    (hccLS : ∀ L ≥ L₁, ∀ r : ℕ, (T + 3) * L ≤ r → ∀ U : Array N,
      U ∉ LocalGoodFamily.locSumBadCommon (N := N) p m r T L →
      ∀ (B : Finset (Fin N)) (hB : B.Nonempty) (s t : ℕ), s ≤ t →
      U ∈ ClockLocMove.locCoordGeom p m B hB r T L s t →
      Swarming.Group.average B
          (fun k => HA p m U t B (X p m U t k) - HA p m U s B (X p m U s k))
        ≤ LocalGoodFamily.Cmax (N := N) p m
            * (((runMaxA p m U hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
          + 3 * LocalGoodFamily.Cmax (N := N) p m * LocalGoodFamily.betaOf (N := N) p m T L Cerr) :
    ∀ L ≥ max L₁ 2, ∀ r : ℕ, (T + 3) * L ≤ r →
      ∀ (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty),
      (arrayMeasure N).real
          {U : Array N | MWin.locMoveFailAtClockWin p m A hA hAc r T L
            (RecClockLG.Bstar L) (LocalGoodFamily.Cmax (N := N) p m)
            (LocalGoodFamily.betaOf (N := N) p m T L Cerr)
            ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4))
            (ClockLocMove.locCoordGeom p m A hA r T L) (RecClockLG.Astar r T L) U}
        ≤ 4 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 * LocalGoodAll.exf (rateEnv T N) L
          + Cerr * LocalGoodAll.exf c L := by
  intro L hL r hr A hA hAc
  have hL₁ : L₁ ≤ L := le_trans (le_max_left L₁ 2) hL
  have hL2 : 2 ≤ L := le_trans (le_max_right L₁ 2) hL
  have hL1 : 1 ≤ L := by omega
  have hL0 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL1
  have hB : 0 < RecClockLG.Bstar L := RecClockLG.Bstar_pos hL1
  have hC1 : 1 ≤ LocalGoodFamily.Cmax (N := N) p m := LocalGoodFamily.one_le_Cmax p m
  have hγC : 1 ≤ LocMoveCompose.gammaRate p m A * LocalGoodFamily.Cmax (N := N) p m :=
    RecordGroupUniform.gammaRate_mul_common (N := N) hp0 hp1 hA
  have hε : 0 < (L : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hL0 _
  have hcc : ∀ s t : ℕ, s ≤ t → ∀ U : Array N,
      U ∉ LocalGoodFamily.locSumBadCommon (N := N) p m r T L →
      U ∈ ClockLocMove.locCoordGeom p m A hA r T L s t →
      Swarming.Group.average A
          (fun k => HA p m U t A (X p m U t k) - HA p m U s A (X p m U s k))
        ≤ LocalGoodFamily.Cmax (N := N) p m
            * (((runMaxA p m U hA t : ℤ) : ℝ) - ((Xmin p m U A hA s : ℤ) : ℝ))
          + 3 * LocalGoodFamily.Cmax (N := N) p m
              * LocalGoodFamily.betaOf (N := N) p m T L Cerr := by
    intro s t hst U hU hgeom
    exact hccLS L hL₁ r hr U hU A hA s t hst hgeom
  have hmain := MWin.measureReal_locMoveFailAtClockWin_le (N := N) (p := p) hp0 hp1 hm
    (A := A) hA hAc (T := T) (L := L) hL2 (r := r) hr
    (B := RecClockLG.Bstar L) (ε₁ := (L : ℝ) ^ ((3 : ℝ) / 4))
    (ε₂ := (L : ℝ) ^ ((3 : ℝ) / 4)) (C := LocalGoodFamily.Cmax (N := N) p m)
    (β := LocalGoodFamily.betaOf (N := N) p m T L Cerr) hB hC1 hγC hε hε
    (bad := LocalGoodFamily.locSumBadCommon (N := N) p m r T L)
    (eb := Cerr * LocalGoodAll.exf c L)
    (geom := ClockLocMove.locCoordGeom p m A hA r T L)
    (Aw := RecClockLG.Astar r T L) hcc (hbadLS L hL₁ r hr)
  -- convert the two exponential windows into the profile
  have e1 : 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2
        * Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
            (4 * (((T + 3) * L : ℕ) : ℝ)
              * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2))
      ≤ 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 * LocalGoodAll.exf (rateEnv T N) L := by
    apply mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact WindowLocal.exp_env_le_exf (N := N) hp0 hp1.le hT hL1
  have e2 : 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2
        * Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
            (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * RecClockLG.Bstar L) ^ 2))
      ≤ 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 * LocalGoodAll.exf (rateEnv T N) L := by
    have h := WindowLocal.exp_maxgrowth_le_exp_env (N := N) hp0 hp1.le (T := T) hL1
    have h2 : Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
            (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * RecClockLG.Bstar L) ^ 2))
        ≤ LocalGoodAll.exf (rateEnv T N) L := le_trans h
          (WindowLocal.exp_env_le_exf (N := N) hp0 hp1.le hT hL1)
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hsplit : 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2
        * Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
            (4 * (((T + 3) * L : ℕ) : ℝ)
              * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2))
      + 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2
        * Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
            (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * RecClockLG.Bstar L) ^ 2))
      + Cerr * LocalGoodAll.exf c L
      ≤ 4 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 * LocalGoodAll.exf (rateEnv T N) L
        + Cerr * LocalGoodAll.exf c L := by
    have h4 : (4 : ℝ) * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2
          * LocalGoodAll.exf (rateEnv T N) L
        = 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 * LocalGoodAll.exf (rateEnv T N) L
          + 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 * LocalGoodAll.exf (rateEnv T N) L := by
      ring
    linarith [e1, e2, h4]
  linarith [hmain, hsplit]

/-! ## 2. The simultaneous failure event over every nonempty proper group -/

/-- A nonempty proper group has nonempty complement. -/
theorem compl_nonempty_of_mem_properGroups {A : Finset (Fin N)}
    (hA : A ∈ Swarming.Enl.properGroups (N := N)) : Aᶜ.Nonempty := by
  rw [UniversalFamily.compl_nonempty_iff_ne_univ]
  exact (Swarming.Enl.mem_properGroups.mp hA).2

/-- The canonical-geometry failure event does not depend on the proofs of nonemptiness. -/
theorem locMoveFailCanon_congr (p : ℝ) (m : ℕ) {A : Finset (Fin N)} (hA hA' : A.Nonempty)
    (hAc hAc' : Aᶜ.Nonempty) (r T L : ℕ) (B C β ε₁ ε₂ : ℝ) (Aw : ℕ) (U : Array N) :
    MWin.locMoveFailAtClockWin p m A hA hAc r T L B C β ε₁ ε₂
        (ClockLocMove.locCoordGeom p m A hA r T L) Aw U
      ↔ MWin.locMoveFailAtClockWin p m A hA' hAc' r T L B C β ε₁ ε₂
        (ClockLocMove.locCoordGeom p m A hA' r T L) Aw U := by
  have h1 : hA = hA' := Subsingleton.elim _ _
  have h2 : hAc = hAc' := Subsingleton.elim _ _
  subst h1
  subst h2
  exact Iff.rfl

/-- **The simultaneous canonical-geometry `(locmove)` failure event** over every nonempty proper
group, each at its own `(loccoord)` window family. -/
noncomputable def moveFailCanonAll (p : ℝ) (m : ℕ) (r T L : ℕ) (B C β ε₁ ε₂ : ℝ) (Aw : ℕ) :
    Set (Array N) :=
  ⋃ A ∈ Swarming.Enl.properGroups (N := N),
    (if h : A ∈ Swarming.Enl.properGroups (N := N) then
      ({U : Array N | MWin.locMoveFailAtClockWin p m A
        (Swarming.Enl.mem_properGroups.mp h).1 (compl_nonempty_of_mem_properGroups h) r T L
        B C β ε₁ ε₂ (ClockLocMove.locCoordGeom p m A
          (Swarming.Enl.mem_properGroups.mp h).1 r T L) Aw U} : Set (Array N))
      else (∅ : Set (Array N)))

/-- **Avoiding the simultaneous event excludes the failure of every group** at the caller's own
proofs of nonemptiness. -/
theorem not_mem_locMoveFailCanon_of_not_mem_moveFailCanonAll {p : ℝ} {m r T L : ℕ}
    {B C β ε₁ ε₂ : ℝ} {Aw : ℕ} {U : Array N}
    (h : U ∉ moveFailCanonAll (N := N) p m r T L B C β ε₁ ε₂ Aw)
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) :
    ¬ MWin.locMoveFailAtClockWin p m A hA hAc r T L B C β ε₁ ε₂
      (ClockLocMove.locCoordGeom p m A hA r T L) Aw U := by
  intro hc
  have hne : A ≠ Finset.univ := by
    rw [← UniversalFamily.compl_nonempty_iff_ne_univ]
    exact hAc
  have hmem : A ∈ Swarming.Enl.properGroups (N := N) :=
    Swarming.Enl.mem_properGroups.mpr ⟨hA, hne⟩
  refine h (Set.mem_iUnion.mpr ⟨A, Set.mem_iUnion.mpr ⟨hmem, ?_⟩⟩)
  rw [dif_pos hmem]
  exact (locMoveFailCanon_congr p m hA (Swarming.Enl.mem_properGroups.mp hmem).1 hAc
    (compl_nonempty_of_mem_properGroups hmem) r T L B C β ε₁ ε₂ Aw U).mp hc

/-- **The measured bound of the simultaneous canonical event**, with the finite-union factor
`#properGroups ≤ 2^N`. -/
theorem measureReal_moveFailCanonAll_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 1 ≤ m) {T : ℕ} (hT : 1 ≤ T) {Cerr c : ℝ} (hCerr1 : 1 ≤ Cerr) (hc : 0 < c)
    {L₁ : ℕ}
    (hbadLS : ∀ L ≥ L₁, ∀ r : ℕ, (T + 3) * L ≤ r →
      (arrayMeasure N).real (LocalGoodFamily.locSumBadCommon (N := N) p m r T L)
        ≤ Cerr * LocalGoodAll.exf c L)
    (hccLS : ∀ L ≥ L₁, ∀ r : ℕ, (T + 3) * L ≤ r → ∀ U : Array N,
      U ∉ LocalGoodFamily.locSumBadCommon (N := N) p m r T L →
      ∀ (B : Finset (Fin N)) (hB : B.Nonempty) (s t : ℕ), s ≤ t →
      U ∈ ClockLocMove.locCoordGeom p m B hB r T L s t →
      Swarming.Group.average B
          (fun k => HA p m U t B (X p m U t k) - HA p m U s B (X p m U s k))
        ≤ LocalGoodFamily.Cmax (N := N) p m
            * (((runMaxA p m U hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
          + 3 * LocalGoodFamily.Cmax (N := N) p m * LocalGoodFamily.betaOf (N := N) p m T L Cerr) :
    ∀ L ≥ max L₁ 2, ∀ r : ℕ, (T + 3) * L ≤ r →
      (arrayMeasure N).real
          (moveFailCanonAll (N := N) p m r T L (RecClockLG.Bstar L)
            (LocalGoodFamily.Cmax (N := N) p m)
            (LocalGoodFamily.betaOf (N := N) p m T L Cerr)
            ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4)) (RecClockLG.Astar r T L))
        ≤ (2 : ℝ) ^ N * (4 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2
            * LocalGoodAll.exf (rateEnv T N) L + Cerr * LocalGoodAll.exf c L) := by
  intro L hL r hr
  have hper : ∀ (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty),
      (arrayMeasure N).real
        {U : Array N | MWin.locMoveFailAtClockWin p m A hA hAc r T L
          (RecClockLG.Bstar L) (LocalGoodFamily.Cmax (N := N) p m)
          (LocalGoodFamily.betaOf (N := N) p m T L Cerr)
          ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4))
          (ClockLocMove.locCoordGeom p m A hA r T L) (RecClockLG.Astar r T L) U}
        ≤ 4 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 * LocalGoodAll.exf (rateEnv T N) L
          + Cerr * LocalGoodAll.exf c L :=
    measureReal_locMoveFailCanon_le (N := N) hp0 hp1 hm hT hCerr1 hc hbadLS hccLS L hL r hr
  have hκ : 0 ≤ 4 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 * LocalGoodAll.exf (rateEnv T N) L
      + Cerr * LocalGoodAll.exf c L := by
    have h1 := WindowAbsorb.exf_pos (rateEnv T N) L
    have h2 := WindowAbsorb.exf_pos c L
    have : (0:ℝ) ≤ 4 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 := by positivity
    nlinarith
  have hcard : ((Swarming.Enl.properGroups (N := N)).card : ℝ) ≤ (2 : ℝ) ^ N := by
    have h := Swarming.Enl.card_properGroups_le (N := N)
    calc ((Swarming.Enl.properGroups (N := N)).card : ℝ) ≤ ((2 ^ N : ℕ) : ℝ) := by
          exact_mod_cast h
      _ = (2 : ℝ) ^ N := by push_cast; ring
  set κ : ℝ := 4 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 * LocalGoodAll.exf (rateEnv T N) L
    + Cerr * LocalGoodAll.exf c L with hκdef
  have hper' : ∀ A ∈ Swarming.Enl.properGroups (N := N),
      (arrayMeasure N).real
        (if h : A ∈ Swarming.Enl.properGroups (N := N) then
          ({U : Array N | MWin.locMoveFailAtClockWin p m A
            (Swarming.Enl.mem_properGroups.mp h).1 (compl_nonempty_of_mem_properGroups h) r T L
            (RecClockLG.Bstar L) (LocalGoodFamily.Cmax (N := N) p m)
            (LocalGoodFamily.betaOf (N := N) p m T L Cerr)
            ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4))
            (ClockLocMove.locCoordGeom p m A (Swarming.Enl.mem_properGroups.mp h).1 r T L)
            (RecClockLG.Astar r T L) U} : Set (Array N))
          else (∅ : Set (Array N))) ≤ κ := by
    intro A hA
    rw [dif_pos hA, hκdef]
    exact hper A (Swarming.Enl.mem_properGroups.mp hA).1 (compl_nonempty_of_mem_properGroups hA)
  have h1 : (arrayMeasure N).real
      (moveFailCanonAll (N := N) p m r T L (RecClockLG.Bstar L)
        (LocalGoodFamily.Cmax (N := N) p m)
        (LocalGoodFamily.betaOf (N := N) p m T L Cerr)
        ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4)) (RecClockLG.Astar r T L))
      ≤ ((Swarming.Enl.properGroups (N := N)).card : ℝ) * κ := by
    refine le_trans (measureReal_biUnion_finset_le (Swarming.Enl.properGroups (N := N))
      (fun A => if h : A ∈ Swarming.Enl.properGroups (N := N) then
        ({U : Array N | MWin.locMoveFailAtClockWin p m A
          (Swarming.Enl.mem_properGroups.mp h).1 (compl_nonempty_of_mem_properGroups h) r T L
          (RecClockLG.Bstar L) (LocalGoodFamily.Cmax (N := N) p m)
          (LocalGoodFamily.betaOf (N := N) p m T L Cerr)
          ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4))
          (ClockLocMove.locCoordGeom p m A (Swarming.Enl.mem_properGroups.mp h).1 r T L)
          (RecClockLG.Astar r T L) U} : Set (Array N))
        else (∅ : Set (Array N)))) ?_
    refine le_trans (Finset.sum_le_sum (g := fun _ => κ) ?_) ?_
    · exact hper'
    · rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : ((Swarming.Enl.properGroups (N := N)).card : ℝ) * κ ≤ (2 : ℝ) ^ N * κ :=
    mul_le_mul_of_nonneg_right hcard hκ
  exact le_trans h1 (by rw [hκdef] at h2 ⊢; exact h2)

end WindowMeas
