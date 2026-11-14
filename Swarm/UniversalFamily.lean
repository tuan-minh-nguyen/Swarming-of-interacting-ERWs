/-
# The universal-family instantiation of the finite-family local-good theorem

## What this file is

`LocalGoodFamily.exists_famBad_and_good` measures one bad event `famBad` for an **arbitrary
finite** family of nonempty proper walker sets `moveFam` and an arbitrary finite family of
disjoint nonempty pairs `grpFam`, and off that event it extracts the paper's clauses for every
*element of those families*.  Proposition `local` of the paper quantifies over **all** nonempty
proper `A ⊆ [N]` and **all** disjoint nonempty `I, J`.

This file closes that quantifier by instantiating the theorem at the two universal families

* `moveAllFam  = {A : Finset (Fin N) | A.Nonempty ∧ Aᶜ.Nonempty}` (nonempty *proper* groups), and
* `grpAllFam   = {(I, J) : I.Nonempty ∧ J.Nonempty ∧ Disjoint I J}`,

discharging `hne`, `hco`, `hI`, `hJ`, `hdisj` by membership extraction, and then rewriting the
family conclusions from `A ∈ moveAllFam` / `q ∈ grpAllFam` into the paper's literal hypothesis
form `A.Nonempty`, `Aᶜ.Nonempty`, `Disjoint I J`.  The resulting bad event `univBad` is a
**single** set depending only on `N, m, p, T, L, r` (and the error coefficient), not on any
choice of family, and the constants are those of the fixed universal families, hence functions
of `N, m, p, T` alone (their cardinalities are bounded by `2^N` and `4^N`; see
`moveAllFam_card_le` / `grpAllFam_card_le`).

## Exact boundary

Nothing here is a new probabilistic estimate: it is the exact universal-instantiation step, and
every carrier of the family package (`recordCarrier`, `locmoveGood`, `locCoordGeom`, `SepSet`,
the `(locsum)` range content) remains an explicit hypothesis of the corresponding display; no
positivity or non-vacuity of `GoodWinAllPairs` is claimed.  `locmart` and `locgroup` are kept in
the shapes in which the family package exports them.
-/
import Swarm.LocalGoodFamily

noncomputable section

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance LocGroupQ LocGroupWindow
open SwarmMarks SwarmLogRatio LocSumAct LocSumR1 LocOccCarrier LocOccAllStarts
open LocOccCarrierAssembly SummedSlope.Model
open RecordDefect RecordoSupply SwarmRecordMeas SwarmRecordMeas.Actual
open ActualRecordFiltration LocGroupSimul LocMoveCompose LocMoveLocal LocMoveMart
open Loccoord Swarming.Enl
open LocOccSingleWindow LocOccAllPairs LocOccSingleWindowAllPairs

namespace UniversalFamily

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. The two universal families -/

/-- **All nonempty proper walker sets** `A ⊆ [N]`: the index set of display `(locmove)`. -/
noncomputable def moveAllFam : Finset (Finset (Fin N)) :=
  Finset.univ.filter (fun A : Finset (Fin N) => A.Nonempty ∧ Aᶜ.Nonempty)

/-- **All disjoint nonempty pairs**: the index set of display `(locgroup)`. -/
noncomputable def grpAllFam : Finset (Finset (Fin N) × Finset (Fin N)) :=
  Finset.univ.filter (fun q : Finset (Fin N) × Finset (Fin N) =>
    q.1.Nonempty ∧ q.2.Nonempty ∧ Disjoint q.1 q.2)

theorem mem_moveAllFam {A : Finset (Fin N)} :
    A ∈ moveAllFam (N := N) ↔ A.Nonempty ∧ Aᶜ.Nonempty := by
  simp [moveAllFam]

theorem mem_grpAllFam {q : Finset (Fin N) × Finset (Fin N)} :
    q ∈ grpAllFam (N := N) ↔ q.1.Nonempty ∧ q.2.Nonempty ∧ Disjoint q.1 q.2 := by
  simp [grpAllFam]

/-- The paper's word "proper" in the form used by the family package: `Aᶜ` is nonempty exactly
when `A` is not the whole walker set. -/
theorem compl_nonempty_iff_ne_univ (A : Finset (Fin N)) :
    Aᶜ.Nonempty ↔ A ≠ Finset.univ := by
  rw [Finset.nonempty_iff_ne_empty]
  exact not_congr (Finset.compl_eq_empty_iff A)

/-- The membership characterisation in the paper's own words: `A` is nonempty and proper. -/
theorem mem_moveAllFam' {A : Finset (Fin N)} :
    A ∈ moveAllFam (N := N) ↔ A.Nonempty ∧ A ≠ Finset.univ := by
  rw [mem_moveAllFam, compl_nonempty_iff_ne_univ]

theorem moveAllFam_ne : ∀ A ∈ moveAllFam (N := N), A.Nonempty :=
  fun A hA => (mem_moveAllFam.mp hA).1

theorem moveAllFam_co : ∀ A ∈ moveAllFam (N := N), Aᶜ.Nonempty :=
  fun A hA => (mem_moveAllFam.mp hA).2

theorem grpAllFam_I : ∀ q ∈ grpAllFam (N := N), q.1.Nonempty :=
  fun q hq => (mem_grpAllFam.mp hq).1

theorem grpAllFam_J : ∀ q ∈ grpAllFam (N := N), q.2.Nonempty :=
  fun q hq => (mem_grpAllFam.mp hq).2.1

theorem grpAllFam_disj : ∀ q ∈ grpAllFam (N := N), Disjoint q.1 q.2 :=
  fun q hq => (mem_grpAllFam.mp hq).2.2

/-! ### The families are nonempty when `N ≥ 2` (the instantiation is not vacuous) -/

theorem moveAllFam_nonempty (hN : 2 ≤ N) : (moveAllFam (N := N)).Nonempty := by
  refine ⟨{(⟨0, by omega⟩ : Fin N)}, mem_moveAllFam.mpr ⟨Finset.singleton_nonempty _, ?_⟩⟩
  rw [Finset.nonempty_iff_ne_empty]
  intro h
  have h1 : (⟨1, by omega⟩ : Fin N) ∈ ({(⟨0, by omega⟩ : Fin N)} : Finset (Fin N))ᶜ := by
    simp [Fin.ext_iff]
  rw [h] at h1
  exact absurd h1 (Finset.notMem_empty _)

theorem grpAllFam_nonempty (hN : 2 ≤ N) : (grpAllFam (N := N)).Nonempty := by
  refine ⟨({(⟨0, by omega⟩ : Fin N)}, {(⟨1, by omega⟩ : Fin N)}), ?_⟩
  rw [mem_grpAllFam]
  refine ⟨Finset.singleton_nonempty _, Finset.singleton_nonempty _, ?_⟩
  rw [Finset.disjoint_singleton]
  simp [Fin.ext_iff]

/-! ### The family sizes are bounded by functions of `N` alone -/

/-- The move family has at most `2^N` members: the constants of the instantiated theorem are
therefore functions of `N, m, p, T` only, never of a chosen family. -/
theorem moveAllFam_card_le : (moveAllFam (N := N)).card ≤ 2 ^ N := by
  have h1 : (moveAllFam (N := N)).card ≤ (Finset.univ : Finset (Finset (Fin N))).card :=
    Finset.card_filter_le _ _
  rw [show (Finset.univ : Finset (Finset (Fin N))).card = Fintype.card (Finset (Fin N)) from rfl,
    Fintype.card_finset, Fintype.card_fin] at h1
  exact h1

/-- The pair family has at most `4^N` members. -/
theorem grpAllFam_card_le : (grpAllFam (N := N)).card ≤ 4 ^ N := by
  have h1 : (grpAllFam (N := N)).card
      ≤ (Finset.univ : Finset (Finset (Fin N) × Finset (Fin N))).card :=
    Finset.card_filter_le _ _
  rw [show (Finset.univ : Finset (Finset (Fin N) × Finset (Fin N))).card
      = Fintype.card (Finset (Fin N) × Finset (Fin N)) from rfl,
    Fintype.card_prod, Fintype.card_finset, Fintype.card_fin] at h1
  calc (grpAllFam (N := N)).card ≤ 2 ^ N * 2 ^ N := h1
    _ = 4 ^ N := by rw [← mul_pow]; norm_num

/-! ## 2. The single universal bad event -/

/-- **The universal bad event.**  `famBad` of the family package at the two universal families:
one set of trajectories on which *some* group of *some* size has failed, so that off it every
nonempty proper `A` and every disjoint nonempty pair satisfies its display.  It depends on
`N, m, p, T, L, r` (and the error coefficient) only. -/
noncomputable def univBad (p : ℝ) (m : ℕ) (Cerr : ℝ) (r T L : ℕ) : Set (Array N) :=
  LocalGoodFamily.famBad (N := N) p m Cerr (moveAllFam (N := N)) moveAllFam_ne moveAllFam_co
    (grpAllFam (N := N)) grpAllFam_I grpAllFam_J r T L

/-- `moveBadCommon` does not depend on the proof terms of nonemptiness/properness. -/
theorem moveBadCommon_congr {p : ℝ} {m : ℕ} {Cerr : ℝ} {A : Finset (Fin N)}
    (hA hA' : A.Nonempty) (hAc hAc' : Aᶜ.Nonempty) (r T L : ℕ) :
    LocalGoodFamily.moveBadCommon (N := N) p m Cerr A hA hAc r T L
      = LocalGoodFamily.moveBadCommon (N := N) p m Cerr A hA' hAc' r T L := by
  rw [Subsingleton.elim hA hA', Subsingleton.elim hAc hAc']

/-- `pairBad` does not depend on the proof terms of nonemptiness. -/
theorem pairBad_congr {p : ℝ} {m : ℕ} {I J : Finset (Fin N)}
    (hI hI' : I.Nonempty) (hJ hJ' : J.Nonempty) (r T L : ℕ) :
    LocalGoodFamily.pairBad (N := N) p m I J hI hJ r T L
      = LocalGoodFamily.pairBad (N := N) p m I J hI' hJ' r T L := by
  rw [Subsingleton.elim hI hI', Subsingleton.elim hJ hJ']

/-- Off the universal bad event, every nonempty proper `A` has its `(locmove)` display: the
membership form the family package exports. -/
theorem not_mem_univBad_move {p : ℝ} {m : ℕ} {Cerr : ℝ} {r T L : ℕ} {U : Array N}
    (h : U ∉ univBad (N := N) p m Cerr r T L) :
    U ∉ LocalGoodFamily.famMovePart (N := N) p m Cerr (moveAllFam (N := N))
      moveAllFam_ne moveAllFam_co r T L :=
  (LocalGoodFamily.not_mem_famBad h).1.2

/-- Off the universal bad event, every disjoint nonempty pair has its `(locgroup)` display. -/
theorem not_mem_univBad_pair {p : ℝ} {m : ℕ} {Cerr : ℝ} {r T L : ℕ} {U : Array N}
    (h : U ∉ univBad (N := N) p m Cerr r T L) :
    U ∉ LocalGoodFamily.famPairPart (N := N) p m (grpAllFam (N := N))
      grpAllFam_I grpAllFam_J r T L :=
  (LocalGoodFamily.not_mem_famBad h).2

/-- **The paper-form `(locmove)` failure set of one nonempty proper `A` is avoided.**  This is the
usable form of `not_mem_univBad_move`: the family package's proof arguments are replaced by the
caller's `A.Nonempty`, `Aᶜ.Nonempty`. -/
theorem not_mem_univBad_moveBad {p : ℝ} {m : ℕ} {Cerr : ℝ} {r T L : ℕ} {U : Array N}
    (h : U ∉ univBad (N := N) p m Cerr r T L)
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) :
    U ∉ LocalGoodFamily.moveBadCommon (N := N) p m Cerr A hA hAc r T L := by
  intro hc
  have hmem : A ∈ moveAllFam (N := N) := mem_moveAllFam.mpr ⟨hA, hAc⟩
  refine LocalGoodFamily.not_mem_moveBadCommon (not_mem_univBad_move h) A hmem ?_
  rwa [moveBadCommon_congr hA (moveAllFam_ne A hmem) hAc (moveAllFam_co A hmem) r T L]

/-- **The paper-form `(locgroup)` failure set of one disjoint nonempty pair is avoided.** -/
theorem not_mem_univBad_pairBad {p : ℝ} {m : ℕ} {Cerr : ℝ} {r T L : ℕ} {U : Array N}
    (h : U ∉ univBad (N := N) p m Cerr r T L)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hdisj : Disjoint I J) :
    U ∉ LocalGoodFamily.pairBad (N := N) p m I J hI hJ r T L := by
  intro hc
  have hmem : (I, J) ∈ grpAllFam (N := N) := mem_grpAllFam.mpr ⟨hI, hJ, hdisj⟩
  refine LocalGoodFamily.not_mem_pairBad (not_mem_univBad_pair h) (I, J) hmem ?_
  rwa [pairBad_congr hI (grpAllFam_I (I, J) hmem) hJ (grpAllFam_J (I, J) hmem) r T L]

/-- The typeclass instance needed by every statement here follows from `2 ≤ N`; stated so that
the theorems can be applied with only the paper's hypothesis `N ≥ 2`. -/
theorem nonempty_fin_of_two_le {N : ℕ} (hN : 2 ≤ N) : Nonempty (Fin N) :=
  ⟨⟨0, by omega⟩⟩

/-! ## 3. The measure bound for the single universal bad event -/

/-- **The measured bound of the universal bad event**, with the six countably many
group-independent components charged once and the `2^N - 2` move clauses and the `4^N`-bounded
pair clauses charged through the fixed families.  The constants are those obtained at the two
universal families, i.e. they are functions of `N, m, p, T`. -/
theorem exists_univBad_bound {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (hN : 2 ≤ N) {T : ℕ} (hT : 1 ≤ T) :
    ∃ Cerr CT cT : ℝ, 1 ≤ Cerr ∧ 0 < CT ∧ 0 < cT ∧ ∃ L₀ : ℕ,
      ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
        (arrayMeasure N).real (univBad (N := N) p m Cerr r T L)
          ≤ CT * LocalGoodAll.exf cT L := by
  obtain ⟨Cerr, hCerr1, ⟨CT, cT, hCT, hcT, L₀, hbound⟩, _⟩ :=
    LocalGoodFamily.exists_famBad_and_good (N := N) hp0 hp1 hm hT hN
      (moveAllFam (N := N)) moveAllFam_ne moveAllFam_co
      (grpAllFam (N := N)) grpAllFam_I grpAllFam_J grpAllFam_disj
  exact ⟨Cerr, CT, cT, hCerr1, hCT, hcT, L₀, hbound⟩

/-! ## 4. The paper-form universal theorem -/

/-- **Proposition `local`, universal-family form.**

For `1/2 < p < 1`, `2 ≤ m`, `2 ≤ N` and every `T ≥ 1` there are an error coefficient
`Cerr ≥ 1`, constants `CT, cT > 0` and thresholds `L₀`, all functions of `N, m, p, T` only
(they are the constants of the two fixed universal families), such that for every `L ≥ L₀`,
every `r ≥ (T+3)L` and every trajectory `U` on the paper's carrier `recordCarrier` that lies off
the **single** universal bad event `univBad`:

* the forward-potential support holds for every walker and every truncation;
* `(locmart)` holds at the actual record clock;
* `(locmove)` holds at the group-independent coefficient `Cmax` for **every nonempty proper**
  walker set `A`, on every window of the record interval on which the paper's window hypotheses
  `locmoveGood` and the geometric window `locCoordGeom` hold;
* `(loccoord)` holds for **every nonempty** group `B` at the same coefficient and error;
* `(lococc)` holds as the literal pointwise occupation display at the actual record fibre `τ_r`;
* the `GoodWinAllPairs` fibre event holds for every band member;
* `(locgroup)` holds for **every pair of disjoint nonempty** sets `I, J`;
* the `(locsum)` pointwise content holds on the `(lococc)` window.

The carriers `SepSet`, `locmoveGood`, `locCoordGeom` and the `(locsum)` range content are the
paper's own window hypotheses and remain explicit, exactly as in the finite-family package. -/
theorem exists_universal_bad_and_good {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) {T : ℕ} (hT : 1 ≤ T) :
    ∃ Cerr : ℝ, 1 ≤ Cerr ∧ ∃ CT cT : ℝ, 0 < CT ∧ 0 < cT ∧ ∃ L₀ : ℕ,
      (∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
        (arrayMeasure N).real (univBad (N := N) p m Cerr r T L)
          ≤ CT * LocalGoodAll.exf cT L) ∧
      (∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r → ∀ U : Array N,
        U ∈ RecClockLG.recordCarrier (N := N) p m r L →
        U ∉ univBad (N := N) p m Cerr r T L →
        (∀ j : Fin N, ∀ u : ℕ,
            BddAbove (Set.range fun n' => Gtrunc p (siteMarks p m U j) n' (u + 1))) ∧
          U ∈ RecordClock.locMartGood (N := N) p m r T L ∧
          (∀ (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty), ∀ s t : ℕ,
            recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + (T + 3) * L →
            locmoveGood p m A hA (r : ℤ) T L (RecClockLG.Bstar L) (recTimeA p m U r) s t U →
            U ∈ ClockLocMove.locCoordGeom p m A hA r T L s t →
            WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
              ≤ locmoveRHS (N := N) p m A hA L (LocalGoodFamily.Cmax (N := N) p m)
                  (LocalGoodFamily.betaOf (N := N) p m T L Cerr)
                  ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4)) s t U) ∧
          (∀ (B : Finset (Fin N)) (hB : B.Nonempty) (s t : ℕ), s ≤ t →
            U ∈ ClockLocMove.locCoordGeom p m B hB r T L s t →
            Swarming.Group.average B
                (fun k => HA p m U t B (X p m U t k) - HA p m U s B (X p m U s k))
              ≤ LocalGoodFamily.Cmax (N := N) p m
                  * (((runMaxA p m U hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
                + Cerr * (L : ℝ) ^ ((3 : ℝ) / 4)) ∧
          OccDisplayNull.occFace (N := N) p m (LocOccSiteRate.Ccan p m) r T L
            (recTimeA p m U r) U ∧
          (∀ s0 : ℕ, U ∈ LocOccFibreSum.band p m r L s0 →
            U ∈ LocOccSingleWindowAllPairs.GoodWinAllPairs (N := N) p m
              (LocOccSiteRate.Ccan p m) r T L s0) ∧
          (∀ (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty), Disjoint I J →
            ∀ s t : ℕ, recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
            (∀ u ∈ Finset.Ico s t, SepSet p m u I J U) →
            WA p m U t I J hI hJ - WA p m U s I J hI hJ ≤ (L : ℝ) ^ ((3 : ℝ) / 4)) ∧
          (∀ j : Fin N, ∀ a0 b0 : ℕ,
            LocOccCarrierAssembly.A0 r T L ≤ a0 →
            b0 ≤ LocOccCarrierAssembly.A0 r T L + LocOccCarrierAssembly.Lw T L → a0 ≤ b0 →
            ∑ x ∈ Finset.Ico a0 b0, (hof p (siteMarks p m U j) x) ^ 2
              ≤ 2 * LocOccSiteRate.Ccan p m * ((b0 : ℝ) - (a0 : ℝ))
                + 6 * LocOccSiteRate.Ccan p m
                  * ((betaT (xOf (LocOccCarrierAssembly.Lw T L)) : ℕ) : ℝ))) := by
  obtain ⟨Cerr, hCerr1, ⟨CT, cT, hCT, hcT, Lb, hbound⟩, Lg, hgood⟩ :=
    LocalGoodFamily.exists_famBad_and_good (N := N) hp0 hp1 hm hT hN
      (moveAllFam (N := N)) moveAllFam_ne moveAllFam_co
      (grpAllFam (N := N)) grpAllFam_I grpAllFam_J grpAllFam_disj
  refine ⟨Cerr, hCerr1, CT, cT, hCT, hcT, max Lb Lg, ?_, ?_⟩
  · intro L hL r hr
    exact hbound L (le_trans (le_max_left Lb Lg) hL) r hr
  · intro L hL r hr U hcarr hnot
    have hLg : Lg ≤ L := le_trans (le_max_right Lb Lg) hL
    obtain ⟨hpot, hlocmart, hmove, hcoord, hocc, hgoodwin, hgroup, hsum⟩ :=
      hgood L hLg r hr U hcarr hnot
    refine ⟨hpot, hlocmart, ?_, hcoord, hocc, hgoodwin, ?_, hsum⟩
    · -- `(locmove)` for every nonempty proper `A`
      intro A hA hAc s t hs hst htK hmg hgeom
      have hmem : A ∈ moveAllFam (N := N) := mem_moveAllFam.mpr ⟨hA, hAc⟩
      have hfam := hmove A hmem s t hs hst htK
      rw [show moveAllFam_ne A hmem = hA from Subsingleton.elim _ _,
        show moveAllFam_co A hmem = hAc from Subsingleton.elim _ _] at hfam
      exact hfam hmg hgeom
    · -- `(locgroup)` for every disjoint nonempty pair
      intro I J hI hJ hdisj s t hs hst htK hsep
      have hmem : (I, J) ∈ grpAllFam (N := N) := mem_grpAllFam.mpr ⟨hI, hJ, hdisj⟩
      have hfam := hgroup (I, J) hmem s t hs hst htK hsep
      rw [show grpAllFam_I (I, J) hmem = hI from Subsingleton.elim _ _,
        show grpAllFam_J (I, J) hmem = hJ from Subsingleton.elim _ _] at hfam
      exact hfam

/-! ## 5. The universal bad event contains every finite-family bad event -/

/-- Every finite family of nonempty proper walker sets has its `(locmove)` bad part inside the
universal one. -/
theorem famMovePart_subset (p : ℝ) (m : ℕ) (Cerr : ℝ)
    (moveFam : Finset (Finset (Fin N))) (hne : ∀ A ∈ moveFam, A.Nonempty)
    (hco : ∀ A ∈ moveFam, Aᶜ.Nonempty) (r T L : ℕ) :
    LocalGoodFamily.famMovePart (N := N) p m Cerr moveFam hne hco r T L
      ⊆ LocalGoodFamily.famMovePart (N := N) p m Cerr (moveAllFam (N := N))
          moveAllFam_ne moveAllFam_co r T L := by
  intro U hU
  simp only [LocalGoodFamily.famMovePart, Set.mem_iUnion] at hU ⊢
  obtain ⟨A, hA, hUA⟩ := hU
  have hmem : A ∈ moveAllFam (N := N) := mem_moveAllFam.mpr ⟨hne A hA, hco A hA⟩
  refine ⟨A, hmem, ?_⟩
  rw [dif_pos hA] at hUA
  rw [dif_pos hmem]
  rw [moveBadCommon_congr (hne A hA) (moveAllFam_ne A hmem) (hco A hA)
    (moveAllFam_co A hmem) r T L]
  exact hUA

/-- Every finite family of disjoint nonempty pairs has its `(locgroup)` bad part inside the
universal one. -/
theorem famPairPart_subset (p : ℝ) (m : ℕ)
    (grpFam : Finset (Finset (Fin N) × Finset (Fin N)))
    (hI : ∀ q ∈ grpFam, q.1.Nonempty) (hJ : ∀ q ∈ grpFam, q.2.Nonempty)
    (hdisj : ∀ q ∈ grpFam, Disjoint q.1 q.2) (r T L : ℕ) :
    LocalGoodFamily.famPairPart (N := N) p m grpFam hI hJ r T L
      ⊆ LocalGoodFamily.famPairPart (N := N) p m (grpAllFam (N := N))
          grpAllFam_I grpAllFam_J r T L := by
  intro U hU
  simp only [LocalGoodFamily.famPairPart, Set.mem_iUnion] at hU ⊢
  obtain ⟨q, hq, hUq⟩ := hU
  have hmem : q ∈ grpAllFam (N := N) :=
    mem_grpAllFam.mpr ⟨hI q hq, hJ q hq, hdisj q hq⟩
  refine ⟨q, hmem, ?_⟩
  rw [dif_pos hq] at hUq
  rw [dif_pos hmem]
  rw [pairBad_congr (hI q hq) (grpAllFam_I q hmem) (hJ q hq) (grpAllFam_J q hmem) r T L]
  exact hUq

/-- **The single universal bad event dominates every finite-family bad event.**  Hence a bound
on `univBad` (or nullity of it) covers simultaneously every nonempty proper group and every
disjoint nonempty pair — no family choice remains. -/
theorem famBad_subset_univBad {p : ℝ} {m : ℕ} {Cerr : ℝ} {r T L : ℕ}
    (moveFam : Finset (Finset (Fin N))) (hne : ∀ A ∈ moveFam, A.Nonempty)
    (hco : ∀ A ∈ moveFam, Aᶜ.Nonempty)
    (grpFam : Finset (Finset (Fin N) × Finset (Fin N)))
    (hI : ∀ q ∈ grpFam, q.1.Nonempty) (hJ : ∀ q ∈ grpFam, q.2.Nonempty)
    (hdisj : ∀ q ∈ grpFam, Disjoint q.1 q.2) :
    LocalGoodFamily.famBad (N := N) p m Cerr moveFam hne hco grpFam hI hJ r T L
      ⊆ univBad (N := N) p m Cerr r T L := by
  intro U hU
  simp only [LocalGoodFamily.famBad, univBad, Set.mem_union] at hU ⊢
  rcases hU with (⟨h11 | h12⟩ | h2)
  · exact Or.inl (Or.inl h11)
  · exact Or.inl (Or.inr (famMovePart_subset p m Cerr moveFam hne hco r T L h12))
  · exact Or.inr (famPairPart_subset p m grpFam hI hJ hdisj r T L h2)

end UniversalFamily
