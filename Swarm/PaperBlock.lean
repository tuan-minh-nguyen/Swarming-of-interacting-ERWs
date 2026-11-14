/-
# The paper-local clauses of Proposition `local` for the actual trajectory,
as `JoinStep.LocalClauses` / `BlkCoin.BlockClauses` at the paper's constants

## What this file does

* It introduces the three actual objects of the paper's Proposition `local` on the *actual*
  interacting trajectory `U`:

    `Xa i n = X_n^i`,  `τa r = τ_r`,  `Hc A n x = ⌈H_n^A(x)⌉`,

  where `Hc` is the honest integer-valued translation of the paper's real-valued potential
  `H_n^A` (the tightness lane's `H : Finset ι → ℕ → ℤ → ℤ` is `ℤ`-valued, the martingale lane's
  `SepGroup.Model.HA` is `ℝ`-valued; `⌈·⌉` is the exact translation, and its two round-off
  losses `+1` per potential *difference* are proved to be re-absorbable).
* It proves the definitional bridge between the two lanes
  (`LocalFluid.runMaxI` vs `Swarming.Trajectory.runMax`, `Glue.sMin` vs `Loccoord.Xmin`,
   `Glue.sMaxM` vs `Swarming.Enl.runMaxA`, `Glue.Sep` vs `SepSet`, `Glue.Wst` vs `BlkCoin.Wpot`).
* It proves, **unconditionally off the single universal bad event `univBad`** on the record
  carrier, the paper's clauses in the exact field shapes of the tightness lane:
  `hmono`, `hunit`, `hcoord` (the literal single-time spatial `(loccoord)`),
  `wmove` (the paper's `(locmove)` at the `T`-free coefficient `paperC`, `+ C_T L^{3/4}`),
  and `group` (the paper's `(locgroup)` at the potential family `Jᶜ`);
* It bundles these into `BlkCoin.BlockClauses` at the common coefficient
  `Cfin = max paperC Cocc`, conditional on **two explicit premises**:
  `LocalFluid.LocOcc` at `Cfin`, and the `(locmove)` good-window content
  `MoveCarrier` (`ambGood`, `GoodW`, `GoodStep`).  The public martingale package
  derives the movement display from the latter via
  `LocMovePaperWindow.familyGood_locmove_paperWindow_good3`.

## Exact boundary

No probabilistic estimate is added or assumed beyond the public bound on `univBad`;
no `(nocoin)`/stationarity/invariance/start-law appears.  `GoodWinAllPairs` positivity is not
claimed.  The `(lococc)` field and `MoveCarrier` remain hypotheses of the final theorem,
not discharged conclusions.  In particular this is not yet a measured `PaperBadBlockProfile`,
a block estimate, $d_T$ tightness, or a common-velocity theorem.
-/
import Swarm.FamilyHeadlineNoGeom
import Swarm.UniversalFamily
import Swarm.LocMovePaper
import Swarm.PaperLocCoordFixed
import Swarm.OccPaperPointwise
import Swarm.EndpointHalving
import Swarm.CoinGen

noncomputable section

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance LocGroupQ LocGroupWindow
open SwarmMarks SwarmLogRatio LocSumAct LocSumR1 LocOccCarrier LocOccAllStarts
open LocOccCarrierAssembly SummedSlope.Model
open SepGroup RecordDefect RecordoSupply SwarmRecordMeas SwarmRecordMeas.Actual
open ActualRecordFiltration LocGroupSimul LocMoveCompose LocMoveLocal LocMoveMart
open Loccoord Swarming.Enl
open LocOccSingleWindow LocOccAllPairs LocOccSingleWindowAllPairs

namespace PaperBlock

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. The three actual objects and the integer potential -/

/-- The actual interacting positions, as a `ι → ℕ → ℤ` family. -/
abbrev Xa (p : ℝ) (m : ℕ) (U : Array N) : Fin N → ℕ → ℤ := fun i n => X p m U n i

/-- The actual record clock `τ_r`. -/
abbrev tauA (p : ℝ) (m : ℕ) (U : Array N) : ℕ → ℕ := fun r => recTimeA p m U r

/-- **The integer potential.**  The tightness lane's `H` is `ℤ → ℤ`-valued; the paper's
`H_n^A` (`SepGroup.Model.HA`) is real-valued.  This is the honest translation: the ceiling of
the real potential.  Its round-off is at most `+1` per *difference* (`Hc_sub_le`), and it is
exactly `⌈·⌉` of the paper's potential, not a rescaled or truncated surrogate. -/
def Hc (p : ℝ) (m : ℕ) (U : Array N) : Finset (Fin N) → ℕ → ℤ → ℤ :=
  fun A n x => ⌈HA p m U n A x⌉

theorem Hc_eq (p : ℝ) (m : ℕ) (U : Array N) (A : Finset (Fin N)) (n : ℕ) (x : ℤ) :
    Hc p m U A n x = ⌈HA p m U n A x⌉ := rfl

/-! ### 1.1 `runMaxI Xa = runMax` -/

/-- Each walker of the actual trajectory moves by exactly one site per step. -/
theorem Xa_step (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (n : ℕ) :
    |Xa p m U i (n + 1) - Xa p m U i n| = 1 := by
  have hstep := Swarming.Trajectory.pos_succ_eq_add_one_or_sub_one p m U i n
  simp only [Xa, SepGroup.Model.X_apply]
  rcases hstep with h | h
  · have h1 : (trajectory p m U (n + 1)).pos i - (trajectory p m U n).pos i = 1 := by omega
    rw [h1]; norm_num
  · have h1 : (trajectory p m U (n + 1)).pos i - (trajectory p m U n).pos i = -1 := by omega
    rw [h1]; norm_num

theorem runMax_mono (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) {n n' : ℕ} (hnn' : n ≤ n') :
    Swarming.Trajectory.runMax p m U j n ≤ Swarming.Trajectory.runMax p m U j n' := by
  unfold Swarming.Trajectory.runMax
  refine Finset.sup'_le _ _ (fun t ht => Finset.le_sup' (fun t => (trajectory p m U t).pos j) ?_)
  rw [Finset.mem_range] at ht ⊢
  omega

theorem le_runMaxI (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (n : ℕ) :
    Xa p m U i n ≤ LocalFluid.runMaxI (Xa p m U) i n := by
  cases n with
  | zero => rw [LocalFluid.runMaxI_zero]
  | succ k =>
      rw [LocalFluid.runMaxI_succ]
      exact le_max_right _ _

/-- **The recursive running maximum of the tightness lane is the paper's `M_n^i`.** -/
theorem runMaxI_eq (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (n : ℕ) :
    LocalFluid.runMaxI (Xa p m U) i n = Swarming.Trajectory.runMax p m U i n := by
  refine le_antisymm ?_ ?_
  · -- `runMaxI ≤ runMax`
    induction n with
    | zero =>
        rw [LocalFluid.runMaxI_zero]
        exact Swarming.Trajectory.le_runMax p m U i 0
    | succ k ih =>
        rw [LocalFluid.runMaxI_succ]
        refine max_le ?_ ?_
        · exact le_trans ih (runMax_mono p m U i (Nat.le_succ k))
        · exact Swarming.Trajectory.le_runMax p m U i (k + 1)
  · -- `runMax ≤ runMaxI`
    unfold Swarming.Trajectory.runMax
    refine Finset.sup'_le _ _ (fun t ht => ?_)
    rw [Finset.mem_range] at ht
    exact le_trans (le_runMaxI p m U i t)
      (LocalFluid.runMaxI_mono (Xa p m U) i (by omega))

/-! ### 1.2 `sMin`, `sMaxM` -/

theorem sMin_eq_Xmin (p : ℝ) (m : ℕ) (U : Array N) (A : Finset (Fin N)) (hA : A.Nonempty)
    (n : ℕ) :
    Glue.sMin (Xa p m U) A n = Xmin p m U A hA n := by
  unfold Glue.sMin Xmin
  rw [dif_pos hA]

theorem sMaxM_eq_runMaxA (p : ℝ) (m : ℕ) (U : Array N) (A : Finset (Fin N)) (hA : A.Nonempty)
    (n : ℕ) :
    Glue.sMaxM (Xa p m U) A n = runMaxA p m U hA n := by
  have h1 : Glue.sMaxM (Xa p m U) A n
      = A.sup' hA (fun i => LocalFluid.runMaxI (Xa p m U) i n) := by
    unfold Glue.sMaxM
    rw [dif_pos hA]
  have h2 : runMaxA p m U hA n
      = A.sup' hA (fun i => Swarming.Trajectory.runMax p m U i n) := rfl
  rw [h1, h2]
  exact Finset.sup'_congr hA rfl (fun i _ => runMaxI_eq p m U i n)

/-! ### 1.3 `Sep` vs `SepSet` -/

/-- On the record carrier every position in the paper's window is nonnegative. -/
theorem nonneg_of_carrier (p : ℝ) (m r L T : ℕ) (U : Array N)
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (hr : (T + 3) * L ≤ r) {n : ℕ} (h1 : recTimeA p m U r ≤ n)
    (h2 : n ≤ recTimeA p m U r + T * L) (i : Fin N) : 0 ≤ X p m U n i :=
  Glue.pos_nonneg (X := Xa p m U) (τ := tauA p m U)
    (LocCoordGeomCarrier.isRecord_recTimeA_of_carrier hcarr)
    (fun i n => Xa_step p m U i n)
    (LocCoordGeomCarrier.defect_le_of_carrier hcarr) h1 h2 hr

/-- `(sep)` in the tightness lane implies the martingale lane's `SepSet`, given nonnegativity of
all positions (which on the record carrier is `nonneg_of_carrier`). -/
theorem sepSet_of_sep (p : ℝ) (m n : ℕ) (I J : Finset (Fin N)) (U : Array N)
    (h0 : ∀ i : Fin N, 0 ≤ X p m U n i) (h : Glue.Sep (Xa p m U) I J n) :
    SepSet p m n I J U := by
  refine ⟨h0, fun i hi j hj => ?_⟩
  have h2 := h.2.2.2 i hi j hj
  simpa only [Xa, runMaxI_eq] using h2

/-- The martingale lane's `SepSet` implies the tightness lane's `(sep)`. -/
theorem sep_of_sepSet (p : ℝ) (m n : ℕ) (I J : Finset (Fin N)) (U : Array N)
    (h : SepSet p m n I J U) (hI : I.Nonempty) (hJ : J.Nonempty) :
    Glue.Sep (Xa p m U) I J n := by
  obtain ⟨h0, h2⟩ := h
  refine ⟨fun i _ => h0 i, hI, hJ, fun i hi j hj => ?_⟩
  have := h2 i hi j hj
  simpa only [Xa, runMaxI_eq] using this

/-! ## 2. The integer potential: monotonicity and unit increment -/

theorem ceil_sub_le {a b : ℝ} : ((⌈b⌉ : ℤ) : ℝ) - ((⌈a⌉ : ℤ) : ℝ) ≤ b - a + 1 := by
  have h1 : ((⌈b⌉ : ℤ) : ℝ) ≤ b + 1 := by
    have := Int.ceil_lt_add_one b
    linarith
  have h2 : a ≤ ((⌈a⌉ : ℤ) : ℝ) := Int.le_ceil a
  linarith

theorem ceil_sub_gt {a b : ℝ} : b - a - 1 < ((⌈b⌉ : ℤ) : ℝ) - ((⌈a⌉ : ℤ) : ℝ) := by
  have h1 : b ≤ ((⌈b⌉ : ℤ) : ℝ) := Int.le_ceil b
  have h2 : ((⌈a⌉ : ℤ) : ℝ) < a + 1 := Int.ceil_lt_add_one a
  linarith

/-- `H^w(x + d) ≥ H^w(x) + d` for `x ≥ 0`, `d : ℕ`. -/
theorem HZ_add_nat_ge {w : ℕ → ℝ} (hw0 : ∀ n, 0 < w n) (hw1 : ∀ n, w n ≤ 1) :
    ∀ (d : ℕ) (x : ℤ), 0 ≤ x → (d : ℝ) ≤ HZ w (x + (d : ℤ)) - HZ w x
  | 0, x, _ => by simp
  | d + 1, x, hx => by
      have ih := HZ_add_nat_ge hw0 hw1 d x hx
      have hpos : 0 ≤ x + (d : ℤ) := by
        have : (0 : ℤ) ≤ (d : ℤ) := by exact_mod_cast Nat.zero_le d
        linarith
      have hstep : HZ w (x + ((d + 1 : ℕ) : ℤ)) = HZ w (x + (d : ℤ)) + hfix w (x + (d : ℤ)).toNat := by
        rw [show x + ((d + 1 : ℕ) : ℤ) = (x + (d : ℤ)) + 1 by omega]
        exact HZ_add_one hpos
      have hone : (1 : ℝ) ≤ hfix w (x + (d : ℤ)).toNat := one_le_hfix w hw0 hw1 _
      rw [hstep]
      push_cast
      linarith

/-- The paper's `h^w ≥ 1`: the potential grows at least as fast as the identity. -/
theorem HZ_diff_ge {w : ℕ → ℝ} (hw0 : ∀ n, 0 < w n) (hw1 : ∀ n, w n ≤ 1) {x y : ℤ} (hxy : x ≤ y) :
    (y : ℝ) - (x : ℝ) ≤ HZ w y - HZ w x := by
  rcases lt_or_ge x 0 with hx | hx
  · rcases lt_or_ge y 0 with hy | hy
    · rw [HZ_neg hx, HZ_neg hy]
    · rw [HZ_neg hx, HZ_nonneg hy]
      have h1 : (y.toNat : ℝ) ≤ Hfix w y.toNat := Hfix_ge w hw0 hw1 y.toNat
      have h2 : (y.toNat : ℝ) = (y : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hy
      linarith
  · have hy : 0 ≤ y := le_trans hx hxy
    have hd : (((y - x).toNat : ℕ) : ℤ) = y - x := Int.toNat_of_nonneg (by omega)
    have hxy' : x + (((y - x).toNat : ℕ) : ℤ) = y := by omega
    have hsum := HZ_add_nat_ge hw0 hw1 (y - x).toNat x hx
    rw [hxy'] at hsum
    have hcast : (((y - x).toNat : ℕ) : ℝ) = (y : ℝ) - (x : ℝ) := by
      have h' := congrArg (fun z : ℤ => (z : ℝ)) hd
      push_cast at h'
      exact h'
    rw [hcast] at hsum
    exact hsum

theorem HA_diff_ge {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1) (m : ℕ) (U : Array N)
    (n : ℕ) (A : Finset (Fin N)) {x y : ℤ} (hxy : x ≤ y) :
    (y : ℝ) - (x : ℝ) ≤ HA p m U n A y - HA p m U n A x :=
  HZ_diff_ge (wA_pos p m U hp n A) (wA_le_one p m U hp1 n A) hxy

theorem Hc_mono (p : ℝ) (m : ℕ) (U : Array N) (hp : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1)
    (A : Finset (Fin N)) (n : ℕ) {x y : ℤ} (hxy : x ≤ y) :
    Hc p m U A n x ≤ Hc p m U A n y := by
  rw [Hc_eq, Hc_eq]
  exact Int.ceil_mono (HZ_mono (wA_pos p m U hp n A) (wA_le_one p m U hp1 n A) hxy)

theorem Hc_unit (p : ℝ) (m : ℕ) (U : Array N) (hp : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1)
    (A : Finset (Fin N)) (n : ℕ) {x y : ℤ} (hxy : x ≤ y) :
    y - x ≤ Hc p m U A n y - Hc p m U A n x := by
  rw [Hc_eq, Hc_eq]
  have h1 : ((y - x : ℤ) : ℝ) < (((⌈HA p m U n A y⌉ - ⌈HA p m U n A x⌉) + 1 : ℤ) : ℝ) := by
    push_cast
    have h2 := HA_diff_ge hp hp1 m U n A hxy
    have h3 := ceil_sub_gt (a := HA p m U n A x) (b := HA p m U n A y)
    linarith
  have h4 : (y - x : ℤ) < (⌈HA p m U n A y⌉ - ⌈HA p m U n A x⌉) + 1 := by exact_mod_cast h1
  exact Int.lt_add_one_iff.mp h4

/-! ### 2.1 The ceiling of a potential difference -/

theorem Hc_diff_le (p : ℝ) (m : ℕ) (U : Array N) (A : Finset (Fin N)) (n : ℕ) (a0 b0 : ℤ) :
    ((Hc p m U A n b0 - Hc p m U A n a0 : ℤ) : ℝ)
      ≤ HA p m U n A b0 - HA p m U n A a0 + 1 := by
  rw [Hc_eq, Hc_eq]
  push_cast
  have := ceil_sub_le (a := HA p m U n A a0) (b := HA p m U n A b0)
  linarith


/-! ## 3. `Wst`/`Wpot`/`WA`: the potential observables of the two lanes -/

/-- The tightness lane's `W` with potential family `I` is `BlkCoin.Wpot` at `A = I`. -/
theorem Wst_eq_Wpot (p : ℝ) (m : ℕ) (U : Array N)
    (H : Finset (Fin N) → ℕ → ℤ → ℤ) (A J : Finset (Fin N)) (n : ℕ) :
    Glue.Wst H (Xa p m U) A J n = BlkCoin.Wpot H (Xa p m U) A A J n := by
  unfold Glue.Wst BlkCoin.Wpot
  rfl

/-- **The integer potential costs at most `+1` in `W`.**  `W^{I,J}_n` built from `⌈H_n^{Jᶜ}⌉` is
at most the paper's real-valued `W^{I,J}_n` (`SepGroup.Model.WA`) plus one. -/
theorem Wpot_le_WA_add_one (p : ℝ) (m : ℕ) (U : Array N)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (n : ℕ) :
    BlkCoin.Wpot (Hc p m U) (Xa p m U) Jᶜ I J n ≤ WA p m U n I J hI hJ + 1 := by
  rw [BlkCoin.Wpot_of_nonempty hJ]
  unfold SepGroup.Model.WA
  rw [Swarming.Group.average, Swarming.Group.maximumOn]
  simp only [Hc_eq]
  have hcard : (0 : ℝ) < (I.card : ℝ) := by
    have h : 0 < I.card := Finset.card_pos.mpr hI
    exact_mod_cast h
  have hterm : ∀ i ∈ I,
      ((⌈HA p m U n Jᶜ (Xa p m U i n)⌉ : ℤ) : ℝ) ≤ HA p m U n Jᶜ (Xa p m U i n) + 1 := by
    intro i _
    have := Int.ceil_lt_add_one (HA p m U n Jᶜ (Xa p m U i n))
    linarith
  have hsum : (∑ i ∈ I, ((⌈HA p m U n Jᶜ (Xa p m U i n)⌉ : ℤ) : ℝ))
      ≤ (∑ i ∈ I, HA p m U n Jᶜ (Xa p m U i n)) + (I.card : ℝ) := by
    have h := Finset.sum_le_sum hterm
    have hsplit : (∑ i ∈ I, (HA p m U n Jᶜ (Xa p m U i n) + 1))
        = (∑ i ∈ I, HA p m U n Jᶜ (Xa p m U i n)) + (I.card : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    linarith
  have hsup : (J.sup' hJ (fun j => HA p m U n Jᶜ (Xa p m U j n)))
      ≤ ((J.sup' hJ (fun j => ⌈HA p m U n Jᶜ (Xa p m U j n)⌉) : ℤ) : ℝ) := by
    refine Finset.sup'_le hJ _ (fun j hj => ?_)
    have h1 : HA p m U n Jᶜ (Xa p m U j n) ≤ ((⌈HA p m U n Jᶜ (Xa p m U j n)⌉ : ℤ) : ℝ) :=
      Int.le_ceil _
    have h2 : ((⌈HA p m U n Jᶜ (Xa p m U j n)⌉ : ℤ) : ℝ)
        ≤ ((J.sup' hJ (fun j => ⌈HA p m U n Jᶜ (Xa p m U j n)⌉) : ℤ) : ℝ) := by
      exact_mod_cast Finset.le_sup' (fun j => ⌈HA p m U n Jᶜ (Xa p m U j n)⌉) hj
    linarith
  have h1 : (∑ i ∈ I, ((⌈HA p m U n Jᶜ (Xa p m U i n)⌉ : ℤ) : ℝ)) / (I.card : ℝ)
      ≤ (∑ i ∈ I, HA p m U n Jᶜ (Xa p m U i n)) / (I.card : ℝ) + 1 := by
    rw [div_add_one (ne_of_gt hcard)]
    exact div_le_div_of_nonneg_right hsum hcard.le
  linarith


/-- **The other side of the ceiling:** `W` built from `⌈H⌉` is at least the paper's real `W`
minus one.  Together with `Wpot_le_WA_add_one` this gives `|Wpot - WA| ≤ 1`, which is what a
*difference* of the observable needs. -/
theorem WA_sub_one_le_Wpot (p : ℝ) (m : ℕ) (U : Array N)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (n : ℕ) :
    WA p m U n I J hI hJ - 1 ≤ BlkCoin.Wpot (Hc p m U) (Xa p m U) Jᶜ I J n := by
  rw [BlkCoin.Wpot_of_nonempty hJ]
  unfold SepGroup.Model.WA
  rw [Swarming.Group.average, Swarming.Group.maximumOn]
  simp only [Hc_eq]
  have hcard : (0 : ℝ) < (I.card : ℝ) := by
    have h : 0 < I.card := Finset.card_pos.mpr hI
    exact_mod_cast h
  have hsum : (∑ i ∈ I, HA p m U n Jᶜ (Xa p m U i n))
      ≤ (∑ i ∈ I, ((⌈HA p m U n Jᶜ (Xa p m U i n)⌉ : ℤ) : ℝ)) :=
    Finset.sum_le_sum (fun i _ => Int.le_ceil _)
  have hdiv : (∑ i ∈ I, HA p m U n Jᶜ (Xa p m U i n)) / (I.card : ℝ)
      ≤ (∑ i ∈ I, ((⌈HA p m U n Jᶜ (Xa p m U i n)⌉ : ℤ) : ℝ)) / (I.card : ℝ) :=
    div_le_div_of_nonneg_right hsum hcard.le
  have hsup : ((J.sup' hJ (fun j => ⌈HA p m U n Jᶜ (Xa p m U j n)⌉) : ℤ) : ℝ)
      ≤ (J.sup' hJ (fun j => HA p m U n Jᶜ (Xa p m U j n))) + 1 := by
    obtain ⟨j0, hj0, hval⟩ :=
      Finset.exists_mem_eq_sup' hJ (fun j => ⌈HA p m U n Jᶜ (Xa p m U j n)⌉)
    rw [hval]
    have h1 : ((⌈HA p m U n Jᶜ (Xa p m U j0 n)⌉ : ℤ) : ℝ)
        ≤ HA p m U n Jᶜ (Xa p m U j0 n) + 1 := by
      have := Int.ceil_lt_add_one (HA p m U n Jᶜ (Xa p m U j0 n))
      linarith
    have h2 : HA p m U n Jᶜ (Xa p m U j0 n)
        ≤ (J.sup' hJ (fun j => HA p m U n Jᶜ (Xa p m U j n))) :=
      Finset.le_sup' (fun j => HA p m U n Jᶜ (Xa p m U j n)) hj0
    linarith
  linarith


/-! ## 4. The one error coefficient `C_T` -/

/-- **The single `T`-dependent constant `C_T`** of Proposition `local`, chosen as the maximum of
the constants required by the `(locmove)`, `(loccoord)` and `(locgroup)` displays.  It depends on
`N, m, p, T` only (and on the `(locsum)` error coefficient `Cerr`), while the coefficient `C` of
the displays — `LocMovePaper.paperC` — is independent of `T`. -/
noncomputable def CTtot (p : ℝ) (m T : ℕ) (Cerr : ℝ) : ℝ :=
  max (max (LocMovePaper.paperCT m Cerr + 2) (LocCoordPaper.CT p m T + 1)) 3

theorem paperCT_add_two_le_CTtot (p : ℝ) (m T : ℕ) (Cerr : ℝ) :
    LocMovePaper.paperCT m Cerr + 2 ≤ CTtot p m T Cerr :=
  le_trans (le_max_left _ _) (le_max_left _ _)

theorem CTpaper_add_one_le_CTtot (p : ℝ) (m T : ℕ) (Cerr : ℝ) :
    LocCoordPaper.CT p m T + 1 ≤ CTtot p m T Cerr :=
  le_trans (le_max_right _ _) (le_max_left _ _)

theorem two_le_CTtot (p : ℝ) (m T : ℕ) (Cerr : ℝ) : (2 : ℝ) ≤ CTtot p m T Cerr :=
  le_trans (by norm_num) (le_max_right _ _)

theorem three_le_CTtot (p : ℝ) (m T : ℕ) (Cerr : ℝ) : (3 : ℝ) ≤ CTtot p m T Cerr :=
  le_max_right _ _

theorem CTtot_pos (p : ℝ) (m T : ℕ) (Cerr : ℝ) : 0 < CTtot p m T Cerr :=
  lt_of_lt_of_le (by norm_num) (three_le_CTtot p m T Cerr)

/-- The paper's `T`-free coefficient dominates the `(loccoord)` coefficient `Cmax`. -/
theorem Cmax_le_paperC (p : ℝ) (m : ℕ) :
    LocalGoodFamily.Cmax (N := N) p m ≤ LocMovePaper.paperC (N := N) p m := by
  rw [LocMovePaper.paperC_eq]
  nlinarith [sq_nonneg (LocalGoodFamily.Cmax (N := N) p m - 1 / 2)]

/-- `L^{3/4} ≥ 1` for `L ≥ 1`. -/
theorem one_le_L34 {L : ℕ} (hL : 1 ≤ L) : (1 : ℝ) ≤ (L : ℝ) ^ ((3 : ℝ) / 4) := by
  have h1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  calc (1 : ℝ) = (1 : ℝ) ^ ((3 : ℝ) / 4) := (Real.one_rpow _).symm
    _ ≤ (L : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_le_rpow (by norm_num) h1 (by norm_num)

/-! ## 5. `(loccoord)` in the paper's literal single-time spatial shape -/

/-- **The paper's `(loccoord)`**, in exactly the shape of `JoinStep.LocalClauses.hcoord`, for the
integer potential `Hc`, at the `T`-free coefficient `paperC` and the single error coefficient
`CTtot`.

Inputs: the `(locsum)` pointwise content at the `(lococc)` window (the eighth clause of the public
family headline, `exists_famBad_and_good`), the record carrier, and the paper's range
`r - (T+2)L ≤ a0 ≤ b0 ≤ R_n^A`. -/
theorem hcoord_clause {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {T r L : ℕ} (hL : 1 ≤ L) (hr : (T + 3) * L ≤ r) {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (hsum : ∀ (j : Fin N) (a0 b0 : ℕ),
      LocOccCarrierAssembly.A0 r T L ≤ a0 →
      b0 ≤ LocOccCarrierAssembly.A0 r T L + LocOccCarrierAssembly.Lw T L → a0 ≤ b0 →
      ∑ x ∈ Finset.Ico a0 b0, (hof p (siteMarks p m U j) x) ^ 2
        ≤ 2 * LocOccSiteRate.Ccan p m * ((b0 : ℝ) - (a0 : ℝ))
          + 6 * LocOccSiteRate.Ccan p m * ((betaT (xOf (LocOccCarrierAssembly.Lw T L)) : ℕ) : ℝ))
    {Cerr : ℝ} (hCerr : 1 ≤ Cerr)
    (A : Finset (Fin N)) (hA : A.Nonempty) (n : ℕ)
    (h1 : tauA p m U r ≤ n) (h2 : n ≤ tauA p m U r + T * L)
    (a0 b0 : ℤ) (ha : (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ a0) (hab : a0 ≤ b0)
    (hb : b0 ≤ Glue.sMaxM (Xa p m U) A n) :
    ((Hc p m U A n b0 - Hc p m U A n a0 : ℤ) : ℝ)
      ≤ LocMovePaper.paperC (N := N) p m * ((b0 - a0 : ℤ) : ℝ)
        + CTtot p m T Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) := by
  -- `(T+2)L ≤ r`, hence `a0 ≥ 0`
  have hTL : (T + 2) * L ≤ r := le_trans (Nat.mul_le_mul_right L (by omega)) hr
  have ha0nn : (0 : ℤ) ≤ a0 := by
    have h1' : (((T + 2) * L : ℕ) : ℤ) ≤ (r : ℤ) := by exact_mod_cast hTL
    linarith
  have hb0nn : (0 : ℤ) ≤ b0 := le_trans ha0nn hab
  -- rewrite the upper end through `sMaxM = runMaxA`
  have hb' : ((b0.toNat : ℕ) : ℤ) ≤ runMaxA p m U hA n := by
    rw [← sMaxM_eq_runMaxA p m U A hA n]
    rw [Int.toNat_of_nonneg hb0nn]
    exact hb
  -- the three hypotheses of the paper-form `(loccoord)` in `ℕ`
  have hA0 : r - (T + 2) * L ≤ a0.toNat := by
    have h2' : (((r - (T + 2) * L : ℕ)) : ℤ) ≤ a0 := by
      rw [Nat.cast_sub hTL]; linarith
    have h2'' : (((r - (T + 2) * L : ℕ)) : ℤ) ≤ ((a0.toNat : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg ha0nn]; exact h2'
    exact_mod_cast h2''
  have hab' : a0.toNat ≤ b0.toNat := Int.toNat_le_toNat hab
  have hmain := PaperLocCoord.loccoord_fixed_of_locsum (N := N) hp0 hp1 hL hsum hcarr hA h1 h2
    hA0 hab' hb'
  -- turn the `.toNat` endpoints back into `a0`, `b0`
  have hcast_a : ((a0.toNat : ℕ) : ℤ) = a0 := Int.toNat_of_nonneg ha0nn
  have hcast_b : ((b0.toNat : ℕ) : ℤ) = b0 := Int.toNat_of_nonneg hb0nn
  rw [hcast_b, hcast_a] at hmain
  -- the ceiling round-off
  have hceil := Hc_diff_le p m U A n a0 b0
  -- the width, and the coefficient comparison
  have hdiff : (0 : ℝ) ≤ ((b0 - a0 : ℤ) : ℝ) := by
    have : (0 : ℤ) ≤ b0 - a0 := by omega
    exact_mod_cast this
  have hwidth : ((b0.toNat : ℕ) : ℝ) - ((a0.toNat : ℕ) : ℝ) = ((b0 - a0 : ℤ) : ℝ) := by
    have h1' : ((b0.toNat : ℕ) : ℝ) = (b0 : ℝ) := by exact_mod_cast hcast_b
    have h2' : ((a0.toNat : ℕ) : ℝ) = (a0 : ℝ) := by exact_mod_cast hcast_a
    rw [h1', h2']
    push_cast
    ring
  rw [hwidth] at hmain
  have hCcomp : LocalGoodFamily.Cmax (N := N) p m * ((b0 - a0 : ℤ) : ℝ)
      ≤ LocMovePaper.paperC (N := N) p m * ((b0 - a0 : ℤ) : ℝ) :=
    mul_le_mul_of_nonneg_right (Cmax_le_paperC p m) hdiff
  have hL34 : (1 : ℝ) ≤ (L : ℝ) ^ ((3 : ℝ) / 4) := one_le_L34 hL
  have hCT : LocCoordPaper.CT p m T * (L : ℝ) ^ ((3 : ℝ) / 4) + 1
      ≤ CTtot p m T Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) := by
    have h1' : (LocCoordPaper.CT p m T + 1) * (L : ℝ) ^ ((3 : ℝ) / 4)
        ≤ CTtot p m T Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_right (CTpaper_add_one_le_CTtot p m T Cerr)
        (Real.rpow_nonneg (by positivity) _)
    nlinarith [h1', hL34]
  linarith [hceil, hmain, hCcomp, hCT]


/-! ## 6. `(locgroup)` for every disjoint nonempty pair -/

/-- **The paper's `(locgroup)`** in exactly the shape of `BlkCoin.BlockClauses.group`, at the
potential family `Jᶜ = univ \ J`, from the public universal `(locgroup)` clause. -/
theorem group_clause {p : ℝ} {m r T L : ℕ} {U : Array N} (hL : 1 ≤ L)
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L) (hr : (T + 3) * L ≤ r)
    {Cerr : ℝ}
    (hgroup : ∀ (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty), Disjoint I J →
      ∀ s t : ℕ, recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
      (∀ u ∈ Finset.Ico s t, SepSet p m u I J U) →
      WA p m U t I J hI hJ - WA p m U s I J hI hJ ≤ (L : ℝ) ^ ((3 : ℝ) / 4)) :
    ∀ (I J : Finset (Fin N)), Disjoint I J → I.Nonempty → J.Nonempty →
      ∀ s t : ℕ, tauA p m U r ≤ s → s ≤ t → t ≤ tauA p m U r + T * L →
      (∀ u : ℕ, s ≤ u → u < t → Glue.Sep (Xa p m U) I J u) →
      BlkCoin.Wpot (Hc p m U) (Xa p m U) (Finset.univ \ J) I J t
        - BlkCoin.Wpot (Hc p m U) (Xa p m U) (Finset.univ \ J) I J s
        ≤ CTtot p m T Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) := by
  intro I J hdisj hI hJ s t hs hst ht hsep
  -- the two endpoints of the real-valued observable
  have hWt : BlkCoin.Wpot (Hc p m U) (Xa p m U) (Finset.univ \ J) I J t
      ≤ WA p m U t I J hI hJ + 1 := Wpot_le_WA_add_one p m U I J hI hJ t
  have hWs : WA p m U s I J hI hJ - 1
      ≤ BlkCoin.Wpot (Hc p m U) (Xa p m U) (Finset.univ \ J) I J s :=
    WA_sub_one_le_Wpot p m U I J hI hJ s
  -- `(sep)` on `[s,t)` gives `SepSet` there, using nonnegativity on the carrier
  have hsepSet : ∀ u ∈ Finset.Ico s t, SepSet p m u I J U := by
    intro u hu
    rw [Finset.mem_Ico] at hu
    have hτu : recTimeA p m U r ≤ u := le_trans hs hu.1
    have huT : u ≤ recTimeA p m U r + T * L :=
      le_trans (le_of_lt hu.2) (by rw [← show tauA p m U r = recTimeA p m U r from rfl]; exact ht)
    exact sepSet_of_sep p m u I J U
      (fun i => nonneg_of_carrier p m r L T U hcarr hr hτu huT i)
      (hsep u hu.1 hu.2)
  have hmain := hgroup I J hI hJ hdisj s t hs hst ht hsepSet
  have hL34 : (1 : ℝ) ≤ (L : ℝ) ^ ((3 : ℝ) / 4) := one_le_L34 hL
  have hCT : (L : ℝ) ^ ((3 : ℝ) / 4) + 2 ≤ CTtot p m T Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) := by
    have h3 : (3 : ℝ) ≤ CTtot p m T Cerr := three_le_CTtot p m T Cerr
    have h0 : (0 : ℝ) < (L : ℝ) ^ ((3 : ℝ) / 4) := lt_of_lt_of_le zero_lt_one hL34
    nlinarith
  linarith

/-! ## 7. `(locmove)` in the paper's shape, with the good-window carrier explicit -/

/-- **The paper's `(locmove)`** at the `T`-free coefficient `paperC` and the single error
coefficient `CTtot`, in the shape of `JoinStep.LocalClauses.wmove` at the integer potential
`Hc`, with the paper's window `[τ_r, τ_r+TL]` and the source's half-open time set `[s,t)`.

The three good-window requirements `ambGood`, `GoodW`, `GoodStep` of
`LocMovePaperWindow.familyGood_locmove_paperWindow_good3` are kept as explicit hypotheses: they
are the content of the paper's `(locmax)` inside `𝒢_{r,L,T}` that the public martingale package
carries, and nothing about their probability is claimed here.  `(sep)` itself is not a separate
hypothesis — it is a conjunct of `GoodW`. -/
theorem wmove_clause {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m r T L : ℕ} {U : Array N}
    (hL : 1 ≤ L) {Cerr : ℝ} {A : Finset (Fin N)} (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    (hmove : ∀ s t : ℕ, recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
      U ∈ ambGood p m hA (r : ℤ) T L →
      (∀ n ∈ Finset.Ico s t, GoodW p m n A Aᶜ hA (RecClockLG.Bstar L) U) →
      (∀ n ∈ Finset.Ico s t, GoodStep p m n Aᶜ (RecClockLG.Bstar L) U) →
      WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
        ≤ LocMoveCompose.locmoveRHS (N := N) p m A hA L (LocalGoodFamily.Cmax (N := N) p m)
            (LocalGoodFamily.betaOf (N := N) p m T L Cerr)
            ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4)) s t U)
    (s t : ℕ) (hs : tauA p m U r ≤ s) (hst : s ≤ t) (ht : t ≤ tauA p m U r + T * L)
    (hamb : U ∈ ambGood p m hA (r : ℤ) T L)
    (hW : ∀ n ∈ Finset.Ico s t, GoodW p m n A Aᶜ hA (RecClockLG.Bstar L) U)
    (hstep : ∀ n ∈ Finset.Ico s t, GoodStep p m n Aᶜ (RecClockLG.Bstar L) U) :
    Glue.Wst (Hc p m U) (Xa p m U) A (Finset.univ \ A) t
        - Glue.Wst (Hc p m U) (Xa p m U) A (Finset.univ \ A) s
      ≤ LocMovePaper.paperC (N := N) p m
          * (((Glue.sMaxM (Xa p m U) A s : ℤ) : ℝ) - ((Glue.sMin (Xa p m U) A s : ℤ) : ℝ))
        - ((t - s : ℕ) : ℝ) / LocMovePaper.paperC (N := N) p m
        + CTtot p m T Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) := by
  -- the martingale lane's paper-form display
  have hmain := hmove s t hs hst ht hamb hW hstep
  have hpaper := LocMovePaper.locmoveRHS_le_paperMoveRHS (N := N) hp0 hp1 (m := m) (T := T) A hA hL (Cerr := Cerr) s t U
  -- `Wst = Wpot`, and the potential family of `WA` is `(Aᶜ)ᶜ = A`
  have hAcA : (Aᶜ)ᶜ = A := by ext i; simp
  have hWt : Glue.Wst (Hc p m U) (Xa p m U) A (Finset.univ \ A) t
      ≤ WA p m U t A Aᶜ hA hAc + 1 := by
    rw [Wst_eq_Wpot]
    have h := Wpot_le_WA_add_one (N := N) p m U A Aᶜ hA hAc t
    rwa [hAcA] at h
  have hWs : WA p m U s A Aᶜ hA hAc - 1
      ≤ Glue.Wst (Hc p m U) (Xa p m U) A (Finset.univ \ A) s := by
    rw [Wst_eq_Wpot]
    have h := WA_sub_one_le_Wpot (N := N) p m U A Aᶜ hA hAc s
    rwa [hAcA] at h
  -- rewrite the paper's endpoints into the tightness lane's extrema
  have hmax : Glue.sMaxM (Xa p m U) A s = runMaxA p m U hA s := sMaxM_eq_runMaxA p m U A hA s
  have hmin : Glue.sMin (Xa p m U) A s = Xmin p m U A hA s := sMin_eq_Xmin p m U A hA s
  have hL34 : (1 : ℝ) ≤ (L : ℝ) ^ ((3 : ℝ) / 4) := one_le_L34 hL
  have hCT : LocMovePaper.paperCT m Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) + 2
      ≤ CTtot p m T Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) := by
    have h2 : LocMovePaper.paperCT m Cerr + 2 ≤ CTtot p m T Cerr :=
      paperCT_add_two_le_CTtot p m T Cerr
    have h0 : (0 : ℝ) < (L : ℝ) ^ ((3 : ℝ) / 4) := lt_of_lt_of_le zero_lt_one hL34
    calc LocMovePaper.paperCT m Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) + 2
        ≤ LocMovePaper.paperCT m Cerr * (L : ℝ) ^ ((3 : ℝ) / 4)
            + 2 * (L : ℝ) ^ ((3 : ℝ) / 4) := by linarith
      _ = (LocMovePaper.paperCT m Cerr + 2) * (L : ℝ) ^ ((3 : ℝ) / 4) := by ring
      _ ≤ CTtot p m T Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) := by
          exact mul_le_mul_of_nonneg_right h2 h0.le
  rw [hmax, hmin]
  unfold LocMovePaper.paperMoveRHS at hpaper
  linarith


/-! ## 8. The move carrier: the exact content of the paper's `(locmax)` window for `(locmove)` -/

/-- **The good-window carrier of the `(locmove)` display.**  This is the *only* clause of the
paper-local bundle that the public martingale package keeps as a hypothesis: on the record
window, `(locmove)` needs `ambGood` (the `Γ`-count lower bound), `GoodW` (the truncated potential
envelope) and `GoodStep` at every integer time of `[s,t)`.  In the paper these are supplied by
`(locmax)` inside `𝒢_{r,L,T}`; the public package
`LocMovePaperWindow.familyGood_locmove_paperWindow_good3` proves the display from exactly these
three and nothing else.  No positivity is claimed for this carrier. -/
def MoveCarrier (p : ℝ) (m r T L : ℕ) (U : Array N) : Prop :=
  ∀ (A : Finset (Fin N)) (hA : A.Nonempty), ∀ s t : ℕ,
    recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
    (∀ u : ℕ, s ≤ u → u < t → Glue.Sep (Xa p m U) A Aᶜ u) →
    U ∈ ambGood p m hA (r : ℤ) T L ∧
      (∀ n ∈ Finset.Ico s t, GoodW p m n A Aᶜ hA (RecClockLG.Bstar L) U) ∧
      (∀ n ∈ Finset.Ico s t, GoodStep p m n Aᶜ (RecClockLG.Bstar L) U)

/-! ## 10. The common coefficient `C` and the exact `BlockClauses` interface -/

/-- The explicit `(lococc)` coefficient of the public display `OccDisplayNull.occDisplayAllStarts`
at the canonical `(locsum)` constant `LocOccSiteRate.Ccan`. -/
noncomputable def Cocc (p : ℝ) (m : ℕ) : ℝ :=
  (2 * LocOccSiteRate.Ccan p m + Lc p m) + 2 * CJc p m * (2 * LocOccSiteRate.Ccan p m) + 1

/-- **The common coefficient `C`** of Proposition `local`.  The paper uses one `C(N,m,p)` in
`(loccoord)`, `(locmove)` and `(lococc)`.  The three displays are upper bounds whose right-hand
sides increase with `C`, so the honest common choice is the maximum of the constants the three
sources actually produce: `paperC = 1 + Cmax²` for `(loccoord)`/`(locmove)` and `Cocc` for
`(lococc)`.  `C` is a function of `N, m, p` only — not of `T`, not of `L`, not of the group. -/
noncomputable def Cfin (p : ℝ) (m : ℕ) : ℝ :=
  max (LocMovePaper.paperC (N := N) p m) (Cocc p m)

theorem paperC_le_Cfin (p : ℝ) (m : ℕ) :
    LocMovePaper.paperC (N := N) p m ≤ Cfin (N := N) p m := le_max_left _ _

theorem one_le_Cfin (p : ℝ) (m : ℕ) : (1 : ℝ) ≤ Cfin (N := N) p m :=
  le_trans (LocMovePaper.one_le_paperC (N := N) p m) (paperC_le_Cfin p m)

theorem Cfin_pos (p : ℝ) (m : ℕ) : 0 < Cfin (N := N) p m :=
  lt_of_lt_of_le zero_lt_one (one_le_Cfin p m)

theorem Cmax_le_Cfin (p : ℝ) (m : ℕ) :
    LocalGoodFamily.Cmax (N := N) p m ≤ Cfin (N := N) p m :=
  le_trans (Cmax_le_paperC p m) (paperC_le_Cfin p m)

/-- `(loccoord)` at the common coefficient `Cfin`. -/
theorem hcoord_clause_fin {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {T r L : ℕ} (hL : 1 ≤ L) (hr : (T + 3) * L ≤ r) {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (hsum : ∀ (j : Fin N) (a0 b0 : ℕ),
      LocOccCarrierAssembly.A0 r T L ≤ a0 →
      b0 ≤ LocOccCarrierAssembly.A0 r T L + LocOccCarrierAssembly.Lw T L → a0 ≤ b0 →
      ∑ x ∈ Finset.Ico a0 b0, (hof p (siteMarks p m U j) x) ^ 2
        ≤ 2 * LocOccSiteRate.Ccan p m * ((b0 : ℝ) - (a0 : ℝ))
          + 6 * LocOccSiteRate.Ccan p m * ((betaT (xOf (LocOccCarrierAssembly.Lw T L)) : ℕ) : ℝ))
    {Cerr : ℝ} (hCerr : 1 ≤ Cerr)
    (A : Finset (Fin N)) (hA : A.Nonempty) (n : ℕ)
    (h1 : tauA p m U r ≤ n) (h2 : n ≤ tauA p m U r + T * L)
    (a0 b0 : ℤ) (ha : (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ a0) (hab : a0 ≤ b0)
    (hb : b0 ≤ Glue.sMaxM (Xa p m U) A n) :
    ((Hc p m U A n b0 - Hc p m U A n a0 : ℤ) : ℝ)
      ≤ Cfin (N := N) p m * ((b0 - a0 : ℤ) : ℝ)
        + CTtot p m T Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) := by
  have h := hcoord_clause (N := N) hp0 hp1 hL hr hcarr hsum hCerr A hA n h1 h2 a0 b0 ha hab hb
  have hnn : (0 : ℝ) ≤ ((b0 - a0 : ℤ) : ℝ) := by
    have : (0 : ℤ) ≤ b0 - a0 := by omega
    exact_mod_cast this
  have hle : LocMovePaper.paperC (N := N) p m * ((b0 - a0 : ℤ) : ℝ)
      ≤ Cfin (N := N) p m * ((b0 - a0 : ℤ) : ℝ) :=
    mul_le_mul_of_nonneg_right (paperC_le_Cfin p m) hnn
  linarith


/-! ## 9. The paper-local bundle off the single universal bad event -/

/-- **Proposition `local`, in the tightness lane's clause shapes, off the single universal bad
event.**

One bad event (`UniversalFamily.univBad`), one exponential profile (`LocalGoodAll.exf`), the same
`Cerr`, `CT`, `cT`, `L₀` for all walkers and all groups, with the paper's error coefficient
`CTtot = C_T` and common coefficient `Cfin = max paperC Cocc` (`T`-free).  For every `L ≥ L₀`, every `r ≥ (T+3)L`,
every trajectory on the record carrier and off `univBad`:

* `hmono`, `hunit` — the potential `Hc = ⌈H_n^A⌉` is monotone and grows at least as fast as the
  identity (the paper's `h^w ≥ 1`);
* `hcoord` — the paper's literal `(loccoord)` `H_n^A(b0) - H_n^A(a0) ≤ C(b0-a0) + C_T L^{3/4}` at
  every nonempty `A`, every `n ∈ [τ_r, τ_r+TL]` and the paper's range `r-(T+2)L ≤ a0 ≤ b0 ≤ R_n^A`;
* `wmove` — the paper's `(locmove)` in the shape of `JoinStep.LocalClauses.wmove` at the same `C`
  and `C_T`, on `[s,t) ⊂ [τ_r, τ_r+TL]`, subject to the explicit `MoveCarrier`;
* `group` — the paper's `(locgroup)` for **every** disjoint nonempty `I J` at the potential family
  `Jᶜ`, in the shape of `BlkCoin.BlockClauses.group`.

The `(lococc)` field is the explicit hypothesis `hocc` at the common coefficient `Cfin`.
The coefficient transfer for `(locmove)` is proved from `paperC ≤ Cfin`, nonnegativity of
`R_s^A - min_A X_s`, and the reverse inequality for the reciprocal drift term.  Thus the
conclusion is genuinely `BlkCoin.BlockClauses` at one coefficient `Cfin`.  Neither `hocc` nor
`MoveCarrier` is derived here, and no positivity or measure estimate for either is asserted.
-/
theorem paper_local_clauses {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (hN : 2 ≤ N) {T : ℕ} (hT : 1 ≤ T) :
    ∃ Cerr : ℝ, 1 ≤ Cerr ∧ ∃ CT cT : ℝ, 0 < CT ∧ 0 < cT ∧ ∃ L₀ : ℕ,
      (∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
        (arrayMeasure N).real (UniversalFamily.univBad (N := N) p m Cerr r T L)
          ≤ CT * LocalGoodAll.exf cT L) ∧
      (∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r → ∀ U : Array N,
        U ∈ RecClockLG.recordCarrier (N := N) p m r L →
        U ∉ UniversalFamily.univBad (N := N) p m Cerr r T L →
        LocalFluid.LocOcc (Xa p m U) (tauA p m U)
            (Cfin (N := N) p m) (CTtot p m T Cerr) T L r →
        MoveCarrier p m r T L U →
        BlkCoin.BlockClauses (Xa p m U) (tauA p m U) (Hc p m U)
            (Cfin (N := N) p m) (CTtot p m T Cerr) T L r) := by
  obtain ⟨Cerr, hCerr1, CT, cT, hCT, hcT, L₀, hbound, hgood⟩ :=
    UniversalFamily.exists_universal_bad_and_good (N := N) hp0 hp1 hm hN hT
  refine ⟨Cerr, hCerr1, CT, cT, hCT, hcT, max L₀ 1, ?_, ?_⟩
  · intro L hL r hr
    exact hbound L (le_trans (le_max_left L₀ 1) hL) r hr
  · intro L hL r hr U hcarr hnot hocc hmove
    have hL₀ : L₀ ≤ L := le_trans (le_max_left L₀ 1) hL
    have hL1 : 1 ≤ L := le_trans (le_max_right L₀ 1) hL
    obtain ⟨-, -, -, -, -, -, hlocgroup, hsum⟩ := hgood L hL₀ r hr U hcarr hnot
    -- `hmono`, `hunit`
    have hmono : ∀ (A : Finset (Fin N)) (n : ℕ) {x y : ℤ}, x ≤ y →
        Hc p m U A n x ≤ Hc p m U A n y :=
      fun A n _ _ hxy => Hc_mono p m U (le_of_lt hp0) (le_of_lt hp1) A n hxy
    have hunit : ∀ (A : Finset (Fin N)) (n : ℕ) {x y : ℤ}, x ≤ y →
        y - x ≤ Hc p m U A n y - Hc p m U A n x :=
      fun A n _ _ hxy => Hc_unit p m U (le_of_lt hp0) (le_of_lt hp1) A n hxy
    -- `(loccoord)`
    have hcoord : ∀ (A : Finset (Fin N)) (n : ℕ), A.Nonempty → A ≠ Finset.univ →
        tauA p m U r ≤ n → n ≤ tauA p m U r + T * L → ∀ a0 b0 : ℤ,
        (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ a0 → a0 ≤ b0 →
        b0 ≤ Glue.sMaxM (Xa p m U) A n →
        ((Hc p m U A n b0 - Hc p m U A n a0 : ℤ) : ℝ)
          ≤ Cfin (N := N) p m * ((b0 - a0 : ℤ) : ℝ)
            + CTtot p m T Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) := by
      intro A n hA _ h1 h2 a0 b0 ha hab hb
      exact hcoord_clause_fin (N := N) hp0 hp1 hL1 hr hcarr hsum hCerr1 A hA n h1 h2 a0 b0 ha hab hb
    -- `(locmove)`
    have hwmove : ∀ (A : Finset (Fin N)) (s t : ℕ), A.Nonempty → A ≠ Finset.univ →
        tauA p m U r ≤ s → s ≤ t → t ≤ tauA p m U r + T * L →
        (∀ u : ℕ, s ≤ u → u < t → Glue.Sep (Xa p m U) A (Finset.univ \ A) u) →
        Glue.Wst (Hc p m U) (Xa p m U) A (Finset.univ \ A) t
            - Glue.Wst (Hc p m U) (Xa p m U) A (Finset.univ \ A) s
          ≤ Cfin (N := N) p m
              * (((Glue.sMaxM (Xa p m U) A s : ℤ) : ℝ) - ((Glue.sMin (Xa p m U) A s : ℤ) : ℝ))
            - ((t - s : ℕ) : ℝ) / Cfin (N := N) p m
            + CTtot p m T Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) := by
      intro A s t hAn hAn' hs hst ht hsep
      have hAc : Aᶜ.Nonempty := by
        rw [UniversalFamily.compl_nonempty_iff_ne_univ]; exact hAn'
      obtain ⟨hamb, hW, hstep⟩ := hmove A hAn s t hs hst ht hsep
      have hfamBad : U ∉ LocalGoodFamily.famBad (N := N) p m Cerr
          (UniversalFamily.moveAllFam (N := N)) UniversalFamily.moveAllFam_ne
          UniversalFamily.moveAllFam_co (UniversalFamily.grpAllFam (N := N))
          UniversalFamily.grpAllFam_I UniversalFamily.grpAllFam_J r T L := hnot
      have hpc := wmove_clause (N := N) hp0 hp1 hL1 hAn hAc
        (fun s t hs hst ht hamb hW hstep =>
          LocCoordGeomCarrier.familyGood_locmove_paperWindow_good3 (N := N) hcarr hr hfamBad A
            (UniversalFamily.mem_moveAllFam.mpr ⟨hAn, hAc⟩) s t hs hst ht hamb hW hstep)
        s t hs hst ht hamb hW hstep
      obtain ⟨i0, hi0⟩ := hAn
      have hspread : (0 : ℝ) ≤
          ((Glue.sMaxM (Xa p m U) A s : ℤ) : ℝ) - ((Glue.sMin (Xa p m U) A s : ℤ) : ℝ) := by
        have h5 : Glue.sMin (Xa p m U) A s ≤ Glue.sMaxM (Xa p m U) A s :=
          le_trans (Glue.sMin_le (X := Xa p m U) (S := A) (n := s) (i := i0) ⟨i0, hi0⟩ hi0)
            (le_trans (le_runMaxI p m U i0 s)
              (Glue.le_sMaxM (X := Xa p m U) (S := A) (n := s) (i := i0) ⟨i0, hi0⟩ hi0))
        have h6 : ((Glue.sMin (Xa p m U) A s : ℤ) : ℝ) ≤ ((Glue.sMaxM (Xa p m U) A s : ℤ) : ℝ) :=
          Int.cast_le.mpr h5
        linarith
      have hCpc : (0 : ℝ) < LocMovePaper.paperC (N := N) p m := LocMovePaper.paperC_pos (N := N) p m
      have hCmono := paperC_le_Cfin (N := N) p m
      have e1 : LocMovePaper.paperC (N := N) p m
            * (((Glue.sMaxM (Xa p m U) A s : ℤ) : ℝ) - ((Glue.sMin (Xa p m U) A s : ℤ) : ℝ))
          ≤ Cfin (N := N) p m
            * (((Glue.sMaxM (Xa p m U) A s : ℤ) : ℝ) - ((Glue.sMin (Xa p m U) A s : ℤ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hCmono hspread
      have e2 : ((t - s : ℕ) : ℝ) / Cfin (N := N) p m
          ≤ ((t - s : ℕ) : ℝ) / LocMovePaper.paperC (N := N) p m :=
        div_le_div_of_nonneg_left (by positivity) hCpc hCmono
      linarith
    exact ⟨⟨hmono, hunit, hcoord, hwmove, hocc⟩,
      fun I J hdisj hI hJ => group_clause hL1 hcarr hr hlocgroup I J hdisj hI hJ⟩


end PaperBlock


