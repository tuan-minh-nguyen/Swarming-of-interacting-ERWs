/-
# The windowed move carrier: `GoodStep` from the level-window envelope alone

`MoveStep` reduces `PaperBlock.MoveCarrier` to `SiteWindow.GoodWWin` (the shape of the paper's
`(locmax)`) **plus** the two below-window suprema `efixLow`/`esumLow`.  `CarrierObstruction`
shows those two extra conjuncts are not level-window facts and in fact make the carrier false.
This file supplies the repair on the carrier side:

* `stepOk_of_EfixWin` — the two one-step potential differences of the complementary group are
  bounded by `SiteWindow.EfixWin` at the level window `[Alo - 1, xTop]`, provided every walker of
  that group sits at level `≥ Alo`.  No below-window information is used, and (unlike
  `MoveStep.stepOk_of_Efix`) no side condition `1 ≤ B` is needed: the boundary step
  `HA(-1)` cannot be reached.
* `goodStep_of_goodWWin` — hence `GoodStep` follows from `GoodWWin` and the position bound.
* `goodWWin_mono` — `GoodWWin` is monotone in the level.
* `MoveCarrierWin` — `MoveCarrierProper` with the plain envelope replaced by `GoodWWin` at the
  level window `Alo`, with the same ambient and `GoodStep` conjuncts.
* `moveCarrierWin_of_win` — a producer whose residuals are exactly
  (`ambGoodAll`, `GoodWWin` at `Alo`, positions `≥ Alo`, nonnegativity of positions).
  All four are level-window/bookkeeping statements: `AmbGoodAll` and `GoodWWin` are the measured
  objects (`Swarming.Enl.gamma_ambient_good_measure_ge`, `CarrierModel.winGood_goodWWin`), and
  the position bound is the record-geometry bound `Astar` (`LocCoordGeomCarrier`).
-/
import Swarm.MoveStep
import Swarm.WindowEnvelope

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory Filter Topology
open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open LocGroupQ LocMoveLocal LocMoveMart
open SwarmJointDrift
open MoveStep
open RecordoSupply SwarmRecordMeas SwarmRecordMeas.Actual
open Finset

namespace CarrierWin

/-! ## 1. `GoodWWin` is monotone in the level -/

theorem goodWWin_mono {N : ℕ} [Nonempty (Fin N)] {p : ℝ} {m n : ℕ} {A : Finset (Fin N)}
    (hA : A.Nonempty) {B B' : ℝ} (hBB : B ≤ B') {Alo : ℕ} {U : Swarming.Uniform.Array N}
    (h : SiteWindow.GoodWWin p m n A Aᶜ hA B Alo U) :
    SiteWindow.GoodWWin p m n A Aᶜ hA B' Alo U :=
  ⟨h.1, le_trans h.2.1 hBB, le_trans h.2.2 hBB⟩

/-! ## 2. The windowed envelope contains the one-step bounds -/

/-- **The level-window envelope controls the frozen-potential steps of the complementary
group.**  This is the windowed counterpart of `MoveStep.stepOk_of_Efix`: the two levels
`X^j` and `X^j - 1` are read off `SiteWindow.hfix_le_EfixWin`, so only levels inside
`[Alo - 1, xTop]` are used.  The hypothesis `Alo ≤ (X^j).toNat` excludes the boundary value
`HA(-1)`, so no separate `1 ≤ B` side condition is needed. -/
theorem stepOk_of_EfixWin {N : ℕ} [Nonempty (Fin N)] {p : ℝ} (hp0 : (1 : ℝ) / 2 ≤ p)
    (hp1 : p ≤ 1) {m n : ℕ} {A : Finset (Fin N)} {hK : (A ∪ Aᶜ).Nonempty} {B : ℝ}
    {Alo : ℕ} (hAlo : 1 ≤ Alo) {U : Swarming.Uniform.Array N}
    (hsep : SepSet p m n A Aᶜ U)
    (hE : SiteWindow.EfixWin p m n Aᶜ (A ∪ Aᶜ) hK Alo U ≤ B)
    (hpos : ∀ j ∈ Aᶜ, Alo ≤ (X p m U n j).toNat) :
    StepOk p m n Aᶜ B U := by
  intro j hj
  have hAcA : (Aᶜ)ᶜ = A := by ext i; simp
  rw [hAcA]
  have hX0 : 0 ≤ X p m U n j := hsep.1 j
  have hXle : X p m U n j ≤ (n : ℤ) := (abs_le.mp (SwarmM3.abs_X_le p m U n j)).2
  have hjun : j ∈ A ∪ Aᶜ := by simp
  have hRsup : runMax p m U j n ≤ RmaxZ p m n (A ∪ Aᶜ) hK U :=
    Finset.le_sup' (f := fun k => runMax p m U k n) hjun
  have hRle : (trajectory p m U n).pos j ≤ runMax p m U j n := le_runMax p m U j n
  have hRZ : X p m U n j ≤ RmaxZ p m n (A ∪ Aᶜ) hK U := le_trans hRle hRsup
  have hRZnn : 0 ≤ RmaxZ p m n (A ∪ Aᶜ) hK U := le_trans hX0 hRZ
  have hle_top : ∀ y : ℤ, 0 ≤ y → y ≤ X p m U n j →
      y.toNat ≤ xTop p m n (A ∪ Aᶜ) hK U := by
    intro y hy0 hyx
    have h1 : (y.toNat : ℤ) = y := Int.toNat_of_nonneg hy0
    have h2 : ((RmaxZ p m n (A ∪ Aᶜ) hK U).toNat : ℤ) = RmaxZ p m n (A ∪ Aᶜ) hK U :=
      Int.toNat_of_nonneg hRZnn
    have hnatR : y.toNat ≤ (RmaxZ p m n (A ∪ Aᶜ) hK U).toNat := by
      have h3 : (y.toNat : ℤ) ≤ ((RmaxZ p m n (A ∪ Aᶜ) hK U).toNat : ℤ) := by
        rw [h1, h2]; exact le_trans hyx hRZ
      exact_mod_cast h3
    have hnatN : y.toNat ≤ n := by
      have h3 : (y.toNat : ℤ) ≤ (n : ℤ) := by rw [h1]; exact le_trans hyx hXle
      exact_mod_cast h3
    show y.toNat ≤ min (n + 2) ((RmaxZ p m n (A ∪ Aᶜ) hK U).toNat + 1)
    omega
  have hw0 : ∀ k, 0 < wA p m U n A k := fun k => wA_pos p m U hp0 n A k
  have hw1 : ∀ k, wA p m U n A k ≤ 1 := fun k => wA_le_one p m U hp1 n A k
  have hfixnn : ∀ u, 0 ≤ hfix (wA p m U n A) u :=
    fun u => le_trans zero_le_one (one_le_hfix _ hw0 hw1 u)
  -- the position of `j` is at least one, so the left step is genuine
  have hX1 : (1 : ℤ) ≤ X p m U n j := by
    have hp := hpos j hj
    have h2 : 1 ≤ (X p m U n j).toNat := le_trans hAlo hp
    have h3 : ((1 : ℕ) : ℤ) ≤ ((X p m U n j).toNat : ℤ) := by exact_mod_cast h2
    rwa [Int.toNat_of_nonneg hX0] at h3
  constructor
  · -- the right step
    have hid : HA p m U n A (X p m U n j + 1) - HA p m U n A (X p m U n j)
        = hfix (wA p m U n A) (X p m U n j).toNat := HZ_succ_sub hX0
    rw [hid, abs_of_nonneg (hfixnn _)]
    have hle := SiteWindow.hfix_le_EfixWin (J := Aᶜ) hK U (A := Alo)
      (u := (X p m U n j).toNat) ?_ (hle_top _ hX0 le_rfl)
    rw [hAcA] at hle
    refine le_trans hle hE
    have := hpos j hj
    omega
  · -- the left step, now always at a level `≥ Alo - 1 ≥ 0`
    have hy0 : 0 ≤ X p m U n j - 1 := by omega
    have hid : HA p m U n A ((X p m U n j - 1) + 1) - HA p m U n A (X p m U n j - 1)
        = hfix (wA p m U n A) (X p m U n j - 1).toNat := HZ_succ_sub hy0
    rw [show X p m U n j - 1 + 1 = X p m U n j from by ring] at hid
    have hneg : HA p m U n A (X p m U n j - 1) - HA p m U n A (X p m U n j)
        = -(hfix (wA p m U n A) (X p m U n j - 1).toNat) := by
      rw [← hid]; ring
    rw [hneg, abs_neg, abs_of_nonneg (hfixnn _)]
    have hle := SiteWindow.hfix_le_EfixWin (J := Aᶜ) hK U (A := Alo)
      (u := (X p m U n j - 1).toNat) ?_ (hle_top _ hy0 (by omega))
    rw [hAcA] at hle
    refine le_trans hle hE
    have h2 : Alo ≤ (X p m U n j - 1).toNat + 1 := by
      have h3 : (((X p m U n j - 1).toNat : ℕ) : ℤ) = X p m U n j - 1 :=
        Int.toNat_of_nonneg hy0
      have hXe : X p m U n j = ((X p m U n j).toNat : ℤ) := (Int.toNat_of_nonneg hX0).symm
      have hp := hpos j hj
      have h4 : (Alo : ℤ) ≤ (((X p m U n j - 1).toNat + 1 : ℕ) : ℤ) := by
        push_cast
        omega
      exact_mod_cast h4
    exact h2

/-- **`GoodStep` follows from the windowed good event.** -/
theorem goodStep_of_goodWWin {N : ℕ} [Nonempty (Fin N)] {p : ℝ} (hp0 : (1 : ℝ) / 2 ≤ p)
    (hp1 : p ≤ 1) {m n : ℕ} {A : Finset (Fin N)} (hA : A.Nonempty) {B : ℝ} {Alo : ℕ}
    (hAlo : 1 ≤ Alo) {U : Swarming.Uniform.Array N}
    (h : SiteWindow.GoodWWin p m n A Aᶜ hA B Alo U)
    (hpos : ∀ j ∈ Aᶜ, Alo ≤ (X p m U n j).toNat) :
    GoodStep p m n Aᶜ B U := by
  have hAcA : (Aᶜ)ᶜ = A := by ext i; simp
  refine ⟨?_, stepOk_of_EfixWin hp0 hp1 hAlo h.1 h.2.1 hpos⟩
  show SepSet p m n (Aᶜ)ᶜ Aᶜ U
  rw [hAcA]
  exact h.1

/-! ## 3. The windowed carrier -/

/-- **The windowed move carrier.**  `MoveStep.MoveCarrierProper` with the whole-prefix envelope
`GoodW` replaced by the level-window event `SiteWindow.GoodWWin` at `Alo`.  By
`stepOk_of_EfixWin` the `GoodStep` conjunct is not an extra residual once the walkers of the
complementary group sit at level `≥ Alo`. -/
def MoveCarrierWin {N : ℕ} [Nonempty (Fin N)] (p : ℝ) (m r T L Alo : ℕ)
    (U : Swarming.Uniform.Array N) : Prop :=
  ∀ (A : Finset (Fin N)) (hA : A.Nonempty), A ≠ Finset.univ → ∀ s t : ℕ,
    recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
    (∀ u : ℕ, s ≤ u → u < t → Glue.Sep (PaperBlock.Xa p m U) A Aᶜ u) →
    U ∈ Swarming.Enl.ambGood p m hA (r : ℤ) T L ∧
      (∀ n ∈ Finset.Ico s t, SiteWindow.GoodWWin p m n A Aᶜ hA (RecClockLG.Bstar L) Alo U) ∧
      (∀ n ∈ Finset.Ico s t, GoodStep p m n Aᶜ (RecClockLG.Bstar L) U)

/-- **The plain carrier implies the windowed one**: nothing is lost by weakening the envelope to
its level-window part. -/
theorem moveCarrierProper_to_win {N : ℕ} [Nonempty (Fin N)] {p : ℝ} (hp0 : (1 : ℝ) / 2 ≤ p)
    (hp1 : p ≤ 1) {m r T L Alo : ℕ} {U : Swarming.Uniform.Array N}
    (h : MoveStep.MoveCarrierProper (N := N) p m r T L U) :
    MoveCarrierWin (N := N) p m r T L Alo U := by
  intro A hA hne s t hs hst ht hsep
  obtain ⟨hamb, hgood, hstep⟩ := h A hA hne s t hs hst ht hsep
  exact ⟨hamb, fun n hn => MoveStep.goodWWin_of_goodW hp0 hp1 hA Alo (hgood n hn), hstep⟩

/-- **Producer for the windowed carrier.**  The residuals are exactly
* the measured ambient event `ambGoodAll`,
* `SiteWindow.GoodWWin` at level `Bstar L` on the level window `[Alo - 1, xTop]` at every time
  of every separated movement window,
* the record-geometry lower bound `Alo ≤ X_n^j` on the *positions* of all walkers throughout the
  movement window (in the paper `Alo = Astar r T L`; `LocCoordGeomCarrier`/`DefectGeom`).

No below-window bound is required, no nonnegativity hypothesis, and no side condition
`1 ≤ Bstar L`: `GoodWWin` already contains `SepSet`, and `stepOk_of_EfixWin` needs only the
position bound. -/
theorem moveCarrierWin_of_win {N : ℕ} [Nonempty (Fin N)] {p : ℝ} (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) {m r T L Alo : ℕ} (hAlo : 1 ≤ Alo) {U : Swarming.Uniform.Array N}
    (hamb : U ∈ Swarming.Enl.ambGoodAll (N := N) p m (r : ℤ) T L)
    (hwin : ∀ (A : Finset (Fin N)) (hA : A.Nonempty), A ≠ Finset.univ → ∀ s t : ℕ,
      recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
      (∀ u : ℕ, s ≤ u → u < t → Glue.Sep (PaperBlock.Xa p m U) A Aᶜ u) →
      ∀ n ∈ Finset.Ico s t,
        SiteWindow.GoodWWin p m n A Aᶜ hA (RecClockLG.Bstar L) Alo U)
    (hposAll : ∀ n : ℕ, recTimeA p m U r ≤ n → n ≤ recTimeA p m U r + T * L →
      ∀ j : Fin N, Alo ≤ (X p m U n j).toNat) :
    MoveCarrierWin (N := N) p m r T L Alo U := by
  intro A hA hne s t hs hst ht hsep
  have hAc : Aᶜ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hnil
    exact hne ((Finset.compl_eq_empty_iff A).mp hnil)
  refine ⟨MoveStep.ambGood_of_ambGoodAll hA hAc hamb,
    fun n hn => hwin A hA hne s t hs hst ht hsep n hn, ?_⟩
  intro n hn
  have hn1 : recTimeA p m U r ≤ n := le_trans hs (Finset.mem_Ico.mp hn).1
  have hn2 : n ≤ recTimeA p m U r + T * L :=
    le_trans (le_of_lt (Finset.mem_Ico.mp hn).2) ht
  exact goodStep_of_goodWWin hp0.le hp1.le hA hAlo
    (hwin A hA hne s t hs hst ht hsep n hn)
    (fun j _ => hposAll n hn1 hn2 j)

/-- **Consumer form**: the windowed carrier plus the position bound gives the same `GoodStep`
shape that `PaperBlock.MoveCarrier` supplies, without any below-window hypothesis. -/
theorem moveCarrierWin_step {N : ℕ} [Nonempty (Fin N)] {p : ℝ} (hp0 : (1 : ℝ) / 2 ≤ p)
    (hp1 : p ≤ 1) {m r T L Alo : ℕ} (hAlo : 1 ≤ Alo) {U : Swarming.Uniform.Array N}
    (h : MoveCarrierWin (N := N) p m r T L Alo U) {A : Finset (Fin N)} (hA : A.Nonempty)
    (hne : A ≠ Finset.univ) {s t : ℕ} (hs : recTimeA p m U r ≤ s) (hst : s ≤ t)
    (ht : t ≤ recTimeA p m U r + T * L)
    (hsep : ∀ u : ℕ, s ≤ u → u < t → Glue.Sep (PaperBlock.Xa p m U) A Aᶜ u)
    (hpos : ∀ n ∈ Finset.Ico s t, ∀ j ∈ Aᶜ, Alo ≤ (X p m U n j).toNat) :
    ∀ n ∈ Finset.Ico s t, GoodStep p m n Aᶜ (RecClockLG.Bstar L) U := by
  intro n hn
  exact goodStep_of_goodWWin hp0 hp1 hA hAlo
    ((h A hA hne s t hs hst ht hsep).2.1 n hn) (hpos n hn)

/-! ## 4. Axiom audit -/


end CarrierWin
