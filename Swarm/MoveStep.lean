/-
# MoveStep — deterministic reduction of the predictable local-good carriers

`PaperBlock.MoveCarrier` keeps three conjuncts for every separated movement window
`[s,t) ⊂ [τ_r, τ_r + T L]` and every nonempty proper group `A`:

* `U ∈ ambGood p m hA (r : ℤ) T L`  (the `Γ`-count lower bound of `(locmax)`),
* `∀ n ∈ [s,t), GoodW p m n A Aᶜ hA (RecClockLG.Bstar L) U` (the potential envelope), and
* `∀ n ∈ [s,t), GoodStep p m n Aᶜ (RecClockLG.Bstar L) U` (the frozen-potential step bound).

This file proves that the third conjunct is **not independent**: on the separation event the
`GoodW` envelope already dominates every one-step difference of the frozen potential at the
positions of the complementary group, so `GoodW` implies `GoodStep` at the same level `B`.
The only side condition is the numerical fact `1 ≤ B`.

The proof is purely deterministic.  It uses only

* the definition of `LocGroupQ.Efix` as a supremum of `hfix (wA p m U n A)` over the sites
  `u ≤ xTop`,
* `Cookie.Hfix_succ` / `SepGroup.HZ_nonneg` for the exact one-step identity
  `HZ w (x+1) - HZ w x = hfix w x.toNat`, and
* the trajectory bounds `0 ≤ X_n^j ≤ n` and `X_n^j ≤ runMax_n^j ≤ Rmax_n`.

No probability, no measured event and no positivity of any good event is used.
-/
import Swarm.PaperBlock
import Swarm.WindowEnvelope

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff LocGroupQ LocMoveLocal LocMoveCompose LocMoveMart
open SwarmMarks SwarmLogRatio LocSumAct LocSumR1 LocOccCarrier LocOccAllStarts
open LocOccCarrierAssembly SummedSlope.Model
open LocOccSingleWindow LocOccAllPairs LocOccSingleWindowAllPairs
open RecordoSupply SwarmRecordMeas SwarmRecordMeas.Actual

namespace MoveStep

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. Reading a single `hfix` value out of the `Efix` envelope -/

/-- **The `Efix` envelope bounds every `hfix` value inside the window.**  `Efix` is the supremum
of `hfix (wA p m U n Jᶜ)` over the sites `u ≤ xTop`; a site inside the window therefore has
`hfix` bounded by the same constant. -/
theorem hfix_le_of_Efix {p : ℝ} {m n : ℕ} {J K : Finset (Fin N)} (hK : K.Nonempty) {B : ℝ}
    {U : Array N} (hE : Efix p m n J K hK U ≤ B) {u : ℕ}
    (hu : u ≤ xTop p m n K hK U) (hun : u < n + 3) :
    hfix (wA p m U n Jᶜ) u ≤ B := by
  have hle : (if u ≤ xTop p m n K hK U then hfix (wA p m U n Jᶜ) u else 0) ≤ B :=
    le_trans (Finset.le_sup' (f := fun u : ℕ =>
        if u ≤ xTop p m n K hK U then hfix (wA p m U n Jᶜ) u else 0)
      (Finset.mem_range.mpr hun)) hE
  rwa [if_pos hu] at hle

/-! ## 2. The exact one-step identity of the potential on `ℤ` -/

/-- **One step to the right.**  For `x ≥ 0` the potential difference `HZ w (x+1) - HZ w x` is
exactly the step `hfix w x.toNat`. -/
theorem HZ_succ_sub {w : ℕ → ℝ} {x : ℤ} (hx : 0 ≤ x) :
    SepGroup.HZ w (x + 1) - SepGroup.HZ w x = hfix w x.toNat := by
  have h1 : SepGroup.HZ w (x + 1) = Hfix w (x + 1).toNat := SepGroup.HZ_nonneg (by omega)
  have h2 : SepGroup.HZ w x = Hfix w x.toNat := SepGroup.HZ_nonneg hx
  have h3 : (x + 1).toNat = x.toNat + 1 := by omega
  rw [h1, h2, h3, Cookie.Hfix_succ]
  ring

/-- **One step to the left of the boundary.**  `HZ w (-1) = -1` by the paper's convention. -/
theorem HZ_neg_one (w : ℕ → ℝ) : SepGroup.HZ w ((0 : ℤ) - 1) = -1 := by
  rw [SepGroup.HZ_neg (by norm_num)]
  norm_num

/-! ## 3. `GoodW` implies `GoodStep` -/

/-- **The envelope already contains the step bound.**

If the frozen potential step at time `n` is bounded by `B` on the whole window
`[0, xTop]` (which is the second conjunct of `LocGroupQ.GoodW`), then every one-step
difference of `H_n^{A}` at the actual positions of the complementary group is at most `B`.
The side conditions are `1 ≤ B` (the boundary value `hfix w (-1) = 1`) and the trajectory
bounds `0 ≤ X_n^j ≤ n`, which are part of the separation event. -/
theorem stepOk_of_Efix {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    {A : Finset (Fin N)} {hK : (A ∪ Aᶜ).Nonempty} {B : ℝ} (hB1 : 1 ≤ B) {U : Array N}
    (hsep : SepSet p m n A Aᶜ U)
    (hE : Efix p m n Aᶜ (A ∪ Aᶜ) hK U ≤ B) :
    StepOk p m n Aᶜ B U := by
  intro j hj
  have hAcA : (Aᶜ)ᶜ = A := by ext i; simp
  rw [hAcA]
  -- the position of `j` and its two elementary bounds
  have hX0 : 0 ≤ X p m U n j := hsep.1 j
  have hXle : X p m U n j ≤ (n : ℤ) := (abs_le.mp (SwarmM3.abs_X_le p m U n j)).2
  have hjun : j ∈ A ∪ Aᶜ := by simp
  have hRsup : runMax p m U j n ≤ RmaxZ p m n (A ∪ Aᶜ) hK U :=
    Finset.le_sup' (f := fun k => runMax p m U k n) hjun
  have hRle : (trajectory p m U n).pos j ≤ runMax p m U j n := le_runMax p m U j n
  have hRZ : X p m U n j ≤ RmaxZ p m n (A ∪ Aᶜ) hK U := le_trans hRle hRsup
  have hRZnn : 0 ≤ RmaxZ p m n (A ∪ Aᶜ) hK U := le_trans hX0 hRZ
  -- any nonnegative level below `X` lies inside the window `[0, xTop]`
  have hle_top : ∀ y : ℤ, 0 ≤ y → y ≤ X p m U n j → y.toNat ≤ xTop p m n (A ∪ Aᶜ) hK U := by
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
    show y.toNat ≤ min (n + 2) (Rmax p m n (A ∪ Aᶜ) hK U + 1)
    show y.toNat ≤ min (n + 2) ((RmaxZ p m n (A ∪ Aᶜ) hK U).toNat + 1)
    omega
  -- the two structural facts about `hfix`
  have hw0 : ∀ k, 0 < wA p m U n A k := fun k => wA_pos p m U hp0.le n A k
  have hw1 : ∀ k, wA p m U n A k ≤ 1 := fun k => wA_le_one p m U hp1 n A k
  have hfixnn : ∀ u, 0 ≤ hfix (wA p m U n A) u :=
    fun u => le_trans zero_le_one (one_le_hfix _ hw0 hw1 u)
  constructor
  · -- the right step
    have hid : HA p m U n A (X p m U n j + 1) - HA p m U n A (X p m U n j)
        = hfix (wA p m U n A) (X p m U n j).toNat := HZ_succ_sub hX0
    rw [hid, abs_of_nonneg (hfixnn _)]
    have hEfix := hfix_le_of_Efix (J := Aᶜ) hK hE (hle_top _ hX0 le_rfl) ?_
    · rwa [hAcA] at hEfix
    have : (X p m U n j).toNat ≤ n := by
      have h3 : ((X p m U n j).toNat : ℤ) ≤ (n : ℤ) := by
        rw [Int.toNat_of_nonneg hX0]; exact hXle
      exact_mod_cast h3
    omega
  · -- the left step
    rcases lt_or_ge (X p m U n j) 1 with hlt | hge
    · -- the walker sits at the origin: the boundary value is `1`
      have hx0 : X p m U n j = 0 := by omega
      rw [hx0]
      have h1 : HA p m U n A ((0 : ℤ) - 1) = -1 := by
        show SepGroup.HZ (wA p m U n A) ((0 : ℤ) - 1) = -1
        exact HZ_neg_one _
      have h2 : HA p m U n A (0 : ℤ) = 0 := by
        show SepGroup.HZ (wA p m U n A) (0 : ℤ) = 0
        exact SepGroup.HZ_zero _
      rw [h1, h2]
      norm_num
      exact hB1
    · -- a genuine left step
      have hy0 : 0 ≤ X p m U n j - 1 := by omega
      have hid : HA p m U n A ((X p m U n j - 1) + 1) - HA p m U n A (X p m U n j - 1)
          = hfix (wA p m U n A) (X p m U n j - 1).toNat := HZ_succ_sub hy0
      rw [show X p m U n j - 1 + 1 = X p m U n j from by ring] at hid
      have hneg : HA p m U n A (X p m U n j - 1) - HA p m U n A (X p m U n j)
          = -(hfix (wA p m U n A) (X p m U n j - 1).toNat) := by
        rw [← hid]; ring
      rw [hneg, abs_neg, abs_of_nonneg (hfixnn _)]
      have hEfix := hfix_le_of_Efix (J := Aᶜ) hK hE
        (hle_top _ hy0 (by omega)) ?_
      · rwa [hAcA] at hEfix
      have : (X p m U n j - 1).toNat ≤ n := by
        have h3 : ((X p m U n j - 1).toNat : ℤ) ≤ (n : ℤ) := by
          rw [Int.toNat_of_nonneg hy0]; omega
        exact_mod_cast h3
      omega

/-- **`GoodW` implies `GoodStep`.**  The third conjunct of `PaperBlock.MoveCarrier` is a
consequence of the second one, at the same level `B ≥ 1`. -/
theorem goodStep_of_goodW {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    {A : Finset (Fin N)} (hA : A.Nonempty) {B : ℝ} (hB1 : 1 ≤ B) {U : Array N}
    (h : GoodW p m n A Aᶜ hA B U) :
    GoodStep p m n Aᶜ B U := by
  have hAcA : (Aᶜ)ᶜ = A := by ext i; simp
  refine ⟨?_, stepOk_of_Efix hp0 hp1 hB1 h.1 h.2.1⟩
  show SepSet p m n (Aᶜ)ᶜ Aᶜ U
  rw [hAcA]
  exact h.1


/-! ## 4. `Bstar` is at least one -/

theorem one_le_Bstar (L : ℕ) : 1 ≤ RecClockLG.Bstar L := by
  have hx : (0 : ℝ) ≤ LocSumAct.xOf L := Real.rpow_nonneg (Nat.cast_nonneg L) _
  have h6 : (6 : ℝ) ≤ RecClockLG.Bstar L := by
    have h1 : 2 * LocSumAct.xOf L + 6 ≤ RecClockLG.Bstar L := le_max_left _ _
    linarith
  linarith


/-! ## 5. The ambient `Γ`-count conjunct lies on the measured `ambBadAll` event -/

/-- `ambBad` does not depend on the proof of nonemptiness. -/
theorem ambBad_congr (p : ℝ) (m : ℕ) {A : Finset (Fin N)} (hA hA' : A.Nonempty)
    (r : ℤ) (T L : ℕ) :
    Swarming.Enl.ambBad p m hA r T L = Swarming.Enl.ambBad p m hA' r T L := by
  rw [Subsingleton.elim hA hA']

/-- **The ambient good event of one proper group, from the simultaneous one.**  Together with
`Swarming.Enl.gamma_ambient_good_measure_ge` this makes the first conjunct of
`PaperBlock.MoveCarrier` for proper groups a consequence of a single *measured* event. -/
theorem ambGood_of_ambGoodAll {p : ℝ} {m : ℕ} {r : ℤ} {T L : ℕ} {A : Finset (Fin N)}
    (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) {U : Array N}
    (h : U ∈ Swarming.Enl.ambGoodAll (N := N) p m r T L) :
    U ∈ Swarming.Enl.ambGood p m hA r T L := by
  have hne : A ≠ Finset.univ := by
    intro hEq
    rw [hEq] at hAc
    simp at hAc
  have hmem : A ∈ Swarming.Enl.properGroups N :=
    Swarming.Enl.mem_properGroups.mpr ⟨hA, hne⟩
  intro hb
  have hb' : U ∈ Swarming.Enl.ambBad p m (Swarming.Enl.mem_properGroups.mp hmem).1 r T L := by
    rw [← ambBad_congr p m hA (Swarming.Enl.mem_properGroups.mp hmem).1 r T L]
    exact hb
  exact h (Set.mem_iUnion.mpr ⟨⟨A, hmem⟩,
    Set.mem_iUnion.mpr ⟨Finset.mem_attach _ _, hb'⟩⟩)

/-! ## 6. Reducing `PaperBlock.MoveCarrier` to the envelope carrier -/

/-- **`PaperBlock.MoveCarrier` without the redundant step conjunct.**  It keeps the ambient
`Γ`-count event and the potential envelope `GoodW`, and drops `GoodStep`. -/
def MoveCarrierTwo (p : ℝ) (m r T L : ℕ) (U : Array N) : Prop :=
  ∀ (A : Finset (Fin N)) (hA : A.Nonempty), ∀ s t : ℕ,
    recTimeA p m U r ≤ s → s ≤ t →
    t ≤ recTimeA p m U r + T * L →
    (∀ u : ℕ, s ≤ u → u < t → Glue.Sep (PaperBlock.Xa p m U) A Aᶜ u) →
    U ∈ Swarming.Enl.ambGood p m hA (r : ℤ) T L ∧
      (∀ n ∈ Finset.Ico s t, GoodW p m n A Aᶜ hA (RecClockLG.Bstar L) U)

/-- **`PaperBlock.MoveCarrier` is equivalent to the two-conjunct carrier.**  The `GoodStep`
conjunct is derived from `GoodW` at the same level `Bstar L ≥ 1`. -/
theorem moveCarrier_iff_two {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m r T L : ℕ} {U : Array N} :
    PaperBlock.MoveCarrier p m r T L U ↔ MoveCarrierTwo (N := N) p m r T L U := by
  constructor
  · intro h A hA s t hs hst ht hsep
    exact ⟨(h A hA s t hs hst ht hsep).1, (h A hA s t hs hst ht hsep).2.1⟩
  · intro h A hA s t hs hst ht hsep
    obtain ⟨hamb, henv⟩ := h A hA s t hs hst ht hsep
    exact ⟨hamb, henv, fun n hn =>
      goodStep_of_goodW hp0 hp1.le hA (one_le_Bstar L) (henv n hn)⟩

/-- **The proper-group restriction of `PaperBlock.MoveCarrier`.**  This is the form in which the
carrier is consumed by `(locmove)`: `PaperBlock.paper_local_clauses` only ever applies it at
`A ≠ univ`. -/
def MoveCarrierProper (p : ℝ) (m r T L : ℕ) (U : Array N) : Prop :=
  ∀ (A : Finset (Fin N)) (hA : A.Nonempty), A ≠ Finset.univ → ∀ s t : ℕ,
    recTimeA p m U r ≤ s → s ≤ t →
    t ≤ recTimeA p m U r + T * L →
    (∀ u : ℕ, s ≤ u → u < t → Glue.Sep (PaperBlock.Xa p m U) A Aᶜ u) →
    U ∈ Swarming.Enl.ambGood p m hA (r : ℤ) T L ∧
      (∀ n ∈ Finset.Ico s t, GoodW p m n A Aᶜ hA (RecClockLG.Bstar L) U) ∧
      (∀ n ∈ Finset.Ico s t, GoodStep p m n Aᶜ (RecClockLG.Bstar L) U)

/-- **The envelope carrier**: the only conjunct of `MoveCarrierProper` that the public data do
not already supply.  In the paper this is the `(locmax)` content of `𝒢_{r,L,T}`. -/
def EnvelopeCarrier (p : ℝ) (m r T L : ℕ) (U : Array N) : Prop :=
  ∀ (A : Finset (Fin N)) (hA : A.Nonempty), A ≠ Finset.univ → ∀ s t : ℕ,
    recTimeA p m U r ≤ s → s ≤ t →
    t ≤ recTimeA p m U r + T * L →
    (∀ u : ℕ, s ≤ u → u < t → Glue.Sep (PaperBlock.Xa p m U) A Aᶜ u) →
    ∀ n ∈ Finset.Ico s t, GoodW p m n A Aᶜ hA (RecClockLG.Bstar L) U

theorem moveCarrierProper_of_moveCarrier {p : ℝ} {m r T L : ℕ} {U : Array N}
    (h : PaperBlock.MoveCarrier p m r T L U) : MoveCarrierProper (N := N) p m r T L U := by
  intro A hA _ s t hs hst ht hsep
  exact h A hA s t hs hst ht hsep

/-- **The exact reduction.**  On the measured ambient event `ambGoodAll`, the proper-group
`MoveCarrier` is *equivalent* to the single envelope carrier: the `Γ`-count conjunct is
measured and the step conjunct is redundant. -/
theorem moveCarrierProper_iff_envelope {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m r T L : ℕ} {U : Array N}
    (hamb : U ∈ Swarming.Enl.ambGoodAll (N := N) p m (r : ℤ) T L) :
    MoveCarrierProper (N := N) p m r T L U ↔ EnvelopeCarrier (N := N) p m r T L U := by
  constructor
  · intro h A hA hne s t hs hst ht hsep
    exact (h A hA hne s t hs hst ht hsep).2.1
  · intro h A hA hne s t hs hst ht hsep
    have hAc : Aᶜ.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hnil
      exact hne ((Finset.compl_eq_empty_iff A).mp hnil)
    have henv := h A hA hne s t hs hst ht hsep
    exact ⟨ambGood_of_ambGoodAll hA hAc hamb, henv,
      fun n hn => goodStep_of_goodW hp0 hp1.le hA (one_le_Bstar L) (henv n hn)⟩


/-! ## 7. `GoodW` implies the *windowed* good event

`LocGroupQ.Efix` is the supremum of `hfix (wA p m U n Jᶜ)` over the whole prefix `[0, xTop]`,
whereas `SiteWindow.EfixWin` restricts it to the level window `[Alo - 1, xTop]`.  The plain
supremum therefore dominates the windowed one, so the (stronger) `GoodW` conjunct of
`PaperBlock.MoveCarrier` supplies the windowed `GoodWWin` shape that
`SiteWindow.goodWWin_of_locmax` produces from `(locmax)`.  The converse is not implied by the
definitions: `GoodW` asks for a bound at *every* level below `xTop`, including the levels
below the window. -/

theorem EfixWin_le_Efix {p : ℝ} (hp0 : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    {J K : Finset (Fin N)} (hK : K.Nonempty) (Alo : ℕ) (U : Array N) :
    SiteWindow.EfixWin p m n J K hK Alo U ≤ Efix p m n J K hK U := by
  have hw0 : ∀ k, 0 < wA p m U n Jᶜ k := fun k => wA_pos p m U hp0 n Jᶜ k
  have hw1 : ∀ k, wA p m U n Jᶜ k ≤ 1 := fun k => wA_le_one p m U hp1 n Jᶜ k
  refine Finset.sup'_le _ _ (fun u hu => ?_)
  refine le_trans ?_ (Finset.le_sup'
    (f := fun u : ℕ => if u ≤ xTop p m n K hK U then hfix (wA p m U n Jᶜ) u else 0) hu)
  by_cases h : Alo ≤ u + 1 ∧ u ≤ xTop p m n K hK U
  · rw [if_pos h, if_pos h.2]
  · rw [if_neg h]
    by_cases h2 : u ≤ xTop p m n K hK U
    · rw [if_pos h2]
      exact le_trans zero_le_one (one_le_hfix _ hw0 hw1 u)
    · rw [if_neg h2]

theorem EsumWin_le_Esum {p : ℝ} (hp0 : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    {J K : Finset (Fin N)} (hK : K.Nonempty) (Alo : ℕ) (U : Array N) :
    SiteWindow.EsumWin p m n J K hK Alo U ≤ Esum p m n J K hK U := by
  have hw0 : ∀ k, 0 < wA p m U n Jᶜ k := fun k => wA_pos p m U hp0 n Jᶜ k
  have hw1 : ∀ k, wA p m U n Jᶜ k ≤ 1 := fun k => wA_le_one p m U hp1 n Jᶜ k
  refine Finset.sup'_le _ _ (fun u hu => ?_)
  by_cases h : Alo ≤ u ∧ u ≤ xTop p m n K hK U
  · rw [if_pos h]
    rw [hSum_eq_sum_indicator (u := u) (x := xTop p m n K hK U) (M := n + 2)
      (xTop_le p m n K hK U)]
    have hthis := Finset.le_sup' (s := Finset.range (n + 3))
      (f := fun u : ℕ => if u ≤ xTop p m n K hK U then
        ∑ z ∈ Finset.Ico u (n + 2),
          (if z < xTop p m n K hK U then
            ∏ v ∈ Finset.Ico (u + 1) (z + 1), rq (wA p m U n Jᶜ) v else 0) else 0) hu
    rwa [if_pos h.2] at hthis
  · rw [if_neg h]
    exact Esum_nonneg hp0 hp1 m n J K hK U

/-- The part of the `Efix` supremum that lies **below** the level window `[Alo - 1, xTop]`.
The paper's `(locmax)` bounds `h^*` only on `[r-(T+3)L, r+(T+3)L]`, i.e. only on the window;
this supremum is exactly the extra content of the plain `Efix` used by `GoodW`. -/
noncomputable def efixLow (p : ℝ) (m n : ℕ) (J K : Finset (Fin N)) (hK : K.Nonempty)
    (Alo : ℕ) (U : Array N) : ℝ :=
  (Finset.range (n + 3)).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩
    (fun u => if u + 1 < Alo ∧ u ≤ xTop p m n K hK U then hfix (wA p m U n Jᶜ) u else 0)

/-- **Exact decomposition of the plain `Efix` envelope.**  The supremum over the whole prefix
`[0, xTop]` is at most the maximum of its window part `EfixWin Alo` and its part below the window
`efixLow Alo`.  Consequently, a `(locmax)` that bounds `h^*` only on the level window does *not*
by itself bound `Efix`: the extra bound `efixLow Alo ≤ B` is needed. -/
theorem Efix_le_max {p : ℝ} (hp0 : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    {J K : Finset (Fin N)} (hK : K.Nonempty) (Alo : ℕ) (U : Array N) :
    Efix p m n J K hK U
      ≤ max (SiteWindow.EfixWin p m n J K hK Alo U) (efixLow p m n J K hK Alo U) := by
  have hw0 : ∀ k, 0 < wA p m U n Jᶜ k := fun k => wA_pos p m U hp0 n Jᶜ k
  have hw1 : ∀ k, wA p m U n Jᶜ k ≤ 1 := fun k => wA_le_one p m U hp1 n Jᶜ k
  refine Finset.sup'_le _ _ (fun u hu => ?_)
  by_cases h2 : u ≤ xTop p m n K hK U
  · rw [if_pos h2]
    by_cases h3 : Alo ≤ u + 1
    · refine le_trans ?_ (le_max_left _ _)
      exact SiteWindow.hfix_le_EfixWin (p := p) (m := m) (n := n) (J := J) (K := K) hK U h3 h2
    · have hlt : u + 1 < Alo := by omega
      refine le_trans ?_ (le_max_right _ _)
      have hthis := Finset.le_sup' (s := Finset.range (n + 3))
        (f := fun u : ℕ => if u + 1 < Alo ∧ u ≤ xTop p m n K hK U then
          hfix (wA p m U n Jᶜ) u else 0) hu
      rwa [if_pos (show u + 1 < Alo ∧ u ≤ xTop p m n K hK U from ⟨hlt, h2⟩)] at hthis
  · rw [if_neg h2]
    have h0 : (0 : ℝ) ≤ efixLow p m n J K hK Alo U := by
      refine le_trans ?_ (Finset.le_sup' (s := Finset.range (n + 3))
        (f := fun u : ℕ => if u + 1 < Alo ∧ u ≤ xTop p m n K hK U then
          hfix (wA p m U n Jᶜ) u else 0)
        (Finset.mem_range.mpr (by omega : 0 < n + 3)))
      by_cases hh : (0 : ℕ) + 1 < Alo ∧ (0 : ℕ) ≤ xTop p m n K hK U
      · rw [if_pos hh]
        exact le_trans zero_le_one (one_le_hfix _ hw0 hw1 0)
      · rw [if_neg hh]
    exact le_trans h0 (le_max_right _ _)

/-- The below-window part of the `Esum` supremum (the exact complement of `EsumWin Alo`
inside the prefix). -/
noncomputable def esumLow (p : ℝ) (m n : ℕ) (J K : Finset (Fin N)) (hK : K.Nonempty)
    (Alo : ℕ) (U : Array N) : ℝ :=
  (Finset.range (n + 3)).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩
    (fun u => if u < Alo ∧ u ≤ xTop p m n K hK U then
      ∑ z ∈ Finset.Ico u (n + 2),
        (if z < xTop p m n K hK U then
          ∏ v ∈ Finset.Ico (u + 1) (z + 1), rq (wA p m U n Jᶜ) v else 0)
      else 0)

theorem Esum_le_max {p : ℝ} (hp0 : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    {J K : Finset (Fin N)} (hK : K.Nonempty) (Alo : ℕ) (U : Array N) :
    Esum p m n J K hK U
      ≤ max (SiteWindow.EsumWin p m n J K hK Alo U) (esumLow p m n J K hK Alo U) := by
  have hw0 : ∀ k, 0 < wA p m U n Jᶜ k := fun k => wA_pos p m U hp0 n Jᶜ k
  have hw1 : ∀ k, wA p m U n Jᶜ k ≤ 1 := fun k => wA_le_one p m U hp1 n Jᶜ k
  refine Finset.sup'_le _ _ (fun u hu => ?_)
  by_cases h2 : u ≤ xTop p m n K hK U
  · rw [if_pos h2]
    by_cases h3 : Alo ≤ u
    · rw [← hSum_eq_sum_indicator (u := u) (x := xTop p m n K hK U) (M := n + 2)
        (xTop_le p m n K hK U)]
      refine le_trans ?_ (le_max_left _ _)
      have hthis := Finset.le_sup' (s := Finset.range (n + 3))
        (f := fun u : ℕ => if Alo ≤ u ∧ u ≤ xTop p m n K hK U then
          hSum (wA p m U n Jᶜ) u (xTop p m n K hK U) else 0) hu
      rwa [if_pos (show Alo ≤ u ∧ u ≤ xTop p m n K hK U from ⟨h3, h2⟩)] at hthis
    · have hlt : u < Alo := by omega
      refine le_trans ?_ (le_max_right _ _)
      have hthis := Finset.le_sup' (s := Finset.range (n + 3))
        (f := fun u : ℕ => if u < Alo ∧ u ≤ xTop p m n K hK U then
          ∑ z ∈ Finset.Ico u (n + 2),
            (if z < xTop p m n K hK U then
              ∏ v ∈ Finset.Ico (u + 1) (z + 1), rq (wA p m U n Jᶜ) v else 0)
          else 0) hu
      rwa [if_pos (show u < Alo ∧ u ≤ xTop p m n K hK U from ⟨hlt, h2⟩)] at hthis
  · rw [if_neg h2]
    have h0 : (0 : ℝ) ≤ esumLow p m n J K hK Alo U := by
      refine le_trans ?_ (Finset.le_sup' (s := Finset.range (n + 3))
        (f := fun u : ℕ => if u < Alo ∧ u ≤ xTop p m n K hK U then
          ∑ z ∈ Finset.Ico u (n + 2),
            (if z < xTop p m n K hK U then
              ∏ v ∈ Finset.Ico (u + 1) (z + 1), rq (wA p m U n Jᶜ) v else 0)
          else 0)
        (Finset.mem_range.mpr (by omega : 0 < n + 3)))
      by_cases hh : (0 : ℕ) < Alo ∧ (0 : ℕ) ≤ xTop p m n K hK U
      · rw [if_pos hh]
        exact Finset.sum_nonneg fun z _ => by
          split_ifs with hz
          · exact Finset.prod_nonneg fun v _ => rq_nonneg (hw0 v) (hw1 v)
          · exact le_rfl
      · rw [if_neg hh]
    exact le_trans h0 (le_max_right _ _)

theorem efixLow_le_Efix {p : ℝ} (hp0 : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    {J K : Finset (Fin N)} (hK : K.Nonempty) (Alo : ℕ) (U : Array N) :
    efixLow p m n J K hK Alo U ≤ Efix p m n J K hK U := by
  refine Finset.sup'_le _ _ (fun u hu => ?_)
  by_cases h : u + 1 < Alo ∧ u ≤ xTop p m n K hK U
  · rw [if_pos h]
    have hthis := Finset.le_sup' (s := Finset.range (n + 3))
      (f := fun u : ℕ => if u ≤ xTop p m n K hK U then hfix (wA p m U n Jᶜ) u else 0) hu
    rwa [if_pos h.2] at hthis
  · rw [if_neg h]
    exact Efix_nonneg hp0 hp1 m n J K hK U

theorem esumLow_le_Esum {p : ℝ} (hp0 : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    {J K : Finset (Fin N)} (hK : K.Nonempty) (Alo : ℕ) (U : Array N) :
    esumLow p m n J K hK Alo U ≤ Esum p m n J K hK U := by
  refine Finset.sup'_le _ _ (fun u hu => ?_)
  by_cases h : u < Alo ∧ u ≤ xTop p m n K hK U
  · rw [if_pos h]
    have hthis := Finset.le_sup' (s := Finset.range (n + 3))
      (f := fun u : ℕ => if u ≤ xTop p m n K hK U then
        ∑ z ∈ Finset.Ico u (n + 2),
          (if z < xTop p m n K hK U then
            ∏ v ∈ Finset.Ico (u + 1) (z + 1), rq (wA p m U n Jᶜ) v else 0)
        else 0) hu
    rwa [if_pos h.2] at hthis
  · rw [if_neg h]
    exact Esum_nonneg hp0 hp1 m n J K hK U

/-- **The plain good window is the windowed good window plus the below-window bounds.**

This is the exact content of the envelope carrier: `GoodWWin` (which `(locmax)` on the level
window supplies, and which `CarrierModel` measures) together with the two below-window
suprema.  Conversely `GoodWWin` follows from `GoodW` (`goodWWin_of_goodW`), so the pair of
hypotheses `efixLow ≤ B`, `esumLow ≤ B` is exactly the extra content of the envelope. -/
theorem goodW_of_goodWWin_low {p : ℝ} (hp0 : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    {A : Finset (Fin N)} (hA : A.Nonempty) {B : ℝ} (Alo : ℕ) {U : Array N}
    (hW : SiteWindow.GoodWWin p m n A Aᶜ hA B Alo U)
    (hfixLow : efixLow p m n Aᶜ (A ∪ Aᶜ) (hA.mono Finset.subset_union_left) Alo U ≤ B)
    (hsumLow : esumLow p m n Aᶜ (A ∪ Aᶜ) (hA.mono Finset.subset_union_left) Alo U ≤ B) :
    GoodW p m n A Aᶜ hA B U := by
  refine ⟨hW.1, le_trans (Efix_le_max hp0 hp1 _ Alo U) ?_,
    le_trans (Esum_le_max hp0 hp1 _ Alo U) ?_⟩
  · exact max_le hW.2.1 hfixLow
  · exact max_le hW.2.2 hsumLow

/-- **The plain good window gives the windowed one.** -/
theorem goodWWin_of_goodW {p : ℝ} (hp0 : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    {A : Finset (Fin N)} (hA : A.Nonempty) {B : ℝ} (Alo : ℕ) {U : Array N}
    (h : GoodW p m n A Aᶜ hA B U) :
    SiteWindow.GoodWWin p m n A Aᶜ hA B Alo U :=
  ⟨h.1,
    le_trans (EfixWin_le_Efix hp0 hp1 _ Alo U) h.2.1,
    le_trans (EsumWin_le_Esum hp0 hp1 _ Alo U) h.2.2⟩

/-- **`PaperBlock.MoveCarrier` supplies the windowed `(locmax)`-shaped carrier.**  This is the
form in which the public window machine consumes the envelope: `GoodWWin` at the level window
starting at `Alo` (in the paper, `Astar r T L`). -/
theorem goodWWin_of_moveCarrierProper {p : ℝ} (hp0 : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1)
    {m r T L Alo : ℕ} {U : Array N}
    (h : MoveCarrierProper (N := N) p m r T L U) :
    ∀ (A : Finset (Fin N)) (hA : A.Nonempty), A ≠ Finset.univ → ∀ s t : ℕ,
      recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
      (∀ u : ℕ, s ≤ u → u < t → Glue.Sep (PaperBlock.Xa p m U) A Aᶜ u) →
      ∀ n ∈ Finset.Ico s t, SiteWindow.GoodWWin p m n A Aᶜ hA (RecClockLG.Bstar L) Alo U := by
  intro A hA hne s t hs hst ht hsep n hn
  exact goodWWin_of_goodW hp0 hp1 hA Alo ((h A hA hne s t hs hst ht hsep).2.1 n hn)

/-- **The potential step is `2 + hprev` at weight `1/2`.**  Since `wA` only takes the values
`1/2` and `p`, this is the exact source of the linear growth of `hfix` on a run of `1/2`-sites. -/
theorem hfix_eq_two_add_hprev {w : ℕ → ℝ} {u : ℕ} (hw : w u = 1 / 2) :
    hfix w u = 2 + hprev w u := by
  rw [Cookie.hfix_eq, hw]
  norm_num
  ring

/-- **Linear growth on a run of `1/2`-sites.**  If the weight is `1/2` up to level `u`, the
potential at `u` is exactly `3 + 2u`; hence it is unbounded in `u` and *cannot* be bounded by a
constant that only depends on the level window. -/
theorem hfix_eq_of_half {w : ℕ → ℝ} :
    ∀ u : ℕ, (∀ v ≤ u, w v = 1 / 2) → hfix w u = 3 + 2 * (u : ℝ)
  | 0, hw => by
      rw [hfix_eq_two_add_hprev (hw 0 le_rfl), hprev_zero]
      norm_num
  | (u + 1), hw => by
      have hprev_eq : hfix w u = 3 + 2 * (u : ℝ) := hfix_eq_of_half u (fun v hv => hw v (by omega))
      rw [hfix_eq_two_add_hprev (hw (u + 1) le_rfl), hprev_succ, hprev_eq]
      push_cast
      ring

/-- **The plain envelope is unbounded below the window.**  Whenever the group weight is `1/2`
up to level `u` (which `wA = 1/2` realises at every site of a walker with local time below `m`),
the plain `Efix` is at least `3 + 2u`.  This is why `GoodW` — unlike `GoodWWin` — is not a
function of the level window alone. -/
theorem efix_ge_of_half {p : ℝ} {m n : ℕ} {J K : Finset (Fin N)} (hK : K.Nonempty)
    {U : Array N} {u : ℕ} (hu : u ≤ xTop p m n K hK U) (hun : u < n + 3)
    (hw : ∀ v ≤ u, wA p m U n Jᶜ v = 1 / 2) :
    3 + 2 * (u : ℝ) ≤ Efix p m n J K hK U := by
  have h1 : (if u ≤ xTop p m n K hK U then hfix (wA p m U n Jᶜ) u else 0)
      ≤ Efix p m n J K hK U :=
    Finset.le_sup' (s := Finset.range (n + 3))
      (f := fun u : ℕ => if u ≤ xTop p m n K hK U then hfix (wA p m U n Jᶜ) u else 0)
      (Finset.mem_range.mpr hun)
  rw [if_pos hu] at h1
  rwa [hfix_eq_of_half u hw] at h1

/-- **Consumer form: the windowed envelope plus the below-window bounds give the carrier.**

This is the usable residual of direction B.  A producer who has

* the measured ambient event `ambGoodAll`,
* `SiteWindow.GoodWWin` at level `Bstar L` on the level window `[Alo-1, xTop]` at every integer
  time of each separated movement window (the `(locmax)` shape; `SiteWindow.goodWWin_of_locmax`
  produces it from the window hypotheses, `CarrierModel.winGood_goodWWin` measures it), and
* the two below-window suprema bounded by `Bstar L`

obtains `MoveCarrierProper`, hence the `(locmove)` carrier of `PaperBlock.paper_local_clauses`
at `A ≠ univ`. -/
theorem moveCarrierProper_of_winLow {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m r T L Alo : ℕ} {U : Array N}
    (hamb : U ∈ Swarming.Enl.ambGoodAll (N := N) p m (r : ℤ) T L)
    (hwin : ∀ (A : Finset (Fin N)) (hA : A.Nonempty), A ≠ Finset.univ → ∀ s t : ℕ,
      recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
      (∀ u : ℕ, s ≤ u → u < t → Glue.Sep (PaperBlock.Xa p m U) A Aᶜ u) →
      ∀ n ∈ Finset.Ico s t,
        SiteWindow.GoodWWin p m n A Aᶜ hA (RecClockLG.Bstar L) Alo U)
    (hlowF : ∀ (A : Finset (Fin N)) (hA : A.Nonempty), A ≠ Finset.univ → ∀ s t : ℕ,
      recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
      (∀ u : ℕ, s ≤ u → u < t → Glue.Sep (PaperBlock.Xa p m U) A Aᶜ u) →
      ∀ n ∈ Finset.Ico s t,
        efixLow p m n Aᶜ (A ∪ Aᶜ) (hA.mono Finset.subset_union_left) Alo U
          ≤ RecClockLG.Bstar L)
    (hlowS : ∀ (A : Finset (Fin N)) (hA : A.Nonempty), A ≠ Finset.univ → ∀ s t : ℕ,
      recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
      (∀ u : ℕ, s ≤ u → u < t → Glue.Sep (PaperBlock.Xa p m U) A Aᶜ u) →
      ∀ n ∈ Finset.Ico s t,
        esumLow p m n Aᶜ (A ∪ Aᶜ) (hA.mono Finset.subset_union_left) Alo U
          ≤ RecClockLG.Bstar L) :
    MoveCarrierProper (N := N) p m r T L U := by
  intro A hA hne s t hs hst ht hsep
  have hAc : Aᶜ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hnil
    exact hne ((Finset.compl_eq_empty_iff A).mp hnil)
  have hgood : ∀ n ∈ Finset.Ico s t, GoodW p m n A Aᶜ hA (RecClockLG.Bstar L) U :=
    fun n hn => goodW_of_goodWWin_low hp0.le hp1.le hA Alo
      (hwin A hA hne s t hs hst ht hsep n hn)
      (hlowF A hA hne s t hs hst ht hsep n hn)
      (hlowS A hA hne s t hs hst ht hsep n hn)
  exact ⟨ambGood_of_ambGoodAll hA hAc hamb, hgood,
    fun n hn => goodStep_of_goodW hp0 hp1.le hA (one_le_Bstar L) (hgood n hn)⟩

/-! ## 8. Axiom audit -/

/-- **Exact characterisation of the `GoodW` envelope.**

The plain good window at a level window `Alo` is *equivalent* to the conjunction of
`SiteWindow.GoodWWin` (the shape `SiteWindow.goodWWin_of_locmax` and
`CarrierModel.winGood_goodWWin` produce and measure) and the two below-window suprema.
So the envelope conjunct of `PaperBlock.MoveCarrier` is precisely
"`(locmax)` on the level window **plus** the same bound below the window". -/
theorem goodW_iff_goodWWin_low {p : ℝ} (hp0 : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    {A : Finset (Fin N)} (hA : A.Nonempty) {B : ℝ} (Alo : ℕ) {U : Array N} :
    GoodW p m n A Aᶜ hA B U ↔
      SiteWindow.GoodWWin p m n A Aᶜ hA B Alo U ∧
        efixLow p m n Aᶜ (A ∪ Aᶜ) (hA.mono Finset.subset_union_left) Alo U ≤ B ∧
        esumLow p m n Aᶜ (A ∪ Aᶜ) (hA.mono Finset.subset_union_left) Alo U ≤ B := by
  constructor
  · intro h
    exact ⟨goodWWin_of_goodW hp0 hp1 hA Alo h,
      le_trans (efixLow_le_Efix hp0 hp1 _ Alo U) h.2.1,
      le_trans (esumLow_le_Esum hp0 hp1 _ Alo U) h.2.2⟩
  · rintro ⟨hW, hf, hs⟩
    exact goodW_of_goodWWin_low hp0 hp1 hA Alo hW hf hs


end MoveStep
