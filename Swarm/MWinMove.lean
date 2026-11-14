/-
# Display `(locmove)` from the windowed envelope

`LocMoveCompose.locmove_ae` proves the paper's `(locmove)` display almost surely from the paper's
good window, whose `W`-conjunct is the *prefix* envelope `LocGroupQ.GoodW`.  `PrefixObstruction`
shows that conjunct is not a function of the `(locmax)` window, so it cannot be discharged on the
record window; `CarrierWin.MoveCarrierWin` replaces it by the *windowed* envelope
`SiteWindow.GoodWWin` at level `Alo` together with the record-geometry position bound.

This file proves the display for that windowed carrier.  `MWinTrunc` supplies the missing
identification `Q_t - Q_s = Σ dQTW` on `winTrunc` windows, so the `Γ`-drift half
(`Swarming.GammaStrict.ae_window_gamma_drift_le`, which never used `GoodW`) can be closed against
`LocGroupSimul.measure_deviation_dQTW_le` instead of the prefix-truncated martingale.  The
max-growth half (`LocMoveCompose.maxgrowth_half_pointwise`, truncated by `GoodStep`) and the
deterministic convex combination (`LocMoveCompose.convex_combine_sharp`) are used unchanged.

Delivered here:

* `gamma_half_pointwise_win` — the `Γ`-drift half on a `winTrunc` window (same constants);
* `locmoveGoodWin`, `locmoveGoodWin.toGood` — the windowed good window of `(locmove)`;
* `locmove_ae_win` — the display almost surely on the windowed good window;
* `measure_locmove_le_win` — the per-window measured clause, with the first error term now the
  windowed maximal deviation `measure_deviation_dQTW_le`.

Nothing here estimates `GoodWWin` itself, the record geometry, `(loccoord)`, `(lococc)`, the
`(locsum)` carrier, `(locgroup)`, halving, tightness, regeneration or the speed; those stay
explicit inputs, exactly as in the prefix version.
-/
import Swarm.MWinTrunc
import Swarm.GammaStrictWindow
import Swarm.LocMoveLocalProfile

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift LocGroupQ LocGroupWindow LocMoveMart LocMoveLocal LocGroupSimul Swarming.Enl
open LocMoveCompose Loccoord

namespace MWin

variable {N : ℕ}

/-! ## 1. The `Γ`-drift half on a windowed good window -/

/-- **The `Γ`-drift half of `(locmove)`, pointwise, with the windowed truncation.**

Off a null set, on a window on which the windowed good event `winTrunc` holds at every time, the
record pin holds, and the *windowed* martingale sum does not deviate by `ε` anywhere in the
window, the paper's `-(R_t^A - R_s^A)` bound holds with the martingale defect replaced by `ε`.

This is `LocMoveCompose.gamma_half_pointwise` with `GoodW` replaced by `LocGroupSimul.winTrunc`
and `dQT` by `dQTW`; the constants are identical. -/
theorem gamma_half_pointwise_win {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    {Th Lh : ℕ} (hL : 1 ≤ Lh) {r : ℤ} (hr : (((Th + 3) * Lh : ℕ) : ℤ) ≤ r)
    {n0 s t : ℕ} (hn0 : n0 ≤ s) (hst : s ≤ t) (hhor : t ≤ n0 + (Th + 3) * Lh)
    {B ε : ℝ} {Aw : ℕ} :
    ∀ᵐ U ∂(arrayMeasure N),
      (U ∈ ambGood p m hA r Th Lh ∧
        (∀ n ∈ Finset.Ico s t, winTrunc p m n A Aᶜ hA B Aw U) ∧
        (r - (Lh : ℤ) ≤ runMaxA p m U hA n0 ∧ runMaxA p m U hA n0 ≤ r) ∧
        (∀ k ≤ t - s,
          |LocMart.psum (fun j => dQTW p m (s + j) A Aᶜ hA hAc B Aw) k U| < ε)) →
      WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc ≤
        -((2 * p - 1) * (1 - p) ^ ((2 * m - 1) * A.card) / ((A.card : ℕ) : ℝ)) *
            ((runMaxA p m U hA t - runMaxA p m U hA s : ℤ) : ℝ)
          + (2 * p - 1) / ((A.card : ℕ) : ℝ) *
              ((2 * (m : ℝ) * (1 - p) ^ ((2 * m - 1) * A.card) + 4 * (m : ℝ)) *
                Real.sqrt (Lh * Real.sqrt Lh))
          + ε := by
  haveI hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hid : Disjoint A Aᶜ := disjoint_compl_right
  filter_upwards [Swarming.GammaStrict.ae_window_gamma_drift_le (N := N) hp0 hp1 hm A hA hAc
      hL hr hn0 hst hhor,
    ae_psum_dQTW_eq_Q_sub (N := N) hp0 hp1 (m := m) A Aᶜ hA hAc hid B Aw] with U hdrift hQeq
  rintro ⟨hgood, hwin, hrec, hdev⟩
  have hsepwin : ∀ n ∈ Finset.Ico s t, SepSet p m n A Aᶜ U :=
    fun n hn => winTrunc_sep (hwin n hn)
  have hdr := hdrift hgood hsepwin hrec.1 hrec.2
  have hQ := hQeq s t hst (fun k hk hkt => hwin k (Finset.mem_Ico.mpr ⟨hk, hkt⟩))
  have hdev' : LocMart.psum (fun j => dQTW p m (s + j) A Aᶜ hA hAc B Aw) (t - s) U ≤ ε := by
    have := hdev (t - s) le_rfl
    rw [abs_lt] at this
    exact le_of_lt this.2
  rw [hQ] at hdev'
  linarith

/-! ## 2. The windowed good window of `(locmove)` -/

/-- The good window of display `(locmove)` with the **windowed** `W`-envelope: the record window is
`ambGood` and pinned at `r`, the windowed good event `winTrunc` holds throughout `[s,t)` (this
contains `(sep)` and both level-window envelope bounds), and `GoodStep` (the group-maximum step
truncation) holds throughout `[s,t)`, all at the common level `B` with level-window left edge
`Aw`. -/
def locmoveGoodWin (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty) (r : ℤ)
    (Th Lh : ℕ) (B : ℝ) (Aw : ℕ) (n0 s t : ℕ) (U : Array N) : Prop :=
  U ∈ ambGood p m hA r Th Lh ∧
    (∀ n ∈ Finset.Ico s t, winTrunc p m n A Aᶜ hA B Aw U) ∧
    (∀ n ∈ Finset.Ico s t, GoodStep p m n Aᶜ B U) ∧
    (r - (Lh : ℤ) ≤ runMaxA p m U hA n0 ∧ runMaxA p m U hA n0 ≤ r)

/-- `(sep)` is a conjunct of the windowed good event. -/
theorem locmoveGoodWin_sep {p : ℝ} {m : ℕ} {A : Finset (Fin N)} {hA : A.Nonempty} {r : ℤ}
    {Th Lh : ℕ} {B : ℝ} {Aw n0 s t : ℕ} {U : Array N}
    (h : locmoveGoodWin (N := N) p m A hA r Th Lh B Aw n0 s t U) :
    ∀ n ∈ Finset.Ico s t, SepSet p m n A Aᶜ U :=
  fun n hn => winTrunc_sep (h.2.1 n hn)

/-- The windowed good window is contained in the *prefix*-good window with the same `B`: the
windowed envelope bounds the prefix one only through `GoodW`, which is false in general, so we
only record the deterministic-order statement that `GoodStep` is shared. -/
theorem locmoveGoodWin_step {p : ℝ} {m : ℕ} {A : Finset (Fin N)} {hA : A.Nonempty} {r : ℤ}
    {Th Lh : ℕ} {B : ℝ} {Aw n0 s t : ℕ} {U : Array N}
    (h : locmoveGoodWin (N := N) p m A hA r Th Lh B Aw n0 s t U) :
    ∀ n ∈ Finset.Ico s t, GoodStep p m n Aᶜ B U := h.2.2.1

/-! ## 3. The display almost surely on the windowed good window -/
theorem locmove_ae_win {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    {Th Lh : ℕ} (hL : 1 ≤ Lh) {r : ℤ} (hr : (((Th + 3) * Lh : ℕ) : ℤ) ≤ r)
    {n0 s t : ℕ} (hn0 : n0 ≤ s) (hst : s ≤ t) (hhor : t ≤ n0 + (Th + 3) * Lh)
    {B ε₁ ε₂ C β : ℝ} {Aw : ℕ} (hC1 : 1 ≤ C) (hγC : 1 ≤ gammaRate p m A * C)
    {bad geom : Set (Array N)}
    (hcc : ∀ U : Array N, U ∉ bad → U ∈ geom →
      Swarming.Group.average A
        (fun k => HA p m U t A (X p m U t k) - HA p m U s A (X p m U s k))
        ≤ C * (((runMaxA p m U hA t : ℤ) : ℝ) - ((Xmin p m U A hA s : ℤ) : ℝ)) + 3 * C * β) :
    ∀ᵐ U ∂(arrayMeasure N),
      (U ∈ ambGood p m hA r Th Lh ∧
        (∀ n ∈ Finset.Ico s t, LocGroupSimul.winTrunc p m n A Aᶜ hA B Aw U) ∧
        (∀ n ∈ Finset.Ico s t, GoodStep p m n Aᶜ B U) ∧
        (r - (Lh : ℤ) ≤ runMaxA p m U hA n0 ∧ runMaxA p m U hA n0 ≤ r) ∧
        U ∉ bad ∧ U ∈ geom ∧
        (∀ k ≤ t - s,
          |LocMart.psum (fun j => LocGroupSimul.dQTW p m (s + j) A Aᶜ hA hAc B Aw) k U| < ε₁) ∧
        (∀ k ≤ t - s,
          |Lcum p m (s + k) Aᶜ hAc B U - Lcum p m s Aᶜ hAc B U| < ε₂)) →
      WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc ≤
        (1 + C ^ 2) *
            (((runMaxA p m U hA s : ℤ) : ℝ) - ((Xmin p m U A hA s : ℤ) : ℝ))
          - ((t - s : ℕ) : ℝ) / (1 + C ^ 2)
          + max (3 * C * β + ε₂) (gammaErr (N := N) p m A Lh + ε₁) := by
  haveI hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hid : Disjoint A Aᶜ := disjoint_compl_right
  filter_upwards [gamma_half_pointwise_win (N := N) hp0 hp1 hm A hA hAc hL hr hn0 hst hhor
      (B := B) (ε := ε₁) (Aw := Aw),
    maxgrowth_half_pointwise (N := N) hp0 hp1 m A hAc (B := B) (ε := ε₂) hst] with U hgam hmax
  rintro ⟨hgood, hwin, hgoodStep, hrec, hbad, hgeom, hdev₁, hdev₂⟩
  -- the two halves and the local-coordinate bound
  have hdom := hgam ⟨hgood, hwin, hrec, hdev₁⟩
  have hmaxg := hmax ⟨hgoodStep, hdev₂⟩
  have hloc := hcc U hbad hgeom
  -- abbreviations
  set Rt : ℤ := runMaxA p m U hA t with hRteq
  set Rs : ℤ := runMaxA p m U hA s with hRseq
  set Xs : ℤ := Xmin p m U A hA s with hXseq
  set R : ℝ := ((Rt - Rs : ℤ) : ℝ) with hReq
  set R₀ : ℝ := ((Rs : ℤ) : ℝ) - ((Xs : ℤ) : ℝ) with hR₀eq
  set x : ℝ := WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc with hxeq
  set E : ℝ := 3 * C * β + ε₂ with hEeq
  set E' : ℝ := gammaErr (N := N) p m A Lh + ε₁ with hE'eq
  have hcast : ((Rt : ℤ) : ℝ) - ((Rs : ℤ) : ℝ) = R := by
    rw [hReq]; push_cast; ring
  have hRtRs : ((Rt : ℤ) : ℝ) - ((Rs : ℤ) : ℝ) = R := hcast
  -- nonnegativity
  have hRnn : 0 ≤ R := by
    have hmono : runMaxA p m U hA s ≤ runMaxA p m U hA t := runMaxA_mono hst
    rw [hReq]
    have h2 : (0 : ℤ) ≤ Rt - Rs := by rw [hRteq, hRseq]; linarith
    exact_mod_cast h2
  have hR₀nn : 0 ≤ R₀ := by
    have h1 : Xmin p m U A hA s ≤ runMaxA p m U hA s := by
      have h2 := Xmin_le_Rmax (p := p) (m := m) U hA (le_refl s)
      have h3 : Rmax p m U A hA s = runMaxA p m U hA s := rfl
      rw [h3] at h2; exact h2
    rw [hR₀eq, hRseq, hXseq]
    have h4 : (0 : ℤ) ≤ runMaxA p m U hA s - Xmin p m U A hA s := by linarith
    have h5 := (Int.cast_le (R := ℝ)).mpr h4
    push_cast at h5
    linarith
  -- the paper's two bounds on `x`
  have hloc' : Swarming.Group.average A
      (fun k => HA p m U t A (X p m U t k) - HA p m U s A (X p m U s k))
      ≤ C * (R + R₀) + 3 * C * β := by
    have h3 : ((Rmax p m U A hA t : ℤ) : ℝ) - ((Xmin p m U A hA s : ℤ) : ℝ) = R + R₀ := by
      rw [hReq, hR₀eq, hRteq, hRseq, hXseq]
      have : ((Rmax p m U A hA t : ℤ) : ℝ) = ((runMaxA p m U hA t : ℤ) : ℝ) := by rfl
      rw [this]
      push_cast
      ring
    rw [← h3]
    exact hloc
  have hW : x = (Anow p m t A Aᶜ U - Anow p m s A Aᶜ U)
      - (Mnow p m t Aᶜ hAc U - Mnow p m s Aᶜ hAc U) := by
    rw [hxeq, WA_eq, WA_eq]
    ring
  have havg : Anow p m t A Aᶜ U - Anow p m s A Aᶜ U
      = Swarming.Group.average A
          (fun k => HA p m U t A (X p m U t k) - HA p m U s A (X p m U s k)) := by
    simp only [Anow, Swarming.Group.average, Finset.sum_sub_distrib, compl_compl, sub_div]
  -- bound (i)
  have hi : x ≤ C * R + C * R₀ - ((t - s : ℕ) : ℝ) + E := by
    rw [hW, havg, hEeq]
    linarith [hloc', hmaxg]
  -- bound (ii)
  have hii : x ≤ -R / C + E' := by
    have hCp : (0 : ℝ) < C := by linarith
    have hpos : 0 < gammaRate p m A := by
      have hp2 : (0 : ℝ) < 2 * p - 1 := by linarith
      have hbase : (0 : ℝ) < 1 - p := by linarith
      have hpow : (0 : ℝ) < (1 - p) ^ ((2 * m - 1) * A.card) := by positivity
      have hcard : (0 : ℝ) < ((A.card : ℕ) : ℝ) := by
        have : 0 < A.card := Finset.card_pos.mpr hA
        exact_mod_cast this
      rw [gammaRate]
      positivity
    have h2 : R / C ≤ gammaRate p m A * R := by
      rw [div_le_iff₀ hCp]
      calc R = R * 1 := (mul_one R).symm
        _ ≤ R * (gammaRate p m A * C) := mul_le_mul_of_nonneg_left hγC hRnn
        _ = gammaRate p m A * R * C := by ring
    have hbound : -(gammaRate p m A * R) ≤ -R / C := by
      rw [neg_div]
      linarith [h2]
    have heq1 : (-((2 * p - 1) * (1 - p) ^ ((2 * m - 1) * A.card) / ((A.card : ℕ) : ℝ))) * R
        = -(gammaRate p m A * R) := by
      rw [gammaRate, neg_mul]
    have heq2 : (2 * p - 1) / ((A.card : ℕ) : ℝ) *
          ((2 * (m : ℝ) * (1 - p) ^ ((2 * m - 1) * A.card) + 4 * (m : ℝ)) *
            Real.sqrt (Lh * Real.sqrt Lh)) + ε₁
        = gammaErr (N := N) p m A Lh + ε₁ := by
      rw [gammaErr]
    have hdom' : x ≤ -(gammaRate p m A * R) + E' := by
      rw [hE'eq]
      linarith [hdom, heq1, heq2]
    linarith [hdom', hbound]
  have hmain := convex_combine_sharp hC1 hRnn hR₀nn hi hii
  rw [hxeq, hR₀eq, hRseq, hXseq, hEeq, hE'eq] at hmain
  exact hmain


/-! ## 4. The measured `(locmove)` clause at the windowed carrier -/

/-- **The `(locmove)` deviation estimate on the windowed carrier.**  On the windowed good window,
the paper's display fails only on a set of measure at most the sum of the two maximal-deviation
bounds and the `(loccoord)` bad set's measure:

`2 (t-s+1) e^{-ε₁²/(4 (t-s) (2 envB)²)} + 2 (t-s+1) e^{-ε₂²/(4 (t-s) (2B)²)} + e_b`.

The first term is now the **windowed** maximal deviation
`LocGroupSimul.measure_deviation_dQTW_le` (envelope `2·stepEnv p B`, the same envelope as the
prefix version), the second the max-growth half's
`LocMoveLocalProfile.measure_max_abs_Lcum_window_le`, the third the carrier `(loccoord)` bound.
No term depends on `T`, and no prefix envelope `GoodW` appears. -/
theorem measure_locmove_le_win {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    {Th Lh : ℕ} (hL : 1 ≤ Lh) {r : ℤ} (hr : (((Th + 3) * Lh : ℕ) : ℤ) ≤ r)
    {n0 s t : ℕ} (hn0 : n0 ≤ s) (hst : s ≤ t) (hhor : t ≤ n0 + (Th + 3) * Lh)
    {B ε₁ ε₂ C β : ℝ} (hB : 0 < B) {Aw : ℕ} (hC1 : 1 ≤ C)
    (hγC : 1 ≤ gammaRate p m A * C)
    (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (hK : 1 ≤ t - s)
    (hside₁ : ε₁ ≤ 4 * ((t - s : ℕ) : ℝ) * stepEnv (N := N) p B)
    (hside₂ : ε₂ ≤ 4 * ((t - s : ℕ) : ℝ) * B)
    {bad geom : Set (Array N)} {eb : ℝ}
    (hcc : ∀ U : Array N, U ∉ bad → U ∈ geom →
      Swarming.Group.average A
        (fun k => HA p m U t A (X p m U t k) - HA p m U s A (X p m U s k))
        ≤ C * (((runMaxA p m U hA t : ℤ) : ℝ) - ((Xmin p m U A hA s : ℤ) : ℝ)) + 3 * C * β)
    (hbad : (arrayMeasure N).real bad ≤ eb) :
    (arrayMeasure N).real
      {U : Array N |
        locmoveGoodWin (N := N) p m A hA r Th Lh B Aw n0 s t U ∧ U ∈ geom ∧
          ¬ (WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
              ≤ locmoveRHS (N := N) p m A hA Lh C β ε₁ ε₂ s t U)}
      ≤ 2 * (((t - s : ℕ) : ℝ) + 1) *
          Real.exp (-(ε₁ ^ 2) / (4 * (((t - s : ℕ) : ℝ) * (2 * stepEnv (N := N) p B) ^ 2)))
        + 2 * (((t - s : ℕ) : ℝ) + 1) *
          Real.exp (-(ε₂ ^ 2) / (4 * (((t - s : ℕ) : ℝ) * (2 * B) ^ 2)))
        + eb := by
  haveI hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hid : Disjoint A Aᶜ := disjoint_compl_right
  set K : ℕ := t - s with hKdef
  have hae := locmove_ae_win (N := N) hp0 hp1 hm A hA hAc hL hr hn0 hst hhor (B := B)
    (ε₁ := ε₁) (ε₂ := ε₂) (C := C) (β := β) (Aw := Aw) hC1 hγC (bad := bad) (geom := geom) hcc
  have hae' : ∀ᵐ U ∂(arrayMeasure N),
      (locmoveGoodWin (N := N) p m A hA r Th Lh B Aw n0 s t U ∧ U ∉ bad ∧ U ∈ geom ∧
        (∀ k ≤ t - s,
          |LocMart.psum (fun j => dQTW p m (s + j) A Aᶜ hA hAc B Aw) k U| < ε₁) ∧
        (∀ k ≤ t - s,
          |Lcum p m (s + k) Aᶜ hAc B U - Lcum p m s Aᶜ hAc B U| < ε₂)) →
      WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
        ≤ locmoveRHS (N := N) p m A hA Lh C β ε₁ ε₂ s t U := by
    filter_upwards [hae] with U hU
    rintro ⟨hg, hbad', hgeom', hdev1, hdev2⟩
    exact hU ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2, hbad', hgeom', hdev1, hdev2⟩
  set D₁ : Set (Array N) :=
    {U | ∃ k ≤ K, ε₁ ≤ |LocMart.psum (fun j => dQTW p m (s + j) A Aᶜ hA hAc B Aw) k U|}
    with hD₁
  set D₂ : Set (Array N) :=
    {U | ∃ k ≤ K, ε₂ ≤ |Lcum p m (s + k) Aᶜ hAc B U - Lcum p m s Aᶜ hAc B U|} with hD₂
  set N₀ : Set (Array N) :=
    {U | ¬ ((locmoveGoodWin (N := N) p m A hA r Th Lh B Aw n0 s t U ∧ U ∉ bad ∧ U ∈ geom ∧
        (∀ k ≤ t - s,
          |LocMart.psum (fun j => dQTW p m (s + j) A Aᶜ hA hAc B Aw) k U| < ε₁) ∧
        (∀ k ≤ t - s,
          |Lcum p m (s + k) Aᶜ hAc B U - Lcum p m s Aᶜ hAc B U| < ε₂)) →
      WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
        ≤ locmoveRHS (N := N) p m A hA Lh C β ε₁ ε₂ s t U)} with hN₀
  have hK' : K = t - s := hKdef
  have hD₁b := measure_deviation_dQTW_le (N := N) (m := m) hp0 hp1 A Aᶜ hA hAc hid hB Aw
    (s := s) (K := K) (by rw [hK']; exact hK) hε₁ (by rw [hK']; exact hside₁)
  have hD₂b := measure_max_abs_Lcum_window_le (N := N) hp0.le hp1.le m Aᶜ hAc hB (s := s)
    (K := K) (by rw [hK']; exact hK) hε₂ (by rw [hK']; exact hside₂)
  have hD₂b' : (arrayMeasure N).real
        {U | ∃ k ≤ K, ε₂ ≤ |Lcum p m (s + k) Aᶜ hAc B U - Lcum p m s Aᶜ hAc B U|}
      ≤ 2 * ((K : ℝ) + 1) *
          Real.exp (-(ε₂ ^ 2) / (4 * ((K : ℝ) * (2 * B) ^ 2))) := by
    have h := hD₂b
    rwa [show (4 : ℝ) * (K : ℝ) * (2 * B) ^ 2 = 4 * ((K : ℝ) * (2 * B) ^ 2) by ring] at h
  have hN₀z : (arrayMeasure N) N₀ = 0 := (MeasureTheory.ae_iff (μ := arrayMeasure N)).1 hae'
  have hsub : {U : Array N |
        locmoveGoodWin (N := N) p m A hA r Th Lh B Aw n0 s t U ∧ U ∈ geom ∧
          ¬ (WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
              ≤ locmoveRHS (N := N) p m A hA Lh C β ε₁ ε₂ s t U)}
      ⊆ D₁ ∪ D₂ ∪ bad ∪ N₀ := by
    intro U hU
    by_cases h1 : U ∈ D₁
    · exact Or.inl (Or.inl (Or.inl h1))
    by_cases h2 : U ∈ D₂
    · exact Or.inl (Or.inl (Or.inr h2))
    by_cases h3 : U ∈ bad
    · exact Or.inl (Or.inr h3)
    · refine Or.inr ?_
      rw [hN₀]
      intro hmaster
      refine hU.2.2 (hmaster ⟨hU.1, h3, hU.2.1, ?_, ?_⟩)
      · intro k hk
        exact not_le.mp (fun hc => h1 ⟨k, by rw [hKdef]; exact hk, hc⟩)
      · intro k hk
        exact not_le.mp (fun hc => h2 ⟨k, by rw [hKdef]; exact hk, hc⟩)
  have hN0z : (arrayMeasure N).real N₀ = 0 := by
    rw [measureReal_def, hN₀z]
    simp
  calc (arrayMeasure N).real {U : Array N |
        locmoveGoodWin (N := N) p m A hA r Th Lh B Aw n0 s t U ∧ U ∈ geom ∧
          ¬ (WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
              ≤ locmoveRHS (N := N) p m A hA Lh C β ε₁ ε₂ s t U)}
      ≤ (arrayMeasure N).real (D₁ ∪ D₂ ∪ bad ∪ N₀) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (arrayMeasure N).real (D₁ ∪ D₂ ∪ bad) + (arrayMeasure N).real N₀ :=
        MeasureTheory.measureReal_union_le (μ := arrayMeasure N) _ _
    _ ≤ ((arrayMeasure N).real (D₁ ∪ D₂) + (arrayMeasure N).real bad)
          + (arrayMeasure N).real N₀ := by
        have h := MeasureTheory.measureReal_union_le (μ := arrayMeasure N) (D₁ ∪ D₂) bad
        linarith
    _ ≤ (((arrayMeasure N).real D₁ + (arrayMeasure N).real D₂) + (arrayMeasure N).real bad)
          + (arrayMeasure N).real N₀ := by
        have h := MeasureTheory.measureReal_union_le (μ := arrayMeasure N) D₁ D₂
        linarith
    _ ≤ 2 * ((K : ℝ) + 1) *
          Real.exp (-(ε₁ ^ 2) / (4 * ((K : ℝ) * (2 * stepEnv (N := N) p B) ^ 2)))
        + 2 * ((K : ℝ) + 1) * Real.exp (-(ε₂ ^ 2) / (4 * ((K : ℝ) * (2 * B) ^ 2))) + eb := by
        simp only [hD₁, hD₂]
        linarith [hD₁b, hD₂b', hbad, hN0z]

/-! ## 5. Axiom audit -/


end MWin
