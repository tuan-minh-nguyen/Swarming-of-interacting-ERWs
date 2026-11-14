/-
# Composing the two halves of `(locmove)`

The accepted tree has the two halves of the display `(locmove)` of Proposition `local`
(`main_1d_revised.tex` lines 1285 and 1303-1311) separately:

* the **max-growth half** `LocMoveLocal.Mnow_good_window_ge` +
  `LocMoveLocalProfile.measure_good_window_dev_le` (predictably truncated maximum process, envelope
  `2B`), and
* the **`Γ`-drift half** `Swarming.GammaStrict.ae_window_gamma_drift_le` with the martingale defect
  estimated by `LocGroupGamma.measure_gamma_window_le`,

together with `LocMoveH.convex_combine` (the paper's last step) and
`LocCoordRange.loccoord_full_window` (the mean-term bound (loccoord)).

What was missing is the **assembly**: on one common carrier, from the same window, derive the
single-constant display

  `W_t^{A,Aᶜ} - W_s^{A,Aᶜ} ≤ C (R_s^A - min_{i∈A} X_s^i) - (t-s)/C + (explicit error)`

with a *joint* exceptional probability.  This file does that.  It introduces no stochastic
hypothesis beyond the ones the accepted files already carry: the only new inputs are

* the local-coordinate bound, which is `LocCoordRange.loccoord_full_window` verbatim, and
* the two predictable good events `GoodW` and `GoodStep` at one common truncation level `B`.

The exceptional set is the union of the two maximal-deviation events and the `(locsum)` bad set;
its measure is bounded by the sum of the three explicit bounds.  Nothing here claims `(coincide)`,
`(meet)`, halving, invariant existence, regeneration or `MainClaim`, and no `T`-dependent
coefficient is introduced.
-/
import Swarm.LocGroupWindow
import Swarm.LocGroupGamma
import Swarm.LocCoordRange
import Swarm.LocMoveH
import Swarm.LocMoveLocalTotal
import Swarm.LocMoveLocalWindow
import Swarm.GammaStrictWindow

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace LocMoveCompose

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift LocGroupQ LocGroupWindow LocMoveMart LocMoveLocal Swarming.Enl

variable {N : ℕ}

/-! ## 1. The two halves as pointwise statements off null sets -/

/-- **The `Γ`-drift half, pointwise.**  Off a null set, on a window on which the separation event
and the predictable event `GoodW` hold at every time, inside the record window, and *provided the
truncated martingale sum does not deviate by `ε` anywhere in the window*, the paper's
`-(R_t^A - R_s^A)` bound with the martingale defect replaced by `ε` holds. -/
theorem gamma_half_pointwise {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    {Th Lh : ℕ} (hL : 1 ≤ Lh) {r : ℤ} (hr : (((Th + 3) * Lh : ℕ) : ℤ) ≤ r)
    {n0 s t : ℕ} (hn0 : n0 ≤ s) (hst : s ≤ t) (hhor : t ≤ n0 + (Th + 3) * Lh)
    {B ε : ℝ} :
    ∀ᵐ U ∂(arrayMeasure N),
      (U ∈ ambGood p m hA r Th Lh ∧
        (∀ n ∈ Finset.Ico s t, SepSet p m n A Aᶜ U) ∧
        (∀ n ∈ Finset.Ico s t, GoodW p m n A Aᶜ hA B U) ∧
        (r - (Lh : ℤ) ≤ runMaxA p m U hA n0 ∧ runMaxA p m U hA n0 ≤ r) ∧
        (∀ k ≤ t - s,
          |LocMart.psum (fun j => dQT p m A Aᶜ hA hAc B (s + j)) k U| < ε)) →
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
    ae_psum_dQT_eq_Q_sub (N := N) hp0 hp1 (m := m) A Aᶜ hA hAc hid B] with U hdrift hQeq
  rintro ⟨hgood, hsep, hgoodW, hrec, hdev⟩
  have hdr := hdrift hgood hsep hrec.1 hrec.2
  have hQ := hQeq s t hst (fun k hk hkt => hgoodW k (Finset.mem_Ico.mpr ⟨hk, hkt⟩))
  have hdev' : LocMart.psum (fun j => dQT p m A Aᶜ hA hAc B (s + j)) (t - s) U ≤ ε := by
    have := hdev (t - s) le_rfl
    rw [abs_lt] at this
    exact le_of_lt this.2
  linarith

/-- **The max-growth half, pointwise.**  Off a null set, on a window on which the predictable event
`GoodStep` holds at every time, and *provided the truncated maximum martingale does not deviate by
`ε`*, the paper's `-(t-s)` bound holds literally. -/
theorem maxgrowth_half_pointwise {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ)
    (A : Finset (Fin N)) (hAc : Aᶜ.Nonempty) {B ε : ℝ} {s t : ℕ} (hst : s ≤ t) :
    ∀ᵐ U ∂(arrayMeasure N),
      ((∀ k ∈ Finset.Ico s t, GoodStep p m k Aᶜ B U) ∧
        (∀ k ≤ t - s,
          |Lcum p m (s + k) Aᶜ hAc B U - Lcum p m s Aᶜ hAc B U| < ε)) →
      ((t - s : ℕ) : ℝ) - ε ≤ Mnow p m t Aᶜ hAc U - Mnow p m s Aᶜ hAc U := by
  haveI hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  filter_upwards [Mnow_good_window_ge (p := p) hp0 hp1 (m := m) Aᶜ hAc B (s := s) (t := t) hst]
    with U hge
  rintro ⟨hgood, hdev⟩
  have hineq := hge (fun k hk => hgood k hk)
  have hsum := sum_Ico_LdM_eq (p := p) (m := m) (s := s) (t := t) Aᶜ hAc B hst U
  rw [hsum] at hineq
  have hstep := hdev (t - s) le_rfl
  have hsk : s + (t - s) = t := Nat.add_sub_cancel' hst
  rw [hsk] at hstep
  rw [abs_lt] at hstep
  linarith [hstep.1]

end LocMoveCompose

namespace LocMoveCompose

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift LocGroupQ LocGroupWindow LocMoveMart LocMoveLocal Swarming.Enl Loccoord

variable {N : ℕ}

/-! ## 2. The deterministic last step: the paper's convex combination at `C_f = 1 + C²` -/

/-- **The paper's last step of `(locmove)`, in the exact shape of the display.**  Two bounds on the
same quantity `x`,

`x ≤ C R + C R₀ - Δ + E` and `x ≤ -R/C + E'`,

with `R = R_t^A - R_s^A ≥ 0`, `R₀ = R_s^A - min_{i∈A}X_s^i ≥ 0`, combine with weights `1/(1+C²)`
and `C²/(1+C²)` into

`x ≤ (1+C²) R₀ - Δ/(1+C²) + max E E'`,

i.e. display `(locmove)` with the single constant `C_f = 1 + C²` in both places (the paper's
"replacing `C` by `1+C²`"). -/
theorem convex_combine_sharp {C x R R₀ Δ E E' : ℝ} (hC1 : 1 ≤ C)
    (hR : 0 ≤ R) (hR₀ : 0 ≤ R₀)
    (h₁ : x ≤ C * R + C * R₀ - Δ + E) (h₂ : x ≤ -R / C + E') :
    x ≤ (1 + C ^ 2) * R₀ - Δ / (1 + C ^ 2) + max E E' := by
  have hcomb := LocMove.convex_combine (C := C) (x := x) (R := R) (R₀ := R₀) (Δ := Δ)
    (E := E) (E' := E') hC1 h₁ h₂
  have hden : 0 < 1 + C ^ 2 := by positivity
  have hcoef : C / (1 + C ^ 2) ≤ 1 + C ^ 2 := by
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg C, zero_le_one (α := ℝ), sq_nonneg (C ^ 2)]
  have hstep : C / (1 + C ^ 2) * R₀ ≤ (1 + C ^ 2) * R₀ :=
    mul_le_mul_of_nonneg_right hcoef hR₀
  linarith

/-! ## 3. The two halves on one carrier: the `(locmove)` display almost everywhere -/

/-- The `Γ`-trial error coefficient `κ C_L L^{3/4}` of `(locmove)`, with
`κ = (2p-1)/|A|` and `C_L = 2m(1-p)^((2m-1)|A|) + 4m`. -/
noncomputable def gammaErr {N : ℕ} (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (Lh : ℕ) : ℝ :=
  (2 * p - 1) / ((A.card : ℕ) : ℝ) *
    ((2 * (m : ℝ) * (1 - p) ^ ((2 * m - 1) * A.card) + 4 * (m : ℝ)) *
      Real.sqrt (Lh * Real.sqrt Lh))

/-- The `Γ`-drift rate `γ = (2p-1)(1-p)^((2m-1)|A|)/|A|`. -/
noncomputable def gammaRate {N : ℕ} (p : ℝ) (m : ℕ) (A : Finset (Fin N)) : ℝ :=
  (2 * p - 1) * (1 - p) ^ ((2 * m - 1) * A.card) / ((A.card : ℕ) : ℝ)

/-- **`(locmove)` off one null set, on one carrier.**  Both good events are evaluated on the same
window `[s,t)`, at the same truncation level `B`; the local-coordinate bound is supplied
pointwise off `bad`.  Almost surely, whenever

* the record window is `ambGood` and `r - L ≤ R^A_{n₀} ≤ r`,
* `(sep)` holds at every time of the window,
* `GoodW` (the `W`-step truncation) and `GoodStep` (the maximum-step truncation) hold at every time,
* the window is off `bad` (where `(loccoord)` fails),
* neither truncated martingale deviates by `ε₁` (resp. `ε₂`) in the window,

the display of Proposition `local` holds with `C_f = 1 + C²`:

`W_t - W_s ≤ C_f (R_s^A - min_{i∈A}X_s^i) - (t-s)/C_f + max (3Cβ + ε₂) (κ C_L L^{3/4} + ε₁)`.
-/
theorem locmove_ae {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    {Th Lh : ℕ} (hL : 1 ≤ Lh) {r : ℤ} (hr : (((Th + 3) * Lh : ℕ) : ℤ) ≤ r)
    {n0 s t : ℕ} (hn0 : n0 ≤ s) (hst : s ≤ t) (hhor : t ≤ n0 + (Th + 3) * Lh)
    {B ε₁ ε₂ C β : ℝ} (hC1 : 1 ≤ C) (hγC : 1 ≤ gammaRate p m A * C)
    {bad geom : Set (Array N)}
    (hcc : ∀ U : Array N, U ∉ bad → U ∈ geom →
      Swarming.Group.average A
        (fun k => HA p m U t A (X p m U t k) - HA p m U s A (X p m U s k))
        ≤ C * (((runMaxA p m U hA t : ℤ) : ℝ) - ((Xmin p m U A hA s : ℤ) : ℝ)) + 3 * C * β) :
    ∀ᵐ U ∂(arrayMeasure N),
      (U ∈ ambGood p m hA r Th Lh ∧
        (∀ n ∈ Finset.Ico s t, SepSet p m n A Aᶜ U) ∧
        (∀ n ∈ Finset.Ico s t, GoodW p m n A Aᶜ hA B U) ∧
        (∀ n ∈ Finset.Ico s t, GoodStep p m n Aᶜ B U) ∧
        (r - (Lh : ℤ) ≤ runMaxA p m U hA n0 ∧ runMaxA p m U hA n0 ≤ r) ∧
        U ∉ bad ∧ U ∈ geom ∧
        (∀ k ≤ t - s,
          |LocMart.psum (fun j => dQT p m A Aᶜ hA hAc B (s + j)) k U| < ε₁) ∧
        (∀ k ≤ t - s,
          |Lcum p m (s + k) Aᶜ hAc B U - Lcum p m s Aᶜ hAc B U| < ε₂)) →
      WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc ≤
        (1 + C ^ 2) *
            (((runMaxA p m U hA s : ℤ) : ℝ) - ((Xmin p m U A hA s : ℤ) : ℝ))
          - ((t - s : ℕ) : ℝ) / (1 + C ^ 2)
          + max (3 * C * β + ε₂) (gammaErr (N := N) p m A Lh + ε₁) := by
  haveI hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hid : Disjoint A Aᶜ := disjoint_compl_right
  filter_upwards [gamma_half_pointwise (N := N) hp0 hp1 hm A hA hAc hL hr hn0 hst hhor
      (B := B) (ε := ε₁),
    maxgrowth_half_pointwise (N := N) hp0 hp1 m A hAc (B := B) (ε := ε₂) hst] with U hgam hmax
  rintro ⟨hgood, hsep, hgoodW, hgoodStep, hrec, hbad, hgeom, hdev₁, hdev₂⟩
  -- the two halves and the local-coordinate bound
  have hdom := hgam ⟨hgood, hsep, hgoodW, hrec, hdev₁⟩
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

end LocMoveCompose

namespace LocMoveCompose

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift LocGroupQ LocGroupWindow LocMoveMart LocMoveLocal Swarming.Enl Loccoord

variable {N : ℕ}

/-! ## 4. The good window and the right-hand side of the display, as named objects -/

/-- The good window of display `(locmove)`: the record window is `ambGood` and pinned at `r`,
`(sep)` holds throughout `[s,t)`, `GoodW` (the `W`-step truncation) holds throughout `[s,t)`, and
`GoodStep` (the group-maximum step truncation) holds throughout `[s,t)`, all at the common
truncation level `B`. -/
def locmoveGood (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty) (r : ℤ)
    (Th Lh : ℕ) (B : ℝ) (n0 s t : ℕ) (U : Array N) : Prop :=
  U ∈ ambGood p m hA r Th Lh ∧
    (∀ n ∈ Finset.Ico s t, SepSet p m n A Aᶜ U) ∧
    (∀ n ∈ Finset.Ico s t, GoodW p m n A Aᶜ hA B U) ∧
    (∀ n ∈ Finset.Ico s t, GoodStep p m n Aᶜ B U) ∧
    (r - (Lh : ℤ) ≤ runMaxA p m U hA n0 ∧ runMaxA p m U hA n0 ≤ r)

/-- The right-hand side of display `(locmove)` at `C_f = 1 + C²`. -/
noncomputable def locmoveRHS (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (Lh : ℕ) (C β ε₁ ε₂ : ℝ) (s t : ℕ) (U : Array N) : ℝ :=
  (1 + C ^ 2) * (((runMaxA p m U hA s : ℤ) : ℝ) - ((Xmin p m U A hA s : ℤ) : ℝ))
    - ((t - s : ℕ) : ℝ) / (1 + C ^ 2)
    + max (3 * C * β + ε₂) (gammaErr (N := N) p m A Lh + ε₁)

/-- **The `(locmove)` deviation estimate.**  On the good window, the paper's display fails only on
a set of measure at most the sum of the two maximal-deviation bounds and the `(loccoord)` bad
set's measure:

`2 (t-s+1) e^{-ε₁²/(4 (t-s) (2 envB)²)} + 2 (t-s+1) e^{-ε₂²/(4 (t-s) (2B)²)} + e_b`.

The first term is the `Γ`-drift half's martingale (`LocGroupWindow.measure_deviation_goodW_le`), the
second the max-growth half's (`LocMoveLocalProfile.measure_max_abs_Lcum_window_le`), the third the
carrier `(loccoord)` bound.  No term depends on `T`. -/
theorem measure_locmove_le {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    {Th Lh : ℕ} (hL : 1 ≤ Lh) {r : ℤ} (hr : (((Th + 3) * Lh : ℕ) : ℤ) ≤ r)
    {n0 s t : ℕ} (hn0 : n0 ≤ s) (hst : s ≤ t) (hhor : t ≤ n0 + (Th + 3) * Lh)
    {B ε₁ ε₂ C β : ℝ} (hB : 0 < B) (hC1 : 1 ≤ C) (hγC : 1 ≤ gammaRate p m A * C)
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
        locmoveGood (N := N) p m A hA r Th Lh B n0 s t U ∧ U ∈ geom ∧
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
  -- the master pointwise statement
  have hae := locmove_ae (N := N) hp0 hp1 hm A hA hAc hL hr hn0 hst hhor (B := B)
    (ε₁ := ε₁) (ε₂ := ε₂) (C := C) (β := β) hC1 hγC (bad := bad) (geom := geom) hcc
  have hae' : ∀ᵐ U ∂(arrayMeasure N),
      (locmoveGood (N := N) p m A hA r Th Lh B n0 s t U ∧ U ∉ bad ∧ U ∈ geom ∧
        (∀ k ≤ t - s,
          |LocMart.psum (fun j => dQT p m A Aᶜ hA hAc B (s + j)) k U| < ε₁) ∧
        (∀ k ≤ t - s,
          |Lcum p m (s + k) Aᶜ hAc B U - Lcum p m s Aᶜ hAc B U| < ε₂)) →
      WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
        ≤ locmoveRHS (N := N) p m A hA Lh C β ε₁ ε₂ s t U := by
    filter_upwards [hae] with U hU
    rintro ⟨hg, hbad', hgeom', hdev1, hdev2⟩
    have hg' : U ∈ ambGood p m hA r Th Lh ∧
        (∀ n ∈ Finset.Ico s t, SepSet p m n A Aᶜ U) ∧
        (∀ n ∈ Finset.Ico s t, GoodW p m n A Aᶜ hA B U) ∧
        (∀ n ∈ Finset.Ico s t, GoodStep p m n Aᶜ B U) ∧
        (r - (Lh : ℤ) ≤ runMaxA p m U hA n0 ∧ runMaxA p m U hA n0 ≤ r) := hg
    exact hU ⟨hg'.1, hg'.2.1, hg'.2.2.1, hg'.2.2.2.1, hg'.2.2.2.2, hbad', hgeom', hdev1, hdev2⟩
  set D₁ : Set (Array N) :=
    {U | ∃ k ≤ K, ε₁ ≤ |LocMart.psum (fun j => dQT p m A Aᶜ hA hAc B (s + j)) k U|}
    with hD₁
  set D₂ : Set (Array N) :=
    {U | ∃ k ≤ K, ε₂ ≤ |Lcum p m (s + k) Aᶜ hAc B U - Lcum p m s Aᶜ hAc B U|} with hD₂
  set N₀ : Set (Array N) :=
    {U | ¬ ((locmoveGood (N := N) p m A hA r Th Lh B n0 s t U ∧ U ∉ bad ∧ U ∈ geom ∧
        (∀ k ≤ t - s,
          |LocMart.psum (fun j => dQT p m A Aᶜ hA hAc B (s + j)) k U| < ε₁) ∧
        (∀ k ≤ t - s,
          |Lcum p m (s + k) Aᶜ hAc B U - Lcum p m s Aᶜ hAc B U| < ε₂)) →
      WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
        ≤ locmoveRHS (N := N) p m A hA Lh C β ε₁ ε₂ s t U)} with hN₀
  have hK' : K = t - s := hKdef
  have hD₁b := measure_deviation_goodW_le (N := N) (m := m) hp0 hp1 A Aᶜ hA hAc hid hB (s := s) (K := K)
    (by rw [hK']; exact hK) hε₁ (by rw [hK']; exact hside₁)
  have hD₂b := measure_max_abs_Lcum_window_le (N := N) hp0.le hp1.le m Aᶜ hAc hB (s := s)
    (K := K) (by rw [hK']; exact hK) hε₂ (by rw [hK']; exact hside₂)
  have hD₂b' : (arrayMeasure N).real
        {U | ∃ k ≤ K, ε₂ ≤ |Lcum p m (s + k) Aᶜ hAc B U - Lcum p m s Aᶜ hAc B U|}
      ≤ 2 * ((K : ℝ) + 1) *
          Real.exp (-(ε₂ ^ 2) / (4 * ((K : ℝ) * (2 * B) ^ 2))) := by
    have h := hD₂b
    rwa [show (4 : ℝ) * (K : ℝ) * (2 * B) ^ 2 = 4 * ((K : ℝ) * (2 * B) ^ 2) by ring] at h
  have hN₀z : (arrayMeasure N) N₀ = 0 := (MeasureTheory.ae_iff (μ := arrayMeasure N)).1 hae'
  -- the event is contained in `D₁ ∪ D₂ ∪ bad ∪ N₀`
  have hsub : {U : Array N |
        locmoveGood (N := N) p m A hA r Th Lh B n0 s t U ∧ U ∈ geom ∧
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
        locmoveGood (N := N) p m A hA r Th Lh B n0 s t U ∧ U ∈ geom ∧
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

end LocMoveCompose

namespace LocMoveCompose

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift LocGroupQ LocGroupWindow LocMoveMart LocMoveLocal Swarming.Enl Loccoord

variable {N : ℕ}

/-! ## 5. Discharging the carrier: `(locmove)` with `(loccoord)` instantiated -/

/-- **Display `(locmove)` of Proposition `local`, composed, with every exception probability
explicit.**

The local-coordinate input is instantiated at `LocCoordRange.loccoord_full_window`: outside the
actual `(locsum)` bad set `LsBad N p m C₀ ((2T+4)L) (r-(T+2)L)`, whose measure is at most
`exp(-c L^{1/16})`, the mean term obeys

`average_{i∈A}(H_t^A(X_t^i) - H_s^A(X_s^i)) ≤ ((2C₀+1)/2)(R_t^A - min_{i∈A}X_s^i) + 3C₀β`,

`β = betaT (xOf ((2T+4)L))`, provided the record window's two extreme positions lie in the enlarged
`(locsum)` window `[r-(T+2)L, r+(T+2)L]`.  Those three containment conditions are *pointwise*
conditions on the trajectory, not probability claims; they are carried inside the measured event,
so the estimate below is unconditional.

With `C_f = ((2C₀+1)/2)` and the `Γ`-rate hypothesis `1 ≤ γ C_f` (always satisfiable by enlarging
`C₀`, which is free apart from `Mb < C₀`), on the good window the display fails only on a set of
measure at most

`2(t-s+1) e^{-ε₁²/(4(t-s)(2 envB)²)} + 2(t-s+1) e^{-ε₂²/(4(t-s)(2B)²)} + e^{-c L^{1/16}}`.

All coefficients are independent of `T`. -/
theorem exists_measure_locmove_total {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    {C₀ : ℝ} (hC₀1 : 1 ≤ C₀) (hC₀M : LocSum.Mb p (LocSumAct.qOf p m) < C₀)
    (hγC : 1 ≤ gammaRate p m A * ((2 * C₀ + 1) / 2)) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ Th r : ℕ, (3 * Th + 6) * L ≤ r →
      ∀ {n0 s t : ℕ} (_hn0 : n0 ≤ s) (_hst : s ≤ t) (_hhor : t ≤ n0 + (Th + 3) * L)
        (_hr : (Th + 3) * L ≤ r)
        {B ε₁ ε₂ : ℝ}, 0 < B → 0 < ε₁ → 0 < ε₂ → 1 ≤ t - s →
        ε₁ ≤ 4 * ((t - s : ℕ) : ℝ) * stepEnv (N := N) p B →
        ε₂ ≤ 4 * ((t - s : ℕ) : ℝ) * B →
      (arrayMeasure N).real
        {U : Array N |
          locmoveGood (N := N) p m A hA (r : ℤ) Th L B n0 s t U ∧
            (0 ≤ Xmin p m U A hA s ∧
              r - (Th + 2) * L ≤ (Xmin p m U A hA s).toNat ∧
              (Rmax p m U A hA t).toNat ≤ r + (Th + 2) * L) ∧
            ¬ (WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
                ≤ locmoveRHS (N := N) p m A hA L ((2 * C₀ + 1) / 2)
                    ((LocSumAct.betaT (LocSumAct.xOf ((2 * Th + 4) * L)) : ℕ) : ℝ) ε₁ ε₂ s t U)}
        ≤ 2 * (((t - s : ℕ) : ℝ) + 1) *
            Real.exp (-(ε₁ ^ 2) / (4 * (((t - s : ℕ) : ℝ) * (2 * stepEnv (N := N) p B) ^ 2)))
          + 2 * (((t - s : ℕ) : ℝ) + 1) *
            Real.exp (-(ε₂ ^ 2) / (4 * (((t - s : ℕ) : ℝ) * (2 * B) ^ 2)))
          + Real.exp (-c * LocSumAct.xOf ((2 * Th + 4) * L)) := by
  haveI hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  obtain ⟨c, hc, L₀, hLL⟩ :=
    Loccoord.loccoord_full_window (N := N) hp0 hp1 hm hC₀1 hC₀M
  refine ⟨c, hc, max L₀ 1, ?_⟩
  intro L hLbig Th r hr n0 s t hn0 hst hhor hr' B ε₁ ε₂ hB hε₁ hε₂ hK hside₁ hside₂
  have hL0 : L₀ ≤ L := le_trans (le_max_left _ _) hLbig
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hLbig
  -- the actual `(locsum)` bad set and the trajectory's window containment
  set bad : Set (Array N) :=
    LocSumR1.LsBad N p m C₀ ((2 * Th + 4) * L) (r - (Th + 2) * L) with hbaddef
  set geom : Set (Array N) :=
    {U : Array N | 0 ≤ Xmin p m U A hA s ∧
      r - (Th + 2) * L ≤ (Xmin p m U A hA s).toNat ∧
      (Rmax p m U A hA t).toNat ≤ r + (Th + 2) * L} with hgeomdef
  -- its measured bound
  have hbadmeas : (arrayMeasure N).real bad
      ≤ Real.exp (-c * LocSumAct.xOf ((2 * Th + 4) * L)) := by
    have h1 := (hLL L hL0 Th r hr).1
    rw [measureReal_def]
    calc ((arrayMeasure N) bad).toReal
        ≤ (ENNReal.ofReal (Real.exp (-c * LocSumAct.xOf ((2 * Th + 4) * L)))).toReal :=
          ENNReal.toReal_mono (ENNReal.ofReal_ne_top) h1
      _ = Real.exp (-c * LocSumAct.xOf ((2 * Th + 4) * L)) :=
          ENNReal.toReal_ofReal (Real.exp_pos _).le
  -- the `(loccoord)` bound, at the paper's constant `(2C₀+1)/2` and error `3((2C₀+1)/2)β`
  have hβ0 : (0 : ℝ) ≤ ((LocSumAct.betaT (LocSumAct.xOf ((2 * Th + 4) * L)) : ℕ) : ℝ) := by
    have hx : 1 ≤ LocSumAct.xOf ((2 * Th + 4) * L) := by
      apply LocSumAct.one_le_xOf
      have h1 : 0 < 2 * Th + 4 := by omega
      have h2 : 0 < L := by omega
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.ne_of_gt h1) (Nat.ne_of_gt h2))
    exact (LocSumAct.betaT_pos hx).le
  have hC1 : (1 : ℝ) ≤ (2 * C₀ + 1) / 2 := by linarith
  have hcc : ∀ U : Array N, U ∉ bad → U ∈ geom →
      Swarming.Group.average A
        (fun k => HA p m U t A (X p m U t k) - HA p m U s A (X p m U s k))
        ≤ ((2 * C₀ + 1) / 2) *
            (((runMaxA p m U hA t : ℤ) : ℝ) - ((Xmin p m U A hA s : ℤ) : ℝ))
          + 3 * ((2 * C₀ + 1) / 2) *
              ((LocSumAct.betaT (LocSumAct.xOf ((2 * Th + 4) * L)) : ℕ) : ℝ) := by
    intro U hUb hUg
    obtain ⟨hX0, hAle, hLb⟩ := hUg
    have hres := (hLL L hL0 Th r hr).2 U hUb A hA s t hst hX0 hAle hLb
    have hRmax : ((Loccoord.Rmax p m U A hA t : ℤ) : ℝ) = ((runMaxA p m U hA t : ℤ) : ℝ) :=
      rfl
    rw [hRmax] at hres
    have hstep : 3 * C₀ * ((LocSumAct.betaT (LocSumAct.xOf ((2 * Th + 4) * L)) : ℕ) : ℝ)
        ≤ 3 * ((2 * C₀ + 1) / 2) *
            ((LocSumAct.betaT (LocSumAct.xOf ((2 * Th + 4) * L)) : ℕ) : ℝ) := by
      nlinarith [hβ0, hC₀1]
    linarith
  have hmain := measure_locmove_le (N := N) hp0 hp1 (le_trans (by norm_num : 1 ≤ 2) hm) A hA hAc
    (Th := Th) (Lh := L) (by omega) (r := (r : ℤ)) (by omega)
    hn0 hst hhor (B := B) (ε₁ := ε₁) (ε₂ := ε₂) (C := (2 * C₀ + 1) / 2)
    (β := ((LocSumAct.betaT (LocSumAct.xOf ((2 * Th + 4) * L)) : ℕ) : ℝ))
    hB hC1 hγC hε₁ hε₂ hK hside₁ hside₂ (bad := bad) (geom := geom) hcc hbadmeas
  convert hmain using 3
  rfl

end LocMoveCompose
