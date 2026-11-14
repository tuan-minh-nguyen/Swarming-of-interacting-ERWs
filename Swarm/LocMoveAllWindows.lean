/-
# `(locmove)` at *every* window length: the short-window branch closed

`LOC_MOVE_COMPOSE.md` records the restriction of the accepted paper-scale statement:

> At the paper's local scale the statement has an `L^(1/16)` exponent, but only for `L ≤ t−s`.
> Short windows are not covered by that instantiation.

This file removes the restriction.  The restriction comes from the Chernoff side condition
`ε ≤ 4 (t-s) B`.  `LocWindowSharp.measure_deviation_goodW_le_sharp` and
`LocWindowSharp.measure_max_abs_Lcum_window_le_sharp` prove the same two maximal deviation
bounds for **every** `ε > 0` (sharp conditional Hoeffding, no truncation of the exponential), with
the exponent improved from `-ε²/(4 K (2B)²)` to `-ε²/(2 K (2B)²)`.

Consequently the composition goes through unchanged, with the same carrier `locmoveGood`,
the same record window, the same `(loccoord)` bad set and the same error term
`max (3Cβ + ε₂) (gammaErr + ε₁)`, but without any hypothesis on `ε₁, ε₂`:

* `measure_locmove_le_all` — the composed `(locmove)` exceptional bound, no side condition;
* `exists_measure_locmove_total_all` — the same with `(loccoord)` instantiated;
* `exists_measure_locmove_paper_scale_all` — at `B = L^(1/16)`, `ε₁ = ε₂ = L^(3/4)`, for every
  window with `1 ≤ t-s ≤ (T+3)L`, with exponents `-(xOf L)^6/(8(T+3))` and
  `-(xOf L)^4/(800 N² (T+3))` and the same `(locsum)` term `exp(-c·xOf((2T+4)L))`.

What is *not* claimed: the measure of the carrier `locmoveGood` itself (GoodW/GoodStep
probability, record-containment, separation survival) is still unestimated, `(locsum)`
containment is carried inside the measured event, and no halving/tightness/invariant-law/
`MainClaim` statement is made here.  The model parameters `N ≥ 2`, `m ≥ 2`, `1/2 < p < 1` are
untouched, and nothing is assumed about them beyond what the accepted files already assume.

No `sorry`, no new axiom.
-/
import Swarm.LocWindowSharp
import Swarm.LocMoveCompose
import Swarm.PaperScale

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace WCJFSharp

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open LocMoveCompose SwarmJointDrift LocGroupQ LocGroupWindow LocMoveMart LocMoveLocal
open Swarming.Enl Loccoord

variable {N : ℕ}

/-! ## 0. Arithmetic: the doubled exponents at the paper's local scale -/

/-- `Γ`-half exponent with the sharp constant: `−(xOf L)^4/(800 N² (T+3))`. -/
theorem gamma_exponent_le_half {L K T : ℕ} (hL : 1 ≤ L) (hK : 1 ≤ K)
    (hKle : K ≤ (T + 3) * L)
    {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) (hN : 1 ≤ N) :
    -(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
        (2 * (K : ℝ) * (2 * stepEnv (N := N) p (LocSumAct.xOf L)) ^ 2)
      ≤ -((LocSumAct.xOf L) ^ 4 / (800 * ((N : ℝ) ^ 2 * ((T : ℝ) + 3)))) := by
  have h := LocMoveCompose.gamma_exponent_le (N := N) hL hK hKle hp0 hp1 hN
  have h2 : 2 * (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
        (4 * (K : ℝ) * (2 * stepEnv (N := N) p (LocSumAct.xOf L)) ^ 2))
      ≤ 2 * (-((LocSumAct.xOf L) ^ 4 / (1600 * ((N : ℝ) ^ 2 * ((T : ℝ) + 3))))) := by
    linarith
  have e1 : 2 * (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
        (4 * (K : ℝ) * (2 * stepEnv (N := N) p (LocSumAct.xOf L)) ^ 2))
      = -(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
        (2 * (K : ℝ) * (2 * stepEnv (N := N) p (LocSumAct.xOf L)) ^ 2) := by ring
  have e2 : 2 * (-((LocSumAct.xOf L) ^ 4 / (1600 * ((N : ℝ) ^ 2 * ((T : ℝ) + 3)))))
      = -((LocSumAct.xOf L) ^ 4 / (800 * ((N : ℝ) ^ 2 * ((T : ℝ) + 3)))) := by
    field_simp
    ring
  linarith [h2, e1, e2]

/-- Max-growth exponent with the sharp constant: `−(xOf L)^6/(8 (T+3))`. -/
theorem maxgrowth_exponent_le_half {L K T : ℕ} (hL : 1 ≤ L) (hK : 1 ≤ K)
    (hKle : K ≤ (T + 3) * L) :
    -(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) / (2 * (K : ℝ) * (2 * LocSumAct.xOf L) ^ 2)
      ≤ -((LocSumAct.xOf L) ^ 6 / (8 * ((T : ℝ) + 3))) := by
  have h := LocMoveCompose.maxgrowth_exponent_le hL hK hKle
  have h2 : 2 * (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) / (4 * (K : ℝ) * (2 * LocSumAct.xOf L) ^ 2))
      ≤ 2 * (-((LocSumAct.xOf L) ^ 6 / (16 * ((T : ℝ) + 3)))) := by linarith
  have e1 : 2 * (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) / (4 * (K : ℝ) * (2 * LocSumAct.xOf L) ^ 2))
      = -(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) / (2 * (K : ℝ) * (2 * LocSumAct.xOf L) ^ 2) := by ring
  have e2 : 2 * (-((LocSumAct.xOf L) ^ 6 / (16 * ((T : ℝ) + 3))))
      = -((LocSumAct.xOf L) ^ 6 / (8 * ((T : ℝ) + 3))) := by
    field_simp
    ring
  linarith [h2, e1, e2]

/-! ## 1. The composed `(locmove)` bound, every `ε > 0` -/

theorem measure_locmove_le_all {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    {Th Lh : ℕ} (hL : 1 ≤ Lh) {r : ℤ} (hr : (((Th + 3) * Lh : ℕ) : ℤ) ≤ r)
    {n0 s t : ℕ} (hn0 : n0 ≤ s) (hst : s ≤ t) (hhor : t ≤ n0 + (Th + 3) * Lh)
    {B ε₁ ε₂ C β : ℝ} (hB : 0 < B) (hC1 : 1 ≤ C) (hγC : 1 ≤ gammaRate p m A * C)
    (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (hK : 1 ≤ t - s)
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
          Real.exp (-(ε₁ ^ 2) / (2 * (((t - s : ℕ) : ℝ) * (2 * stepEnv (N := N) p B) ^ 2)))
        + 2 * (((t - s : ℕ) : ℝ) + 1) *
          Real.exp (-(ε₂ ^ 2) / (2 * (((t - s : ℕ) : ℝ) * (2 * B) ^ 2)))
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
  have hD₁b := measure_deviation_goodW_le_sharp (N := N) (m := m) hp0 hp1 A Aᶜ hA hAc hid hB (s := s) (K := K)
    (by rw [hK']; exact hK) hε₁
  have hD₂b := measure_max_abs_Lcum_window_le_sharp (N := N) hp0.le hp1.le m Aᶜ hAc hB (s := s)
    (K := K) (by rw [hK']; exact hK) hε₂
  have hD₂b' : (arrayMeasure N).real
        {U | ∃ k ≤ K, ε₂ ≤ |Lcum p m (s + k) Aᶜ hAc B U - Lcum p m s Aᶜ hAc B U|}
      ≤ 2 * ((K : ℝ) + 1) *
          Real.exp (-(ε₂ ^ 2) / (2 * ((K : ℝ) * (2 * B) ^ 2))) := hD₂b
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
          Real.exp (-(ε₁ ^ 2) / (2 * ((K : ℝ) * (2 * stepEnv (N := N) p B) ^ 2)))
        + 2 * ((K : ℝ) + 1) * Real.exp (-(ε₂ ^ 2) / (2 * ((K : ℝ) * (2 * B) ^ 2))) + eb := by
        simp only [hD₁, hD₂]
        linarith [hD₁b, hD₂b', hbad, hN0z]

/-! ## 2. `(locmove)` with the `(loccoord)` bad set instantiated, every `ε > 0` -/

theorem exists_measure_locmove_total_all {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    {C₀ : ℝ} (hC₀1 : 1 ≤ C₀) (hC₀M : LocSum.Mb p (LocSumAct.qOf p m) < C₀)
    (hγC : 1 ≤ gammaRate p m A * ((2 * C₀ + 1) / 2)) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ Th r : ℕ, (3 * Th + 6) * L ≤ r →
      ∀ {n0 s t : ℕ} (_hn0 : n0 ≤ s) (_hst : s ≤ t) (_hhor : t ≤ n0 + (Th + 3) * L)
        (_hr : (Th + 3) * L ≤ r)
        {B ε₁ ε₂ : ℝ}, 0 < B → 0 < ε₁ → 0 < ε₂ → 1 ≤ t - s →
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
            Real.exp (-(ε₁ ^ 2) / (2 * (((t - s : ℕ) : ℝ) * (2 * stepEnv (N := N) p B) ^ 2)))
          + 2 * (((t - s : ℕ) : ℝ) + 1) *
            Real.exp (-(ε₂ ^ 2) / (2 * (((t - s : ℕ) : ℝ) * (2 * B) ^ 2)))
          + Real.exp (-c * LocSumAct.xOf ((2 * Th + 4) * L)) := by
  haveI hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  obtain ⟨c, hc, L₀, hLL⟩ :=
    Loccoord.loccoord_full_window (N := N) hp0 hp1 hm hC₀1 hC₀M
  refine ⟨c, hc, max L₀ 1, ?_⟩
  intro L hLbig Th r hr n0 s t hn0 hst hhor hr' B ε₁ ε₂ hB hε₁ hε₂ hK
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
  have hmain := measure_locmove_le_all (N := N) hp0 hp1 (le_trans (by norm_num : 1 ≤ 2) hm) A hA hAc
    (Th := Th) (Lh := L) (by omega) (r := (r : ℤ)) (by omega)
    hn0 hst hhor (B := B) (ε₁ := ε₁) (ε₂ := ε₂) (C := (2 * C₀ + 1) / 2)
    (β := ((LocSumAct.betaT (LocSumAct.xOf ((2 * Th + 4) * L)) : ℕ) : ℝ))
    hB hC1 hγC hε₁ hε₂ hK (bad := bad) (geom := geom) hcc hbadmeas
  convert hmain using 3
  rfl

/-! ## 3. Paper scale, every window length `1 ≤ t-s ≤ (T+3)L` -/

theorem exists_measure_locmove_paper_scale_all {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    (hN : 1 ≤ N) {C₀ : ℝ} (hC₀1 : 1 ≤ C₀) (hC₀M : LocSum.Mb p (LocSumAct.qOf p m) < C₀)
    (hγC : 1 ≤ gammaRate p m A * ((2 * C₀ + 1) / 2)) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ T r : ℕ, (3 * T + 6) * L ≤ r →
      ∀ {n0 s t : ℕ} (_hn0 : n0 ≤ s) (_hst : s ≤ t) (_hhor : t ≤ n0 + (T + 3) * L)
        (_hr : (T + 3) * L ≤ r) (_hK : 1 ≤ t - s),
      (arrayMeasure N).real
        {U : Array N |
          locmoveGood (N := N) p m A hA (r : ℤ) T L (LocSumAct.xOf L) n0 s t U ∧
            (0 ≤ Xmin p m U A hA s ∧
              r - (T + 2) * L ≤ (Xmin p m U A hA s).toNat ∧
              (Rmax p m U A hA t).toNat ≤ r + (T + 2) * L) ∧
            ¬ (WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
                ≤ locmoveRHS (N := N) p m A hA L ((2 * C₀ + 1) / 2)
                    ((LocSumAct.betaT (LocSumAct.xOf ((2 * T + 4) * L)) : ℕ) : ℝ)
                    ((L : ℝ) ^ (3 / 4 : ℝ)) ((L : ℝ) ^ (3 / 4 : ℝ)) s t U)}
        ≤ 2 * (((t - s : ℕ) : ℝ) + 1) *
            Real.exp (-((LocSumAct.xOf L) ^ 6 / (8 * ((T : ℝ) + 3))))
          + 2 * (((t - s : ℕ) : ℝ) + 1) *
            Real.exp (-((LocSumAct.xOf L) ^ 4 / (800 * ((N : ℝ) ^ 2 * ((T : ℝ) + 3)))))
          + Real.exp (-c * LocSumAct.xOf ((2 * T + 4) * L)) := by
  obtain ⟨c, hc, L₀, htot⟩ :=
    exists_measure_locmove_total_all (N := N) hp0 hp1 hm A hA hAc hC₀1 hC₀M hγC
  refine ⟨c, hc, max L₀ 1, ?_⟩
  intro L hLbig T r hr n0 s t hn0 hst hhor hr' hK
  have hL0 : L₀ ≤ L := le_trans (le_max_left _ _) hLbig
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hLbig
  have hK1 : 1 ≤ t - s := hK
  have hKle : t - s ≤ (T + 3) * L := by omega
  have hx1 : (1 : ℝ) ≤ LocSumAct.xOf L := LocSumAct.one_le_xOf hL1
  have hB : (0 : ℝ) < LocSumAct.xOf L := by linarith
  have hLr : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL1)
  have hε : (0 : ℝ) < (L : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hLr _
  have hmain := htot L hL0 T r hr hn0 hst hhor hr' (B := LocSumAct.xOf L) hB hε hε hK1
  have hE₁ : Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
        (2 * (((t - s : ℕ) : ℝ) * (2 * stepEnv (N := N) p (LocSumAct.xOf L)) ^ 2)))
      ≤ Real.exp (-((LocSumAct.xOf L) ^ 4 / (800 * ((N : ℝ) ^ 2 * ((T : ℝ) + 3))))) := by
    apply Real.exp_le_exp.mpr
    have h2 : (2 * (((t - s : ℕ) : ℝ) * (2 * stepEnv (N := N) p (LocSumAct.xOf L)) ^ 2))
        = 2 * ((t - s : ℕ) : ℝ) * (2 * stepEnv (N := N) p (LocSumAct.xOf L)) ^ 2 := by ring
    rw [h2]
    exact gamma_exponent_le_half (N := N) hL1 hK1 hKle hp0 hp1.le hN
  have hE₂ : Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
        (2 * (((t - s : ℕ) : ℝ) * (2 * LocSumAct.xOf L) ^ 2)))
      ≤ Real.exp (-((LocSumAct.xOf L) ^ 6 / (8 * ((T : ℝ) + 3)))) := by
    apply Real.exp_le_exp.mpr
    have h2 : (2 * (((t - s : ℕ) : ℝ) * (2 * LocSumAct.xOf L) ^ 2))
        = 2 * ((t - s : ℕ) : ℝ) * (2 * LocSumAct.xOf L) ^ 2 := by ring
    rw [h2]
    exact maxgrowth_exponent_le_half hL1 hK1 hKle
  calc (arrayMeasure N).real
        {U : Array N |
          locmoveGood (N := N) p m A hA (r : ℤ) T L (LocSumAct.xOf L) n0 s t U ∧
            (0 ≤ Xmin p m U A hA s ∧
              r - (T + 2) * L ≤ (Xmin p m U A hA s).toNat ∧
              (Rmax p m U A hA t).toNat ≤ r + (T + 2) * L) ∧
            ¬ (WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
                ≤ locmoveRHS (N := N) p m A hA L ((2 * C₀ + 1) / 2)
                    ((LocSumAct.betaT (LocSumAct.xOf ((2 * T + 4) * L)) : ℕ) : ℝ)
                    ((L : ℝ) ^ (3 / 4 : ℝ)) ((L : ℝ) ^ (3 / 4 : ℝ)) s t U)}
      ≤ 2 * (((t - s : ℕ) : ℝ) + 1) *
            Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
              (2 * (((t - s : ℕ) : ℝ) * (2 * stepEnv (N := N) p (LocSumAct.xOf L)) ^ 2)))
          + 2 * (((t - s : ℕ) : ℝ) + 1) *
            Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
              (2 * (((t - s : ℕ) : ℝ) * (2 * LocSumAct.xOf L) ^ 2)))
          + Real.exp (-c * LocSumAct.xOf ((2 * T + 4) * L)) := hmain
    _ ≤ 2 * (((t - s : ℕ) : ℝ) + 1) *
            Real.exp (-((LocSumAct.xOf L) ^ 6 / (8 * ((T : ℝ) + 3))))
          + 2 * (((t - s : ℕ) : ℝ) + 1) *
            Real.exp (-((LocSumAct.xOf L) ^ 4 / (800 * ((N : ℝ) ^ 2 * ((T : ℝ) + 3)))))
          + Real.exp (-c * LocSumAct.xOf ((2 * T + 4) * L)) := by
        nlinarith [hE₁, hE₂,
          Real.exp_pos (-((LocSumAct.xOf L) ^ 6 / (8 * ((T : ℝ) + 3)))),
          Real.exp_pos (-((LocSumAct.xOf L) ^ 4 / (800 * ((N : ℝ) ^ 2 * ((T : ℝ) + 3))))),
          Real.exp_pos (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
              (2 * (((t - s : ℕ) : ℝ) * (2 * stepEnv (N := N) p (LocSumAct.xOf L)) ^ 2))),
          Real.exp_pos (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
              (2 * (((t - s : ℕ) : ℝ) * (2 * LocSumAct.xOf L) ^ 2)))]

end WCJFSharp
