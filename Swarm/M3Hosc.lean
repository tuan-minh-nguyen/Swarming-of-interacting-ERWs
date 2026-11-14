/-
  # Site-indexed oscillation of the projected potential at the record window

  The paper's `(locmart)` paragraph of Proposition `local` uses the *site-indexed* martingales
  `H_{j,n}(z) = E[H_j(z) | F_n]` for the `O_T(L)` deterministic integers `z` of the record
  window and claims

      |H_{j,t}(z) - H_{j,s}(z)| <= C_T L^{3/4}   for all  tau_r <= s <= t <= tau_r + floor (T L),

  outside an event of probability `C_T e^{-c_T L^{1/16}}`.  This is precisely the `hosc` field of
  `LocOcc.lococc_window` (`H t (X s) - H s (X s) <= CH * L34`, evaluated at the walker's own
  starting site `X_s^i`).

  `SiteHMax.measure_sup_siteH_window_scale` proves that bound with the martingale started at
  the **deterministic time zero**.  The record window starts at the random record time `tau_r`,
  so that statement cannot be applied: restarting at `tau_r` is the whole content of the
  estimate.  This file supplies the *shifted* version, using

  * `ShiftedQplResidual.measureReal_cell_max_abs_shift_le_of_ptrunc_ae` — the deterministic
    start `s`, cell-weighted maximal Azuma bound with an a.e. predictable envelope;
  * `SiteHMax.Hinc` / `SiteHMax.siteGood` / `ae_abs_Hinc_le_of_good` — the actual increment,
    its predictable good event and its envelope `capB`.

  What is proved (all at the actual model `Swarming.Uniform.arrayMeasure N`, `1/2 < p < 1`,
  `2 <= m`, no restriction relating `m`, `N` beyond the model's own `Nonempty`/`Fin N`):

  * `sum_Ico_Hinc_eq`, `psum_Hinc_sub`: the partial sums of the site-indexed increment are the
    differences of `projH` at the two times — no probability, no adaptedness input;
  * `measureReal_cell_siteOsc_le_sharp`: at a fixed site `y`, on a `F_s`-measurable cell `A`,
    the shifted maximal oscillation of `H_{j,·}(y)` from the deterministic start `s` is bounded
    by `mu.real A * 2 (n+1) exp (-δ² / (4 n capB²))` **on the event that the predictable
    truncation never fires** (`∀ k < n, siteGood (s+k)`);
  * `measureReal_cell_siteOsc_le`: the same with the truncation residual `A ∩ {∃ k < n, ¬
    siteGood (s+k)}` added outside the exponential term;
  * `measureReal_cell_siteOsc_pair_le`: the two-sided form `ε <= |H_v(y) - H_u(y)|` over all
    pairs `s <= u <= v <= s+n` (factor `2` in the threshold, hence `16` in the exponent);
  * `measureReal_cell_supSiteOsc_pair_le`: the union bound over a finite site set, with the
    truncation residual charged exactly once (not once per site);
  * `siteGood_of_shift_window`: on the shifted record window the truncation never fires, so the
    residual is a purely geometric event;
  * `measureReal_recordWindow_supSiteOsc`: the record-window form, where the residual is
    discharged by the record containment and `(locmax)`; and
  * `measureReal_recordWindow_hosc`: the `hosc`-shaped corollary at the walker's own site
    `X_s^i`, with the paper's scale `V = L^{1/16}`, `n = T L`, `ε = L^{3/4}`.

  Not claimed here: `(locsum)`, the record-cost structure `hJstruct`, the above-record slope
  `hslopeHi`, the endpoint `F` bounds, or the assembled `(lococc)`.  Those are the remaining
  fields of `LocOcc.lococc_window`; see `README.md` for their exact status.  No `sorry`, no
  custom axiom, no `native_decide`.
-/
import Swarm.SiteHMax
import Swarm.ShiftedQplResidual
import Swarm.WideLocMaxG

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

namespace M3Hosc

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory Swarming.Enl SwarmCross

variable {N : ℕ}

/-! ### 1. Partial sums of the site-indexed increment -/

/-- **The site-indexed increments telescope to the potential difference.**
`∑_{t ∈ Ico a b} (H_{j,t+1}(y) - H_{j,t}(y)) = H_{j,b}(y) - H_{j,a}(y)`. -/
theorem sum_Ico_Hinc_eq (p : ℝ) (m : ℕ) (j : Fin N) (y : ℤ) {a b : ℕ} (hab : a ≤ b)
    (U : Array N) :
    ∑ t ∈ Finset.Ico a b, SiteHMax.Hinc p m j y t U
      = projH p m j b U y - projH p m j a U y := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
      rw [Finset.sum_Ico_succ_top (by omega) (f := fun t => SiteHMax.Hinc p m j y t U), ih]
      show (projH p m j b U y - projH p m j a U y)
          + (projH p m j (b + 1) U y - projH p m j b U y)
        = projH p m j (b + 1) U y - projH p m j a U y
      ring

/-- **The shifted partial-sum difference is the `projH` increment.** -/
theorem psum_Hinc_sub (p : ℝ) (m : ℕ) (j : Fin N) (y : ℤ) (s k : ℕ) (U : Array N) :
    LocMart.psum (SiteHMax.Hinc p m j y) (s + k) U
        - LocMart.psum (SiteHMax.Hinc p m j y) s U
      = projH p m j (s + k) U y - projH p m j s U y := by
  have hsub : LocMart.psum (SiteHMax.Hinc p m j y) (s + k) U
        - LocMart.psum (SiteHMax.Hinc p m j y) s U
      = ∑ t ∈ Finset.Ico s (s + k), SiteHMax.Hinc p m j y t U := by
    unfold LocMart.psum
    rw [← Finset.sum_Ico_eq_sub (f := fun t => SiteHMax.Hinc p m j y t U) (Nat.le_add_right s k)]
  rw [hsub, sum_Ico_Hinc_eq p m j y (Nat.le_add_right s k)]

/-- The shifted oscillation event in `projH` form is the partial-sum event. -/
theorem siteOsc_set_eq (p : ℝ) (m : ℕ) (j : Fin N) (y : ℤ) (s : ℕ) (n : ℕ) (δ : ℝ) :
    {U : Array N | ∃ k ≤ n, δ ≤ |projH p m j (s + k) U y - projH p m j s U y|}
      = {U : Array N | ∃ k ≤ n,
          δ ≤ |LocMart.psum (SiteHMax.Hinc p m j y) (s + k) U
            - LocMart.psum (SiteHMax.Hinc p m j y) s U|} := by
  ext U
  constructor
  · rintro ⟨k, hk, h⟩
    exact ⟨k, hk, by rwa [psum_Hinc_sub p m j y s k U]⟩
  · rintro ⟨k, hk, h⟩
    exact ⟨k, hk, by rwa [psum_Hinc_sub p m j y s k U] at h⟩

/-! ### 2. The shifted maximal oscillation at one fixed site -/

/-- On the good event the truncated and untruncated shifted partial-sum differences agree. -/
theorem psum_siteInc_eq_of_good (p : ℝ) (m : ℕ) (j : Fin N) (V : ℝ) (y : ℤ) (s n : ℕ)
    (U : Array N) (hgood : ∀ k < n, U ∈ SiteHMax.siteGood p m j V (s + k)) {k : ℕ}
    (hk : k ≤ n) :
    LocMart.psum (SiteHMax.siteInc p m j V y) (s + k) U
        - LocMart.psum (SiteHMax.siteInc p m j V y) s U
      = projH p m j (s + k) U y - projH p m j s U y := by
  rw [← psum_Hinc_sub p m j y s k U]
  unfold LocMart.psum
  rw [← Finset.sum_Ico_eq_sub
      (f := fun t => SiteHMax.siteInc p m j V y t U) (Nat.le_add_right s k),
    ← Finset.sum_Ico_eq_sub (f := fun t => SiteHMax.Hinc p m j y t U) (Nat.le_add_right s k)]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hge : s ≤ t := (Finset.mem_Ico.mp ht).1
  have hlt : t < s + k := (Finset.mem_Ico.mp ht).2
  have hts : t - s < n := by omega
  have heq : s + (t - s) = t := Nat.add_sub_cancel' hge
  unfold SiteHMax.siteInc
  rw [← heq]
  exact Set.indicator_of_mem (hgood (t - s) hts) _

/-- **Shifted site-indexed maximal oscillation, on the event that the predictable truncation
never fires.**

For a `F_s`-measurable cell `A`, a level `V ≥ 0`, a horizon `n ≥ 1` and a deviation `δ > 0`,

  `mu.real (A ∩ {∀ k < n, h_j(M_{s+k}^j - 1) ≤ V} ∩
        {∃ k ≤ n, δ ≤ |H_{j,s+k}(y) - H_{j,s}(y)|})
    ≤ mu.real A · 2 (n+1) exp (-δ² / (4 n (capB V)²))`.

The start time `s` is deterministic and the cell `A` carries the randomness of the record
conditioning; no future law is used.  The proof applies the shifted maximal Azuma bound to the
*predictably truncated* increment `siteInc`, whose envelope `capB` holds almost everywhere (so
no residual is charged), and then compares it with `Hinc` on the good event. -/
theorem measureReal_cell_siteOsc_le_sharp {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m : ℕ) (j : Fin N) (y : ℤ) {s : ℕ} {A : Set (Array N)}
    (hA : MeasurableSet[enlFilt p m s] A) {V : ℝ} (hV : 0 ≤ V)
    {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) :
    (arrayMeasure N).real
        (A ∩ {U | ∀ k < n, U ∈ SiteHMax.siteGood p m j V (s + k)} ∩
          {U | ∃ k ≤ n, δ ≤ |projH p m j (s + k) U y - projH p m j s U y|})
      ≤ (arrayMeasure N).real A *
          (2 * ((n : ℝ) + 1) *
            Real.exp (-(δ ^ 2) / (4 * (n : ℝ) * (SiteHMax.capB p m V) ^ 2))) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hpne : p ≠ 0 := by linarith
  have hCpos : 0 < SiteHMax.capB p m V := SiteHMax.capB_pos hp0 hp1 m hV
  have hG : ∀ k : ℕ, MeasurableSet[enlFilt p m (s + k)] (Set.univ : Set (Array N)) :=
    fun k => MeasurableSet.univ
  have hξm : ∀ k : ℕ, StronglyMeasurable[enlFilt p m (s + k + 1)]
      (SiteHMax.siteInc p m j V y (s + k)) := fun k =>
    SiteHMax.stronglyMeasurable_siteInc hp0.le m (s + k) j V y
  have hξi : ∀ k : ℕ, Integrable (SiteHMax.siteInc p m j V y (s + k)) (arrayMeasure N) := by
    intro k
    refine Integrable.of_bound (SiteHMax.stronglyMeasurable_siteInc hp0.le m (s + k) j V y
      |>.mono ((enlFilt p m).le (s + k + 1))).aestronglyMeasurable
      (SiteHMax.capB p m V) ?_
    filter_upwards [SiteHMax.ae_abs_siteInc_le (p := p) hp0 hp1 m (s + k) j y hV] with U hU
    simpa only [Real.norm_eq_abs] using hU
  have hξ0 : ∀ k : ℕ, (arrayMeasure N)[SiteHMax.siteInc p m j V y (s + k) |
      ↑(enlFilt p m (s + k))] =ᵐ[arrayMeasure N] 0 := fun k =>
    SiteHMax.condExp_siteInc_eq_zero hp0 hp1 hpne m (s + k) j V y
  have hbdd : ∀ k : ℕ, ∀ᵐ U ∂(arrayMeasure N),
      U ∈ (Set.univ : Set (Array N)) →
        |SiteHMax.siteInc p m j V y (s + k) U| ≤ SiteHMax.capB p m V := by
    intro k
    filter_upwards [SiteHMax.ae_abs_siteInc_le (p := p) hp0 hp1 m (s + k) j y hV] with U hU _
    exact hU
  have hmain := ShiftedQplResidual.measureReal_cell_max_abs_shift_le_of_ptrunc_ae
    (μ := arrayMeasure N) (ℱ := enlFilt p m) (s := s) (A := A) hA
    (G := fun _ => Set.univ) hG
    (ξ := SiteHMax.siteInc p m j V y) hξm hξi hξ0 hCpos hbdd hn hδ
  have hres : (A ∩ {U : Array N | ∃ k < n, U ∉ (Set.univ : Set (Array N))}) = ∅ := by
    ext U
    simp
  rw [hres, measureReal_empty, add_zero] at hmain
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) hmain
  rintro U ⟨⟨hUA, hgood⟩, k, hk, hdev⟩
  exact ⟨hUA, k, hk, by
    rw [psum_siteInc_eq_of_good p m j V y s n U hgood hk]
    exact hdev⟩

/-- **Shifted site-indexed maximal oscillation with the truncation residual.**  The residual
`{∃ k < n, ¬ siteGood (s+k)}` is an `F_{s+n-1}`-measurable event and is charged once, outside
the exponential term. -/
theorem measureReal_cell_siteOsc_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m : ℕ) (j : Fin N) (y : ℤ) {s : ℕ} {A : Set (Array N)}
    (hA : MeasurableSet[enlFilt p m s] A) {V : ℝ} (hV : 0 ≤ V)
    {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) :
    (arrayMeasure N).real
        (A ∩ {U | ∃ k ≤ n, δ ≤ |projH p m j (s + k) U y - projH p m j s U y|})
      ≤ (arrayMeasure N).real A *
          (2 * ((n : ℝ) + 1) *
            Real.exp (-(δ ^ 2) / (4 * (n : ℝ) * (SiteHMax.capB p m V) ^ 2)))
        + (arrayMeasure N).real
            (A ∩ {U | ∃ k < n, U ∉ SiteHMax.siteGood p m j V (s + k)}) := by
  set G : Set (Array N) := {U | ∀ k < n, U ∈ SiteHMax.siteGood p m j V (s + k)} with hGdef
  set bad : Set (Array N) :=
    {U | ∃ k ≤ n, δ ≤ |projH p m j (s + k) U y - projH p m j s U y|} with hbad
  have hsub : A ∩ bad ⊆ (A ∩ G ∩ bad) ∪
      (A ∩ {U | ∃ k < n, U ∉ SiteHMax.siteGood p m j V (s + k)}) := by
    intro U hU
    by_cases hmem : U ∈ G
    · exact Or.inl ⟨⟨hU.1, hmem⟩, hU.2⟩
    · refine Or.inr ⟨hU.1, ?_⟩
      simp only [G, Set.mem_ofPred_eq, not_forall] at hmem
      obtain ⟨k, hk, hkbad⟩ := hmem
      exact ⟨k, hk, hkbad⟩
  have h1 : (arrayMeasure N).real (A ∩ bad)
      ≤ (arrayMeasure N).real (A ∩ G ∩ bad)
        + (arrayMeasure N).real (A ∩ {U | ∃ k < n, U ∉ SiteHMax.siteGood p m j V (s + k)}) :=
    (measureReal_mono hsub (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  have h2 : (arrayMeasure N).real (A ∩ G ∩ bad)
      ≤ (arrayMeasure N).real A *
          (2 * ((n : ℝ) + 1) *
            Real.exp (-(δ ^ 2) / (4 * (n : ℝ) * (SiteHMax.capB p m V) ^ 2))) :=
    measureReal_cell_siteOsc_le_sharp hp0 hp1 m j y hA hV hn hδ
  linarith [h1, h2]

/-! ### 3. The two-sided form over pairs of times -/

/-- **Every pair in the window is controlled by the shifted maximal oscillation.**  If
`ε ≤ |H_v(y) - H_u(y)|` for some `s ≤ u ≤ v ≤ s+n`, then the shifted maximum from `s`
exceeds `ε/2`. -/
theorem pairOsc_subset_shiftOsc (p : ℝ) (m : ℕ) (j : Fin N) (y : ℤ) (s n : ℕ) {ε : ℝ} :
    {U : Array N | ∃ u v : ℕ, s ≤ u ∧ u ≤ v ∧ v ≤ s + n ∧
        ε ≤ |projH p m j v U y - projH p m j u U y|}
      ⊆ {U : Array N | ∃ k ≤ n, ε / 2 ≤ |projH p m j (s + k) U y - projH p m j s U y|} := by
  rintro U ⟨u, v, hsu, huv, hvn, hdev⟩
  set a := projH p m j v U y - projH p m j s U y with ha
  set b := projH p m j u U y - projH p m j s U y with hb
  have hdiff : projH p m j v U y - projH p m j u U y = a - b := by rw [ha, hb]; ring
  have htri : |a - b| ≤ |a| + |b| := by
    rw [abs_le]
    constructor <;> linarith [le_abs_self a, neg_abs_le a, le_abs_self b, neg_abs_le b]
  have hε : ε ≤ |a| + |b| := by rw [hdiff] at hdev; linarith
  rcases le_or_gt (ε / 2) |a| with h | h
  · refine ⟨v - s, by omega, ?_⟩
    have hv : s + (v - s) = v := Nat.add_sub_cancel' (le_trans hsu huv)
    rw [hv]
    exact h
  · have hb' : ε / 2 ≤ |b| := by
      have : |a| < ε / 2 := h
      linarith
    refine ⟨u - s, by omega, ?_⟩
    have hu : s + (u - s) = u := Nat.add_sub_cancel' hsu
    rw [hu]
    exact hb'

/-- **Shifted two-sided oscillation of `H_{j,·}(y)` over all pairs in a window, on the
non-firing event** (the pair form of `measureReal_cell_siteOsc_le_sharp`). -/
theorem measureReal_cell_siteOsc_pair_le_sharp {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m : ℕ) (j : Fin N) (y : ℤ) {s : ℕ} {A : Set (Array N)}
    (hA : MeasurableSet[enlFilt p m s] A) {V : ℝ} (hV : 0 ≤ V)
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    (arrayMeasure N).real
        (A ∩ {U | ∀ k < n, U ∈ SiteHMax.siteGood p m j V (s + k)} ∩
          {U | ∃ u v : ℕ, s ≤ u ∧ u ≤ v ∧ v ≤ s + n ∧
            ε ≤ |projH p m j v U y - projH p m j u U y|})
      ≤ (arrayMeasure N).real A *
          (2 * ((n : ℝ) + 1) *
            Real.exp (-(ε ^ 2) / (16 * (n : ℝ) * (SiteHMax.capB p m V) ^ 2))) := by
  have hδ : 0 < ε / 2 := by linarith
  have h := measureReal_cell_siteOsc_le_sharp (p := p) hp0 hp1 m j y hA hV hn hδ
  have hexp : -((ε / 2) ^ 2) / (4 * (n : ℝ) * (SiteHMax.capB p m V) ^ 2)
      = -(ε ^ 2) / (16 * (n : ℝ) * (SiteHMax.capB p m V) ^ 2) := by
    have hnum : (ε / 2) ^ 2 = ε ^ 2 / 4 := by ring
    rw [hnum]
    have hC : (SiteHMax.capB p m V) ^ 2 ≠ 0 := by
      have := (SiteHMax.capB_pos hp0 hp1 m hV).ne'
      positivity
    have hn' : (n : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    field_simp
    ring
  rw [hexp] at h
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) h
  rintro U ⟨⟨hUA, hgood⟩, hbad⟩
  exact ⟨⟨hUA, hgood⟩, pairOsc_subset_shiftOsc p m j y s n hbad⟩

/-- **Shifted two-sided oscillation of `H_{j,·}(y)` over all pairs in a window**, with the
deviation `ε` (not `ε/2`) and the resulting factor `16` in the exponent. -/
theorem measureReal_cell_siteOsc_pair_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m : ℕ) (j : Fin N) (y : ℤ) {s : ℕ} {A : Set (Array N)}
    (hA : MeasurableSet[enlFilt p m s] A) {V : ℝ} (hV : 0 ≤ V)
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    (arrayMeasure N).real
        (A ∩ {U | ∃ u v : ℕ, s ≤ u ∧ u ≤ v ∧ v ≤ s + n ∧
          ε ≤ |projH p m j v U y - projH p m j u U y|})
      ≤ (arrayMeasure N).real A *
          (2 * ((n : ℝ) + 1) *
            Real.exp (-(ε ^ 2) / (16 * (n : ℝ) * (SiteHMax.capB p m V) ^ 2)))
        + (arrayMeasure N).real
            (A ∩ {U | ∃ k < n, U ∉ SiteHMax.siteGood p m j V (s + k)}) := by
  have hδ : 0 < ε / 2 := by linarith
  have h := measureReal_cell_siteOsc_le (p := p) hp0 hp1 m j y hA hV hn hδ
  have hexp : -((ε / 2) ^ 2) / (4 * (n : ℝ) * (SiteHMax.capB p m V) ^ 2)
      = -(ε ^ 2) / (16 * (n : ℝ) * (SiteHMax.capB p m V) ^ 2) := by
    have hnum : (ε / 2) ^ 2 = ε ^ 2 / 4 := by ring
    rw [hnum]
    have hC : (SiteHMax.capB p m V) ^ 2 ≠ 0 := by
      have := (SiteHMax.capB_pos hp0 hp1 m hV).ne'
      positivity
    have hn' : (n : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    field_simp
    ring
  rw [hexp] at h
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) h
  rintro U ⟨hUA, hbad⟩
  exact ⟨hUA, pairOsc_subset_shiftOsc p m j y s n hbad⟩

end M3Hosc

namespace M3Hosc

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory Swarming.Enl SwarmCross

variable {N : ℕ}

/-! ### 4. The union bound over the site window -/

/-- **Shifted site-window oscillation with the truncation residual charged once.**  For a finite
deterministic site set `S` the supremum over `S` costs exactly `S.card` exponential terms; the
truncation residual `{∃ k < n, ¬ siteGood (s+k)}` is shared by all sites and is therefore charged
once, outside the cardinality factor. -/
theorem measureReal_cell_supSiteOsc_pair_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m : ℕ) (j : Fin N) (S : Finset ℕ) {s : ℕ} {n : ℕ} (hn : 1 ≤ n) {A : Set (Array N)}
    (hA : MeasurableSet[enlFilt p m s] A) {V : ℝ} (hV : 0 ≤ V) {ε : ℝ} (hε : 0 < ε) :
    (arrayMeasure N).real
        (A ∩ {U | ∃ y ∈ S, ∃ u v : ℕ, s ≤ u ∧ u ≤ v ∧ v ≤ s + n ∧
          ε ≤ |projH p m j v U ((y : ℕ) : ℤ) - projH p m j u U ((y : ℕ) : ℤ)|})
      ≤ (S.card : ℝ) * ((arrayMeasure N).real A *
            (2 * ((n : ℝ) + 1) *
              Real.exp (-(ε ^ 2) / (16 * (n : ℝ) * (SiteHMax.capB p m V) ^ 2))))
        + (arrayMeasure N).real
            (A ∩ {U | ∃ k < n, U ∉ SiteHMax.siteGood p m j V (s + k)}) := by
  classical
  set G : Set (Array N) := {U | ∀ k < n, U ∈ SiteHMax.siteGood p m j V (s + k)} with hGdef
  set R : Set (Array N) := {U | ∃ k < n, U ∉ SiteHMax.siteGood p m j V (s + k)} with hRdef
  set bad : ℕ → Set (Array N) := fun y => {U | ∃ u v : ℕ, s ≤ u ∧ u ≤ v ∧ v ≤ s + n ∧
      ε ≤ |projH p m j v U ((y : ℕ) : ℤ) - projH p m j u U ((y : ℕ) : ℤ)|} with hbaddef
  have hsub : (A ∩ {U | ∃ y ∈ S, U ∈ bad y}) ⊆
      (A ∩ R) ∪ ⋃ y ∈ S, (A ∩ G ∩ bad y) := by
    intro U hU
    obtain ⟨hUA, y, hy, hbad⟩ := hU
    by_cases hmem : U ∈ G
    · exact Or.inr (Set.mem_biUnion hy ⟨⟨hUA, hmem⟩, hbad⟩)
    · refine Or.inl ⟨hUA, ?_⟩
      simp only [G, Set.mem_ofPred_eq, not_forall] at hmem
      obtain ⟨k, hk, hkbad⟩ := hmem
      exact ⟨k, hk, hkbad⟩
  have h1 : (arrayMeasure N).real (A ∩ {U | ∃ y ∈ S, U ∈ bad y})
      ≤ (arrayMeasure N).real (A ∩ R)
        + (arrayMeasure N).real (⋃ y ∈ S, (A ∩ G ∩ bad y)) := by
    have h2 := measureReal_mono hsub (measure_ne_top (arrayMeasure N) _)
    have h3 := measureReal_union_le (μ := arrayMeasure N) (A ∩ R)
      (⋃ y ∈ S, (A ∩ G ∩ bad y))
    linarith [h2, h3]
  have h4 : (arrayMeasure N).real (⋃ y ∈ S, (A ∩ G ∩ bad y))
      ≤ ∑ y ∈ S, (arrayMeasure N).real (A ∩ G ∩ bad y) :=
    measureReal_biUnion_finset_le (μ := arrayMeasure N) S (fun y => A ∩ G ∩ bad y)
  have h5 : ∀ y ∈ S, (arrayMeasure N).real (A ∩ G ∩ bad y)
      ≤ (arrayMeasure N).real A *
          (2 * ((n : ℝ) + 1) *
            Real.exp (-(ε ^ 2) / (16 * (n : ℝ) * (SiteHMax.capB p m V) ^ 2))) :=
    fun y _ => measureReal_cell_siteOsc_pair_le_sharp (p := p) hp0 hp1 m j ((y : ℕ) : ℤ)
      hA hV hn hε
  have h6 : (∑ y ∈ S, (arrayMeasure N).real (A ∩ G ∩ bad y))
      ≤ (S.card : ℝ) * ((arrayMeasure N).real A *
          (2 * ((n : ℝ) + 1) *
            Real.exp (-(ε ^ 2) / (16 * (n : ℝ) * (SiteHMax.capB p m V) ^ 2)))) := by
    calc (∑ y ∈ S, (arrayMeasure N).real (A ∩ G ∩ bad y))
        ≤ ∑ _y ∈ S, ((arrayMeasure N).real A *
            (2 * ((n : ℝ) + 1) *
              Real.exp (-(ε ^ 2) / (16 * (n : ℝ) * (SiteHMax.capB p m V) ^ 2)))) :=
          Finset.sum_le_sum h5
      _ = (S.card : ℝ) * ((arrayMeasure N).real A *
            (2 * ((n : ℝ) + 1) *
              Real.exp (-(ε ^ 2) / (16 * (n : ℝ) * (SiteHMax.capB p m V) ^ 2)))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have h7 : (arrayMeasure N).real (A ∩ {U | ∃ k < n, U ∉ SiteHMax.siteGood p m j V (s + k)})
      = (arrayMeasure N).real (A ∩ R) := by rw [hRdef]
  rw [h7]
  have h8 := le_trans h1 (add_le_add le_rfl (h4.trans h6))
  show (arrayMeasure N).real (A ∩ {U | ∃ y ∈ S, U ∈ bad y}) ≤
    (S.card : ℝ) * ((arrayMeasure N).real A *
          (2 * ((n : ℝ) + 1) *
            Real.exp (-(ε ^ 2) / (16 * (n : ℝ) * (SiteHMax.capB p m V) ^ 2))))
      + (arrayMeasure N).real (A ∩ R)
  linarith [h8]

/-! ### 5. The truncation never fires on the shifted record window -/

/-- **On the shifted record window every predictable truncation event holds.**  If the running
record `M_{s+k}^j` stays inside `[A, A+M)` for `k < n` and `h_j ≤ V` on the whole site window
`[A-1, A+M)`, then `h_j(M_{s+k}^j - 1) ≤ V` for every `k < n`, i.e. `siteGood (s+k)` holds.
`h_j` is a time-independent functional of the array, which is why one `(locmax)` event controls
the whole time window. -/
theorem siteGood_of_shift_window {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m : ℕ) (j : Fin N) {A M n s : ℕ} (hA : 1 ≤ A) {V : ℝ} {U : Array N}
    (hrec : ∀ k < n, A ≤ (recVal j (prefOf p m (s + k) U)).toNat ∧
      (recVal j (prefOf p m (s + k) U)).toNat < A + M)
    (hh : ∀ y ∈ Finset.Ico (A - 1) (A + M),
      SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) y ≤ V)
    {k : ℕ} (hk : k < n) : U ∈ SiteHMax.siteGood p m j V (s + k) := by
  obtain ⟨hlo, hhi⟩ := hrec k hk
  have hk0 : (recVal j (prefOf p m (s + k) U)).toNat ≠ 0 := by omega
  have hmem : (recVal j (prefOf p m (s + k) U)).toNat - 1 ∈ Finset.Ico (A - 1) (A + M) :=
    Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hH : HprevAt p m (s + k) j U
      = SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
          ((recVal j (prefOf p m (s + k) U)).toNat - 1) := by
    unfold HprevAt
    rw [if_neg hk0]
  show HprevAt p m (s + k) j U ≤ V
  rw [hH]
  exact hh _ hmem

/-! ### 6. The record-window form -/

/-- **Shifted site-window oscillation on a cell with deterministic containment and `(locmax)`.**
Let `A` be `F_s`-measurable and suppose that on `A` the record stays in `[A0, A0+M)` throughout
the window and `h_j ≤ V` on the site window `[A0-1, A0+M)`.  Then the truncation never fires on
`A` and the oscillation of `H_{j,·}(y)` over the pairs `s ≤ u ≤ v ≤ s+n`, uniformly over the
`M` sites `y ∈ [A0, A0+M)`, exceeds `ε` only on an event of measure at most

  `M · 2 (n+1) · exp (-ε² / (16 n (capB V)²))`.

The containment and `(locmax)` hypotheses are exactly the deterministic content of the paper's
`{d_r ≤ L}` and `(locmax)` conditions (see `README.md`); both are measurable at time `s` because
`h_j` is a time-independent functional of the array. -/
theorem measureReal_recordWindow_supSiteOsc {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m : ℕ) (j : Fin N) {A0 M s : ℕ} (hA0 : 1 ≤ A0) {V : ℝ} (hV : 0 ≤ V)
    {A : Set (Array N)} (hA : MeasurableSet[enlFilt p m s] A)
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε)
    (hrec : ∀ U ∈ A, ∀ k < n, A0 ≤ (recVal j (prefOf p m (s + k) U)).toNat ∧
      (recVal j (prefOf p m (s + k) U)).toNat < A0 + M)
    (hloc : ∀ U ∈ A, ∀ y ∈ Finset.Ico (A0 - 1) (A0 + M),
      SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) y ≤ V) :
    (arrayMeasure N).real
        (A ∩ {U | ∃ y ∈ Finset.Ico A0 (A0 + M), ∃ u v : ℕ,
          s ≤ u ∧ u ≤ v ∧ v ≤ s + n ∧
            ε ≤ |projH p m j v U ((y : ℕ) : ℤ) - projH p m j u U ((y : ℕ) : ℤ)|})
      ≤ (M : ℝ) * (2 * ((n : ℝ) + 1) *
          Real.exp (-(ε ^ 2) / (16 * (n : ℝ) * (SiteHMax.capB p m V) ^ 2))) := by
  have hres : A ∩ {U | ∃ k < n, U ∉ SiteHMax.siteGood p m j V (s + k)} = ∅ := by
    ext U
    constructor
    · rintro ⟨hUA, k, hk, hkbad⟩
      exact absurd (siteGood_of_shift_window hp0 hp1 m j hA0 (fun k hk => hrec U hUA k hk)
        (fun y hy => hloc U hUA y hy) hk) hkbad
    · simp
  have hmain := measureReal_cell_supSiteOsc_pair_le (p := p) hp0 hp1 m j
    (Finset.Ico A0 (A0 + M)) hn hA hV hε
  rw [hres, measureReal_empty, add_zero] at hmain
  have hcard : ((Finset.Ico A0 (A0 + M)).card : ℝ) = (M : ℝ) := by
    rw [Nat.card_Ico, Nat.add_sub_cancel_left]
  calc (arrayMeasure N).real
        (A ∩ {U | ∃ y ∈ Finset.Ico A0 (A0 + M), ∃ u v : ℕ,
          s ≤ u ∧ u ≤ v ∧ v ≤ s + n ∧
            ε ≤ |projH p m j v U ((y : ℕ) : ℤ) - projH p m j u U ((y : ℕ) : ℤ)|})
      ≤ ((Finset.Ico A0 (A0 + M)).card : ℝ) * ((arrayMeasure N).real A *
          (2 * ((n : ℝ) + 1) *
            Real.exp (-(ε ^ 2) / (16 * (n : ℝ) * (SiteHMax.capB p m V) ^ 2)))) := hmain
    _ = (M : ℝ) * ((arrayMeasure N).real A *
          (2 * ((n : ℝ) + 1) *
            Real.exp (-(ε ^ 2) / (16 * (n : ℝ) * (SiteHMax.capB p m V) ^ 2)))) := by
        rw [hcard]
    _ ≤ (M : ℝ) * (2 * ((n : ℝ) + 1) *
          Real.exp (-(ε ^ 2) / (16 * (n : ℝ) * (SiteHMax.capB p m V) ^ 2))) := by
        have hmuA : (arrayMeasure N).real A ≤ 1 := by
          haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
          exact measureReal_le_one
        have hE : 0 ≤ 2 * ((n : ℝ) + 1) *
            Real.exp (-(ε ^ 2) / (16 * (n : ℝ) * (SiteHMax.capB p m V) ^ 2)) := by positivity
        have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
        nlinarith [hmuA, hE, hM0, mul_le_mul_of_nonneg_left hmuA hE]

/-! ### 7. The `hosc` corollary at the walker's own site -/

/-- **`hosc` at the walker's own site.**  If in addition to the record containment and `(locmax)`
the position of walker `i` stays in the site window `[A0, A0+M)` throughout the window (which on
`{d_r ≤ L}` is the paper's `X_u^i ≥ r - (T+1)L ≥ 0`), then

  `mu {∃ u v, s ≤ u ≤ v ≤ s+n, ε ≤ |H_{j,v}(X_u^i) - H_{j,u}(X_u^i)|}`
  `  ≤ M · 2 (n+1) · exp (-ε² / (16 n (capB V)²))`.

`u = s`, `v = t` is the `hosc` field of `LocOcc.lococc_window`. -/
theorem measureReal_recordWindow_hosc {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m : ℕ) (i j : Fin N) {A0 M s : ℕ} (hA0 : 1 ≤ A0) {V : ℝ} (hV : 0 ≤ V)
    {A : Set (Array N)} (hA : MeasurableSet[enlFilt p m s] A)
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ U ∈ A, ∀ u : ℕ, s ≤ u → u ≤ s + n →
      A0 ≤ ((trajectory p m U u).pos i).toNat ∧
        ((trajectory p m U u).pos i).toNat < A0 + M)
    (hrec : ∀ U ∈ A, ∀ k < n, A0 ≤ (recVal j (prefOf p m (s + k) U)).toNat ∧
      (recVal j (prefOf p m (s + k) U)).toNat < A0 + M)
    (hloc : ∀ U ∈ A, ∀ y ∈ Finset.Ico (A0 - 1) (A0 + M),
      SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) y ≤ V) :
    (arrayMeasure N).real
        (A ∩ {U | ∃ u v : ℕ, s ≤ u ∧ u ≤ v ∧ v ≤ s + n ∧
          ε ≤ |projH p m j v U ((trajectory p m U u).pos i)
            - projH p m j u U ((trajectory p m U u).pos i)|})
      ≤ (M : ℝ) * (2 * ((n : ℝ) + 1) *
          Real.exp (-(ε ^ 2) / (16 * (n : ℝ) * (SiteHMax.capB p m V) ^ 2))) := by
  have hbase := measureReal_recordWindow_supSiteOsc (p := p) hp0 hp1 m j (A0 := A0) (M := M)
    (n := n) (s := s) (V := V) hA0 hV hA hn hε hrec hloc
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) hbase
  rintro U ⟨hUA, u, v, hsu, huv, hvn, hdev⟩
  obtain ⟨hlo, hhi⟩ := hpos U hUA u hsu (le_trans huv hvn)
  have hcast : ((((trajectory p m U u).pos i).toNat : ℤ)) = (trajectory p m U u).pos i := by
    have h0 : (0 : ℤ) ≤ (trajectory p m U u).pos i := by
      have : (0 : ℤ) ≤ (A0 : ℤ) := by exact_mod_cast Nat.zero_le A0
      have hA0Z : (A0 : ℤ) ≤ ((trajectory p m U u).pos i).toNat := by exact_mod_cast hlo
      omega
    exact Int.toNat_of_nonneg h0
  exact ⟨hUA, ((trajectory p m U u).pos i).toNat, Finset.mem_Ico.mpr ⟨hlo, hhi⟩,
    u, v, hsu, huv, hvn, by rw [hcast]; exact hdev⟩

/-! ### 8. The paper's scale: `V = L^{1/16}`, `n = T L`, `ε = L^{3/4}` -/

/-- The `(locmax)`-scale envelope is at most `9 Cproj L^{1/16}`, hence its square is at most
`81 Cproj² L^{1/8}`. -/
theorem capB_xOf_sq_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) {L : ℕ}
    (hL : 1 ≤ L) :
    (SiteHMax.capB p m ((L : ℝ) ^ (1 / 16 : ℝ))) ^ 2
      ≤ 81 * (SiteHMax.Cproj p m) ^ 2 * (L : ℝ) ^ (1 / 8 : ℝ) := by
  have hL0 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hb := SiteHMax.capB_xOf_le (p := p) hp0 hp1 m (L := L) hL
  have hb0 : 0 ≤ SiteHMax.capB p m ((L : ℝ) ^ (1 / 16 : ℝ)) :=
    le_of_lt (SiteHMax.capB_pos hp0 hp1 m (Real.rpow_nonneg (le_of_lt hL0) _))
  have h1 : (SiteHMax.capB p m ((L : ℝ) ^ (1 / 16 : ℝ))) ^ 2
      ≤ (9 * SiteHMax.Cproj p m * (L : ℝ) ^ (1 / 16 : ℝ)) ^ 2 := by
    have h9 : (0 : ℝ) ≤ 9 * SiteHMax.Cproj p m * (L : ℝ) ^ (1 / 16 : ℝ) := by
      have := SiteHMax.Cproj_nonneg hp0 hp1 m
      positivity
    exact pow_le_pow_left₀ hb0 hb 2
  have hsq : ((L : ℝ) ^ (1 / 16 : ℝ)) ^ 2 = (L : ℝ) ^ (1 / 8 : ℝ) := by
    rw [← Real.rpow_natCast ((L : ℝ) ^ (1 / 16 : ℝ)) 2,
      ← Real.rpow_mul (le_of_lt hL0)]
    norm_num
  calc (SiteHMax.capB p m ((L : ℝ) ^ (1 / 16 : ℝ))) ^ 2
      ≤ (9 * SiteHMax.Cproj p m * (L : ℝ) ^ (1 / 16 : ℝ)) ^ 2 := h1
    _ = 81 * (SiteHMax.Cproj p m) ^ 2 * (L : ℝ) ^ (1 / 8 : ℝ) := by
        rw [mul_pow, mul_pow, hsq]; ring

/-- **The exponent of the paper-scale bound.**  With `n = T L`, `ε = L^{3/4}` and
`V = L^{1/16}`, the maximal-Azuma exponent is at least `L^{3/8} / (1296 T Cproj²)`. -/
theorem exp_arg_scale_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) {L T : ℕ}
    (hT : 1 ≤ T) (hL : 1 ≤ L) :
    -((((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
        (16 * ((T * L : ℕ) : ℝ) *
          (SiteHMax.capB p m ((L : ℝ) ^ (1 / 16 : ℝ))) ^ 2))
      ≤ -((L : ℝ) ^ (3 / 8 : ℝ) / (1296 * (T : ℝ) * (SiteHMax.Cproj p m) ^ 2)) := by
  have hL0 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hCp : (2 : ℝ) ≤ SiteHMax.Cproj p m := by
    unfold SiteHMax.Cproj
    have := inv_pos.mpr (one_sub_aRec_pos hp0 hp1 m)
    linarith
  have hcap : (SiteHMax.capB p m ((L : ℝ) ^ (1 / 16 : ℝ))) ^ 2
      ≤ 81 * (SiteHMax.Cproj p m) ^ 2 * (L : ℝ) ^ (1 / 8 : ℝ) :=
    capB_xOf_sq_le hp0 hp1 m hL
  have hTL : ((T * L : ℕ) : ℝ) = (T : ℝ) * (L : ℝ) := by push_cast; ring
  have heps : ((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 = (L : ℝ) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast ((L : ℝ) ^ (3 / 4 : ℝ)) 2,
      ← Real.rpow_mul (le_of_lt hL0)]
    norm_num
  have hpow : (L : ℝ) ^ (3 / 2 : ℝ) = (L : ℝ) ^ (3 / 8 : ℝ) * (L : ℝ) ^ (9 / 8 : ℝ) := by
    rw [← Real.rpow_add hL0]
    norm_num
  rw [heps]
  have hden : 16 * ((T * L : ℕ) : ℝ) * (SiteHMax.capB p m ((L : ℝ) ^ (1 / 16 : ℝ))) ^ 2
      ≤ 1296 * (T : ℝ) * (SiteHMax.Cproj p m) ^ 2 * (L : ℝ) ^ (9 / 8 : ℝ) := by
    have hstep : 16 * ((T * L : ℕ) : ℝ) *
        (SiteHMax.capB p m ((L : ℝ) ^ (1 / 16 : ℝ))) ^ 2
        ≤ 16 * ((T * L : ℕ) : ℝ) *
          (81 * (SiteHMax.Cproj p m) ^ 2 * (L : ℝ) ^ (1 / 8 : ℝ)) := by
      have h0 : (0 : ℝ) ≤ 16 * ((T * L : ℕ) : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left hcap h0
    have hLsplit : (L : ℝ) * (L : ℝ) ^ (1 / 8 : ℝ) = (L : ℝ) ^ (9 / 8 : ℝ) := by
      conv_lhs => lhs; rw [← Real.rpow_one (L : ℝ)]
      rw [← Real.rpow_add hL0]
      norm_num
    have hEq : 16 * ((T * L : ℕ) : ℝ) *
        (81 * (SiteHMax.Cproj p m) ^ 2 * (L : ℝ) ^ (1 / 8 : ℝ))
        = 1296 * (T : ℝ) * (SiteHMax.Cproj p m) ^ 2 * (L : ℝ) ^ (9 / 8 : ℝ) := by
      rw [hTL]
      calc 16 * ((T : ℝ) * (L : ℝ)) *
            (81 * (SiteHMax.Cproj p m) ^ 2 * (L : ℝ) ^ (1 / 8 : ℝ))
          = (1296 * (T : ℝ) * (SiteHMax.Cproj p m) ^ 2) *
              ((L : ℝ) * (L : ℝ) ^ (1 / 8 : ℝ)) := by ring
        _ = 1296 * (T : ℝ) * (SiteHMax.Cproj p m) ^ 2 * (L : ℝ) ^ (9 / 8 : ℝ) := by
            rw [hLsplit]
    linarith [hstep, hEq.le, hEq.ge]
  have hZpos : 0 < 16 * ((T * L : ℕ) : ℝ) *
      (SiteHMax.capB p m ((L : ℝ) ^ (1 / 16 : ℝ))) ^ 2 := by
    have hTL0 : (0 : ℝ) < ((T * L : ℕ) : ℝ) := by rw [hTL]; positivity
    have hcb : 0 < SiteHMax.capB p m ((L : ℝ) ^ (1 / 16 : ℝ)) :=
      SiteHMax.capB_pos hp0 hp1 m (Real.rpow_nonneg (le_of_lt hL0) _)
    positivity
  have hDpos : 0 < 1296 * (T : ℝ) * (SiteHMax.Cproj p m) ^ 2 := by positivity
  have hkey : (L : ℝ) ^ (3 / 8 : ℝ) / (1296 * (T : ℝ) * (SiteHMax.Cproj p m) ^ 2)
      ≤ (L : ℝ) ^ (3 / 2 : ℝ) /
        (16 * ((T * L : ℕ) : ℝ) * (SiteHMax.capB p m ((L : ℝ) ^ (1 / 16 : ℝ))) ^ 2) := by
    rw [div_le_div_iff₀ hDpos hZpos]
    calc (L : ℝ) ^ (3 / 8 : ℝ) *
          (16 * ((T * L : ℕ) : ℝ) *
            (SiteHMax.capB p m ((L : ℝ) ^ (1 / 16 : ℝ))) ^ 2)
        ≤ (L : ℝ) ^ (3 / 8 : ℝ) *
            (1296 * (T : ℝ) * (SiteHMax.Cproj p m) ^ 2 * (L : ℝ) ^ (9 / 8 : ℝ)) :=
          mul_le_mul_of_nonneg_left hden (by positivity)
      _ = (L : ℝ) ^ (3 / 2 : ℝ) *
            (1296 * (T : ℝ) * (SiteHMax.Cproj p m) ^ 2) := by
          rw [hpow]; ring
  exact neg_le_neg hkey

/-- **`hosc` at the paper's scale.**  On a cell `A` carrying the record containment, the
position containment and `(locmax) ≤ L^{1/16}`,

  `mu {∃ u v in the window, L^{3/4} ≤ |H_{j,v}(X_u^i) - H_{j,u}(X_u^i)|}`
  `  ≤ M · 2 (T L + 1) · exp ( -L^{3/8} / (1296 T Cproj²) )`.

This is a `C_T L exp(-c_T L^{1/8})`-type rate, stronger than the paper's
`C_T e^{-c_T L^{1/16}}`. -/
theorem measureReal_recordWindow_hosc_scale {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m : ℕ) (i j : Fin N) {A0 M s : ℕ} (hA0 : 1 ≤ A0) {A : Set (Array N)}
    (hA : MeasurableSet[enlFilt p m s] A) {T L : ℕ} (hT : 1 ≤ T) (hL : 1 ≤ L)
    (hpos : ∀ U ∈ A, ∀ u : ℕ, s ≤ u → u ≤ s + T * L →
      A0 ≤ ((trajectory p m U u).pos i).toNat ∧
        ((trajectory p m U u).pos i).toNat < A0 + M)
    (hrec : ∀ U ∈ A, ∀ k < T * L, A0 ≤ (recVal j (prefOf p m (s + k) U)).toNat ∧
      (recVal j (prefOf p m (s + k) U)).toNat < A0 + M)
    (hloc : ∀ U ∈ A, ∀ y ∈ Finset.Ico (A0 - 1) (A0 + M),
      SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) y ≤ (L : ℝ) ^ (1 / 16 : ℝ)) :
    (arrayMeasure N).real
        (A ∩ {U | ∃ u v : ℕ, s ≤ u ∧ u ≤ v ∧ v ≤ s + T * L ∧
          (L : ℝ) ^ (3 / 4 : ℝ) ≤ |projH p m j v U ((trajectory p m U u).pos i)
            - projH p m j u U ((trajectory p m U u).pos i)|})
      ≤ (M : ℝ) * (2 * (((T * L : ℕ) : ℝ) + 1)) *
          Real.exp (-((L : ℝ) ^ (3 / 8 : ℝ) / (1296 * (T : ℝ) * (SiteHMax.Cproj p m) ^ 2))) := by
  have hV : 0 ≤ (L : ℝ) ^ (1 / 16 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hK : 1 ≤ T * L := by nlinarith
  have hε : (0 : ℝ) < (L : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hL) _
  have hmain := measureReal_recordWindow_hosc (p := p) hp0 hp1 m i j (A0 := A0) (M := M)
    (n := T * L) (s := s) (V := (L : ℝ) ^ (1 / 16 : ℝ)) hA0 hV hA hK hε hpos hrec hloc
  refine hmain.trans ?_
  have harg := exp_arg_scale_le (p := p) hp0 hp1 m (L := L) (T := T) hT hL
  have hexp : Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
        (16 * ((T * L : ℕ) : ℝ) *
          (SiteHMax.capB p m ((L : ℝ) ^ (1 / 16 : ℝ))) ^ 2))
      ≤ Real.exp (-((L : ℝ) ^ (3 / 8 : ℝ) / (1296 * (T : ℝ) * (SiteHMax.Cproj p m) ^ 2))) := by
    refine Real.exp_le_exp.mpr ?_
    simpa only [neg_div] using harg
  have hpos2 : 0 ≤ 2 * (((T * L : ℕ) : ℝ) + 1) := by positivity
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hstep := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hpos2) hM0
  simpa only [mul_assoc] using hstep

end M3Hosc

namespace M3Hosc

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory Swarming.Enl SwarmCross

variable {N : ℕ}

/-! ### 9. Instantiation on the record cell

The paper's geometric content of `{d_r ≤ L}` at the record time `s = tau_r`, in the form in which
it is actually available: at time `s` every position and every running maximum lies in `[r-L, r]`
(the upper bound because `r` is the global maximum, the lower bound because the defect is `≤ L`).
Together with `(locmax)` on the site window, unit steps give the containment `[A0, A0+M)` with
`A0 = r - (T+1)L`, `M = (2T+3)L` over the whole window of length `T L`, which is exactly the
hypothesis list of `measureReal_recordWindow_hosc_scale`. -/

/-- **`hosc` on the actual record cell at the paper's scale.**  With `A0 = r - (T+1)L` and
`M = (2T+3)L`, on any `F_s`-measurable cell `A` on which

* the record `M_s^j` of walker `j` at time `s` lies in `[r-L, r]`,
* the position `X_s^i` of walker `i` at time `s` lies in `[r-L, r]`,
* `h_j ≤ L^{1/16}` on the site window `[A0-1, A0+M)`,

one has

  `mu(A ∩ {∃ s ≤ u ≤ v ≤ s+TL, L^{3/4} ≤ |H_{j,v}(X_u^i) - H_{j,u}(X_u^i)|})`
  `  ≤ M · 2 (TL+1) · exp (-L^{3/8}/(1296 T Cproj²))`.

The three deterministic hypotheses are the *only* geometric inputs; no probability enters them,
and all three are measurable at time `s` (the last because `h_j` is a time-independent functional
of the array).  `u = s`, `v = t` is the `hosc` field of `LocOcc.lococc_window` on the record
window. -/
theorem measureReal_recordCell_hosc_scale {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m : ℕ) (i j : Fin N) {r s T L : ℕ} (hL : 1 ≤ L) (hT : 1 ≤ T)
    (hlt : (T + 1) * L + 1 ≤ r)
    {A : Set (Array N)} (hA : MeasurableSet[enlFilt p m s] A)
    (hrecr : ∀ U ∈ A, (r : ℤ) - (L : ℤ) ≤ recVal j (prefOf p m s U) ∧
      recVal j (prefOf p m s U) ≤ (r : ℤ))
    (hpos0 : ∀ U ∈ A, (r : ℤ) - (L : ℤ) ≤ (trajectory p m U s).pos i ∧
      (trajectory p m U s).pos i ≤ (r : ℤ))
    (hloc : ∀ U ∈ A, ∀ y ∈ Finset.Ico (r - (T + 1) * L - 1)
        (r - (T + 1) * L + (2 * T + 3) * L),
      SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) y ≤ (L : ℝ) ^ (1 / 16 : ℝ)) :
    (arrayMeasure N).real
        (A ∩ {U | ∃ u v : ℕ, s ≤ u ∧ u ≤ v ∧ v ≤ s + T * L ∧
          (L : ℝ) ^ (3 / 4 : ℝ) ≤ |projH p m j v U ((trajectory p m U u).pos i)
            - projH p m j u U ((trajectory p m U u).pos i)|})
      ≤ (((2 * T + 3) * L : ℕ) : ℝ) * (2 * (((T * L : ℕ) : ℝ) + 1)) *
          Real.exp (-((L : ℝ) ^ (3 / 8 : ℝ) / (1296 * (T : ℝ) * (SiteHMax.Cproj p m) ^ 2))) := by
  have hmul : (T + 1) * L = T * L + L := by ring
  have hA0le : (T + 1) * L ≤ r := by omega
  have hA0Z : (((r - (T + 1) * L : ℕ)) : ℤ) = (r : ℤ) - (((T + 1) * L : ℕ) : ℤ) :=
    Nat.cast_sub hA0le
  have hArith : ((r - (T + 1) * L) + (2 * T + 3) * L : ℕ) = r + (T + 2) * L := by
    have h1 : (2 * T + 3) * L = (T + 1) * L + (T + 2) * L := by ring
    rw [h1]
    omega
  have hTLup : ((T * L : ℕ) : ℤ) ≤ (((T + 2) * L : ℕ) : ℤ) := by
    have h : T * L ≤ (T + 2) * L := Nat.mul_le_mul_right L (by omega)
    exact_mod_cast h
  -- positions
  have hpos : ∀ U ∈ A, ∀ u : ℕ, s ≤ u → u ≤ s + T * L →
      (r - (T + 1) * L) ≤ ((trajectory p m U u).pos i).toNat ∧
        ((trajectory p m U u).pos i).toNat < (r - (T + 1) * L) + (2 * T + 3) * L := by
    intro U hUA u hsu huT
    obtain ⟨hs1, hs2⟩ := hpos0 U hUA
    have hsub := QplWindow.pos_sub_run_le p m U i s (u - s)
    have hadd := QplWindow.pos_le_add_run p m U i s (u - s)
    have hueq : s + (u - s) = u := Nat.add_sub_cancel' hsu
    rw [hueq] at hsub hadd
    have hcast : (((u - s : ℕ)) : ℤ) ≤ (((T * L : ℕ)) : ℤ) := by
      exact_mod_cast (by omega : u - s ≤ T * L)
    have hlowZ : (((r - (T + 1) * L : ℕ)) : ℤ) ≤ (trajectory p m U u).pos i := by
      rw [hA0Z, hmul]
      push_cast
      linarith
    have hupZ : (trajectory p m U u).pos i
        < ((((r - (T + 1) * L) + (2 * T + 3) * L : ℕ)) : ℤ) := by
      rw [hArith]
      push_cast
      linarith
    have hnn : (0 : ℤ) ≤ (trajectory p m U u).pos i := by
      have : (0 : ℤ) ≤ (((r - (T + 1) * L : ℕ)) : ℤ) := by exact_mod_cast Nat.zero_le _
      linarith
    exact ⟨(Int.le_toNat hnn).2 hlowZ, (Int.toNat_lt hnn).2 hupZ⟩
  -- the record
  have hrec : ∀ U ∈ A, ∀ k < T * L, (r - (T + 1) * L) ≤
      (recVal j (prefOf p m (s + k) U)).toNat ∧
        (recVal j (prefOf p m (s + k) U)).toNat < (r - (T + 1) * L) + (2 * T + 3) * L := by
    intro U hUA k hk
    obtain ⟨hr1, hr2⟩ := hrecr U hUA
    have hmono := QplWindow.recVal_mono_le (p := p) (m := m) (j := j) (U := U)
      (a := s) (b := s + k) (by omega)
    have hrun := QplWindow.recVal_le_add_run (p := p) (m := m) (j := j) (U := U) s (s + k)
      (by omega)
    have hsubk : (s + k - s : ℕ) = k := by omega
    rw [hsubk] at hrun
    have hlowZ : (((r - (T + 1) * L : ℕ)) : ℤ) ≤ recVal j (prefOf p m (s + k) U) := by
      rw [hA0Z, hmul]
      push_cast
      linarith
    have hupZ : recVal j (prefOf p m (s + k) U)
        < ((((r - (T + 1) * L) + (2 * T + 3) * L : ℕ)) : ℤ) := by
      rw [hArith]
      have hkr : ((k : ℕ) : ℤ) ≤ (((T * L : ℕ)) : ℤ) := by exact_mod_cast le_of_lt hk
      push_cast
      linarith
    have hnn : (0 : ℤ) ≤ recVal j (prefOf p m (s + k) U) :=
      zero_le_recVal_prefOf p m U j (s + k)
    exact ⟨(Int.le_toNat hnn).2 hlowZ, (Int.toNat_lt hnn).2 hupZ⟩
  -- the site window matches `(locmax)`
  have hloc' : ∀ U ∈ A, ∀ y ∈ Finset.Ico ((r - (T + 1) * L) - 1)
        ((r - (T + 1) * L) + (2 * T + 3) * L),
      SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) y ≤ (L : ℝ) ^ (1 / 16 : ℝ) := by
    intro U hUA y hy
    refine hloc U hUA y ?_
    rw [Finset.mem_Ico] at hy ⊢
    omega
  exact measureReal_recordWindow_hosc_scale (p := p) hp0 hp1 m i j
    (A0 := r - (T + 1) * L) (M := (2 * T + 3) * L) (s := s)
    (by omega) hA hT hL hpos hrec hloc'

end M3Hosc
