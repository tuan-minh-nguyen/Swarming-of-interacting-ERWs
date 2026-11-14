/-  Site-indexed maximal oscillation of the projected potential `H_{j,n}(z)` of the WCJF
  interacting-walk model, on the good `(locmax)` window.

  The paper (`main_1d_revised.tex`, proof of Prop. `ball` and the `(locmart)`
  paragraph of the tightness proof) works with the martingales

      `H_{j,n}(z) = E[H_j(z) | F_n]`,   `z` a *deterministic* integer in the locmax window
      `[r - (T+3)L, r + (T+3)L]`,

  and claims a maximal oscillation bound uniformly over the `O_T(L)` sites `z`, using only
  the increment estimate

      `|H_{j,n+1}(z) - H_{j,n}(z)| <= (h_j(M_n^j - 1) + 2) / (1-a) * 1{z > M_n^j}`

  on `(locmax)`.  The content of this file:

  * `Hinc` is the *site-indexed* increment `H_{j,n+1}(z) - H_{j,n}(z)` at a fixed site `z`;
  * `siteGood` is the **predictable** good event `{h_j(M_n^j - 1) <= V}` (measurable for the
    enlarged filtration at time `n`, *not* at `n+1`); the record-enlarged σ-algebra is not
    needed: `H0_le_HprevAt_add_two` gives `b_{n+1} <= b_n + 2`, so the two-record envelope
    `C(1 + b_n + b_{n+1})` of `abs_projH_increment_le` is dominated on `siteGood` by the
    deterministic constant `capB = C (2V + 7)`;
  * `siteInc` is the **predictably truncated** increment `1_{siteGood n} * Hinc n`, which is a
    martingale difference (`condExp_siteInc_eq_zero`), is `F_{n+1}`-strongly-measurable and is
    bounded a.e. by the constant `capB`;
  * `measure_max_abs_siteH_le` — for one fixed site, the two-sided maximal Azuma--Hoeffding
    bound on the intersection of the truncated martingale event with the geometric event
    `∀ n < K, 1_{siteGood n} = 1`;
  * `measure_sup_siteH_le` — the **union bound over the sites**: the sup over a finite
    deterministic site set costs exactly the cardinality of the set (this is the step the
    paper leaves implicit when it says "there are `O_T(L)` martingales in this collection");
  * `measure_sup_siteH_window_le` — the window form: record inside `[A, A+M)` and
    `h_j <= V` on the whole site window `[A-1, A+M)` force every `siteGood k` deterministically,
    so the residual geometric event costs nothing beyond the deterministic record condition;
  * `measure_sup_siteH_window_paper_scale` — the profile at `V = L^{1/16}`, `M = 2(T+3)L`,
    `K = T L`, `ε = L^{3/4}`: exponent `L^{3/8}/(324 T C^2)`.

  Not claimed: any statement about the raw/non-projected compensator, joint oscillation over
  `(j, z)`, the drift half of `(locmove)`, tightness, regeneration or `MainClaim`.  No
  Poissonisation, no `sorry`, no additional axiom.
-/
import Swarm.ProjHAdvance
import Swarm.ProjTower
import Swarm.LocMaxVar

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

namespace SiteHMax

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory Swarming.Enl SwarmCross

variable {N : ℕ}

/-! ### 1. The site-indexed increment, its predictable truncation, and the constants -/

/-- The constant of the complete projected-increment envelope `abs_projH_increment_le`,
`(2/(1-a) + 2)`. -/
noncomputable def Cproj (p : ℝ) (m : ℕ) : ℝ := 2 * (1 - aRec p m)⁻¹ + 2

/-- The deterministic increment bound on the good event `{h_j(M_n^j - 1) <= V}`:
`C (1 + (V+2) + (V+4))`. -/
noncomputable def capB (p : ℝ) (m : ℕ) (V : ℝ) : ℝ := Cproj p m * (2 * V + 7)

/-- The site-indexed increment of the projected potential,
`H_{j,n+1}(z) - H_{j,n}(z)` at the fixed site `z`. -/
noncomputable def Hinc (p : ℝ) (m : ℕ) (j : Fin N) (y : ℤ) (n : ℕ) : Array N → ℝ :=
  fun U => projH p m j (n + 1) U y - projH p m j n U y

/-- The predictable good event at time `n`: the predecessor potential at the running record is
at most `V`.  This is the `(locmax)`-type condition at the *record* site only. -/
def siteGood (p : ℝ) (m : ℕ) (j : Fin N) (V : ℝ) (n : ℕ) : Set (Array N) :=
  {U | HprevAt p m n j U ≤ V}

/-- The **predictably truncated** site-indexed increment. -/
noncomputable def siteInc (p : ℝ) (m : ℕ) (j : Fin N) (V : ℝ) (y : ℤ) (n : ℕ) :
    Array N → ℝ :=
  (siteGood p m j V n).indicator (Hinc p m j y n)

/-- `Cproj` is nonnegative. -/
theorem Cproj_nonneg {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) :
    0 ≤ Cproj p m := by
  unfold Cproj
  have h := one_sub_aRec_pos hp1 hp2 m
  have h1 : 0 < (1 - aRec p m)⁻¹ := inv_pos.mpr h
  linarith

/-- `capB` is positive. -/
theorem capB_pos {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) {V : ℝ}
    (hV : 0 ≤ V) : 0 < capB p m V := by
  unfold capB
  have h1 : 0 < (1 - aRec p m)⁻¹ := inv_pos.mpr (one_sub_aRec_pos hp1 hp2 m)
  have hCp : 0 < Cproj p m := by
    unfold Cproj
    linarith
  have h2 : 0 < 2 * V + 7 := by linarith
  exact mul_pos hCp h2

/-! ### 2. The predictable event is measurable at time `n` -/

/-- `siteGood` is measurable in the enlarged filtration **at its own time**. -/
theorem measurableSet_siteGood {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m n : ℕ) (j : Fin N) (V : ℝ) :
    MeasurableSet[enlFilt p m n] (siteGood p m j V n) := by
  letI : MeasurableSpace (Array N) := enlFilt p m n
  exact measurableSet_le (measurable_HprevAt_enlFilt hp m n j) measurable_const

/-! ### 3. The two-record envelope on the predictable event -/

/-- **The record cost at the next time is controlled by the current one.**
`b_{n+1} <= h_j(M_n^j - 1) + 4`.  Either the record does not move (then `b` is unchanged) or it
advances by one and `h_j(M_n^j) <= h_j(M_n^j - 1) + 2` gives the extra `2`. -/
theorem bRec_succ_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m n : ℕ) (j : Fin N)
    (U : Array N) : bRec p m (n + 1) j U ≤ HprevAt p m n j U + 4 := by
  have hr0 : 0 ≤ recVal j (prefOf p m n U) := zero_le_recVal_prefOf p m U j n
  have hb : bRec p m (n + 1) j U = HprevAt p m (n + 1) j U + 2 := rfl
  rw [hb]
  rcases recVal_succ_eq_or p m U j n with hsame | hadv
  · have hH : HprevAt p m (n + 1) j U = HprevAt p m n j U := by
      unfold HprevAt
      rw [hsame]
    rw [hH]
    linarith
  · have hH : HprevAt p m (n + 1) j U ≤ H0 p m n j U := by
      have hcast : (recVal j (prefOf p m n U) + 1).toNat
          = (recVal j (prefOf p m n U)).toNat + 1 := by
        have hz : ((recVal j (prefOf p m n U) + 1).toNat : ℤ)
            = ((recVal j (prefOf p m n U)).toNat + 1 : ℕ) := by
          rw [Int.toNat_of_nonneg (by linarith : (0 : ℤ) ≤ recVal j (prefOf p m n U) + 1)]
          push_cast
          linarith [Int.toNat_of_nonneg hr0]
        exact_mod_cast hz
      have hne : (recVal j (prefOf p m n U)).toNat + 1 ≠ 0 := Nat.succ_ne_zero _
      unfold HprevAt H0
      rw [hadv, hcast, if_neg hne, Nat.add_sub_cancel]
    have h2 := H0_le_HprevAt_add_two hp1 hp2 m n j U
    linarith

/-- **The increment envelope on the predictable good event.**
On `{h_j(M_n^j - 1) <= V}` the site-indexed increment is bounded by the deterministic
constant `capB = C (2V + 7)`, for every site `z`. -/
theorem ae_abs_Hinc_le_of_good {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m n : ℕ)
    (j : Fin N) (y : ℤ) {V : ℝ} (hV : 0 ≤ V) :
    ∀ᵐ U ∂(arrayMeasure N),
      U ∈ siteGood p m j V n → |Hinc p m j y n U| ≤ capB p m V := by
  filter_upwards [abs_projH_increment_le (p := p) hp1 hp2 m (n := n) j y] with U hU hgood
  have hg : HprevAt p m n j U ≤ V := hgood
  have hb1 : bRec p m n j U ≤ V + 2 := by
    have h2 : bRec p m n j U = HprevAt p m n j U + 2 := rfl
    linarith
  have hb2 : bRec p m (n + 1) j U ≤ V + 4 :=
    le_trans (bRec_succ_le hp1 hp2 m n j U) (by linarith)
  have hsum : 1 + bRec p m n j U + bRec p m (n + 1) j U ≤ 2 * V + 7 := by linarith
  have hC : 0 ≤ Cproj p m := Cproj_nonneg hp1 hp2 m
  have hbig : (2 * (1 - aRec p m)⁻¹ + 2) * (1 + bRec p m n j U + bRec p m (n + 1) j U)
      ≤ capB p m V := by
    unfold capB
    exact mul_le_mul_of_nonneg_left hsum (by simpa only [Cproj] using hC)
  exact le_trans hU hbig

/-- The truncated increment is bounded by `capB` almost everywhere (the bound is trivial off
the good event). -/
theorem ae_abs_siteInc_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m n : ℕ)
    (j : Fin N) (y : ℤ) {V : ℝ} (hV : 0 ≤ V) :
    ∀ᵐ U ∂(arrayMeasure N), |siteInc p m j V y n U| ≤ capB p m V := by
  filter_upwards [ae_abs_Hinc_le_of_good (p := p) hp1 hp2 m n j y hV] with U hU
  have hc0 : 0 ≤ capB p m V := le_of_lt (capB_pos hp1 hp2 m hV)
  unfold siteInc
  by_cases h : U ∈ siteGood p m j V n
  · rw [Set.indicator_of_mem h]
    exact hU h
  · rw [Set.indicator_of_notMem h, abs_zero]
    exact hc0

/-! ### 4. Measurability, integrability and the martingale-difference property -/

/-- `H_{j,n}(z)` at a fixed site is integrable (it is a conditional expectation). -/
theorem integrable_projH_site (p : ℝ) (m n : ℕ) (j : Fin N) (y : ℤ) :
    Integrable (fun U : Array N => projH p m j n U y) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  simpa only [projH] using
    (integrable_condExp (μ := arrayMeasure N) (m := enlFilt p m n)
      (f := fun V : Array N => SwarmOcc.Hpot (siteH p m j V) y))

/-- The site-indexed increment is `F_{n+1}`-strongly-measurable. -/
theorem stronglyMeasurable_Hinc (p : ℝ) (m n : ℕ) (j : Fin N) (y : ℤ) :
    StronglyMeasurable[enlFilt p m (n + 1)] (Hinc p m j y n) := by
  have h1 : StronglyMeasurable[enlFilt (N := N) p m (n + 1)]
      (fun U => projH p m j (n + 1) U y) := stronglyMeasurable_projH p m j (n + 1) y
  have h2 : StronglyMeasurable[enlFilt (N := N) p m (n + 1)]
      (fun U => projH p m j n U y) :=
    (stronglyMeasurable_projH p m j n y).mono ((enlFilt p m).mono (Nat.le_succ n))
  exact h1.sub h2

/-- The truncated increment is `F_{n+1}`-strongly-measurable: the truncating event is
`F_n`-measurable, hence `F_{n+1}`-measurable. -/
theorem stronglyMeasurable_siteInc {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m n : ℕ) (j : Fin N)
    (V : ℝ) (y : ℤ) :
    StronglyMeasurable[enlFilt p m (n + 1)] (siteInc p m j V y n) :=
  (stronglyMeasurable_Hinc p m n j y).indicator
    ((enlFilt p m).mono (Nat.le_succ n) _ (measurableSet_siteGood hp m n j V))

/-- **`H_{j,·}(z)` is a martingale**: the site-indexed increment has zero conditional mean. -/
theorem condExp_Hinc_eq_zero {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hpne : p ≠ 0)
    (m n : ℕ) (j : Fin N) (y : ℤ) :
    condExp (enlFilt p m n) (arrayMeasure N) (Hinc p m j y n) =ᵐ[arrayMeasure N] 0 := by
  classical
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hpt : condExp (enlFilt p m n) (arrayMeasure N)
      (fun U : Array N => projH p m j (n + 1) U y - projH p m j n U y)
      =ᵐ[arrayMeasure N]
      (condExp (enlFilt p m n) (arrayMeasure N) (fun U : Array N => projH p m j (n + 1) U y)
        - condExp (enlFilt p m n) (arrayMeasure N) (fun U : Array N => projH p m j n U y)) :=
    condExp_sub (μ := arrayMeasure N) (m := enlFilt p m n)
      (f := fun U : Array N => projH p m j (n + 1) U y)
      (g := fun U : Array N => projH p m j n U y)
      (integrable_projH_site p m (n + 1) j y) (integrable_projH_site p m n j y)
  have htower := ProjTower.condExp_projH_succ_fixed hp0 hp1 hpne m n j y
  have hself : condExp (enlFilt p m n) (arrayMeasure N) (fun U : Array N => projH p m j n U y)
      = fun U : Array N => projH p m j n U y :=
    condExp_of_stronglyMeasurable (μ := arrayMeasure N) ((enlFilt p m).le n)
      (stronglyMeasurable_projH p m j n y) (integrable_projH_site p m n j y)
  have hH : Hinc p m j y n
      = fun U : Array N => projH p m j (n + 1) U y - projH p m j n U y := rfl
  rw [hH]
  filter_upwards [hpt, htower] with U h1 h2
  simp only [Pi.sub_apply, Pi.zero_apply, h1, h2, hself, sub_self]

/-- The truncated increment has zero conditional mean: predictability of the truncating event
allows the conditional centring to pass through the indicator. -/
theorem condExp_siteInc_eq_zero {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hpne : p ≠ 0) (m n : ℕ) (j : Fin N) (V : ℝ) (y : ℤ) :
    condExp (enlFilt p m n) (arrayMeasure N) (siteInc p m j V y n) =ᵐ[arrayMeasure N] 0 := by
  classical
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hInt : Integrable (Hinc p m j y n) (arrayMeasure N) :=
    (integrable_projH_site p m (n + 1) j y).sub (integrable_projH_site p m n j y)
  have hmeas : MeasurableSet[enlFilt p m n] (siteGood p m j V n) :=
    measurableSet_siteGood hp0.le m n j V
  have hind := condExp_indicator (μ := arrayMeasure N) (m := enlFilt p m n) hInt hmeas
  have hzero := condExp_Hinc_eq_zero hp0 hp1 hpne m n j y
  filter_upwards [hind, hzero] with U h1 h2
  show condExp (enlFilt p m n) (arrayMeasure N)
      ((siteGood p m j V n).indicator (Hinc p m j y n)) U = 0
  rw [h1, Set.indicator_apply]
  by_cases h : U ∈ siteGood p m j V n <;> simp [h, h2]

/-! ### 5. The two-sided maximal bound at one fixed site -/

/-- **Maximal oscillation of `H_{j,·}(z)` at one fixed site, on the predictable good event.**

For `K >= 1`, a level `V >= 0`, a deviation `ε > 0` with the Chernoff side condition
`ε <= 2 K capB`,

  `μ{ ∀ n < K, h_j(M_n^j - 1) <= V  and  ∃ k <= K, ε <= |Σ_{n<k} (H_{j,n+1}(z) - H_{j,n}(z))| }`
  `  <= 2 (K+1) exp (-ε² / (4 K capB²))`.

The geometric event `∀ n < K, h_j(M_n^j - 1) <= V` is exactly the place where the truncation
could have fired; on its complement the comparison of the truncated and untruncated partial
sums is not available, and the statement is stated on the *intersection*, not conditionally. -/
theorem measure_max_abs_siteH_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hpne : p ≠ 0) (m : ℕ) (j : Fin N) (y : ℤ) {K : ℕ} (hK : 1 ≤ K) {V ε : ℝ}
    (hV : 0 ≤ V) (hε : 0 < ε) (hεK : ε ≤ 2 * K * capB p m V) :
    (arrayMeasure N).real
        ({U | ∀ k < K, U ∈ siteGood p m j V k} ∩
          {U | ∃ k ≤ K, ε ≤ |∑ i ∈ Finset.range k, Hinc p m j y i U|})
      ≤ 2 * ((K : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (K : ℝ) * (capB p m V) ^ 2)) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hc0 : 0 < capB p m V := capB_pos hp0 hp1 m hV
  have hS : 0 < (K : ℝ) * (capB p m V) ^ 2 := by
    have hK0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
    exact mul_pos hK0 (pow_pos hc0 2)
  have hproxy : LocMax.proxy (fun _ : ℕ => capB p m V) K
      = (K : ℝ) * (capB p m V) ^ 2 := by
    simp [LocMax.proxy, Finset.sum_const, nsmul_eq_mul]
  have hmain := LocMax.measure_max_abs_psum_ge_le_ae (μ := arrayMeasure N)
    (ℱ := enlFilt p m) (ξ := siteInc p m j V y) (c := fun _ => capB p m V) (ε := ε)
    (n := K) (S := (K : ℝ) * (capB p m V) ^ 2) hK hS ?_ ?_ ?_ ?_ ?_ hε ?_
  · -- transfer the abstract partial sums to the site-indexed ones
    have hmono : (arrayMeasure N).real
        ({U | ∀ k < K, U ∈ siteGood p m j V k} ∩
          {U | ∃ k ≤ K, ε ≤ |∑ i ∈ Finset.range k, Hinc p m j y i U|})
        ≤ (arrayMeasure N).real
          {U | ∃ k ≤ K, ε ≤ |LocMart.psum (siteInc p m j V y) k U|} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      rintro U ⟨hgood, k, hk, hdev⟩
      refine ⟨k, hk, ?_⟩
      have hpsum : LocMart.psum (siteInc p m j V y) k U
          = ∑ i ∈ Finset.range k, Hinc p m j y i U := by
        unfold LocMart.psum
        refine Finset.sum_congr rfl fun i hi => ?_
        have hik : i < K := lt_of_lt_of_le (Finset.mem_range.mp hi) hk
        show (siteGood p m j V i).indicator (Hinc p m j y i) U = Hinc p m j y i U
        exact Set.indicator_of_mem (hgood i hik) _
      rw [hpsum]
      exact hdev
    have hform : 2 * ((K : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (K : ℝ) * (capB p m V) ^ 2))
        = 2 * ((K : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * ((K : ℝ) * (capB p m V) ^ 2))) := by
      have hden : 4 * (K : ℝ) * (capB p m V) ^ 2 = 4 * ((K : ℝ) * (capB p m V) ^ 2) := by
        ring
      rw [hden]
    rw [hform]
    exact le_trans hmono hmain
  · -- the proxy `Σ_{k<K} capB² = K capB²`
    rw [hproxy]
  · -- `F_{k+1}`-measurability
    intro k _
    exact stronglyMeasurable_siteInc hp0.le m k j V y
  · -- positivity of the envelope
    intro k _
    exact hc0
  · -- a.e. increment bound
    intro k _
    exact ae_abs_siteInc_le hp0 hp1 m k j y hV
  · -- conditional centring
    intro k _
    exact condExp_siteInc_eq_zero hp0 hp1 hpne m k j V y
  · -- Chernoff side condition
    intro k _
    have h1 : ε * capB p m V ≤ 2 * (K : ℝ) * capB p m V * capB p m V := by
      have := mul_le_mul_of_nonneg_right hεK (le_of_lt hc0)
      calc ε * capB p m V ≤ (2 * (K : ℝ) * capB p m V) * capB p m V := this
        _ = 2 * (K : ℝ) * capB p m V * capB p m V := by ring
    calc ε * capB p m V ≤ 2 * (K : ℝ) * capB p m V * capB p m V := h1
      _ = 2 * ((K : ℝ) * (capB p m V) ^ 2) := by ring

/-! ### 6. The union bound over the sites -/

/-- **Supremum over a finite deterministic site set, honestly.**  The maximum over the sites in
`s` costs exactly `s.card`: each site contributes the single-site maximal bound, and the
geometric truncation event is *shared* by all sites, so it is not paid again per site. -/
theorem measure_sup_siteH_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hpne : p ≠ 0)
    (m : ℕ) (j : Fin N) (s : Finset ℕ) {K : ℕ} (hK : 1 ≤ K) {V ε : ℝ} (hV : 0 ≤ V)
    (hε : 0 < ε) (hεK : ε ≤ 2 * K * capB p m V) :
    (arrayMeasure N).real
        ({U | ∀ k < K, U ∈ siteGood p m j V k} ∩
          {U | ∃ y ∈ s, ∃ k ≤ K, ε ≤ |∑ i ∈ Finset.range k, Hinc p m j (y : ℤ) i U|})
      ≤ (s.card : ℝ) *
          (2 * ((K : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (K : ℝ) * (capB p m V) ^ 2))) := by
  have hsub : ({U : Array N | ∀ k < K, U ∈ siteGood p m j V k} ∩
        {U : Array N | ∃ y ∈ s, ∃ k ≤ K, ε ≤ |∑ i ∈ Finset.range k, Hinc p m j (y : ℤ) i U|})
      ⊆ ⋃ y ∈ s, ({U : Array N | ∀ k < K, U ∈ siteGood p m j V k} ∩
        {U : Array N | ∃ k ≤ K, ε ≤ |∑ i ∈ Finset.range k, Hinc p m j (y : ℤ) i U|}) := by
    rintro U ⟨hg, y, hy, hdev⟩
    exact Set.mem_biUnion hy ⟨hg, hdev⟩
  calc (arrayMeasure N).real _
      ≤ (arrayMeasure N).real (⋃ y ∈ s,
          ({U : Array N | ∀ k < K, U ∈ siteGood p m j V k} ∩
            {U : Array N | ∃ k ≤ K, ε ≤ |∑ i ∈ Finset.range k, Hinc p m j (y : ℤ) i U|})) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ y ∈ s, (arrayMeasure N).real
          ({U : Array N | ∀ k < K, U ∈ siteGood p m j V k} ∩
            {U : Array N | ∃ k ≤ K, ε ≤ |∑ i ∈ Finset.range k, Hinc p m j (y : ℤ) i U|}) :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _y ∈ s, (2 * ((K : ℝ) + 1) *
          Real.exp (-(ε ^ 2) / (4 * (K : ℝ) * (capB p m V) ^ 2))) :=
        Finset.sum_le_sum fun y _ => measure_max_abs_siteH_le hp0 hp1 hpne m j (y : ℤ) hK hV hε hεK
    _ = (s.card : ℝ) *
          (2 * ((K : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (K : ℝ) * (capB p m V) ^ 2))) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-! ### 7. The locmax window: the residual geometric event is discharged deterministically -/

/-- **On the record window, every predictable truncation event holds.**  If at every time
`k < K` the running record lies in the deterministic interval `[A, A+M)` and `h_j <= V`
throughout the site window `[A-1, A+M)`, then `h_j(M_k^j - 1) <= V` for every `k < K`, i.e.
`siteGood k` holds: the truncation never fires.  This is the exact sense in which the
`(locmax)` site-window bound controls the truncation residual. -/
theorem siteGood_of_window {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) (j : Fin N)
    {A M K : ℕ} (hA : 1 ≤ A) {V : ℝ} {U : Array N}
    (hrec : ∀ k < K, A ≤ (recVal j (prefOf p m k U)).toNat ∧
      (recVal j (prefOf p m k U)).toNat < A + M)
    (hh : ∀ y ∈ Finset.Ico (A - 1) (A + M),
      SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) y ≤ V)
    {k : ℕ} (hk : k < K) : U ∈ siteGood p m j V k := by
  obtain ⟨hlo, hhi⟩ := hrec k hk
  have hk0 : (recVal j (prefOf p m k U)).toNat ≠ 0 := by omega
  have hmem : (recVal j (prefOf p m k U)).toNat - 1 ∈ Finset.Ico (A - 1) (A + M) :=
    Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hH : HprevAt p m k j U
      = SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
          ((recVal j (prefOf p m k U)).toNat - 1) := by
    unfold HprevAt
    rw [if_neg hk0]
  show HprevAt p m k j U ≤ V
  rw [hH]
  exact hh _ hmem

/-- **Site-indexed maximal oscillation on the good locmax window.**
The record stays inside `[A, A+M)`, the whole site window `[A-1, A+M)` carries `h_j <= V`, and
the supremum of the site-indexed projected-potential oscillation over the sites of `[A, A+M)`
is at most `ε` up to the maximal Azuma--Hoeffding probability

  `M · 2(K+1) · exp(-ε²/(4 K capB²))`.

The geometric content (truncation residual, record window, site window) is *deterministic*: no
probability is charged for it, and no almost-sure modification is used. -/
theorem measure_sup_siteH_window_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hpne : p ≠ 0) (m : ℕ) (j : Fin N) {A M K : ℕ} (hA : 1 ≤ A) (hK : 1 ≤ K) {V ε : ℝ}
    (hV : 1 ≤ V) (hε : 0 < ε) (hεK : ε ≤ 2 * K * capB p m V) :
    (arrayMeasure N).real
        ({U | (∀ k < K, A ≤ (recVal j (prefOf p m k U)).toNat ∧
              (recVal j (prefOf p m k U)).toNat < A + M)} ∩
          {U | ∀ y ∈ Finset.Ico (A - 1) (A + M),
              SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) y ≤ V} ∩
          {U | ∃ y ∈ Finset.Ico A (A + M), ∃ k ≤ K,
              ε ≤ |∑ i ∈ Finset.range k, Hinc p m j (y : ℤ) i U|})
      ≤ (M : ℝ) * (2 * ((K : ℝ) + 1) *
          Real.exp (-(ε ^ 2) / (4 * (K : ℝ) * (capB p m V) ^ 2))) := by
  have hV0 : 0 ≤ V := by linarith
  have hcard : (Finset.Ico A (A + M)).card = M := by
    rw [Nat.card_Ico]
    omega
  have hsub : ({U : Array N | (∀ k < K, A ≤ (recVal j (prefOf p m k U)).toNat ∧
          (recVal j (prefOf p m k U)).toNat < A + M)} ∩
        {U : Array N | ∀ y ∈ Finset.Ico (A - 1) (A + M),
          SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) y ≤ V} ∩
        {U : Array N | ∃ y ∈ Finset.Ico A (A + M), ∃ k ≤ K,
          ε ≤ |∑ i ∈ Finset.range k, Hinc p m j (y : ℤ) i U|})
      ⊆ ({U : Array N | ∀ k < K, U ∈ siteGood p m j V k} ∩
        {U : Array N | ∃ y ∈ Finset.Ico A (A + M), ∃ k ≤ K,
          ε ≤ |∑ i ∈ Finset.range k, Hinc p m j (y : ℤ) i U|}) := by
    rintro U ⟨⟨hrec, hh⟩, y, hy, k, hk, hdev⟩
    exact ⟨fun k hk => siteGood_of_window hp0 hp1 m j hA hrec hh hk, y, hy, k, hk, hdev⟩
  calc (arrayMeasure N).real _
      ≤ (arrayMeasure N).real
          ({U : Array N | ∀ k < K, U ∈ siteGood p m j V k} ∩
            {U : Array N | ∃ y ∈ Finset.Ico A (A + M), ∃ k ≤ K,
              ε ≤ |∑ i ∈ Finset.range k, Hinc p m j (y : ℤ) i U|}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ((Finset.Ico A (A + M)).card : ℝ) * (2 * ((K : ℝ) + 1) *
          Real.exp (-(ε ^ 2) / (4 * (K : ℝ) * (capB p m V) ^ 2))) :=
        measure_sup_siteH_le hp0 hp1 hpne m j _ hK hV0 hε hεK
    _ = (M : ℝ) * (2 * ((K : ℝ) + 1) *
          Real.exp (-(ε ^ 2) / (4 * (K : ℝ) * (capB p m V) ^ 2))) := by
        rw [hcard]

/-! ### 8. The record-window scale `V = L^{1/16}`, `K = T L`, `ε = L^{3/4}` -/

/-- The envelope at the paper's local scale: on `{h_j(M_n^j - 1) <= L^{1/16}}` the site-indexed
projected increment is bounded by `Cproj · (2 L^{1/16} + 7)`. -/
theorem capB_xOf_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) {L : ℕ}
    (hL : 1 ≤ L) :
    capB p m ((L : ℝ) ^ (1 / 16 : ℝ)) ≤ 9 * Cproj p m * (L : ℝ) ^ (1 / 16 : ℝ) := by
  have hV : (1 : ℝ) ≤ (L : ℝ) ^ (1 / 16 : ℝ) := Real.one_le_rpow (by exact_mod_cast hL) (by norm_num)
  have hCp : 0 ≤ Cproj p m := Cproj_nonneg hp0 hp1 m
  unfold capB
  have h1 : 2 * (L : ℝ) ^ (1 / 16 : ℝ) + 7 ≤ 9 * (L : ℝ) ^ (1 / 16 : ℝ) := by linarith
  calc Cproj p m * (2 * (L : ℝ) ^ (1 / 16 : ℝ) + 7)
      ≤ Cproj p m * (9 * (L : ℝ) ^ (1 / 16 : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 hCp
    _ = 9 * Cproj p m * (L : ℝ) ^ (1 / 16 : ℝ) := by ring

/-- **Site-indexed maximal oscillation on the good locmax window at the paper's scale.**
With `V = L^{1/16}` (the `(locmax)` level), `M = 2(T+3)L` (the paper's window width,
`|Ico A (A + 2(T+3)L)| = 2(T+3)L`), `K = T L` and `ε = L^{3/4}`:

  `P ( record in [A, A+2(T+3)L)  and  h_j <= L^{1/16} on [A-1, A+2(T+3)L)`
  `   and  sup_{y in [A,A+2(T+3)L)} max_{k<=TL} |Σ_{n<k} (H_{j,n+1}(y) - H_{j,n}(y))| >= L^{3/4})`
  `  <= 2(T+3)L · (2TL + 1) · exp ( -L^{3/2} / (4 T L · capB(L^{1/16})²) )`.

Every parameter here is explicit; the only non-numeric ingredient is the model constant
`Cproj p m = 2/(1-a) + 2`, which enters through `capB`.  The probability is that of the
*intersection* of the three events; on the complement of the first two the statement is
vacuous and no almost-sure replacement is made. -/
theorem measure_sup_siteH_window_scale {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hpne : p ≠ 0) (m : ℕ) (j : Fin N) {A M T L : ℕ}
    (hA : 1 ≤ A) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    (arrayMeasure N).real
        ({U | (∀ k < T * L, A ≤ (recVal j (prefOf p m k U)).toNat ∧
              (recVal j (prefOf p m k U)).toNat < A + M)} ∩
          {U | ∀ y ∈ Finset.Ico (A - 1) (A + M),
              SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) y ≤ (L : ℝ) ^ (1 / 16 : ℝ)} ∩
          {U | ∃ y ∈ Finset.Ico A (A + M), ∃ k ≤ T * L,
              (L : ℝ) ^ (3 / 4 : ℝ) ≤
                |∑ i ∈ Finset.range k, Hinc p m j (y : ℤ) i U|})
      ≤ (M : ℝ) * (2 * (((T * L : ℕ) : ℝ) + 1)) *
          Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
            (4 * ((T * L : ℕ) : ℝ) * (capB p m ((L : ℝ) ^ (1 / 16 : ℝ))) ^ 2)) := by
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hT1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hK : 1 ≤ T * L := by nlinarith
  have hV : (1 : ℝ) ≤ (L : ℝ) ^ (1 / 16 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hε : (0 : ℝ) < (L : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hcap18 : 18 ≤ capB p m ((L : ℝ) ^ (1 / 16 : ℝ)) := by
    have hCp2 : 2 ≤ Cproj p m := by
      unfold Cproj
      have h := inv_pos.mpr (one_sub_aRec_pos hp0 hp1 m)
      linarith
    unfold capB
    have h7 : 9 ≤ 2 * (L : ℝ) ^ (1 / 16 : ℝ) + 7 := by linarith
    nlinarith [hCp2, h7]
  have hεK : (L : ℝ) ^ (3 / 4 : ℝ) ≤
      2 * ((T * L : ℕ) : ℝ) * capB p m ((L : ℝ) ^ (1 / 16 : ℝ)) := by
    have hLe : (L : ℝ) ^ (3 / 4 : ℝ) ≤ (L : ℝ) :=
      Real.rpow_le_self_of_one_le hL1 (by norm_num)
    have hcast : ((T * L : ℕ) : ℝ) = (T : ℝ) * (L : ℝ) := by push_cast; ring
    have hTL : (1 : ℝ) ≤ (T : ℝ) * (L : ℝ) := by nlinarith
    have hstep : (2 : ℝ) * ((T : ℝ) * (L : ℝ)) * 18 ≤
        2 * ((T : ℝ) * (L : ℝ)) * capB p m ((L : ℝ) ^ (1 / 16 : ℝ)) := by
      have h2 : (0 : ℝ) ≤ 2 * ((T : ℝ) * (L : ℝ)) := by linarith
      exact mul_le_mul_of_nonneg_left hcap18 h2
    have h36 : (L : ℝ) ≤ 36 * ((T : ℝ) * (L : ℝ)) := by nlinarith
    rw [hcast]
    linarith
  have hmain := measure_sup_siteH_window_le (M := M)
    (V := (L : ℝ) ^ (1 / 16 : ℝ)) (ε := (L : ℝ) ^ (3 / 4 : ℝ)) hp0 hp1 hpne m j hA hK hV hε hεK
  rw [mul_assoc]
  exact hmain
