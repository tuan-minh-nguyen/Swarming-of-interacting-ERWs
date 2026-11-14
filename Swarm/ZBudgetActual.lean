/-
  **DIRECTION B (m2) — `ZBudgetActual.lean`: the actual pathwise eventual `Z` budget `(Vbound)`.**

  The occupation assembly (`SwarmOcc.occbnd_of_pieces`, `JboundActual.occbnd_coef`) consumes the
  eventual pathwise budget

      Z_T <= A * M_T^i + delta * T      eventually,  M_T^i = max_{t <= T} X_t^i ,

  where `Z_T = Zpot p m eps i j U T = H_{j,T}(X_T^i) - F_{b_T}(X_T^i - M_T^j)` is the paper's
  `Z_n`.  This file proves that budget **in the actual model** (`Swarming.Uniform.arrayMeasure N`),
  with

  * the explicit coefficient `A = targetParam p m + 1 = (1+a)/(1-a) + 1` of the paper's `(Vbound)`
    (`(spav)`: the spatial average `r^{-1} sum_{x<r} h_j(x) -> (1+a)/(1-a)`), and
  * the paper's budget `delta = 1/64`.

  The proof is the paper's, in three separated layers:

  1. **Deterministic algebra** (`Hpot_le_linear`, `Zpot_le_Hpot_add`): from a *linear spatial
     bound* `sum_{x<m} h x <= K m` (valid for `m >= R`) plus the spatial prefix `sum_{x<R} h x`,
     the potential term obeys `H(x) <= K max 0 x + sum_{x<R} h x`; and the correction term obeys
     the paper's `(Fbounds)` bound `-F_b <= b^2/(eps (1-a)^2)`.
  2. **The two actual stochastic inputs, as honest a.e. theorems of the array**:
     * `exists_linear_bound_array` — the *first* display of `(spav)` in the form the pathwise
       budget needs (transported from `S12.spav_uniform` along `measurePreserving_siteMarks`);
     * `exists_log_bound_array` — `(Kmom)` `h_j(x) <= c log(n+2)` uniformly over `x <= n+1`
       (transported from `MarkTails.hof_eventually_log_bound`), which controls the cap
       `b_T = h_j(M_T^j - 1) + 2` at the *random* record `M_T^j <= T`.
  3. **Absorption**: `log^2 T = o(T)`, so both the `(Fbounds)` correction cost and the spatial
     prefix are absorbed into `delta * T`.

  Nothing is assumed: the two inputs are *proved*, and the only remaining numerical content is
  the elementary `log^2/T -> 0`.  No integral bound is substituted for the pathwise `hZ`.

  Main result: `Zbudget_ae` (coefficient `targetParam p m + 1`, `delta = 1/64`), its
  `SwarmSpeed.runMax` restatement `Zbudget_ae_runMax` (the shape of
  `JboundActual.occbnd_of_pieces_coef`), and the abstract-coefficient corollary
  `Zbudget_ae_coef` for `A >= targetParam p m + 1`.

  **Endpoint of `hZ`.**  The onset is random (`∃ N₀(U)`), which is what "eventually almost
  surely" means.  `OccInterface.occupation_bound_one_eighth` states `hZ` with a deterministic
  `N₀`; the two forms are reconciled in the README (`hZ` with a random onset is composed with the
  same-shaped `hJ`, `hQ`; the deterministic-`N₀` interface needs the *uniform* onset, which is
  not claimed here).
-/
import Swarm.CorrectionDrift
import Swarm.S15
import Swarm.MarkTails
import Swarm.MarkN
import Swarm.SpatialG
import Swarm.S12

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology

namespace Swarming.Enl
namespace ZBudget

open Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross

variable {N : ℕ}

/-! ## 1. Deterministic layer: step sizes, record growth, the potential bound

Nothing in this section is probabilistic.  The lemmas are stated for the actual trajectory or for
an abstract sequence of site values, and they are the exact algebraic content of `(Vbound)`. -/

/-- The driven step is `±1`, so one step changes the position by one. -/
lemma abs_drivenStep (u α : ℝ) : |Swarming.drivenStep u α| = 1 := by
  unfold Swarming.drivenStep
  split_ifs <;> norm_num

/-- **A walker moves at most one site per unit time**: `|X_t^i| <= t`. -/
theorem abs_pos_le_time (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (t : ℕ) :
    |(trajectory p m U t).pos i| ≤ (t : ℤ) := by
  induction t with
  | zero => simp
  | succ n ih =>
      set s : ℤ := drivenStep (U (i, (trajectory p m U n).pos i,
          (trajectory p m U n).ell i ((trajectory p m U n).pos i)))
        (rightProbability p m (trajectory p m U n).ell i
          ((trajectory p m U n).pos i)) with hs
      have hstep : (trajectory p m U (n + 1)).pos i
          = (trajectory p m U n).pos i + s := by
        rw [trajectory_succ, nextWalkState_pos, nextPos]
      have habs : |s| = 1 := by rw [hs]; exact abs_drivenStep _ _
      rw [hstep]
      calc |(trajectory p m U n).pos i + s|
          ≤ |(trajectory p m U n).pos i| + |s| := abs_add_le _ _
        _ = |(trajectory p m U n).pos i| + 1 := by rw [habs]
        _ ≤ (n : ℤ) + 1 := by linarith
        _ = ((n + 1 : ℕ) : ℤ) := by push_cast; ring

/-- **The record is at most the time**: `M_n^j <= n`.  This is what makes the `(Kmom)` logarithmic
bound applicable at the *random* record site. -/
theorem runMax_le_time (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (n : ℕ) :
    runMax p m U j n ≤ (n : ℤ) := by
  refine Finset.sup'_le _ _ (fun t ht => ?_)
  have ht' : t ≤ n := by simpa using ht
  have h1 : (trajectory p m U t).pos j ≤ |(trajectory p m U t).pos j| := le_abs_self _
  have h2 : |(trajectory p m U t).pos j| ≤ (t : ℤ) := abs_pos_le_time p m U j t
  have h3 : (t : ℤ) ≤ (n : ℤ) := by exact_mod_cast ht'
  linarith

/-- **The paper's `(Vbound)` algebraic core.**  If the site values are nonnegative and their
spatial partial sums are linearly bounded above the threshold `R`, then the potential is bounded
by `K x` above zero, plus the finite prefix `sum_{x<R} h x`. -/
theorem Hpot_le_linear {h : ℕ → ℝ} {K : ℝ} {R : ℕ}
    (hK0 : 0 ≤ K) (hK : ∀ m ≥ R, ∑ x ∈ Finset.range m, h x ≤ K * (m : ℝ))
    (hpos : ∀ x, 0 ≤ h x) (x : ℤ) :
    SwarmOcc.Hpot h x ≤ K * max 0 (x : ℝ) + ∑ x ∈ Finset.range R, h x := by
  have hR0 : (0 : ℝ) ≤ ∑ x ∈ Finset.range R, h x := Finset.sum_nonneg fun x _ => hpos x
  rcases le_or_gt x 0 with hx | hx
  · rw [SwarmOcc.Hpot_of_nonpos hx]
    have hx' : (x : ℝ) ≤ 0 := by exact_mod_cast hx
    rw [max_eq_left hx']
    linarith
  · have hx0 : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx.le
    rw [SwarmOcc.Hpot, if_neg (by omega : ¬ x ≤ 0), max_eq_right hx0]
    set g : ℕ := x.toNat with hgdef
    have hgx : (g : ℝ) = (x : ℝ) := by
      have h1 : ((g : ℕ) : ℤ) = x := by rw [hgdef]; exact Int.toNat_of_nonneg hx.le
      exact_mod_cast h1
    rw [← hgx]
    rcases lt_or_ge g R with hgR | hgR
    · have hmono : ∑ u ∈ Finset.range g, h u ≤ ∑ u ∈ Finset.range R, h u :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hgR.le)
          (fun x _ _ => hpos x)
      have hKg : (0 : ℝ) ≤ K * (g : ℝ) := mul_nonneg hK0 (Nat.cast_nonneg g)
      linarith
    · have h := hK g hgR
      linarith

/-- **The correction term of `Z_T` is `(Fbounds)`-controlled**: `-F_b <= b^2/(eps (1-a)^2)`.
Together with `F_b <= 0` (`SwarmOcc.Fcorr_nonpos`) this says `Z_T <= H_{j,T}(X_T^i) + b_T^2/(...)`
pointwise in the array. -/
theorem Zpot_le_Hpot_add {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    {eps : ℝ} (hε : 0 < eps) (i j : Fin N) (U : Array N) (t : ℕ) :
    VdriftAssembly.Zpot p m eps i j U t
      ≤ SwarmOcc.Hpot (envH p m j U) ((trajectory p m U t).pos i)
        + bRec p m t j U ^ 2 / (eps * (1 - aRec p m) ^ 2) := by
  have ha0 : (0 : ℝ) ≤ aRec p m := zero_le_aRec hp1 hp2 m
  have ha1 : aRec p m < 1 := aRec_lt_one hp1 hp2 m
  have hb : (0 : ℝ) ≤ bRec p m t j U := by
    have h := three_le_bRec hp1 hp2 m t j U
    linarith
  have h := SwarmOcc.Fcorr_abs_le (a := aRec p m) (ε := eps) (b := bRec p m t j U) ha0 ha1 hb hε
    ((trajectory p m U t).pos i - runMax p m U j t)
  have h' := neg_le_of_abs_le h
  simp only [VdriftAssembly.Zpot]
  linarith

/-- **`Z` dominates the potential** (companion of `Zpot_le_Hpot_add`): since `F_b <= 0`
(`SwarmOcc.Fcorr_nonpos`), `Z_T >= H_{j,T}(X_T^i)`.  This is why `Z_T` cannot be bounded above by
a constant when walker `i` sits at a high site, and it is the direction used by the countermodel
`ZCounterModel.Zpot_U0_ge`. -/
theorem Hpot_le_Zpot (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) (t : ℕ) :
    SwarmOcc.Hpot (envH p m j U) ((trajectory p m U t).pos i)
      ≤ VdriftAssembly.Zpot p m eps i j U t := by
  have hF : SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
      ((trajectory p m U t).pos i - runMax p m U j t) ≤ 0 :=
    SwarmOcc.Fcorr_nonpos _ _ _ _
  simp only [VdriftAssembly.Zpot]
  linarith

/-- The budget in the `SwarmSpeed.runMax` shape used by `JboundActual.occbnd_of_pieces_coef`:
the two running maxima agree definitionally. -/
theorem runMax_eq_speed (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (n : ℕ) :
    runMax p m U j n = SwarmSpeed.runMax (fun t => (trajectory p m U t).pos j) n := by
  unfold runMax SwarmSpeed.runMax
  rfl

/-! ## 2. The two actual stochastic inputs -/

/-- **The first display of `(spav)`, in the linear-spatial-bound form the pathwise `Z` budget
needs.**  For the actual array, walker `j`'s site-potential row has eventually linearly bounded
partial sums, with the paper's constant `(1+a)/(1-a) + 1 = targetParam p m + 1`.

This is `S12.spav_uniform` transported along `measurePreserving_siteMarks`; the `+1` is the
tolerance `eps = 1` of that uniform estimate. -/
theorem exists_linear_bound_array {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (j : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N), ∃ R₀ : ℕ, ∀ r ≥ R₀,
      ∑ x ∈ Finset.range r, SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x
        ≤ (SwarmSpatial.targetParam p m + 1) * (r : ℝ) := by
  have hp0 : 0 < p := by linarith
  have hTP : SwarmSpatial.targetParam p m = (1 + aRec p m) / (1 - aRec p m) := rfl
  have ha0 : (0 : ℝ) ≤ aRec p m := zero_le_aRec hp1 hp2 m
  have ha1 : aRec p m < 1 := aRec_lt_one hp1 hp2 m
  have hTP0 : (0 : ℝ) ≤ SwarmSpatial.targetParam p m := by
    rw [hTP]
    have h1 : (0 : ℝ) < 1 - aRec p m := by linarith
    positivity
  filter_upwards [(SwarmLogRatio.measurePreserving_siteMarks (N := N) hp0 hp2 m j)
    |>.quasiMeasurePreserving.ae (SwarmSpatial.spav_uniform (p := p) (m := m) hp1 hp2 hm)] with U hU
  obtain ⟨R₀, hR⟩ := Filter.eventually_atTop.mp (hU 1 (by norm_num))
  refine ⟨R₀, fun r hr => ?_⟩
  have hmain := hR r hr r le_rfl
  have hsplit := le_abs_self (∑ x ∈ Finset.range r,
    SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x - (r : ℝ) * SwarmSpatial.targetParam p m)
  have h1 : ∑ x ∈ Finset.range r, SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x
      ≤ (r : ℝ) + (r : ℝ) * SwarmSpatial.targetParam p m := by linarith
  have h2 : (r : ℝ) + (r : ℝ) * SwarmSpatial.targetParam p m
      = (SwarmSpatial.targetParam p m + 1) * (r : ℝ) := by ring
  linarith

/-- **(Kmom) at the actual array, one walker family.**  Almost surely,
`h_j(x) <= c log(n+2)` for *every* site `x <= n+1` and all large `n`; this is
`MarkTails.hof_eventually_log_bound` transported along `measurePreserving_siteMarks`. -/
theorem exists_log_bound_array {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (j : Fin N) :
    ∃ c : ℝ, 0 < c ∧ ∀ᵐ U ∂(arrayMeasure N), ∀ᶠ n : ℕ in atTop, ∀ x ≤ n + 1,
      SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x ≤ c * Real.log ((n : ℝ) + 2) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨θ, hθ, hγ⟩ := SwarmMarks.exists_theta_paper hp1 hp2 hm
  have hq0 : 0 < (1 - p) ^ (m - 1) := pow_pos (by linarith) _
  have hq1 : (1 - p) ^ (m - 1) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hγpos : 0 < (1 - (1 - p) ^ (m - 1)) * Real.exp (2 * θ)
      + (1 - p) ^ (m - 1) * ((1 - p) / p) * Real.exp (θ / p) := by
    have h1 : 0 ≤ (1 - (1 - p) ^ (m - 1)) * Real.exp (2 * θ) := by
      have : (0 : ℝ) ≤ 1 - (1 - p) ^ (m - 1) := by linarith
      positivity
    have h2 : 0 < (1 - p) ^ (m - 1) * ((1 - p) / p) * Real.exp (θ / p) := by
      have hratio : 0 < (1 - p) / p := by
        apply div_pos (by linarith) hp0
      positivity
    linarith
  refine ⟨3 / θ, by positivity, ?_⟩
  filter_upwards [(SwarmLogRatio.measurePreserving_siteMarks (N := N) hp0 hp2 m j)
    |>.quasiMeasurePreserving.ae (SwarmMarks.hof_eventually_log_bound (p := p)
      (q := (1 - p) ^ (m - 1))
      (γ := (1 - (1 - p) ^ (m - 1)) * Real.exp (2 * θ)
        + (1 - p) ^ (m - 1) * ((1 - p) / p) * Real.exp (θ / p))
      hp1 hp2 hq0 hq1 hθ hγpos hγ le_rfl)] with U hU
  filter_upwards [hU] with n hn x hx
  exact hn x hx

/-- **The cap `b_T = h_j(M_T^j - 1) + 2` grows only logarithmically.**  Since the record satisfies
`M_T^j <= T` (`runMax_le_time`), `(Kmom)` bounds the *random* record site by the same logarithm. -/
theorem bRec_eventually_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    {c : ℝ} (hc : 0 ≤ c) (j : Fin N) (U : Array N)
    (hlog : ∀ᶠ n : ℕ in atTop, ∀ x ≤ n + 1,
      SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x ≤ c * Real.log ((n : ℝ) + 2)) :
    ∀ᶠ T : ℕ in atTop, bRec p m T j U ≤ 3 + c * Real.log ((T : ℝ) + 2) := by
  filter_upwards [hlog] with T hT
  have hT2 : (1 : ℝ) ≤ (T : ℝ) + 2 := by
    have h0 : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
    linarith
  have hlog0 : (0 : ℝ) ≤ Real.log ((T : ℝ) + 2) := Real.log_nonneg hT2
  rcases Nat.eq_zero_or_pos ((recVal j (prefOf p m T U)).toNat) with h0 | hpos
  · have hH : HprevAt p m T j U = 1 := HprevAt_of_zero p m T j U h0
    have hb3 : bRec p m T j U = 3 := by simp only [bRec, hH]; norm_num
    rw [hb3]
    have hcl : (0 : ℝ) ≤ c * Real.log ((T : ℝ) + 2) := mul_nonneg hc hlog0
    linarith
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega :
      (recVal j (prefOf p m T U)).toNat ≠ 0)
    rw [bRec, HprevAt_of_succ p m T j U k hk]
    have hrec : recVal j (prefOf p m T U) ≤ (T : ℤ) := by
      rw [← runMax_eq_recVal p m U j T]
      exact runMax_le_time p m U j T
    have hnonneg : (0 : ℤ) ≤ recVal j (prefOf p m T U) := by omega
    have hcast : ((recVal j (prefOf p m T U)).toNat : ℤ) = recVal j (prefOf p m T U) :=
      Int.toNat_of_nonneg hnonneg
    have hk1 : ((k : ℕ) : ℤ) + 1 ≤ (T : ℤ) := by
      rw [hk] at hcast
      push_cast at hcast
      omega
    have hkT : k ≤ T + 1 := by omega
    have := hT k hkT
    linarith

/-! ### Absorbing the logarithmic cap into `delta * T` -/

/-- `log^2 T = o(T)` in the explicit form needed here: for every fixed constant `C >= 0` and every
`B > 0`, `C + (3 + c log(T+2))^2 / B <= T/64` eventually.  This is the step
`b_n = O(log n) => b_n^2/(eps (1-a)^2) = o(n)` of the paper's `(Vbound)`. -/
theorem eventually_const_add_log_sq_div_le {C c B : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c) (hB : 0 < B) :
    ∀ᶠ T : ℕ in atTop,
      C + (3 + c * Real.log ((T : ℝ) + 2)) ^ 2 / B ≤ (1 / 64) * (T : ℝ) := by
  have hlog1 : Tendsto (fun T : ℕ => Real.log ((T : ℝ) + 2) / (T : ℝ)) atTop (nhds 0) :=
    SwarmSpatial.tendsto_log_div_nat (c := 2) (by norm_num)
  have hlog2 : Tendsto (fun T : ℕ => Real.log ((T : ℝ) + 2) ^ 2 / (T : ℝ)) atTop (nhds 0) :=
    SwarmSpatialSq.tendsto_log_sq_div_nat (c := 2) (by norm_num)
  have hinv : Tendsto (fun T : ℕ => C / (T : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C
  have hinv2 : Tendsto (fun T : ℕ => (9 / B) / (T : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (9 / B)
  have hsum : Tendsto (fun T : ℕ => C / (T : ℝ) + (9 / B) / (T : ℝ)
      + ((6 * c) / B) * (Real.log ((T : ℝ) + 2) / (T : ℝ))
      + ((c ^ 2) / B) * (Real.log ((T : ℝ) + 2) ^ 2 / (T : ℝ))) atTop (nhds 0) := by
    have h3 : Tendsto (fun T : ℕ => ((6 * c) / B) * (Real.log ((T : ℝ) + 2) / (T : ℝ)))
        atTop (nhds 0) := by
      simpa using hlog1.const_mul ((6 * c) / B)
    have h4 : Tendsto (fun T : ℕ => ((c ^ 2) / B) * (Real.log ((T : ℝ) + 2) ^ 2 / (T : ℝ)))
        atTop (nhds 0) := by
      simpa using hlog2.const_mul ((c ^ 2) / B)
    have h5 := ((hinv.add hinv2).add h3).add h4
    simpa using h5
  have hcongr : (fun T : ℕ => (C + (3 + c * Real.log ((T : ℝ) + 2)) ^ 2 / B) / (T : ℝ))
      =ᶠ[atTop] (fun T : ℕ => C / (T : ℝ) + (9 / B) / (T : ℝ)
        + ((6 * c) / B) * (Real.log ((T : ℝ) + 2) / (T : ℝ))
        + ((c ^ 2) / B) * (Real.log ((T : ℝ) + 2) ^ 2 / (T : ℝ))) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with T hT
    have hT0 : (T : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hT
    field_simp
    ring
  have hratio : Tendsto (fun T : ℕ => (C + (3 + c * Real.log ((T : ℝ) + 2)) ^ 2 / B) / (T : ℝ))
      atTop (nhds 0) := hsum.congr' hcongr.symm
  have hsmall : ∀ᶠ T : ℕ in atTop,
      (C + (3 + c * Real.log ((T : ℝ) + 2)) ^ 2 / B) / (T : ℝ) < 1 / 64 :=
    (tendsto_order.1 hratio).2 (1 / 64) (by norm_num)
  filter_upwards [hsmall, Filter.eventually_gt_atTop (0 : ℕ)] with T hlt hT
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have heq : (C + (3 + c * Real.log ((T : ℝ) + 2)) ^ 2 / B) / (T : ℝ) * (T : ℝ)
      = C + (3 + c * Real.log ((T : ℝ) + 2)) ^ 2 / B := by
    field_simp
  nlinarith [hlt, hTpos, heq]

/-! ## 3. The actual pathwise `Z` budget `(Vbound)` -/

/-- **The paper's `(Vbound)` in the actual model, with the paper's coefficient and `delta = 1/64`.**

For `1/2 < p < 1`, `m >= 2`, `eps > 0` and distinct-or-equal walkers `i`, `j`, almost surely the
paper's `Z_T = H_{j,T}(X_T^i) - F_{b_T}(X_T^i - M_T^j)` obeys, eventually in `T`,

    Z_T <= ((1+a)/(1-a) + 1) * max 0 (M_T^i) + T/64 ,

where `M_T^i = max_{t <= T} X_t^i` is the running maximum of **walker `i`** — the index of the
spatial average in the paper's `(Jbound)`/`(occbnd)`.

Every ingredient is proved: the spatial average (`exists_linear_bound_array`), the logarithmic cap
growth (`exists_log_bound_array`, `(Kmom)`), and the `log^2 T = o(T)` absorption.  The onset `N₀`
depends on the array, as an almost-sure eventual statement must. -/
theorem Zbudget_ae {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {eps : ℝ} (hε : 0 < eps) (i j : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      VdriftAssembly.Zpot p m eps i j U T
        ≤ (SwarmSpatial.targetParam p m + 1) * max 0 ((runMax p m U i T : ℤ) : ℝ)
          + (1 / 64) * (T : ℝ) := by
  obtain ⟨c, hcpos, hU2⟩ := exists_log_bound_array (N := N) hp1 hp2 hm (j := j)
  have ha1 : aRec p m < 1 := aRec_lt_one hp1 hp2 m
  have hBpos : 0 < eps * (1 - aRec p m) ^ 2 := by
    have h1 : (0 : ℝ) < 1 - aRec p m := by linarith
    positivity
  filter_upwards [exists_linear_bound_array (N := N) hp1 hp2 hm (j := j), hU2] with U hlin hlog
  obtain ⟨R₀, hR₀⟩ := hlin
  have hC0 : (0 : ℝ) ≤ ∑ x ∈ Finset.range R₀,
      SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x :=
    Finset.sum_nonneg fun x _ => le_trans zero_le_one (SwarmMarks.one_le_hof hp1.le hp2 _ x)
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.mp
    (eventually_const_add_log_sq_div_le (C := ∑ x ∈ Finset.range R₀,
        SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x) (c := c)
      (B := eps * (1 - aRec p m) ^ 2) hC0 hcpos.le hBpos)
  obtain ⟨T₂, hT₂⟩ := Filter.eventually_atTop.mp
    (bRec_eventually_le (m := m) hp1 hp2 hcpos.le j U hlog)
  refine ⟨max (max R₀ T₁) (max T₂ 1), fun T hT => ?_⟩
  have hTR : R₀ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTT₁ : T₁ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTT₂ : T₂ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hT1 : T ≤ T := le_rfl
  have hlogT : (0 : ℝ) ≤ Real.log ((T : ℝ) + 2) := by
    apply Real.log_nonneg
    have h0 : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
    linarith
  -- the two bounding pieces
  have hHp : SwarmOcc.Hpot (envH p m j U) ((trajectory p m U T).pos i)
      ≤ (SwarmSpatial.targetParam p m + 1)
          * max 0 ((trajectory p m U T).pos i : ℝ)
        + ∑ x ∈ Finset.range R₀, SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x := by
    have henv : envH p m j U = fun u => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u :=
      rfl
    rw [henv]
    exact Hpot_le_linear (K := SwarmSpatial.targetParam p m + 1)
      (by have := aRec_lt_one hp1 hp2 m; have h0 : (0:ℝ) ≤ aRec p m := zero_le_aRec hp1 hp2 m
          have h1 : (0:ℝ) < 1 - aRec p m := by linarith
          have : (0:ℝ) ≤ (1 + aRec p m) / (1 - aRec p m) := by positivity
          have hTP : SwarmSpatial.targetParam p m = (1 + aRec p m) / (1 - aRec p m) := rfl
          rw [hTP]; linarith)
      hR₀ (fun x => le_trans zero_le_one (SwarmMarks.one_le_hof hp1.le hp2 _ x))
      ((trajectory p m U T).pos i)
  have hZp := Zpot_le_Hpot_add (p := p) hp1 hp2 (m := m) hε i j U T
  have hb := hT₂ T hTT₂
  have hb0 : (0 : ℝ) ≤ bRec p m T j U := by
    have h3 := three_le_bRec hp1 hp2 m T j U
    linarith
  have hg0 : (0 : ℝ) ≤ 3 + c * Real.log ((T : ℝ) + 2) := by
    have : (0 : ℝ) ≤ c * Real.log ((T : ℝ) + 2) := mul_nonneg hcpos.le hlogT
    linarith
  have hsq : bRec p m T j U ^ 2 / (eps * (1 - aRec p m) ^ 2)
      ≤ (3 + c * Real.log ((T : ℝ) + 2)) ^ 2 / (eps * (1 - aRec p m) ^ 2) := by
    apply div_le_div_of_nonneg_right _ hBpos.le
    nlinarith
  have habs := hT₁ T hTT₁
  have hXle : ((trajectory p m U T).pos i : ℝ) ≤ ((runMax p m U i T : ℤ) : ℝ) := by
    have := le_runMax p m U i T
    exact_mod_cast this
  have hmax : max 0 ((trajectory p m U T).pos i : ℝ) ≤ max 0 ((runMax p m U i T : ℤ) : ℝ) :=
    max_le_max le_rfl hXle
  have hcoef : (0 : ℝ) ≤ SwarmSpatial.targetParam p m + 1 := by
    have h0 : (0:ℝ) ≤ aRec p m := zero_le_aRec hp1 hp2 m
    have h1 : (0:ℝ) < 1 - aRec p m := by linarith [aRec_lt_one hp1 hp2 m]
    have hTP : SwarmSpatial.targetParam p m = (1 + aRec p m) / (1 - aRec p m) := rfl
    have : (0:ℝ) ≤ (1 + aRec p m) / (1 - aRec p m) := by positivity
    rw [hTP]; linarith
  have hKM : (SwarmSpatial.targetParam p m + 1) * max 0 ((trajectory p m U T).pos i : ℝ)
      ≤ (SwarmSpatial.targetParam p m + 1) * max 0 ((runMax p m U i T : ℤ) : ℝ) :=
    mul_le_mul_of_nonneg_left hmax hcoef
  linarith

/-- **The same budget with an arbitrary larger coefficient** `A >= (1+a)/(1-a) + 1`.  This is the
form the coefficient-general occupation assembly (`JboundActual.occbnd_of_pieces_coef`,
`occbnd_coef`) consumes, where `A` is enlarged to dominate the record-cost coefficient `B` as well,
so that a *single* `M` serves both the `Z` and the `J` budget. -/
theorem Zbudget_ae_coef {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {eps : ℝ} (hε : 0 < eps) (i j : Fin N) {A : ℝ}
    (hA : SwarmSpatial.targetParam p m + 1 ≤ A) :
    ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      VdriftAssembly.Zpot p m eps i j U T
        ≤ A * max 0 ((runMax p m U i T : ℤ) : ℝ) + (1 / 64) * (T : ℝ) := by
  filter_upwards [Zbudget_ae (N := N) hp1 hp2 hm hε i j] with U hU
  obtain ⟨N₀, hN₀⟩ := hU
  refine ⟨N₀, fun T hT => ?_⟩
  have h1 := hN₀ T hT
  have hM0 : (0 : ℝ) ≤ max 0 ((runMax p m U i T : ℤ) : ℝ) := le_max_left _ _
  have h2 : (SwarmSpatial.targetParam p m + 1) * max 0 ((runMax p m U i T : ℤ) : ℝ)
      ≤ A * max 0 ((runMax p m U i T : ℤ) : ℝ) :=
    mul_le_mul_of_nonneg_right hA hM0
  linarith

/-- **`hZ`-shape at the `SwarmSpeed.runMax` of walker `i`**: the exact form of the `hZ` premise of
`JboundActual.occbnd_of_pieces_coef` (there `M n = (SwarmSpeed.runMax u n : ℝ)`, `u` = the
positions of walker `i`). -/
theorem Zbudget_ae_runMax {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {eps : ℝ} (hε : 0 < eps) (i j : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      VdriftAssembly.Zpot p m eps i j U T
        ≤ (SwarmSpatial.targetParam p m + 1)
            * (SwarmSpeed.runMax (fun t => (trajectory p m U t).pos i) T : ℝ)
          + (1 / 64) * (T : ℝ) := by
  filter_upwards [Zbudget_ae (N := N) hp1 hp2 hm hε i j] with U hU
  obtain ⟨N₀, hN₀⟩ := hU
  refine ⟨N₀, fun T hT => ?_⟩
  have h1 := hN₀ T hT
  rw [runMax_eq_speed p m U i T] at h1
  have h2 : ((SwarmSpeed.runMax (fun t => (trajectory p m U t).pos i) T : ℤ) : ℝ)
      = max 0 ((SwarmSpeed.runMax (fun t => (trajectory p m U t).pos i) T : ℤ) : ℝ) := by
    have h0 : (0 : ℤ) ≤ SwarmSpeed.runMax (fun t => (trajectory p m U t).pos i) T := by
      have := SwarmSpeed.le_runMax (u := fun t => (trajectory p m U t).pos i) (t := 0) (n := T)
        (Nat.zero_le T)
      simpa using this
    have h0' : (0 : ℝ) ≤ ((SwarmSpeed.runMax (fun t => (trajectory p m U t).pos i) T : ℤ) : ℝ) := by
      exact_mod_cast h0
    exact (max_eq_right h0').symm
  rw [← h2] at h1
  linarith

/-- **`hZ` in the literal interface shape with a prescribed majorant `M`.**  The occupation
interface `OccInterface.occupation_bound_one_eighth` uses one arbitrary function `M : Array N →
ℕ → ℝ` in *both* the `Z` and the `J` premise, at coefficient exactly `1`.  This corollary is the
drop-in form: any `M` dominating `(targetParam p m + 1) * max 0 M_T^i` can be used.  (Taking
`M := C * max 0 M_T^i` with `C >= max (targetParam p m + 1) (J-coefficient)` reconciles the two
premises; the price is that the final occupation constant is `2C`, so `kappa` in
`SwarmSpeed.exists_kappa_of_occupation` shrinks but stays positive.) -/
theorem Zbudget_ae_M {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {eps : ℝ} (hε : 0 < eps) (i j : Fin N) {M : Array N → ℕ → ℝ}
    (hM : ∀ (U : Array N) (T : ℕ),
      (SwarmSpatial.targetParam p m + 1) * max 0 ((runMax p m U i T : ℤ) : ℝ) ≤ M U T) :
    ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      VdriftAssembly.Zpot p m eps i j U T ≤ M U T + (1 / 64) * (T : ℝ) := by
  filter_upwards [Zbudget_ae (N := N) hp1 hp2 hm hε i j] with U hU
  obtain ⟨N₀, hN₀⟩ := hU
  exact ⟨N₀, fun T hT => le_trans (hN₀ T hT) (by linarith [hM U T])⟩

end ZBudget
end Swarming.Enl


