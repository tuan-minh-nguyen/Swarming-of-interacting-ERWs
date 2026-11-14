/-  The paper (`main_1d_revised.tex`, end of Proposition `spatial` and the last line of
  Proposition `ball`) is explicit that the lower-speed constant `kappa(m,p)` must **not** depend
  on the walker count `N`:

  > the value of `C_s` may depend on `N`, which is fixed [...]; for the construction of
  > `kappa` in Proposition `ball`, these union bounds enter only through `b_n = O(log(n+2))`
  > and the summability of the martingale moment series, so `kappa` remains independent of `N`.

  `Swarm.Ballistic m p` is a *single* `kappa > 0` quantified before `N`, so every link of the
  occupation chain has to exhibit its constants **outside** the `N`-quantifier.  The integrated
  chain does not: `SwarmSpatialSq.exists_hof_sq_linear_bound_array`,
  `SwarmSpatialSq.exists_shifted_sq_linear_bound_array`,
  `Swarming.Enl.JBudgetActual.exists_wCap_eventual` and
  `Swarming.Enl.JBudgetActual.Jsum_eventual` are all stated with `N` fixed and the constant
  existentially bound *inside* it, so the composed coefficient of
  `SwarmActualBudget.actual_occupation_and_speed_of_hQ` is `sum_{i,j} B_{ij}`, an `N`-indexed
  quantity.

  Mathematically nothing is lost: each of those constants is an explicit expression in
  `p, m, eps` (`Ksq p ((1-p)^(m-1))` and `aRec p m`), and the only `N`-dependence in the proofs
  is the measure space `Array N` itself.  This file removes the quantifier mismatch:

  * `exists_hof_sq_linear_bound_uniform`
  * `exists_shifted_sq_linear_bound_uniform`
  * `exists_wCap_eventual_uniform`
  * `Jsum_eventual_uniform` — one coefficient `B(p,m,eps)` for **all** `N` and **all** pairs;
  * `actual_speed_uniform_of_JB` — the actual trajectory has a lower-speed constant
    `7 / (40 * max 1 (A + B))` that is **the same for every `N`**, from an `N`-uniform `J`
    coefficient `B`, the already-`N`-free `Z` coefficient `targetParam p m + 1`, and the
    `N`-free rate `1/64` for `Q`.

  No statement is weakened and no new hypothesis is introduced: each of the four uniform
  statements is the corresponding integrated statement with `∃ C` hoisted out of a fixed `N`,
  proved by the same argument with the explicit constant.
-/
import Swarm.BallisticInterfaceActual
import Swarm.ZBudgetActual
import Swarm.JBudgetActual
import Swarm.ActualBudgetInterfaces
import Swarm.S15

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology

namespace SwarmUniform

open Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl Swarming.Enl.VdriftAssembly Swarming.Enl.JBudgetActual

variable {N : ℕ}

/-! ## 1. The quenched spatial constant, uniformly in `N` -/

/-- **`(spav)` second display with an `N`-free constant.**  One `K = |Ksq p q| + 1` works for
every walker count simultaneously: only the probability space `Array N` changes. -/
theorem exists_hof_sq_linear_bound_uniform {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (j : Fin N),
      ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), ∃ R₀ : ℕ, ∀ r ≥ R₀,
        ∑ x ∈ Finset.range r,
          (SwarmMarks.hof p (SwarmLogRatio.siteMarksN p m U j) x) ^ 2 ≤ K * r := by
  set KK : ℝ := |SwarmSpatialSq.Ksq p ((1 - p) ^ (m - 1))| + 1 with hKKdef
  have hKK : SwarmSpatialSq.Ksq p ((1 - p) ^ (m - 1)) < KK := by
    rw [hKKdef]
    have := le_abs_self (SwarmSpatialSq.Ksq p ((1 - p) ^ (m - 1)))
    linarith
  have hpos : 0 < KK := by rw [hKKdef]; positivity
  refine ⟨KK, hpos, ?_⟩
  intro N j
  filter_upwards [SwarmSpatialSq.tendsto_hof_sq_average_array (N := N) hp1 hp2 hm] with U hU
  have hev : ∀ᶠ r : ℕ in atTop, (r : ℝ)⁻¹ *
      ∑ x ∈ Finset.range r,
        (SwarmMarks.hof p (SwarmLogRatio.siteMarksN p m U j) x) ^ 2 < KK :=
    (hU j).eventually (isOpen_Iio.mem_nhds hKK)
  have hev2 : ∀ᶠ r : ℕ in atTop,
      ∑ x ∈ Finset.range r,
        (SwarmMarks.hof p (SwarmLogRatio.siteMarksN p m U j) x) ^ 2 ≤ KK * r := by
    filter_upwards [hev, Filter.eventually_gt_atTop 0] with r hr hr0
    have hrpos : (0 : ℝ) < r := by exact_mod_cast hr0
    have hmul := mul_lt_mul_of_pos_left hr hrpos
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hrpos), one_mul] at hmul
    linarith
  exact eventually_atTop.mp hev2

/-- **The shifted `(spav)` weight with an `N`-free constant** (`JboundActual`'s `hces` shape). -/
theorem exists_shifted_sq_linear_bound_uniform {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (j : Fin N),
      ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), ∃ R₀ : ℕ, ∀ r ≥ R₀,
        ∑ x ∈ Finset.range r,
          (9 * (SwarmMarks.hof p (SwarmLogRatio.siteMarksN p m U j) (x - 1)) ^ 2)
            ≤ K * (r : ℝ) := by
  have hp : 0 < p := by linarith
  obtain ⟨K₁, hK₁pos, hU₁⟩ := exists_hof_sq_linear_bound_uniform (p := p) hp0 hp1 hm
  refine ⟨9 * ((3 / p) ^ 2 + K₁), by positivity, ?_⟩
  intro N j
  filter_upwards [hU₁ N j] with U hU
  obtain ⟨R₀, hR₀⟩ := hU
  refine ⟨max 2 (R₀ + 1), fun r hr => ?_⟩
  have hr2 : 2 ≤ r := le_trans (le_max_left _ _) hr
  have hr0 : R₀ ≤ r - 1 := by
    have := le_trans (le_max_right (2 : ℕ) (R₀ + 1)) hr
    omega
  have hbase := hR₀ (r - 1) hr0
  have hzero : SwarmMarks.hof p (SwarmLogRatio.siteMarksN p m U j) 0 ≤ 3 / p :=
    SwarmSpatialSq.hof_zero_le_three_div hp hp1.le (SwarmLogRatio.siteMarksN p m U j)
  have hzero0 : 0 ≤ SwarmMarks.hof p (SwarmLogRatio.siteMarksN p m U j) 0 := by
    linarith [SwarmMarks.one_le_hof hp0.le hp1 (SwarmLogRatio.siteMarksN p m U j) 0]
  have hzeroSq : (SwarmMarks.hof p (SwarmLogRatio.siteMarksN p m U j) 0) ^ 2 ≤ (3 / p) ^ 2 := by
    have hmul := mul_le_mul hzero hzero hzero0 (by positivity : (0 : ℝ) ≤ 3 / p)
    nlinarith
  have hshift := SwarmSpatialSq.sum_pred
    (fun x => 9 * (SwarmMarks.hof p (SwarmLogRatio.siteMarksN p m U j) x) ^ 2)
    (by omega : 1 ≤ r)
  have hmul : 9 * (∑ x ∈ Finset.range (r - 1),
      (SwarmMarks.hof p (SwarmLogRatio.siteMarksN p m U j) x) ^ 2)
      ≤ 9 * (K₁ * ((r - 1 : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left hbase (by positivity)
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
  have hrcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ r)]
    norm_num
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  calc
    (∑ x ∈ Finset.range r, (9 * (SwarmMarks.hof p (SwarmLogRatio.siteMarksN p m U j) (x - 1)) ^ 2))
        = 9 * (SwarmMarks.hof p (SwarmLogRatio.siteMarksN p m U j) 0) ^ 2
          + ∑ x ∈ Finset.range (r - 1),
            (9 * (SwarmMarks.hof p (SwarmLogRatio.siteMarksN p m U j) x) ^ 2) := hshift
    _ ≤ 9 * (3 / p) ^ 2 + 9 * (K₁ * ((r - 1 : ℕ) : ℝ)) := by
        have hsum : (∑ x ∈ Finset.range (r - 1),
            (9 * (SwarmMarks.hof p (SwarmLogRatio.siteMarksN p m U j) x) ^ 2))
            = 9 * (∑ x ∈ Finset.range (r - 1),
              (SwarmMarks.hof p (SwarmLogRatio.siteMarksN p m U j) x) ^ 2) := by
          rw [Finset.mul_sum]
        have h1 : 9 * (SwarmMarks.hof p (SwarmLogRatio.siteMarksN p m U j) 0) ^ 2
            ≤ 9 * (3 / p) ^ 2 := by
          have := mul_le_mul_of_nonneg_left hzeroSq (by norm_num : (0 : ℝ) ≤ 9)
          nlinarith
        rw [hsum]
        linarith
    _ = 9 * (3 / p) ^ 2 + 9 * K₁ * ((r : ℝ) - 1) := by rw [hrcast]; ring
    _ ≤ 9 * ((3 / p) ^ 2 + K₁) * (r : ℝ) := by
        have h1 : (0 : ℝ) ≤ 9 * (3 / p) ^ 2 := by positivity
        have h2 : (0 : ℝ) ≤ 9 * K₁ := by positivity
        nlinarith

/-- **`(hces)` with an `N`-free constant**: the `bCap`-squared spatial sums. -/
theorem exists_wCap_eventual_uniform {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (j : Fin N),
      ∀ᵐ U ∂(arrayMeasure N), ∃ R₀ : ℕ, ∀ r ≥ R₀,
        ∑ x ∈ Finset.range r, wCap p m U j x ≤ K * (r : ℝ) := by
  obtain ⟨K, hKpos, hU⟩ := exists_shifted_sq_linear_bound_uniform (p := p) hp0 hp1 hm
  refine ⟨K, hKpos, ?_⟩
  intro N j
  filter_upwards [hU N j] with U hU
  obtain ⟨R₀, hR₀⟩ := hU
  refine ⟨R₀, fun r hr => ?_⟩
  have hle := Finset.sum_le_sum (fun x (_ : x ∈ Finset.range r) =>
    wCap_le_shifted (N := N) hp0.le hp1 m U j x)
  have hshift : (∑ x ∈ Finset.range r,
      9 * (SwarmMarks.hof p (SwarmLogRatio.siteMarksN p m U j) (x - 1)) ^ 2) ≤ K * (r : ℝ) :=
    hR₀ r hr
  exact le_trans hle (by simpa only [SwarmLogRatio.siteMarksN] using hshift)

end SwarmUniform

namespace SwarmUniform

open Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl Swarming.Enl.VdriftAssembly Swarming.Enl.JBudgetActual

variable {N : ℕ}

/-! ## 2. The record-cost budget `(Jbound)` with one coefficient for all `N` -/

/-- **`(Jbound)` with a single `N`-free coefficient.**  There is `B = B(p,m,eps) > 0` such that
for **every** walker count `N`, every pair of walkers and almost every array,

    `sum_{t<T} |J_{t+1}| <= B * M_T^i + T/64`   eventually.

The constant is `2 (eps (1-a)^2)^{-1} K` with `K` the `N`-free spatial constant of
`exists_wCap_eventual_uniform`; only the onset `N₀` depends on the array (through the spatial
threshold), exactly as in the paper. -/
theorem abs_Jcorr_sum_eventual_uniform {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) {eps : ℝ} (hε : 0 < eps) :
    ∃ B : ℝ, 0 < B ∧ ∀ (N : ℕ) (i j : Fin N),
      ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
        (∑ t ∈ Finset.range T, |Jcorr p m eps i j U t|)
          ≤ B * (((runMax p m U i T : ℤ)) : ℝ) + (1 / 64) * (T : ℝ) := by
  obtain ⟨K, hKpos, hU⟩ := exists_wCap_eventual_uniform (p := p) hp0 hp1 hm
  have hq : 0 < (1 - p) ^ (m - 1) := pow_pos (by linarith) _
  have haa := ExcitedEnv.aConst_bounds hp0 hp1 hq (ExcitedEnv.q_le_half hp0 hp1 hm)
  have ha0 : 0 ≤ aRec p m := by
    have h := haa.1
    simp only [aRec]
    linarith
  have ha1 : aRec p m < 1 := by
    simpa only [aRec] using haa.2.1
  have h1ma : (0 : ℝ) < 1 - aRec p m := by linarith
  refine ⟨2 * (1 / (eps * (1 - aRec p m) ^ 2)) * K, by positivity, ?_⟩
  intro N i j
  filter_upwards [hU N j, ae_runMax_eventually_ge_all (N := N) hp0.le m] with U hUj hlev
  obtain ⟨R₀, hR₀⟩ := hUj
  obtain ⟨N₁, hN₁⟩ := hlev i R₀
  refine ⟨max N₁ ⌈64 * (2 * (1 / (eps * (1 - aRec p m) ^ 2)) * K)⌉₊, fun T hT => ?_⟩
  have hTN₁ : N₁ ≤ T := le_trans (le_max_left _ _) hT
  have hTceil : ⌈64 * (2 * (1 / (eps * (1 - aRec p m) ^ 2)) * K)⌉₊ ≤ T :=
    le_trans (le_max_right _ _) hT
  have hM : R₀ ≤ max 0 (SwarmSpeed.runMax (fun s => (trajectory p m U s).pos i) T).toNat := by
    rw [← runMax_eq_speedRunMax (N := N) p m U i T]
    have hmax : max 0 (runMax p m U i T).toNat = (runMax p m U i T).toNat :=
      Nat.max_eq_right (Nat.zero_le _)
    rw [hmax]
    exact hN₁ T hTN₁
  have hb : ∀ x : ℕ, 0 ≤ bCap p m U j x := fun x => bCap_nonneg hp0.le hp1 m U j x
  have hw : ∀ x : ℕ, 0 ≤ wCap p m U j x := fun x => wCap_nonneg p m U j x
  have hbw : ∀ x : ℕ, (bCap p m U j x) ^ 2 ≤ wCap p m U j x :=
    fun x => bCap_sq_le_wCap hp0.le hp1 m U j x
  have hmono : ∀ t : ℕ, (runMax p m U j t).toNat ≤ (runMax p m U j (t + 1)).toNat :=
    fun t => recNat_le_succ p m U j t
  have hstep : ∀ t : ℕ, (runMax p m U j (t + 1)).toNat ≤ (runMax p m U j t).toNat + 1 :=
    fun t => recNat_succ_le p m U j t
  have hbound := SwarmSpatialSq.Jbound_runMax_eventual (a := aRec p m) (ε := eps)
    ha0 ha1 hε hb hw hbw hmono hstep (K := K) (R₀ := R₀) hR₀ T hM
  have hsum : (∑ t ∈ Finset.range T, |Jcorr p m eps i j U t|)
      = ∑ t ∈ Finset.range T, |SwarmJb.Jinc (aRec p m) eps (bCap p m U j)
          (fun s => (trajectory p m U s).pos i) (fun s => (runMax p m U j s).toNat) t| := by
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Jcorr_eq_Jinc]
  rw [hsum]
  have hz : (0 : ℝ) ≤ (((runMax p m U i T : ℤ)) : ℝ) := by
    have h := zero_le_runMax p m U i T
    exact_mod_cast h
  have hmax2 : max 0 (((SwarmSpeed.runMax (fun s => (trajectory p m U s).pos i) T : ℤ)) : ℝ)
      = (((runMax p m U i T : ℤ)) : ℝ) := by
    rw [← runMax_eq_speedRunMax (N := N) p m U i T]
    exact max_eq_right hz
  rw [hmax2] at hbound
  have hBle : 2 * (1 / (eps * (1 - aRec p m) ^ 2)) * K ≤ (1 / 64) * (T : ℝ) := by
    have h1 : 64 * (2 * (1 / (eps * (1 - aRec p m) ^ 2)) * K)
        ≤ (⌈64 * (2 * (1 / (eps * (1 - aRec p m) ^ 2)) * K)⌉₊ : ℝ) :=
      Nat.le_ceil _
    have h2 : ((⌈64 * (2 * (1 / (eps * (1 - aRec p m) ^ 2)) * K)⌉₊ : ℕ) : ℝ) ≤ (T : ℝ) := by
      exact_mod_cast hTceil
    linarith
  calc (∑ t ∈ Finset.range T, |SwarmJb.Jinc (aRec p m) eps (bCap p m U j)
          (fun s => (trajectory p m U s).pos i) (fun s => (runMax p m U j s).toNat) t|)
      ≤ 2 * (1 / (eps * (1 - aRec p m) ^ 2)) * K
          * ((((runMax p m U i T : ℤ)) : ℝ) + 1) :=
        hbound
    _ = 2 * (1 / (eps * (1 - aRec p m) ^ 2)) * K * (((runMax p m U i T : ℤ)) : ℝ)
          + 2 * (1 / (eps * (1 - aRec p m) ^ 2)) * K := by
        ring
    _ ≤ 2 * (1 / (eps * (1 - aRec p m) ^ 2)) * K * (((runMax p m U i T : ℤ)) : ℝ)
          + (1 / 64) * (T : ℝ) := by
        linarith

/-- **`Jsum` with a single `N`-free coefficient** (the shape the occupation ledger consumes). -/
theorem Jsum_eventual_uniform {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) {eps : ℝ} (hε : 0 < eps) :
    ∃ B : ℝ, 0 < B ∧ ∀ (N : ℕ) (i j : Fin N),
      ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
        Jsum p m eps i j U T ≤ B * (((runMax p m U i T : ℤ)) : ℝ) + (1 / 64) * (T : ℝ) := by
  obtain ⟨B, hBpos, hU⟩ := abs_Jcorr_sum_eventual_uniform (p := p) hp0 hp1 hm (eps := eps) hε
  refine ⟨B, hBpos, ?_⟩
  intro N i j
  filter_upwards [hU N i j] with U hU
  obtain ⟨N₀, hN₀⟩ := hU
  exact ⟨N₀, fun T hT => le_trans (Jsum_le_abs_sum p m eps i j U T) (hN₀ T hT)⟩

/-! ## 3. The paper's `N`-uniform lower speed for the constructed process -/

/-- **The paper's lower-speed constant is uniform in `N`.**

The paper's `kappa = 7/(40 C)` with `C = max 1 (A + B)` (its `C` is the occupation coefficient,
here split into the `Z` coefficient `A` and the `J` coefficient `B`).  `A = targetParam p m + 1`
is already an explicit function of `p,m` in `Zbudget_ae_runMax`, the `Q` input is a *rate*
`1/64` with no coefficient, and `B` is the `N`-free record-cost coefficient of
`Jsum_eventual_uniform`.  Hence a single `kappa` works for every walker count at once — the
statement `Swarm.Ballistic` requires `kappa` before `N`, and this is the concrete-array shadow
of that requirement.

The hypotheses are the three occupation budgets in the paper's per-pair form, with the `Z` and
`Q` budgets supplied *internally* (`Zbudget_ae_runMax`, `1/64` rate) and only the record-cost
coefficient and the lower-tail `Q` budget passed in.  No transport to the marginal model class
`Swarm.IsInteractingLaw` is claimed. -/
theorem actual_speed_uniform_of_uniform_JB {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) {B : ℝ} (hB : 0 < B)
    (hJ : ∀ (N : ℕ) (i j : Fin N),
      ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
        Jsum p m (1 / 64) i j U T ≤ B * (((runMax p m U i T : ℤ)) : ℝ) + (1 / 64) * (T : ℝ))
    (hQ : ∀ (N : ℕ) (i j : Fin N), i ≠ j →
      ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
        -((1 / 64 : ℝ) * (T : ℝ))
          ≤ Qcomp p m (1 / 64) (fun t => alphaFun p m t i) i j U T) :
    ∀ (N : ℕ), 2 ≤ N → ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
      7 / (40 * max 1 ((SwarmSpatial.targetParam p m + 1) + B))
        ≤ liminf (fun n : ℕ => ((trajectory p m U n).pos i : ℝ) / n) atTop := by
  intro N hN
  set A : ℝ := SwarmSpatial.targetParam p m + 1 with hA
  have hcoef : ∀ i j : Fin N, i ≠ j →
      SwarmBIA.InterfacesGen p m N (1 / 64) (1 / 64) A B i j := by
    intro i j hij
    filter_upwards [Swarming.Enl.ZBudget.Zbudget_ae_runMax (N := N)
        hp0 hp1 hm (by norm_num : (0 : ℝ) < 1 / 64) i j, hJ N i j, hQ N i j hij]
      with U hZ hJU hQU
    obtain ⟨NZ, hZU⟩ := hZ
    obtain ⟨NJ, hJU⟩ := hJU
    obtain ⟨NQ, hQU⟩ := hQU
    refine ⟨max NZ (max NJ NQ), 0, 0, 0, ?_, ?_, ?_⟩
    · intro T hT
      have hZT := hZU T (le_trans (le_max_left _ _) hT)
      simpa only [← Swarming.Enl.ZBudget.runMax_eq_speed, hA, add_zero] using hZT
    · intro T hT
      have hJT := hJU T (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT)
      linarith
    · intro T hT
      have hQT := hQU T (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT)
      simpa only [sub_zero] using hQT
  exact SwarmBIA.actual_speed_coef_of_interfaces (N := N) hp0 hp1 hm hN
    (by norm_num) (by norm_num) (by norm_num) hcoef

end SwarmUniform

namespace SwarmUniform

open Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl Swarming.Enl.VdriftAssembly Swarming.Enl.JBudgetActual

/-- **One `kappa > 0` for every walker count**, from the repo's named residual input
`SwarmActualBudget.QResidual` alone (quantified over all `N`).  This is
`SwarmActualBudget.actual_occupation_and_speed_of_hQ`'s speed half with the `N`-dependence of the
constant removed; nothing else changes, and `QResidual` remains the only stochastic hypothesis. -/
theorem actual_speed_uniform_of_QResidual {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hQ : ∀ N : ℕ, SwarmActualBudget.QResidual p m N) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ), 2 ≤ N → ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
      κ ≤ liminf (fun n : ℕ => ((trajectory p m U n).pos i : ℝ) / n) atTop := by
  obtain ⟨B, hB, hJ⟩ := Jsum_eventual_uniform (p := p) hp0 hp1 hm
    (eps := 1 / 64) (by norm_num)
  refine ⟨7 / (40 * max 1 ((SwarmSpatial.targetParam p m + 1) + B)), by positivity, ?_⟩
  intro N hN
  exact actual_speed_uniform_of_uniform_JB hp0 hp1 hm hB hJ
    (fun N i j hij => hQ N i j hij) N hN

end SwarmUniform


namespace SwarmUniform

open Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl Swarming.Enl.VdriftAssembly Swarming.Enl.JBudgetActual

/-- **The occupation front with an `N`-free constant**, companion of
`actual_speed_uniform_of_QResidual`.  Same hypotheses, same `1/64` rates, but the coefficient
`max 1 (A + B)` and the time coefficient `1/8` are fixed once and for all. -/
theorem actual_occupation_uniform_of_QResidual {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hQ : ∀ N : ℕ, SwarmActualBudget.QResidual p m N) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 2 ≤ N → ∀ᵐ U ∂(arrayMeasure N),
      ∀ i j : Fin N, i ≠ j → ∃ N₁ : ℕ, ∀ n ≥ N₁,
        SwarmOccTwo.OccOfMax p m N i j U n
          ≤ C * ((SwarmSpeed.runMax (fun t => (trajectory p m U t).pos i) n : ℤ) : ℝ)
            + (1 / 8) * (n : ℝ) := by
  obtain ⟨B, hB, hJ⟩ := Jsum_eventual_uniform (p := p) hp0 hp1 hm
    (eps := 1 / 64) (by norm_num)
  set A : ℝ := SwarmSpatial.targetParam p m + 1 with hA
  refine ⟨max 1 (A + B), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro N hN
  have hcoef : ∀ i j : Fin N, i ≠ j →
      SwarmBIA.InterfacesGen p m N (1 / 64) (1 / 64) A B i j := by
    intro i j hij
    filter_upwards [Swarming.Enl.ZBudget.Zbudget_ae_runMax (N := N)
        hp0 hp1 hm (by norm_num : (0 : ℝ) < 1 / 64) i j, hJ N i j, hQ N i j hij]
      with U hZ hJU hQU
    obtain ⟨NZ, hZU⟩ := hZ
    obtain ⟨NJ, hJU⟩ := hJU
    obtain ⟨NQ, hQU⟩ := hQU
    refine ⟨max NZ (max NJ NQ), 0, 0, 0, ?_, ?_, ?_⟩
    · intro T hT
      have hZT := hZU T (le_trans (le_max_left _ _) hT)
      simpa only [← Swarming.Enl.ZBudget.runMax_eq_speed, hA, add_zero] using hZT
    · intro T hT
      have hJT := hJU T (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT)
      linarith
    · intro T hT
      have hQT := hQU T (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT)
      simpa only [sub_zero] using hQT
  exact SwarmBIA.actual_occ_coef_of_interfaces (N := N) hp0 hp1 hm
    (by norm_num) (by norm_num) (by norm_num) hcoef

end SwarmUniform

