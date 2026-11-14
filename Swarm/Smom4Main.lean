/-
  **`(Smom₄)`: the static fourth moment of the paper's `max_j max_x (h_j(x) + G_j(x))`.**

  This is the display `maxmom` of `main_1d_revised.tex` (Proposition `spatial`) at `s = 4`, for the
  **actual** array `arrayMeasure N` and for the Lean objects of `SwarmSiteDiff`:

      `∫ U, (1 + staticMax p m n I hI U)^4 ∂(arrayMeasure N) ≤ C · log(n+2)^4`,

  with an explicit constant `Csmom4 p m N` depending only on `p`, `m` and `N` (the last only
  through `log N`, as the paper allows for `C_s`), for **every** `m` and every nonempty finite
  `I : Finset (Fin N)`.

  The route is the union bound of the paper's proof in its sharpest finite form: off the event
  `BadRun p m I n T` (some row of `I` has `T` consecutive unmarked sites among `0,…,n+1`) both
  `h_i` and `G_i` are `O(T)` (files `Smom4Run`, `Smom4Moment` and `SwarmMpot.MpotMoment`), while
  the exact run probability `(1-q)^T`, `q = (1-p)^(m-1)`, makes the bad event negligible for
  `T ≍ log(n+2)/q`.  The paper instead integrates an exponential-moment estimate
  (`expmom`) against the same union bound; both give `maxmom`, and this route needs no
  conditional expectation at all.
-/
import Swarm.Smom4Moment
import Swarm.MpotMain

set_option maxHeartbeats 3000000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace SwarmSmom4

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmQVariance SwarmJointDrift SwarmSiteDiff SwarmMpot

variable {N : ℕ} {p : ℝ} {m : ℕ}

/-! ### 1. The `log⁴` moment bound with the ceiling threshold -/

theorem integral_one_add_staticMax_pow_four_le (hp0 : 1 / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m)
    {I : Finset (Fin N)} (hI : I.Nonempty) (n : ℕ) :
    ∫ U, (1 + staticMax p m n I hI U) ^ 4 ∂(arrayMeasure N)
      ≤ Astat p ^ 4
          * (1 + (Nat.ceil (Real.log (((I.card : ℝ) * ((n : ℝ) + 2))
              * (4 * ((n : ℝ) + 2) + 5) ^ 4) / (1 - p) ^ (m - 1)) : ℝ)) ^ 4
        + 1 := by
  haveI := arrayMeasure_isProbabilityMeasure N
  have hp : 1 / 2 ≤ p := hp0.le
  have hp1' : p ≤ 1 := hp1.le
  have hA := Astat_pos hp0
  set q : ℝ := (1 - p) ^ (m - 1) with hq
  set B : ℝ := 4 * ((n : ℝ) + 2) + 5 with hB
  set M : ℝ := (I.card : ℝ) * ((n : ℝ) + 2) with hM
  have hq0 : 0 < q := by rw [hq]; exact pow_pos (by linarith) _
  have hq1 : q < 1 := by
    rw [hq]
    have h1 : (1 - p) ^ (m - 1) ≤ (1 - p) ^ 1 :=
      pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
    rw [pow_one] at h1
    linarith
  have hB0 : 0 < B := by rw [hB]; positivity
  have hcard1 : 1 ≤ I.card := Finset.card_pos.mpr hI
  have hM0 : 0 < M := by
    rw [hM]
    have h1 : (0 : ℝ) < (I.card : ℝ) := by exact_mod_cast hcard1
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    positivity
  set T : ℕ := Nat.ceil (Real.log (M * B ^ 4) / q) with hTH
  have hxT : (1 - q) ^ T ≤ 1 / (M * B ^ 4) := by
    rw [hTH]
    exact rpow_ceil_le hq0 hq1 (by positivity)
  have hTpos : 1 ≤ T := by
    rw [hTH]
    apply Nat.ceil_pos.mpr
    have hcardR : (1 : ℝ) ≤ (I.card : ℝ) := by exact_mod_cast hcard1
    have hn2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by
      have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hM2 : (2 : ℝ) ≤ M := by
      rw [hM]
      have := mul_le_mul hcardR hn2 (by norm_num : (0:ℝ) ≤ 2)
        (by linarith : (0:ℝ) ≤ (I.card : ℝ))
      linarith
    have hB1 : (1 : ℝ) ≤ B := by rw [hB]; nlinarith
    have hB4 : (1 : ℝ) ≤ B ^ 4 := by
      simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hB1 4
    have h1 : (1 : ℝ) < M * B ^ 4 := by
      have := mul_le_mul hM2 hB4 (by norm_num : (0:ℝ) ≤ 1) (by linarith : (0:ℝ) ≤ M)
      linarith
    have h2 : (0 : ℝ) < Real.log (M * B ^ 4) := Real.log_pos h1
    positivity
  -- the pointwise bound
  have hpoint : ∀ U : Array N, (1 + staticMax p m n I hI U) ^ 4
      ≤ Astat p ^ 4 * (1 + (T : ℝ)) ^ 4
        + Set.indicator (BadRun p m I n T) (fun _ => B ^ 4) U := by
    intro U
    by_cases hU : U ∈ BadRun p m I n T
    · rw [Set.indicator_of_mem hU]
      have hb := one_add_staticMax_le_crude hp hp1' (m := m) (n := n) (hI := hI) U
      have hone : (1 : ℝ) ≤ 1 + staticMax p m n I hI U := by
        have := one_le_staticMax' hp hp1' (m := m) (n := n) (hI := hI) U
        linarith
      have h1 : (1 + staticMax p m n I hI U) ^ 4 ≤ B ^ 4 := by
        rw [hB]
        exact pow_le_pow_left₀ (by linarith) hb 4
      have h2 : (0 : ℝ) ≤ Astat p ^ 4 * (1 + (T : ℝ)) ^ 4 := by positivity
      linarith
    · rw [Set.indicator_of_notMem hU]
      have hb := one_add_staticMax_le_of_notMem_badRun hp0 hp1 I hI hTpos hU
      have hone : (1 : ℝ) ≤ 1 + staticMax p m n I hI U := by
        have := one_le_staticMax' hp hp1' (m := m) (n := n) (hI := hI) U
        linarith
      have h1 : (1 + staticMax p m n I hI U) ^ 4 ≤ (Astat p * (1 + (T : ℝ))) ^ 4 :=
        pow_le_pow_left₀ (by linarith) hb 4
      have h2 : (0 : ℝ) ≤ B ^ 4 := by positivity
      calc (1 + staticMax p m n I hI U) ^ 4 ≤ (Astat p * (1 + (T : ℝ))) ^ 4 := h1
        _ = Astat p ^ 4 * (1 + (T : ℝ)) ^ 4 := by ring
        _ ≤ Astat p ^ 4 * (1 + (T : ℝ)) ^ 4 + 0 := le_add_of_nonneg_right le_rfl
  -- integrate
  have hInt1 : Integrable (fun U => (1 + staticMax p m n I hI U) ^ 4) (arrayMeasure N) :=
    integrable_staticMax_fourth hp hp1' hI
  have hInt2 : Integrable (fun U => Astat p ^ 4 * (1 + (T : ℝ)) ^ 4
      + Set.indicator (BadRun p m I n T) (fun _ => B ^ 4) U) (arrayMeasure N) := by
    refine Integrable.add (integrable_const _) ?_
    exact (integrable_const (B ^ 4)).indicator (measurableSet_badRun I n T)
  have hmain : ∫ U, (1 + staticMax p m n I hI U) ^ 4 ∂(arrayMeasure N)
      ≤ ∫ U, (Astat p ^ 4 * (1 + (T : ℝ)) ^ 4
          + Set.indicator (BadRun p m I n T) (fun _ => B ^ 4) U) ∂(arrayMeasure N) :=
    integral_mono_ae hInt1 hInt2 (Filter.Eventually.of_forall hpoint)
  have hconst : ∫ _U : Array N, Astat p ^ 4 * (1 + (T : ℝ)) ^ 4 ∂(arrayMeasure N)
      = Astat p ^ 4 * (1 + (T : ℝ)) ^ 4 := by
    rw [MeasureTheory.integral_const]
    simp [Measure.real, smul_eq_mul]
  have hind : ∫ U, Set.indicator (BadRun p m I n T) (fun _ => B ^ 4) U ∂(arrayMeasure N)
      = (arrayMeasure N).real (BadRun p m I n T) * B ^ 4 := by
    rw [MeasureTheory.integral_indicator_const (B ^ 4) (measurableSet_badRun I n T)]
    simp [smul_eq_mul]
  have hbadraw := badRun_real_le (p := p) (m := m) (N := N) (by linarith : (0 : ℝ) < p) hp1
    I n T
  have hbad : (arrayMeasure N).real (BadRun p m I n T) ≤ M * (1 - q) ^ T := by
    have heq : ((I.card : ℝ) * ((n : ℝ) + 2)) * (1 - (1 - p) ^ (m - 1)) ^ T = M * (1 - q) ^ T := by
      rw [← hM, ← hq]
    rw [← heq]
    exact hbadraw
  have hfin : (arrayMeasure N).real (BadRun p m I n T) * B ^ 4 ≤ 1 := by
    have hBB : (0 : ℝ) < B ^ 4 := by positivity
    calc (arrayMeasure N).real (BadRun p m I n T) * B ^ 4
        ≤ (M * (1 - q) ^ T) * B ^ 4 := mul_le_mul_of_nonneg_right hbad hBB.le
      _ ≤ (M * (1 / (M * B ^ 4))) * B ^ 4 := by
          apply mul_le_mul_of_nonneg_right _ hBB.le
          exact mul_le_mul_of_nonneg_left hxT hM0.le
      _ = 1 := by
          have h1 : M * B ^ 4 ≠ 0 := ne_of_gt (by positivity)
          field_simp
  have hsplit : ∫ U, (Astat p ^ 4 * (1 + (T : ℝ)) ^ 4
        + Set.indicator (BadRun p m I n T) (fun _ => B ^ 4) U) ∂(arrayMeasure N)
      = Astat p ^ 4 * (1 + (T : ℝ)) ^ 4
        + (arrayMeasure N).real (BadRun p m I n T) * B ^ 4 := by
    rw [integral_add (integrable_const _)
      ((integrable_const (B ^ 4)).indicator (measurableSet_badRun I n T)), hconst, hind]
  rw [hsplit] at hmain
  linarith [hmain, hfin]

/-! ### 2. The size of the ceiling threshold -/

theorem ceil_threshold_le_four (hp0 : 1 / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m)
    {I : Finset (Fin N)} (hI : I.Nonempty) (n : ℕ) :
    (1 + (Nat.ceil (Real.log (((I.card : ℝ) * ((n : ℝ) + 2))
        * (4 * ((n : ℝ) + 2) + 5) ^ 4) / (1 - p) ^ (m - 1)) : ℝ))
      ≤ ((Real.log N + 4 * Real.log 13 + 5) / (1 - p) ^ (m - 1) + 3)
          * (Real.log ((n : ℝ) + 2) + 1) := by
  have hcard1 : 1 ≤ I.card := Finset.card_pos.mpr hI
  have hN1 : 0 < N := by
    have h := Finset.card_le_univ I
    simp only [Fintype.card_fin] at h
    omega
  set q : ℝ := (1 - p) ^ (m - 1) with hq
  set B : ℝ := 4 * ((n : ℝ) + 2) + 5 with hB
  set M : ℝ := (I.card : ℝ) * ((n : ℝ) + 2) with hM
  have hq0 : 0 < q := by rw [hq]; exact pow_pos (by linarith) _
  have hB0 : 0 < B := by rw [hB]; positivity
  have hM0 : 0 < M := by
    rw [hM]
    have h1 : (0 : ℝ) < (I.card : ℝ) := by exact_mod_cast hcard1
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    positivity
  have hs1 : (1 : ℝ) ≤ Real.log ((n : ℝ) + 2) + 1 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ (n : ℝ) + 2 by linarith)
    linarith
  have hs0 : (0 : ℝ) ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_nonneg (show (1 : ℝ) ≤ (n : ℝ) + 2 by linarith)
  have hlN : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hl13 : (0 : ℝ) < Real.log 13 := Real.log_pos (by norm_num)
  -- `B ≤ 13 (n+2)`
  have hB13 : B ≤ 13 * ((n : ℝ) + 2) := by
    rw [hB]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have hlogB : Real.log B ≤ Real.log 13 + Real.log ((n : ℝ) + 2) := by
    have h2 : (0 : ℝ) < 13 * ((n : ℝ) + 2) := by positivity
    calc Real.log B ≤ Real.log (13 * ((n : ℝ) + 2)) := Real.log_le_log hB0 hB13
      _ = Real.log 13 + Real.log ((n : ℝ) + 2) := Real.log_mul (by norm_num) (by positivity)
  have hlogM : Real.log M ≤ Real.log N + Real.log ((n : ℝ) + 2) := by
    have hcN : (I.card : ℝ) ≤ (N : ℝ) := by
      have h := Finset.card_le_univ I
      simp only [Fintype.card_fin] at h
      exact_mod_cast h
    have h1 : M ≤ (N : ℝ) * ((n : ℝ) + 2) := by
      rw [hM]
      exact mul_le_mul_of_nonneg_right hcN (by positivity)
    have h2 : (0 : ℝ) < (N : ℝ) * ((n : ℝ) + 2) := by
      have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
      positivity
    calc Real.log M ≤ Real.log ((N : ℝ) * ((n : ℝ) + 2)) := Real.log_le_log hM0 h1
      _ = Real.log N + Real.log ((n : ℝ) + 2) := Real.log_mul (by positivity) (by positivity)
  have hlogMB : Real.log (M * B ^ 4) ≤ Real.log N + 4 * Real.log 13 + 5 * Real.log ((n : ℝ) + 2) := by
    rw [Real.log_mul hM0.ne' (by positivity), Real.log_pow]
    push_cast
    nlinarith [hlogM, hlogB]
  have hslope : Real.log (M * B ^ 4)
      ≤ (Real.log N + 4 * Real.log 13 + 5) * (Real.log ((n : ℝ) + 2) + 1) := by
    nlinarith [hlogMB, hs0]
  have hlogpos : (0 : ℝ) < Real.log (M * B ^ 4) := by
    apply Real.log_pos
    have h2 : (1 : ℝ) ≤ (I.card : ℝ) := by exact_mod_cast hcard1
    have h3 : (2 : ℝ) ≤ (n : ℝ) + 2 := by
      have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have h1 : (2 : ℝ) ≤ M := by
      rw [hM]
      have := mul_le_mul h2 h3 (by norm_num : (0:ℝ) ≤ 2)
        (by linarith : (0:ℝ) ≤ (I.card : ℝ))
      linarith
    have h5 : (1 : ℝ) ≤ B := by rw [hB]; nlinarith
    have h4 : (1 : ℝ) ≤ B ^ 4 := by
      simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) h5 4
    have h6 : (2 : ℝ) ≤ M * B ^ 4 := by
      have := mul_le_mul h1 h4 (by norm_num : (0:ℝ) ≤ 1) (by linarith : (0:ℝ) ≤ M)
      linarith
    linarith
  have hT : (Nat.ceil (Real.log (M * B ^ 4) / q) : ℝ) < Real.log (M * B ^ 4) / q + 1 :=
    Nat.ceil_lt_add_one (div_nonneg hlogpos.le hq0.le)
  have hdiv : Real.log (M * B ^ 4) / q
      ≤ ((Real.log N + 4 * Real.log 13 + 5) * (Real.log ((n : ℝ) + 2) + 1)) / q :=
    div_le_div_of_nonneg_right hslope hq0.le
  have hkey : (Nat.ceil (Real.log (M * B ^ 4) / q) : ℝ) + 1
      ≤ ((Real.log N + 4 * Real.log 13 + 5) / q) * (Real.log ((n : ℝ) + 2) + 1) + 2 := by
    have h2 : ((Real.log N + 4 * Real.log 13 + 5) * (Real.log ((n : ℝ) + 2) + 1)) / q
        = ((Real.log N + 4 * Real.log 13 + 5) / q) * (Real.log ((n : ℝ) + 2) + 1) := by
      field_simp
    linarith
  have hAplus : ((Real.log N + 4 * Real.log 13 + 5) / q) * (Real.log ((n : ℝ) + 2) + 1) + 2
      ≤ ((Real.log N + 4 * Real.log 13 + 5) / q + 2) * (Real.log ((n : ℝ) + 2) + 1) := by
    nlinarith [hs1]
  have hfin : (Nat.ceil (Real.log (M * B ^ 4) / q) : ℝ) + 1
      ≤ ((Real.log N + 4 * Real.log 13 + 5) / q + 2) * (Real.log ((n : ℝ) + 2) + 1) := by
    linarith
  have hmono : ((Real.log N + 4 * Real.log 13 + 5) / q + 2) * (Real.log ((n : ℝ) + 2) + 1)
      ≤ ((Real.log N + 4 * Real.log 13 + 5) / q + 3) * (Real.log ((n : ℝ) + 2) + 1) := by
    have h6 : (0 : ℝ) ≤ Real.log ((n : ℝ) + 2) + 1 := by linarith
    nlinarith [h6]
  have hqeq : (1 - p) ^ (m - 1) = q := rfl
  rw [hqeq, hq, hB, hM] at *
  linarith [hfin, hmono]

/-! ### 3. The explicit constant and `(Smom₄)` -/

/-- The constant of the ceiling: `((log N + 4 log 13 + 5)/q + 3)`. -/
noncomputable def Lsmom4 (p : ℝ) (m N : ℕ) : ℝ :=
  (Real.log N + 4 * Real.log 13 + 5) / (1 - p) ^ (m - 1) + 3

/-- The explicit constant of `(Smom₄)`. -/
noncomputable def Csmom4 (p : ℝ) (m N : ℕ) : ℝ :=
  max (81 * Astat p ^ 4 * Lsmom4 p m N ^ 4 + 5)
    (5 * (2 * Astat p) ^ 4)

theorem Csmom4_pos (hp0 : 1 / 2 < p) (hp1 : p < 1) (m N : ℕ) :
    0 < Csmom4 p m N := by
  have hA := Astat_pos hp0
  have hlN : (0 : ℝ) ≤ Real.log N := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · simp [hN]
    · exact Real.log_nonneg (by exact_mod_cast hN)
  have hl13 : (0 : ℝ) < Real.log 13 := Real.log_pos (by norm_num)
  have hq : (0 : ℝ) < (1 - p) ^ (m - 1) := pow_pos (by linarith) _
  have hL : (0 : ℝ) ≤ Lsmom4 p m N := by
    unfold Lsmom4
    positivity
  have h1 : (0 : ℝ) < 81 * Astat p ^ 4 * Lsmom4 p m N ^ 4 + 5 := by positivity
  unfold Csmom4
  exact lt_of_lt_of_le h1 (le_max_left _ _)

/-- `1 ≤ 5·log(n+2)^4`: the elementary factor used to absorb the additive `1`. -/
theorem one_le_five_mul_log_pow_four (n : ℕ) :
    (1 : ℝ) ≤ 5 * (Real.log ((n : ℝ) + 2)) ^ 4 := by
  have hlog2 : (0.6931 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by
    have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hmono : Real.log 2 ≤ Real.log ((n : ℝ) + 2) := Real.log_le_log (by norm_num) h2
  have hpow : (0.2307 : ℝ) < (Real.log ((n : ℝ) + 2)) ^ 4 := by
    have h1 : (0.6931 : ℝ) ^ 4 ≤ (Real.log ((n : ℝ) + 2)) ^ 4 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 4
    have h2' : (0.2307 : ℝ) < (0.6931 : ℝ) ^ 4 := by norm_num
    linarith
  linarith

/-- **`(Smom₄)`, the static `maxmom` at `s = 4`, for the actual array and every `m ≥ 2`.** -/
theorem hSmom4_actual_ge_two (hp0 : 1 / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m)
    {I : Finset (Fin N)} (hI : I.Nonempty) :
    ∀ n : ℕ, ∫ U, (1 + staticMax p m n I hI U) ^ 4 ∂(arrayMeasure N)
      ≤ Csmom4 p m N * (Real.log ((n : ℝ) + 2)) ^ 4 := by
  haveI := arrayMeasure_isProbabilityMeasure N
  have hp : 1 / 2 ≤ p := hp0.le
  have hp1' : p ≤ 1 := hp1.le
  have hA := Astat_pos hp0
  intro n
  have hmain := integral_one_add_staticMax_pow_four_le hp0 hp1 hm hI n
  have hthr := ceil_threshold_le_four hp0 hp1 hm hI n
  have hT0 : (0 : ℝ) ≤ 1 + (Nat.ceil (Real.log (((I.card : ℝ) * ((n : ℝ) + 2))
      * (4 * ((n : ℝ) + 2) + 5) ^ 4) / (1 - p) ^ (m - 1)) : ℝ) := by positivity
  have hL0 : (0 : ℝ) ≤ Lsmom4 p m N := by
    unfold Lsmom4
    have hlN : (0 : ℝ) ≤ Real.log N := by
      rcases Nat.eq_zero_or_pos N with hN | hN
      · simp [hN]
      · exact Real.log_nonneg (by exact_mod_cast hN)
    have hl13 : (0 : ℝ) < Real.log 13 := Real.log_pos (by norm_num)
    have hq : (0 : ℝ) < (1 - p) ^ (m - 1) := pow_pos (by linarith) _
    positivity
  have hs0 : (0 : ℝ) ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_nonneg (show (1 : ℝ) ≤ (n : ℝ) + 2 by linarith)
  -- `1 ≤ 2·log(n+2)`, hence `log(n+2) + 1 ≤ 3·log(n+2)`
  have hlog2 : (0.6931 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hn2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by
    have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hlogmono : Real.log 2 ≤ Real.log ((n : ℝ) + 2) := Real.log_le_log (by norm_num) hn2
  have h2log : (1 : ℝ) ≤ 2 * Real.log ((n : ℝ) + 2) := by nlinarith
  have hstep1 : (1 + (Nat.ceil (Real.log (((I.card : ℝ) * ((n : ℝ) + 2))
      * (4 * ((n : ℝ) + 2) + 5) ^ 4) / (1 - p) ^ (m - 1)) : ℝ)) ^ 4
      ≤ Lsmom4 p m N ^ 4 * (Real.log ((n : ℝ) + 2) + 1) ^ 4 := by
    have h1 : (1 + (Nat.ceil (Real.log (((I.card : ℝ) * ((n : ℝ) + 2))
        * (4 * ((n : ℝ) + 2) + 5) ^ 4) / (1 - p) ^ (m - 1)) : ℝ))
        ≤ Lsmom4 p m N * (Real.log ((n : ℝ) + 2) + 1) := by
      have := hthr
      unfold Lsmom4
      linarith
    calc (1 + (Nat.ceil (Real.log (((I.card : ℝ) * ((n : ℝ) + 2))
          * (4 * ((n : ℝ) + 2) + 5) ^ 4) / (1 - p) ^ (m - 1)) : ℝ)) ^ 4
        ≤ (Lsmom4 p m N * (Real.log ((n : ℝ) + 2) + 1)) ^ 4 :=
          pow_le_pow_left₀ hT0 h1 4
      _ = Lsmom4 p m N ^ 4 * (Real.log ((n : ℝ) + 2) + 1) ^ 4 := by ring
  have hstep2 : (Real.log ((n : ℝ) + 2) + 1) ^ 4
      ≤ 81 * (Real.log ((n : ℝ) + 2)) ^ 4 := by
    have h1 : Real.log ((n : ℝ) + 2) + 1 ≤ 3 * Real.log ((n : ℝ) + 2) := by linarith
    calc (Real.log ((n : ℝ) + 2) + 1) ^ 4 ≤ (3 * Real.log ((n : ℝ) + 2)) ^ 4 :=
          pow_le_pow_left₀ (by linarith) h1 4
      _ = 81 * (Real.log ((n : ℝ) + 2)) ^ 4 := by ring
  have hbig : Astat p ^ 4 * (1 + (Nat.ceil (Real.log (((I.card : ℝ) * ((n : ℝ) + 2))
      * (4 * ((n : ℝ) + 2) + 5) ^ 4) / (1 - p) ^ (m - 1)) : ℝ)) ^ 4 + 1
      ≤ (81 * Astat p ^ 4 * Lsmom4 p m N ^ 4 + 5) * (Real.log ((n : ℝ) + 2)) ^ 4 := by
    have hA4 : (0 : ℝ) ≤ Astat p ^ 4 := by positivity
    have hL4 : (0 : ℝ) ≤ Lsmom4 p m N ^ 4 := by positivity
    have hlog4 : (0 : ℝ) ≤ (Real.log ((n : ℝ) + 2)) ^ 4 := by positivity
    have h1 : Astat p ^ 4 * (1 + (Nat.ceil (Real.log (((I.card : ℝ) * ((n : ℝ) + 2))
        * (4 * ((n : ℝ) + 2) + 5) ^ 4) / (1 - p) ^ (m - 1)) : ℝ)) ^ 4
        ≤ Astat p ^ 4 * (Lsmom4 p m N ^ 4 * (Real.log ((n : ℝ) + 2) + 1) ^ 4) :=
      mul_le_mul_of_nonneg_left hstep1 hA4
    have h2 : Astat p ^ 4 * (Lsmom4 p m N ^ 4 * (Real.log ((n : ℝ) + 2) + 1) ^ 4)
        ≤ Astat p ^ 4 * (Lsmom4 p m N ^ 4 * (81 * (Real.log ((n : ℝ) + 2)) ^ 4)) := by
      have h3 := mul_le_mul_of_nonneg_left hstep2 hL4
      nlinarith [h3, hA4]
    have h3 : Astat p ^ 4 * (Lsmom4 p m N ^ 4 * (81 * (Real.log ((n : ℝ) + 2)) ^ 4))
        = (81 * Astat p ^ 4 * Lsmom4 p m N ^ 4) * (Real.log ((n : ℝ) + 2)) ^ 4 := by ring
    have hone := one_le_five_mul_log_pow_four n
    have h5 : (0 : ℝ) ≤ 81 * Astat p ^ 4 * Lsmom4 p m N ^ 4 := by positivity
    nlinarith [h1, h2, h3, hone, h5, hlog4]
  have hC1 : (81 * Astat p ^ 4 * Lsmom4 p m N ^ 4 + 5) ≤ Csmom4 p m N := by
    unfold Csmom4
    exact le_max_left _ _
  have hlog4nn : (0 : ℝ) ≤ (Real.log ((n : ℝ) + 2)) ^ 4 := by positivity
  calc ∫ U, (1 + staticMax p m n I hI U) ^ 4 ∂(arrayMeasure N)
      ≤ (81 * Astat p ^ 4 * Lsmom4 p m N ^ 4 + 5) * (Real.log ((n : ℝ) + 2)) ^ 4 :=
        le_trans hmain hbig
    _ ≤ Csmom4 p m N * (Real.log ((n : ℝ) + 2)) ^ 4 :=
        mul_le_mul_of_nonneg_right hC1 hlog4nn

/-- **`(Smom₄)` for every `m`.**  For `m ≤ 1` every site is marked, so `staticMax` is uniformly
bounded by `2·Astat p` and the `log⁴` shape is immediate. -/
theorem hSmom4_actual (hp0 : 1 / 2 < p) (hp1 : p < 1) {I : Finset (Fin N)} (hI : I.Nonempty) :
    ∀ n : ℕ, ∫ U, (1 + staticMax p m n I hI U) ^ 4 ∂(arrayMeasure N)
      ≤ Csmom4 p m N * (Real.log ((n : ℝ) + 2)) ^ 4 := by
  haveI := arrayMeasure_isProbabilityMeasure N
  have hp : 1 / 2 ≤ p := hp0.le
  have hp1' : p ≤ 1 := hp1.le
  have hA := Astat_pos hp0
  by_cases hm : m ≤ 1
  · intro n
    have hb : ∀ U : Array N, (1 + staticMax p m n I hI U) ^ 4 ≤ (2 * Astat p) ^ 4 := by
      intro U
      have hsmU : ∀ (i : Fin N) (x : ℤ), SiteMark p m U i x := by
        intro i x k hk
        obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hk
        omega
      have hnotmem : U ∉ BadRun p m I n 1 := by
        intro hmem
        simp only [BadRun, Set.mem_iUnion] at hmem
        obtain ⟨i, hi, a, ha, hrun'⟩ := hmem
        have hsite : ((a + 0 : ℕ) : ℤ)
            ∈ (Finset.range 1).image (fun j : ℕ => ((a + j : ℕ) : ℤ)) :=
          Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), rfl⟩
        exact hrun' ((a + 0 : ℕ) : ℤ) hsite (hsmU i ((a + 0 : ℕ) : ℤ))
      have h1 := one_add_staticMax_le_of_notMem_badRun hp0 hp1 I hI (L := 1) le_rfl hnotmem
      have hone : (1 : ℝ) ≤ 1 + staticMax p m n I hI U := by
        have := one_le_staticMax' hp hp1' (m := m) (n := n) (hI := hI) U
        linarith
      have h2 : 1 + staticMax p m n I hI U ≤ 2 * Astat p := by
        have hA1 := Astat_ge_one hp0
        have h3 : ((1 : ℕ) : ℝ) = 1 := by norm_num
        rw [h3] at h1
        nlinarith
      exact pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ 1 + staticMax p m n I hI U) h2 4
    have hint := integrable_staticMax_fourth hp hp1' (m := m) (n := n) (I := I) hI
    have hle : ∫ U, (1 + staticMax p m n I hI U) ^ 4 ∂(arrayMeasure N)
        ≤ (2 * Astat p) ^ 4 := by
      have := integral_mono_ae hint (integrable_const ((2 * Astat p) ^ 4))
        (Filter.Eventually.of_forall hb)
      simpa using this
    have h5C : (5 * (2 * Astat p) ^ 4) ≤ Csmom4 p m N := by
      unfold Csmom4
      exact le_max_right _ _
    have hone := one_le_five_mul_log_pow_four n
    have h6 : (0 : ℝ) ≤ (2 * Astat p) ^ 4 := by positivity
    calc ∫ U, (1 + staticMax p m n I hI U) ^ 4 ∂(arrayMeasure N)
        ≤ (2 * Astat p) ^ 4 := hle
      _ ≤ Csmom4 p m N * (Real.log ((n : ℝ) + 2)) ^ 4 := by nlinarith
  · push Not at hm
    exact hSmom4_actual_ge_two hp0 hp1 hm hI

end SwarmSmom4
