/-
  **`(Mpot)` for the actual array: `∫ (PotMax p m n I hI)² ≤ C log⁴(n+2)`.**

  This file assembles the two previous stages into the unconditional moment bound that
  `Swarm/QVarBound.lean` assumes as `(Mpot)`:

      `hPot : ∀ k, ∫ U, (PotMax p m k I hI U)² ∂(arrayMeasure N) ≤ C₁ log⁴(k+2)`,

  for `1/2 < p < 1`, `2 ≤ m`, `N ≥ 1` and an arbitrary nonempty finite `I : Finset (Fin N)`.
  The constant `Cpot`/`C₁` is explicit: it depends on `p`, `m`, `N` (logarithmically through
  `log N`, exactly as the accepted `(maxmom)` display `maxmom_N` of `areas/marks` does) and on
  nothing else.  The bound proved is in fact a `log²` bound.

  The `log²` rate: the potential `hfix (omegaN)` grows by `2` per unmarked site, and a run of
  `L` unmarked sites in a window of length `n+2` has probability at most
  `|I|(n+2) (1-q)^L`; the maximum over `n` sites of such a geometric tail has a second
  moment of order `(log n)²`, not `n`.
-/
import Swarm.MpotRun
import Mathlib.Analysis.Complex.ExponentialBounds
import Swarm.MpotProb
import Swarm.MpotMoment

set_option maxHeartbeats 3000000

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal BigOperators

namespace SwarmMpot

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmQVariance
open SwarmJointDrift

variable {N : ℕ} {p : ℝ} {m : ℕ}

/-! ### 1. A geometric power under a ceiling -/

theorem rpow_ceil_le {q C : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hC : 0 < C) :
    (1 - q) ^ (Nat.ceil (Real.log C / q)) ≤ 1 / C := by
  have hx0 : (0 : ℝ) < 1 - q := by linarith
  have hlogx : Real.log (1 - q) ≤ -q := by
    have h := Real.log_le_sub_one_of_pos hx0
    linarith
  set T : ℕ := Nat.ceil (Real.log C / q) with hT
  have h1 : Real.log C / q ≤ (T : ℝ) := Nat.le_ceil _
  have h2 : Real.log C ≤ (T : ℝ) * q := by
    have h := mul_le_mul_of_nonneg_right h1 hq0.le
    rw [div_mul_cancel₀ _ hq0.ne'] at h
    exact h
  have h3 : (T : ℝ) * Real.log (1 - q) ≤ (T : ℝ) * (-q) :=
    mul_le_mul_of_nonneg_left hlogx (Nat.cast_nonneg T)
  have h4 : (T : ℝ) * Real.log (1 - q) ≤ -Real.log C := by
    rw [mul_neg] at h3
    linarith
  calc (1 - q) ^ T = Real.exp ((T : ℝ) * Real.log (1 - q)) := by
        rw [Real.exp_nat_mul, Real.exp_log hx0]
    _ ≤ Real.exp (-Real.log C) := Real.exp_le_exp.mpr h4
    _ = 1 / C := by
        rw [Real.exp_neg, Real.exp_log hC]
        ring

/-! ### 2. The `log²` moment bound -/

theorem integral_potMax_sq_le_logsq (hp0 : 1 / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m)
    {I : Finset (Fin N)} (hI : I.Nonempty) (n : ℕ) :
    ∫ U, (PotMax p m n I hI U) ^ 2 ∂(arrayMeasure N)
      ≤ ((2 * p / (2 * p - 1)) + 4) ^ 2
          * (1 + (Nat.ceil (Real.log ((2 * ((n : ℝ) + 2) + 7) * (2 * ((n : ℝ) + 2) + 7)
              * ((I.card : ℝ) * ((n : ℝ) + 2))) / (1 - p) ^ (m - 1)) : ℝ)) ^ 2
        + 1 := by
  have hp : 1 / 2 ≤ p := le_of_lt hp0
  have hp1' : p ≤ 1 := le_of_lt hp1
  have hpm : (0 : ℝ) < 2 * p - 1 := by linarith
  have hK : (0 : ℝ) ≤ 2 * p / (2 * p - 1) := by positivity
  -- the parameters
  set q : ℝ := (1 - p) ^ (m - 1) with hq
  set B : ℝ := 2 * ((n : ℝ) + 2) + 7 with hB
  set M : ℝ := (I.card : ℝ) * ((n : ℝ) + 2) with hM
  have hq0 : 0 < q := by
    rw [hq]; exact pow_pos (by linarith) _
  have hq1 : q < 1 := by
    rw [hq]
    have h1 : (1 - p) ^ (m - 1) ≤ (1 - p) ^ 1 := by
      apply pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
    rw [pow_one] at h1
    linarith
  have hB0 : 0 < B := by rw [hB]; positivity
  have hcard1 : 1 ≤ I.card := Finset.card_pos.mpr hI
  have hM0 : 0 < M := by
    rw [hM]
    have : (0 : ℝ) < (I.card : ℝ) := by exact_mod_cast hcard1
    have : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    positivity
  set T : ℕ := Nat.ceil (Real.log (B * B * M) / q) with hTH
  have hxT : (1 - q) ^ T ≤ 1 / (B * B * M) := by
    rw [hTH]
    exact rpow_ceil_le hq0 hq1 (by positivity)
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hB11 : (11 : ℝ) ≤ B := by rw [hB]; linarith
  have hM2 : (2 : ℝ) ≤ M := by
    rw [hM]
    have h1 : (1 : ℝ) ≤ (I.card : ℝ) := by exact_mod_cast hcard1
    have h2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by linarith
    nlinarith
  have hlogpos : 0 < Real.log (B * B * M) := by
    apply Real.log_pos
    nlinarith
  have hLpos : 1 ≤ T := by
    rw [hTH]
    exact Nat.ceil_pos.mpr (by positivity)
  -- the pointwise bound
  have hpoint : ∀ U : Array N, (PotMax p m n I hI U) ^ 2
      ≤ ((2 * p / (2 * p - 1)) + 4) ^ 2 * (1 + (T : ℝ)) ^ 2
        + Set.indicator (BadRun p m I n T) (fun _ => B * B) U := by
    intro U
    by_cases hU : U ∈ BadRun p m I n T
    · rw [Set.indicator_of_mem hU]
      have hb := PotMax_le (p := p) hp hp1' (m := m) (n := n) (I := I) (hI := hI) (U := U)
      have hbnn := PotMax_nonneg (p := p) hp hp1' (m := m) (n := n) (I := I) (hI := hI)
        (U := U)
      have hBB : B * B = (2 * ((n : ℝ) + 2) + 3 + 4) ^ 2 := by rw [hB]; ring
      have h1 : (PotMax p m n I hI U) ^ 2 ≤ B * B := by
        rw [hBB]
        nlinarith [hb, hbnn]
      have h2 : (0 : ℝ) ≤ ((2 * p / (2 * p - 1)) + 4) ^ 2 * (1 + (T : ℝ)) ^ 2 := by
        have : (0 : ℝ) ≤ 1 + (T : ℝ) := by positivity
        positivity
      linarith
    · rw [Set.indicator_of_notMem hU]
      have hb := potMax_le_of_notMem_badRun (p := p) (m := m) hp0 hp1' I hI hLpos hU
      have hbnn := PotMax_nonneg (p := p) hp hp1' (m := m) (n := n) (I := I) (hI := hI)
        (U := U)
      have h1 : (PotMax p m n I hI U) ^ 2
          ≤ (((2 * p / (2 * p - 1)) + 4) * (1 + (T : ℝ))) ^ 2 := by
        apply pow_le_pow_left₀ hbnn hb
      have h2 : (0 : ℝ) ≤ B * B := by positivity
      nlinarith [h1]
  -- integrate
  have hInt1 : Integrable (fun U => (PotMax p m n I hI U) ^ 2) (arrayMeasure N) :=
    integrable_potMax_sq (p := p) hp hp1' m n I hI
  have hInt2 : Integrable (fun U => ((2 * p / (2 * p - 1)) + 4) ^ 2 * (1 + (T : ℝ)) ^ 2
      + Set.indicator (BadRun p m I n T) (fun _ => B * B) U) (arrayMeasure N) := by
    refine Integrable.add (integrable_const _) ?_
    exact (integrable_const (B * B)).indicator (measurableSet_badRun I n T)
  have hmain : ∫ U, (PotMax p m n I hI U) ^ 2 ∂(arrayMeasure N)
      ≤ ∫ U, (((2 * p / (2 * p - 1)) + 4) ^ 2 * (1 + (T : ℝ)) ^ 2
          + Set.indicator (BadRun p m I n T) (fun _ => B * B) U) ∂(arrayMeasure N) :=
    integral_mono_ae hInt1 hInt2 (Filter.Eventually.of_forall hpoint)
  have hconst : ∫ _U : Array N, ((2 * p / (2 * p - 1)) + 4) ^ 2 * (1 + (T : ℝ)) ^ 2
      ∂(arrayMeasure N) = ((2 * p / (2 * p - 1)) + 4) ^ 2 * (1 + (T : ℝ)) ^ 2 := by
    rw [MeasureTheory.integral_const]
    simp [Measure.real, smul_eq_mul]
  have hind : ∫ U, Set.indicator (BadRun p m I n T) (fun _ => B * B) U ∂(arrayMeasure N)
      = (arrayMeasure N).real (BadRun p m I n T) * (B * B) := by
    rw [MeasureTheory.integral_indicator_const (B * B) (measurableSet_badRun I n T)]
    simp [smul_eq_mul]
  have hbadraw := badRun_real_le (p := p) (m := m) (N := N) (by linarith : (0:ℝ) < p) hp1 I n T
  have hbad : (arrayMeasure N).real (BadRun p m I n T) ≤ M * (1 - q) ^ T := by
    have heq : ((I.card : ℝ) * ((n : ℝ) + 2)) * (1 - (1 - p) ^ (m - 1)) ^ T = M * (1 - q) ^ T := by
      rw [← hM, ← hq]
    rw [← heq]
    exact hbadraw
  have hfin : (arrayMeasure N).real (BadRun p m I n T) * (B * B) ≤ 1 := by
    have hBB : (0 : ℝ) < B * B := by positivity
    calc (arrayMeasure N).real (BadRun p m I n T) * (B * B)
        ≤ (M * (1 - q) ^ T) * (B * B) :=
          mul_le_mul_of_nonneg_right hbad hBB.le
      _ ≤ (M * (1 / (B * B * M))) * (B * B) := by
          apply mul_le_mul_of_nonneg_right _ hBB.le
          exact mul_le_mul_of_nonneg_left hxT hM0.le
      _ = 1 := by
          have h1 : B * B * M ≠ 0 := ne_of_gt (by positivity)
          have h2 : B * B ≠ 0 := ne_of_gt hBB
          field_simp
  have hsplit : ∫ U, (((2 * p / (2 * p - 1)) + 4) ^ 2 * (1 + (T : ℝ)) ^ 2
        + Set.indicator (BadRun p m I n T) (fun _ => B * B) U) ∂(arrayMeasure N)
      = ((2 * p / (2 * p - 1)) + 4) ^ 2 * (1 + (T : ℝ)) ^ 2
        + (arrayMeasure N).real (BadRun p m I n T) * (B * B) := by
    rw [integral_add (integrable_const _)
      ((integrable_const (B * B)).indicator (measurableSet_badRun I n T)), hconst, hind]
  rw [hsplit] at hmain
  linarith [hmain, hfin]

/-! ### 3. The size of the ceiling threshold -/

/-- The threshold `T = ⌈log(B²M)/q⌉` grows like `((log N + 2 log 13 + 3)/q) log(n+2)`. -/
theorem ceil_threshold_le (hp0 : 1 / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m) {I : Finset (Fin N)}
    (hI : I.Nonempty) (n : ℕ) :
    (1 + (Nat.ceil (Real.log ((2 * ((n : ℝ) + 2) + 7) * (2 * ((n : ℝ) + 2) + 7)
        * ((I.card : ℝ) * ((n : ℝ) + 2))) / (1 - p) ^ (m - 1)) : ℝ))
      ≤ ((Real.log N + 2 * Real.log 13 + 3) / (1 - p) ^ (m - 1) + 3)
          * (Real.log ((n : ℝ) + 2) + 1) := by
  have hcard1 : 1 ≤ I.card := Finset.card_pos.mpr hI
  have hN1 : 0 < N := by
    have h := Finset.card_le_univ I
    simp only [Fintype.card_fin] at h
    omega
  set q : ℝ := (1 - p) ^ (m - 1) with hq
  set B : ℝ := 2 * ((n : ℝ) + 2) + 7 with hB
  set M : ℝ := (I.card : ℝ) * ((n : ℝ) + 2) with hM
  have hq0 : 0 < q := by rw [hq]; exact pow_pos (by linarith) _
  have hq1 : q ≤ 1 := by
    rw [hq]
    exact pow_le_one₀ (by linarith) (by linarith)
  have hB0 : 0 < B := by rw [hB]; positivity
  have hM0 : 0 < M := by
    rw [hM]
    have h1 : (0 : ℝ) < (I.card : ℝ) := by exact_mod_cast hcard1
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    positivity
  have hs1 : (1 : ℝ) ≤ Real.log ((n : ℝ) + 2) + 1 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ (n : ℝ) + 2 by linarith)
    linarith
  have hlN : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hl13 : (0 : ℝ) < Real.log 13 := Real.log_pos (by norm_num)
  -- log of the three factors
  have hlogB : Real.log B ≤ Real.log 13 + Real.log ((n : ℝ) + 2) := by
    have h1 : B ≤ 13 * ((n : ℝ) + 2) := by rw [hB]; nlinarith
    have h2 : (0 : ℝ) < 13 * ((n : ℝ) + 2) := by positivity
    calc Real.log B ≤ Real.log (13 * ((n : ℝ) + 2)) := Real.log_le_log hB0 h1
      _ = Real.log 13 + Real.log ((n : ℝ) + 2) := Real.log_mul (by norm_num) (by positivity)
  have hlogM : Real.log M ≤ Real.log N + Real.log ((n : ℝ) + 2) := by
    have hcN : (I.card : ℝ) ≤ (N : ℝ) := by
      have h := Finset.card_le_univ I
      simp only [Fintype.card_fin] at h
      exact_mod_cast h
    have h1 : M ≤ (N : ℝ) * ((n : ℝ) + 2) := by
      rw [hM]; exact mul_le_mul_of_nonneg_right hcN (by positivity)
    have h2 : (0 : ℝ) < (N : ℝ) * ((n : ℝ) + 2) := by
      have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
      positivity
    calc Real.log M ≤ Real.log ((N : ℝ) * ((n : ℝ) + 2)) := Real.log_le_log hM0 h1
      _ = Real.log N + Real.log ((n : ℝ) + 2) :=
          Real.log_mul (by positivity) (by positivity)
  have hlogBM : Real.log (B * B * M)
      ≤ Real.log N + 2 * Real.log 13 + 3 * Real.log ((n : ℝ) + 2) := by
    have he : B * B * M = B ^ 2 * M := by ring
    rw [he, Real.log_mul (by positivity) hM0.ne', Real.log_pow]
    push_cast
    linarith
  have hslope : Real.log (B * B * M)
      ≤ (Real.log N + 2 * Real.log 13 + 3) * (Real.log ((n : ℝ) + 2) + 1) := by
    have hs0 : (0 : ℝ) ≤ Real.log ((n : ℝ) + 2) := by
      exact Real.log_nonneg (show (1 : ℝ) ≤ (n : ℝ) + 2 by linarith)
    nlinarith
  -- the ceiling
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hB11 : (11 : ℝ) ≤ B := by rw [hB]; linarith
  have hM2 : (2 : ℝ) ≤ M := by
    rw [hM]
    have h1 : (1 : ℝ) ≤ (I.card : ℝ) := by exact_mod_cast hcard1
    have h2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by linarith
    nlinarith
  have hlogpos : (0 : ℝ) < Real.log (B * B * M) := by
    apply Real.log_pos
    nlinarith
  have hT : (Nat.ceil (Real.log (B * B * M) / q) : ℝ) < Real.log (B * B * M) / q + 1 :=
    Nat.ceil_lt_add_one (div_nonneg hlogpos.le hq0.le)
  have hdiv : Real.log (B * B * M) / q
      ≤ ((Real.log N + 2 * Real.log 13 + 3) * (Real.log ((n : ℝ) + 2) + 1)) / q :=
    div_le_div_of_nonneg_right hslope hq0.le
  have hkey : (Nat.ceil (Real.log (B * B * M) / q) : ℝ) + 1
      ≤ ((Real.log N + 2 * Real.log 13 + 3) / q) * (Real.log ((n : ℝ) + 2) + 1) + 2 := by
    have h2 : ((Real.log N + 2 * Real.log 13 + 3) * (Real.log ((n : ℝ) + 2) + 1)) / q
        = ((Real.log N + 2 * Real.log 13 + 3) / q) * (Real.log ((n : ℝ) + 2) + 1) := by
      field_simp
    linarith
  have hLq : (0 : ℝ) ≤ (Real.log N + 2 * Real.log 13 + 3) / q := by positivity
  have hAplus : ((Real.log N + 2 * Real.log 13 + 3) / q) * (Real.log ((n : ℝ) + 2) + 1) + 2
      ≤ ((Real.log N + 2 * Real.log 13 + 3) / q + 2) * (Real.log ((n : ℝ) + 2) + 1) := by
    nlinarith
  have hfin : (Nat.ceil (Real.log (B * B * M) / q) : ℝ) + 1
      ≤ ((Real.log N + 2 * Real.log 13 + 3) / q + 2) * (Real.log ((n : ℝ) + 2) + 1) := by
    linarith
  have hmono : ((Real.log N + 2 * Real.log 13 + 3) / q + 2) * (Real.log ((n : ℝ) + 2) + 1)
      ≤ ((Real.log N + 2 * Real.log 13 + 3) / q + 3) * (Real.log ((n : ℝ) + 2) + 1) := by
    have : (0 : ℝ) ≤ Real.log ((n : ℝ) + 2) + 1 := by linarith
    nlinarith
  linarith [hfin, hmono]

/-- The explicit constant of the `log⁴` moment bound. -/
noncomputable def Cpot (p : ℝ) (m N : ℕ) : ℝ :=
  ((2 * p / (2 * p - 1)) + 4) ^ 2
    * ((Real.log N + 2 * Real.log 13 + 3) / (1 - p) ^ (m - 1) + 3) ^ 2 + 1

theorem Cpot_pos (hp0 : 1 / 2 < p) (hp1 : p < 1) (m N : ℕ) : 0 < Cpot p m N := by
  have hq0 : 0 < (1 - p) ^ (m - 1) := pow_pos (by linarith) _
  have hN : (0 : ℝ) ≤ Real.log N := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · simp [hN]
    · exact Real.log_nonneg (by exact_mod_cast hN)
  have hl13 : (0 : ℝ) < Real.log 13 := Real.log_pos (by norm_num)
  have : (0 : ℝ) ≤ (Real.log N + 2 * Real.log 13 + 3) / (1 - p) ^ (m - 1) + 3 := by positivity
  have : (0 : ℝ) < ((Real.log N + 2 * Real.log 13 + 3) / (1 - p) ^ (m - 1) + 3) ^ 2 := by
    positivity
  have h2 : (0 : ℝ) < ((2 * p / (2 * p - 1)) + 4) ^ 2 := by
    have hpm : (0 : ℝ) < 2 * p - 1 := by linarith
    have h1 : (0 : ℝ) ≤ 2 * p / (2 * p - 1) := by positivity
    positivity
  unfold Cpot
  positivity

/-! ### 4. `(Mpot)` in the form assumed by `QVarBound` -/

theorem integral_potMax_sq_le_logsq' (hp0 : 1 / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m)
    {I : Finset (Fin N)} (hI : I.Nonempty) (n : ℕ) :
    ∫ U, (PotMax p m n I hI U) ^ 2 ∂(arrayMeasure N)
      ≤ Cpot p m N * (Real.log ((n : ℝ) + 2) + 1) ^ 2 := by
  have h1 := integral_potMax_sq_le_logsq (p := p) (m := m) (N := N) hp0 hp1 hm hI n
  have h2 := ceil_threshold_le (p := p) (m := m) (N := N) hp0 hp1 hm hI n
  have hA : (0 : ℝ) ≤ ((2 * p / (2 * p - 1)) + 4) ^ 2 := by
    have hpm : (0 : ℝ) < 2 * p - 1 := by linarith
    have h0 : (0 : ℝ) ≤ 2 * p / (2 * p - 1) := by positivity
    positivity
  have hT0 : (0 : ℝ) ≤ 1 + (Nat.ceil (Real.log ((2 * ((n : ℝ) + 2) + 7) * (2 * ((n : ℝ) + 2) + 7)
      * ((I.card : ℝ) * ((n : ℝ) + 2))) / (1 - p) ^ (m - 1)) : ℝ) := by positivity
  have hsq : (1 + (Nat.ceil (Real.log ((2 * ((n : ℝ) + 2) + 7) * (2 * ((n : ℝ) + 2) + 7)
      * ((I.card : ℝ) * ((n : ℝ) + 2))) / (1 - p) ^ (m - 1)) : ℝ)) ^ 2
      ≤ ((Real.log N + 2 * Real.log 13 + 3) / (1 - p) ^ (m - 1) + 3) ^ 2
        * (Real.log ((n : ℝ) + 2) + 1) ^ 2 := by
    have hb : (0 : ℝ) ≤ (Real.log N + 2 * Real.log 13 + 3) / (1 - p) ^ (m - 1) + 3 := by
      have hq0 : (0 : ℝ) < (1 - p) ^ (m - 1) := pow_pos (by linarith) _
      have hlN : (0 : ℝ) ≤ Real.log N := by
        rcases Nat.eq_zero_or_pos N with hN | hN
        · simp [hN]
        · exact Real.log_nonneg (by exact_mod_cast hN)
      have hl13 : (0 : ℝ) < Real.log 13 := Real.log_pos (by norm_num)
      positivity
    have hs : (0 : ℝ) ≤ Real.log ((n : ℝ) + 2) + 1 := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ (n : ℝ) + 2 by linarith)
      linarith
    have h := mul_le_mul h2 h2 hT0 (mul_nonneg hb hs)
    calc (1 + (Nat.ceil (Real.log ((2 * ((n : ℝ) + 2) + 7) * (2 * ((n : ℝ) + 2) + 7)
        * ((I.card : ℝ) * ((n : ℝ) + 2))) / (1 - p) ^ (m - 1)) : ℝ)) ^ 2
        = (1 + (Nat.ceil (Real.log ((2 * ((n : ℝ) + 2) + 7) * (2 * ((n : ℝ) + 2) + 7)
            * ((I.card : ℝ) * ((n : ℝ) + 2))) / (1 - p) ^ (m - 1)) : ℝ))
          * (1 + (Nat.ceil (Real.log ((2 * ((n : ℝ) + 2) + 7) * (2 * ((n : ℝ) + 2) + 7)
            * ((I.card : ℝ) * ((n : ℝ) + 2))) / (1 - p) ^ (m - 1)) : ℝ)) := by ring
      _ ≤ (((Real.log N + 2 * Real.log 13 + 3) / (1 - p) ^ (m - 1) + 3)
            * (Real.log ((n : ℝ) + 2) + 1))
          * (((Real.log N + 2 * Real.log 13 + 3) / (1 - p) ^ (m - 1) + 3)
            * (Real.log ((n : ℝ) + 2) + 1)) := h
      _ = ((Real.log N + 2 * Real.log 13 + 3) / (1 - p) ^ (m - 1) + 3) ^ 2
            * (Real.log ((n : ℝ) + 2) + 1) ^ 2 := by ring
  have hs1 : (1 : ℝ) ≤ (Real.log ((n : ℝ) + 2) + 1) ^ 2 := by
    have hs : (1 : ℝ) ≤ Real.log ((n : ℝ) + 2) + 1 := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ (n : ℝ) + 2 by linarith)
      linarith
    nlinarith
  unfold Cpot
  nlinarith [h1, hsq, hA, hs1]

/-- **`(Mpot)` for the actual array.**  For `1/2 < p < 1`, `2 ≤ m`, `N ≥ 1` (implied by
`I.Nonempty`) and every `n`,

  `∫ PotMax² ≤ max (13 * Cpot p m N) 750 · log⁴(n+2)`,

an unconditional theorem with an explicit constant. -/
theorem hPot_actual (hp0 : 1 / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m) {I : Finset (Fin N)}
    (hI : I.Nonempty) :
    ∀ n : ℕ, ∫ U, (PotMax p m n I hI U) ^ 2 ∂(arrayMeasure N)
      ≤ max (13 * Cpot p m N) 750 * (Real.log ((n : ℝ) + 2)) ^ 4 := by
  have hp : 1 / 2 ≤ p := le_of_lt hp0
  have hp1' : p ≤ 1 := le_of_lt hp1
  intro n
  have hlog2 : (0.6931 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2nn : (0 : ℝ) ≤ Real.log 2 := by linarith
  have hpow2 : (0.2266 : ℝ) < (Real.log 2) ^ 4 := by
    have h1 : (0.6931 : ℝ) ^ 4 ≤ (Real.log 2) ^ 4 := pow_le_pow_left₀ (by norm_num) hlog2.le 4
    have h2 : (0.2266 : ℝ) < (0.6931 : ℝ) ^ 4 := by norm_num
    linarith
  have hC1pos : (0 : ℝ) < max (13 * Cpot p m N) 750 :=
    lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  rcases Nat.lt_or_ge n 2 with hn | hn
  · -- `n ≤ 1`: the crude deterministic bound
    have hb : ∀ U : Array N, PotMax p m n I hI U ≤ 13 := by
      intro U
      have h := PotMax_le (p := p) hp hp1' (m := m) (n := n) (I := I) (hI := hI) (U := U)
      have hn1 : (n : ℝ) ≤ 1 := by
        have : n ≤ 1 := by omega
        exact_mod_cast this
      linarith
    have h2 : ∀ U : Array N, (PotMax p m n I hI U) ^ 2 ≤ 169 := by
      intro U
      have hnn := PotMax_nonneg (p := p) hp hp1' (m := m) (n := n) (I := I) (hI := hI) (U := U)
      nlinarith [hb U]
    have hint : Integrable (fun U => (PotMax p m n I hI U) ^ 2) (arrayMeasure N) :=
      integrable_potMax_sq (p := p) hp hp1' m n I hI
    have h169 : ∫ U, (PotMax p m n I hI U) ^ 2 ∂(arrayMeasure N) ≤ 169 := by
      have := integral_mono_ae hint (integrable_const (169 : ℝ)) (Filter.Eventually.of_forall h2)
      simpa using this
    have hlogle : (Real.log 2) ^ 4 ≤ (Real.log ((n : ℝ) + 2)) ^ 4 := by
      have hn2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hn2
      exact pow_le_pow_left₀ hlog2nn this 4
    have hfin : (169 : ℝ) ≤ max (13 * Cpot p m N) 750 * (Real.log ((n : ℝ) + 2)) ^ 4 := by
      have h750 : (750 : ℝ) ≤ max (13 * Cpot p m N) 750 := le_max_right _ _
      nlinarith
    linarith
  · -- `n ≥ 2`
    have h1 := integral_potMax_sq_le_logsq' (p := p) (m := m) (N := N) hp0 hp1 hm hI n
    have hlog1 : (1 : ℝ) < Real.log ((n : ℝ) + 2) := by
      have hn4 : (4 : ℝ) ≤ (n : ℝ) + 2 := by
        have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      have hl4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        push_cast
        ring
      have hle : Real.log 4 ≤ Real.log ((n : ℝ) + 2) :=
        Real.log_le_log (by norm_num) hn4
      linarith
    have hlog1nn : (0 : ℝ) ≤ Real.log ((n : ℝ) + 2) := by linarith
    have hstep : (Real.log ((n : ℝ) + 2) + 1) ^ 2
        ≤ 4 * (Real.log ((n : ℝ) + 2)) ^ 2 := by nlinarith
    have hstep2 : 4 * (Real.log ((n : ℝ) + 2)) ^ 2
        ≤ 4 * (Real.log ((n : ℝ) + 2)) ^ 4 := by nlinarith
    have hC1 : (13 * Cpot p m N) ≤ max (13 * Cpot p m N) 750 := le_max_left _ _
    have hCpot0 : (0 : ℝ) < Cpot p m N := Cpot_pos hp0 hp1 m N
    have h4 : (4 : ℝ) * Cpot p m N ≤ max (13 * Cpot p m N) 750 := by linarith
    have hCnn : (0 : ℝ) ≤ Cpot p m N := hCpot0.le
    have hlog4nn : (0 : ℝ) ≤ (Real.log ((n : ℝ) + 2)) ^ 4 := by positivity
    nlinarith [h1, hstep, hstep2, h4, hCnn, hlog4nn]


/-! ### 5. `m ≤ 1`: every site is marked, so `PotMax` is uniformly bounded -/

theorem potMax_le_of_small_m (hp : 1 / 2 < p) (hp1 : p ≤ 1) {n : ℕ} {I : Finset (Fin N)}
    (hI : I.Nonempty) (hm : m ≤ 1) (U : Array N) :
    PotMax p m n I hI U ≤ 2 * ((2 * p / (2 * p - 1)) + 4) := by
  have hsm : ∀ (i : Fin N) (x : ℤ), SiteMark p m U i x := by
    intro i x k hk
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hk
    omega
  have hrun : ∀ i ∈ I, NoLongRun p m U i (n + 1) 1 := by
    intro i _ a _
    exact ⟨0, by omega, hsm i ((a + 0 : ℕ) : ℤ)⟩
  have h := potMax_le_of_noLongRun (p := p) (m := m) (N := N) hp hp1 I hI
    (n := n) (L := 1) le_rfl hrun
  have h1 : (1 : ℝ) + (1 : ℕ) = 2 := by norm_num
  calc PotMax p m n I hI U ≤ ((2 * p / (2 * p - 1)) + 4) * (1 + ((1 : ℕ) : ℝ)) := h
    _ = 2 * ((2 * p / (2 * p - 1)) + 4) := by norm_num; ring

/-- **`(Mpot)` for the actual array, no restriction on `m`.** -/
noncomputable def C1 (p : ℝ) (m N : ℕ) : ℝ :=
  max (13 * Cpot p m N) (max 750 (5 * (2 * ((2 * p / (2 * p - 1)) + 4)) ^ 2))

theorem C1_pos (hp0 : 1 / 2 < p) (hp1 : p < 1) (m N : ℕ) : 0 < C1 p m N := by
  have h : (0 : ℝ) < 750 := by norm_num
  have h1 : (750 : ℝ) ≤ max 750 (5 * (2 * ((2 * p / (2 * p - 1)) + 4)) ^ 2) :=
    le_max_left _ _
  have h2a : (750 : ℝ) ≤ max 750 (5 * (2 * ((2 * p / (2 * p - 1)) + 4)) ^ 2) :=
    le_max_left _ _
  have h2 : (750 : ℝ) ≤ max (13 * Cpot p m N)
      (max 750 (5 * (2 * ((2 * p / (2 * p - 1)) + 4)) ^ 2)) :=
    le_trans h2a (le_max_right _ _)
  unfold C1
  linarith

theorem hPot_actual' (hp0 : 1 / 2 < p) (hp1 : p < 1) {I : Finset (Fin N)}
    (hI : I.Nonempty) :
    ∀ n : ℕ, ∫ U, (PotMax p m n I hI U) ^ 2 ∂(arrayMeasure N)
      ≤ C1 p m N * (Real.log ((n : ℝ) + 2)) ^ 4 := by
  have hp : 1 / 2 ≤ p := le_of_lt hp0
  have hp1' : p ≤ 1 := le_of_lt hp1
  by_cases hm : m ≤ 1
  · -- every site is marked
    have h1 : (0 : ℝ) ≤ 5 * (2 * ((2 * p / (2 * p - 1)) + 4)) ^ 2 := by
      have hpm : (0 : ℝ) < 2 * p - 1 := by linarith
      have h0 : (0 : ℝ) ≤ 2 * p / (2 * p - 1) := by positivity
      positivity
    have hle : 5 * (2 * ((2 * p / (2 * p - 1)) + 4)) ^ 2 ≤ C1 p m N := by
      have : (5 * (2 * ((2 * p / (2 * p - 1)) + 4)) ^ 2)
          ≤ max 750 (5 * (2 * ((2 * p / (2 * p - 1)) + 4)) ^ 2) := le_max_right _ _
      have := le_max_right (13 * Cpot p m N)
        (max 750 (5 * (2 * ((2 * p / (2 * p - 1)) + 4)) ^ 2))
      unfold C1
      linarith
    have hlog2 : (0.6931 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hlog2nn : (0 : ℝ) ≤ Real.log 2 := by linarith
    have hpow2 : (0.22 : ℝ) < (Real.log 2) ^ 4 := by
      have h1' : (0.6931 : ℝ) ^ 4 ≤ (Real.log 2) ^ 4 :=
        pow_le_pow_left₀ (by norm_num) hlog2.le 4
      have h2' : (0.22 : ℝ) < (0.6931 : ℝ) ^ 4 := by norm_num
      linarith
    have hCpos : (0 : ℝ) < C1 p m N := C1_pos hp0 hp1 m N
    intro n
    have hb := potMax_le_of_small_m (p := p) (m := m) (N := N) (n := n) hp0 hp1' hI hm
    have hD : ∀ U : Array N, (PotMax p m n I hI U) ^ 2
        ≤ (2 * ((2 * p / (2 * p - 1)) + 4)) ^ 2 := by
      intro U
      have hnn := PotMax_nonneg (p := p) hp hp1' (m := m) (n := n) (I := I) (hI := hI) (U := U)
      have := hb U
      nlinarith
    have hint : Integrable (fun U => (PotMax p m n I hI U) ^ 2) (arrayMeasure N) :=
      integrable_potMax_sq (p := p) hp hp1' m n I hI
    have h169 : ∫ U, (PotMax p m n I hI U) ^ 2 ∂(arrayMeasure N)
        ≤ (2 * ((2 * p / (2 * p - 1)) + 4)) ^ 2 := by
      have := integral_mono_ae hint (integrable_const ((2 * ((2 * p / (2 * p - 1)) + 4)) ^ 2))
        (Filter.Eventually.of_forall hD)
      simpa using this
    have hlogle : (Real.log 2) ^ 4 ≤ (Real.log ((n : ℝ) + 2)) ^ 4 := by
      have hn2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hn2
      exact pow_le_pow_left₀ hlog2nn this 4
    have hfin : (2 * ((2 * p / (2 * p - 1)) + 4)) ^ 2
        ≤ C1 p m N * (Real.log ((n : ℝ) + 2)) ^ 4 := by
      nlinarith [hle, hlogle, hpow2, hCpos, h1]
    linarith
  · -- `m ≥ 2`: the run bound
    push Not at hm
    intro n
    have hmain := hPot_actual (p := p) (m := m) (N := N) hp0 hp1 hm hI n
    have hC1 : max (13 * Cpot p m N) 750 ≤ C1 p m N := by
      have h1 : max (13 * Cpot p m N) 750 ≤ max (13 * Cpot p m N)
          (max 750 (5 * (2 * ((2 * p / (2 * p - 1)) + 4)) ^ 2)) :=
        max_le_max le_rfl (le_max_left _ _)
      unfold C1
      exact h1
    have hCpos : (0 : ℝ) < C1 p m N := C1_pos hp0 hp1 m N
    have hl4nn : (0 : ℝ) ≤ (Real.log ((n : ℝ) + 2)) ^ 4 := by positivity
    have hmul : max (13 * Cpot p m N) 750 * (Real.log ((n : ℝ) + 2)) ^ 4
        ≤ C1 p m N * (Real.log ((n : ℝ) + 2)) ^ 4 := by
      apply mul_le_mul_of_nonneg_right hC1 hl4nn
    linarith


/-! ### 6. The `QVarBound` reduction with `(Mpot)` discharged

  `Swarm/QVarBound.lean` reduces the paper's `(Qslln)` for `Q^{I,J}` to two moment
  premises `(Mpot)` and `(Mdiff)`.  `hPot_actual'` above *is* `(Mpot)`, so the following
  theorem is `Q_log_variance_of_potMoment` with one of its two premises removed.  `(Mdiff)` is
  the only remaining residual, and nothing here claims `Qslln`, `(diam)`, `Ballistic` or a
  common speed. -/

theorem Q_log_variance_of_mdiff {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {C₂ : ℝ} (hC₂ : 0 ≤ C₂)
    (hDiff : ∀ k : ℕ, ∫ U, (siteDiff p m k I J hI U) ^ 2 ∂(arrayMeasure N)
      ≤ C₂ * (Real.log ((k : ℝ) + 2)) ^ 4) :
    (∀ k : ℕ, Integrable
        (fun U => (MartingaleLimit.inc (Q p m I J hI hJ) k U) ^ 2) (arrayMeasure N))
      ∧ ∀ k : ℕ, ∫ U, (MartingaleLimit.inc (Q p m I J hI hJ) k U) ^ 2 ∂(arrayMeasure N)
        ≤ (8 * C1 p m N + 2 * C₂) * (Real.log ((k : ℝ) + 2)) ^ 4 :=
  Q_log_variance_of_potMoment hp0 hp1 m I J hI hJ hid (C1_pos hp0 hp1 m N).le hC₂
    (fun k => hPot_actual' hp0 hp1 hI k) hDiff

end SwarmMpot
