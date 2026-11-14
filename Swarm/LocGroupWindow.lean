/-
# The `(locgroup)` deviation estimate from the predictable `GoodW` envelope

The paper's Proposition `local` needs display `(locgroup)` (`main_1d.tex`, l. 1005): on the local
good event, for disjoint nonempty `I, J` and a window on which `(sep)` holds at every time,

  `W_t^{I,J} - W_s^{I,J} <= C_T L^{3/4}`.

The tree already supplies every *ingredient* of the corresponding martingale estimate:

* `LocGroupQ.GoodW` — the predictable event `(sep) ∧ Efix ≤ B ∧ Esum ≤ B`, with
  `LocGroupQ.measurableSet_goodW_posFilt` (it is `posFilt n`-measurable);
* `LocGroupQ.abs_WA_step_le_of_goodW` — the one-step size `|W_{n+1} - W_n| ≤ envB p B` on `GoodW`;
* `SwarmJointDrift.condExp_indicator_WA_drift_le_zero` — the paper's `(Wdrift)` as a genuine
  conditional-expectation inequality `E[1_{GoodW}(W_{n+1}-W_n) | F_n] ≤ 0`;
* `LocMax.measure_max_abs_psum_ge_le_ae` — the maximal two-sided Azuma--Hoeffding inequality with
  an arbitrary a.e. envelope;
* `LocScaleArithmetic.envB`/`truncLevel`/`exp_arg_ge` — the deterministic scale arithmetic.

What was missing (and is what this file supplies) is the *truncated* martingale together with its
telescoping, i.e. precisely steps 1--3 of `areas/martingale/LOCGROUP_ENVELOPE.md`:

* `incT` — the `GoodW`-truncated increment `1_{GoodW_n}(W_{n+1}^{I,J} - W_n^{I,J})`, integrable and
  bounded by `envB p B` *pointwise*, not only on `GoodW`;
* `dQT` — its centred version, a genuine `posFilt`-martingale difference
  (`condExp_dQT`), with `|dQT| ≤ 2 envB` a.e. (`ae_abs_dQT_le`);
* `ae_telescope_goodW` — on a window on which `GoodW` holds at *every* time, the drift terms are
  nonpositive and therefore `W_{s+K} - W_s ≤ Σ_{k<K} dQT_{s+k}`;
* `measure_goodW_window_le` — the resulting maximal deviation estimate
  `μ{window good ∧ ε < W_{s+K} - W_s} ≤ 2 (K+1) exp (-ε²/(4 K (2 envB)²))`.

Because the truncation is by `GoodW ⊆ (sep)`, the deviation event itself *contains* the whole
"separation survival" hypothesis: unlike a bound for the untruncated `Q^{I,J}`, there is no
separation-failure remainder to control separately. The second half of the file instantiates the
estimate at the paper's local scale `H = G = L^{1/16}`, `ε = L^{3/4}`, `K ≤ T L`, where
`2 envB + 1 ≤ 321 N L^{1/8}` (`LocScaleArithmetic.two_envB_truncLevel_le`) gives the exponent
`L^{1/4}/(4 (321 N)^2 T)`, stronger than the paper's `L^{1/16}`.

Scope, stated exactly.  Nothing here constructs the `(locmax)` event, the `(locsum)` event, the
record window `[τ_r, τ_r + TL]`, or the defect/tightness chain; the window hypotheses are the
explicit interface of `measure_locmax_window_le`, and no separation-survival, invariant-law,
regeneration or terminal `(locmove)` statement is claimed.  No `sorry`, no extra axiom, no
`native_decide`.
-/
import Swarm.GroupQ2
import Swarm.ScaleArithmetic

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace LocGroupWindow

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance LocGroupQ

variable {N : ℕ}

/-! ## 1. The one-step envelope of `GoodW` -/

/-- The paper's one-step envelope at the truncation level `B`, i.e. the right-hand side of
`abs_WA_step_le_of_goodW`.  It is `LocScaleArithmetic.envB`, so the local-scale arithmetic of
`ScaleArithmetic.lean` applies to it without a second definition. -/
noncomputable def stepEnv (p : ℝ) (B : ℝ) : ℝ := LocScaleArithmetic.envB p N B

theorem stepEnv_eq (p : ℝ) (B : ℝ) :
    stepEnv (N := N) p B
      = 2 * B + 2 * (((2 * p - 1) / p) * (N : ℝ) * ((1 + B) * B)) := rfl

theorem stepEnv_nonneg {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ stepEnv (N := N) p B :=
  LocScaleArithmetic.envB_nonneg hp0 hp1 hB

theorem stepEnv_pos {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) {B : ℝ} (hB : 0 < B) :
    0 < stepEnv (N := N) p B := by
  have hp : (0 : ℝ) < p := by linarith
  have hc : 0 ≤ (2 * p - 1) / p := div_nonneg (by linarith) hp.le
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hprod : 0 ≤ (1 + B) * B := mul_nonneg (by linarith) hB.le
  have h2 : 0 ≤ ((2 * p - 1) / p) * (N : ℝ) * ((1 + B) * B) :=
    mul_nonneg (mul_nonneg hc hN) hprod
  rw [stepEnv_eq]
  linarith

theorem stepEnv_le_quad {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) {B : ℝ} (hB : 0 ≤ B) :
    stepEnv (N := N) p B ≤ 2 * B + 2 * ((N : ℝ) * ((1 + B) * B)) :=
  LocScaleArithmetic.envB_le_quad hp0 hp1 hB

/-! ## 2. The `GoodW`-truncated increment and its centred version -/

/-- The `GoodW`-truncated increment `1_{GoodW_n}(W_{n+1}^{I,J} - W_n^{I,J})`.  Outside the
predictable good event it is *defined* to be zero, so its envelope holds pointwise. -/
noncomputable def incT (p : ℝ) (m : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty)
    (hJ : J.Nonempty) (B : ℝ) (n : ℕ) (U : Array N) : ℝ :=
  ({U | GoodW p m n I J hI B U}).indicator
    (fun U => WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ) U

/-- The centred truncated increment: the paper's `dQ^{I,J}` for the `GoodW`-truncated process. -/
noncomputable def dQT (p : ℝ) (m : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty)
    (hJ : J.Nonempty) (B : ℝ) (n : ℕ) (U : Array N) : ℝ :=
  incT p m I J hI hJ B n U
    - condExp (posFilt N p m n) (arrayMeasure N) (incT p m I J hI hJ B n) U

theorem incT_of_mem {p : ℝ} {m n : ℕ} {I J : Finset (Fin N)} {hI : I.Nonempty}
    {hJ : J.Nonempty} {B : ℝ} {U : Array N}
    (hU : U ∈ {U : Array N | GoodW p m n I J hI B U}) :
    incT p m I J hI hJ B n U
      = WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ := by
  have h : incT p m I J hI hJ B n U
      = ({U : Array N | GoodW p m n I J hI B U}).indicator
          (fun U => WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ) U := rfl
  rw [h, Set.indicator_of_mem hU]

theorem incT_of_notMem {p : ℝ} {m n : ℕ} {I J : Finset (Fin N)} {hI : I.Nonempty}
    {hJ : J.Nonempty} {B : ℝ} {U : Array N}
    (hU : U ∉ {U : Array N | GoodW p m n I J hI B U}) :
    incT p m I J hI hJ B n U = 0 := by
  have h : incT p m I J hI hJ B n U
      = ({U : Array N | GoodW p m n I J hI B U}).indicator
          (fun U => WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ) U := rfl
  rw [h, Set.indicator_of_notMem hU]

/-! ## 3. Measurability, integrability, orthogonality -/

theorem measurable_incT_succ (p : ℝ) (m n : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty)
    (hJ : J.Nonempty) (B : ℝ) :
    Measurable[posFilt N p m (n + 1)] (incT p m I J hI hJ B n) := by
  have h1 : Measurable[posFilt N p m (n + 1)] (fun U => WA p m U (n + 1) I J hI hJ) :=
    measurable_WA_posFilt p m (n + 1) I J hI hJ
  have h2 : Measurable[posFilt N p m (n + 1)] (fun U => WA p m U n I J hI hJ) :=
    (measurable_WA_posFilt p m n I J hI hJ).mono ((posFilt N p m).mono (Nat.le_succ n)) le_rfl
  have h3 : MeasurableSet[posFilt N p m (n + 1)] {U : Array N | GoodW p m n I J hI B U} :=
    ((posFilt N p m).mono (Nat.le_succ n)) _
      (measurableSet_goodW_posFilt p m n I J hI B)
  exact (h1.sub h2).indicator h3

theorem integrable_incT {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (B : ℝ) :
    Integrable (incT p m I J hI hJ B n) (arrayMeasure N) :=
  ((integrable_WA hp hp1 m (n + 1) I J hI hJ).sub
      (integrable_WA hp hp1 m n I J hI hJ)).indicator
    (((posFilt N p m).le n) _ (measurableSet_goodW_posFilt p m n I J hI B))

theorem integrable_condExp_incT {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (B : ℝ) :
    Integrable (fun U => condExp (posFilt N p m n) (arrayMeasure N)
      (incT p m I J hI hJ B n) U) (arrayMeasure N) := by
  haveI := integrable_incT (N := N) hp hp1 m n I J hI hJ B
  exact integrable_condExp

theorem integrable_dQT {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (B : ℝ) :
    Integrable (dQT p m I J hI hJ B n) (arrayMeasure N) :=
  (integrable_incT (N := N) hp hp1 m n I J hI hJ B).sub
    (integrable_condExp_incT (N := N) hp hp1 m n I J hI hJ B)

theorem stronglyMeasurable_incT_succ (p : ℝ) (m n : ℕ) (I J : Finset (Fin N))
    (hI : I.Nonempty) (hJ : J.Nonempty) (B : ℝ) :
    StronglyMeasurable[posFilt N p m (n + 1)] (incT p m I J hI hJ B n) :=
  (measurable_incT_succ p m n I J hI hJ B).stronglyMeasurable

theorem stronglyMeasurable_dQT (p : ℝ) (m n : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty)
    (hJ : J.Nonempty) (B : ℝ) :
    StronglyMeasurable[posFilt N p m (n + 1)] (dQT p m I J hI hJ B n) := by
  have hinc : StronglyMeasurable[posFilt N p m (n + 1)] (fun U => incT p m I J hI hJ B n U) :=
    (measurable_incT_succ p m n I J hI hJ B).stronglyMeasurable
  have hce : StronglyMeasurable[posFilt N p m (n + 1)]
      (fun U => condExp (posFilt N p m n) (arrayMeasure N) (incT p m I J hI hJ B n) U) :=
    stronglyMeasurable_mono_filt (stronglyMeasurable_condExp (μ := arrayMeasure N)
      (m := posFilt N p m n) (f := incT p m I J hI hJ B n))
      ((posFilt N p m).mono (Nat.le_succ n))
  exact hinc.sub hce

/-- The truncated centred increment is a `posFilt`-martingale difference. -/
theorem condExp_dQT {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (B : ℝ) :
    condExp (posFilt N p m n) (arrayMeasure N) (dQT p m I J hI hJ B n)
      =ᵐ[arrayMeasure N] 0 := by
  have hX := integrable_incT (N := N) hp hp1 m n I J hI hJ B
  have hY := integrable_condExp_incT (N := N) hp hp1 m n I J hI hJ B
  have hsub : condExp (posFilt N p m n) (arrayMeasure N) (dQT p m I J hI hJ B n)
      =ᵐ[arrayMeasure N]
        condExp (posFilt N p m n) (arrayMeasure N) (incT p m I J hI hJ B n)
          - condExp (posFilt N p m n) (arrayMeasure N)
              (fun U => condExp (posFilt N p m n) (arrayMeasure N)
                (incT p m I J hI hJ B n) U) :=
    condExp_sub hX hY _
  have hpull : condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => condExp (posFilt N p m n) (arrayMeasure N)
        (incT p m I J hI hJ B n) U)
      = fun U => condExp (posFilt N p m n) (arrayMeasure N)
          (incT p m I J hI hJ B n) U :=
    condExp_of_stronglyMeasurable ((posFilt N p m).le n) stronglyMeasurable_condExp hY
  refine hsub.trans ?_
  rw [hpull]
  filter_upwards with U
  simp

/-- The paper's `(Wdrift)` for the truncated process: the truncation is by a `posFilt n`-measurable
subset of `(sep)`, so the conditional mean of the truncated increment is nonpositive. -/
theorem condExp_incT_nonpos {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m n : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    (B : ℝ) :
    condExp (posFilt N p m n) (arrayMeasure N) (incT p m I J hI hJ B n)
      ≤ᵐ[arrayMeasure N] 0 := by
  have h := condExp_indicator_WA_drift_le_zero (N := N) hp0 hp1 m n I J hI hJ hid
    (A₀ := {U : Array N | GoodW p m n I J hI B U})
    (measurableSet_goodW_posFilt p m n I J hI B) (fun U hU => hU.1)
  have heq : (fun U : Array N => ({U : Array N | GoodW p m n I J hI B U}).indicator
      (fun U => WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ) U)
      = incT p m I J hI hJ B n := rfl
  rw [heq] at h
  exact h

/-! ## 4. Pointwise and a.e. envelopes -/

/-- The truncated increment is bounded by the paper's step envelope *everywhere*. -/
theorem abs_incT_le {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {B : ℝ} (hB : 0 ≤ B) (U : Array N) :
    |incT p m I J hI hJ B n U| ≤ stepEnv (N := N) p B := by
  by_cases hU : GoodW p m n I J hI B U
  · rw [incT_of_mem (U := U) (show U ∈ {U : Array N | GoodW p m n I J hI B U} from hU),
      stepEnv_eq]
    exact abs_WA_step_le_of_goodW hp0 hp1 I J hI hJ hid hU
  · rw [incT_of_notMem (U := U) (show U ∉ {U : Array N | GoodW p m n I J hI B U} from hU),
      abs_zero]
    exact stepEnv_nonneg hp0 hp1 hB

/-- The conditional mean of the truncated increment has the same envelope a.e. -/
theorem ae_abs_condExp_incT_le {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {B : ℝ} (hB : 0 ≤ B) :
    ∀ᵐ U ∂(arrayMeasure N),
      |condExp (posFilt N p m n) (arrayMeasure N) (incT p m I J hI hJ B n) U|
        ≤ stepEnv (N := N) p B := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  set E := stepEnv (N := N) p B with hE
  have hE0 : 0 ≤ E := stepEnv_nonneg hp0 hp1 hB
  have h1 := abs_condExp_ae_le_condExp_abs (μ := arrayMeasure N) (m := posFilt N p m n)
    (f := incT p m I J hI hJ B n)
  have hbdd : (|incT p m I J hI hJ B n|) ≤ᵐ[arrayMeasure N] fun _ => E :=
    Filter.Eventually.of_forall (fun U => abs_incT_le (m := m) (n := n) hp0 hp1 I J hI hJ hid hB U)
  have h2 : condExp (posFilt N p m n) (arrayMeasure N) (|incT p m I J hI hJ B n|)
      ≤ᵐ[arrayMeasure N] condExp (posFilt N p m n) (arrayMeasure N) (fun _ => E) :=
    condExp_mono ((integrable_incT (N := N) hp0.le hp1 m n I J hI hJ B).abs)
      (integrable_const E) hbdd
  have h3 : condExp (posFilt N p m n) (arrayMeasure N) (fun _ => E) = fun _ => E :=
    condExp_const ((posFilt N p m).le n) E
  filter_upwards [h1, h2] with U h1U h2U
  have h3U : condExp (posFilt N p m n) (arrayMeasure N) (fun _ => E) U = E := by rw [h3]
  calc |condExp (posFilt N p m n) (arrayMeasure N) (incT p m I J hI hJ B n) U|
      ≤ condExp (posFilt N p m n) (arrayMeasure N) (|incT p m I J hI hJ B n|) U := h1U
    _ ≤ condExp (posFilt N p m n) (arrayMeasure N) (fun _ => E) U := h2U
    _ = E := h3U

/-- **The martingale differences have the doubled envelope a.e.** -/
theorem ae_abs_dQT_le {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {B : ℝ} (hB : 0 ≤ B) :
    ∀ᵐ U ∂(arrayMeasure N), |dQT p m I J hI hJ B n U| ≤ 2 * stepEnv (N := N) p B := by
  filter_upwards [ae_abs_condExp_incT_le (N := N) hp0 hp1 I J hI hJ hid hB] with U hU
  have h2 := abs_incT_le (m := m) (n := n) hp0 hp1 I J hI hJ hid hB U
  have hd : dQT p m I J hI hJ B n U
      = incT p m I J hI hJ B n U
        - condExp (posFilt N p m n) (arrayMeasure N) (incT p m I J hI hJ B n) U := rfl
  rw [hd]
  calc |incT p m I J hI hJ B n U
        - condExp (posFilt N p m n) (arrayMeasure N) (incT p m I J hI hJ B n) U|
      = |incT p m I J hI hJ B n U
          + (-condExp (posFilt N p m n) (arrayMeasure N) (incT p m I J hI hJ B n) U)| := by
        rw [sub_eq_add_neg]
    _ ≤ |incT p m I J hI hJ B n U|
        + |-condExp (posFilt N p m n) (arrayMeasure N) (incT p m I J hI hJ B n) U| := abs_add_le _ _
    _ = |incT p m I J hI hJ B n U|
        + |condExp (posFilt N p m n) (arrayMeasure N) (incT p m I J hI hJ B n) U| := by
        rw [abs_neg]
    _ ≤ stepEnv (N := N) p B + stepEnv (N := N) p B := add_le_add h2 hU
    _ = 2 * stepEnv (N := N) p B := by ring


/-! ## 5. The shifted filtration of a window starting at `s` -/

/-- The position filtration reindexed to a window starting at `s`: `ℱ k = posFilt (s + k)`.
`LocMax.measure_max_abs_psum_ge_le_ae` needs a filtration indexed from `0`, while the paper's
`(locgroup)` increments live at the absolute times `s, …, s + K - 1`. -/
noncomputable def shiftedFilt (p : ℝ) (m s : ℕ) :
    Filtration ℕ (inferInstance : MeasurableSpace (Array N)) where
  seq k := posFilt N p m (s + k)
  mono' := by
    intro a b hab
    exact (posFilt N p m).mono (Nat.add_le_add_left hab s)
  le' := by
    intro k
    exact (posFilt N p m).le (s + k)

/-- **Maximal deviation of the truncated process.**  For disjoint nonempty `I, J`, `B > 0`,
`K ≥ 1` and `ε > 0` with the Chernoff side condition `ε ≤ 4 K envB`,

  `μ{∃ k ≤ K, ε ≤ |Σ_{j<k} dQT_{s+j}|} ≤ 2 (K+1) exp (-ε²/(4 K (2 envB p B)²))`.

This is the maximal Azuma--Hoeffding inequality of `LocMaxVar` instantiated at the `GoodW`
truncation, on the shifted filtration `k ↦ posFilt (s+k)`. -/
theorem measure_deviation_goodW_le {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {B : ℝ} (hB : 0 < B) {s K : ℕ} (hK : 1 ≤ K) {ε : ℝ} (hε : 0 < ε)
    (hside : ε ≤ 4 * (K : ℝ) * stepEnv (N := N) p B) :
    (arrayMeasure N).real
      {U : Array N | ∃ k ≤ K,
        ε ≤ |LocMart.psum (fun j => dQT p m I J hI hJ B (s + j)) k U|}
      ≤ 2 * ((K : ℝ) + 1) *
          Real.exp (-(ε ^ 2) / (4 * ((K : ℝ) * (2 * stepEnv (N := N) p B) ^ 2))) := by
  haveI hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hp1' : p ≤ 1 := le_of_lt hp1
  set E : ℝ := stepEnv (N := N) p B with hE
  have hEpos : 0 < E := stepEnv_pos hp0 hp1' hB
  set S : ℝ := (K : ℝ) * (2 * E) ^ 2 with hS
  have hSpos : 0 < S := by
    have h2 : (0 : ℝ) < 2 * E := by linarith
    rw [hS]
    positivity
  have hproxy : LocMax.proxy (fun _ : ℕ => 2 * E) K ≤ S := by
    have h : LocMax.proxy (fun _ : ℕ => 2 * E) K = (K : ℝ) * (2 * E) ^ 2 := by
      simp only [LocMax.proxy, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [h, hS]
  have hmeas : ∀ k < K, StronglyMeasurable[(shiftedFilt (N := N) p m s) (k + 1)]
      (fun U => dQT p m I J hI hJ B (s + k) U) := by
    intro k hk
    exact stronglyMeasurable_dQT p m (s + k) I J hI hJ B
  have hcpos : ∀ k < K, 0 < (fun _ : ℕ => 2 * E) k := by
    intro k hk
    have h2 : (0 : ℝ) < 2 * E := by linarith
    exact h2
  have hbdd : ∀ k < K, ∀ᵐ U ∂(arrayMeasure N),
      |(fun U => dQT p m I J hI hJ B (s + k) U) U| ≤ (fun _ : ℕ => 2 * E) k := by
    intro k hk
    simpa only [hE] using ae_abs_dQT_le (N := N) hp0 hp1' I J hI hJ hid hB.le (n := s + k)
  have hmean : ∀ k < K,
      (arrayMeasure N)[(fun U => dQT p m I J hI hJ B (s + k) U)
        | ↑((shiftedFilt (N := N) p m s) k)] =ᵐ[arrayMeasure N] 0 := by
    intro k hk
    exact condExp_dQT hp0.le hp1' m (s + k) I J hI hJ B
  have hsideK : ∀ k < K, ε * (fun _ : ℕ => 2 * E) k ≤ 2 * S := by
    intro k hk
    have h2 : (0 : ℝ) < 2 * E := by linarith
    have hcalc : ε * (2 * E) ≤ (4 * (K : ℝ) * E) * (2 * E) := by
      have := mul_le_mul_of_nonneg_right hside (le_of_lt h2)
      simpa only [hE] using this
    have hS8 : 2 * S = 8 * ((K : ℝ) * E ^ 2) := by
      rw [hS]; ring
    rw [hS8]
    calc ε * (2 * E) ≤ (4 * (K : ℝ) * E) * (2 * E) := hcalc
      _ = 8 * ((K : ℝ) * E ^ 2) := by ring
  have key := LocMax.measure_max_abs_psum_ge_le_ae (μ := arrayMeasure N)
    (ℱ := shiftedFilt (N := N) p m s)
    (ξ := fun k U => dQT p m I J hI hJ B (s + k) U) (c := fun _ : ℕ => 2 * E)
    (ε := ε) (n := K) (S := S) hK hSpos hproxy hmeas hcpos hbdd hmean hε hsideK
  rw [hS, hE] at key
  exact key

/-! ## 6. Telescoping on a window on which `GoodW` holds at every time -/

/-- **The paper's summation of `(Wdrift)` for the truncated process.**  Almost surely, for every
window `[s, s+K)` on which `GoodW` holds at every time, the drift corrections are nonpositive and

  `W_{s+K}^{I,J} - W_s^{I,J} ≤ Q_{s+K} - Q_s = Σ_{k<K} dQ_{s+k}`. -/
theorem ae_telescope_goodW {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    (B : ℝ) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ s K : ℕ,
      (∀ k, s ≤ k → k < s + K → GoodW p m k I J hI B U) →
      WA p m U (s + K) I J hI hJ ≤ WA p m U s I J hI hJ
        + LocMart.psum (fun j => dQT p m I J hI hJ B (s + j)) K U := by
  have hdrift : ∀ᵐ U ∂(arrayMeasure N), ∀ k : ℕ,
      condExp (posFilt N p m k) (arrayMeasure N) (incT p m I J hI hJ B k) U ≤ 0 :=
    ae_all_iff.mpr (fun k => condExp_incT_nonpos (N := N) hp0 hp1 m k I J hI hJ hid B)
  filter_upwards [hdrift] with U hU s K hgood
  have hpt : ∀ k, s ≤ k → k < s + K →
      WA p m U (k + 1) I J hI hJ - WA p m U k I J hI hJ
        ≤ dQT p m I J hI hJ B k U := by
    intro k hk hkt
    have hG : GoodW p m k I J hI B U := hgood k hk hkt
    have hinc := incT_of_mem (hJ := hJ) (U := U) (show U ∈ {U : Array N | GoodW p m k I J hI B U} from hG)
    have hd : dQT p m I J hI hJ B k U
        = incT p m I J hI hJ B k U
          - condExp (posFilt N p m k) (arrayMeasure N) (incT p m I J hI hJ B k) U := rfl
    have hd0 := hU k
    linarith
  have haux := telescope_aux (a := fun n => WA p m U n I J hI hJ)
    (c := fun n => dQT p m I J hI hJ B n U) (s := s) (s + K)
    (Nat.le_add_right s K) hpt
  have hsplit : ∑ k ∈ Finset.range (s + K), dQT p m I J hI hJ B k U
      = ∑ k ∈ Finset.range s, dQT p m I J hI hJ B k U
        + ∑ j ∈ Finset.range K, dQT p m I J hI hJ B (s + j) U := by
    have h := Finset.sum_range_add (fun k => dQT p m I J hI hJ B k U) s K
    simpa only [Nat.add_comm] using h
  rw [hsplit] at haux
  simp only [LocMart.psum]
  linarith

/-! ## 7. The maximal deviation estimate -/

/-- **`(locgroup)` as a maximal deviation estimate, with no separation-survival remainder.**

For disjoint nonempty `I, J`, every truncation level `B > 0` and every window `[s, s+K)`,

  `μ{ GoodW at every time in [s, s+K) and ε < W_{s+K}^{I,J} - W_s^{I,J} }`
    `≤ 2 (K+1) exp (-ε² / (4 K (2 envB p B)²))`.

The Chernoff side condition `ε ≤ 4 K envB p B` is explicit; at the paper's parameters
(`ε = L^{3/4}`, `K ≤ T L`, `envB ≈ L^{1/8}`) it holds for large `L`. -/
theorem measure_goodW_window_le {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {B : ℝ} (hB : 0 < B) {s K : ℕ} (hK : 1 ≤ K) {ε : ℝ} (hε : 0 < ε)
    (hside : ε ≤ 4 * (K : ℝ) * stepEnv (N := N) p B) :
    (arrayMeasure N).real
      {U : Array N |
        (∀ k, s ≤ k → k < s + K → GoodW p m k I J hI B U) ∧
        ε < WA p m U (s + K) I J hI hJ - WA p m U s I J hI hJ}
      ≤ 2 * ((K : ℝ) + 1) *
          Real.exp (-(ε ^ 2) / (4 * ((K : ℝ) * (2 * stepEnv (N := N) p B) ^ 2))) := by
  haveI hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hp1' : p ≤ 1 := le_of_lt hp1
  set E : ℝ := stepEnv (N := N) p B with hE
  have hEpos : 0 < E := stepEnv_pos hp0 hp1' hB
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  set S : ℝ := (K : ℝ) * (2 * E) ^ 2 with hS
  have hSpos : 0 < S := by
    have h2 : (0 : ℝ) < 2 * E := by linarith
    rw [hS]
    positivity
  -- the maximal Azuma--Hoeffding inequality for the shifted process
  have hproxy : LocMax.proxy (fun _ : ℕ => 2 * E) K ≤ S := by
    have h : LocMax.proxy (fun _ : ℕ => 2 * E) K = (K : ℝ) * (2 * E) ^ 2 := by
      simp only [LocMax.proxy, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [h, hS]
  have hmeas : ∀ k < K, StronglyMeasurable[(shiftedFilt (N := N) p m s) (k + 1)]
      (fun U => dQT p m I J hI hJ B (s + k) U) := by
    intro k hk
    exact stronglyMeasurable_dQT p m (s + k) I J hI hJ B
  have hcpos : ∀ k < K, 0 < (fun _ : ℕ => 2 * E) k := by
    intro k hk
    have h2 : (0 : ℝ) < 2 * E := by linarith
    exact h2
  have hbdd : ∀ k < K, ∀ᵐ U ∂(arrayMeasure N),
      |(fun U => dQT p m I J hI hJ B (s + k) U) U| ≤ (fun _ : ℕ => 2 * E) k := by
    intro k hk
    simpa only [hE] using ae_abs_dQT_le (N := N) hp0 hp1' I J hI hJ hid hB.le (n := s + k)
  have hmean : ∀ k < K,
      (arrayMeasure N)[(fun U => dQT p m I J hI hJ B (s + k) U)
        | ↑((shiftedFilt (N := N) p m s) k)] =ᵐ[arrayMeasure N] 0 := by
    intro k hk
    exact condExp_dQT hp0.le hp1' m (s + k) I J hI hJ B
  have hsideK : ∀ k < K, ε * (fun _ : ℕ => 2 * E) k ≤ 2 * S := by
    intro k hk
    have h2 : (0 : ℝ) < 2 * E := by linarith
    have hEk : (0 : ℝ) ≤ E := hEpos.le
    have hcalc : ε * (2 * E) ≤ (4 * (K : ℝ) * E) * (2 * E) := by
      have := mul_le_mul_of_nonneg_right hside (le_of_lt h2)
      simpa only [hE] using this
    have hS8 : 2 * S = 8 * ((K : ℝ) * E ^ 2) := by
      rw [hS]; ring
    rw [hS8]
    calc ε * (2 * E) ≤ (4 * (K : ℝ) * E) * (2 * E) := hcalc
      _ = 8 * ((K : ℝ) * E ^ 2) := by ring
  have key := LocMax.measure_max_abs_psum_ge_le_ae (μ := arrayMeasure N)
    (ℱ := shiftedFilt (N := N) p m s)
    (ξ := fun k U => dQT p m I J hI hJ B (s + k) U) (c := fun _ : ℕ => 2 * E)
    (ε := ε) (n := K) (S := S) hK hSpos hproxy hmeas hcpos hbdd hmean hε hsideK
  -- the a.e. telescoping identity
  have htel : ∀ᵐ U ∂(arrayMeasure N), ∀ s' K' : ℕ,
      (∀ k, s' ≤ k → k < s' + K' → GoodW p m k I J hI B U) →
      WA p m U (s' + K') I J hI hJ ≤ WA p m U s' I J hI hJ
        + LocMart.psum (fun j => dQT p m I J hI hJ B (s' + j)) K' U :=
    ae_telescope_goodW hp0 hp1 I J hI hJ hid B
  -- the deviation event is contained in the martingale excursion, off a null set
  have hsub : {U : Array N |
        (∀ k, s ≤ k → k < s + K → GoodW p m k I J hI B U) ∧
        ε < WA p m U (s + K) I J hI hJ - WA p m U s I J hI hJ}
      ⊆ {U : Array N | ∃ k ≤ K,
            ε ≤ |LocMart.psum (fun k U => dQT p m I J hI hJ B (s + k) U) k U|}
        ∪ {U : Array N | ¬ (∀ s' K' : ℕ,
            (∀ k, s' ≤ k → k < s' + K' → GoodW p m k I J hI B U) →
            WA p m U (s' + K') I J hI hJ ≤ WA p m U s' I J hI hJ
              + LocMart.psum (fun j => dQT p m I J hI hJ B (s' + j)) K' U)} := by
    intro U hU
    by_cases hUT : ∀ s' K' : ℕ,
        (∀ k, s' ≤ k → k < s' + K' → GoodW p m k I J hI B U) →
        WA p m U (s' + K') I J hI hJ ≤ WA p m U s' I J hI hJ
          + LocMart.psum (fun j => dQT p m I J hI hJ B (s' + j)) K' U
    · left
      obtain ⟨hwin, hadv⟩ := hU
      have hle := hUT s K hwin
      have hgt : ε < LocMart.psum (fun j => dQT p m I J hI hJ B (s + j)) K U := by
        linarith
      exact ⟨K, le_rfl, le_trans (le_of_lt hgt) (le_abs_self _)⟩
    · exact Or.inr hUT
  have hT0 : (arrayMeasure N).real {U : Array N | ¬ (∀ s' K' : ℕ,
        (∀ k, s' ≤ k → k < s' + K' → GoodW p m k I J hI B U) →
        WA p m U (s' + K') I J hI hJ ≤ WA p m U s' I J hI hJ
          + LocMart.psum (fun j => dQT p m I J hI hJ B (s' + j)) K' U)} = 0 := by
    have hzero : (arrayMeasure N) {U : Array N | ¬ (∀ s' K' : ℕ,
        (∀ k, s' ≤ k → k < s' + K' → GoodW p m k I J hI B U) →
        WA p m U (s' + K') I J hI hJ ≤ WA p m U s' I J hI hJ
          + LocMart.psum (fun j => dQT p m I J hI hJ B (s' + j)) K' U)} = 0 :=
      MeasureTheory.ae_iff.mp htel
    rw [MeasureTheory.measureReal_eq_zero_iff]
    exact hzero
  calc (arrayMeasure N).real
        {U : Array N |
          (∀ k, s ≤ k → k < s + K → GoodW p m k I J hI B U) ∧
          ε < WA p m U (s + K) I J hI hJ - WA p m U s I J hI hJ}
      ≤ (arrayMeasure N).real
          ({U : Array N | ∃ k ≤ K,
              ε ≤ |LocMart.psum (fun k U => dQT p m I J hI hJ B (s + k) U) k U|}
            ∪ {U : Array N | ¬ (∀ s' K' : ℕ,
              (∀ k, s' ≤ k → k < s' + K' → GoodW p m k I J hI B U) →
              WA p m U (s' + K') I J hI hJ ≤ WA p m U s' I J hI hJ
                + LocMart.psum (fun j => dQT p m I J hI hJ B (s' + j)) K' U)}) :=
        MeasureTheory.measureReal_mono hsub (by finiteness)
    _ ≤ (arrayMeasure N).real {U : Array N | ∃ k ≤ K,
            ε ≤ |LocMart.psum (fun k U => dQT p m I J hI hJ B (s + k) U) k U|}
          + (arrayMeasure N).real {U : Array N | ¬ (∀ s' K' : ℕ,
              (∀ k, s' ≤ k → k < s' + K' → GoodW p m k I J hI B U) →
              WA p m U (s' + K') I J hI hJ ≤ WA p m U s' I J hI hJ
                + LocMart.psum (fun j => dQT p m I J hI hJ B (s' + j)) K' U)} :=
        MeasureTheory.measureReal_union_le _ _
    _ = (arrayMeasure N).real {U : Array N | ∃ k ≤ K,
            ε ≤ |LocMart.psum (fun k U => dQT p m I J hI hJ B (s + k) U) k U|} := by
        rw [hT0, add_zero]
    _ ≤ 2 * ((K : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * S)) := key
    _ = 2 * ((K : ℝ) + 1) *
          Real.exp (-(ε ^ 2) / (4 * ((K : ℝ) * (2 * stepEnv (N := N) p B) ^ 2))) := by
        rw [hS, hE]

/-! ## 8. The `(locmax)` interface: the same estimate with the static envelope hypotheses -/

/-- **`(locgroup)` from the `(locmax)` window hypotheses.**  If, throughout the window `[s, s+K)`,
the walkers are separated and every walker of `I` has its static potential and static tail sum
bounded by `H` resp. `G` on the truncated site range, then the deviation estimate holds with the
truncation level `B = max (2H+6) (2G)`.

The hypotheses are exactly the fields discharged by `(locmax)`
(`R2bLocMaxG.array_locmax_hG`) together with `(sep)`; no separation-survival bound is charged. -/
theorem measure_locmax_window_le {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {H G : ℝ} (hH1 : 1 ≤ H) {s K : ℕ} (hK : 1 ≤ K) {ε : ℝ} (hε : 0 < ε)
    (hside : ε ≤ 4 * (K : ℝ) * stepEnv (N := N) p (max (2 * H + 6) (2 * G))) :
    (arrayMeasure N).real
      {U : Array N |
        (∀ k, s ≤ k → k < s + K →
          SepSet p m k I J U ∧
          (∀ i ∈ I, ∀ u ≤ xTop p m k (I ∪ J) (hI.mono Finset.subset_union_left) U,
            hfix (omegaN p m U i) u ≤ H) ∧
          (∀ i ∈ I, ∀ u ≤ xTop p m k (I ∪ J) (hI.mono Finset.subset_union_left) U,
            Gtail p m U i u (k + 2) ≤ G)) ∧
        ε < WA p m U (s + K) I J hI hJ - WA p m U s I J hI hJ}
      ≤ 2 * ((K : ℝ) + 1) *
          Real.exp (-(ε ^ 2) /
            (4 * ((K : ℝ) * (2 * stepEnv (N := N) p (max (2 * H + 6) (2 * G))) ^ 2))) := by
  have hp1' : p ≤ 1 := le_of_lt hp1
  have hB : 0 < max (2 * H + 6) (2 * G) :=
    lt_of_lt_of_le (by linarith : (0 : ℝ) < 2 * H + 6) (le_max_left _ _)
  have hmain := measure_goodW_window_le (N := N) (m := m) (s := s) (K := K)
    (B := max (2 * H + 6) (2 * G)) (ε := ε) hp0 hp1 I J hI hJ hid hB hK hε hside
  refine le_trans (MeasureTheory.measureReal_mono ?_ (by finiteness)) hmain
  intro U hU
  obtain ⟨hwin, hadv⟩ := hU
  exact ⟨fun k hk hkt => goodW_of_locmax (N := N) (H := H) (G := G) (U := U) hp0 hp1'
    I J hI hJ hid (hwin k hk hkt).1 hH1 (hwin k hk hkt).2.1 (hwin k hk hkt).2.2, hadv⟩

/-! ## 9. The paper's local scale `H = G = L^{1/16}`, `ε = L^{3/4}` -/

/-- The envelope dominates its linear part. -/
theorem le_stepEnv {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) {B : ℝ} (hB : 0 ≤ B) :
    2 * B ≤ stepEnv (N := N) p B := by
  have hp : (0 : ℝ) < p := by linarith
  have hc : 0 ≤ (2 * p - 1) / p := div_nonneg (by linarith) hp.le
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hprod : 0 ≤ (1 + B) * B := mul_nonneg (by linarith) hB
  have h2 : 0 ≤ 2 * (((2 * p - 1) / p) * (N : ℝ) * ((1 + B) * B)) := by
    have h3 : 0 ≤ ((2 * p - 1) / p) * (N : ℝ) * ((1 + B) * B) :=
      mul_nonneg (mul_nonneg hc hN) hprod
    linarith
  rw [stepEnv_eq]
  linarith

/-- At the paper's truncation level the envelope is at least `4 L^{1/16}`. -/
theorem truncLevel_le_stepEnv {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) {L : ℝ} (hL : 1 ≤ L) :
    4 * L ^ ((1 : ℝ) / 16) ≤ stepEnv (N := N) p (LocScaleArithmetic.truncLevel L) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have h0 : (0 : ℝ) ≤ L ^ ((1 : ℝ) / 16) := Real.rpow_nonneg hL0.le _
  have hB : 0 ≤ LocScaleArithmetic.truncLevel L := by
    rw [LocScaleArithmetic.truncLevel_eq hL]; linarith
  have h1 := le_stepEnv (N := N) hp0 hp1 hB
  have h2 : 2 * L ^ ((1 : ℝ) / 16) ≤ LocScaleArithmetic.truncLevel L := by
    rw [LocScaleArithmetic.truncLevel_eq hL]; linarith
  calc 4 * L ^ ((1 : ℝ) / 16) = 2 * (2 * L ^ ((1 : ℝ) / 16)) := by ring
    _ ≤ 2 * LocScaleArithmetic.truncLevel L := by linarith
    _ ≤ stepEnv (N := N) p (LocScaleArithmetic.truncLevel L) := h1

/-- `L^{3/4} ≤ 16 L^{17/16} = 16 L L^{1/16}` for `L ≥ 1`. -/
theorem rpow_three_quarters_le {L : ℝ} (hL : 1 ≤ L) :
    L ^ ((3 : ℝ) / 4) ≤ 16 * (L * L ^ ((1 : ℝ) / 16)) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hmul : L * L ^ ((1 : ℝ) / 16) = L ^ ((17 : ℝ) / 16) := by
    calc L * L ^ ((1 : ℝ) / 16)
        = L ^ (1 : ℝ) * L ^ ((1 : ℝ) / 16) := by rw [Real.rpow_one]
      _ = L ^ ((1 : ℝ) + (1 : ℝ) / 16) := (Real.rpow_add hL0 1 ((1 : ℝ) / 16)).symm
      _ = L ^ ((17 : ℝ) / 16) := by norm_num
  rw [hmul]
  have hsplit : L ^ ((17 : ℝ) / 16) = L ^ ((3 : ℝ) / 4) * L ^ ((5 : ℝ) / 16) := by
    have harg : ((17 : ℝ) / 16) = (3 : ℝ) / 4 + (5 : ℝ) / 16 := by norm_num
    rw [harg, Real.rpow_add hL0]
  rw [hsplit]
  have h516 : (1 : ℝ) ≤ L ^ ((5 : ℝ) / 16) := Real.one_le_rpow hL (by norm_num)
  have h34 : (0 : ℝ) < L ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hL0 _
  nlinarith

/-- **`(locgroup)` at the paper's local scale.**

For disjoint nonempty `I, J`, `1 ≤ N`, `L ≥ 1`, `T > 0` and a window `[s, s+K)` of length
`L ≤ K ≤ T L` on which the walkers are separated and the static `(locmax)` envelope is
`H = G = L^{1/16}`, the group observable gains at most `L^{3/4}` off a set of measure

  `2 (K+1) exp (-L^{1/4} / (4 (321 N)^2 T))`,

which is display `(locgroup)` at the paper's own scale, with the strictly stronger exponent
`L^{1/4}` in place of `L^{1/16}`. -/
theorem measure_truncLevel_window_le {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    (hN : 1 ≤ N) {L T : ℝ} (hL : 1 ≤ L) (hT : 0 < T) {s K : ℕ} (hK : 1 ≤ K)
    (hLK : L ≤ (K : ℝ)) (hKL : (K : ℝ) ≤ T * L) :
    (arrayMeasure N).real
      {U : Array N |
        (∀ k, s ≤ k → k < s + K →
          SepSet p m k I J U ∧
          (∀ i ∈ I, ∀ u ≤ xTop p m k (I ∪ J) (hI.mono Finset.subset_union_left) U,
            hfix (omegaN p m U i) u ≤ L ^ ((1 : ℝ) / 16)) ∧
          (∀ i ∈ I, ∀ u ≤ xTop p m k (I ∪ J) (hI.mono Finset.subset_union_left) U,
            Gtail p m U i u (k + 2) ≤ L ^ ((1 : ℝ) / 16))) ∧
        L ^ ((3 : ℝ) / 4) < WA p m U (s + K) I J hI hJ - WA p m U s I J hI hJ}
      ≤ 2 * ((K : ℝ) + 1) *
          Real.exp (-(L ^ ((1 : ℝ) / 4) / (4 * (321 * (N : ℝ)) ^ 2 * T))) := by
  have hp1' : p ≤ 1 := le_of_lt hp1
  have hL0 : (0 : ℝ) < L := by linarith
  have hH1 : (1 : ℝ) ≤ L ^ ((1 : ℝ) / 16) := Real.one_le_rpow hL (by norm_num)
  have hε : (0 : ℝ) < L ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hL0 _
  have hEeq : stepEnv (N := N) p
        (max (2 * L ^ ((1 : ℝ) / 16) + 6) (2 * L ^ ((1 : ℝ) / 16)))
      = LocScaleArithmetic.envB p N (LocScaleArithmetic.truncLevel L) := rfl
  have hE4 : 4 * L ^ ((1 : ℝ) / 16)
      ≤ stepEnv (N := N) p (max (2 * L ^ ((1 : ℝ) / 16) + 6) (2 * L ^ ((1 : ℝ) / 16))) := by
    rw [hEeq]
    exact truncLevel_le_stepEnv (N := N) hp0 hp1' hL
  have hside : L ^ ((3 : ℝ) / 4)
      ≤ 4 * (K : ℝ) * stepEnv (N := N) p
          (max (2 * L ^ ((1 : ℝ) / 16) + 6) (2 * L ^ ((1 : ℝ) / 16))) := by
    have h1 : (4 : ℝ) * L ≤ 4 * (K : ℝ) := by linarith
    have h0 : (0 : ℝ) ≤ 4 * L ^ ((1 : ℝ) / 16) := by
      have := Real.rpow_nonneg hL0.le ((1 : ℝ) / 16)
      linarith
    have h2 : 4 * L * (4 * L ^ ((1 : ℝ) / 16)) ≤ 4 * (K : ℝ) * (4 * L ^ ((1 : ℝ) / 16)) :=
      mul_le_mul_of_nonneg_right h1 h0
    have h3 : 4 * (K : ℝ) * (4 * L ^ ((1 : ℝ) / 16))
        ≤ 4 * (K : ℝ) * stepEnv (N := N) p
            (max (2 * L ^ ((1 : ℝ) / 16) + 6) (2 * L ^ ((1 : ℝ) / 16))) := by
      have hK0 : (0 : ℝ) ≤ 4 * (K : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left hE4 hK0
    have h4 : L ^ ((3 : ℝ) / 4) ≤ 16 * (L * L ^ ((1 : ℝ) / 16)) :=
      rpow_three_quarters_le hL
    calc L ^ ((3 : ℝ) / 4) ≤ 16 * (L * L ^ ((1 : ℝ) / 16)) := h4
      _ = 4 * L * (4 * L ^ ((1 : ℝ) / 16)) := by ring
      _ ≤ 4 * (K : ℝ) * (4 * L ^ ((1 : ℝ) / 16)) := h2
      _ ≤ 4 * (K : ℝ) * stepEnv (N := N) p
            (max (2 * L ^ ((1 : ℝ) / 16) + 6) (2 * L ^ ((1 : ℝ) / 16))) := h3
  have hmain := measure_locmax_window_le (N := N) (m := m) (s := s) (K := K)
    (H := L ^ ((1 : ℝ) / 16)) (G := L ^ ((1 : ℝ) / 16)) (ε := L ^ ((3 : ℝ) / 4))
    hp0 hp1 I J hI hJ hid hH1 hK hε hside
  refine le_trans hmain ?_
  have hexp := LocScaleArithmetic.exp_arg_ge (N := N) hp0 hp1' hN hL hT hK hKL
  have hEpos : (0 : ℝ) < stepEnv (N := N) p
      (max (2 * L ^ ((1 : ℝ) / 16) + 6) (2 * L ^ ((1 : ℝ) / 16))) :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < 4 * L ^ ((1 : ℝ) / 16)) hE4
  have hden : 4 * ((K : ℝ) * (2 * stepEnv (N := N) p
        (max (2 * L ^ ((1 : ℝ) / 16) + 6) (2 * L ^ ((1 : ℝ) / 16)))) ^ 2)
      ≤ 4 * ((K : ℝ) * (2 * LocScaleArithmetic.envB p N (LocScaleArithmetic.truncLevel L) + 1) ^ 2) := by
    rw [hEeq]
    have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    have hsq : (2 * LocScaleArithmetic.envB p N (LocScaleArithmetic.truncLevel L)) ^ 2
        ≤ (2 * LocScaleArithmetic.envB p N (LocScaleArithmetic.truncLevel L) + 1) ^ 2 := by
      nlinarith [Real.rpow_nonneg hL0.le ((1 : ℝ) / 16)]
    have hm := mul_le_mul_of_nonneg_left hsq hK0
    linarith
  have hexp' : L ^ ((1 : ℝ) / 4) / (4 * (321 * (N : ℝ)) ^ 2 * T)
      ≤ (L ^ ((3 : ℝ) / 4)) ^ 2 /
        (4 * ((K : ℝ) * (2 * stepEnv (N := N) p
          (max (2 * L ^ ((1 : ℝ) / 16) + 6) (2 * L ^ ((1 : ℝ) / 16)))) ^ 2)) := by
    have hnum : (0 : ℝ) ≤ (L ^ ((3 : ℝ) / 4)) ^ 2 := by positivity
    have hpos1 : (0 : ℝ) < 4 * ((K : ℝ) * (2 * stepEnv (N := N) p
        (max (2 * L ^ ((1 : ℝ) / 16) + 6) (2 * L ^ ((1 : ℝ) / 16)))) ^ 2) := by
      have : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
      have : (0 : ℝ) < 2 * stepEnv (N := N) p
          (max (2 * L ^ ((1 : ℝ) / 16) + 6) (2 * L ^ ((1 : ℝ) / 16))) := by linarith
      positivity
    have hpos2 : (0 : ℝ) < 4 * ((K : ℝ) *
        (2 * LocScaleArithmetic.envB p N (LocScaleArithmetic.truncLevel L) + 1) ^ 2) := by
      have hK1 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
      have hB0 : (0 : ℝ) < 2 * LocScaleArithmetic.envB p N (LocScaleArithmetic.truncLevel L) + 1 := by
        have h := hEpos
        rw [hEeq] at h
        linarith
      positivity
    have hden' : 4 * ((K : ℝ) * (2 * stepEnv (N := N) p
          (max (2 * L ^ ((1 : ℝ) / 16) + 6) (2 * L ^ ((1 : ℝ) / 16)))) ^ 2)
        ≤ 4 * ((K : ℝ) *
          (2 * LocScaleArithmetic.envB p N (LocScaleArithmetic.truncLevel L) + 1) ^ 2) := by
      rw [hEeq]
      exact hden
    calc L ^ ((1 : ℝ) / 4) / (4 * (321 * (N : ℝ)) ^ 2 * T)
        ≤ (L ^ ((3 : ℝ) / 4)) ^ 2 /
            (4 * ((K : ℝ) * (2 * LocScaleArithmetic.envB p N
              (LocScaleArithmetic.truncLevel L) + 1) ^ 2)) := by
          simpa only [mul_assoc] using hexp
      _ ≤ (L ^ ((3 : ℝ) / 4)) ^ 2 /
            (4 * ((K : ℝ) * (2 * stepEnv (N := N) p
              (max (2 * L ^ ((1 : ℝ) / 16) + 6) (2 * L ^ ((1 : ℝ) / 16)))) ^ 2)) := by
          exact div_le_div_of_nonneg_left hnum hpos1 hden'
  have hmul : (0 : ℝ) ≤ 2 * ((K : ℝ) + 1) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hmul
  rw [Real.exp_le_exp, neg_div]
  exact neg_le_neg hexp'

/-! ## 10. The truncated and untruncated compensators agree on `GoodW` -/

/-- On the predictable good event the truncated increment *is* the paper's raw `(sep)`-increment,
so the two compensators `E[incT | F_k]` and `E[Qraw | F_k]` agree there.  Consequently the
truncated martingale difference `dQT` and the paper's `dQ` of `WdriftJoint` coincide on `GoodW`.
This is the transfer that lets any bound for the drift half of `(locmove)` — e.g.
`Swarming.GammaStrict.ae_window_gamma_drift_le`, whose defect is `Q_t - Q_s` — be combined with
the maximal estimate for the truncated process: on a window on which `GoodW` holds at every time
the *untruncated* defect `Q_t - Q_s` is exactly the truncated sum bounded there. -/
theorem ae_dQT_eq_dQ_of_goodW {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m k : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    (B : ℝ) :
    ∀ᵐ U ∂(arrayMeasure N), GoodW p m k I J hI B U →
      dQT p m I J hI hJ B k U = dQ p m I J hI hJ k U := by
  haveI hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hp : (1 : ℝ) / 2 ≤ p := le_of_lt hp0
  have hp1' : p ≤ 1 := le_of_lt hp1
  set G : Set (Array N) := {U : Array N | GoodW p m k I J hI B U} with hGdef
  have hGm : MeasurableSet[posFilt N p m k] G := measurableSet_goodW_posFilt p m k I J hI B
  have hQint : Integrable (Qraw p m I J hI hJ k) (arrayMeasure N) :=
    integrable_Qraw hp hp1' m k I J hI hJ
  have hTint : Integrable (incT p m I J hI hJ B k) (arrayMeasure N) :=
    integrable_incT (N := N) hp hp1' m k I J hI hJ B
  have hindQ : Integrable (G.indicator (Qraw p m I J hI hJ k)) (arrayMeasure N) :=
    hQint.indicator (((posFilt N p m).le k) _ hGm)
  have hindT : Integrable (G.indicator (incT p m I J hI hJ B k)) (arrayMeasure N) :=
    hTint.indicator (((posFilt N p m).le k) _ hGm)
  have hmulQ : (G.indicator (fun _ : Array N => (1 : ℝ))) * Qraw p m I J hI hJ k
      = G.indicator (Qraw p m I J hI hJ k) := by
    funext U
    by_cases hU : U ∈ G <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hU]
  have hmulT : (G.indicator (fun _ : Array N => (1 : ℝ))) * incT p m I J hI hJ B k
      = G.indicator (incT p m I J hI hJ B k) := by
    funext U
    by_cases hU : U ∈ G <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hU]
  have hfmeas : StronglyMeasurable[posFilt N p m k]
      (G.indicator (fun _ : Array N => (1 : ℝ))) :=
    stronglyMeasurable_const.indicator hGm
  have hpullQ := condExp_mul_of_stronglyMeasurable_left (μ := arrayMeasure N)
    (m := posFilt N p m k) (f := G.indicator (fun _ : Array N => (1 : ℝ)))
    (g := Qraw p m I J hI hJ k) hfmeas (by rw [hmulQ]; exact hindQ) hQint
  have hpullT := condExp_mul_of_stronglyMeasurable_left (μ := arrayMeasure N)
    (m := posFilt N p m k) (f := G.indicator (fun _ : Array N => (1 : ℝ)))
    (g := incT p m I J hI hJ B k) hfmeas (by rw [hmulT]; exact hindT) hTint
  have hprod : (G.indicator (fun _ : Array N => (1 : ℝ))) * incT p m I J hI hJ B k
      =ᵐ[arrayMeasure N]
        (G.indicator (fun _ : Array N => (1 : ℝ))) * Qraw p m I J hI hJ k := by
    filter_upwards with U
    by_cases hU : U ∈ G
    · have hinc : incT p m I J hI hJ B k U = Qraw p m I J hI hJ k U := by
        rw [incT_of_mem (hJ := hJ) (U := U)
          (show U ∈ {U : Array N | GoodW p m k I J hI B U} from hU), Qraw,
          Set.indicator_of_mem (show U ∈ {U : Array N | SepSet p m k I J U} from hU.1)]
      simp only [Pi.mul_apply, Set.indicator_of_mem hU, one_mul, hinc]
    · simp only [Pi.mul_apply, Set.indicator_of_notMem hU, zero_mul]
  have hce : (arrayMeasure N)[(G.indicator (fun _ : Array N => (1 : ℝ))) * incT p m I J hI hJ B k
        | ↑(posFilt N p m k)]
      =ᵐ[arrayMeasure N]
        (arrayMeasure N)[(G.indicator (fun _ : Array N => (1 : ℝ))) * Qraw p m I J hI hJ k
          | ↑(posFilt N p m k)] :=
    condExp_congr_ae (μ := arrayMeasure N) (m := posFilt N p m k) hprod
  have hcomb : ∀ᵐ U ∂(arrayMeasure N), U ∈ G →
      (arrayMeasure N)[incT p m I J hI hJ B k | ↑(posFilt N p m k)] U
        = (arrayMeasure N)[Qraw p m I J hI hJ k | ↑(posFilt N p m k)] U := by
    filter_upwards [hpullT, hpullQ, hce] with U h1 h2 h3 hGU
    have hf1 : (G.indicator (fun _ : Array N => (1 : ℝ))) U = 1 := by
      simp only [Set.indicator_of_mem hGU]
    calc (arrayMeasure N)[incT p m I J hI hJ B k | ↑(posFilt N p m k)] U
        = ((G.indicator (fun _ : Array N => (1 : ℝ))) *
            (arrayMeasure N)[incT p m I J hI hJ B k | ↑(posFilt N p m k)]) U := by
          simp only [Pi.mul_apply, hf1, one_mul]
      _ = (arrayMeasure N)[(G.indicator (fun _ : Array N => (1 : ℝ))) * incT p m I J hI hJ B k
            | ↑(posFilt N p m k)] U := h1.symm
      _ = (arrayMeasure N)[(G.indicator (fun _ : Array N => (1 : ℝ))) * Qraw p m I J hI hJ k
            | ↑(posFilt N p m k)] U := h3
      _ = ((G.indicator (fun _ : Array N => (1 : ℝ))) *
            (arrayMeasure N)[Qraw p m I J hI hJ k | ↑(posFilt N p m k)]) U := h2
      _ = (arrayMeasure N)[Qraw p m I J hI hJ k | ↑(posFilt N p m k)] U := by
          simp only [Pi.mul_apply, hf1, one_mul]
  filter_upwards [hcomb] with U hU hGU
  have hinc : incT p m I J hI hJ B k U = Qraw p m I J hI hJ k U := by
    rw [incT_of_mem (hJ := hJ) (U := U)
      (show U ∈ {U : Array N | GoodW p m k I J hI B U} from hGU), Qraw,
      Set.indicator_of_mem (show U ∈ {U : Array N | SepSet p m k I J U} from hGU.1)]
  have hcoeq := hU hGU
  simp only [dQT, dQ, hinc, hcoeq]

/-- **On a `GoodW` window the truncated sum is the paper's defect `Q_t - Q_s`.**  Almost surely,
for all `s ≤ t` and every window on which `GoodW` holds at every time,
`Σ_{j<t-s} dQT_{s+j} = Q_t^{I,J} - Q_s^{I,J}`. -/
theorem ae_psum_dQT_eq_Q_sub {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    (B : ℝ) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ s t : ℕ, s ≤ t →
      (∀ k, s ≤ k → k < t → GoodW p m k I J hI B U) →
      LocMart.psum (fun j => dQT p m I J hI hJ B (s + j)) (t - s) U
        = Q p m I J hI hJ t U - Q p m I J hI hJ s U := by
  have hall : ∀ᵐ U ∂(arrayMeasure N), ∀ k : ℕ,
      (GoodW p m k I J hI B U →
        dQT p m I J hI hJ B k U = dQ p m I J hI hJ k U) :=
    ae_all_iff.mpr (fun k => ae_dQT_eq_dQ_of_goodW hp0 hp1 m k I J hI hJ hid B)
  filter_upwards [hall] with U hU s t hst hwin
  have hcongr : LocMart.psum (fun j => dQT p m I J hI hJ B (s + j)) (t - s) U
      = LocMart.psum (fun j => dQ p m I J hI hJ (s + j)) (t - s) U := by
    simp only [LocMart.psum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj' : j < t - s := Finset.mem_range.mp hj
    have hjt : s + j < t := by omega
    exact hU (s + j) (hwin (s + j) (Nat.le_add_right s j) hjt)
  rw [hcongr]
  have hQ : Q p m I J hI hJ t U - Q p m I J hI hJ s U
      = ∑ j ∈ Finset.range (t - s), dQ p m I J hI hJ (s + j) U := by
    have hts : s + (t - s) = t := Nat.add_sub_cancel' hst
    have hsplit := Finset.sum_range_add (fun k => dQ p m I J hI hJ k U) s (t - s)
    simp only [Q, hts] at hsplit ⊢
    linarith
  rw [hQ]
  simp only [LocMart.psum]

end LocGroupWindow
