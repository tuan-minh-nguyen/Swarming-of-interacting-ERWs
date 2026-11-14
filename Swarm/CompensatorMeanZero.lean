/-
  **DIRECTION B (m2) — `CompensatorMeanZero.lean`: the mean-zero layer of the `Q` ledger.**

  What this file settles, and what it does not.

  `OccInterface.occupation_bound_one_eighth` carries three eventual pathwise premises `hZ`, `hJ`,
  `hQ`.  `hQ` is the *lower-tail* statement `-(δ T) <= Qcomp T`; it is **not** an integral or a
  mean statement and it is not proved by anything here.  Direction B asks a strictly different
  question: is `Qcomp` actually a *centred* object, i.e. does the compensator of
  `VdriftTimeAssembly.Qcomp` have zero `enlFilt`-conditional mean, and hence zero mean?  The
  paper's `Edrift` centres the ledger by definition (`Qcomp` is defined as the partial sum of
  `Zpot(t+1) - Zpot t + Jcorr t - Edrift t`), so the honest answer has to be *computed*, not
  asserted.  This file computes it:

  * `Zpot_zero`: `Zpot ... 0 = 0` — the potential starts at zero, so the `max 0 (-Z_0)` term and
    the `omega`-dependent onset `ceil(32 max 0 (-Z_0))` of `SwarmOcc.occbnd_one_eighth` are
    *vacuous* at the actual model.  `occupation_bound_one_eighth_onset` records the resulting
    interface with the onset `N0` only.
  * `integrable_ZJinc`: the increment `Zpot(t+1) - Zpot t + Jcorr t` **is** integrable.  This is
    not automatic from `Zpot` itself (the `Hpot(envH)(X_t)` term is a walker-position-indexed
    projection whose own integrability is not available); it follows from the exact algebra
    `Zpot_add_J`, which identifies the increment with `HpotInc - Cinc`, both of which are already
    integrable.
  * `measurable_corrDrift_enl`, `integrable_Edrift`: the drift `Edrift` is `enlFilt t`-measurable
    and integrable, which is what makes `Edrift` a legitimate compensator rather than a formal
    symbol.
  * `condExp_Qcomp_increment_eq_zero`: `condExp (enlFilt t) (Qcomp (t+1) - Qcomp t) =ᵐ 0`.
    This is the genuine "no fake martingale" statement at the level of conditional
    expectations: every increment of `Qcomp` is centred given the *history up to `t`*, using only
    `CorrectionDrift.compensator_unconditional` and the measurability of `corrDrift`.
  * `condExp_Qcomp_increment_eq_zero_of_le`: for *every* `s <= t` the `t`-th increment is centred
    given `enlFilt s` (not only given `enlFilt t`), and `condExp_Qcomp_block_eq_zero`: every
    future block difference `Qcomp b - Qcomp a` (`s <= a <= b`) is centred given `enlFilt s`.
  * `integral_Qcomp_eq_zero` / `setIntegral_Qcomp_block_eq_zero`: `∫ Qcomp T = 0`, and
    `∫_A (Qcomp b - Qcomp a) = 0` for every `A ∈ enlFilt s`, `s <= a <= b`.

  A statement deliberately **not** claimed: `condExp (enlFilt T) (Qcomp T) =ᵐ 0`.  It is false in
  general, and its failure is exactly the adaptedness gap: `Qcomp T` is (at least formally) an
  `enlFilt T`-observable quantity, so conditioning on its own history cannot centre it.  What
  centres a martingale-difference sum is `condExp (enlFilt t)` applied to the `t`-th increment;
  for that to be usable as a martingale one additionally needs the increment to be
  `enlFilt (t+1)`-measurable, i.e. adaptedness of `Zpot`, which is *not* proved here.

  * Integrability of the ledger's own terms: `integrable_Zpot` (`Z_T` **is** integrable at every
    fixed time, although `Hpot(envH)(X_T)` alone is a position-indexed environment projection),
    `integrable_Jcorr`, `integrable_Jsum`, `integrable_occSum`.
  * `integral_occSum_le`: the **mean-level** occupation ledger

        ∫ occSum_T <= eps T + ∫ Z_T + ∫ sum_{t<T} J_{t+1},

    i.e. the exact mean-level content of `(Vdrift)` after the compensator is discharged by
    `integral_Qcomp_eq_zero`.

  * Section 7: `corrDrift`/`Edrift` are `enlFilt t`- measurable, and — under the *single named
    hypothesis* `hadapt : ∀ t, StronglyMeasurable[enlFilt p m (t+1)] (ZJinc · t)` — the process
    `T ↦ Qcomp T` is a genuine `Martingale` (`martingale_Qcomp`) for the enlarged filtration.
    `hadapt` is the future measurability of the `Hpot(envH)(X_{t+1})` part; it is *not* asserted
    anywhere in this file, only carried as an explicit hypothesis.

  What is **not** proved here: `hQ`.  Zero mean does not give any pathwise lower tail; the passage
  from `∫ Q = 0` to `-(δ T) <= Q T` a.e. is a strong-law statement and stays an explicit
  hypothesis of `OccInterface`.  No martingale claim is made either: `Qcomp` *is* a sum of
  increments with zero past-conditional mean, but a martingale also needs the increments to be
  `enlFilt (t+1)`-measurable, and the future measurability of the `Hpot(envH)(position)` part at
  time `t+1` is not asserted here.
-/
import Swarm.OccInterface

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl
namespace VdriftAssembly

open Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross

variable {N : ℕ}

/-! ## 1. The potential starts at zero -/

/-- `M_0^j = 0`: the running record at time `0` is the time-`0` position. -/
theorem runMax_zero (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) : runMax p m U j 0 = 0 := by
  simp [runMax, trajectory_zero]

/-- **`Z_0 = 0`.**  `Hpot` vanishes at `0` and `Fcorr` vanishes at gap `0` (empty sum), so the
initial potential is exactly zero for every array. -/
theorem Zpot_zero (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) :
    Zpot p m eps i j U 0 = 0 := by
  simp [Zpot, SwarmOcc.Hpot, SwarmOcc.Fcorr, trajectory_zero, runMax_zero p m U j]

/-- **The `max 0 (-Z_0)` constant is zero at the actual model.** -/
theorem max_neg_Zpot_zero (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) :
    max 0 (-(Zpot p m eps i j U 0)) = 0 := by
  rw [Zpot_zero p m eps i j U]
  norm_num

/-- **`(occbnd)` with the onset `N0` only.**  The `omega`-dependent onset
`ceil(32 max 0 (-Z_0))` and the additive constant `max 0 (-Z_0)` of
`OccupInterface.occupation_bound_one_eighth` are vacuous: `Z_0 = 0` identically.  The three
eventual budgets `hZ`, `hJ`, `hQ` remain the only stochastic hypotheses. -/
theorem occupation_bound_one_eighth_onset {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {i j : Fin N}
    (hAB : ∀ n, Budget.paperWeight p m n i j
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j))
    {M : Array N → ℕ → ℝ} {N₀ : ℕ}
    (hZ : ∀ᵐ U ∂(arrayMeasure N), ∀ T ≥ N₀,
      Zpot p m (1 / 32) i j U T ≤ M U T + (1 / 64) * (T : ℝ))
    (hJ : ∀ᵐ U ∂(arrayMeasure N), ∀ T ≥ N₀,
      Jsum p m (1 / 32) i j U T ≤ M U T + (1 / 64) * (T : ℝ))
    (hQ : ∀ᵐ U ∂(arrayMeasure N), ∀ T ≥ N₀,
      -((1 / 64) * (T : ℝ)) ≤ Qcomp p m (1 / 32) (fun t => alphaFun p m t i) i j U T) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ T ≥ N₀,
      occSum p m i j U T ≤ 2 * M U T + (1 / 8) * (T : ℝ) := by
  filter_upwards [occupation_bound_one_eighth hp0 hp1 hAB hZ hJ hQ] with U hU
  intro T hT
  refine hU T ?_
  have h0 : max 0 (-(Zpot p m (1 / 32) i j U 0)) = 0 := max_neg_Zpot_zero p m (1 / 32) i j U
  rw [h0]
  have hz : ⌈(32 : ℝ) * 0⌉₊ = 0 := by norm_num
  rw [hz, max_zero]
  exact hT

/-- **`(occbnd)` at general `eps, δ` with the `omega`-dependent constant removed.**  The
additive `max 0 (-Z_0)` of `VdriftTimeAssembly.occupation_bound_actual` is zero. -/
theorem occupation_bound_actual_onset {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {i j : Fin N} {eps δ : ℝ} (hε : 0 < eps)
    (hAB : ∀ n, Budget.paperWeight p m n i j
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j))
    {M : Array N → ℕ → ℝ} {N₀ : ℕ}
    (hZ : ∀ᵐ U ∂(arrayMeasure N), ∀ T ≥ N₀, Zpot p m eps i j U T ≤ M U T + δ * (T : ℝ))
    (hJ : ∀ᵐ U ∂(arrayMeasure N), ∀ T ≥ N₀, Jsum p m eps i j U T ≤ M U T + δ * (T : ℝ))
    (hQ : ∀ᵐ U ∂(arrayMeasure N), ∀ T ≥ N₀,
      -(δ * (T : ℝ)) ≤ Qcomp p m eps (fun t => alphaFun p m t i) i j U T) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ T ≥ N₀,
      occSum p m i j U T ≤ 2 * M U T + (eps + 3 * δ) * (T : ℝ) := by
  filter_upwards [occupation_bound_actual hp0 hp1 hε hAB hZ hJ hQ] with U hU
  intro T hT
  have h0 : max 0 (-(Zpot p m eps i j U 0)) = 0 := max_neg_Zpot_zero p m eps i j U
  have h := hU T hT
  rw [h0, add_zero] at h
  exact h

/-! ## 2. Integrability of the ledger increment and of the two centred pieces -/

/-- **The `Z`-plus-`J` increment is integrable.**  `Zpot` itself need not be integrable (the
`Hpot(envH)(X_t)` term is a position-indexed projection), but the exact algebra `Zpot_add_J`
identifies the increment with `HpotInc - Cinc`, and both of those are integrable. -/
theorem integrable_ZJinc {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m t : ℕ) (i j : Fin N)
    {eps : ℝ} (hε : 0 < eps) :
    Integrable (fun U : Array N =>
      Zpot p m eps i j U (t + 1) - Zpot p m eps i j U t + Jcorr p m eps i j U t)
      (arrayMeasure N) := by
  have hpne : p ≠ 0 := by linarith
  have h : Integrable (fun U : Array N => HpotInc p m t i j U - Cinc p m eps i j U t)
      (arrayMeasure N) :=
    (Budget.integrable_HpotInc hp0 hp1 hpne m t i j).sub (integrable_Cinc hp0 hp1 m t i j hε)
  exact h.congr (Filter.Eventually.of_forall fun U => (Zpot_add_J p m eps i j U t).symm)

/-- The centred `Hpot` increment `HpotInc_t - E[HpotInc_t | enlFilt t]` is integrable. -/
theorem integrable_centred_HpotInc {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m t : ℕ) (i j : Fin N) :
    Integrable (fun U : Array N => HpotInc p m t i j U
      - condExp (enlFilt p m t) (arrayMeasure N) (HpotInc p m t i j) U) (arrayMeasure N) := by
  have hpne : p ≠ 0 := by linarith
  exact (Budget.integrable_HpotInc hp0 hp1 hpne m t i j).sub integrable_condExp

/-- The centred correction increment `Cinc_t - E[Cinc_t | enlFilt t]` is integrable. -/
theorem integrable_centred_Cinc {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m t : ℕ) (i j : Fin N) {eps : ℝ} (hε : 0 < eps) :
    Integrable (fun U : Array N => Cinc p m eps i j U t
      - condExp (enlFilt p m t) (arrayMeasure N) (fun U => Cinc p m eps i j U t) U)
      (arrayMeasure N) :=
  (integrable_Cinc hp0 hp1 m t i j hε).sub integrable_condExp

/-- **The centred `Hpot` increment has zero `enlFilt t`-conditional mean.** -/
theorem condExp_centred_HpotInc_eq_zero {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m t : ℕ) (i j : Fin N) :
    condExp (enlFilt p m t) (arrayMeasure N)
        (fun U : Array N => HpotInc p m t i j U
          - condExp (enlFilt p m t) (arrayMeasure N) (HpotInc p m t i j) U)
      =ᵐ[arrayMeasure N] 0 := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hpne : p ≠ 0 := by linarith
  have hIntH : Integrable (HpotInc p m t i j) (arrayMeasure N) :=
    Budget.integrable_HpotInc hp0 hp1 hpne m t i j
  have hIntC : Integrable (condExp (enlFilt p m t) (arrayMeasure N) (HpotInc p m t i j))
      (arrayMeasure N) := integrable_condExp
  have hsub : condExp (enlFilt p m t) (arrayMeasure N)
      (fun U : Array N => HpotInc p m t i j U
        - condExp (enlFilt p m t) (arrayMeasure N) (HpotInc p m t i j) U)
      =ᵐ[arrayMeasure N] condExp (enlFilt p m t) (arrayMeasure N) (HpotInc p m t i j)
        - condExp (enlFilt p m t) (arrayMeasure N)
            (condExp (enlFilt p m t) (arrayMeasure N) (HpotInc p m t i j)) :=
    condExp_sub (f := HpotInc p m t i j)
      (g := condExp (enlFilt p m t) (arrayMeasure N) (HpotInc p m t i j)) hIntH hIntC
      (enlFilt p m t)
  have hfix : condExp (enlFilt p m t) (arrayMeasure N)
      (condExp (enlFilt p m t) (arrayMeasure N) (HpotInc p m t i j))
      = condExp (enlFilt p m t) (arrayMeasure N) (HpotInc p m t i j) :=
    condExp_of_stronglyMeasurable ((enlFilt p m).le t) stronglyMeasurable_condExp hIntC
  refine hsub.trans ?_
  refine (Filter.EventuallyEq.sub Filter.EventuallyEq.rfl
    (Filter.EventuallyEq.of_eq hfix)).trans ?_
  filter_upwards with U
  simp

/-- **The centred correction increment has zero `enlFilt t`-conditional mean.**  Uses only the
exact correction identity `CorrectionDrift.condExp_Cinc`; no bound on `Fcorr` and no integrability
of `corrDrift` is needed. -/
theorem condExp_centred_Cinc_eq_zero {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m t : ℕ) (i j : Fin N) {eps : ℝ} (hε : 0 < eps) :
    condExp (enlFilt p m t) (arrayMeasure N)
        (fun U : Array N => Cinc p m eps i j U t
          - condExp (enlFilt p m t) (arrayMeasure N) (fun U => Cinc p m eps i j U t) U)
      =ᵐ[arrayMeasure N] 0 := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hIntC : Integrable (fun U : Array N => Cinc p m eps i j U t) (arrayMeasure N) :=
    integrable_Cinc hp0 hp1 m t i j hε
  have hIntCC : Integrable
      (condExp (enlFilt p m t) (arrayMeasure N) (fun U => Cinc p m eps i j U t))
      (arrayMeasure N) := integrable_condExp
  have hsub : condExp (enlFilt p m t) (arrayMeasure N)
      (fun U : Array N => Cinc p m eps i j U t
        - condExp (enlFilt p m t) (arrayMeasure N) (fun U => Cinc p m eps i j U t) U)
      =ᵐ[arrayMeasure N] condExp (enlFilt p m t) (arrayMeasure N) (fun U => Cinc p m eps i j U t)
        - condExp (enlFilt p m t) (arrayMeasure N)
            (condExp (enlFilt p m t) (arrayMeasure N) (fun U => Cinc p m eps i j U t)) :=
    condExp_sub (f := fun U : Array N => Cinc p m eps i j U t)
      (g := condExp (enlFilt p m t) (arrayMeasure N) (fun U => Cinc p m eps i j U t))
      hIntC hIntCC (enlFilt p m t)
  have hfix : condExp (enlFilt p m t) (arrayMeasure N)
      (condExp (enlFilt p m t) (arrayMeasure N) (fun U => Cinc p m eps i j U t))
      = condExp (enlFilt p m t) (arrayMeasure N)
        (fun U => Cinc p m eps i j U t) :=
    condExp_of_stronglyMeasurable ((enlFilt p m).le t) stronglyMeasurable_condExp hIntCC
  have hcorr : condExp (enlFilt p m t) (arrayMeasure N) (fun U => Cinc p m eps i j U t)
      =ᵐ[arrayMeasure N] fun U => corrDrift (aRec p m) eps (alphaFun p m t i U)
        (bRec p m t j U) ((trajectory p m U t).pos i - runMax p m U j t) :=
    condExp_Cinc hp0 hp1 m t i j hε
  refine hsub.trans ?_
  refine (hcorr.sub ((Filter.EventuallyEq.of_eq hfix).trans hcorr)).trans ?_
  filter_upwards with U
  simp

/-! ## 3. The increment of `Qcomp` is a difference of two centred increments -/

/-- **One-step difference of the compensator**: `Qcomp (t+1) - Qcomp t` is the `t`-th increment
`Z_{t+1} - Z_t + J_{t+1} - E_t` of `Qcomp_eq_sum_increments`. -/
theorem Qcomp_succ_sub (p : ℝ) (m : ℕ) (eps : ℝ) (α : ℕ → Array N → ℝ) (i j : Fin N)
    (U : Array N) (t : ℕ) :
    Qcomp p m eps α i j U (t + 1) - Qcomp p m eps α i j U t
      = Zpot p m eps i j U (t + 1) - Zpot p m eps i j U t + Jcorr p m eps i j U t
        - Edrift p m eps α i j U t := by
  rw [Qcomp_eq_sum_increments p m eps α i j U (t + 1),
    Qcomp_eq_sum_increments p m eps α i j U t, Finset.sum_range_succ]
  ring

/-- **The increment of `Qcomp` is the difference of the two centred increments**, with
`α = alphaFun p m · i` and `E_t` written out.  This is where `Zpot_add_J` and the exact
correction identity enter. -/
theorem Qcomp_increment_eq_centred {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m t : ℕ} {i j : Fin N} {eps : ℝ} (hε : 0 < eps) :
    (fun U : Array N => Qcomp p m eps (fun s => alphaFun p m s i) i j U (t + 1)
        - Qcomp p m eps (fun s => alphaFun p m s i) i j U t)
      =ᵐ[arrayMeasure N]
      (fun U : Array N => (HpotInc p m t i j U
          - condExp (enlFilt p m t) (arrayMeasure N) (HpotInc p m t i j) U)
        - (Cinc p m eps i j U t
          - condExp (enlFilt p m t) (arrayMeasure N) (fun U => Cinc p m eps i j U t) U)) := by
  have hcorr := condExp_Cinc (N := N) hp0 hp1 m t i j hε
  filter_upwards [hcorr] with U hU
  rw [Qcomp_succ_sub p m eps (fun s => alphaFun p m s i) i j U t]
  simp only [Edrift]
  rw [hU, Zpot_add_J]
  ring

/-- **The increment of `Qcomp` is integrable.** -/
theorem integrable_Qcomp_increment {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m t : ℕ} {i j : Fin N} {eps : ℝ} (hε : 0 < eps) :
    Integrable (fun U : Array N => Qcomp p m eps (fun s => alphaFun p m s i) i j U (t + 1)
      - Qcomp p m eps (fun s => alphaFun p m s i) i j U t) (arrayMeasure N) :=
  ((integrable_centred_HpotInc hp0 hp1 m t i j).sub
    (integrable_centred_Cinc hp0 hp1 m t i j hε)).congr
    (Qcomp_increment_eq_centred (N := N) hp0 hp1 (m := m) (t := t) (i := i) (j := j) hε).symm

/-! ## 4. Zero conditional mean and zero mean of `Qcomp` -/

/-- **The compensator has zero conditional-mean increments.**

`condExp (enlFilt t) (Qcomp (t+1) - Qcomp t) =ᵐ 0` on the actual array measure, for every `t`,
with no hypothesis beyond `1/2 < p < 1` and `0 < eps`.  This is the honest centring statement:
`Qcomp` is *defined* with `Edrift` subtracted, and `Edrift` is the exact `enlFilt t`-conditional
mean of the `Z`-plus-`J` increment (`compensator_unconditional`), so the difference is centred.
No pathwise bound on `Qcomp` follows from this. -/
theorem condExp_Qcomp_increment_eq_zero {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m t : ℕ} {i j : Fin N} {eps : ℝ} (hε : 0 < eps) :
    condExp (enlFilt p m t) (arrayMeasure N)
        (fun U : Array N => Qcomp p m eps (fun s => alphaFun p m s i) i j U (t + 1)
          - Qcomp p m eps (fun s => alphaFun p m s i) i j U t)
      =ᵐ[arrayMeasure N] 0 := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  refine (condExp_congr_ae (μ := arrayMeasure N) (m := enlFilt p m t)
    (f := fun U : Array N => Qcomp p m eps (fun s => alphaFun p m s i) i j U (t + 1)
      - Qcomp p m eps (fun s => alphaFun p m s i) i j U t)
    (g := fun U : Array N => (HpotInc p m t i j U
        - condExp (enlFilt p m t) (arrayMeasure N) (HpotInc p m t i j) U)
      - (Cinc p m eps i j U t
        - condExp (enlFilt p m t) (arrayMeasure N) (fun U => Cinc p m eps i j U t) U))
    (Qcomp_increment_eq_centred hp0 hp1 hε)).trans ?_
  refine (condExp_sub (integrable_centred_HpotInc hp0 hp1 m t i j)
    (integrable_centred_Cinc hp0 hp1 m t i j hε) (enlFilt p m t)).trans ?_
  refine ((condExp_centred_HpotInc_eq_zero hp0 hp1 m t i j).sub
    (condExp_centred_Cinc_eq_zero hp0 hp1 m t i j hε)).trans ?_
  filter_upwards with U
  simp

/-- **Each increment of `Qcomp` has zero mean.** -/
theorem integral_Qcomp_increment_eq_zero {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m t : ℕ} {i j : Fin N} {eps : ℝ} (hε : 0 < eps) :
    ∫ U : Array N, (Qcomp p m eps (fun s => alphaFun p m s i) i j U (t + 1)
      - Qcomp p m eps (fun s => alphaFun p m s i) i j U t) ∂(arrayMeasure N) = 0 := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hcent := Qcomp_increment_eq_centred (N := N) hp0 hp1 (m := m) (t := t) (i := i) (j := j) hε
  have hInt : Integrable (fun U : Array N => (HpotInc p m t i j U
        - condExp (enlFilt p m t) (arrayMeasure N) (HpotInc p m t i j) U)
      - (Cinc p m eps i j U t
        - condExp (enlFilt p m t) (arrayMeasure N) (fun U => Cinc p m eps i j U t) U))
      (arrayMeasure N) :=
    (integrable_centred_HpotInc hp0 hp1 m t i j).sub
      (integrable_centred_Cinc hp0 hp1 m t i j hε)
  rw [integral_congr_ae hcent]
  rw [integral_sub (integrable_centred_HpotInc hp0 hp1 m t i j)
    (integrable_centred_Cinc hp0 hp1 m t i j hε)]
  have hH : ∫ U : Array N, (HpotInc p m t i j U
      - condExp (enlFilt p m t) (arrayMeasure N) (HpotInc p m t i j) U) ∂(arrayMeasure N) = 0 := by
    have hpne : p ≠ 0 := by linarith
    rw [integral_sub (Budget.integrable_HpotInc hp0 hp1 hpne m t i j) integrable_condExp,
      integral_condExp ((enlFilt p m).le t)]
    ring
  have hC : ∫ U : Array N, (Cinc p m eps i j U t
      - condExp (enlFilt p m t) (arrayMeasure N) (fun U => Cinc p m eps i j U t) U)
        ∂(arrayMeasure N) = 0 := by
    rw [integral_sub (integrable_Cinc hp0 hp1 m t i j hε) integrable_condExp,
      integral_condExp ((enlFilt p m).le t)]
    ring
  rw [hH, hC]
  ring

/-- `Qcomp` starts at zero. -/
theorem Qcomp_zero (p : ℝ) (m : ℕ) (eps : ℝ) (α : ℕ → Array N → ℝ) (i j : Fin N)
    (U : Array N) : Qcomp p m eps α i j U 0 = 0 := by
  simp [Qcomp]

/-- **Every value of `Qcomp` is integrable**: it is the finite sum of its increments. -/
theorem integrable_Qcomp {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {i j : Fin N} {eps : ℝ} (hε : 0 < eps) (T : ℕ) :
    Integrable (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U T)
      (arrayMeasure N) := by
  have hfun : (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U T)
      = fun U => ∑ t ∈ Finset.range T,
          (Qcomp p m eps (fun r => alphaFun p m r i) i j U (t + 1)
            - Qcomp p m eps (fun r => alphaFun p m r i) i j U t) := by
    funext U
    rw [Qcomp_eq_sum_increments p m eps (fun r => alphaFun p m r i) i j U T]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    exact (Qcomp_succ_sub p m eps (fun r => alphaFun p m r i) i j U t).symm
  rw [hfun]
  exact integrable_finsetSum _ (fun t _ => integrable_Qcomp_increment hp0 hp1 hε)

/-- **The compensator `Qcomp` has zero mean at every time.**  `Q_T` is a finite sum of increments
of zero conditional mean; the mean of the sum is the sum of the means. -/
theorem integral_Qcomp_eq_zero {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {i j : Fin N} {eps : ℝ} (hε : 0 < eps) (T : ℕ) :
    ∫ U : Array N, Qcomp p m eps (fun s => alphaFun p m s i) i j U T ∂(arrayMeasure N) = 0 := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hfun : (fun U : Array N => Qcomp p m eps (fun s => alphaFun p m s i) i j U T)
      = fun U => ∑ t ∈ Finset.range T,
          (Qcomp p m eps (fun s => alphaFun p m s i) i j U (t + 1)
            - Qcomp p m eps (fun s => alphaFun p m s i) i j U t) := by
    funext U
    rw [Qcomp_eq_sum_increments p m eps (fun s => alphaFun p m s i) i j U T]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    exact (Qcomp_succ_sub p m eps (fun s => alphaFun p m s i) i j U t).symm
  rw [hfun, integral_finsetSum]
  · refine Finset.sum_eq_zero (fun t _ => ?_)
    exact integral_Qcomp_increment_eq_zero hp0 hp1 (m := m) (t := t) (i := i) (j := j) hε
  · intro t _
    exact integrable_Qcomp_increment hp0 hp1 (m := m) (t := t) (i := i) (j := j) hε


/-! ## 5. Centring against any *past* `enlFilt`, and block sums -/

/-- **The `t`-th increment is centred given any earlier `enlFilt s`, `s <= t`.**

This is the tower property in the direction that is actually true: the increment has zero
`enlFilt t`-conditional mean, and `enlFilt s <= enlFilt t` for `s <= t`, so its `enlFilt s`
conditional mean is the `enlFilt s`-conditional mean of `0`.  (The opposite statement,
conditioning on a *later* `enlFilt`, is false in general and is not claimed.) -/
theorem condExp_Qcomp_increment_eq_zero_of_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m t s : ℕ} (hst : s ≤ t) {i j : Fin N} {eps : ℝ} (hε : 0 < eps) :
    condExp (enlFilt p m s) (arrayMeasure N)
        (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U (t + 1)
          - Qcomp p m eps (fun r => alphaFun p m r i) i j U t)
      =ᵐ[arrayMeasure N] 0 := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hle : (enlFilt (N := N) p m s : MeasurableSpace (Array N))
      ≤ enlFilt (N := N) p m t :=
    Filtration.mono (enlFilt (N := N) p m) hst
  have htower := condExp_condExp_of_le (μ := arrayMeasure N)
    (m₁ := enlFilt p m s) (m₂ := enlFilt p m t) (m₀ := (inferInstance : MeasurableSpace (Array N)))
    (f := fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U (t + 1)
      - Qcomp p m eps (fun r => alphaFun p m r i) i j U t) hle ((enlFilt p m).le t)
  refine htower.symm.trans ?_
  refine (condExp_congr_ae (μ := arrayMeasure N) (m := enlFilt p m s)
    (f := condExp (enlFilt p m t) (arrayMeasure N)
      (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U (t + 1)
        - Qcomp p m eps (fun r => alphaFun p m r i) i j U t))
    (g := 0) (condExp_Qcomp_increment_eq_zero hp0 hp1 (m := m) (t := t) (i := i) (j := j) hε)).trans ?_
  simp

/-- **Every block difference of the compensator is centred given any earlier `enlFilt s`**:
for `s <= a <= b`, `condExp (enlFilt s) (Qcomp b - Qcomp a) =ᵐ 0`.  Equivalently, for every
`enlFilt s`-measurable set `A` the block contributes nothing to `∫_A`. -/
theorem condExp_Qcomp_block_eq_zero {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m s : ℕ} {i j : Fin N} {eps : ℝ} (hε : 0 < eps) :
    ∀ a b : ℕ, s ≤ a → a ≤ b →
      condExp (enlFilt p m s) (arrayMeasure N)
        (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U b
          - Qcomp p m eps (fun r => alphaFun p m r i) i j U a)
      =ᵐ[arrayMeasure N] 0 := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hzero : ∀ c : ℕ, condExp (enlFilt p m s) (arrayMeasure N)
      (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U c
        - Qcomp p m eps (fun r => alphaFun p m r i) i j U c)
      =ᵐ[arrayMeasure N] 0 := by
    intro c
    have h1 : (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U c
        - Qcomp p m eps (fun r => alphaFun p m r i) i j U c) = fun _ => (0 : ℝ) := by
      funext U; simp
    rw [h1, condExp_const ((enlFilt p m).le s) (0 : ℝ)]
    exact Filter.EventuallyEq.rfl
  intro a b hsa hab
  induction b with
  | zero =>
      have ha0 : a = 0 := Nat.le_zero.mp hab
      subst ha0
      exact hzero 0
  | succ b ih =>
      rcases Nat.lt_or_ge a (b + 1) with hlt | hge
      · have hab' : a ≤ b := Nat.lt_succ_iff.mp hlt
        have hsplit : (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U (b + 1)
              - Qcomp p m eps (fun r => alphaFun p m r i) i j U a)
            = (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U (b + 1)
                - Qcomp p m eps (fun r => alphaFun p m r i) i j U b)
              + fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U b
                - Qcomp p m eps (fun r => alphaFun p m r i) i j U a := by
          funext U; simp only [Pi.add_apply]; ring
        rw [hsplit]
        refine (condExp_add (integrable_Qcomp_increment hp0 hp1 (m := m) (t := b) (i := i) (j := j) hε)
          (by
            refine Integrable.sub ?_ ?_
            · exact integrable_Qcomp hp0 hp1 hε b
            · exact integrable_Qcomp hp0 hp1 hε a)
          (enlFilt p m s)).trans ?_
        refine (Filter.EventuallyEq.add
          (condExp_Qcomp_increment_eq_zero_of_le hp0 hp1 (m := m) (t := b) (s := s)
            (Nat.le_trans hsa hab') (i := i) (j := j) hε) (ih hab')).trans ?_
        simp
      · have hab' : b + 1 ≤ a := hge
        have heq : a = b + 1 := le_antisymm hab hab'
        subst heq
        exact hzero (b + 1)

/-! ## 6. Integrability of the ledger's own terms, and the mean-level occupation bound -/

/-- `Fcorr` at `b_n` and an *ambiently* measurable integer gap is ambient measurable.

`CorrectionDrift.measurable_Fcorr_gap_enl` only covers gaps measurable for the filtration at the
*same* index `n`; `Jcorr` needs the gap `X_{t+1} - M_t`, which mixes two indices. -/
theorem measurable_Fcorr_gap_ambient {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m n : ℕ) (j : Fin N)
    (a eps : ℝ) {φ : Array N → ℤ} (hφ : Measurable φ) :
    Measurable (fun U : Array N => SwarmOcc.Fcorr a eps (bRec p m n j U) (φ U)) := by
  have hb : Measurable (bRec p m n j) := measurable_ambient_of_enl (measurable_bRec_enl hp m n j)
  refine SwarmIID.measurable_of_countable_pieces
    (U := fun y : ℤ => fun U : Array N => SwarmOcc.Fcorr a eps (bRec p m n j U) y)
    (fun y => ?_) φ (fun y => hφ (measurableSet_singleton y))
  have hfun : (fun U : Array N => SwarmOcc.Fcorr a eps (bRec p m n j U) y)
      = fun U => ∑ i ∈ Finset.range y.toNat, SwarmOcc.Fdiff a eps (bRec p m n j U) i := by
    funext U
    rfl
  rw [hfun]
  exact Finset.measurable_sum _ (fun i _ => (measurable_Fdiff_right a eps i).comp hb)

/-- **The record-cost increment is integrable.**  It is a difference of two bounded measurable
terms: both `Fcorr` values are bounded by `abs_Fcorr_bRec_le`, uniformly in the array. -/
theorem integrable_Jcorr {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m t : ℕ) (i j : Fin N)
    {eps : ℝ} (hε : 0 < eps) :
    Integrable (fun U : Array N => Jcorr p m eps i j U t) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hp : (1 : ℝ) / 2 ≤ p := le_of_lt hp0
  have hpos : Measurable (fun U : Array N => (trajectory p m U (t + 1)).pos i) :=
    (enl_pos_measurable p m (t + 1) (k := t + 1) le_rfl i).mono
      ((enlFilt p m).le (t + 1)) le_rfl
  have hrm1 : Measurable (fun U : Array N => runMax p m U j (t + 1)) :=
    (measurable_runMax_enl p m (t + 1) j).mono ((enlFilt p m).le (t + 1)) le_rfl
  have hrm0 : Measurable (fun U : Array N => runMax p m U j t) :=
    (measurable_runMax_enl p m t j).mono ((enlFilt p m).le t) le_rfl
  have hφ1 : Measurable (fun U : Array N =>
      (trajectory p m U (t + 1)).pos i - runMax p m U j (t + 1)) := hpos.sub hrm1
  have hφ0 : Measurable (fun U : Array N =>
      (trajectory p m U (t + 1)).pos i - runMax p m U j t) := hpos.sub hrm0
  have hmeas : Measurable (fun U : Array N => Jcorr p m eps i j U t) :=
    (measurable_Fcorr_gap_ambient hp m (t + 1) j (aRec p m) eps hφ1).sub
      (measurable_Fcorr_gap_ambient hp m t j (aRec p m) eps hφ0)
  have hC1 : ∀ U : Array N, |SwarmOcc.Fcorr (aRec p m) eps (bRec p m (t + 1) j U)
      ((trajectory p m U (t + 1)).pos i - runMax p m U j (t + 1))|
      ≤ (2 * (((t + 1 : ℕ) : ℝ)) + 5) ^ 2 / (eps * (1 - aRec p m) ^ 2) :=
    fun U => abs_Fcorr_bRec_le hp0 hp1 m (t + 1) j hε U _
  have hC0 : ∀ U : Array N, |SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
      ((trajectory p m U (t + 1)).pos i - runMax p m U j t)|
      ≤ (2 * ((t : ℕ) : ℝ) + 5) ^ 2 / (eps * (1 - aRec p m) ^ 2) :=
    fun U => abs_Fcorr_bRec_le hp0 hp1 m t j hε U _
  refine Integrable.of_bound hmeas.aestronglyMeasurable
    (((2 * (((t + 1 : ℕ) : ℝ)) + 5) ^ 2 / (eps * (1 - aRec p m) ^ 2))
      + ((2 * ((t : ℕ) : ℝ) + 5) ^ 2 / (eps * (1 - aRec p m) ^ 2)))
    (Filter.Eventually.of_forall fun U => ?_)
  rw [Real.norm_eq_abs, Jcorr]
  have h := abs_sub (SwarmOcc.Fcorr (aRec p m) eps (bRec p m (t + 1) j U)
      ((trajectory p m U (t + 1)).pos i - runMax p m U j (t + 1)))
    (SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
      ((trajectory p m U (t + 1)).pos i - runMax p m U j t))
  linarith [hC1 U, hC0 U]

/-- **The `Z` potential is integrable at every fixed time.**  This is *not* immediate from
`Hpot(envH)(X_t)` (a position-indexed projection of the environment), but it follows from
`Zpot_zero` and the decomposition of `Z_T` into `T` integrable increments. -/
theorem integrable_Zpot {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) (i j : Fin N)
    {eps : ℝ} (hε : 0 < eps) (T : ℕ) :
    Integrable (fun U : Array N => Zpot p m eps i j U T) (arrayMeasure N) := by
  induction T with
  | zero =>
      rw [show (fun U : Array N => Zpot p m eps i j U 0) = fun _ => (0 : ℝ) from
        funext fun U => Zpot_zero p m eps i j U]
      exact integrable_zero _ _ _
  | succ T ih =>
      have hstep : Integrable (fun U : Array N =>
          Zpot p m eps i j U (T + 1) - Zpot p m eps i j U T) (arrayMeasure N) :=
        ((integrable_ZJinc hp0 hp1 m T i j hε).sub (integrable_Jcorr hp0 hp1 m T i j hε)).congr
          (Filter.Eventually.of_forall fun U => by
            simp only [Pi.sub_apply]
            ring)
      have hsum : (fun U : Array N => Zpot p m eps i j U (T + 1))
          = (fun U : Array N => Zpot p m eps i j U T)
            + fun U : Array N => Zpot p m eps i j U (T + 1) - Zpot p m eps i j U T := by
        funext U
        simp only [Pi.add_apply]
        ring
      rw [hsum]
      exact ih.add hstep

/-- **The `J`-sum is integrable.** -/
theorem integrable_Jsum {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) (i j : Fin N)
    {eps : ℝ} (hε : 0 < eps) (T : ℕ) :
    Integrable (fun U : Array N => Jsum p m eps i j U T) (arrayMeasure N) := by
  have hfun : (fun U : Array N => Jsum p m eps i j U T)
      = fun U => ∑ t ∈ Finset.range T, Jcorr p m eps i j U t := by
    funext U
    simp [Jsum]
  rw [hfun]
  exact integrable_finsetSum _ (fun t _ => integrable_Jcorr hp0 hp1 m t i j hε)

/-- **The occupation count is integrable**: it is a sum of `0/1` indicators, hence bounded by
`T`. -/
theorem integrable_occSum (p : ℝ) (m : ℕ) (i j : Fin N) (T : ℕ) :
    Integrable (fun U : Array N => occSum p m i j U T) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hterm : ∀ t : ℕ, Integrable (fun U : Array N =>
      SwarmOcc.occInd (fun s => (trajectory p m U s).pos i) (fun s => runMax p m U j s) t)
      (arrayMeasure N) := by
    intro t
    have hset : MeasurableSet {U : Array N | 0 ≤ (trajectory p m U t).pos i
        ∧ (trajectory p m U t).pos i ≤ runMax p m U j t} := by
      have h1 : MeasurableSet {U : Array N | (0 : ℤ) ≤ (trajectory p m U t).pos i} :=
        (enlFilt p m).le t _ (enl_pos_measurable p m t (k := t) le_rfl i
          (measurableSet_le (measurable_const (a := (0 : ℤ))) measurable_id))
      have h2 : MeasurableSet {U : Array N |
          (trajectory p m U t).pos i ≤ runMax p m U j t} := by
        have hg : Measurable (fun U : Array N =>
            (trajectory p m U t).pos i - runMax p m U j t) := by
          have hp1' : Measurable (fun U : Array N => (trajectory p m U t).pos i) :=
            (enl_pos_measurable p m t (k := t) le_rfl i).mono ((enlFilt p m).le t) le_rfl
          exact hp1'.sub ((measurable_runMax_enl p m t j).mono ((enlFilt p m).le t) le_rfl)
        have heq : {U : Array N | (trajectory p m U t).pos i ≤ runMax p m U j t}
            = (fun U : Array N => (trajectory p m U t).pos i - runMax p m U j t)
              ⁻¹' Set.Iic (0 : ℤ) := by
          ext U
          simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iic]
          omega
        rw [heq]
        exact hg measurableSet_Iic
      exact h1.inter h2
    have hind : (fun U : Array N =>
        SwarmOcc.occInd (fun s => (trajectory p m U s).pos i) (fun s => runMax p m U j s) t)
        = {U : Array N | 0 ≤ (trajectory p m U t).pos i
            ∧ (trajectory p m U t).pos i ≤ runMax p m U j t}.indicator (fun _ => (1 : ℝ)) := by
      funext U
      by_cases h : 0 ≤ (trajectory p m U t).pos i ∧ (trajectory p m U t).pos i ≤ runMax p m U j t
      · have hm : U ∈ {U : Array N | 0 ≤ (trajectory p m U t).pos i
            ∧ (trajectory p m U t).pos i ≤ runMax p m U j t} := Set.mem_ofPred_eq.mpr h
        rw [SwarmOcc.occInd, if_pos h, Set.indicator_of_mem hm]
      · have hm : U ∉ {U : Array N | 0 ≤ (trajectory p m U t).pos i
            ∧ (trajectory p m U t).pos i ≤ runMax p m U j t} := by
          rw [Set.mem_ofPred_eq]
          exact h
        rw [SwarmOcc.occInd, if_neg h, Set.indicator_of_notMem hm]
    rw [hind]
    exact (integrable_const (1 : ℝ)).indicator hset
  have hfun : (fun U : Array N => occSum p m i j U T)
      = fun U => ∑ t ∈ Finset.range T,
          SwarmOcc.occInd (fun s => (trajectory p m U s).pos i) (fun s => runMax p m U j s) t := by
    funext U
    simp [occSum]
  rw [hfun]
  exact integrable_finsetSum _ (fun t _ => hterm t)

/-- **The occupation ledger at expectation level, with the compensator discharged.**

From the a.e. finite-time ledger `VdriftTimeAssembly.ledger_actual` and the zero mean of `Qcomp`,
for every `T`

    ∫ occSum_T  <=  eps * T + ∫ Z_T + ∫ sum_{t<T} J_{t+1} .

This is the exact mean-level content of `(Vdrift)` plus the definition of `Qcomp`; the compensator
contributes nothing.  It is **not** the paper's pathwise `(occbnd)`: that needs the pathwise
budgets `hZ`, `hJ` and, in particular, the pathwise lower tail `hQ`, which no zero-mean statement
can supply. -/
theorem integral_occSum_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} {i j : Fin N}
    {eps : ℝ} (hε : 0 < eps)
    (hAB : ∀ n, Budget.paperWeight p m n i j
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j))
    (T : ℕ) :
    ∫ U : Array N, occSum p m i j U T ∂(arrayMeasure N)
      ≤ eps * (T : ℝ) + ∫ U : Array N, Zpot p m eps i j U T ∂(arrayMeasure N)
        + ∫ U : Array N, Jsum p m eps i j U T ∂(arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hOcc : Integrable (fun U : Array N => occSum p m i j U T) (arrayMeasure N) :=
    integrable_occSum p m i j T
  have hZ : Integrable (fun U : Array N => Zpot p m eps i j U T) (arrayMeasure N) :=
    integrable_Zpot hp0 hp1 m i j hε T
  have hZ0 : Integrable (fun U : Array N => Zpot p m eps i j U 0) (arrayMeasure N) :=
    integrable_Zpot hp0 hp1 m i j hε 0
  have hJ : Integrable (fun U : Array N => Jsum p m eps i j U T) (arrayMeasure N) :=
    integrable_Jsum hp0 hp1 m i j hε T
  have hQ : Integrable (fun U : Array N =>
      Qcomp p m eps (fun r => alphaFun p m r i) i j U T) (arrayMeasure N) :=
    integrable_Qcomp hp0 hp1 hε T
  have hledger := ledger_actual hp0 hp1 (m := m) (i := i) (j := j) hε hAB T
  have hchain : (fun U : Array N =>
        eps * (T : ℝ) + (Zpot p m eps i j U T - Zpot p m eps i j U 0)
          + Jsum p m eps i j U T - Qcomp p m eps (fun r => alphaFun p m r i) i j U T)
      =ᵐ[arrayMeasure N] fun U : Array N =>
        eps * (T : ℝ) + Zpot p m eps i j U T + Jsum p m eps i j U T
          - Qcomp p m eps (fun r => alphaFun p m r i) i j U T := by
    filter_upwards with U
    rw [Zpot_zero p m eps i j U]
    ring
  have hIntG : Integrable (fun U : Array N =>
      eps * (T : ℝ) + Zpot p m eps i j U T + Jsum p m eps i j U T
        - Qcomp p m eps (fun r => alphaFun p m r i) i j U T) (arrayMeasure N) :=
    (((integrable_const (eps * (T : ℝ))).add hZ).add hJ).sub hQ
  have hIntF : Integrable (fun U : Array N =>
      eps * (T : ℝ) + (Zpot p m eps i j U T - Zpot p m eps i j U 0)
        + Jsum p m eps i j U T - Qcomp p m eps (fun r => alphaFun p m r i) i j U T)
      (arrayMeasure N) :=
    hIntG.congr hchain.symm
  have hmono : ∫ U : Array N, occSum p m i j U T ∂(arrayMeasure N)
      ≤ ∫ U : Array N, eps * (T : ℝ) + (Zpot p m eps i j U T - Zpot p m eps i j U 0)
          + Jsum p m eps i j U T - Qcomp p m eps (fun r => alphaFun p m r i) i j U T
        ∂(arrayMeasure N) :=
    integral_mono_ae hOcc hIntF hledger
  have h1 : ∫ U : Array N, eps * (T : ℝ) + (Zpot p m eps i j U T - Zpot p m eps i j U 0)
        + Jsum p m eps i j U T - Qcomp p m eps (fun r => alphaFun p m r i) i j U T
        ∂(arrayMeasure N)
      = ∫ U : Array N, eps * (T : ℝ) + Zpot p m eps i j U T + Jsum p m eps i j U T
          - Qcomp p m eps (fun r => alphaFun p m r i) i j U T ∂(arrayMeasure N) :=
    integral_congr_ae hchain
  have h2 : ∫ U : Array N, eps * (T : ℝ) + Zpot p m eps i j U T + Jsum p m eps i j U T
        - Qcomp p m eps (fun r => alphaFun p m r i) i j U T ∂(arrayMeasure N)
      = eps * (T : ℝ) + ∫ U : Array N, Zpot p m eps i j U T ∂(arrayMeasure N)
        + ∫ U : Array N, Jsum p m eps i j U T ∂(arrayMeasure N) := by
    have hA : ∫ U : Array N, (eps * (T : ℝ) + Zpot p m eps i j U T + Jsum p m eps i j U T
          - Qcomp p m eps (fun r => alphaFun p m r i) i j U T) ∂(arrayMeasure N)
        = ∫ U : Array N, (eps * (T : ℝ) + Zpot p m eps i j U T + Jsum p m eps i j U T)
            ∂(arrayMeasure N)
          - ∫ U : Array N, Qcomp p m eps (fun r => alphaFun p m r i) i j U T
            ∂(arrayMeasure N) :=
      integral_sub (((integrable_const (eps * (T : ℝ))).add hZ).add hJ) hQ
    rw [hA, integral_Qcomp_eq_zero hp0 hp1 hε T, sub_zero]
    have hB : ∫ U : Array N, (eps * (T : ℝ) + Zpot p m eps i j U T + Jsum p m eps i j U T)
          ∂(arrayMeasure N)
        = ∫ U : Array N, (eps * (T : ℝ) + Zpot p m eps i j U T) ∂(arrayMeasure N)
          + ∫ U : Array N, Jsum p m eps i j U T ∂(arrayMeasure N) :=
      integral_add ((integrable_const (eps * (T : ℝ))).add hZ) hJ
    rw [hB]
    have hC : ∫ U : Array N, (eps * (T : ℝ) + Zpot p m eps i j U T) ∂(arrayMeasure N)
        = eps * (T : ℝ) + ∫ U : Array N, Zpot p m eps i j U T ∂(arrayMeasure N) := by
      rw [integral_add (integrable_const (eps * (T : ℝ))) hZ, integral_const]
      simp only [smul_eq_mul, Measure.real, measure_univ, ENNReal.toReal_one, one_mul]
    rw [hC]
  linarith [hmono, h1, h2]

/-! ## 7. The `enlFilt`-measurability layer: `corrDrift`, and the martingale under an explicit
adaptedness hypothesis

`Edrift` is `condExp (enlFilt t) (HpotInc) - corrDrift`, so the drift term needs no adaptedness of
`Zpot`: `condExp` is strongly measurable by construction and `corrDrift` is `enlFilt t`-measurable
because it only reads `alphaFun t`, `bRec t` and the gap at `t`.  What is genuinely missing for a
martingale statement is the *future* measurability of the `Z`-plus-`J` increment, whose
`Hpot (envH) (X_{t+1})` part is a position-indexed environment projection.  That is isolated below
as the single named hypothesis `hadapt` with its exact type; everything else is proved. -/

/-- The `Z`-plus-`J` increment of the ledger. -/
noncomputable def ZJinc (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) (t : ℕ) : ℝ :=
  Zpot p m eps i j U (t + 1) - Zpot p m eps i j U t + Jcorr p m eps i j U t

/-- `ZJinc` is integrable (restatement of `integrable_ZJinc`). -/
theorem integrable_ZJinc_def {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m t : ℕ)
    (i j : Fin N) {eps : ℝ} (hε : 0 < eps) :
    Integrable (fun U : Array N => ZJinc p m eps i j U t) (arrayMeasure N) :=
  integrable_ZJinc hp0 hp1 m t i j hε

/-- **`corrDrift` is `enlFilt t`-measurable.** -/
theorem measurable_corrDrift_enl {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m t : ℕ) (i j : Fin N)
    (eps : ℝ) :
    Measurable[enlFilt p m t] (fun U : Array N => corrDrift (aRec p m) eps
      (alphaFun p m t i U) (bRec p m t j U)
      ((trajectory p m U t).pos i - runMax p m U j t)) := by
  letI : MeasurableSpace (Array N) := enlFilt p m t
  have hα : Measurable (alphaFun p m t i) := measurable_alphaFun_enl p m t i
  have hup : Measurable (fun U : Array N => SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
      ((trajectory p m U t).pos i - runMax p m U j t + 1)) :=
    measurable_Fcorr_gap_enl hp m t j (aRec p m) eps (measurable_gap_add_enl p m t i j)
  have hdn : Measurable (fun U : Array N => SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
      ((trajectory p m U t).pos i - runMax p m U j t - 1)) :=
    measurable_Fcorr_gap_enl hp m t j (aRec p m) eps (measurable_gap_sub_enl p m t i j)
  have hz : Measurable (fun U : Array N => SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
      ((trajectory p m U t).pos i - runMax p m U j t)) :=
    measurable_Fcorr_gap_enl hp m t j (aRec p m) eps (measurable_gap_enl p m t i j)
  simp only [corrDrift]
  exact ((hα.mul hup).add ((measurable_const.sub hα).mul hdn)).sub hz

/-- **`Edrift` is `enlFilt t`-strongly measurable.** -/
theorem stronglyMeasurable_Edrift_enl {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m t : ℕ) (i j : Fin N)
    (eps : ℝ) :
    StronglyMeasurable[enlFilt p m t]
      (fun U : Array N => Edrift p m eps (fun r => alphaFun p m r i) i j U t) := by
  have hc : StronglyMeasurable[enlFilt p m t]
      (fun U : Array N => condExp (enlFilt p m t) (arrayMeasure N) (HpotInc p m t i j) U) :=
    MeasureTheory.stronglyMeasurable_condExp
  have hcd : StronglyMeasurable[enlFilt p m t] (fun U : Array N =>
      corrDrift (aRec p m) eps (alphaFun p m t i U) (bRec p m t j U)
        ((trajectory p m U t).pos i - runMax p m U j t)) :=
    (measurable_corrDrift_enl hp m t i j eps).stronglyMeasurable
  have hfun : (fun U : Array N => Edrift p m eps (fun r => alphaFun p m r i) i j U t)
      = (fun U : Array N => condExp (enlFilt p m t) (arrayMeasure N) (HpotInc p m t i j) U)
        - fun U : Array N => corrDrift (aRec p m) eps (alphaFun p m t i U) (bRec p m t j U)
            ((trajectory p m U t).pos i - runMax p m U j t) := by
    funext U
    rfl
  rw [hfun]
  exact hc.sub hcd

/-- **The `t`-th increment of `Qcomp` is `enlFilt (t+1)`-strongly measurable**, given the named
adaptedness hypothesis on the `Z`-plus-`J` increment. -/
theorem stronglyMeasurable_Qinc_of_adapted {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {i j : Fin N} {eps : ℝ} (hε : 0 < eps)
    (hadapt : ∀ t, StronglyMeasurable[enlFilt p m (t + 1)] (fun U => ZJinc p m eps i j U t))
    (t : ℕ) :
    StronglyMeasurable[enlFilt p m (t + 1)]
      (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U (t + 1)
        - Qcomp p m eps (fun r => alphaFun p m r i) i j U t) := by
  have hmono : (enlFilt (N := N) p m t : MeasurableSpace (Array N))
      ≤ enlFilt (N := N) p m (t + 1) :=
    Filtration.mono (enlFilt (N := N) p m) (Nat.le_succ t)
  have hE : StronglyMeasurable[enlFilt p m (t + 1)]
      (fun U : Array N => Edrift p m eps (fun r => alphaFun p m r i) i j U t) :=
    (stronglyMeasurable_Edrift_enl hp0.le m t i j eps).mono hmono
  have hfun : (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U (t + 1)
        - Qcomp p m eps (fun r => alphaFun p m r i) i j U t)
      = (fun U : Array N => ZJinc p m eps i j U t)
        - fun U : Array N => Edrift p m eps (fun r => alphaFun p m r i) i j U t := by
    funext U
    simp only [ZJinc, Pi.sub_apply]
    rw [Qcomp_succ_sub p m eps (fun r => alphaFun p m r i) i j U t]
  rw [hfun]
  exact (hadapt t).sub hE

/-- **`Qcomp · T` is `enlFilt T`-strongly measurable**, given the named adaptedness hypothesis. -/
theorem stronglyMeasurable_Qcomp_of_adapted {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {i j : Fin N} {eps : ℝ} (hε : 0 < eps)
    (hadapt : ∀ t, StronglyMeasurable[enlFilt p m (t + 1)] (fun U => ZJinc p m eps i j U t))
    (T : ℕ) :
    StronglyMeasurable[enlFilt p m T]
      (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U T) := by
  induction T with
  | zero =>
      rw [show (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U 0)
        = fun _ => (0 : ℝ) from
          funext fun U => Qcomp_zero p m eps (fun r => alphaFun p m r i) i j U]
      exact stronglyMeasurable_const
  | succ T ih =>
      have hstep := stronglyMeasurable_Qinc_of_adapted hp0 hp1 hε hadapt T
      have hmono : (enlFilt (N := N) p m T : MeasurableSpace (Array N))
          ≤ enlFilt (N := N) p m (T + 1) :=
        Filtration.mono (enlFilt (N := N) p m) (Nat.le_succ T)
      have hsum : (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U (T + 1))
          = (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U T)
            + fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U (T + 1)
              - Qcomp p m eps (fun r => alphaFun p m r i) i j U T := by
        funext U
        simp only [Pi.add_apply]
        ring
      rw [hsum]
      exact (ih.mono hmono).add hstep

/-- **The compensator's block conditionals, from the named adaptedness hypothesis.**
`condExp (enlFilt a) (Qcomp b) =ᵐ Qcomp a` for `a ≤ b`: the block `Qcomp b - Qcomp a` is centred
given `enlFilt a` (proved unconditionally in `condExp_Qcomp_block_eq_zero`), and `Qcomp a` is
`enlFilt a`-measurable under `hadapt`. -/
theorem condExp_Qcomp_eq_of_adapted {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {i j : Fin N} {eps : ℝ} (hε : 0 < eps)
    (hadapt : ∀ t, StronglyMeasurable[enlFilt p m (t + 1)] (fun U => ZJinc p m eps i j U t))
    {a b : ℕ} (hab : a ≤ b) :
    condExp (enlFilt p m a) (arrayMeasure N) (fun U : Array N =>
        Qcomp p m eps (fun r => alphaFun p m r i) i j U b)
      =ᵐ[arrayMeasure N] fun U : Array N =>
        Qcomp p m eps (fun r => alphaFun p m r i) i j U a := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hA : Integrable (fun U : Array N =>
      Qcomp p m eps (fun r => alphaFun p m r i) i j U a) (arrayMeasure N) :=
    integrable_Qcomp hp0 hp1 hε a
  have hD : Integrable (fun U : Array N =>
      Qcomp p m eps (fun r => alphaFun p m r i) i j U b
        - Qcomp p m eps (fun r => alphaFun p m r i) i j U a) (arrayMeasure N) :=
    (integrable_Qcomp hp0 hp1 hε b).sub hA
  have hsplit : (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U b)
      = (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U b
          - Qcomp p m eps (fun r => alphaFun p m r i) i j U a)
        + fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U a := by
    funext U
    simp only [Pi.add_apply]
    ring
  rw [hsplit]
  refine (condExp_add hD hA (enlFilt p m a)).trans ?_
  have hQa : condExp (enlFilt p m a) (arrayMeasure N)
      (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U a)
      = fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U a :=
    condExp_of_stronglyMeasurable ((enlFilt p m).le a)
      (stronglyMeasurable_Qcomp_of_adapted hp0 hp1 hε hadapt a) hA
  refine (Filter.EventuallyEq.add
    (condExp_Qcomp_block_eq_zero (p := p) (m := m) (s := a) (i := i) (j := j) hp0 hp1 hε
      a b le_rfl hab) (Filter.EventuallyEq.of_eq hQa)).trans ?_
  simp

/-- **`Qcomp` is a martingale for the enlarged filtration, given the adaptedness of the
`Z`-plus-`J` increment.**  The hypothesis `hadapt` is the *only* unproved input here, and it is
stated as an explicit hypothesis with its exact type — it is not an axiom and not asserted
anywhere.  In particular this file does **not** prove `Martingale` unconditionally. -/
theorem martingale_Qcomp {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {i j : Fin N} {eps : ℝ} (hε : 0 < eps)
    (hadapt : ∀ t, StronglyMeasurable[enlFilt p m (t + 1)] (fun U => ZJinc p m eps i j U t)) :
    Martingale (fun T (U : Array N) =>
        Qcomp p m eps (fun r => alphaFun p m r i) i j U T) (enlFilt p m) (arrayMeasure N) :=
  ⟨fun T => stronglyMeasurable_Qcomp_of_adapted hp0 hp1 hε hadapt T,
    fun a b hab => condExp_Qcomp_eq_of_adapted hp0 hp1 hε hadapt hab⟩

/-! ## 8. Boundedness and integrability of the drift `Edrift`

`Edrift` is the compensator's predictable part.  Its `condExp` summand is integrable by
construction; the explicit part is `corrDrift`, which is uniformly bounded in the array at each
fixed time because each `Fcorr` factor is (`CorrectionDrift.abs_Fcorr_bRec_le`) and the jump
probability lies in `[0,1]`. -/

/-- **Uniform bound on `corrDrift`** at fixed `t`. -/
theorem abs_corrDrift_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m t : ℕ) (i j : Fin N)
    {eps : ℝ} (hε : 0 < eps) (U : Array N) :
    |corrDrift (aRec p m) eps (alphaFun p m t i U) (bRec p m t j U)
        ((trajectory p m U t).pos i - runMax p m U j t)|
      ≤ 3 * ((2 * ((t : ℕ) : ℝ) + 5) ^ 2 / (eps * (1 - aRec p m) ^ 2)) := by
  set C : ℝ := (2 * ((t : ℕ) : ℝ) + 5) ^ 2 / (eps * (1 - aRec p m) ^ 2) with hC
  have ha1 : aRec p m < 1 := aRec_lt_one hp0 hp1 m
  have hC0 : 0 ≤ C := by
    have h1 : (0 : ℝ) < 1 - aRec p m := by linarith
    have h2 : (0 : ℝ) < eps * (1 - aRec p m) ^ 2 := by positivity
    have h3 : (0 : ℝ) ≤ (2 * ((t : ℕ) : ℝ) + 5) ^ 2 := sq_nonneg _
    exact div_nonneg h3 h2.le
  have hFu := abs_Fcorr_bRec_le hp0 hp1 m t j hε U
    ((trajectory p m U t).pos i - runMax p m U j t + 1)
  have hFd := abs_Fcorr_bRec_le hp0 hp1 m t j hε U
    ((trajectory p m U t).pos i - runMax p m U j t - 1)
  have hFz := abs_Fcorr_bRec_le hp0 hp1 m t j hε U
    ((trajectory p m U t).pos i - runMax p m U j t)
  have hα0 : (0 : ℝ) ≤ alphaFun p m t i U := (alphaFun_mem_Icc hp0 hp1 m t i U).1
  have hα1 : alphaFun p m t i U ≤ 1 := (alphaFun_mem_Icc hp0 hp1 m t i U).2
  have hαabs : |alphaFun p m t i U| ≤ 1 := abs_le.mpr ⟨by linarith, hα1⟩
  have h1α : |1 - alphaFun p m t i U| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hm1 : |alphaFun p m t i U * SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
      ((trajectory p m U t).pos i - runMax p m U j t + 1)| ≤ C := by
    rw [abs_mul]
    calc |alphaFun p m t i U| * |SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
          ((trajectory p m U t).pos i - runMax p m U j t + 1)|
        ≤ 1 * C := by
          refine mul_le_mul hαabs hFu (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  have hm2 : |(1 - alphaFun p m t i U) * SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
      ((trajectory p m U t).pos i - runMax p m U j t - 1)| ≤ C := by
    rw [abs_mul]
    calc |1 - alphaFun p m t i U| * |SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
          ((trajectory p m U t).pos i - runMax p m U j t - 1)|
        ≤ 1 * C := by
          refine mul_le_mul h1α hFd (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  have htri : |alphaFun p m t i U * SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
        ((trajectory p m U t).pos i - runMax p m U j t + 1)
      + (1 - alphaFun p m t i U) * SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
        ((trajectory p m U t).pos i - runMax p m U j t - 1)
      - SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
        ((trajectory p m U t).pos i - runMax p m U j t)|
      ≤ C + C + C := by
    refine le_trans (abs_sub _ _) ?_
    refine le_trans (add_le_add (abs_add_le _ _) le_rfl) ?_
    exact add_le_add (add_le_add hm1 hm2) hFz
  calc |corrDrift (aRec p m) eps (alphaFun p m t i U) (bRec p m t j U)
        ((trajectory p m U t).pos i - runMax p m U j t)|
      = |alphaFun p m t i U * SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
          ((trajectory p m U t).pos i - runMax p m U j t + 1)
        + (1 - alphaFun p m t i U) * SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
          ((trajectory p m U t).pos i - runMax p m U j t - 1)
        - SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
          ((trajectory p m U t).pos i - runMax p m U j t)| := by
        rw [corrDrift]
    _ ≤ C + C + C := htri
    _ = 3 * C := by ring

/-- `corrDrift` is integrable at every fixed time (bounded measurable). -/
theorem integrable_corrDrift {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m t : ℕ)
    (i j : Fin N) {eps : ℝ} (hε : 0 < eps) :
    Integrable (fun U : Array N => corrDrift (aRec p m) eps (alphaFun p m t i U)
      (bRec p m t j U) ((trajectory p m U t).pos i - runMax p m U j t)) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hmeas : Measurable (fun U : Array N => corrDrift (aRec p m) eps (alphaFun p m t i U)
      (bRec p m t j U) ((trajectory p m U t).pos i - runMax p m U j t)) :=
    measurable_ambient_of_enl (p := p) (m := m) (n := t)
      (measurable_corrDrift_enl hp0.le m t i j eps)
  refine Integrable.of_bound hmeas.aestronglyMeasurable
    (3 * ((2 * ((t : ℕ) : ℝ) + 5) ^ 2 / (eps * (1 - aRec p m) ^ 2)))
    (Filter.Eventually.of_forall fun U => ?_)
  rw [Real.norm_eq_abs]
  exact abs_corrDrift_le hp0 hp1 m t i j hε U

/-- **`Edrift` is integrable at every fixed time.** -/
theorem integrable_Edrift {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m t : ℕ)
    (i j : Fin N) {eps : ℝ} (hε : 0 < eps) :
    Integrable (fun U : Array N => Edrift p m eps (fun r => alphaFun p m r i) i j U t)
      (arrayMeasure N) := by
  have hfun : (fun U : Array N => Edrift p m eps (fun r => alphaFun p m r i) i j U t)
      = (fun U : Array N => condExp (enlFilt p m t) (arrayMeasure N) (HpotInc p m t i j) U)
        - fun U : Array N => corrDrift (aRec p m) eps (alphaFun p m t i U) (bRec p m t j U)
            ((trajectory p m U t).pos i - runMax p m U j t) := by
    funext U
    rfl
  rw [hfun]
  exact integrable_condExp.sub (integrable_corrDrift hp0 hp1 m t i j hε)


end VdriftAssembly
end Swarming.Enl
