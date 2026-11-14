/-
  **DIRECTION F (m6) — `VdriftTimeAssembly.lean`: the time-indexed interface from the one-step
  `paperWeight` budget to the integrated `SwarmOcc` `(Zloss)` / `(Vdrift)` / correction-drift
  APIs.**

  What this file is for.  The integrated one-step results of the filtration area are *integral*
  statements (`DischargeInputs.integral_HpotInc_ge_paperWeight_discharged`) plus *restricted*
  `condExp` statements on the below / record / above pieces.  The occupation chain of the
  transience area consumes the paper's `(Zloss)` in a **pointwise** form:
  `SwarmOcc.Vdrift_combine` takes `hDh : ZlossLhs ≤ Dh` as an ordinary inequality of real
  numbers at the actual record `r = M_n^j`, `x = X_n^i`, `b = b_n`, `a = aRec p m`, and
  `SwarmOcc.sum_drift_bound` sums such one-step bounds over `t < T` with a compensator `Q`.
  This file builds exactly that bridge, with every premise visible.

  1. `paperWeight_eq_ZlossLhs`, `paperWeight_eq_occInd_sub`: `Budget.paperWeight` **is** the
     left-hand side of `SwarmOcc.Zloss` and the `hDh` input of `SwarmOcc.Vdrift_combine`, and its
     first term is `SwarmOcc.occInd` at the actual path `t : X_t^i`, `t : M_t^j`.  Definitional.
  2. `oneStep_drift`: the pointwise `enlFilt` bound of Directions A/B (explicit hypothesis `hAB`)
     plus the deterministic correction drift `Fcorr_coin_drift` gives, a.e.
     `1{0 <= X_n^i <= M_n^j} - eps <= E[HpotInc | enlFilt n] - corrDrift`.  This is `(Vdrift)`.
     **Why a pointwise hypothesis is needed and an integral one will not do**: `Vdrift_combine`
     consumes `hDh` at a single `(x, r)` per `w`; an integrated inequality
     `int paperWeight <= int HpotInc` constrains only the relative size of the integrals, and the
     sum `sum_{t<T}` in `sum_drift_bound` is taken pathwise, before any integration.
  3. `Zpot`, `Jcorr`, `Cinc`: the paper's `Z_n = H(X_n^i) - F_{b_n}(X_n^i - M_n^j)`, the
     record-cost increment `J_{n+1}`, and the correction increment.  `Zpot_add_J` is the *exact*
     algebra `Z_{n+1} - Z_n + J_{n+1} = HpotInc_n - Cinc_n`, so the correction residual is
     `Cinc`, not an absorbed error term.  `sum_HpotInc` telescopes the `Hpot` part pathwise.
  4. `Qcomp`: the compensator of the ledger, **defined** by
     `Q_T = Z_T - Z_0 + sum_{t<T} J_{t+1} - sum_{t<T} E_t` (as in `SwarmOcc.sum_drift_bound`),
     with `Qcomp_eq_sum_increments` showing it is literally `sum_{t<T} xi_t`, and
     `occupation_ledger` producing the finite-time bound from the one-step bounds.  No martingale,
     no `o(n)` and no bound on `Q` is asserted here: `Q` is a ledger entry whose bounds stay
     explicit inputs.
  5. `compensator_of_correction`: the compensator identification reduces *exactly* to the
     correction-drift identity `condExp (enlFilt n) (Cinc n) = corrDrift`, which
     `CorrectionDrift.lean` discharges unconditionally.
  6. `sum_gain_le_loss_telescope`: the same time aggregation at the **integral** (mean) level,
     using only the already-integrated unconditional budget
     `integral_HpotInc_ge_paperWeight_discharged`.  No `Q`, no compensator, no pointwise
     hypothesis -- the price is that it is an expectation-level statement.

  Nothing here asserts a martingale, a strong law, occupation, regeneration, `Q`, or the main
  theorem.  Every stochastic premise that is not discharged is an explicit hypothesis, named.
-/
import Swarm.GlobalIntegralBudget
import Swarm.DischargeInputs
import Swarm.OccAssemble
import Swarm.Vdrift
import Swarm.Zdrift

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl
namespace VdriftAssembly

open Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross

variable {N : ℕ}

/-! ## 1. `Budget.paperWeight` is the `(Zloss)` / `Vdrift_combine` left-hand side

`SwarmOcc.Zloss` concludes `forall x, ZlossLhs a b x r <= alpha E x - (1-alpha) Env x`, and
`SwarmOcc.Vdrift_combine` consumes `ZlossLhs a b x r <= Dh` at `x = X_n^i`, `r = M_n^j`,
`b = b_n`, `a = aRec p m`.  `Budget.paperWeight` is that same expression at the actual model;
the two identifications below are definitional (no rewriting, no side conditions). -/

/-- The paper's `(Zloss)` left-hand side at `(x, r, b, a)`:
`1{0 <= x <= r} - b a^{(x-r)} 1{r <= x}`. -/
noncomputable def ZlossLhs (a b : ℝ) (x r : ℤ) : ℝ :=
  (if 0 ≤ x ∧ x ≤ r then (1 : ℝ) else 0)
    - b * (if r ≤ x then a ^ (x - r).toNat else 0)

/-- **`Budget.paperWeight` is `ZlossLhs`.**  Definitional. -/
theorem paperWeight_eq_ZlossLhs (p : ℝ) (m n : ℕ) (i j : Fin N) (U : Array N) :
    Budget.paperWeight p m n i j U
      = ZlossLhs (aRec p m) (bRec p m n j U) ((trajectory p m U n).pos i)
          (runMax p m U j n) := rfl

/-- **`Budget.paperWeight` in the `occInd` spelling of the summed ledger.**  The gain term is
exactly `SwarmOcc.occInd` at the actual path `t : X_t^i` and running record `t : M_t^j`, which is
the `ind` of `SwarmOcc.sum_drift_bound`.  Definitional. -/
theorem paperWeight_eq_occInd_sub (p : ℝ) (m n : ℕ) (i j : Fin N) (U : Array N) :
    Budget.paperWeight p m n i j U
      = SwarmOcc.occInd (fun t => (trajectory p m U t).pos i) (fun t => runMax p m U j t) n
        - bRec p m n j U * (if runMax p m U j n ≤ (trajectory p m U n).pos i then
            aRec p m ^ ((trajectory p m U n).pos i - runMax p m U j n).toNat else 0) := rfl

/-- The paper's one-step gain indicator `1{0 <= X_n^i <= M_n^j}`. -/
noncomputable def gainInd (p : ℝ) (m n : ℕ) (i j : Fin N) (U : Array N) : ℝ :=
  if 0 ≤ (trajectory p m U n).pos i ∧ (trajectory p m U n).pos i ≤ runMax p m U j n then
    (1 : ℝ) else 0

/-- The paper's one-step loss term `b_n a^{(X_n^i - M_n^j)} 1{M_n^j <= X_n^i}`. -/
noncomputable def lossTerm (p : ℝ) (m n : ℕ) (i j : Fin N) (U : Array N) : ℝ :=
  bRec p m n j U * (if runMax p m U j n ≤ (trajectory p m U n).pos i then
    aRec p m ^ ((trajectory p m U n).pos i - runMax p m U j n).toNat else 0)

/-- **`paperWeight = gain - loss`**: the paper's one-step weight splits into the gain indicator
and the (nonnegative) loss term.  Definitional. -/
theorem paperWeight_eq_gain_sub_loss (p : ℝ) (m n : ℕ) (i j : Fin N) (U : Array N) :
    Budget.paperWeight p m n i j U = gainInd p m n i j U - lossTerm p m n i j U := rfl

/-! ## 2. The correction drift `(Fdrift)`, and the one step of `(Vdrift)` -/

/-- The paper's correction drift of the potential `F_b` at gap `g`, in the notation of the
assembly: `alpha F_b(g+1) + (1-alpha) F_b(g-1) - F_b(g)`.  This is the `Df` of
`SwarmOcc.Vdrift_combine`. -/
noncomputable def corrDrift (a ε α b : ℝ) (g : ℤ) : ℝ :=
  α * SwarmOcc.Fcorr a ε b (g + 1) + (1 - α) * SwarmOcc.Fcorr a ε b (g - 1)
    - SwarmOcc.Fcorr a ε b g

/-- `(Fdrift)` in assembly notation: `corrDrift <= FbRHS` is exactly
`SwarmOcc.Fcorr_coin_drift`.  Purely deterministic. -/
theorem corrDrift_le_FbRHS {a ε b α : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hε : 0 < ε) (hα : 1 / 2 ≤ α) (g : ℤ) :
    corrDrift a ε α b g ≤ SwarmOcc.FbRHS a b ε g :=
  SwarmOcc.Fcorr_coin_drift ha0 ha1 hb hε hα g

/-- The one-step drift of `Z_{n+1} - Z_n + J_{n+1}` read off the one-step `Hpot` drift: the
`enlFilt n`-conditional mean of the increment minus the correction drift.  This is the `E_t` of
`SwarmOcc.sum_drift_bound`; `compensator_of_correction` shows it *is* the conditional mean of
`Z_{n+1} - Z_n + J_{n+1}`. -/
noncomputable def Edrift (p : ℝ) (m : ℕ) (eps : ℝ) (α : ℕ → Array N → ℝ) (i j : Fin N)
    (U : Array N) (t : ℕ) : ℝ :=
  condExp (enlFilt p m t) (arrayMeasure N) (HpotInc p m t i j) U
    - corrDrift (aRec p m) eps (α t U) (bRec p m t j U)
        ((trajectory p m U t).pos i - runMax p m U j t)

/-- **One step of `(Vdrift)` on the actual array.**

Input: the a.e. pointwise `enlFilt p m n` lower bound of Directions A/B, in the exact form
`Budget.paperWeight <= E[HpotInc | enlFilt n]`.  Output: a.e.

    1{0 <= X_n^i <= M_n^j} - eps <= E[HpotInc | enlFilt n] - (alpha F_b(g+1) + (1-alpha) F_b(g-1) - F_b(g)),

`g = X_n^i - M_n^j`, `b = b_n`, `a = aRec p m`.  The `alpha` is the actual right-jump probability
`alpha_n^i`, taken as a parameter with the model bound `1/2 <= alpha`; the deterministic side only
uses `alpha >= 1/2` (`Fcorr_coin_drift`). -/
theorem oneStep_drift {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m n : ℕ} {i j : Fin N}
    {eps : ℝ} {α : ℕ → Array N → ℝ} (hε : 0 < eps) (hα : ∀ U, 1 / 2 ≤ α n U)
    (hAB : Budget.paperWeight p m n i j
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j)) :
    (fun U : Array N =>
        SwarmOcc.occInd (fun t => (trajectory p m U t).pos i) (fun t => runMax p m U j t) n
          - eps)
      ≤ᵐ[arrayMeasure N] fun U => Edrift p m eps α i j U n := by
  filter_upwards [hAB] with U hU
  have hDh : (if 0 ≤ (trajectory p m U n).pos i
        ∧ (trajectory p m U n).pos i ≤ runMax p m U j n then (1 : ℝ) else 0)
      - bRec p m n j U * (if runMax p m U j n ≤ (trajectory p m U n).pos i then
          aRec p m ^ ((trajectory p m U n).pos i - runMax p m U j n).toNat else 0)
      ≤ condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j) U := hU
  have hb : (0 : ℝ) ≤ bRec p m n j U := by
    have h3 := three_le_bRec hp0 hp1 m n j U
    linarith
  have h := SwarmOcc.Vdrift_Fcorr (zero_le_aRec hp0 hp1 m) (aRec_lt_one hp0 hp1 m) hb hε
    (hα U) (runMax p m U j n) ((trajectory p m U n).pos i)
    (condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j) U) hDh
  simpa only [SwarmOcc.occInd, Edrift, corrDrift, Pi.sub_apply] using h

/-- The one-step bounds, simultaneously for all `n`, in the shape of the summed ledger. -/
theorem oneStep_all {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} {i j : Fin N}
    {eps : ℝ} {α : ℕ → Array N → ℝ} (hε : 0 < eps) (hα : ∀ t U, 1 / 2 ≤ α t U)
    (hAB : ∀ n, Budget.paperWeight p m n i j
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j)) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ n : ℕ,
      SwarmOcc.occInd (fun t => (trajectory p m U t).pos i) (fun t => runMax p m U j t) n - eps
        ≤ Edrift p m eps α i j U n := by
  rw [MeasureTheory.ae_all_iff]
  intro n
  exact oneStep_drift hp0 hp1 hε (hα n) (hAB n)

/-! ## 3. The `Z` potential, the record-cost increment `J`, and the correction increment

These are raw auxiliary objects. `Jcorr t` is `J_{t+1}` and `Cinc t` is the                   
correction increment; the projected version is in `ProjOptionalLedger`.      
`Z_{n+1} - Z_n + J_{n+1} = (H_{n+1} - H_n) - dF_b`. -/

/-- Raw auxiliary potential; the adapted projected version is `ProjLedger.Zproj`. -/          
noncomputable def Zpot (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) (t : ℕ) : ℝ :=
  SwarmOcc.Hpot (envH p m j U) ((trajectory p m U t).pos i)
    - SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
        ((trajectory p m U t).pos i - runMax p m U j t)

/-- The paper's record-cost increment `J_{t+1} = F_{b_{t+1}}(X_{t+1} - M_{t+1})
- F_{b_t}(X_{t+1} - M_t)`. -/
noncomputable def Jcorr (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) (t : ℕ) : ℝ :=
  SwarmOcc.Fcorr (aRec p m) eps (bRec p m (t + 1) j U)
      ((trajectory p m U (t + 1)).pos i - runMax p m U j (t + 1))
    - SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
      ((trajectory p m U (t + 1)).pos i - runMax p m U j t)

/-- The correction increment of the `Z` potential at frozen record cost and record:
`F_{b_t}(X_{t+1} - M_t) - F_{b_t}(X_t - M_t)`.  This is the object whose conditional mean is
the paper's `(Fdrift)` correction drift `corrDrift`. -/
noncomputable def Cinc (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) (t : ℕ) : ℝ :=
  SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
      ((trajectory p m U (t + 1)).pos i - runMax p m U j t)
    - SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
      ((trajectory p m U t).pos i - runMax p m U j t)

/-- **The exact one-step algebra of the ledger** (the paper's `(Vdrift)` decomposition):
`Z_{t+1} - Z_t + J_{t+1} = HpotInc_t - Cinc_t`.  The `F_{b_{t+1}}` terms cancel exactly; the
correction residual is `Cinc_t` and nothing else. -/
theorem Zpot_add_J (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) (t : ℕ) :
    Zpot p m eps i j U (t + 1) - Zpot p m eps i j U t + Jcorr p m eps i j U t
      = HpotInc p m t i j U - Cinc p m eps i j U t := by
  simp only [Zpot, Jcorr, Cinc, HpotInc]
  ring

/-- **The `Hpot` part telescopes**: the increment uses one fixed environment `envH p m j U`, so
the sum over `t < T` is the difference of two potentials.  This is what turns the summed drift
bound into the `Z_T - Z_0` term of `(occbnd)`. -/
theorem sum_HpotInc (p : ℝ) (m : ℕ) (i j : Fin N) (U : Array N) (T : ℕ) :
    ∑ t ∈ Finset.range T, HpotInc p m t i j U
      = SwarmOcc.Hpot (envH p m j U) ((trajectory p m U T).pos i)
        - SwarmOcc.Hpot (envH p m j U) ((trajectory p m U 0).pos i) := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Finset.sum_range_succ, ih]
      have h : HpotInc p m T i j U
          = SwarmOcc.Hpot (envH p m j U) ((trajectory p m U (T + 1)).pos i)
            - SwarmOcc.Hpot (envH p m j U) ((trajectory p m U T).pos i) := rfl
      rw [h]
      ring

/-! ## 4. The finite-time ledger and its compensator -/

/-- The ledger's compensator at time `T`, **defined** exactly as in
`SwarmOcc.sum_drift_bound`:
`Q_T = Z_T - Z_0 + sum_{t<T} J_{t+1} - sum_{t<T} E_t`.  It is not asserted to be a martingale,
nor bounded; those are the remaining stochastic inputs. -/
noncomputable def Qcomp (p : ℝ) (m : ℕ) (eps : ℝ) (α : ℕ → Array N → ℝ) (i j : Fin N)
    (U : Array N) (T : ℕ) : ℝ :=
  Zpot p m eps i j U T - Zpot p m eps i j U 0
    + (∑ t ∈ Finset.range T, Jcorr p m eps i j U t)
    - (∑ t ∈ Finset.range T, Edrift p m eps α i j U t)

/-- **No hidden compensation**: the compensator is literally the partial sum of the one-step
differences `xi_t = Z_{t+1} - Z_t + J_{t+1} - E_t`. -/
theorem Qcomp_eq_sum_increments (p : ℝ) (m : ℕ) (eps : ℝ) (α : ℕ → Array N → ℝ) (i j : Fin N)
    (U : Array N) (T : ℕ) :
    Qcomp p m eps α i j U T
      = ∑ t ∈ Finset.range T,
          (Zpot p m eps i j U (t + 1) - Zpot p m eps i j U t + Jcorr p m eps i j U t
            - Edrift p m eps α i j U t) := by
  rw [Qcomp, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_range_sub]

/-- **The finite-time ledger (pointwise in the array).**  From the one-step bounds
`1{0 <= X_t <= M_t} - eps <= E_t` for every `t < T`, the summed occupation count obeys

    sum_{t<T} 1{0 <= X_t^i <= M_t^j} <= eps T + (Z_T - Z_0) + sum_{t<T} J_{t+1} - Q_T .

This is `SwarmOcc.sum_drift_bound` instantiated at the paper's objects; the `J` of that theorem is
`t : Jcorr (t-1)` so that `J (t+1) = J_{t+1}`. -/
theorem ledger_pointwise (p : ℝ) (m : ℕ) (eps : ℝ) (α : ℕ → Array N → ℝ) (i j : Fin N)
    (U : Array N)
    (hE : ∀ t : ℕ,
      SwarmOcc.occInd (fun s => (trajectory p m U s).pos i) (fun s => runMax p m U j s) t - eps
        ≤ Edrift p m eps α i j U t) (T : ℕ) :
    ∑ t ∈ Finset.range T,
        SwarmOcc.occInd (fun s => (trajectory p m U s).pos i) (fun s => runMax p m U j s) t
      ≤ eps * (T : ℝ) + (Zpot p m eps i j U T - Zpot p m eps i j U 0)
        + (∑ t ∈ Finset.range T, Jcorr p m eps i j U t) - Qcomp p m eps α i j U T := by
  have h := SwarmOcc.sum_drift_bound
    (Z := fun n => Zpot p m eps i j U n) (E := fun n => Edrift p m eps α i j U n)
    (J := fun n => Jcorr p m eps i j U (n - 1)) (Q := fun n => Qcomp p m eps α i j U n)
    (ε := eps)
    (ind := fun n => SwarmOcc.occInd (fun s => (trajectory p m U s).pos i)
      (fun s => runMax p m U j s) n)
    hE (fun n => by rw [Qcomp]; simp only [Nat.succ_sub_one]) T
  simpa only [Nat.succ_sub_one] using h

/-- **The finite-time ledger, a.e. on the array.**  The one-step pointwise `enlFilt` bounds of
Directions A/B (explicit hypothesis `hAB`) give, for every fixed `T`, the paper's summed
inequality with the exact compensator `Qcomp`. -/
theorem occupation_ledger {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} {i j : Fin N}
    {eps : ℝ} {α : ℕ → Array N → ℝ} (hε : 0 < eps) (hα : ∀ t U, 1 / 2 ≤ α t U)
    (hAB : ∀ n, Budget.paperWeight p m n i j
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j))
    (T : ℕ) :
    (fun U : Array N => ∑ t ∈ Finset.range T,
        SwarmOcc.occInd (fun s => (trajectory p m U s).pos i) (fun s => runMax p m U j s) t)
      ≤ᵐ[arrayMeasure N] fun U =>
        eps * (T : ℝ) + (Zpot p m eps i j U T - Zpot p m eps i j U 0)
          + (∑ t ∈ Finset.range T, Jcorr p m eps i j U t) - Qcomp p m eps α i j U T := by
  filter_upwards [oneStep_all hp0 hp1 hε hα hAB] with U hU
  exact ledger_pointwise p m eps α i j U hU T

/-! ## 5. The compensator identification, reduced to the correction drift

`E_t` was *defined* from the `Hpot` drift.  The identification
`E_t = condExp (enlFilt t) (Z_{t+1} - Z_t + J_{t+1})` -- which is what makes `Q` the centred
compensator of the paper -- reduces, by `Zpot_add_J` and linearity of `condExp`, to the
single correction-drift identity `condExp (enlFilt t) (Cinc t) = corrDrift`.  That identity is
discharged in `CorrectionDrift.lean`; here it is an explicit hypothesis. -/

/-- **The compensator identification modulo the correction drift.** -/
theorem compensator_of_correction {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {i j : Fin N} {eps : ℝ} {α : ℕ → Array N → ℝ}
    (hCint : ∀ t, Integrable (fun U => Cinc p m eps i j U t) (arrayMeasure N))
    (hCorr : ∀ t, condExp (enlFilt p m t) (arrayMeasure N)
        (fun U => Cinc p m eps i j U t)
      =ᵐ[arrayMeasure N] fun U => corrDrift (aRec p m) eps (α t U) (bRec p m t j U)
        ((trajectory p m U t).pos i - runMax p m U j t)) :
    ∀ t, condExp (enlFilt p m t) (arrayMeasure N)
        (fun U => Zpot p m eps i j U (t + 1) - Zpot p m eps i j U t + Jcorr p m eps i j U t)
      =ᵐ[arrayMeasure N] fun U => Edrift p m eps α i j U t := by
  intro t
  have hpne : p ≠ 0 := by linarith
  have hle : enlFilt p m t ≤ (inferInstance : MeasurableSpace (Array N)) := (enlFilt p m).le t
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  refine (condExp_congr_ae (μ := arrayMeasure N) (m := enlFilt p m t)
    (f := fun U => Zpot p m eps i j U (t + 1) - Zpot p m eps i j U t + Jcorr p m eps i j U t)
    (g := (fun U => HpotInc p m t i j U) - fun U => Cinc p m eps i j U t)
    (Filter.Eventually.of_forall fun U => ?_)).trans ?_
  · simpa only [Pi.sub_apply] using Zpot_add_J p m eps i j U t
  refine (condExp_sub (Budget.integrable_HpotInc (N := N) (p := p) hp0 hp1 hpne m t i j)
    (hCint t) (enlFilt p m t)).trans ?_
  filter_upwards [hCorr t] with U hU
  simp only [Pi.sub_apply, Edrift]
  rw [hU]

/-! ## 6. Time aggregation at the integral (mean) level

This route uses only the integrated unconditional one-step budget
`DischargeInputs.integral_HpotInc_ge_paperWeight_discharged`; it needs no pointwise `enlFilt`
bound, no compensator and no `Q`.  It produces the paper's occupation count at expectation
level, with the paper's loss term `sum_t int b_t a^{(X_t - M_t)}` carried explicitly. -/

/-- **The loss term on the finite offset partition**: below the record it vanishes, and on the
above-record piece `A_g` it is `b_n a^g`.  This is the exact expense ledger
`sum_g int b_t a^{(X_t-M_t)} = sum_{t<T} sum_g int_{A_g(t)} b_t a^g` of the mean-level estimate,
and it makes the loss term visibly a finite sum of measurable, bounded pieces. -/
theorem lossTerm_eq_sum_pieces (p : ℝ) (m n : ℕ) (i j : Fin N) (U : Array N) :
    lossTerm p m n i j U
      = ∑ g ∈ Finset.range (n + 1),
          (abovePosSet p m n i j g).indicator (fun U => bRec p m n j U * aRec p m ^ g) U := by
  classical
  by_cases hU : U ∈ Budget.belowSet p m n i j
  · have hlt : (trajectory p m U n).pos i < runMax p m U j n :=
      (Budget.mem_belowSet_iff_lt p m n i j U).mp hU
    have hnot : ¬ runMax p m U j n ≤ (trajectory p m U n).pos i := not_le.mpr hlt
    rw [lossTerm, if_neg hnot]
    have hzero : ∀ g ∈ Finset.range (n + 1),
        (abovePosSet p m n i j g).indicator (fun U => bRec p m n j U * aRec p m ^ g) U = 0 := by
      intro g hg
      exact Set.indicator_of_notMem (f := fun U => bRec p m n j U * aRec p m ^ g) (fun h =>
        (Set.disjoint_left.mp (Budget.disjoint_belowSet_abovePosSet p m n i j hg)) hU h)
    rw [Finset.sum_eq_zero hzero, mul_zero]
  · obtain ⟨g₀, hg₀, hmem₀⟩ := Budget.exists_abovePosSet_of_notMem_belowSet p m n i j hU
    have hposEq : (trajectory p m U n).pos i = runMax p m U j n + (g₀ : ℤ) :=
      (abovePosSet_traj_iff p m n i j g₀ U).mp hmem₀
    have hge : runMax p m U j n ≤ (trajectory p m U n).pos i := by
      have hnn : (0 : ℤ) ≤ (g₀ : ℤ) := by exact_mod_cast Nat.zero_le g₀
      linarith
    have hsingle : ∑ g ∈ Finset.range (n + 1),
        (abovePosSet p m n i j g).indicator (fun U => bRec p m n j U * aRec p m ^ g) U
        = (abovePosSet p m n i j g₀).indicator
            (fun U => bRec p m n j U * aRec p m ^ g₀) U := by
      refine Finset.sum_eq_single (s := Finset.range (n + 1))
        (f := fun g => (abovePosSet p m n i j g).indicator
          (fun U => bRec p m n j U * aRec p m ^ g) U) g₀ ?_ ?_
      · intro b _ hne
        exact Set.indicator_of_notMem (f := fun U => bRec p m n j U * aRec p m ^ b) (fun h =>
          (Set.disjoint_left.mp (Budget.disjoint_abovePosSet p m n i j hne)) h hmem₀)
      · intro hcon
        exact absurd (Finset.mem_range.mpr hg₀) hcon
    rw [hsingle, Set.indicator_of_mem hmem₀, lossTerm, if_pos hge]
    congr 1
    have hgap : (trajectory p m U n).pos i - runMax p m U j n = (g₀ : ℤ) := by
      rw [hposEq]; ring
    rw [hgap, Int.toNat_natCast]

/-- The loss term is integrable: its piecewise form is a finite sum of bounded pieces. -/
theorem integrable_lossTerm {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m n : ℕ)
    (i j : Fin N) : Integrable (lossTerm p m n i j) (arrayMeasure N) := by
  have hsum : Integrable (fun U : Array N => ∑ g ∈ Finset.range (n + 1),
      (abovePosSet p m n i j g).indicator (fun U => bRec p m n j U * aRec p m ^ g) U)
      (arrayMeasure N) := by
    refine integrable_finsetSum _ (fun g _ => ?_)
    exact ((Budget.integrable_bRec_w hp0 hp1 m n j).mul_const (aRec p m ^ g)).indicator
      (Budget.measurableSet_abovePosSet_w p m n i j g)
  exact hsum.congr (Filter.Eventually.of_forall fun U =>
    (lossTerm_eq_sum_pieces p m n i j U).symm)

/-- The loss term is bounded by `b_n <= 2n+5` (`abs_HprevAt_le`), uniformly in the array. -/
theorem abs_lossTerm_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m n : ℕ)
    (i j : Fin N) (U : Array N) :
    |lossTerm p m n i j U| ≤ 2 * (n : ℝ) + 5 := by
  have ha0 : (0 : ℝ) ≤ aRec p m := zero_le_aRec hp0 hp1 m
  have ha1 : aRec p m ≤ 1 := le_of_lt (aRec_lt_one hp0 hp1 m)
  have hfac0 : (0 : ℝ) ≤ if runMax p m U j n ≤ (trajectory p m U n).pos i then
      aRec p m ^ ((trajectory p m U n).pos i - runMax p m U j n).toNat else 0 := by
    split_ifs
    · exact pow_nonneg ha0 _
    · exact le_rfl
  have hfac1 : (if runMax p m U j n ≤ (trajectory p m U n).pos i then
      aRec p m ^ ((trajectory p m U n).pos i - runMax p m U j n).toNat else 0) ≤ 1 := by
    split_ifs
    · exact pow_le_one₀ ha0 ha1
    · norm_num
  have hb1 : bRec p m n j U ≤ 2 * (n : ℝ) + 5 := by
    have h := abs_HprevAt_le hp0 hp1 m n j U
    have h2 : HprevAt p m n j U ≤ 2 * (n : ℝ) + 3 := (abs_le.mp h).2
    simp only [bRec]
    linarith
  have hb0 : (0 : ℝ) ≤ bRec p m n j U := by
    have h3 := three_le_bRec hp0 hp1 m n j U
    linarith
  rw [lossTerm, abs_of_nonneg (mul_nonneg hb0 hfac0)]
  nlinarith

/-- **The time-aggregated *integral* budget.**  Summing the unconditional one-step budget
`int paperWeight_t <= int HpotInc_t` over `t < T` and telescoping the potential gives

    sum_{t<T} int paperWeight_t <= int (H_{j,T}(X_T^i) - H_{j,0}(X_0^i)),

and hence, splitting `paperWeight = gain - loss`,

    sum_{t<T} E[1{0 <= X_t^i <= M_t^j}]
      <= sum_{t<T} int b_t a^{(X_t - M_t)} 1{M_t <= X_t} + int (H_T - H_0).

At expectation level this is the paper's occupation bound with the loss term carried explicitly
and no use of `Q`.  (The remaining content -- that the loss sum and the potential are `O(M_T)` or
`o(T)` -- is `(Jbound)`/`(Vbound)`, not claimed here.) -/
theorem sum_gain_le_loss_telescope {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) {i j : Fin N} (hij : i ≠ j) (T : ℕ) :
    (∑ t ∈ Finset.range T, ∫ U, gainInd p m t i j U ∂(arrayMeasure N))
      ≤ (∑ t ∈ Finset.range T, ∫ U, lossTerm p m t i j U ∂(arrayMeasure N))
        + ∫ U, (SwarmOcc.Hpot (envH p m j U) ((trajectory p m U T).pos i)
            - SwarmOcc.Hpot (envH p m j U) ((trajectory p m U 0).pos i))
            ∂(arrayMeasure N) := by
  have hpne : p ≠ 0 := by linarith
  have hstep : ∀ t ∈ Finset.range T,
      (∫ U, gainInd p m t i j U ∂(arrayMeasure N))
        ≤ (∫ U, HpotInc p m t i j U ∂(arrayMeasure N))
          + ∫ U, lossTerm p m t i j U ∂(arrayMeasure N) := by
    intro t _
    have hsplit : (∫ U, gainInd p m t i j U ∂(arrayMeasure N))
        = (∫ U, Budget.paperWeight p m t i j U ∂(arrayMeasure N))
          + ∫ U, lossTerm p m t i j U ∂(arrayMeasure N) := by
      rw [← integral_add (Budget.integrable_paperWeight_w hp0 hp1 m t i j)
        (integrable_lossTerm hp0 hp1 m t i j)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun U => by
        have h := paperWeight_eq_gain_sub_loss p m t i j U
        linarith)
    rw [hsplit]
    have h := Budget.integral_HpotInc_ge_paperWeight_discharged (N := N) p hp0 hp1 hm hij
      (n := t)
    linarith
  have hsum : (∑ t ∈ Finset.range T, ∫ U, HpotInc p m t i j U ∂(arrayMeasure N))
      = ∫ U, (SwarmOcc.Hpot (envH p m j U) ((trajectory p m U T).pos i)
          - SwarmOcc.Hpot (envH p m j U) ((trajectory p m U 0).pos i))
          ∂(arrayMeasure N) := by
    rw [← integral_finsetSum]
    · exact integral_congr_ae (Filter.Eventually.of_forall fun U => sum_HpotInc p m i j U T)
    · intro t _
      exact Budget.integrable_HpotInc (N := N) (p := p) hp0 hp1 hpne m t i j
  have hmain := Finset.sum_le_sum hstep
  rw [Finset.sum_add_distrib, hsum] at hmain
  simpa only [add_comm] using hmain

end VdriftAssembly
end Swarming.Enl
