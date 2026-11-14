/-
# `(locmove)`: the one-step drift of the group maximum `max_{j∈Aᶜ} H_n^A(X_n^j)`

The paper's proof of `(locmove)` (Proposition `local`) needs the following step, which is
*not* in the tree: at a time `n` satisfying `(sep)` with `I = A`, `J = Aᶜ`,

`E[ max_{j∈Aᶜ} H_{n+1}^A(X_{n+1}^j) - max_{j∈Aᶜ} H_n^A(X_n^j) | F_n ] ≥ 1`.

It is what produces the `-(t-s)` term, and it is the only place in `(locmove)` where the
maximum over the separated group enters with a *positive* drift (the `Γ_y^A` trials later
produce the competing `-(R_t^A - R_s^A)` term).

The proof is short but genuinely nonelementary in the bookkeeping, and it is where the two
halves of `SepGroup`/`WdriftJoint` meet:

* for each single walker `j`, `condExp_indicator_HA_next` gives the exact conditional mean
  `1 + corr` of `H^A(X^j)` at the next step, and on `(sep)` with `j ∈ J` the correction is
  `corr ≥ 0` (`wA_le_rightProbability_of_J`), i.e. every walker's potential grows by at
  least `1` in conditional mean;
* the maximum is handled by `mnow_add_one_le_cmax` (the maximum of the per-walker means is at
  least `max + 1`) together with `condExp_indicator_Mnext_ge`
  (`1_{A₀} max_j E[·|F_n] ≤ᵐ E[1_{A₀} max_j ·|F_n]`).

Here we finish the a.e. algebra that both files leave open: the `F_n`-measurable factor
`max_j H_n^A(X_n^j)` is pulled out of the conditional expectation, so that

`1_{A₀} ≤ᵐ E[ 1_{A₀} (max_j H_n^A(X_{n+1}^j) - max_j H_n^A(X_n^j)) | F_n ]`

for every `F_n`-measurable `A₀ ⊆ {sep}`.  The two arithmetic combinations, the pull-out of
the maximum, and the `Cmax`/`Mnow` bookkeeping are `maxHA_drift_ge_one_aux` below.

Scope, stated exactly: this is the *conditional-mean* half of `(locmove)`.
The passage to the pathwise display `max H_t^A - max H_s^A ≥ (t-s) - C_T L^{3/4}` needs the
maximal Hoeffding–Azuma inequality for the martingale part with the `(locmax)`/`(hcomp)`
increment bound, which is absent from the tree (and from Mathlib); see `NOTES.md`.
-/
import Swarm.WdriftJoint

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace LocMove

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift

variable {N : ℕ}

/-! ## 1. Pulling the `F_n`-measurable maximum out of the conditional expectation -/

/-- `1_{A₀} max_{j∈J} H_n^{Jᶜ}(X_n^j)` is `F_n`-strongly measurable, hence its own
conditional expectation. -/
theorem condExp_indicator_Mnow_eq (p : ℝ) (m n : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty)
    {A₀ : Set (Array N)} (hA₀ : MeasurableSet[posFilt N p m n] A₀)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) :
    condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => A₀.indicator (Mnow p m n J hJ) U)
    =ᵐ[arrayMeasure N] fun U => A₀.indicator (Mnow p m n J hJ) U := by
  have hle := (posFilt N p m).le n
  haveI hsig : SigmaFinite ((arrayMeasure N).trim hle) := inferInstance
  have hstrong : StronglyMeasurable[posFilt N p m n]
      (fun U => A₀.indicator (Mnow p m n J hJ) U) :=
    ((measurable_Mnow_posFilt p m n J hJ).indicator hA₀).stronglyMeasurable
  have hint : Integrable (fun U => A₀.indicator (Mnow p m n J hJ) U) (arrayMeasure N) :=
    (integrable_Mnow hp hp1 m n J hJ).indicator (hle A₀ hA₀)
  exact Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable hle hstrong hint)

/-! ## 2. The one-step maximum drift `≥ 1` -/

/-- **`(locmove)`, one step: the maximum over `Aᶜ` of the group potential `H^A` grows by at
least `1` in conditional mean on `(sep)`.**

With `J = Aᶜ` (so that `H^A = H^{Jᶜ}`), for every `F_n`-measurable `A₀ ⊆ {sep}`:

`1_{A₀} ≤ᵐ E[ 1_{A₀} (max_{j∈J} H_n^A(X_{n+1}^j) - max_{j∈J} H_n^A(X_n^j)) | F_n ]`.

Both maxima are taken with the *time-`n`* weights `w_n^A`, which is exactly the comparison
the paper uses before invoking `H_{n+1}^A(X_{n+1}^j) = H_n^A(X_{n+1}^j)` for `j ∈ Aᶜ`.
`LocMoveWeight.HA_succ_eq_of_sep` proves that identity.  Separation supplies only a non-strict
position inequality at time `n+1`; the argument works because the potential is a prefix sum of
weights, so weight changes at the endpoint itself do not affect it. -/
theorem condExp_indicator_Mnext_sub_Mnow_ge_one
    {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m n : ℕ)
    (J : Finset (Fin N)) (hJ : J.Nonempty)
    {A₀ : Set (Array N)} (hA₀ : MeasurableSet[posFilt N p m n] A₀)
    (hsub : A₀ ⊆ {U | SepSet p m n Jᶜ J U}) :
    (fun U => A₀.indicator (fun _ => (1 : ℝ)) U) ≤ᵐ[arrayMeasure N]
      condExp (posFilt N p m n) (arrayMeasure N)
        (fun U => A₀.indicator (fun U => Mnext p m n J hJ U - Mnow p m n J hJ U) U) := by
  classical
  have hp : 1 / 2 ≤ p := le_of_lt hp0
  have hp1' : p ≤ 1 := le_of_lt hp1
  have hprob := arrayMeasure_isProbabilityMeasure N
  haveI := hprob
  have hle := (posFilt N p m).le n
  have hA₀m : MeasurableSet A₀ := hle A₀ hA₀
  -- (i) `1_{A₀} (max H_n + 1) ≤ 1_{A₀} Cmax`, pointwise.
  have hstep : (fun U => A₀.indicator (fun U => Mnow p m n J hJ U + 1) U)
      ≤ᵐ[arrayMeasure N] fun U => A₀.indicator (Cmax p m n J hJ) U := by
    refine Filter.Eventually.of_forall fun U => ?_
    by_cases hU : U ∈ A₀
    · simp only [Set.indicator_of_mem hU]
      exact mnow_add_one_le_cmax hp hp1' m n U J hJ (fun j => (hsub hU).1 j)
    · simpa only [Set.indicator_of_notMem hU] using (le_refl (0 : ℝ))
  -- (ii) `1_{A₀} Cmax ≤ᵐ E[1_{A₀} max H_{n+1}|F_n]`.
  have hge := condExp_indicator_Mnext_ge hp0 hp1 m n Jᶜ J hJ hA₀ hsub
  -- (iii) combine.
  have hmain : (fun U => A₀.indicator (fun U => Mnow p m n J hJ U + 1) U)
      ≤ᵐ[arrayMeasure N]
      condExp (posFilt N p m n) (arrayMeasure N)
        (fun U => A₀.indicator (Mnext p m n J hJ) U) := hstep.trans hge
  -- (iv) pull out the `F_n`-measurable maximum at time `n`.
  have hnow := condExp_indicator_Mnow_eq p m n J hJ hA₀ hp hp1'
  -- (v) split the conditional expectation of the difference.
  have hintN : Integrable (fun U => A₀.indicator (Mnext p m n J hJ) U) (arrayMeasure N) :=
    (integrable_Mnext hp hp1' m n J hJ).indicator hA₀m
  have hintW : Integrable (fun U => A₀.indicator (Mnow p m n J hJ) U) (arrayMeasure N) :=
    (integrable_Mnow hp hp1' m n J hJ).indicator hA₀m
  have hsplit : condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => A₀.indicator (fun U => Mnext p m n J hJ U - Mnow p m n J hJ U) U)
      =ᵐ[arrayMeasure N]
      condExp (posFilt N p m n) (arrayMeasure N)
          (fun U => A₀.indicator (Mnext p m n J hJ) U)
        - condExp (posFilt N p m n) (arrayMeasure N)
            (fun U => A₀.indicator (Mnow p m n J hJ) U) := by
    have heq : (fun U => A₀.indicator
        (fun U => Mnext p m n J hJ U - Mnow p m n J hJ U) U)
        = (fun U => A₀.indicator (Mnext p m n J hJ) U)
          - (fun U => A₀.indicator (Mnow p m n J hJ) U) := by
      funext U
      simp only [Pi.sub_apply]
      by_cases hU : U ∈ A₀
      · simp only [Set.indicator_of_mem hU]
      · simp only [Set.indicator_of_notMem hU, sub_zero]
    rw [heq]
    exact condExp_sub hintN hintW _
  -- (vi) pointwise finish.
  have hfin : ∀ᵐ U ∂(arrayMeasure N),
      A₀.indicator (fun U => Mnow p m n J hJ U + 1) U
          ≤ condExp (posFilt N p m n) (arrayMeasure N)
            (fun U => A₀.indicator (Mnext p m n J hJ) U) U
      ∧ A₀.indicator (Mnow p m n J hJ) U
          = condExp (posFilt N p m n) (arrayMeasure N)
            (fun U => A₀.indicator (Mnow p m n J hJ) U) U
      ∧ condExp (posFilt N p m n) (arrayMeasure N)
            (fun U => A₀.indicator (fun U => Mnext p m n J hJ U - Mnow p m n J hJ U) U) U
          = condExp (posFilt N p m n) (arrayMeasure N)
              (fun U => A₀.indicator (Mnext p m n J hJ) U) U
            - condExp (posFilt N p m n) (arrayMeasure N)
              (fun U => A₀.indicator (Mnow p m n J hJ) U) U := by
    filter_upwards [hmain, hnow, hsplit] with U h1 h2 h3
    exact ⟨h1, h2.symm, h3⟩
  filter_upwards [hfin] with U hU
  obtain ⟨h1, h2, h3⟩ := hU
  simp only [h3, ← h2]
  by_cases hUm : U ∈ A₀
  · have h1' : Mnow p m n J hJ U + 1
        ≤ condExp (posFilt N p m n) (arrayMeasure N)
            (fun U => A₀.indicator (Mnext p m n J hJ) U) U := by
      simpa only [Set.indicator_of_mem hUm] using h1
    simp only [Set.indicator_of_mem hUm]
    linarith
  · have h1' : (0 : ℝ) ≤ condExp (posFilt N p m n) (arrayMeasure N)
        (fun U => A₀.indicator (Mnext p m n J hJ) U) U := by
      simpa only [Set.indicator_of_notMem hUm] using h1
    simp only [Set.indicator_of_notMem hUm]
    linarith

/-! ## 3. The separation event itself as `A₀` -/

/-- The same statement with `A₀` the full separation event. -/
theorem condExp_Mnext_sub_Mnow_ge_one_sep
    {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m n : ℕ)
    (J : Finset (Fin N)) (hJ : J.Nonempty) :
    (fun U => ({U | SepSet p m n Jᶜ J U} : Set (Array N)).indicator (fun _ => (1 : ℝ)) U)
      ≤ᵐ[arrayMeasure N]
      condExp (posFilt N p m n) (arrayMeasure N)
        (fun U => ({U | SepSet p m n Jᶜ J U} : Set (Array N)).indicator
          (fun U => Mnext p m n J hJ U - Mnow p m n J hJ U) U) :=
  condExp_indicator_Mnext_sub_Mnow_ge_one hp0 hp1 m n J hJ
    (measurableSet_sepSet p m n Jᶜ J) (fun _ h => h)

/-- Integrated form: the expected growth of the separated-group maximum over one step is at
least the probability of `(sep)`. -/
theorem integral_Mnext_sub_Mnow_ge_prob_sep
    {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m n : ℕ)
    (J : Finset (Fin N)) (hJ : J.Nonempty) :
    (arrayMeasure N).real {U | SepSet p m n Jᶜ J U}
      ≤ ∫ U, ({U | SepSet p m n Jᶜ J U} : Set (Array N)).indicator
          (fun U => Mnext p m n J hJ U - Mnow p m n J hJ U) U ∂(arrayMeasure N) := by
  have hp : 1 / 2 ≤ p := le_of_lt hp0
  have hp1' : p ≤ 1 := le_of_lt hp1
  have hprob := arrayMeasure_isProbabilityMeasure N
  haveI := hprob
  have hle := (posFilt N p m).le n
  have hmeas := measurableSet_sepSet p m n Jᶜ J
  have hstep := condExp_Mnext_sub_Mnow_ge_one_sep hp0 hp1 m n J hJ
  have hintN : Integrable (fun U => ({U | SepSet p m n Jᶜ J U} : Set (Array N)).indicator
      (Mnext p m n J hJ) U) (arrayMeasure N) :=
    (integrable_Mnext hp hp1' m n J hJ).indicator (hle _ hmeas)
  have hintW : Integrable (fun U => ({U | SepSet p m n Jᶜ J U} : Set (Array N)).indicator
      (Mnow p m n J hJ) U) (arrayMeasure N) :=
    (integrable_Mnow hp hp1' m n J hJ).indicator (hle _ hmeas)
  have hint : Integrable (fun U => ({U | SepSet p m n Jᶜ J U} : Set (Array N)).indicator
      (fun U => Mnext p m n J hJ U - Mnow p m n J hJ U) U) (arrayMeasure N) :=
    (hintN.sub hintW).congr (Filter.Eventually.of_forall fun U => by
      by_cases hU : U ∈ {U : Array N | SepSet p m n Jᶜ J U}
      · simp only [Set.indicator_of_mem hU, Pi.sub_apply]
      · simp only [Set.indicator_of_notMem hU, Pi.sub_apply, sub_self])
  have hce : ∫ U, condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => ({U | SepSet p m n Jᶜ J U} : Set (Array N)).indicator
        (fun U => Mnext p m n J hJ U - Mnow p m n J hJ U) U) U ∂(arrayMeasure N)
      = ∫ U, ({U | SepSet p m n Jᶜ J U} : Set (Array N)).indicator
        (fun U => Mnext p m n J hJ U - Mnow p m n J hJ U) U ∂(arrayMeasure N) :=
    integral_condExp hle
  have hcondint : Integrable (fun U => condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => ({U | SepSet p m n Jᶜ J U} : Set (Array N)).indicator
        (fun U => Mnext p m n J hJ U - Mnow p m n J hJ U) U) U) (arrayMeasure N) := by
    haveI := hint
    exact integrable_condExp
  have hind : ∫ U, ({U | SepSet p m n Jᶜ J U} : Set (Array N)).indicator
      (fun _ => (1 : ℝ)) U ∂(arrayMeasure N) = (arrayMeasure N).real {U | SepSet p m n Jᶜ J U} := by
    exact integral_indicator_one (hle _ hmeas)
  have hmono : ∫ U, ({U | SepSet p m n Jᶜ J U} : Set (Array N)).indicator
      (fun _ => (1 : ℝ)) U ∂(arrayMeasure N)
      ≤ ∫ U, condExp (posFilt N p m n) (arrayMeasure N)
        (fun U => ({U | SepSet p m n Jᶜ J U} : Set (Array N)).indicator
          (fun U => Mnext p m n J hJ U - Mnow p m n J hJ U) U) U ∂(arrayMeasure N) := by
    refine integral_mono_ae ?_ hcondint hstep
    exact (integrable_const 1).indicator (hle _ hmeas)
  rw [hce, hind] at hmono
  exact hmono


/-! ## 4. The window sum: strict times versus the rest -/

/-- Integrated over a window: the expected growth of the separated-group maximum over `[s,t)`
is at least the sum, over the times of the window, of the probabilities of `(sep)`. -/
theorem sum_integral_growth_ge {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ)
    (J : Finset (Fin N)) (hJ : J.Nonempty) (s t : ℕ) :
    ∑ n ∈ Finset.Ico s t, (arrayMeasure N).real {U | SepSet p m n Jᶜ J U}
      ≤ ∑ n ∈ Finset.Ico s t,
          ∫ U, ({U | SepSet p m n Jᶜ J U} : Set (Array N)).indicator
            (fun U => Mnext p m n J hJ U - Mnow p m n J hJ U) U ∂(arrayMeasure N) :=
  Finset.sum_le_sum fun n _ => integral_Mnext_sub_Mnow_ge_prob_sep hp0 hp1 m n J hJ

/-- **The paper's summation over the strict (`Γ_y^A`) times.**  If `a n ≤ -κ` at the strict
times `T ⊆ [s,t)` and `a n ≤ 0` at every other time of the window, then

`∑_{n∈[s,t)} a n ≤ -κ |T|`.

This is the step "at every other time we apply `(Wdrift)`" of the proof of `(locmove)`, with
`a n` the conditional mean of `W_{n+1}^{A,Aᶜ} - W_n^{A,Aᶜ}` at time `n`. -/
theorem sum_Ico_le_of_strict_card {s t : ℕ} {a : ℕ → ℝ} {T : Finset ℕ} {κ : ℝ}
    (hTsub : T ⊆ Finset.Ico s t)
    (hstrict : ∀ n ∈ T, a n ≤ -κ)
    (hother : ∀ n ∈ Finset.Ico s t, n ∉ T → a n ≤ 0) :
    ∑ n ∈ Finset.Ico s t, a n ≤ -κ * (T.card : ℝ) := by
  classical
  have hsplit : (∑ n ∈ Finset.Ico s t, a n)
      = (∑ n ∈ T, a n) + ∑ n ∈ Finset.Ico s t \ T, a n := by
    have h := Finset.sum_sdiff hTsub (f := a)
    linarith
  have h1 : (∑ n ∈ T, a n) ≤ ∑ n ∈ T, (-κ) := Finset.sum_le_sum hstrict
  have h2 : (∑ n ∈ Finset.Ico s t \ T, a n) ≤ 0 := by
    refine Finset.sum_nonpos fun n hn => ?_
    exact hother n (Finset.mem_sdiff.mp hn).1 (Finset.mem_sdiff.mp hn).2
  have h3 : (∑ _n ∈ T, (-κ)) = -κ * (T.card : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  linarith

/-- **Paper form**: a lower bound `κ' R - Cb` on the number of strict times in the window
turns the drift sum into `-(κ κ') R + κ Cb`; the error term carries the *positive* constant
`κ`, which is where the `C_T L^{3/4}` of `(locmove)` enters. -/
theorem sum_Ico_le_of_strict_lower {s t : ℕ} {a : ℕ → ℝ} {T : Finset ℕ} {κ κ' R Cb : ℝ}
    (hκ : 0 ≤ κ) (hTsub : T ⊆ Finset.Ico s t)
    (hstrict : ∀ n ∈ T, a n ≤ -κ)
    (hother : ∀ n ∈ Finset.Ico s t, n ∉ T → a n ≤ 0)
    (hcard : κ' * R - Cb ≤ (T.card : ℝ)) :
    ∑ n ∈ Finset.Ico s t, a n ≤ -(κ * κ') * R + κ * Cb := by
  have h := sum_Ico_le_of_strict_card hTsub hstrict hother
  nlinarith

/-! ## 5. The paper's final convex combination -/

/-- **The last step of the proof of `(locmove)`.**  Two bounds on the same quantity `x`,

`x ≤ C R + C R₀ - Δ + E`  (from the `H^A`-drift, with `R = R_t^A - R_s^A`, `R₀ = R_s^A -
min_{i∈A} X_s^i`, `Δ = t - s`)

`x ≤ -R/C + E'`  (from the `Γ_y^A` trials),

combine with weights `1/(1+C²)` and `C²/(1+C²)` so that the `R` coefficient cancels *exactly*:
`x ≤ C/(1+C²) R₀ - Δ/(1+C²) + max E E'`.  Since `C ≥ 1` gives `C/(1+C²) ≤ 1`, replacing `C`
by `1 + C²` recovers the display `(locmove)` with a coefficient independent of `T`. -/
theorem convex_combine {C x R R₀ Δ E E' : ℝ} (hC1 : 1 ≤ C)
    (h₁ : x ≤ C * R + C * R₀ - Δ + E) (h₂ : x ≤ -R / C + E') :
    x ≤ C / (1 + C ^ 2) * R₀ - Δ / (1 + C ^ 2) + max E E' := by
  have hCpos : 0 < C := by linarith
  have hden : 0 < 1 + C ^ 2 := by positivity
  have hw1 : 0 ≤ 1 / (1 + C ^ 2) := by positivity
  have hw2 : 0 ≤ C ^ 2 / (1 + C ^ 2) := by positivity
  have hsum : 1 / (1 + C ^ 2) + C ^ 2 / (1 + C ^ 2) = 1 := by
    field_simp
  have hx : x = 1 / (1 + C ^ 2) * x + C ^ 2 / (1 + C ^ 2) * x := by
    rw [← add_mul, hsum, one_mul]
  have step1 : 1 / (1 + C ^ 2) * x ≤ 1 / (1 + C ^ 2) * (C * R + C * R₀ - Δ + E) :=
    mul_le_mul_of_nonneg_left h₁ hw1
  have step2 : C ^ 2 / (1 + C ^ 2) * x ≤ C ^ 2 / (1 + C ^ 2) * (-R / C + E') :=
    mul_le_mul_of_nonneg_left h₂ hw2
  have hE : 1 / (1 + C ^ 2) * E + C ^ 2 / (1 + C ^ 2) * E' ≤ max E E' := by
    have hA : E ≤ max E E' := le_max_left _ _
    have hB : E' ≤ max E E' := le_max_right _ _
    calc 1 / (1 + C ^ 2) * E + C ^ 2 / (1 + C ^ 2) * E'
        ≤ 1 / (1 + C ^ 2) * max E E' + C ^ 2 / (1 + C ^ 2) * max E E' :=
          add_le_add (mul_le_mul_of_nonneg_left hA hw1) (mul_le_mul_of_nonneg_left hB hw2)
      _ = max E E' := by rw [← add_mul, hsum, one_mul]
  have hcancel : 1 / (1 + C ^ 2) * (C * R) + C ^ 2 / (1 + C ^ 2) * (-R / C) = 0 := by
    field_simp
    ring
  rw [hx]
  calc 1 / (1 + C ^ 2) * x + C ^ 2 / (1 + C ^ 2) * x
      ≤ 1 / (1 + C ^ 2) * (C * R + C * R₀ - Δ + E)
        + C ^ 2 / (1 + C ^ 2) * (-R / C + E') := add_le_add step1 step2
    _ = C / (1 + C ^ 2) * R₀ - Δ / (1 + C ^ 2)
        + (1 / (1 + C ^ 2) * E + C ^ 2 / (1 + C ^ 2) * E') := by
      field_simp
      ring
    _ ≤ C / (1 + C ^ 2) * R₀ - Δ / (1 + C ^ 2) + max E E' := by linarith


/-! ## 6. The matching strict step at a `Γ`-time: conditional mean `≤ -(2p-1)/|I|` -/

/-- **The `Γ`-time half of `(locmove)`.**  At a time at which `(sep)` holds, the walker `i₀ ∈ I`
sits on a site that is excited for its own group (`w_n^{I}(X^{i₀}) = p`) but not for itself
(`α_n^{i₀} = 1/2`), and every correction of the group is nonpositive, the conditional mean of
`W_{n+1}^{I,J} - W_n^{I,J}` is at most `-(2p-1)/|I|`.

This is the quantitative form of `Cavg ≤ -(2p-1)/|I|` (`cavg_le_neg_card`) placed inside the
conditional expectation `condExp_indicator_WA_drift_le_cavg`; together with
`sum_Ico_le_of_strict_lower` it is exactly the paper's summation over the good records
`Γ_y^I`, and the only missing ingredient for the `-R_t^I + R_s^I` half of `(locmove)` is the
almost-sure lower bound on their number. -/
theorem condExp_indicator_WA_strict_le
    {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m n : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {A₀ : Set (Array N)} (hA₀ : MeasurableSet[posFilt N p m n] A₀)
    (hsub : A₀ ⊆ {U | SepSet p m n I J U})
    {i₀ : Fin N} (hi₀ : i₀ ∈ I)
    (hα : ∀ U ∈ A₀,
      rightProbability p m (trajectory p m U n).ell i₀ (X p m U n i₀) = 1 / 2)
    (hw : ∀ U ∈ A₀, wA p m U n Jᶜ (X p m U n i₀).toNat = p) :
    condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => A₀.indicator
        (fun U => WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ) U)
    ≤ᵐ[arrayMeasure N] fun U => (-(2 * p - 1) / ((I.card : ℕ) : ℝ)) *
      A₀.indicator (fun _ => (1 : ℝ)) U := by
  have hp : 1 / 2 ≤ p := le_of_lt hp0
  have hp1' : p ≤ 1 := le_of_lt hp1
  refine (condExp_indicator_WA_drift_le_cavg hp0 hp1 m n I J hI hJ hA₀ hsub).trans ?_
  refine Filter.Eventually.of_forall fun U => ?_
  by_cases hU : U ∈ A₀
  · have hsep : Sep p m U n I J := hsub hU
    have hnonpos : ∀ i ∈ I, corr p m U n Jᶜ i ≤ 0 :=
      fun i hi => corr_nonpos_of_sep hp hp1' hid hsep hi
    have hc : Cavg p m n I J U ≤ -(2 * p - 1) / ((I.card : ℕ) : ℝ) :=
      cavg_le_neg_card hp hp1' m n U I J hI hi₀ (hα U hU) (hw U hU) hnonpos
    simpa only [Set.indicator_of_mem hU, mul_one] using hc
  · simp only [Set.indicator_of_notMem hU, mul_zero, Pi.zero_apply, le_refl]

/-! ## 7. The paper's exact positive coefficient `(2p-1)(1-p)^{(2m-1)|I|}/|I|` -/

/-- The coefficient produced by the `Γ_y^I` trials is strictly positive. -/
theorem gamma_rate_pos {p : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) (I : Finset (Fin N))
    (hI : I.Nonempty) :
    0 < (2 * p - 1) * (1 - p) ^ ((2 * m - 1) * I.card) / ((I.card : ℕ) : ℝ) := by
  have h1 : 0 < 2 * p - 1 := by linarith
  have h2 : 0 < 1 - p := by linarith
  have h3 : (0 : ℝ) < (I.card : ℕ) := by exact_mod_cast Finset.card_pos.mpr hI
  exact div_pos (mul_pos h1 (pow_pos h2 _)) h3

/-- **The `-(R_t^I - R_s^I)` half of `(locmove)`, at the paper's constants.**  If the
strict (excited) times of the window number at least `(1-p)^{(2m-1)|I|} R - Cb`, then the
drift sum is at most `-(2p-1)(1-p)^{(2m-1)|I|} R/|I| + (2p-1) Cb/|I|`.  Taking `R = R_t^I - R_s^I`
and `Cb = 4m L^{3/4}` this is the paper's estimate, whose coefficient
`(2p-1)(1-p)^{(2m-1)|I|}/|I| ≥ (2p-1)(1-p)^{(2m-1)(N-1)}/(N-1) > 0` is independent of `T`. -/
theorem sum_Ico_le_gamma_rate {p : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (m : ℕ)
    (I : Finset (Fin N)) (hI : I.Nonempty)
    {s t : ℕ} {a : ℕ → ℝ} {T : Finset ℕ} {R Cb : ℝ}
    (hTsub : T ⊆ Finset.Ico s t)
    (hstrict : ∀ n ∈ T, a n ≤ -(2 * p - 1) / ((I.card : ℕ) : ℝ))
    (hother : ∀ n ∈ Finset.Ico s t, n ∉ T → a n ≤ 0)
    (hcard : (1 - p) ^ ((2 * m - 1) * I.card) * R - Cb ≤ (T.card : ℝ)) :
    ∑ n ∈ Finset.Ico s t, a n
      ≤ -((2 * p - 1) * (1 - p) ^ ((2 * m - 1) * I.card) / ((I.card : ℕ) : ℝ)) * R
        + (2 * p - 1) / ((I.card : ℕ) : ℝ) * Cb := by
  have hcard_pos : (0 : ℝ) < (I.card : ℕ) := by exact_mod_cast Finset.card_pos.mpr hI
  have hκ : (0 : ℝ) ≤ (2 * p - 1) / ((I.card : ℕ) : ℝ) :=
    div_nonneg (by linarith) (le_of_lt hcard_pos)
  have hstrict' : ∀ n ∈ T, a n ≤ -((2 * p - 1) / ((I.card : ℕ) : ℝ)) :=
    fun n hn => by simpa only [neg_div] using hstrict n hn
  have h := sum_Ico_le_of_strict_lower (κ := (2 * p - 1) / ((I.card : ℕ) : ℝ))
    (κ' := (1 - p) ^ ((2 * m - 1) * I.card)) hκ hTsub hstrict' hother hcard
  calc ∑ n ∈ Finset.Ico s t, a n
      ≤ -((2 * p - 1) / ((I.card : ℕ) : ℝ) * (1 - p) ^ ((2 * m - 1) * I.card)) * R
        + (2 * p - 1) / ((I.card : ℕ) : ℝ) * Cb := h
    _ = -((2 * p - 1) * (1 - p) ^ ((2 * m - 1) * I.card) / ((I.card : ℕ) : ℝ)) * R
        + (2 * p - 1) / ((I.card : ℕ) : ℝ) * Cb := by ring

end LocMove
