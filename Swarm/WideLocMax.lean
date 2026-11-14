/-
# The wide harmonic `(locmax)` bound with independent spatial margins

The integrated `(locmax)` inputs

* `LocSumR1.array_locmax_bound` (`Swarm/R2LocMax.lean`) and
* `LocSumR1.array_locmax_bound_start` (`Swarm/LocStartRange.lean`, the one used by
  `LocMoveLocalTotal.exists_measure_sep_window_dev_le_total`)

both control the harmonic row `hof p (siteMarks p m U j)` only on the window

  `Finset.Ico (A - ellT (xOf L)) (A + L)`,

i.e. the same `L` fixes the harmonic level `xOf L`, the lower margin `ellT (xOf L)` and the upper
margin `L`.  `LocLeaderObstruction.margin_short` (in `LeaderRangeObstruction.lean`) shows this
window is strictly too narrow to host the read sites of a record window of length `T*L`.

This file proves the genuine wide bound: with **independent** margins `M` (below) and `Up`
(above) and an independent level `L`, the union bound over the window sites still closes
provided the cardinality `M + Up` stays below a fixed multiple `K * L` of the level scale.
Nothing but the *cardinality* of the window enters the proof, because

* `LocSumR1.hof_tail_of_exp_moment` is a per-site Markov bound with an arbitrary site `y`,
* `LocSumR1.markMeasure_exists_site_tail` is a union bound over an arbitrary finite site set,
* `LocSumR1.measurePreserving_siteMarks` transports it to the actual array.

Constants are quantified honestly:

* `array_locmax_bound_wide_explicit` takes the exponential-moment data `θ, C` as hypotheses and
  the absorption inequality at the scale `L` explicitly; the conclusion is the rate `θ/2`;
* `array_locmax_bound_wide` existentially quantifies `c > 0` (it is `θ/2`) and a threshold
  `L₀` which depends on `N`, `K`, `C`, `θ` — the polynomial union factor is `N * K * x^16` with
  `x = L^(1/16)`, absorbed by `LocSumR1.eventually_poly_mul_exp_le … 16`;
* `array_locmax_bound_wide_T` is the shape used at the paper's record window, where
  `M + Up = 2*L + 2*T*L + 2 ≤ (2*T+4)*L`, so `K = 2*T+4`.  The rate `c` does not depend on `T`;
  the threshold does (the union factor carries the factor `2*T+4`).

No probabilistic input beyond the existing exponential moment `exists_exp_moment_hof` is used.
-/
import Swarm.LocStartRange
import Swarm.LeaderRangeObstruction

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace WideRepair

noncomputable section

open SwarmMarks SwarmLogRatio Swarming.Uniform LocSumAct

variable {N : ℕ}

/-- The harmonic `(locmax)` bad event on the wide window `[A - M, A + Up)`, at level `L`
(the level enters only through `xOf L`).  `M` and `Up` are independent of `L`; the narrow
`LocMoveLocal.HMaxBad` is the case `M = ellT (xOf L)`, `Up = L`. -/
def HMaxBadW (p : ℝ) (m L M Up A : ℕ) (U : Array N) : Prop :=
  ∃ j : Fin N, ∃ y ∈ Finset.Ico (A - M) (A + Up),
    xOf L ≤ hof p (siteMarks p m U j) y

/-- **The wide harmonic window bound, with the constants exposed.**

For a fixed exponential-moment bound of `hof` with parameters `θ, C` (which exist by
`exists_exp_moment_hof` for `1/2 < p < 1`, `2 ≤ m`), any window `[A - M, A + Up)` with
`M ≤ A` satisfies

  `P (∃ j, ∃ y ∈ [A-M, A+Up), L^(1/16) ≤ h_j(y)) ≤ exp(-(θ/2) · L^(1/16))`

as soon as the explicit absorption inequality

  `N · (M + Up) · C · exp(-θ·x) ≤ exp(-(θ/2)·x)`,   `x = L^(1/16)`,

holds.  This isolates the entire dependence on the window: only its cardinality `M + Up`. -/
theorem array_locmax_bound_wide_explicit {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} {θ C : ℝ} (hθ : 0 < θ) (hCpos : 0 < C)
    (hmom : ∀ x : ℕ, ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * hof p ω x))
        ∂(markMeasure (boolMeasure (qOf p m))) ≤ ENNReal.ofReal C)
    {L : ℕ} {A M Up : ℕ} (hMA : M ≤ A)
    (habs : (N : ℝ) * (((M : ℝ) + (Up : ℝ))) * C * Real.exp (-(θ * xOf L))
      ≤ Real.exp (-(θ / 2) * xOf L)) :
    arrayMeasure N {U : Array N | HMaxBadW p m L M Up A U}
      ≤ ENNReal.ofReal (Real.exp (-(θ / 2) * xOf L)) := by
  have hp0 : 0 < p := by linarith
  have hC : ∀ x : ℕ, ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * hof p ω x))
      ∂(markMeasure (boolMeasure (qOf p m))) ≤ ENNReal.ofReal C := hmom
  have hCnn : (0 : ℝ) ≤ C := hCpos.le
  set x := xOf L with hxdef
  -- the per-walker row bound
  have hrow : ∀ j : Fin N, arrayMeasure N {U : Array N | ∃ y ∈ Finset.Ico (A - M) (A + Up),
      x ≤ hof p (siteMarks p m U j) y}
      ≤ ((Finset.Ico (A - M) (A + Up)).card : ℝ≥0∞)
        * ENNReal.ofReal (C * Real.exp (-(θ * x))) := by
    intro j
    have hmp := measurePreserving_siteMarks (N := N) hp0 hp2 m j
    have hmeas := LocSumR1.measurableSet_hof_exists (p := p) (ne_of_gt hp0)
      (Finset.Ico (A - M) (A + Up)) x
    have heq : {U : Array N | ∃ y ∈ Finset.Ico (A - M) (A + Up),
        x ≤ hof p (siteMarks p m U j) y}
        = (fun U : Array N => siteMarks p m U j) ⁻¹'
            {ω : ℕ → Bool | ∃ y ∈ Finset.Ico (A - M) (A + Up), x ≤ hof p ω y} := rfl
    rw [heq]
    calc arrayMeasure N ((fun U : Array N => siteMarks p m U j) ⁻¹'
          {ω : ℕ → Bool | ∃ y ∈ Finset.Ico (A - M) (A + Up), x ≤ hof p ω y})
        = (Measure.map (fun U : Array N => siteMarks p m U j) (arrayMeasure N))
            {ω : ℕ → Bool | ∃ y ∈ Finset.Ico (A - M) (A + Up), x ≤ hof p ω y} := by
          rw [Measure.map_apply (measurable_siteMarks hp0 hp2 m j) hmeas]
      _ = markMeasure (boolMeasure (qOf p m))
            {ω : ℕ → Bool | ∃ y ∈ Finset.Ico (A - M) (A + Up), x ≤ hof p ω y} :=
          congrArg (fun ν : Measure (ℕ → Bool) =>
            ν {ω : ℕ → Bool | ∃ y ∈ Finset.Ico (A - M) (A + Up), x ≤ hof p ω y}) hmp.map_eq
      _ ≤ _ :=
          LocSumR1.markMeasure_exists_site_tail hθ hCnn hC (ne_of_gt hp0)
            (Finset.Ico (A - M) (A + Up)) x
  -- the union over the walkers
  have hset : {U : Array N | ∃ j : Fin N, ∃ y ∈ Finset.Ico (A - M) (A + Up),
        x ≤ hof p (siteMarks p m U j) y}
      = ⋃ j : Fin N, {U : Array N | ∃ y ∈ Finset.Ico (A - M) (A + Up),
          x ≤ hof p (siteMarks p m U j) y} := by
    ext U
    simp
  rw [show {U : Array N | HMaxBadW p m L M Up A U}
      = {U : Array N | ∃ j : Fin N, ∃ y ∈ Finset.Ico (A - M) (A + Up),
          x ≤ hof p (siteMarks p m U j) y} from rfl]
  rw [hset]
  refine (measure_iUnion_fintype_le _ _).trans ?_
  refine (Finset.sum_le_sum fun j _ => hrow j).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- the cardinality of the window
  have hcardval : (Finset.Ico (A - M) (A + Up)).card = M + Up := by
    rw [Nat.card_Ico]
    omega
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hexpnn : (0 : ℝ) ≤ Real.exp (-(θ * x)) := (Real.exp_pos _).le
  have hfinal : (N : ℝ) * (((M + Up : ℕ)) : ℝ) * (C * Real.exp (-(θ * x)))
      ≤ Real.exp (-(θ / 2) * x) := by
    have hcast : (((M + Up : ℕ)) : ℝ) = (M : ℝ) + (Up : ℝ) := by push_cast; ring
    rw [hcast]
    have hshape : (N : ℝ) * ((M : ℝ) + (Up : ℝ)) * (C * Real.exp (-(θ * x)))
        = (N : ℝ) * ((M : ℝ) + (Up : ℝ)) * C * Real.exp (-(θ * x)) := by ring
    rw [hshape]
    exact habs
  rw [hcardval, ← ENNReal.ofReal_natCast N, ← ENNReal.ofReal_natCast (M + Up)]
  refine LocSumR1.ofReal_mul_three_le (a := (N : ℝ)) (b := (((M + Up : ℕ)) : ℝ))
    (c := C * Real.exp (-(θ * x))) (d := Real.exp (-(θ / 2) * x)) hNnn (by positivity)
    (mul_nonneg hCnn hexpnn) ?_
  rw [← mul_assoc]
  exact hfinal

/-- **The wide harmonic window bound with a polynomial growth condition on the cardinal.**

There are `c > 0` and `L₀` such that for every `L ≥ L₀`, every anchor `A` and every pair of
independent margins with `M ≤ A` and `M + Up ≤ K * L`,

  `P (∃ j, ∃ y ∈ [A-M, A+Up), L^(1/16) ≤ h_j(y)) ≤ exp(-c · L^(1/16))`.

`c` is `θ/2` from `exists_exp_moment_hof` and is **independent of `K`, `M`, `Up`**; only `L₀`
depends on `K` (through the polynomial factor `N * K * x^16`, `x = L^(1/16)`). -/
theorem array_locmax_bound_wide {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (K : ℝ) (hK : 0 ≤ K) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ (A M Up : ℕ), M ≤ A →
      ((M : ℝ) + (Up : ℝ)) ≤ K * (L : ℝ) →
      arrayMeasure N {U : Array N | HMaxBadW p m L M Up A U}
        ≤ ENNReal.ofReal (Real.exp (-c * xOf L)) := by
  obtain ⟨θ, hθ, C, hCpos, hCraw⟩ := exists_exp_moment_hof (p := p) hp1 hp2 hm
  have hp0 : 0 < p := by linarith
  have hC : ∀ x : ℕ, ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * hof p ω x))
      ∂(markMeasure (boolMeasure (qOf p m))) ≤ ENNReal.ofReal C := fun x => hCraw x
  have hCnn : (0 : ℝ) ≤ C := hCpos.le
  -- absorption of the polynomial union factor `N * K * x^16`
  have hpoly := LocSumR1.eventually_poly_mul_exp_le (C := (N : ℝ) * K * C) (c := θ)
    (by positivity) hθ 16
  have hev : ∀ᶠ L : ℕ in atTop,
      ((N : ℝ) * K * C) * (xOf L) ^ 16 * Real.exp (-θ * xOf L)
        ≤ Real.exp (-(θ / 2) * xOf L) := xOf_tendsto.eventually hpoly
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp hev
  refine ⟨θ / 2, by linarith, max L₁ 1, ?_⟩
  intro L hL A M Up hMA hMU
  have hLge1 : L₁ ≤ L := le_trans (le_max_left _ _) hL
  have hLpos : 1 ≤ L := le_trans (le_max_right _ _) hL
  set x := xOf L with hxdef
  have hxe : x ^ 16 = (L : ℝ) := xOf_pow L
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hexpnn : (0 : ℝ) ≤ Real.exp (-(θ * x)) := (Real.exp_pos _).le
  have hx16nn : (0 : ℝ) ≤ x ^ 16 := by positivity
  -- the window cardinality, and its polynomial bound
  have hcardval : (Finset.Ico (A - M) (A + Up)).card = M + Up := by
    rw [Nat.card_Ico]
    omega
  have hcardle : (((Finset.Ico (A - M) (A + Up)).card : ℕ) : ℝ) ≤ K * x ^ 16 := by
    rw [hcardval]
    have hcast : (((M + Up : ℕ)) : ℝ) = (M : ℝ) + (Up : ℝ) := by push_cast; ring
    rw [hcast, hxe]
    exact hMU
  have hcardnn : (0 : ℝ) ≤ (((Finset.Ico (A - M) (A + Up)).card : ℕ) : ℝ) := by positivity
  -- the explicit absorption inequality
  have hstep : (N : ℝ) * (((Finset.Ico (A - M) (A + Up)).card : ℕ) : ℝ) * C
      ≤ (N : ℝ) * K * C * x ^ 16 := by
    have h1 : (N : ℝ) * (((Finset.Ico (A - M) (A + Up)).card : ℕ) : ℝ) * C
        ≤ (N : ℝ) * (K * x ^ 16) * C := by
      refine mul_le_mul_of_nonneg_right ?_ hCnn
      exact mul_le_mul_of_nonneg_left hcardle hNnn
    have h2 : (N : ℝ) * (K * x ^ 16) * C = (N : ℝ) * K * C * x ^ 16 := by ring
    linarith [h1, h2.le, h2.ge]
  have hcastup : (((M + Up : ℕ)) : ℝ) = (M : ℝ) + (Up : ℝ) := by push_cast; ring
  have hstep' : (N : ℝ) * ((M : ℝ) + (Up : ℝ)) * C ≤ (N : ℝ) * K * C * x ^ 16 := by
    rw [← hcastup, ← hcardval]
    exact hstep
  have habs : (N : ℝ) * ((M : ℝ) + (Up : ℝ)) * C * Real.exp (-(θ * x))
      ≤ Real.exp (-(θ / 2) * x) := by
    have hmono : (N : ℝ) * ((M : ℝ) + (Up : ℝ)) * C * Real.exp (-(θ * x))
        ≤ ((N : ℝ) * K * C * x ^ 16) * Real.exp (-(θ * x)) :=
      mul_le_mul_of_nonneg_right hstep' hexpnn
    have hpolyL : ((N : ℝ) * K * C) * x ^ 16 * Real.exp (-(θ * x))
        ≤ Real.exp (-(θ / 2) * x) := by
      simpa [hxdef] using hL₁ L hLge1
    have hshape : ((N : ℝ) * K * C * x ^ 16) * Real.exp (-(θ * x))
        = ((N : ℝ) * K * C) * x ^ 16 * Real.exp (-(θ * x)) := by ring
    linarith [hmono, hpolyL, hshape.le, hshape.ge]
  exact array_locmax_bound_wide_explicit (N := N) hp1 hp2 hθ hCpos hC (p := p)
    (A := A) (M := M) (Up := Up) hMA (by simpa [hxdef] using habs)

/-- **The wide window bound at the record-window scale.**  For a fixed `T ≥ 1` the record window
`[R - L - T*L, R + T*L]` has margins `M = L + 2*T*L + 2`, `Up = L`, hence cardinality
`2*L + 2*T*L + 2 ≤ (2*T+4)*L`.  The rate `c` is independent of `T`; the threshold `L₀` is not
(the union factor is `N * (2*T+4) * x^16`). -/
theorem array_locmax_bound_wide_T {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (T : ℕ) (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ (A M Up : ℕ), M ≤ A →
      M + Up ≤ (2 * T + 4) * L →
      arrayMeasure N {U : Array N | HMaxBadW p m L M Up A U}
        ≤ ENNReal.ofReal (Real.exp (-c * xOf L)) := by
  have hK : (0 : ℝ) ≤ 2 * (T : ℝ) + 4 := by positivity
  obtain ⟨c, hc, L₀, h⟩ := array_locmax_bound_wide (N := N) (p := p) hp1 hp2 hm
    (2 * (T : ℝ) + 4) hK
  refine ⟨c, hc, L₀, ?_⟩
  intro L hL A M Up hMA hMU
  refine h L hL A M Up hMA ?_
  have h1 : ((M + Up : ℕ) : ℝ) ≤ (((2 * T + 4) * L : ℕ) : ℝ) := by exact_mod_cast hMU
  push_cast at h1
  linarith

end

end WideRepair

namespace WideRepair

noncomputable section

open SwarmMarks SwarmLogRatio Swarming.Uniform LocSumAct

variable {N : ℕ}

/-- **Cross-check: the wide bound subsumes the integrated narrow bound.**  At `T = 1` the wide
theorem covers the margins `M = ⌈L^(1/16)⌉`, `Up = L` (because
`⌈L^(1/16)⌉ + L ≤ (2*1+4)*L`), so `LocSumR1.array_locmax_bound_start` is recovered from
`array_locmax_bound_wide_T`.  The wide statement is therefore strictly stronger, not a
weakening. -/
theorem array_locmax_bound_start_of_wide {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ A : ℕ, ellT (xOf L) ≤ A →
      arrayMeasure N {U : Array N | HMaxBadW p m L (ellT (xOf L)) L A U}
        ≤ ENNReal.ofReal (Real.exp (-c * xOf L)) := by
  obtain ⟨c, hc, L₀, h⟩ := array_locmax_bound_wide_T (N := N) (p := p) hp1 hp2 hm 1 le_rfl
  refine ⟨c, hc, max L₀ 1, ?_⟩
  intro L hL A hA
  have hL0 : L₀ ≤ L := le_trans (le_max_left _ _) hL
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  have hℓ : ellT (xOf L) ≤ L := LocLeaderObstruction.ellT_le_self hL1
  have hMU : ellT (xOf L) + L ≤ (2 * 1 + 4) * L := by omega
  exact h L hL0 A (ellT (xOf L)) L hA hMU

end

end WideRepair

namespace WideRepair

noncomputable section

open SwarmMarks SwarmLogRatio Swarming.Uniform LocSumAct

variable {N : ℕ}

/-- **The wide bound on the paper's own window** `[r-(T+3)L, r+(T+3)L)`, i.e. with margins of
total width `2*(T+3)*L`.  Immediate from `array_locmax_bound_wide_T` at `T+1`, since
`2*(T+3) = 2*(T+1)+4`. -/
theorem array_locmax_bound_paper_window {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (T : ℕ) (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ (A M Up : ℕ), M ≤ A →
      M + Up ≤ 2 * (T + 3) * L →
      arrayMeasure N {U : Array N | HMaxBadW p m L M Up A U}
        ≤ ENNReal.ofReal (Real.exp (-c * xOf L)) := by
  obtain ⟨c, hc, L₀, h⟩ := array_locmax_bound_wide_T (N := N) (p := p) hp1 hp2 hm
    (T + 1) (by omega)
  refine ⟨c, hc, L₀, ?_⟩
  intro L hL A M Up hMA hMU
  refine h L hL A M Up hMA ?_
  have hEq : 2 * (T + 3) * L = (2 * (T + 1) + 4) * L := by ring
  rwa [hEq] at hMU

end

end WideRepair
