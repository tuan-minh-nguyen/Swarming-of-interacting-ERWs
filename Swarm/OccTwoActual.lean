/-
  **Historical fixed-constant actual-trajectory occupation interface.** Its `PaperPiecesTwoSided`
  premise together with both orderings is refuted for `p < 35/64` at the actual array (see
  `OccPaper.lean`). These formal reductions cannot be instantiated for those parameters. The
  coefficient must depend on `m,p`; `OccTwoC.lean` supplies the corrected general-coefficient
  interface. Actual transience and the negative-visit bound remain proved and usable.

  The original development follows, with its fixed constants left unchanged to preserve the
  precise statements of the counterexample.

  `OccTwoSide.lean` proves that the paper's summed two-sided `(Vdrift)` plus the two-sided
  `(Vbound)`, `(Jbound)` and `Q_n = o(n)` bounds give the one-sided occupation estimate
  consumed by the covering argument, provided the walker's negative visits are eventually
  bounded.  This file supplies that bound at the actual recursive trajectory from the
  already verified transience theorem `SwarmBad.ae_transience_actual`, and composes
  everything into the paper's `(occbnd)` for the actual trajectory — and further into the
  paper's lower speed bound `7/80 <= liminf X^i_n/n`, using the verified oscillation
  `SwarmHosc.trajectory_hosc`.

  Nothing here is a hypothesis about an abstract system: the objects are
  `Swarming.Trajectory.trajectory p m U` on `Swarming.Uniform.arrayMeasure N`, the actual
  nested path filtration is not even mentioned, and every constant (`2`, `1/8`, `7/80`) is
  independent of `N`.  The single residual input is `PaperPiecesTwoSided`, which is exactly
  the paper's four per-pair estimates in their *two-sided* form, i.e. the form in which the
  paper's own one-step drift inequality and `SwarmOcc.sum_drift_bound` produce them.
-/
import Swarm.Imports
import Swarm.OccTwoSide
import Swarm.FrozenBadTime
import Swarm.ActualHosc

open MeasureTheory Filter
open Swarming Swarming.Uniform Swarming.Trajectory
open scoped Topology BigOperators

namespace SwarmOccTwo

variable {N : ℕ} {p : ℝ} {m : ℕ}

/-! ### The actual occupation counts -/

/-- The one-sided occupation count `#{t < n : X^i_t <= M^j_t}` of the actual trajectory. -/
noncomputable def OccOfMax (p : ℝ) (m N : ℕ) (i j : Fin N) (U : Array N) (n : ℕ) : ℝ :=
  SwarmSpeed.occ (fun t => (trajectory p m U t).pos i)
    (SwarmSpeed.runMax (fun t => (trajectory p m U t).pos j)) n

/-- The paper's two-sided occupation count `#{t < n : 0 <= X^i_t <= M^j_t}` of the actual
trajectory. -/
noncomputable def OccTwoOfMax (p : ℝ) (m N : ℕ) (i j : Fin N) (U : Array N) (n : ℕ) : ℝ :=
  occTwo (fun t => (trajectory p m U t).pos i)
    (SwarmSpeed.runMax (fun t => (trajectory p m U t).pos j)) n

/-- **The paper's four per-pair estimates, in the two-sided form in which the paper's own
one-step drift inequality `(Vdrift)` produces them.**  This is the residual stochastic input
of the occupation estimate for walker `i` against the running maximum of walker `j`:
the summed two-sided `(Vdrift)` at `eps = 1/64`, the two-sided `(Vbound)` and `(Jbound)`
each with budget `n/64`, and `Q_n >= -n/64` (from `Q_n = o(n)`). -/
def PaperPiecesTwoSided (p : ℝ) (m N : ℕ) (i j : Fin N) (U : Array N) : Prop :=
  ∃ (Z J Q : ℕ → ℝ) (N₀ : ℕ),
    (∀ n, OccTwoOfMax p m N i j U n ≤ (1 / 64) * n + (Z n - Z 0) + J n - Q n) ∧
    (∀ n ≥ N₀, Z n ≤
      (SwarmSpeed.runMax (fun t => (trajectory p m U t).pos i) n : ℝ) + (1 / 64) * n) ∧
    (∀ n ≥ N₀, J n ≤
      (SwarmSpeed.runMax (fun t => (trajectory p m U t).pos i) n : ℝ) + (1 / 64) * n) ∧
    (∀ n ≥ N₀, -((1 / 64) * n) ≤ Q n)

/-! ### Negative visits are bounded: the actual transience input -/

/-- **Eventual nonnegativity of the actual walker**, from the verified transience
`SwarmBad.ae_transience_actual`. -/
theorem ae_eventually_nonneg_actual (hp0 : 1 / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m)
    (i j : Fin N) (hij : i ≠ j) :
    ∀ᵐ U ∂(arrayMeasure N), ∃ k : ℕ, ∀ t ≥ k, 0 ≤ (trajectory p m U t).pos i := by
  filter_upwards [SwarmBad.ae_transience_actual (N := N) hp0 hp1 hm i j hij] with U hU
  obtain ⟨k, hk⟩ := tendsto_atTop_atTop.mp hU 0
  exact ⟨k, hk⟩

/-- **Bounded negative visits for the actual walker**: a.s. there is `K` with
`#{t < n : X^i_t < 0} <= K` for every `n`.  This is the `K(omega)` that
`OccTwoSide.occbnd_of_twoSided` absorbs into the eventual onset. -/
theorem ae_negCount_bdd (hp0 : 1 / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m)
    (i j : Fin N) (hij : i ≠ j) :
    ∀ᵐ U ∂(arrayMeasure N), ∃ K : ℕ, ∀ n : ℕ,
      negCount (fun t => (trajectory p m U t).pos i) n ≤ (K : ℝ) := by
  filter_upwards [ae_eventually_nonneg_actual (N := N) hp0 hp1 hm i j hij] with U hU
  obtain ⟨k, hk⟩ := hU
  exact ⟨k, fun n => negCount_le_of_eventually_nonneg
    (u := fun t => (trajectory p m U t).pos i) hk n⟩

/-! ### The two-sided inputs give the one-sided occupation estimate -/

/-- **`(occbnd)` for one ordered pair of the actual trajectory.**  From the paper's four
two-sided estimates for `(i,j)` and the actual transience of walker `i`, the one-sided
occupation count is eventually at most `2 M^i_n + n/8`. -/
theorem actual_occ_of_twoSided (hp0 : 1 / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m)
    (i j : Fin N) (hij : i ≠ j)
    (hP : ∀ᵐ U ∂(arrayMeasure N), PaperPiecesTwoSided p m N i j U) :
    ∀ᵐ U ∂(arrayMeasure N), ∃ N₁ : ℕ, ∀ n ≥ N₁,
      OccOfMax p m N i j U n ≤
        2 * ((SwarmSpeed.runMax (fun t => (trajectory p m U t).pos i) n : ℤ) : ℝ) + (1 / 8) * n := by
  filter_upwards [hP, ae_negCount_bdd (N := N) hp0 hp1 hm i j hij] with U hU hneg
  obtain ⟨Z, J, Q, N₀, h1, h2, h3, h4⟩ := hU
  obtain ⟨K, hK⟩ := hneg
  refine ⟨max N₀ ⌈64 * max 0 ((K : ℝ) - Z 0)⌉₊, fun n hn => ?_⟩
  exact occbnd_of_twoSided_runMax (u := fun t => (trajectory p m U t).pos i)
    (v := fun t => (trajectory p m U t).pos j) h1 hK h2 h3 h4 n hn

/-- **`(occbnd)` for every ordered pair of the actual trajectory**, simultaneously for every
pair of distinct walkers `i ≠ j` with `N >= 2`.  The conclusion is exactly the conclusion of
`SwarmHosc.OccupationBound` restricted to the actual system
`(arrayMeasure N, trajectory p m ·)`. -/
theorem actual_occ_of_twoSided_all (hp0 : 1 / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m)
    (hP : ∀ᵐ U ∂(arrayMeasure N), ∀ i j : Fin N, i ≠ j → PaperPiecesTwoSided p m N i j U) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ i j : Fin N, i ≠ j → ∃ N₁ : ℕ, ∀ n ≥ N₁,
      OccOfMax p m N i j U n ≤
        2 * ((SwarmSpeed.runMax (fun t => (trajectory p m U t).pos i) n : ℤ) : ℝ) + (1 / 8) * n := by
  have hpair : ∀ x : Fin N × Fin N, ∀ᵐ U ∂(arrayMeasure N), x.1 ≠ x.2 →
      (PaperPiecesTwoSided p m N x.1 x.2 U ∧
        ∃ K : ℕ, ∀ n : ℕ, negCount (fun t => (trajectory p m U t).pos x.1) n ≤ (K : ℝ)) := by
    intro x
    by_cases hx : x.1 = x.2
    · exact Filter.Eventually.of_forall fun U hne => absurd hx hne
    · have h1 : ∀ᵐ U ∂(arrayMeasure N), PaperPiecesTwoSided p m N x.1 x.2 U :=
        hP.mono fun U hU => hU x.1 x.2 hx
      exact (h1.and (ae_negCount_bdd (N := N) hp0 hp1 hm x.1 x.2 hx)).mono
        fun U h _ => h
  have hall := Filter.eventually_all.mpr hpair
  filter_upwards [hall] with U hU i j hij
  obtain ⟨⟨Z, J, Q, N₀, h1, h2, h3, h4⟩, ⟨K, hK⟩⟩ := hU (i, j) hij
  refine ⟨max N₀ ⌈64 * max 0 ((K : ℝ) - Z 0)⌉₊, fun n hn => ?_⟩
  exact occbnd_of_twoSided_runMax (u := fun t => (trajectory p m U t).pos i)
    (v := fun t => (trajectory p m U t).pos j) h1 hK h2 h3 h4 n hn

/-- The paired form: both orderings of every pair, as a conjunction.  (The all-pairs
statement above applied to `(i,j)` and `(j,i)`.) -/
theorem actual_occ_of_twoSided_both (hp0 : 1 / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m)
    (hP : ∀ᵐ U ∂(arrayMeasure N), ∀ i j : Fin N, i ≠ j → PaperPiecesTwoSided p m N i j U) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ i j : Fin N, i ≠ j → ∃ N₁ : ℕ, ∀ n ≥ N₁,
      OccOfMax p m N i j U n ≤
          2 * ((SwarmSpeed.runMax (fun t => (trajectory p m U t).pos i) n : ℤ) : ℝ) + (1 / 8) * n ∧
        OccOfMax p m N j i U n ≤
          2 * ((SwarmSpeed.runMax (fun t => (trajectory p m U t).pos j) n : ℤ) : ℝ) + (1 / 8) * n := by
  have h := actual_occ_of_twoSided_all (N := N) hp0 hp1 hm hP
  filter_upwards [h] with U hU i j hij
  obtain ⟨N₁, h1⟩ := hU i j hij
  obtain ⟨N₂, h2⟩ := hU j i (Ne.symm hij)
  exact ⟨max N₁ N₂, fun n hn =>
    ⟨h1 n (le_trans (le_max_left _ _) hn), h2 n (le_trans (le_max_right _ _) hn)⟩⟩

/-! ### The paper's lower speed bound at the actual trajectory -/

/-- The actual walker position divided by time is eventually at most `1`, because every
jump has length one (the paper's trivial upper bound, used only to make `liminf`
cobounded). -/
theorem actual_pos_div_le_one (hp0 : 1 / 2 < p) (hp1 : p < 1) (i : Fin N) (U : Array N) :
    ∀ᶠ n : ℕ in atTop, ((trajectory p m U n).pos i : ℝ) / n ≤ 1 := by
  have hlaw := SwarmCross.Actual.actual_isInteractingLaw (N := N) hp0 hp1 m
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hle : ((trajectory p m U n).pos i : ℝ) ≤ (n : ℝ) := by
    have h1 : (trajectory p m U n).pos i ≤ (n : ℤ) :=
      le_trans (le_abs_self _) (Swarm.abs_le_time_of_law hlaw n U i)
    exact_mod_cast h1
  rw [div_le_one hn0]
  exact hle

/-- **The paper's lower bound `7/80 <= liminf X^i_n/n` for the actual trajectory**, from the
four two-sided per-pair estimates and nothing else: the oscillation premise is the verified
`SwarmHosc.trajectory_hosc`, the negative-visit correction is the verified actual transience,
and the occupation estimate is `actual_occ_of_twoSided_all`. -/
theorem actual_liminf_speed_of_twoSided (hp0 : 1 / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m)
    (hN : 2 ≤ N)
    (hP : ∀ᵐ U ∂(arrayMeasure N), ∀ i j : Fin N, i ≠ j → PaperPiecesTwoSided p m N i j U) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
      7 / 80 ≤ liminf (fun n : ℕ => ((trajectory p m U n).pos i : ℝ) / n) atTop := by
  have hocc := actual_occ_of_twoSided_all (N := N) hp0 hp1 hm hP
  have hosc := SwarmHosc.trajectory_hosc (p := p) hp0 hp1 m N
  filter_upwards [hocc, hosc] with U hU hoscU i
  obtain ⟨j, hji⟩ := SwarmHosc.exists_ne_of_two_le hN i
  obtain ⟨N₁, hN₁⟩ := hU i j (Ne.symm hji)
  obtain ⟨N₂, hN₂⟩ := hU j i hji
  have h0 : 0 ≤ (fun t => (trajectory p m U t).pos i) 0 := by
    simp [trajectory_zero, initialWalkState]
  have hkey := SwarmSpeed.liminf_speed
    (u := fun t => (trajectory p m U t).pos i)
    (v := fun t => (trajectory p m U t).pos j)
    h0 (C := 2) (B := 1) (by norm_num) (N := max N₁ N₂)
    (fun n hn => hN₁ n (le_trans (le_max_left _ _) hn))
    (fun n hn => hN₂ n (le_trans (le_max_right _ _) hn))
    (hoscU i) (actual_pos_div_le_one (N := N) (p := p) (m := m) hp0 hp1 i U)
  have h80 : 7 / (40 * 2 : ℝ) = 7 / 80 := by norm_num
  simpa [h80] using hkey

end SwarmOccTwo
