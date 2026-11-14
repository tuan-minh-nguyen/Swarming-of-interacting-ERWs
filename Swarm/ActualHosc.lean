/-
  Direction (E): the oscillation statement `max(M^i_t) - X^i_t = o(n)` for the **actual**
  recursive interacting trajectory (not only for abstract systems satisfying the model law),
  obtained by instantiating `SwarmHosc.hosc_of_law` with the verified
  `SwarmCross.Actual.actual_isInteractingLaw`.

  Also: the residual occupation estimate stated in the paper's own four-way
  decomposition (drift inequality + the `Z`, `J`, `Q` bounds of Proposition `ball`),
  which is the exact input of `SwarmSpeed.speed_lower_bound` after the verified final
  summation `SwarmOcc.occbnd_one_eighth`.
-/
import Swarm.Imports
import Swarm.SwarmMart
import Swarm.Ballistic
import Swarm.ActualInstance
import Swarm.OccAssemble

open MeasureTheory ProbabilityTheory Filter Topology
open Swarming Swarming.Uniform Swarming.Trajectory SwarmCross
open scoped BigOperators ENNReal

set_option maxHeartbeats 1000000

namespace SwarmHosc

/-! ### The concrete trajectory -/

/-- **`hosc` for the actual recursive trajectory**, unconditionally for `1/2 < p < 1`. -/
theorem trajectory_hosc {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m N : ℕ) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N, Tendsto
      (fun n => ((SwarmSpeed.runMax
          (fun t => (Swarming.Trajectory.trajectory p m U t).pos i) n : ℝ)
        - (((Swarming.Trajectory.trajectory p m U n).pos i : ℤ) : ℝ)) / n)
      atTop (𝓝 0) :=
  hosc_of_law (μ := arrayMeasure N) (𝓕 := pathFilt (N := N) p m)
    (X := fun t (U : Array N) => (Swarming.Trajectory.trajectory p m U t).pos)
    (SwarmCross.Actual.actual_isInteractingLaw hp0 hp1 m)
    (le_of_lt hp0) (le_of_lt hp1)

/-- **`max_{t<=n} |M^i_t| = o(n)` for the actual recursive trajectory.** -/
theorem trajectory_mart_max_div {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m N : ℕ) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ t ≤ n, |Swarm.mart p
          (fun t (U : Array N) => (Swarming.Trajectory.trajectory p m U t).pos) m t U i|
        ≤ ε * n := by
  have h := ae_mart_max_div (μ := arrayMeasure N) (𝓕 := pathFilt (N := N) p m)
    (X := fun t (U : Array N) => (Swarming.Trajectory.trajectory p m U t).pos)
    (SwarmCross.Actual.actual_isInteractingLaw hp0 hp1 m) (le_of_lt hp0) (le_of_lt hp1)
  exact ae_all_iff.mpr h

/-! ### The paper's four premises, packaged -/

/-- **The one-sided four-piece interface for `(occbnd)`**, for every system with the model law and every
ordered pair of distinct walkers: the summed drift inequality `(Vdrift)` together with the
three almost-sure bounds `(Vbound)`, `(Jbound)` and `Q_n/n -> 0` (in `n/64` form), with the
paper's `eps = 1/32` and slack `1/64`.

This is the exact input shape of `SwarmOcc.occbnd_one_eighth`; no constant here depends on
the number of walkers `N`.

Warning: `SwarmSpeed.occ` is one-sided, whereas the paper's `(Vdrift)` and `SwarmOcc.occInd`
are two-sided. Those inputs do not imply this interface without a negative-visit correction.
Use `OccTwoSide`/`OccTwoActual` for that route; actual transience supplies the necessary
finitely-many-negative-visits input there. -/
def OccupationPieces (m : ℕ) (p : ℝ) : Prop :=
  ∀ (N : ℕ) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Fin N → ℤ) (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›),
    2 ≤ N → Swarm.IsInteractingLaw 𝓕 μ X m p →
      ∀ᵐ ω ∂μ, ∀ (i j : Fin N), i ≠ j →
        (∃ (Z J Q : ℕ → ℝ) (N₀ : ℕ),
          (∀ n, SwarmSpeed.occ (fun t => X t ω i) (SwarmSpeed.runMax (fun t => X t ω j)) n
              ≤ (1 / 32) * n + (Z n - Z 0) + J n - Q n) ∧
          (∀ n ≥ N₀, Z n ≤ (SwarmSpeed.runMax (fun t => X t ω i) n : ℝ) + (1 / 64) * n) ∧
          (∀ n ≥ N₀, J n ≤ (SwarmSpeed.runMax (fun t => X t ω i) n : ℝ) + (1 / 64) * n) ∧
          (∀ n ≥ N₀, -((1 / 64) * n) ≤ Q n)) ∧
        (∃ (Z J Q : ℕ → ℝ) (N₀ : ℕ),
          (∀ n, SwarmSpeed.occ (fun t => X t ω j) (SwarmSpeed.runMax (fun t => X t ω i)) n
              ≤ (1 / 32) * n + (Z n - Z 0) + J n - Q n) ∧
          (∀ n ≥ N₀, Z n ≤ (SwarmSpeed.runMax (fun t => X t ω j) n : ℝ) + (1 / 64) * n) ∧
          (∀ n ≥ N₀, J n ≤ (SwarmSpeed.runMax (fun t => X t ω j) n : ℝ) + (1 / 64) * n) ∧
          (∀ n ≥ N₀, -((1 / 64) * n) ≤ Q n))

/-- **From the paper's four premises to the occupation estimate** (constant `2`, `eps = 1/8`,
uniform in `N`), the verified final summation of Proposition `ball`. -/
theorem occupationBound_of_pieces {m : ℕ} {p : ℝ} (h : OccupationPieces m p) :
    OccupationBound m p := by
  intro N Ω _ μ _ X 𝓕 hN hlaw
  filter_upwards [h N Ω μ X 𝓕 hN hlaw] with ω hω
  intro i j hij
  obtain ⟨⟨Z, J, Q, N₀, hdrift, hZ, hJ, hQ⟩, ⟨Z', J', Q', N₀', hdrift', hZ', hJ', hQ'⟩⟩ :=
    hω i j hij
  have h1 := SwarmOcc.occbnd_one_eighth (Occ := fun n =>
      SwarmSpeed.occ (fun t => X t ω i) (SwarmSpeed.runMax (fun t => X t ω j)) n)
    (Z := Z) (J := J) (Q := Q) (M := fun n => (SwarmSpeed.runMax (fun t => X t ω i) n : ℝ))
    (N := N₀) hdrift hZ hJ hQ
  have h2 := SwarmOcc.occbnd_one_eighth (Occ := fun n =>
      SwarmSpeed.occ (fun t => X t ω j) (SwarmSpeed.runMax (fun t => X t ω i)) n)
    (Z := Z') (J := J') (Q := Q') (M := fun n => (SwarmSpeed.runMax (fun t => X t ω j) n : ℝ))
    (N := N₀') hdrift' hZ' hJ' hQ'
  exact ⟨max (max N₀ ⌈32 * max 0 (-(Z 0))⌉₊)
      (max N₀' ⌈32 * max 0 (-(Z' 0))⌉₊),
    fun n hn => ⟨h1 n (le_trans (le_max_left _ _) hn),
      h2 n (le_trans (le_max_right _ _) hn)⟩⟩

/-- **Proposition `ball` (lower half) from the paper's four explicit stochastic premises**,
with `kappa = 7/80` independent of `N`.  The oscillation term is supplied by
`SwarmHosc.hosc_of_law`, not assumed. -/
theorem ballistic_of_pieces {m : ℕ} {p : ℝ} (hp1 : 1 / 2 ≤ p) (hp2 : p ≤ 1)
    (h : OccupationPieces m p) : Swarm.Ballistic m p :=
  ballistic_of_occupation hp1 hp2 (occupationBound_of_pieces h)

/-- **`Swarm.Ballistic` is a consequence of the paper's four per-pair stochastic
estimates.**  Consequently `Swarm.main_theorem` holds with `Ballistic` replaced by that
hypothesis. -/
theorem main_theorem_of_pieces {m : ℕ} {p : ℝ} (hm : 2 ≤ m) (hp1 : 1 / 2 < p) (hp2 : p < 1)
    (h : OccupationPieces m p) (hregen : Swarm.RegenAvailable m p)
    (hinit : Swarm.InitialRegen m p) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (X : ℕ → Ω → Fin N → ℤ) (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›),
      2 ≤ N → Swarm.IsInteractingLaw 𝓕 μ X m p →
        ∃ v : ℝ, κ ≤ v ∧ v ≤ 2 * p - 1 ∧
          ∀ᵐ ω ∂μ, ∀ i : Fin N, Tendsto (fun n => Swarm.pos X n i ω / n) atTop (𝓝 v) :=
  Swarm.main_theorem hm hp1 hp2
    (ballistic_of_pieces (le_of_lt hp1) (le_of_lt hp2) h) hregen hinit

end SwarmHosc
