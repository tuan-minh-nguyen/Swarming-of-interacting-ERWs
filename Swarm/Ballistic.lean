/-
  Direction (E): Proposition `ball` (the lower half of the paper's interval), reduced to
  the paper's occupation estimate `(occbnd)` with its constant uniform in the number of
  walkers, plus the now-unconditional oscillation term.

  `SwarmHosc.hosc_of_law` proves `max(M^i_t) - X^i_t = o(n)` (`(prelim)`) for every system
  with the model law, with `p ∈ [1/2,1]`.  What remains of Proposition `ball` is the
  occupation-count estimate

      #{t < n : X^i_t <= M^j_t}  <=  2 M^i_t + n/8      eventually,

  for both orderings of every pair, almost surely, with an almost-sure onset and the
  *same* constant `2` for every `N` and every system.  That statement is the paper's
  `(occbnd)`; it is *not* the ballistic conclusion (it bounds an occupation count, not a
  speed) and it is strictly stronger than nothing: the verified covering argument
  `SwarmSpeed.liminf_speed` turns it into `kappa <= liminf X^i_n/n` with
  `kappa = 7/(40*2) = 7/80`, independent of `N`.

  So this file removes `hosc` from the hypothesis list of `(ball)` and pins the residual
  stochastic input to the occupation estimate alone.
-/
import Swarm.Imports
import Swarm.SwarmMart
import Swarm.Speed
import Swarm.Assembly.Model
import Swarm.Assembly

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal

set_option maxHeartbeats 1000000

namespace SwarmHosc

variable {Ω : Type*} [m0 : MeasurableSpace Ω] {μ : Measure Ω} {N : ℕ}
  {X : ℕ → Ω → Fin N → ℤ} {𝓕 : Filtration ℕ m0} {m : ℕ} {p : ℝ}

/-- Historical fixed-constant occupation premise, NOT the paper's general-coefficient
`(occbnd)`. `SwarmOccC.not_occupationBound_of_lt_35_64` refutes it for `1/2 < p < 35/64` and
for every `m`. Conditional results containing it do not supply ballisticity in that range.
Use `SwarmOccC.OccupationBoundC` in `OccConst.lean` for the corrected residual with coefficient
`C(m,p)`. Retained so that the formal counterexample refers to this exact statement. -/
def OccupationBound (m : ℕ) (p : ℝ) : Prop :=
  ∀ (N : ℕ) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Fin N → ℤ) (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›),
    2 ≤ N → Swarm.IsInteractingLaw 𝓕 μ X m p →
      ∀ᵐ ω ∂μ, ∀ (i j : Fin N), i ≠ j → ∃ N₀ : ℕ, ∀ n ≥ N₀,
        SwarmSpeed.occ (fun t => X t ω i) (SwarmSpeed.runMax (fun t => X t ω j)) n
          ≤ 2 * (SwarmSpeed.runMax (fun t => X t ω i) n : ℝ) + (1 / 8) * n ∧
        SwarmSpeed.occ (fun t => X t ω j) (SwarmSpeed.runMax (fun t => X t ω i)) n
          ≤ 2 * (SwarmSpeed.runMax (fun t => X t ω j) n : ℝ) + (1 / 8) * n

/-- For `N ≥ 2` every walker has a distinct partner. -/
lemma exists_ne_of_two_le {N : ℕ} (hN : 2 ≤ N) (i : Fin N) : ∃ j : Fin N, j ≠ i := by
  by_cases hi : (i : ℕ) = 0
  · refine ⟨⟨1, by omega⟩, fun h => ?_⟩
    have hv : (1 : ℕ) = (i : ℕ) := congrArg Fin.val h
    omega
  · refine ⟨⟨0, by omega⟩, fun h => ?_⟩
    have hv : (0 : ℕ) = (i : ℕ) := congrArg Fin.val h
    omega

/-- Eventual upper bound `X_n^i <= n` on the model, used only to make `liminf` cobounded. -/
lemma eventually_pos_div_le_one (hlaw : Swarm.IsInteractingLaw 𝓕 μ X m p) (i : Fin N) (ω : Ω) :
    ∀ᶠ n : ℕ in atTop, ((X n ω i : ℤ) : ℝ) / n ≤ 1 := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hle : ((X n ω i : ℤ) : ℝ) ≤ (n : ℝ) := by
    have h1 : |X n ω i| ≤ (n : ℤ) := Swarm.abs_le_time_of_law hlaw n ω i
    have h2 : X n ω i ≤ (n : ℤ) := le_trans (le_abs_self _) h1
    exact_mod_cast h2
  rw [div_le_one hn0]
  exact hle

/-- **Proposition `ball`, lower half, as a reduction.**  From the paper's occupation
estimate `(occbnd)` with constant `2` (uniform in `N`) and the model law, every walker
satisfies `7/80 <= liminf X^i_n/n` almost surely, with `7/80` independent of `N` — i.e.
`Swarm.Ballistic m p`.

The oscillation premise `max(M^i_t) - X^i_t = o(n)` is *not* an assumption here: it is
`SwarmHosc.hosc_of_law`, proved from the martingale `(mart)`. -/
theorem ballistic_of_occupation {m : ℕ} {p : ℝ} (hp1 : 1 / 2 ≤ p) (hp2 : p ≤ 1)
    (hocc : OccupationBound m p) : Swarm.Ballistic m p := by
  refine ⟨7 / 80, by norm_num, ?_⟩
  intro N Ω _ μ _ X 𝓕 hN hlaw
  have hocc_ae := hocc N Ω μ X 𝓕 hN hlaw
  have hosc_ae := hosc_of_law (μ := μ) (𝓕 := 𝓕) hlaw hp1 hp2
  filter_upwards [hocc_ae, hosc_ae] with ω hω hoscω
  intro i
  obtain ⟨j, hji⟩ := exists_ne_of_two_le hN i
  obtain ⟨N₀, hN₀⟩ := hω i j (Ne.symm hji)
  have h0 : 0 ≤ (fun n => X n ω i) 0 := by
    have := hlaw.2.1 ω i
    simp [this]
  have hupper : ∀ᶠ n : ℕ in atTop, ((fun n => X n ω i) n : ℝ) / n ≤ 1 := by
    simpa [Swarm.pos] using eventually_pos_div_le_one (μ := μ) (𝓕 := 𝓕) hlaw i ω
  have hkey := SwarmSpeed.liminf_speed (u := fun n => X n ω i) (v := fun n => X n ω j)
    h0 (C := 2) (B := 1) (by norm_num) (N := N₀)
    (fun n hn => (hN₀ n hn).1) (fun n hn => (hN₀ n hn).2) (hoscω i) hupper
  have h80 : 7 / (40 * 2 : ℝ) = 7 / 80 := by norm_num
  simpa [Swarm.pos, h80] using hkey

end SwarmHosc
