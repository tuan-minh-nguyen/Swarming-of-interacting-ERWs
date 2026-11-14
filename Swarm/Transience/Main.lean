/-
  **Lemma `transience` for the actual interacting trajectory, reduced to the paper's
  no-bad-time condition.**

  `main_1d_revised.tex`, proof of Lemma `transience`, splits into
  (1) the crossing estimate eq. (cross),
  (2) Borel--Cantelli over the levels, giving that eventually in `k` no time
      `s <= (k+1)^4` is *bad* (`X^i_s = b_k`, `M^j_s >= b_k + 1`, and `X^i` reaches `a_k`
      before `b_k + 1`),
  (3) the pathwise argument concluding `X^i_n -> +infty`.

  `Discharge.lean` proves (3) together with every other pathwise input of the paper's
  argument for the actual trajectory.  The only thing this theorem still assumes is (2),
  as an explicit hypothesis on the sample — it is not hidden in a structure, it is not a
  weakening, and it is precisely what the crossing estimate plus Borel--Cantelli supply.
-/
import Swarm.Discharge

open MeasureTheory Filter
open Swarming Swarming.Uniform Swarming.Trajectory
open scoped ENNReal BigOperators Topology

namespace SwarmDischarge

open SwarmSpeed

/-- The paper's **bad time** at level `k`: at time `s`, walker `i` sits at `b_k`, walker
`j`'s running maximum is already at least `b_k + 1`, and walker `i` reaches `a_k` before
`b_k + 1`.  This is the event excluded by the Borel--Cantelli consequence of eq. (cross). -/
def BadTime {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (i j : Fin N) (k s : ℕ) : Prop :=
  (trajectory p m U s).pos i = (lvlB k : ℤ) ∧
  (lvlB k : ℤ) + 1 ≤ runMax (fun t => (trajectory p m U t).pos j) s ∧
  SwarmDeepNat.hitBefore (fun t => (trajectory p m U t).pos i) s ((lvlB k : ℤ) + 1) (lvlA k)

/-- **Lemma `transience`, modulo the no-bad-time condition.**  For `p >= 1/2` and any two
walkers `i`, `j`, almost surely: if above level `K` no time `s <= (k+1)^4` is a bad time,
then walker `i` is transient to `+infinity`.

Every other hypothesis of the pathwise lemma (`UnitSteps`, `u 0 = 0`, every level visited,
`hτk`, `hMv`, and the arithmetic of the levels `b_k = floor(k^{1/4})-1`, `a_k = b_k/2`) is
discharged here from the verified model; see `Discharge.lean` and `Rate.lean`. -/
theorem ae_transience_of_no_bad_times {N : ℕ} {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ)
    (i j : Fin N) {K : ℕ} (hK : 2 ≤ K) :
    ∀ᵐ U ∂(arrayMeasure N),
      (∀ k ≥ K, ∀ s ≤ (k + 1) ^ 4, ¬ BadTime p m U i j k s) →
        Tendsto (fun n => (trajectory p m U n).pos i) atTop atTop := by
  filter_upwards [ae_all_levels_hit (N := N) hp m i,
    ae_eventually_reach_succ (N := N) hp m i,
    ae_eventually_runMax_ge_lvlB (N := N) hp m j] with U hlv hτ hM
  intro hbad
  obtain ⟨K₁, hK₁⟩ := hτ
  obtain ⟨K₂, hK₂⟩ := hM
  refine transience_of_paper_levels_nat (fun n => (trajectory p m U n).pos i)
    (fun n => (trajectory p m U n).pos j) (trajectory_unitSteps p m U i)
    (trajectory_zero_pos p m U i) hlv (K := max K (max K₁ K₂)) ?_ ?_ ?_ ?_
  · omega
  · intro k hk s hs
    simpa only [BadTime] using hbad k (le_trans (le_max_left _ _) hk) s hs
  · intro k hk
    have h1 : K₁ ≤ k :=
      le_trans (le_trans (le_max_left K₁ K₂) (le_max_right K (max K₁ K₂))) hk
    obtain ⟨t, ht, he⟩ := hK₁ k h1
    exact le_trans (SwarmDeepNat.firstHit_le he) ht
  · intro k hk s hks hs
    have h2 : K₂ ≤ k :=
      le_trans (le_trans (le_max_right K₁ K₂) (le_max_right K (max K₁ K₂))) hk
    exact hK₂ k h2 s hks hs

end SwarmDischarge

