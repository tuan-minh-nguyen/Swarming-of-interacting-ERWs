/-
  **The actual product-decay event and the resulting transience reduction.**

  `RawLogRatio` proves eventual block-product decay for the real uniform array.
  `Aggregation` supplies Borel--Cantelli and the nonnegative-level path argument.
  This file joins those boundaries using `ActualExtra`, the paper's extra event with
  `omegaAt` of the other walker.  The exported theorem has only the integrated crossing
  estimate as a stochastic premise; the strong law and product decay are proved inside.
  It does not assert that this remaining crossing premise has been established.
-/
import Swarm.RawLogRatio
import Swarm.Aggregation

open MeasureTheory Filter
open Swarming Swarming.Uniform Swarming.Trajectory
open scoped ENNReal BigOperators Topology

namespace SwarmDischarge

noncomputable section

open SwarmSpeed

/-- The paper's extra event, written with the actual weights of walker `j`. -/
def ActualExtra {N : ℕ} (p : ℝ) (m : ℕ) (j : Fin N) (c : ℝ) (k : ℕ) :
    Set (Array N) :=
  {U | ∏ x ∈ Finset.Ioc (lvlA k) (lvlB k),
      ((1 - omegaAt p m U j (x : ℤ)) / omegaAt p m U j (x : ℤ)) ≤
    Real.exp (-(c * (lvlB k : ℝ)))}

/-- The actual extra event holds eventually almost surely. -/
theorem ae_eventually_actualExtra {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p)
    (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m) (j : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ᶠ k : ℕ in atTop,
      U ∈ ActualExtra p m j (SwarmLogRatio.paperC p ((1 - p) ^ (m - 1))) k := by
  filter_upwards [SwarmLogRatio.ae_prod_decay_array (N := N) hp1 hp2 hm j] with U hU
  filter_upwards [hU] with k hk
  simpa only [ActualExtra, Set.mem_ofPred_eq, neg_mul] using hk

/--
Transience of the actual interacting trajectory, with the log-ratio strong law and eventual
product decay discharged.  The remaining premise is precisely the integrated conditional
crossing estimate on the paper's bad-time/product-small event.
-/
theorem ae_transience_of_actual_crossing_bound {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p)
    (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m) (a b : Fin N) {K : ℕ}
    (hcross : ∀ k ≥ K, ∀ s : ℕ,
      (arrayMeasure N)
        ({U : Array N | BadTime p m U a b k s} ∩
          ActualExtra p m b (SwarmLogRatio.paperC p ((1 - p) ^ (m - 1))) k)
        ≤ ENNReal.ofReal (Real.exp
          (-(SwarmLogRatio.paperC p ((1 - p) ^ (m - 1)) * (lvlB k : ℝ))))) :
    ∀ᵐ U ∂(arrayMeasure N),
      Tendsto (fun n => (trajectory p m U n).pos a) atTop atTop := by
  exact ae_transience_of_factored_crossing_bound (N := N) hp1.le m a b
    (SwarmLogRatio.paperC_paper_pos hp1 hp2)
    (ae_eventually_actualExtra hp1 hp2 hm b) hcross

end
end SwarmDischarge
