/-
# The actual diameter estimate

The block-uniform Q variance, the reset-time spatial comparison, and the finite-summand deficit
transfer are now proved.  This file instantiates them to close `(diam)` at the actual array.
-/
import Swarm.HcompMain
import Swarm.DiamPayoff
import Swarm.Smom4Q

open Filter Finset MeasureTheory Topology
open scoped BigOperators

namespace DiamAssemblyHcomp

open Swarming Swarming.Uniform

/-- **Actual `(diam)`:** for every `1/2 < p < 1`, `2 ≤ m`, and `2 ≤ N`, almost surely the
largest spread among the interacting walkers is sublinear in time. -/
theorem diam_actual {N : ℕ} {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) [Nonempty (Fin N)] :
    ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
      Tendsto (fun n => ((LeaderDescent.spreadZ (DiamAssembly.XA p m U) n : ℤ) : ℝ) / (n : ℝ))
        atTop (𝓝 0) :=
  diam_conditional (N := N) hp0 hp1 hm hN
    (SwarmSmom4.Q_log_variance_uniform_blocks (N := N) hp0 hp1 m)
    (DiamAssemblyHdefA.hdefA (N := N) hp0 hp1 m)

end DiamAssemblyHcomp
