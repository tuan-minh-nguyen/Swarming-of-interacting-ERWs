# Proof dependencies for Theorem 1.2

The author-approved statement is [Swarming.swarm_diameter](../draft/DiameterAnchor.lean).
The [manifest](../draft/anchors.json) pins the exact declaration and the version of
`main_1d_regeneration_revised.tex`. The symbol names and line numbers below
refer to that version. An edge lists a result used in the indicated proof.

| Result | Source lines and reference | Inputs |
| --- | --- | --- |
| Walk law and diameter | 77–94, 104–111, `rule`, `distance-def` | Existing uniform-array trajectory and integer diameter |
| Positive speed and sublinear diameter | 399–408, 751–831, `ball`, `diameter` | Existing `M4Blk.main_claim_direct` |
| Simultaneous record geometry | 838–854, `record`, `recordo`, `block` | Walk law, positive speed |
| Spatial sum estimate | 341–398, `max-spatial-tail` | Marked-site recurrence and exponential moment, independent geometric gaps |
| Cubic record estimate | 855–1151, `tight`, `max-cubic-prob` | Record geometry, spatial sums, conditional jump and local-time estimates, extremal coalescence |
| Linear record estimate | 1152–1585, `max-linear-block` | Record geometry, minimum occupation estimate, martingale deviation bounds |
| Record diameter and duration tails | 1586–1638, `record-tail`, `record-duration-tail` | Cubic and linear record estimates, positive speed |
| First regeneration and translated future | 1640–1771, `regen`, `freshlaw` | Record tightness, strict positivity, finite first regeneration, stopped uniform-array factorization |
| Mean duration and record occupation | 1772–1818, `record-average`, `record-moment` | First-regeneration factorization in levels, arithmetic renewal, record duration tails |
| Two-walker diameter estimate | 1850–1993, `max-two-local-bound` | Dominating potentials, spatial sum bounds, optional stopping, martingale deviation bounds |
| Upper bound for cycle occupation | 1997–2070, `max-regeneration-occupation` | Record interval exceedance and duration tails, record occupation identity |
| Lower bound on a finite excursion | 2076–2161, `max-trial` | Simultaneous records, uniform jump lower bound, symmetric-walk confinement and reflection, positive speed for fewer walkers |
| Limiting diameter law | 2165–2189, `max-diameter-distribution` | First regeneration and translated future, finite mean duration, positive mass at time one, arithmetic renewal |
| Upper tail of the limiting diameter | 2190–2196, `max-diameter-upper` | Limiting diameter law, upper cycle occupation bound |
| Almost sure upper bound | 2198–2220, proof of `maxdistance-order` | Upper cycle occupation bound, finite first regeneration, first Borel–Cantelli lemma |
| Almost sure lower bound | 2222–2253, `max-record-density` | Regeneration density, finite excursion bound, conditional failure product, first Borel–Cantelli lemma |
| Lower tail of the limiting diameter | 2255–2275, proof of `diameter-tail` | Almost sure lower bound, first cycle occupation law, union bound over cycles |
| `Swarming.swarm_diameter` | 112–126, `maxdistance` | Both almost sure bounds, limiting diameter law, both tails, common constants |

The [renewal and occupation modules](DIAMETER-SUPPORT.md) establish the
limiting law for the actual swarm. The first regeneration factorization
applies separately to its level and time. The mean duration follows
from the existing finite-mean theorem for selected regeneration blocks.
The lower bounds use positive density of simultaneous records and the
conditional finite-path estimates in each of the three regimes. The
conditional failure estimate sums over the first eligible record and
then removes the time interval covered by that trial.

The record occupation identity in `tendsto_record_event_occupation` follows
from arithmetic renewal in the level variable. The limit is also the
Cesàro limit in `record-average-bound`. Using the partition into intervals
before the first regeneration, `first_regeneration_diameter_occupation_le_record_limsup`
bounds the expected visit count by
$$
\mathbb E^*D\left(
u\limsup_{r\to\infty}\mathbb P(\mathcal E_r(x))
+ \sum_{v\ge0}\limsup_{r\to\infty}\mathbb P(W_r>u+v)
\right),
$$
where $\mathcal E_r(x)=\{\exists\,t\in[\tau_r,\tau_{r+1})\colon\Delta_t\ge x\}$,
$W_r=\tau_{r+1}-\tau_r$, and $u$ is any nonnegative integer.
Taking $u=\lceil x^3\rceil$, we obtain the stretched exponential bound
in `eventually_regeneration_occupation_le_of_record_tails`. The assumptions
are an upper bound with the target exponent for the record exceedances
and an upper bound with exponent $1/3$ for the record durations.
Using the expected visit count, we obtain the almost sure logarithmic upper
bound in `ae_log_pow_upper_of_regeneration_occupation` and the limiting
upper tail in `exists_diameter_limit_with_upper_tail_of_regeneration_occupation`.

The existing bound in `M4Blk.paperBadBlockProfile` has exponent $1/16$.
It proves uniform tightness of the diameters at the record times. The
probabilities of initial diameter exceedances converge by the record
occupation identity. Using this convergence in
`record_diameter_tail_le_of_contraction`, we take the limit in the
record level at each fixed scale, then iterate the halving estimate.
`record_duration_limsup_le_of_advance` bounds the duration tail
from the advance estimate in the same block.

For exceedances within a record interval, we have two bounds.
`record_interval_exceedance_prob_le_initial_or_duration` uses the
nearest-neighbour step bound. `record_interval_exceedance_prob_le`
uses the drift martingale at the first hitting time of the record level.
The sharp record estimates of Sections 3.1 and 4.1 are verified. The estimate of Section 3.2 remains open in Lean.
The spatial estimate `max-spatial-tail` is formalised in
`arrayMeasure_sum_hof_pow_tail`. Convexity at each marked site and
summation over the intervals bound the spatial sum by the initial potential
and the sum of gap lengths raised to the power $q+1$. The prescribed finite
gap events have the law of a product of geometric measures. The proof
combines the truncated exponential estimate for their sum of powers with
the existing exponential moment for the initial potential.
Using a finite union bound in `arrayMeasure_local_hof_estimates`, we
obtain the spatial bounds in `max-cubic-spatial` uniformly over every
walker, site and subinterval of the prescribed interval. The coefficient of
the subinterval length depends only on $m,p$.

Using this spatial bound and the conditional martingale estimate at each
first-passage time, `record_projH_oscillation_le_cube_root` bounds projected
potential oscillations beyond $\varepsilon L$ by $e^{-cL^{1/3}}$.
`gamma_trial_concentration` bounds the probability of an $\varepsilon L$
deficit from the trial-count lower estimate by $e^{-cL}$, uniformly over the
nonempty proper groups and the prescribed subintervals.

`record_Qpl_oscillation_le_cube_root` establishes the same oscillation bound
for the occupation martingale on every pair of times in the record interval.
The geometric condition holds throughout each first-passage cell. The sum of
the spatial exceptional masses over the disjoint cells is bounded by the
unconditional failure probability of the spatial estimate.

`record_group_drift_failure_le_cube_root` keeps the group potential fixed
at the time before each jump. The linear bound on this increment permits
an Azuma bound of order $e^{-cL^{1/3}}$ and preserves the conditional drift
term in `max-fixed-coordinate`. Its sign on separated subintervals yields
the estimate `locgroup` in `record_separated_group_failure_le_cube_root`.

`record_group_advance_drift_failure_le_cube_root` combines the group
drift estimate with the trial count on the random interval of record levels.
The finishing times of the successful trials are distinct and each contributes
a negative correction. This proves `locmove-second` at the cube-root rate.

`record_group_potential_failure_le_cube_root` proves `loccoord` using the
spatial sum of squared potentials. `record_group_maximum_failure_le_cube_root`
proves the unit-rate lower bound for the trailing group's maximum potential.
In `record_group_movement_failure_le_cube_root`, the two drift inequalities
cancel the advance of the leading group's record, as in `locmove`. The
failure probability is bounded by $3e^{-cL^{1/3}}$.

## Local clauses on the record interval

`record_occupation_estimate_of_local_bounds` takes a potential cutoff `V` and an error bound `E ≥ V ^ 2`. It reuses `SummedSlope.lococc_summed` for the summed occupation inequality. `record_occupation_failure_le_cube_root` applies the spatial and martingale estimates with `V = L ^ (1 / 3)` and `E` proportional to `ε * L`, uniformly over the integer subintervals of the record interval.

`record_local_clauses_failure_le_cube_root` combines the occupation estimate, group potential bounds, movement estimates, and compensated trajectory martingale. The error in `BlkCoin.BlockClauses` and `JoinStep.MartClause` is `ε * L`. The common coefficient `C` is chosen before the time horizon and the error tolerance. The probability that either clause fails on the record carrier is at most `K * exp (-c * L ^ (1 / 3))`.

## Cubic record-block estimate

`coalesced_at_of_local_errors` allows the coefficient of `L ^ (3 / 4)` to vary with the scale. Its integer upper bound divided by `L` tends to zero along the sequences appearing in `record_defect_halves_of_local_clauses`. The compactness argument in the latter theorem fixes an error tolerance `ε > 0` before the scale and record level. `record_cubic_block_failure_le` combines halving, record advancement and `record_local_clauses_failure_le_cube_root` at that tolerance. The result proves `max-cubic-prob` on the original probability space.

`record_interval_tails_le_of_block` applies the contraction at scale `2 * L` and controls each record duration by the time to reach the later record. It establishes cube-root bounds for the duration and diameter exceedance. `swarm_diameter_cubic` then proves all parts of Theorem 1.2 when `3 ≤ N ≤ m`. The cubic duration bound also applies to two walkers.

## Two-walker crossing estimates

`record_downward_crossing_prob_le` partitions the event by the first-passage time to the initial record level. On each measurable part, the existing frozen-walk crossing estimate bounds the probability by the integral of the product of site ratios. The disjoint parts are summed before taking the expectation of the product. `record_downward_excursion_failure_le_sqrt` uses this estimate and a finite union bound over the interval in `max-two-downward`.

`record_offset_martingale_window_prob_le` shifts the same partition by a fixed offset. `two_walker_front_excursion_prob_le` applies it to `max-two-front-new`. The excitation count is constant during an excursion above a level that the other walker has yet to reach.

## Two-walker record and diameter bounds

`record_offset_interval_survival_prob_le` iterates the potential exit-time estimate on the disjoint record-time events. `two_walker_passage_order_prob_le` combines that estimate with the martingale bound on excursions. `two_walker_meeting_of_no_deviations` controls the first time both walkers have reached the initial level. `exists_passage_order_of_large_diameter` reduces a later exceedance to a passage before the trailing walker exits. Together with the downward-crossing and spatial probability bounds, these prove `max-two-local-bound` in `record_two_walker_halving_failure_le_sqrt`.

`record_two_walker_exceedance_limsup_le` uses the cube-root duration bound at times of order $L^2$ for the time cutoff in the record contraction. For the exceedance between two successive records, it balances the duration and martingale estimates at times of order $x^{3/2}$. `swarm_diameter_two_walker` proves the $N=2$ case of Theorem 1.2.

## Minimum progress when `m < N`

Every walker at the global minimum is excited when the minimum is nonnegative. `minimum_progress_of_compensated_error` sums the compensated paths truncated at the terminal minimum plus the error allowance. Using the record-time martingale bound, `record_minimum_progress_failure_le_exp` controls the failure of minimum progress uniformly over all subintervals. `softMinimum_sub_ge_weighted_sum` controls the increments of the logarithmic approximation of the minimum for the separated-group comparison.

## Bounded comparison functions

`boundedSlope_increment_eq_min` identifies the comparison drift after truncation. It lies in `[0, 1]` and equals one at an excited site when the slope bound is at least `(2 * p - 1)⁻¹`. `boundedSlope_le_window` bounds a truncated slope by the affine recursion restarted at the left endpoint of a finite spatial interval. `softMinimum_weighted_drift_lower` bounds the contribution of walkers farther than the prescribed distance from the minimum.

## Spatial estimates and minimum occupation when `m < N`

The affine recursion started at `K = 8 * k` is bounded by `10 * Q` for the truncation to `k` consecutive sites. A slope exceeding `K - 2` requires the product of the last `k` ratios to exceed one half. The two spatial sums have exponential concentration by applying Hoeffding's inequality on each residue class modulo `k`.

The occupation test is a sum over the sites of a fixed finite set. Its increment is controlled by a predictable sum of the walkers' compensated steps and a strictly negative term when an excited minimizer occupies the set. `record_small_set_minimum_occupation_failure_le_exp` applies a union bound over subsets of sufficiently small cardinality. The estimate applies to the exceptional sites selected from the array.

## Maximum and limiting tail

Write $T=\tau_D$, $\mu=\mathbb E^*T$ and $M_n=\max_{0\le j\le n}\Delta_j$.
Let $\nu$ be the probability measure in equation (4.13) and let $u_s$
be the probability of a regeneration at time $s$. Using the last-renewal
identity and $0\le u_s\le1$, we have for every $x\ge0$
$$
\mathbb P^*(\Delta_n\ge x)
\le \sum_{t\ge0}\mathbb P^*(T>t,\Delta_t\ge x)
= \mu\,\nu([x,\infty)).
$$
By a union bound,
$$
\mathbb P^*(M_n\ge x)\le(n+1)\mu\,\nu([x,\infty)).
$$
The upper occupation estimate therefore suffices for the almost sure upper
bound by Borel–Cantelli. For the lower tail, suppose
$M_n\ge a(\log n)^\beta$ eventually almost surely under $\mathbb P^*$. For
$n=\lceil\exp((x/a)^{1/\beta})\rceil$, we have
$\mathbb P^*(M_n\ge x)\ge1/2$ for all large $x$. Thus
$$
\nu([x,\infty))\ge\frac{1}{2\mu(n+1)}
\ge\frac{1}{6\mu}\exp(-(x/a)^{1/\beta}).
$$
