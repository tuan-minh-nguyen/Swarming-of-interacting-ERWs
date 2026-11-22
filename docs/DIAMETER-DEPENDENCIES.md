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
The logarithmic upper bound follows from a stretched exponential bound
on the expected visit count by `ae_log_pow_upper_of_regeneration_occupation`.

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
The sharp block estimates of Sections 3.1, 3.2 and 4.1 remain to be proved.

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
