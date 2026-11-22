# Swarm diameter formalisation

The source is Theorem 1.2 of `main_1d_regeneration_revised.tex`, with
SHA-256 `1ea00e1c34ca56655cf84d8307d74247cb135dbbda61295038256505f2b44e6b`.

Write $\Delta_t$ for the diameter at time $t$ and $T=\tau_D$ for the first
positive regeneration time. Under the law $\mathbb P^*$ conditioned on strict
positivity, $\mathbb P^*(T=1)>0$ and $\mathbb E^*T<\infty$.
For every Borel set $A\subseteq\mathbb R$, the formalised limiting law satisfies
$$
\nu(A)=\frac{1}{\mathbb E^*T}\sum_{t\ge0}\mathbb P^*(T>t,\ \Delta_t\in A).
$$
The probabilities of $\{\Delta_n\in A\}$ under $\mathbb P$ and $\mathbb P^*$
both converge to $\nu(A)$. Under $\mathbb P^*$, for each $n$,
$$
\mathbb P^*(\exists t\le n,\ \Delta_t\in A)
\le (n+1)\sum_{t\ge0}\mathbb P^*(T>t,\ \Delta_t\in A).
$$
These conclusions are in `Swarming.Diameter.exists_diameter_occupationLaw`.

| Module | Result |
| --- | --- |
| [SwarmRenewal.lean](../SwarmDiameter/SwarmRenewal.lean) | Weak convergence to a law on $[0,\infty)$, the first-regeneration occupation formula, and the finite-horizon bound above. |
| [ArithmeticRenewal.lean](../SwarmDiameter/ArithmeticRenewal.lean) | The arithmetic renewal limit and its convolution with an absolutely summable sequence. |
| [CycleOccupation.lean](../SwarmDiameter/CycleOccupation.lean) | The normalized occupation law, with its numerator as the expected visit count. |
| [RenewalProcess.lean](../SwarmDiameter/RenewalProcess.lean), [FirstIntervalOccupation.lean](../SwarmDiameter/FirstIntervalOccupation.lean), [DelayedRenewal.lean](../SwarmDiameter/DelayedRenewal.lean) | Occupation limits from the renewal process or just the first-regeneration factorization, and passage through an almost surely finite initial delay. |
| [RegenerationBlocks.lean](../SwarmDiameter/RegenerationBlocks.lean) | Mutual independence from the finite product identities in [Swarm/RegenIid.lean](../Swarm/RegenIid.lean). |
| [RegenerationProbability.lean](../SwarmDiameter/RegenerationProbability.lean) | First-regeneration factorization in time and level and the law of the translated future. |
| [RecordIntervals.lean](../SwarmDiameter/RecordIntervals.lean) | First hitting times, invariance by translation at a simultaneous record, and the diameter bound inside each record interval. |
| [RecordOccupation.lean](../SwarmDiameter/RecordOccupation.lean) | Occupation limits for record-interval events, including exceedances and duration tails. |
| [RecordOccupationBound.lean](../SwarmDiameter/RecordOccupationBound.lean) | The expected visit count before the first regeneration is bounded by record probabilities. |
| [OccupationTail.lean](../SwarmDiameter/OccupationTail.lean) | Stretched exponential bound on the expected visit count from bounds on record interval exceedances and durations. |
| [SwarmUpperGrowth.lean](../SwarmDiameter/SwarmUpperGrowth.lean) | Transfer from the expected visit count to the almost sure logarithmic upper bound and the limiting upper tail. |
| [DyadicTail.lean](../SwarmDiameter/DyadicTail.lean) | A dyadic contraction with a stretched exponential error bounds a tail that tends to zero. |
| [RecordExceedance.lean](../SwarmDiameter/RecordExceedance.lean) | Uniform tightness and the record diameter occupation limit. The initial diameter and duration control exceedances inside each interval, with an additional martingale bound for the two-walker regime. Sharp block estimates suffice for the tails of the initial diameters and durations. |
| [SpatialGapSums.lean](../SwarmDiameter/SpatialGapSums.lean) | The deterministic bound in the spatial sum estimate. Convexity at marked sites reduces the spatial sum to the initial potential and the sum of powers of the gap lengths. |
| [MarkedSpatialTail.lean](../SwarmDiameter/MarkedSpatialTail.lean) | The spatial tail bound in `max-spatial-tail` for the actual row of each walker. The proof uses prescribed geometric gaps and an exponential estimate for the truncated sum of powers. |
| [RecordDensity.lean](../SwarmDiameter/RecordDensity.lean) | Positive lower density of simultaneous records under both laws. |
| [TwoWalkerTrial.lean](../SwarmDiameter/TwoWalkerTrial.lean) | At a simultaneous record the conditional probability of diameter at least $L^2+L$ after $4L+L^3$ steps is at least $e^{-CL}$ for $L\ge8$. |
| [CubicTrial.lean](../SwarmDiameter/CubicTrial.lean) | For $m\ge N\ge3$, the conditional probability of diameter at least $aL^3$ after $4L+L^3$ steps from a simultaneous record is at least $e^{-CL}$ for large $L$. |
| [SwarmLowerBounds.lean](../SwarmDiameter/SwarmLowerBounds.lean) | The almost sure lower bound and limiting lower tail of Theorem 1.2 in all three regimes, with one constant for both lower bounds. |
| [LinearTrial.lean](../SwarmDiameter/LinearTrial.lean) | From a common position at a stopping time $S$, the probability of $\Delta_{S+L}\ge2L$ conditional on the past is at least $(1-p)^{2L}$, expressed by integration on each past event. |
| [SymmetricConfinement.lean](../SwarmDiameter/SymmetricConfinement.lean), [ReflectionExcursion.lean](../SwarmDiameter/ReflectionExcursion.lean) | Finite symmetric-walk path counts for confinement and for an excursion to $L^2$ in $L^3$ steps above $-L$. |
| [TailBounds.lean](../SwarmDiameter/TailBounds.lean) | Borel–Cantelli upper bound and lower-tail transfer from an almost sure lower bound, with the finite-horizon probability estimates stated as premises. |

The record occupation identity is also available at successive record levels.
Write $\tau_r$ for the first visit to level $r$ by any walker,
$W_r=\tau_{r+1}-\tau_r$, and
$\mathcal E_r(x)=\{\exists\,t\in[\tau_r,\tau_{r+1})\colon\Delta_t\ge x\}$.
For an integer $u\ge0$, the formalised upper bound for the expected number of
visits at diameter at least $x$ before $T$ is
$
\mathbb E^*D\left(
u\limsup_{r\to\infty}\mathbb P(\mathcal E_r(x))
+\sum_{v\ge0}\limsup_{r\to\infty}\mathbb P(W_r>u+v)
\right).
$
We truncate each record interval at duration $u$ and sum the integer
duration tails. Using a stretched exponential bound on the expected visit
count, `ae_log_pow_upper_of_regeneration_occupation` proves the almost sure
logarithmic upper bound under the original law.

The sharp upper probability bounds for the record intervals remain open in
Lean. The existing estimate in `M4Blk.paperBadBlockProfile` has exponent
$1/16$ and supplies the tightness used for the qualitative limit.

## Verification

The GitHub Actions workflow replays the model-dependent modules and runs the
focused audit. The arithmetic renewal and finite-walk proofs can also be
replayed with the following command.

```bash
bash scripts/verify_diameter_support.sh
```

With Lean 4.33.1 and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`,
the replay checked 525 declarations in the renewal, trial bounds and
symmetric-walk modules and 627 in the swarm model check. Every imported
declaration in the audited modules depends only on standard Lean axioms.
The source inventory check and all ten verification-tool tests passed.
[Renewal and symmetric-walk check](https://github.com/tuan-minh-nguyen/Swarming-of-interacting-ERWs/actions/runs/44964146200/job/137029254370).
[Record interval and deterministic spatial sum checks](https://github.com/tuan-minh-nguyen/Swarming-of-interacting-ERWs/actions/runs/44965381467).

## References

We prove the positive-mass-at-one case of P. Erdős, W. Feller and H. Pollard,
*A property of power series with positive coefficients*, Bull. Amer. Math. Soc.
55 (1949), 201–204, using the renewal equation and square summability of its
successive differences. For the passage to weak convergence we use Mathlib's
Portmanteau theorem.

We reviewed the Lean repositories below for reusable probability, ergodic
theory and renewal results. The modules in this branch use the existing
Mathlib dependency and the formalisation's own regeneration results.

- [wkshum/ProbabilityTheory](https://github.com/wkshum/ProbabilityTheory/tree/e6387d4fd8005d627d2aec40d10f039ddb4e4b40)
- [marcmorningstar/lean4-ergodic-theory](https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f)
- [or4nge19/MCMC](https://github.com/or4nge19/MCMC/tree/b874137741fbdf23eaac83540b9f79a912a2bc0d)
