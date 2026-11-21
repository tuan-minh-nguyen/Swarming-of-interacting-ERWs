# Renewal and occupation for the swarm diameter theorem

The reference is Theorem 1.2 of `main_1d_regeneration_revised.tex`, with
SHA-256 `1ea00e1c34ca56655cf84d8307d74247cb135dbbda61295038256505f2b44e6b`.
Here we formalise the renewal argument in Section 4, including the calculation
in equation (4.13) for an observation from independent and identically
distributed intervals.

For intervals of positive integer duration $D$, write $p_j=\mathbb P(D=j+1)$
and $u_n=\sum_{k\ge0}\mathbb P(S_k=n)$, where $S_k$ is the start time of interval
$k$ and $S_0=0$. The proofs assume $p_0>0$ and $\mathbb E D<\infty$. For an
observation $Y_t$ at age $t$ in one interval and a measurable set $A$, the
limiting probability is
$$
\frac{1}{\mathbb E D}\sum_{t\ge0}\mathbb P(D>t,\ Y_t\in A).
$$

| Module | Main result |
| --- | --- |
| [ArithmeticRenewal.lean](../SwarmDiameter/ArithmeticRenewal.lean) | `renewalMass_tendsto` and `renewalReward_tendsto_mean` prove the renewal limit and its convolution with an absolutely summable sequence. |
| [CycleOccupation.lean](../SwarmDiameter/CycleOccupation.lean) | `occupationLaw_real_apply` identifies the normalized occupation measure on every measurable set. |
| [RenewalProcess.lean](../SwarmDiameter/RenewalProcess.lean) | `renewalMass_eq_sum_renewalTime_prob` identifies the renewal mass with the arrival probabilities. The last-renewal partition in `observation_prob_eq_renewalReward` leads to `tendstoInDistribution_occupationLaw`. |
| [FirstIntervalOccupation.lean](../SwarmDiameter/FirstIntervalOccupation.lean) | `observation_prob_tendsto_of_first_interval` proves the occupation limit from the first-regeneration factorization. |
| [DelayedRenewal.lean](../SwarmDiameter/DelayedRenewal.lean) | `observation_prob_tendsto_of_delay` transfers the limiting probabilities through an almost surely finite initial regeneration. |
| [RegenerationBlocks.lean](../SwarmDiameter/RegenerationBlocks.lean) | `KacFormula.iIndepFun_of_fresh` proves mutual independence from the finite product identities in [Swarm/RegenIid.lean](../Swarm/RegenIid.lean). |

For the swarm application, the intervals and observations must be identified
with the regeneration times and diameters of the interacting walks. The proof
still needs this identification, the hypotheses for applying the renewal
theorem to that law, and the transfer from the process conditioned to stay
positive to the original process. The sharp occupation and excursion
estimates in Section 4 and the almost sure bounds also remain open in Lean.
The exponent $1/16$ in `M4Blk.paperBadBlockProfile` is weaker than the exponents
required in the revised manuscript.

## Verification

With the pinned Mathlib artifacts available, run

```bash
bash scripts/verify_diameter_support.sh
```

[GitHub Actions run 44884167585](https://github.com/tuan-minh-nguyen/Swarming-of-interacting-ERWs/actions/runs/44884167585)
built the support modules with Lean 4.33.1 and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. Lean replayed and audited 217
declarations at trust level zero. The source inventory check and all ten
verification-tool tests passed. The swarm-specific proof of the diameter
theorem is in development.

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
