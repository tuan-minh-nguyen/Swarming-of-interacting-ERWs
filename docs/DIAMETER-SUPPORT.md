# Diameter: essential supporting facts

For the swarm's diameter $\Delta_t$, use the actual trajectory positions.
The principal export is
[`Swarming.swarm_diameter`](../SwarmDiameter/Main.lean). Its three regimes are
proved: $N=2$, $N\ge3,m<N$, and $N\ge3,m\ge N$. In particular,
[`swarm_diameter_linear`](../SwarmDiameter/SwarmDiameterLinear.lean) supplies
the full exponential estimate in the second regime; it is **not** an open case.

Write $T=\tau_D$ for the first positive regeneration time and
$\mathbb P^*$ for the law conditioned on strict positivity, with expectation
$\mathbb E^*$. The limiting law has the occupation formula
$$
\nu(A)=\frac1{\mathbb E^*T}\sum_{t\ge0}
\mathbb P^*(T>t,\ \Delta_t\in A),
$$
for Borel $A\subseteq\mathbb R$. This is the conclusion supplied by
`Swarming.Diameter.exists_diameter_occupationLaw`. The renewal construction
also yields $\mathbb P^*(T=1)>0$ and $\mathbb E^*T<\infty$.

The two supplementary implementations,
[RenewalProcess.lean](../SwarmDiameter/RenewalProcess.lean) and
[RegenerationBlocks.lean](../SwarmDiameter/RegenerationBlocks.lean), are
covered by the separate renewal/occupation supporting audit, while the
remaining diameter modules are covered by the theorem replay. The common
witness for the almost-sure bounds, limiting law and both tails is in
[Main.lean](../SwarmDiameter/Main.lean).

For reproduction use the verification commands in the root
[README](../README.md#verification). The current counts and raw logs are kept
in [VERIFICATION-94cc7117.md](VERIFICATION-94cc7117.md), rather than repeated
in this note.
