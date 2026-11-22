# Swarming of interacting excited random walks

Lean formalisation of Theorems 1.1 and 1.2 of the manuscript
*Swarming of interacting excited random walks*.

## Model

All $N$ walkers start at zero on the integers, where $N\ge2$.
For walker $j$, let $L_n^j(x)$ count its visits to $x$ up to and including time $n$.
At time $n$, walker $i$ at $x$ jumps right with probability

```math
\begin{cases}
p,& \text{if }\sum_{j\ne i}L_n^j(x)\ge m,\\
\frac12,&\text{otherwise},
\end{cases}
```

where $m\ge 2$ is an integer and $\frac12<p<1$. All walkers jump
simultaneously. Independent uniform random variables drive their jumps.
The definitions are in [UniformArray.lean](Swarm/UniformArray.lean)
and [Trajectory.lean](Swarm/Trajectory.lean).

## Theorem 1.1 — Common deterministic speed

For every integer $m\ge 2$ and $\frac12<p<1$, there exists a deterministic
constant $\kappa(m,p)>0$, independent of $N$, such that for every $N\ge2$
there exists a deterministic speed $v_N(m,p)$ satisfying

```math
\kappa(m,p)\le v_N(m,p)\le 2p-1,
\qquad
\lim_{n\to\infty}\frac{X_n^i}{n}=v_N(m,p)
\quad\text{almost surely for every }1\le i\le N.
```

The formal declarations are `M4Blk.main_claim` and
`M4Blk.main_claim_direct` in [BlkMeasure.lean](Swarm/BlkMeasure.lean).

## Theorem 1.2 — Swarm diameter

Define the diameter and running maximum by

```math
D_n=\max_{1\le i,j\le N}|X_n^i-X_n^j|,
\qquad M_n=\max_{0\le k\le n}D_k.
```

Set

```math
\beta=
\begin{cases}
2,&N=2,\\
1,&2\le m<N,\\
3,&3\le N\le m.
\end{cases}
```

There exist constants $c>0$, $C\ge1$, and a probability measure
$\nu$ on $[0,\infty)$ such that, almost surely, for all sufficiently
large $n$,

```math
C^{-1}(\log n)^\beta\le M_n\le C(\log n)^\beta.
```

Moreover, $D_n$ converges in distribution to $\nu$, and for all
sufficiently large $x$,

```math
\exp(-Cx^{1/\beta})\le \nu([x,\infty))
\le \exp(-cx^{1/\beta}).
```

The theorem is [Swarming.swarm_diameter](SwarmDiameter/Main.lean).
Its proof covers all three parameter regimes.

## Verification

The project uses Lean 4.33.1 with dependencies pinned in
[lean-toolchain](lean-toolchain) and [lake-manifest.json](lake-manifest.json).
After restoring the Mathlib cache, verify Theorem 1.1 with:

```bash
lake exe cache get
bash scripts/verify.sh
```

Theorem 1.2 can be built with `lake build SwarmDiameter`. The
[GitHub Actions workflow](.github/workflows/diameter-checks.yml)
also checks its approved statement and replays the proofs with Lean trust
level zero. The project checks permit only the foundational axioms
`propext`, `Classical.choice`, and `Quot.sound`.

The [verification record](docs/VERIFICATION.md) documents the successful
proof checks. See [Theorem 1.2 proof dependencies](docs/DIAMETER-DEPENDENCIES.md),
[renewal and occupation results](docs/DIAMETER-SUPPORT.md), and the
[statement review](docs/STATEMENT-REVIEW.md) for further details.

## Attribution and license

The supplied [third-party notices](THIRD_PARTY_LICENSES.txt) are preserved.
Mathlib and its dependencies retain their own licenses and attribution.
The original archive contained no overall license for this formalisation;
no new license has been assigned to it here. The manuscript is a separate work.
