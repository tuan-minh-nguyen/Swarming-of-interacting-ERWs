# Swarming of interacting excited random walks

Lean formalisation of Theorems 1.1 and 1.2 of Tuan-Minh Nguyen's manuscript,
*Swarming of interacting excited random walks*.

**Current status (23 November 2026):** Both theorems passed the [GitHub Actions
verification workflow](https://github.com/tuan-minh-nguyen/Swarming-of-interacting-ERWs/actions/runs/45080762725)
on the single branch **main**, at commit
[ea728fa2](https://github.com/tuan-minh-nguyen/Swarming-of-interacting-ERWs/commit/ea728fa2f3d4796fafcbbdeebdc4ee1ca87f51f7).
The workflow completed its source checks, approved diameter statement check,
renewal/occupation support proof replay, 674-module Swarm build, diameter
proof compilation, and trust-level-zero diameter axiom audit. The diameter
audit checked 1,322 declarations and admitted only the foundational axioms
propext, Classical.choice, and Quot.sound. A separate earlier complete
axiom audit for Theorem 1.1 checked 18,376 declarations; see
[the verification record](docs/VERIFICATION.md). No mathematical proof
text was modified during the November 23 repository cleanup.

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
These are two final proof assemblies sharing intermediate results.
All 672 original proof modules and one import-support module belong to
the transitive import closure of Theorem 1.1.

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
Its proof covers all three parameter regimes. The
[proof dependencies](docs/DIAMETER-DEPENDENCIES.md) and
[renewal/occupation support results](docs/DIAMETER-SUPPORT.md)
document the mathematical argument.

The certified workflow
[diameter-checks.yml](.github/workflows/diameter-checks.yml)
compiles the full diameter formalisation and rechecks imported proofs
at trust level zero. The source import audit reports **89 of 91**
diameter source files reachable from the public theorem. 
The additional modules SwarmDiameter.RenewalProcess and
SwarmDiameter.RegenerationBlocks are separately compiled and
axiom-checked as supporting results, and therefore remain in the repository.

## Build and verify

Requirements: [Lean 4.33.1](https://github.com/leanprover/lean4/releases/tag/v4.33.1),
Python 3.9 or newer, Bash, Git, and GNU time. The toolchain file and Lake manifest pin
all dependencies. Mathlib is pinned to
[`0df444a360eaa60ab8c11dca51a86af692955474`](https://github.com/leanprover-community/mathlib4/commit/0df444a360eaa60ab8c11dca51a86af692955474).

From a fresh checkout with `lean` and `lake` on `PATH`:

```bash
lake exe cache get
bash scripts/verify.sh
```

This script verifies Theorem 1.1 in a fresh project-only build with bounded concurrency.
For a separate build with recorded timings:

```bash
python3 scripts/build.py --work .scratch/source-build --jobs 2
```

Choose a new work directory for every such build. This command compiles the sources for Theorem 1.1 using the pinned dependency
artifacts and the new output directory. It does not compile or remove dependency artifacts. Ordinary
incremental builds remain available through `lake build`.

The verification script checks the source inventory for Theorem 1.1 and both
exports of that theorem from a separate importing module. It audits the
transitive axiom dependencies of every declaration in the imported project modules. Its
last Lean invocation uses trust level zero to recheck imported proofs. The
permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.
Diagnostic commands belong to the separate `audit` directory. The build
logs and per-module timing records are written under `.scratch`.

The dated [verification record](docs/VERIFICATION.md) describes Theorem 1.1 statement checks,
axiom coverage, and [release review](docs/RELEASE-REVIEW.md). The
[14 November elaboration report](docs/ELABORATION_REPORT_2026-11-14.md) records historical Theorem 1.1 measurements only; it is not a matched before/after timing study for the expanded diameter repository.

## Source correspondence

The source for Theorem 1.1 is `main_1d_revised.tex`, identified by SHA-256
`65afa8e87670bcf9c9d8261c6b23a5323ae41c51c33794c42dd26c49a0603a37`.
The [diameter statement manifest](docs/diameter-statement.json) identifies the source of Theorem 1.2 as `main_1d_regeneration_revised.tex` and pins its approved signature.

[docs/source-map.json](docs/source-map.json) records each original source path
and hash, its present module, and a hash of the proof text excluding comments,
imports, and diagnostic commands. These hashes check preservation of the
supplied proof text; they do not establish mathematical correspondence by
themselves. The independent statement and definition review is recorded in
[docs/STATEMENT-REVIEW.md](docs/STATEMENT-REVIEW.md).

For conditional independence with respect to the revealed sigma-algebra,
see `Swarming.Enl.enl_fresh_law` and `Swarming.Enl.condExp_pattern_enl` in
[Swarm/EnlLaw.lean](Swarm/EnlLaw.lean) and
[Swarm/EnlJoint.lean](Swarm/EnlJoint.lean). Earlier product identities on
exact real-valued histories can concern events of probability zero.

## Errata and deviations

The [dated review](docs/ERRATA-AND-DEVIATIONS.md) identified no manuscript errata in the statements and definitions it examined and records
four deviations or scope conventions: `Fin N` indexing, unused zeroth array
coordinates, total division at time zero, and the scope of the original Theorem 1.1
proof closure. Both main theorem statements are preserved.

## Attribution and license

The supplied [third-party notices](THIRD_PARTY_LICENSES.txt) are preserved.
Mathlib and its dependencies retain their own licenses and attribution.
The original archive contained no overall license for this formalisation;
no new license has been assigned to it here. The manuscript is a separate work.
