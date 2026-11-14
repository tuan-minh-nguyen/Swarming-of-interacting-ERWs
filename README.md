# Swarming of interacting excited random walks

Lean formalisation of Theorem 1.1 of Tuan-Minh Nguyen's manuscript,
*Swarming of interacting excited random walks*.

For every threshold $m\ge2$ and parameter $1/2\lt p\lt1$, we prove that all
walkers have a common deterministic positive speed. We choose the positive
lower bound before the population size $N$, so the bound is uniform in $N$.
The construction starts every walker at zero and uses independent uniform
random variables. Local times include visits at time zero, and walkers jump
simultaneously.

The main declarations are `M4Blk.main_claim` and `M4Blk.main_claim_direct` in
[Swarm/BlkMeasure.lean](Swarm/BlkMeasure.lean). There are 672 original proof modules and one import-support module,
all in the transitive import closure of the main result. The second declaration follows a
different final assembly from the first; the proofs share substantial
dependencies.

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

The verification script runs a fresh project-only build with bounded concurrency.
For a separate build with recorded timings:

```bash
python3 scripts/build.py --work .scratch/source-build --jobs 2
```

Choose a new work directory for every such build. This command compiles all
project sources using only the pinned dependency artifacts and the new output
directory. It does not compile or remove dependency artifacts. Ordinary
incremental builds remain available through `lake build`.

The verification script checks the complete source inventory, builds the
project, checks both main statements from a separate importing module, and
audits the transitive axiom dependencies of every project declaration. Its
last Lean invocation uses trust level zero to recheck imported proofs. The
permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.
Diagnostic commands belong to the separate `audit` directory. The build
logs and per-module timing records are written under `.scratch`.

The [verification record](docs/VERIFICATION.md) describes the statement checks,
axiom coverage, and [release review](docs/RELEASE-REVIEW.md). The
[elaboration report](docs/ELABORATION_REPORT_2026-11-14.md) records the measured
import improvement and the full-build methodology.

## Source correspondence

The reference is the supplied `main_1d_revised.tex`, identified by SHA-256
`65afa8e87670bcf9c9d8261c6b23a5323ae41c51c33794c42dd26c49a0603a37`.
The manuscript is not included in this code repository.

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

The [record](docs/ERRATA-AND-DEVIATIONS.md) lists zero manuscript errata and
four deviations or scope conventions: `Fin N` indexing, unused zeroth array
coordinates, total division at time zero, and the restriction to the main
theorem's proof closure. The main mathematical statement is unchanged.

## Attribution and license

The supplied [third-party notices](THIRD_PARTY_LICENSES.txt) are preserved.
Mathlib and its dependencies retain their own licenses and attribution.
The original archive contained no overall license for this formalisation;
no new license has been assigned to it here. The manuscript is a separate work.
