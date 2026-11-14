# Verification record

Date: 14 November 2026 (Melbourne).

## Reference and scope

We checked the supplied `lean.zip`, SHA-256
`41f9b2741f4089a47498e25a12383fd15f3ade21a014a42e2c0abafa8dd56ed8`,
against `main_1d_revised.tex`, SHA-256
`65afa8e87670bcf9c9d8261c6b23a5323ae41c51c33794c42dd26c49a0603a37`.
The target is Theorem 1.1, LaTeX label `main`, for the strong construction in
`uniform`. We reviewed the main statement and model definitions independently
of the implementation's proof. This is not a separate audit of every informal
argument in the manuscript.

We retained all 672 original proof modules. One import-support module and one
library facade complete the 674-module production build. The source map
records both the original file hashes and normalized proof-text hashes. All
original proof text is unchanged, excluding comments, imports, and diagnostic
commands. Existing declaration names and resource-limit directives are retained.

## Main statements and model

Both exports, `M4Blk.main_claim` and `M4Blk.main_claim_direct`, have exactly
five explicit outer binders: `p`, `m`, `hp0`, `hp1`, and `hm`. There are no
additional outer type-class or universe parameters. Separate consumer proofs
use the fully explicit constants `@M4Blk.main_claim` and
`@M4Blk.main_claim_direct` at the manuscript's exact type.

The positive lower bound precedes the population size. The deterministic common
speed precedes the sampled array, and all walkers share one probability-one
event. The array is the actual product uniform measure, and the trajectory is
its actual recursive construction, with inclusive local times, visits summed
only over other walkers, and simultaneous jumps from the old state.

The [independent statement review](STATEMENT-REVIEW.md) contains the binder
classification and definition-by-definition source comparison. The four
implementation and scope conventions are recorded in
[Errata and deviations](ERRATA-AND-DEVIATIONS.md).

## Axiom and source checks

The production tree contains no active proof holes, custom-axiom declarations,
or native compiler-trust shortcuts. The separate named audit checks all eight
declarations in the principal theorem file and both exact consumer statements.
Their transitive axiom dependencies are exactly the permitted foundations:
`propext`, `Classical.choice`, and `Quot.sound`.

The complete imported-project audit checks 673 source modules and 18,376
project declarations, including auxiliary definitions and declarations outside
the main namespace. Every transitive axiom dependency is in the same allowlist.
The facade contains only its principal import and introduces no declaration.

The verification-tool regressions cover empty and incomplete axiom logs,
nonstandard axioms, proof holes after nested comments and string literals,
interpolation, modified axiom declarations, all names on an import line, and
Python optimization. All ten cases pass. Integrity checks use explicit failures
and remain active under `python3 -O`.

## Fresh-checkout result

The full documented verifier passed in a separate detached checkout. We
restored its pinned dependencies separately and began with no project proof
artifacts. All 674 modules were rebuilt, with zero reused project artifacts,
and the trust-level-zero audit passed for all 18,376 declarations. The complete
run took 20 minutes 41 seconds with two single-threaded workers. The build
reported zero errors and 744 nonfatal compiler/linter warnings. We subsequently
clarified comments in two modules, rechecked both modules, and reran the exact
main-statement checks and trust-level-zero declaration audit successfully. The
mathematical proof text is unchanged.

## Reproduction

The exact toolchain is Lean 4.33.1. Mathlib and its eight dependencies are pinned
in [lake-manifest.json](../lake-manifest.json). No CSLib installation or ambient
project search path is needed.

```bash
lake exe cache get
SWARM_BUILD_JOBS=2 bash scripts/verify.sh
```

Dependency cache restoration is a separate setup step. The verifier builds only
project sources, with one Lean thread per process and at most two concurrent
processes in the command above. The default is one process. Every release run
uses a new output directory. Only that directory and Lake's declared dependency
paths are available to the audits. Development resume functionality is not
used in a release run.

The last audit uses `lean -t0`, which rechecks imported proofs. This uses the
same Lean implementation; it is not a comparator or a second proof-checking
implementation.

## Independent review and changes

The independent review found and we corrected verification-tool defects in
comment stripping, import parsing, optimization-sensitive assertions, coverage,
and build-output validation. We also corrected descriptions of exact-history
identities: identities on singleton real-valued histories alone are not
conditional laws for the revealed sigma-algebra. The genuine conditional laws
are proved in `Swarming.Enl.enl_fresh_law` and
`Swarming.Enl.condExp_pattern_enl`. Their mathematical statements and proofs
are unchanged.

We preserved the supplied third-party notices byte for byte. The original
archive supplied no overall license for the formalisation; no new license or
repository visibility change is part of this verification.
