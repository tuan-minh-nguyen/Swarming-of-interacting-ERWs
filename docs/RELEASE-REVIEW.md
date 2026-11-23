# Release review — Theorem 1.1 (14 November 2026)

This is a historical review of the original Theorem 1.1 release, not a
current whole-repository certification or a new performance benchmark.
The project subsequently adopted [Apache License 2.0](../LICENSE);
statements about the absence of a project license below describe only
this earlier review.
For the successful 23 November 2026 checks of Theorems 1.1 and 1.2, see
[the current verification record](VERIFICATION.md#current-repository-certification--23-november-2026)
and the [repository README](../README.md).

We independently reviewed the main theorem and model against the supplied
manuscript, and separately reviewed the proposed release files and verification
tools. The statement review is in [STATEMENT-REVIEW.md](STATEMENT-REVIEW.md).
The runtime results are in [VERIFICATION.md](VERIFICATION.md).

## Static checks

- All 672 original file hashes and normalized proof-text reference hashes match
  the supplied archive. All 673 current source-map entries pass the preservation
  check, including the import-only support module.
- Every production module is reachable from the main theorem import. The facade
  contains only that import. No active proof diagnostic remains in production.
- The two exact consumer types match the manuscript's main theorem, including
  the lower bound chosen before the population size and a common deterministic
  speed for all walkers.
- The source checker passes normally and under Python optimization. All ten
  verification-tool regressions pass. The verification shell script passes
  syntax checking.
- Relative documentation links resolve. GitHub-unsupported custom math macros
  and private source paths were checked. Process identifiers were removed from
  comments without altering proof text.
- The supplied third-party notices are byte-identical. No new overall license
  has been assigned.

## Findings and disposition

| Finding | Disposition |
|---|---|
| Python optimization could remove assertion-based integrity checks | Explicit conditionals now fail under both normal and optimized execution. |
| Import scanning omitted additional names or indented imports | One shared parser reads every name and rejects unsupported syntax. |
| Comment delimiters inside string literals could hide subsequent code | Literal and interpolation handling is separate from comments; the reproduced cases are regression checks. |
| A positive declaration count alone could hide incomplete audit coverage | The audit also requires all 673 expected project modules. |
| Successful process status did not establish that a build artifact existed | The builder requires the artifact and records its hash. |
| Development cache reuse needed source and dependency validation | Reuse validates source, artifact, setup, and dependency closure; release runs use fresh output directories. |
| Ordinary proof files repeated diagnostics on each build | All 2,037 diagnostics were removed; the separate audit covers every project declaration. |
| Exact-history identities were described as conditional laws | Comments now distinguish these identities from conditional laws for the revealed sigma-algebra. |
| A raw auxiliary potential was identified with the current manuscript’s projected potential | The comments now distinguish the objects; the [projection note](PROOF-ROUTE-NOTE.md) records the source comparison without asserting a manuscript erratum. |

During runtime validation we also made the new audit counters explicitly
natural numbers. The final audit compiles and checks all 18,376 declarations.

## Runtime acceptance

The separate checkout rebuilt all 674 production modules without reused project
artifacts. Both fully explicit consumer terms and both five-binder checks pass.
The ten named axiom reports and the complete declaration audit pass. The final
run rechecks imported proofs at trust level zero. All dependencies are pinned,
and no dependency module was compiled during the measured project build.

## Scope

The source-level review concerns Theorem 1.1 and the literal model definitions.
It is not an independent proof of each auxiliary manuscript assertion. The two
final proof routes share dependencies. The axiom check and imported-proof
replay use Lean 4.33.1, rather than a second implementation of its proof checker.
The formalisation's original proof text is retained; its public module paths,
imports, comments, documentation, and verification tools have been revised.
