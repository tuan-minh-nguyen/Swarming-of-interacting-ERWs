# Verification of both principal theorems

Verified at proof-source commit
`94cc7117c363aaa51a72d88d7afabd711025d4fa`, from a fresh detached checkout
of the connected GitHub repository. Subsequent changes to this documentation
do not change the mathematical or verifier sources.

## Statements checked

Reference manuscript: `main_1d-3.tex`, SHA-256
`b1727fd4da2a57742e79dcab6944c2d3e491ab5fcb93ad06036ca656bfa34ec1`.

| Statement | Lean export | Result |
|---|---|---|
| Common deterministic positive speed with one lower bound before $N$ | `M4Blk.main_claim`, `M4Blk.main_claim_direct` in [Swarm/BlkMeasure.lean](../Swarm/BlkMeasure.lean) | Exact consumer statements passed; no additional premises |
| Running diameter logarithmic bounds, nonnegative limiting law and both tail bounds | `Swarming.swarm_diameter` in [SwarmDiameter/Main.lean](../SwarmDiameter/Main.lean) | Complete diameter replay and axiom check passed |

The two speed declarations are alternative final assemblies from shared
dependencies. Both use the actual trajectory under
`Swarming.Uniform.arrayMeasure N`. For the diameter, the actual path witness
`posPath p m U n i` is `(Swarming.Trajectory.trajectory p m U n).pos i`.
The running maximum ranges over $0,\ldots,n$; the three regimes are
$N=2$, $N\ge3,m<N$, and $N\ge3,m\ge N$, with exponents $2,1,3$.

See [statement and model correspondence](STATEMENT-REVIEW.md) and the
[auxiliary-process distinction](PROOF-ROUTE-NOTE.md) for the scope of the
correspondence checks. This record does not claim a separate audit of every
auxiliary theorem in the manuscript.

## Completed checks

Toolchain: Lean 4.33.1. Mathlib pinned at
`0df444a360eaa60ab8c11dca51a86af692955474`.
The core build was fresh and non-resumed, using the restored pinned dependency
cache but no pre-existing project objects.

| Check | Result |
|---|---|
| Source inventory and proof-text preservation | 673 modules; complete closure |
| Main project build | 674/674 project modules |
| Main named axiom and statement checks | 10 reports; both exact consumers passed |
| Complete Swarm axiom audit at trust zero | 18,376 declarations |
| Independent renewal/occupation supporting audit | 525 declarations |
| Diameter replay using the repository's CI order | 91 modules; 89/91 in the main import closure and two separate support modules |
| Diameter axiom audit at trust zero | 1,322 declarations |
| Final three-export check | 3/3 only allowed foundational axioms |
| Verifier regression tests | 10/10 passed |

The allowed axiom set is exactly `propext`, `Classical.choice`, and
`Quot.sound`. No custom axioms or proof holes were accepted in these
declarations or their inspected transitive dependencies.

The source inventories, mathematical exports and reproduction commands are in
the root [README](../README.md). The proofs are not two independent
reconstructions of all supporting lemmas.

## Reproduction and evidence

Follow the root [verification commands](../README.md#verification) and
[CI definition](../.github/workflows/diameter-checks.yml). Use
[audit/TwoTheorems.lean](../audit/TwoTheorems.lean) to re-check the three
principal exports.

Evidence retained on GitHub:

- [machine-readable certificate](verification-94cc7117.json).
- [full main verifier log](verification/94cc7117/main-verify.log).
- [supporting replay log](verification/94cc7117/diameter-support-verify.log).
- [diameter replay and audit log](verification/94cc7117/diameter-verify.log).
- [exported statements and final axiom log](verification/94cc7117/final-export-types-and-axioms.log),
including the printed `posPath` definition.
