# Verification of the two principal theorems

**Result: passed at GitHub commit `94cc7117c363aaa51a72d88d7afabd711025d4fa`.**

Checked locally from a fresh detached checkout of the connected GitHub
repository, not inferred from its historical verification report. This commit
adds only Lean verification evidence; README.md and the mathematical source
remain unchanged.
The mathematical and verifier sources were unchanged during these checks. No Ultramath run was used.

## Paper and exports

Manuscript: `attachments/improving-and-polishing-the-wcjf/main_1d-3.tex`,
SHA-256 `b1727fd4da2a57742e79dcab6944c2d3e491ab5fcb93ad06036ca656bfa34ec1`.

| Paper statement | Lean export | Verification scope |
|---|---|---|
| `\label{main}`: common deterministic positive speed, with one positive lower bound before $N$ | `M4Blk.main_claim` and `M4Blk.main_claim_direct`, `Swarm/BlkMeasure.lean` | Both exact consumer statements, no additional premises, all axiom checks |
| `\label{maxdistance}`: running logarithmic diameter bounds, nonnegative limiting law, convergence in distribution and tail bounds | `Swarming.swarm_diameter`, `SwarmDiameter/Main.lean` | Complete diameter build, independent support replay and axiom checks |

The two `M4Blk` declarations are alternative final assemblies from shared
dependencies; they are not called independent proofs of all intermediate
lemmas. The positive lower bound precedes $N$ and both speed declarations use
the actual trajectory under `Swarming.Uniform.arrayMeasure N`.

For the diameter export, `spreadZ` computes the maximum position minus the
minimum. Its running maximum ranges exactly over times $0,\ldots,n$. The
printed `posPath` definition is
`(Swarming.Trajectory.trajectory p m U n).pos i`, so its population is not a
surrogate process. The three branches match the paper:

* $N=2$: logarithmic exponent $2$ and tail exponent $1/2$;
* $N\ge3$, $m<N$: exponent $1$ and tail exponent $1$;
* $N\ge3$, $m\ge N$: logarithmic exponent $3$ and tail exponent $1/3$.

The limiting law, convergence and tail inequalities share one witness, as
required. These correspondences were also read against the attached
manuscript, not inferred only from declaration names.

## Fresh checks actually completed

Toolchain: **Lean 4.33.1**. Mathlib: pinned commit
`0df444a360eaa60ab8c11dca51a86af692955474`. No existing project compiled
object was supplied: the core build was fresh and non-resumed.

| Check | Completed result |
|---|---|
| Source inventory / proof text | **673 modules; complete closure** |
| Diameter declaration and source scan | **91 files; 89/91 in main import closure; other two covered separately** |
| Verifier tests | **10/10 passed** |
| Fresh Swarm build | **674/674 project modules** |
| Named main statement and axiom checks | **10 reports; two exact consumers passed** |
| Trust-zero complete Swarm axiom audit | **18,376 declarations** |
| Independent renewal/occupation supporting audit | **525 declarations** |
| Diameter replay using the repository's CI order | **91 modules** |
| Trust-zero diameter axiom audit | **1,322 declarations** |
| Final check of the three named exports | **3/3 only allowed foundational axioms** |

All inspected transitive axiom dependencies use only `propext`,
`Classical.choice`, and `Quot.sound`. There are no extra assumptions or
custom axioms in these results. The directed import checks for the diameter
cover `RenewalProcess` and `RegenerationBlocks` with their distinct
renewal/occupation supporting replay rather than silently omitting them.

## Scope

This certifies **both named statements and their Lean source dependency
closures** through elaboration and kernel checking. It is not a separate
rewriting, formal reconstruction, or whole-paper editorial audit of every
auxiliary proposition. Historical verification notes in the repository may
name different commits; this audit is specifically for the revision above.

## Evidence

- `certificate.json`: machine-readable revision, commands and counts.
- `TwoTheorems.lean`: exact final consumer/print module.
- `final-export-types-and-axioms.log`: exact exported types, actual `posPath`
  definition and the three final axiom closures.
- `main-verify.log`: complete fresh main-project verifier.
- `diameter-support-verify.log`: independent supporting replay
- `diameter-verify.log`: module-by-module replay and final diameter audit.

To reproduce, check out the named repository revision and run its
`scripts/verify.sh`, `scripts/verify_diameter_support.sh`, and the build/audit
stages specified in `.github/workflows/diameter-checks.yml`.
