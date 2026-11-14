# Elaboration report — 14 November 2026

## 1. Setup and provenance

We used Lean 4.33.1 on Linux x86-64, with nine available processors and about
9.7 GiB RAM. Mathlib is pinned to
`0df444a360eaa60ab8c11dca51a86af692955474`. The supplied source archive and
manuscript hashes are recorded in [VERIFICATION.md](VERIFICATION.md).

We measured individual Lean processes with GNU time, and used Lean's
`--profile` output for phase attribution. We ran the import comparison serially,
interleaving the two variants three times. No other Lean process ran during
those comparisons. The full project build uses two processes, each with one
Lean thread. Dependency restoration precedes the measured project build.


## 2. Source size and build scope

| Quantity | Count |
|---|---:|
| Tracked Lean files, including audits and Lake configuration | 677 |
| Physical lines | 222,347 |
| Non-comment, nonblank code lines | 164,531 |
| Comment-only files | 0 |
| Original proof modules | 672 |
| Additional import-support module | 1 |
| Library facade | 1 |
| Production compilation targets | 674 |

We counted the committed source snapshot through `git ls-tree` and `git show`,
with nested comments and literals handled by the source scanner. We retained
the legacy Lean import/export conventions in 676 files, excluding the Lake
configuration. The audit files are separate from the production import graph.


## 3. Fresh-build measurements

We ran the documented verifier in a detached source checkout with separately
cloned pinned dependencies, a restored dependency cache, and zero project proof
artifacts. Every project artifact was rebuilt; no development resume was used.

| Quantity | Measurement |
|---|---:|
| Production modules | 674 |
| Compilation wall time | 1225.13 s |
| Complete verifier wall time | 1,241.33 s (20 min 41 s) |
| Complete verifier user CPU | 1,993.80 s |
| Complete verifier system CPU | 339.82 s |
| Complete verifier CPU utilization | 187% |
| Sum of project-module CPU | 2309.24 s |
| Sum of per-module elapsed time | 2329.57 s |
| Implied worker parallelism | 1.901 |
| Largest module peak RSS | 3.70 GiB |
| Largest process peak RSS, including audits | 3.88 GiB |
| Build errors | 0 |
| Compiler/linter warnings | 744 |
| Reused project artifacts | 0 |

At two single-threaded workers the CPU work floor is 1154.62
seconds; the measured weighted import-chain estimate is
508.94 seconds. This configuration is limited primarily by
total work. The chain estimate uses concurrent-build per-file elapsed times
and is not a separate uncontended lower-bound experiment. RSS values are
per-process maxima, not aggregate memory across both workers.

## 4. Build health

We removed 2,037 active `#print axioms` and `#check` commands from production
files. The separate audit checks every project declaration's axiom dependencies,
so coverage extends beyond the former selection of printed declarations.
This is a verification and output change; no separate timing gain is attributed
to diagnostic removal.

We preserved existing heartbeat settings and mathematical proof text. No resource
limit increase is counted as an optimization. An early two-process trial at
`-M 3500` stopped at Lean's configured memory threshold while loading Mathlib.
The serial baseline check and both measured variants use `-M 8000`.


All 674 production targets pass. Both consumer statements, both five-binder
checks, the ten named axiom reports, and the trust-level-zero imported-proof
recheck pass. The complete axiom audit covers 18,376 project declarations.
There are no proof-hole warnings. The existing nonfatal warning census is:

| Kind | Count |
|---|---:|
| style suggestions | 212 |
| unused named variables | 177 |
| deprecated syntax or declarations | 120 |
| unused section variables | 110 |
| unused simp arguments | 86 |
| unnecessary simpa | 11 |
| Unused tactic linter: `push_cast` does nothing | 8 |
| Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice | 7 |
| class-definition reducibility | 2 |
| Unused tactic linter: `norm_num at hLge4 ⊢` does nothing | 2 |
| this tactic is never executed | 2 |
| Unused tactic linter: `push_cast at hk ⊢` does nothing | 1 |
| The namespace `SlowBlock` is duplicated in the declaration `SlowBlock.SlowBlock`. | 1 |
| Unused tactic linter: `linarith` does nothing | 1 |
| Try `simp at h` instead of `simpa using h` | 1 |
| Unused tactic linter: `push_cast at h ⊢` does nothing | 1 |
| Unused tactic linter: `push_cast at hs1 ht1 ⊢` does nothing | 1 |
| Unused tactic linter: `norm_num` does nothing | 1 |

## 5. Heavy tail

| Elapsed threshold | Modules |
|---|---:|
| At least 10 s | 18 |
| At least 20 s | 8 |
| At least 30 s | 6 |
| At least 40 s | 3 |

The thirty slowest production targets are:

| Module | Elapsed seconds | CPU seconds |
|---|---:|---:|
| `Swarm.RecordCarrierPaperScale` | 56.73 | 56.62 |
| `Swarm.LocOccSingleWindow` | 53.55 | 53.44 |
| `Swarm.LocOccSingleWindowAllPairs` | 51.71 | 51.58 |
| `Swarm.SummedSlope` | 35.56 | 35.51 |
| `Swarm.LocStartRange` | 31.55 | 31.49 |
| `Swarm.LocOccProjected` | 30.76 | 30.67 |
| `Swarm.LocOccFibreSum` | 29.00 | 29.00 |
| `Swarm.LocGroupSimultaneous` | 20.08 | 20.00 |
| `Swarm.R4Assemble` | 18.87 | 18.82 |
| `Swarm.MpotMain` | 17.70 | 17.65 |
| `Swarm.LocalGoodFamily` | 15.43 | 15.38 |
| `Swarm.WindowLe` | 13.99 | 13.95 |
| `Swarm.ClockLocMoveExp` | 13.34 | 13.28 |
| `Swarm.Smom4Main` | 13.14 | 13.09 |
| `Swarm.LocOccEndpoint` | 11.69 | 11.67 |
| `Swarm.ProjHSpatial` | 11.64 | 11.61 |
| `Swarm.LocCoordPaper` | 11.21 | 11.18 |
| `Swarm.CoincideClass` | 10.16 | 10.14 |
| `Swarm.CondBC` | 9.63 | 5.67 |
| `Swarm.RecClockLocgroup` | 9.62 | 9.57 |
| `Swarm.LocOccCarrierAssembly` | 9.60 | 9.59 |
| `Swarm.JoinSub` | 9.27 | 9.25 |
| `Swarm.RecordClockTail` | 9.06 | 9.03 |
| `Swarm.S13` | 9.05 | 9.00 |
| `Swarm.SharpClass` | 8.93 | 8.90 |
| `Swarm.PaperScale` | 8.81 | 8.77 |
| `Swarm.LocMoveT3` | 8.65 | 8.61 |
| `Swarm.QplWindow` | 8.57 | 8.55 |
| `Swarm.SiteDiffStatic` | 8.47 | 8.43 |
| `Swarm.RawSecondMoment` | 8.37 | 8.35 |

## 6. Source-area CPU

Areas refer to the original source ownership recorded in the source map.

| Area | Modules | CPU seconds |
|---|---:|---:|
| martingale | 134 | 824.83 |
| tightness | 137 | 427.92 |
| kac | 124 | 274.81 |
| filtration | 68 | 175.54 |
| spatialavg | 33 | 119.76 |
| transience | 45 | 115.23 |
| occupation | 24 | 93.63 |
| assembly | 34 | 83.58 |
| marks | 17 | 61.17 |
| base | 22 | 48.11 |
| recordkernel | 13 | 27.37 |
| symmetric | 6 | 14.38 |
| reflection | 5 | 11.40 |
| invariance | 4 | 10.06 |
| pathfilt | 4 | 8.06 |
| recordo | 1 | 5.77 |
| support | 2 | 4.67 |
| spatial | 1 | 2.95 |

## 7. Serial own-file profiles

After the build and audits finished, we rechecked the five slowest files
serially, one at a time, without object serialization or concurrent Lean jobs.

| Module | Wall | Import | Interpretation | Type-class inference | Simp |
|---|---:|---:|---:|---:|---:|
| `Swarm.RecordCarrierPaperScale` | 59.76 s | 4.82s | 45s | 3.7s | 577ms |
| `Swarm.LocOccSingleWindow` | 52.30 s | 1.32s | 41.5s | 3.38s | 740ms |
| `Swarm.LocOccSingleWindowAllPairs` | 51.67 s | 1.35s | 41.8s | 3.23s | 567ms |
| `Swarm.SummedSlope` | 34.58 s | 1.22s | 26.7s | 2.98s | 839ms |
| `Swarm.LocStartRange` | 30.89 s | 1.32s | 16.7s | 5.01s | 1.67s |

All five checks pass. Interpretation is the dominant remaining phase. The
per-event logs identify repeated `nlinarith` calls, including individual calls
of about 7–9 seconds in the three record-window files. Import loading is no
longer their main cost. These figures locate remaining arithmetic costs; no
additional proof-body refactor is included in this release.

## 8. Applied improvement

`Swarm.Swarming` originally imported all of Mathlib. Its own mathematics needs
real arithmetic, finite sums, finite maxima, and a small set of tactics. We
replaced the umbrella import with eight specific provider modules. No statement
or proof text changed. Both measured variants retained the same diagnostics.

| Variant | Run 1 | Run 2 | Run 3 | Median wall | Median peak RSS |
|---|---:|---:|---:|---:|---:|
| Umbrella import | 24.92 s | 21.28 s | 23.95 s | 23.95 s | 5.41 GiB |
| Specific imports | 4.96 s | 4.97 s | 4.83 s | 4.96 s | 1.77 GiB |

We obtain a 79.3% reduction in median wall time and a 67.2% reduction in median
peak RSS for this file on this machine. The median profiled import phase falls
from 19.9 seconds to 0.907 seconds. The raw measurements are in
[import-benchmark.json](import-benchmark.json).

For the other 120 umbrella-import sites, we selected the probability, analysis,
and tactic modules used by the project in `Swarm.Imports`. Its Mathlib source
import closure has 2,773 modules, compared with 8,312 for `Mathlib`. Additional
results and instances required by individual files have explicit local imports.
Every resulting project module is checked by compilation.


## 9. What the measurements do not establish

The import reduction is a measured improvement in a foundational file. We do
not report a repository-wide speedup factor: there is no successful matched
full-build timing for the original archive. Full-build measurements describe
only the proposed release.

Wall times include import I/O and apply to this host and cache state. Per-file
build times also include object serialization and simultaneous work in the
other process. Separate serial own-file profiles are the basis for attributing
remaining costs to elaboration phases.


We have no prior full-build series for trend comparisons. The timings precede two comment-only clarifications whose modules and final
audits were separately rechecked. The recorded warning
counts reflect the source files’ existing linter settings. We did not run a
registry comparator or an independent implementation of Lean’s proof checker.

## 10. Methodology

After restoring the pinned dependency cache, run:

```bash
python3 scripts/build.py --work .scratch/measurement --jobs 2
```

The output directory contains `summary.json`, individual Lean logs, GNU time
records, and the isolated search path. Use a new directory for each release
measurement. Development resumes are excluded from release measurements.

For an individual warm profile, from the same checkout:

```bash
LEAN_PATH="$(cat .scratch/measurement/lean-path.txt)" \
  lean -j1 -M 8000 --profile Swarm/Swarming.lean
```

To compare imports, prepare two untracked copies with identical mathematical
and diagnostic text, changing only the import block. Check them serially at the
same module path, alternating variants for three runs. Count only successful
runs and retain the full phase output and GNU time records.

## 11. Evidence

- [Verification record](VERIFICATION.md)
- [Statement and definition review](STATEMENT-REVIEW.md)
- [Errata and deviations](ERRATA-AND-DEVIATIONS.md)
- [Import A/B measurements](import-benchmark.json)
- [Full-build measurements](build-measurements.json)
- [Own-file phase measurements](own-file-profiles.json)
