# Independent statement and model review

Review date: 14 November 2026. This is a source review of the supplied
manuscript and original archive. No Lean build or axiom computation was run by
this reviewer. Source agreement and successful proof checking are separate
claims.

## Pinned inputs

| Input | SHA-256 |
|---|---|
| `upload/main_1d_revised.tex` | `65afa8e87670bcf9c9d8261c6b23a5323ae41c51c33794c42dd26c49a0603a37` |
| `upload/lean.zip` | `41f9b2741f4089a47498e25a12383fd15f3ade21a014a42e2c0abafa8dd56ed8` |

The exact exports reviewed are `M4Blk.main_claim` and
`M4Blk.main_claim_direct` in
`original/results/lean/areas/assembly/BlkMeasure.lean`, lines 386–390 and
432–436. The archive has no author-frozen declaration manifest; the closure
manifest records module ownership and object hashes, not author approval.

## Reconstruction from the manuscript

The model at lines 77–89 has finitely many walkers, all started at zero.
Local times include the visit at time zero and the visit at the current time.
At time n, walker i jumps right with probability p exactly when the sum of the
local times of all the other walkers at its current site is at least m; its
right probability is otherwise 1/2. Section 2.1, lines 168–189, specifies the
joint law through independent uniforms, indexed by walker, site, and visit
number. Thus the intended model includes conditional independence of the jumps
at a fixed time; it is more specific than the marginal display (rule) alone.

Theorem 1.1, label `main`, lines 95–100, states: for every m >= 2 and
1/2 < p < 1, there is a positive deterministic lower bound depending on m and p
only; for every N >= 2 there is a deterministic speed between that lower bound
and 2p-1; almost surely all N walkers have that speed.

## Binder review

Both exports have the same source-written binders. There is no bundled
assumption in either signature.

| Binder | Meaning | Classification | Source |
|---|---|---|---|
| `p : ℝ` | excitation parameter | SOURCE | theorem `main`, line 96 |
| `m : ℕ` | threshold | SOURCE | model, line 77; theorem `main` |
| `hp0 : 1/2 < p` | lower endpoint | SOURCE | theorem `main`, line 96 |
| `hp1 : p < 1` | upper endpoint | SOURCE | theorem `main`, line 96 |
| `hm : 2 ≤ m` | threshold restriction | SOURCE | theorem `main`, line 96 |

Counts for each export: SOURCE = 5; STANDING = 0; TYPING = 0; RULED = 0;
EXCESS = 0. The surrounding section declares `{N : ℕ}` and
`[Nonempty (Fin N)]` at line 64, but neither is free in these two displayed
types or their proof expressions. The exact elaborated binders still require
the independent consumer checks and `#check @...` after a successful build.

The conclusion has the following scope, which agrees with the manuscript:

| Component | Scope and assessment |
|---|---|
| `∃ κ : ℝ, 0 < κ` | Before N; no dependence on N or the sampled array. |
| `∀ N : ℕ, 2 ≤ N →` | Every finite population in the source range. |
| `∃ v : ℝ, κ ≤ v ∧ v ≤ 2*p-1` | A single deterministic speed for this N, m, p. |
| `∀ᵐ U ∂arrayMeasure N` | One probability-one event for the construction. |
| `∀ i : Fin N` | Every walker on that event; no walker-dependent speed. |
| `Tendsto (fun n => ((trajectory p m U n).pos i : ℝ)/(n : ℝ)) atTop (𝓝 v)` | The stated ordinary limit along natural times. |

The source-written theorem types have no integrability, regeneration,
tightness, conditional-independence, block-estimate, or positive-speed
assumptions. `main_claim` supplies the proved `paperBadBlockProfile` to
`M4Term.main_claim_of_paper_badblock_profile`. The second export supplies the
proved `dT_tight` to `SwarmDTR.main_claim_of_dT_tight`. These inputs appear in
the proof bodies, rather than as premises of the advertised theorems.

## Definition review

Paths in the definition review refer to the supplied archive; `source-map.json` records their current locations.

| Object | Inspected implementation | Assessment |
|---|---|---|
| One uniform | `UniformArray.lean:12`, `volume.restrict (Ioo 0 1)` | Literal Uniform(0,1) measure, total mass one proved at lines 14–17. |
| Driving array | `UniformArray.lean:20–24`, product on `Fin N × ℤ × ℕ` | Actual infinite product measure; independence proved at lines 42–44, with no independence premise. |
| Initial positions | `Trajectory.lean:27–29`, `pos _ := 0` | Exact source start. |
| Initial local times | `Trajectory.lean:29`, one at zero, zero elsewhere | Includes time-zero visits, as in the source. |
| Local time | `LocalTime.lean:37–38`, cardinality of visits in `range (n+1)` | Literal inclusive local time; `Trajectory.ell_eq_localTime`, lines 49–60, identifies the recursively stored counts. |
| Other visits | `Swarming.lean:468–469`, finite sum omitting the current walker | Exact sum over other walkers. |
| Excitation | `Swarming.lean:472–473`, `m ≤ otherVisits` | Threshold is inclusive, exact source convention. |
| Right probability | `Swarming.lean:476–479`, p in excited case and 1/2 otherwise | Exact two branches, no hidden fallback within the source domain. |
| Jump | `Swarming.lean:225`, right when `u ≤ α` | Matches manuscript (uniform), line 179, including endpoint convention. |
| Simultaneous update | `Trajectory.lean:18–25` | Every walker consults the same old state; counts increase at the new positions only after the simultaneous jumps. |
| Full trajectory | `Trajectory.lean:31–33` | Literal recursion from the specified start; no choice of an abstract process. |
| Fresh coordinates | `Trajectory.lean:118–125` | Injectivity across walkers and departure times proved. |

For the core model definitions: BODY_MATCH = OK; PUBLIC_CARRIER = OK up to
the explicit indexing convention below; WELL_DEFINEDNESS = N/A_LITERAL;
CHARACTERIZATION = N/A_LITERAL; CHOICE_INDEPENDENCE = N/A. No source-defining
object is selected from an assumed existence proposition. This is a static
definition verdict; proof checking of the cited supporting theorems remains
the build auditor's task.

Three harmless conventions should be stated in release documentation:

1. Walker indices use `Fin N` (zero through N-1) instead of one through N.
2. The product array includes coordinate k=0. The trajectory never consumes
   that coordinate: `Reveal.lean:86–100` proves that its local time at every
   current position is at least one. The manuscript indexes only k>=1.
3. Lean's real quotient at n=0 is total. This single initial term has no
   effect on `Tendsto ... atTop`.

These are conventions, not errors in the manuscript and not restrictions on
the theorem.

## Conditional independence and an important documentation caveat

The genuine conditional law is present. In
`areas/filtration/EnlFilt.lean:325–327`, an event of the enlarged sigma-algebra
is specified on each countable position-prefix piece by the values of exactly
the coordinates already read. `prefRead`, lines 93–95, includes departure
times strictly below n. This matches the enlarged filtration in manuscript
line 183. Positions and revealed values are proved measurable at lines
385–401 and 429–462. Nestedness and the `Filtration` construction occur at
lines 494–530.

`areas/filtration/EnlLaw.lean:138–141` states the independent uniform law over
every measurable event G of this sigma-algebra. Its proof uses countable
position-prefix pieces and finite-product independence, rather than singleton
real-valued histories. `areas/filtration/EnlJoint.lean:284–286` then states
the joint conditional expectation identity for every vector of +/-1 jumps;
its right-hand side, `weightFun`, lines 39–40, is the product of the individual
current jump probabilities. Its sole jump-vector premise says that every
coordinate is +/-1, which is the source support, not an independence premise.
`EnlRight.lean` and `EnlDrift.lean` contain the corresponding single-walker
conditional probability and drift identities.

By contrast, `HistoryCylinder.historyEvent`, lines 31–32, fixes exact values
of finitely many real uniforms. For n>0 and N>0 the event used by
`Transition.conditional_jumpLaw`, lines 98–102, has probability zero.
Consequently that identity alone does not establish a conditional law, and
the comments describing it as the conditional law are too strong. Likewise,
`HistoryLaw.historyConditionalJumpMean` is explicitly zero at a zero-mass
history, so its centered-mean theorem alone does not establish a martingale
property. These identities are not false; they are insufficient for that
interpretation. Release documentation should cite `EnlLaw.enl_fresh_law`
and `EnlJoint.condExp_pattern_enl` for genuine conditional independence, and
describe the earlier history identities accurately. No mathematical proof
edit is needed solely to fix those descriptions.

## Verdict and limits

DECLARATION_FIDELITY: PASS by independent source reading, subject to
confirmation of the elaborated binders.

MODEL_BODY_MATCH: PASS by source reading, with the conventions above.

No substantive statement mismatch or excess main-theorem assumption was found.
No erratum in the manuscript is asserted by this review. The two theorem
statements express the main result for the intended strong construction.

This review does not certify all 672 proof modules, the validity of imported
compiled objects, the allowed axiom closures, the exact elaborated theorem
types, dependency versions, fresh-checkout reproducibility, or a final release
tree that differs from the pinned original. Those require the separate build,
axiom, consumer, dependency, and final-tree checks. In particular a static
source match does not justify marking either theorem PROVED in this session.
