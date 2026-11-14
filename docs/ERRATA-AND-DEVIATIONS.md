# Errata and deviations

We distinguish defects in the manuscript from implementation conventions and
differences of scope. The reference is `main_1d_revised.tex`, SHA-256
`65afa8e87670bcf9c9d8261c6b23a5323ae41c51c33794c42dd26c49a0603a37`.
Locations refer to its LaTeX labels. We count entries rather than occurrences.
No manuscript erratum is asserted by this review. The main declarations
`M4Blk.main_claim` and `M4Blk.main_claim_direct` state Theorem 1.1 without
additional mathematical premises.

| Source | Errata | Deviations |
|---|---:|---:|
| Swarming of interacting excited random walks | 0 | 4 |

## Swarming of interacting excited random walks

### Errata

None identified in the reviewed main statement and model definitions. This
is not a claim that every sentence of the manuscript has been audited.

### Deviations

1. **Model and theorem `main`: walker indexing.** The manuscript indexes
   walkers from one through $N$. In Lean we use `Fin N`, with values from
   zero through $N-1$. Every walker is included and the mathematical
   statement is unchanged. See `Swarming.Model.LocalTimes` in
   [Swarming.lean](../Swarm/Swarming.lean) and `M4Blk.main_claim` in
   [BlkMeasure.lean](../Swarm/BlkMeasure.lean).

2. **Strong construction `uniform`: departure-number indexing.** The
   manuscript's array has departure numbers at least one. The Lean product
   array also has a zeroth coordinate at each site. We never read that
   coordinate: the current site's inclusive local time is at least one.
   Thus the trajectory has the same law. See `Swarming.Uniform.Array` in
   [UniformArray.lean](../Swarm/UniformArray.lean) and the positive local-time
   result in [Reveal.lean](../Swarm/Reveal.lean).

3. **Limit `lln`: time-zero quotient.** Lean's real division is total, so
   the sequence also has a value at time zero. We take its limit along
   `Filter.atTop`; the initial value has no effect on that limit. See
   `M4Blk.main_claim` in [BlkMeasure.lean](../Swarm/BlkMeasure.lean).

4. **Scope of this repository.** We include the full source dependency
   closure of Theorem 1.1. We do not claim a separate formal counterpart
   for every auxiliary statement in the manuscript. The source inventory includes one additional import-support module and
   is [source-map.json](source-map.json); the root import is
   [Swarm.lean](../Swarm.lean).

## Proof route and scope

The main proofs refer to the actual recursively constructed trajectory and
the actual product measure. Intermediate statements may have hypotheses
concerning occupation estimates, tightness, or regeneration; those
hypotheses do not appear in either main theorem. The estimates used by the
main assembly are supplied by theorems in its import closure.

The two final proofs share dependencies. They are alternative final
assemblies, rather than independent proofs of all intermediate results.
Corrections to comments describing exact-history identities do not change
their mathematical statements or proofs. Conditional laws for the revealed
sigma-algebra are proved in [EnlLaw.lean](../Swarm/EnlLaw.lean) and
[EnlJoint.lean](../Swarm/EnlJoint.lean).

The [projection note](PROOF-ROUTE-NOTE.md) distinguishes raw auxiliary
quantities from the manuscript’s conditionally projected process. The raw
nonmeasurability result is not a counterexample to the current manuscript.

The manuscript text, figures, simulations, historical build artifacts, and
unrelated formalisation modules are outside the repository's scope.
