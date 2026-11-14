/-
# The paper's `P^*` identity at a strict record time, and its use

`Swarm/FreshLaw.lean` proves `freshlawStrict_hfac`: at a fixed strict record time `(t, d)`
the relative future is independent of the past with the seed law.  Nothing in the tree consumed
it (`grep` shows no use of `freshlawStrict_hfac` outside its own audit file), so the "fresh-law
product factorisation" was available but not *wired*.  `Swarm/KacTransfer.lean` proves the
abstract transfer

  `μ(A ∩ Φ ⁻¹' B) = μ A * ν B  ⟹  (μ ↾ A).map Φ = μ A • ν`

for an arbitrary measurable `Φ`.  This file performs that instantiation for the actual array
law, the actual relative future `relFuture` and the paper's seed law.  The results are the
paper's §3.2 identities

  `P_π(X ∈ B | A) = P^*(B)`,  `E_{P_π(·|A)}[g] = E^*[g]`,

for `A` a strict regeneration event at a fixed time.  This is a *fixed-time* statement (it does
not construct the first-hit segment law and does not need the record chain); its point is that
the `P^*` of the paper is, in Lean, exactly `SwarmSeed.seedLaw`, and that the factorisation is
consumable in the exact `hfac` shape of `KacFormula.kac_paper_bound`.

Main results:

* `measurableSet_regenAtStrict`;
* `map_restrict_regenAtStrict` — `(P ↾ A).map relFuture = P(A) • P^*`;
* `map_restrict_normalized` — the conditional law itself is `P^*`;
* `lintegral_regenAtStrict` / `lintegral_conditioned` — the conditional expectation of any
  measurable path functional equals its `P^*`-expectation.

All conditional on the single residual `0 < P(V)`; no proof holes and no extra axioms.
-/
import Swarm.SeedHorizon
import Swarm.KacTransfer

open MeasureTheory Set ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SwarmSeed

variable {N : ℕ} {p : ℝ} {m : ℕ}

/-- The strict regeneration event at `(t, d)` is measurable.  It is the record event
(`measurableSet_recordSet`) intersected with the preimage of `strictPos` under the measurable
relative future. -/
theorem measurableSet_regenAtStrict (t : ℕ) (d : ℤ) :
    MeasurableSet {U : Swarming.Uniform.Array N | SwarmFresh.RegenAtStrict p m U t d} := by
  have hset : {U : Swarming.Uniform.Array N | SwarmFresh.RegenAtStrict p m U t d}
      = SwarmFresh.recordSet (N := N) p m t d
        ∩ (fun U => SwarmFresh.relFuture p m U t d) ⁻¹' SwarmFresh.strictPos (N := N) := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      SwarmFresh.regenAtStrict_iff, SwarmFresh.recordSet]
  rw [hset]
  exact (SwarmFresh.measurableSet_recordSet p m t d).inter
    ((SwarmFresh.measurable_relFuture p m t d N) SwarmFresh.measurableSet_strictPos)

/-- **`(P ↾ A).map relFuture = P(A) • P^*`** at a strict record time: the paper's
`P_π(X ∈ B | A) = P^*(B)`, stated without dividing. -/
theorem map_restrict_regenAtStrict (t : ℕ) (d : ℤ)
    (hVpos : 0 < (Swarming.Uniform.arrayMeasure N)
      {U : Swarming.Uniform.Array N |
        SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)}) :
    ((Swarming.Uniform.arrayMeasure N).restrict
        {U : Swarming.Uniform.Array N | SwarmFresh.RegenAtStrict p m U t d}).map
        (fun U => SwarmFresh.relFuture p m U t d)
      = (Swarming.Uniform.arrayMeasure N)
          {U : Swarming.Uniform.Array N | SwarmFresh.RegenAtStrict p m U t d} • seedLaw p m N := by
  refine KacFormula.map_restrict_eq_smul_of_factorization
    (μ := Swarming.Uniform.arrayMeasure N)
    (fun U => SwarmFresh.relFuture p m U t d) (SwarmFresh.measurable_relFuture p m t d N)
    _ (measurableSet_regenAtStrict (p := p) (m := m) t d) (seedLaw p m N) ?_
  intro B hB
  exact freshlawStrict_hfac_seedLaw (N := N) (p := p) (m := m) hVpos t d hB

/-- **The conditional law of the future at a strict record time is the seed law `P^*`.** -/
theorem map_restrict_normalized (t : ℕ) (d : ℤ) (hVpos : 0 < (Swarming.Uniform.arrayMeasure N)
      {U : Swarming.Uniform.Array N |
        SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)})
    (hmass : (Swarming.Uniform.arrayMeasure N)
      {U : Swarming.Uniform.Array N | SwarmFresh.RegenAtStrict p m U t d} ≠ 0) :
    (((Swarming.Uniform.arrayMeasure N)
          {U : Swarming.Uniform.Array N | SwarmFresh.RegenAtStrict p m U t d})⁻¹ •
        ((Swarming.Uniform.arrayMeasure N).restrict
          {U : Swarming.Uniform.Array N | SwarmFresh.RegenAtStrict p m U t d})).map
        (fun U => SwarmFresh.relFuture p m U t d)
      = seedLaw p m N := by
  rw [Measure.map_smul, map_restrict_regenAtStrict (N := N) (p := p) (m := m) t d hVpos,
    smul_smul, ENNReal.inv_mul_cancel hmass (measure_ne_top _ _), one_smul]

/-- **Conditional expectation of a path functional at a strict record time.**  For every
measurable `g : (ℕ → Fin N → ℤ) → ℝ≥0∞`,
`∫_{A} g(relFuture) dP = P(A) · ∫ g dP^*`. -/
theorem lintegral_regenAtStrict (t : ℕ) (d : ℤ)
    (hVpos : 0 < (Swarming.Uniform.arrayMeasure N)
      {U : Swarming.Uniform.Array N |
        SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)})
    {g : (ℕ → Fin N → ℤ) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ U in {U : Swarming.Uniform.Array N | SwarmFresh.RegenAtStrict p m U t d},
        g (SwarmFresh.relFuture p m U t d) ∂(Swarming.Uniform.arrayMeasure N)
      = (Swarming.Uniform.arrayMeasure N)
          {U : Swarming.Uniform.Array N | SwarmFresh.RegenAtStrict p m U t d}
        * ∫⁻ X, g X ∂seedLaw p m N :=
  KacFormula.lintegral_restrict_comp
    (μ := Swarming.Uniform.arrayMeasure N)
    (Φ := fun U => SwarmFresh.relFuture p m U t d) (SwarmFresh.measurable_relFuture p m t d N)
    (A := {U : Swarming.Uniform.Array N | SwarmFresh.RegenAtStrict p m U t d})
    (ν := seedLaw p m N)
    (c := (Swarming.Uniform.arrayMeasure N)
      {U : Swarming.Uniform.Array N | SwarmFresh.RegenAtStrict p m U t d})
    (g := g) hg
    (map_restrict_regenAtStrict (N := N) (p := p) (m := m) t d hVpos)

/-- **`E_{P(·|A)}[g] = E^*[g]`**: under the conditioned array law at a strict record time, every
measurable path functional has the same expectation as under the seed law `P^*`. -/
theorem lintegral_conditioned (t : ℕ) (d : ℤ)
    (hVpos : 0 < (Swarming.Uniform.arrayMeasure N)
      {U : Swarming.Uniform.Array N |
        SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)})
    (hmass : (Swarming.Uniform.arrayMeasure N)
      {U : Swarming.Uniform.Array N | SwarmFresh.RegenAtStrict p m U t d} ≠ 0)
    {g : (ℕ → Fin N → ℤ) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ U, g (SwarmFresh.relFuture p m U t d)
        ∂(((Swarming.Uniform.arrayMeasure N)
              {U : Swarming.Uniform.Array N | SwarmFresh.RegenAtStrict p m U t d})⁻¹ •
          ((Swarming.Uniform.arrayMeasure N).restrict
            {U : Swarming.Uniform.Array N | SwarmFresh.RegenAtStrict p m U t d}))
      = ∫⁻ X, g X ∂seedLaw p m N := by
  rw [lintegral_smul_measure, lintegral_regenAtStrict (N := N) (p := p) (m := m) t d hVpos hg,
    smul_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel hmass (measure_ne_top _ _), one_mul]

end SwarmSeed


