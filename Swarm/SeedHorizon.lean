/-
# From a uniform finite-horizon seed bound to the paper's `P(V) > 0`

`Swarm/FreshLaw.lean` proves the paper's `(freshlaw)` factorisation for the actual
array law `P = arrayMeasure N`, with the *single* residual hypothesis

  `hV : P(posPath ∈ strictPos) ≠ 0`     (the paper's `P(V) > 0`),

where `strictPos` is the set of fresh paths that start at `0` and are *strictly* positive at
every time `n ≥ 1` (`SwarmFresh.strictPos`).  This is an infinite-horizon event: it is a
condition on the whole trajectory.

Any combinatorial proof of seed positivity can only ever produce a bound on a *finite-horizon*
event, i.e. on the sets

  `strictPosUpto L = {X | X 0 = 0, 0 < X n for 1 ≤ n ≤ L}`,

because a finite coordinate block determines only finitely many times.  This file supplies
the missing measure-theoretic passage: it is enough that the finite-horizon seed masses are
bounded below by a *single positive constant* `c`, independent of `L`.

Main results:

* `strictPosUpto_antitone`, `iInter_strictPosUpto` — the horizon sets decrease to `strictPos`;
* `seed_pos_of_uniform_lower` — the general form (for an arbitrary measurable
  `f : Array N → (ℕ → Fin N → ℤ)` and an arbitrary antitone family decreasing to a limit set);
* `seed_pos_strict` / `seed_pos_nonneg` — the two instances used by `FreshLaw.lean`
  (`strictPos` and `nonnegPath`);
* `freshlawStrict_hfac_of_pos` — `freshlawStrict_hfac` with the seed hypothesis in the
  strictly-positive form `0 < P(strictPos)` and with `hVtop` discharged (a probability measure
  gives `≤ 1 < ⊤`), so that a downstream user has exactly one residual premise to feed;
* `seedLaw` + `isProbabilityMeasure_seedLaw` + `freshlawStrict_hfac_seedLaw` — the paper's
  `P^*` as an honest probability measure, and `(freshlaw)` in the paper's multiplicative form
  `P(A ∩ φ⁻¹B) = P(A) · P^*(B)`.

No proof-hole, no axioms beyond Lean's: see `Audit.lean`.
-/
import Swarm.FreshLaw

open MeasureTheory Set ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SwarmSeed

variable {N : ℕ} {p : ℝ} {m : ℕ}

/-! ### The horizon truncations of the strict seed event -/

/-- Strict positivity of a fresh path up to time `L`.  It pins the path down at `X 0` and at
the finitely many times `1 ≤ n ≤ L`, hence depends on finitely many coordinates only. -/
def strictPosUpto (L : ℕ) : Set (ℕ → Fin N → ℤ) :=
  {X | (∀ i, X 0 i = 0) ∧ ∀ n ∈ Finset.Icc 1 L, ∀ i, (0 : ℤ) < X n i}

theorem measurableSet_strictPosUpto (L : ℕ) : MeasurableSet (strictPosUpto (N := N) L) := by
  have h1 : {X : ℕ → Fin N → ℤ | ∀ i, X 0 i = 0} = ⋂ i, {X : ℕ → Fin N → ℤ | X 0 i = 0} := by
    ext X; simp
  have h2 : {X : ℕ → Fin N → ℤ | ∀ n ∈ Finset.Icc 1 L, ∀ i, (0 : ℤ) < X n i}
      = ⋂ n, ⋂ (_ : n ∈ Finset.Icc 1 L), ⋂ i, {X : ℕ → Fin N → ℤ | (0 : ℤ) < X n i} := by
    ext X; simp
  have hsplit : strictPosUpto (N := N) L
      = {X : ℕ → Fin N → ℤ | ∀ i, X 0 i = 0}
        ∩ {X : ℕ → Fin N → ℤ | ∀ n ∈ Finset.Icc 1 L, ∀ i, (0 : ℤ) < X n i} := rfl
  rw [hsplit, h1, h2]
  refine MeasurableSet.inter ?_ ?_
  · exact MeasurableSet.iInter fun i =>
      (by fun_prop : Measurable fun X : ℕ → Fin N → ℤ => X 0 i) (measurableSet_singleton 0)
  · exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun i =>
        (by fun_prop : Measurable fun X : ℕ → Fin N → ℤ => X n i) measurableSet_Ioi

theorem strictPosUpto_antitone : Antitone (strictPosUpto (N := N)) := by
  intro L L' hLL' X hX
  obtain ⟨h0, h⟩ := hX
  refine ⟨h0, fun n hn i => h n ?_ i⟩
  exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, le_trans (Finset.mem_Icc.mp hn).2 hLL'⟩

theorem iInter_strictPosUpto : (⋂ L, strictPosUpto (N := N) L) = SwarmFresh.strictPos (N := N) := by
  apply Set.Subset.antisymm
  · intro X hX
    rw [SwarmFresh.mem_strictPos]
    refine ⟨(Set.iInter_subset (fun L => strictPosUpto (N := N) L) 0 hX).1, fun n hn i => ?_⟩
    exact (Set.iInter_subset (fun L => strictPosUpto (N := N) L) n hX).2 n
      (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩) i
  · intro X hX
    rw [SwarmFresh.mem_strictPos] at hX
    refine Set.mem_iInter.mpr fun L => ?_
    exact ⟨hX.1, fun n hn i => hX.2 n (Finset.mem_Icc.mp hn).1 i⟩

/-! ### The general continuity-from-above bridge -/

/-- **Finite horizon ⟹ infinite horizon, uniformly in the horizon.**  If every horizon
truncation has mass at least `c > 0`, then the limiting event has positive mass.  This is the
one place where continuity from above (a probability measure, so no mass escapes) is used. -/
theorem seed_pos_of_uniform_lower {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {T : Set α} {S : ℕ → Set α}
    (hS : ∀ L, MeasurableSet (S L)) (hanti : Antitone S) (hInter : (⋂ L, S L) = T)
    {c : ℝ≥0∞} (hc : 0 < c) (h : ∀ L, c ≤ μ (S L)) : 0 < μ T := by
  have hfin : ∃ L, μ (S L) ≠ ⊤ := ⟨0, measure_ne_top μ _⟩
  have hEq : μ T = ⨅ L, μ (S L) := by
    rw [← hInter]
    exact Antitone.measure_iInter hanti (fun L => (hS L).nullMeasurableSet) hfin
  rw [hEq]
  exact lt_of_lt_of_le hc (le_iInf h)

/-- **Only a cofinal set of horizons is needed.**  If the horizon bound is available along any
unbounded sequence of horizons `f L → ∞` (e.g. only at dyadic lengths, which is what a
finite-block construction naturally gives), the same conclusion follows: the measure of the
horizon truncations is antitone, so its infimum over a cofinal subsequence is the full infimum. -/
theorem seed_pos_of_uniform_lower_cofinal {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {T : Set α} {S : ℕ → Set α}
    (hS : ∀ L, MeasurableSet (S L)) (hanti : Antitone S) (hInter : (⋂ L, S L) = T)
    {f : ℕ → ℕ} (hf : Tendsto f atTop atTop)
    {c : ℝ≥0∞} (hc : 0 < c) (h : ∀ L, c ≤ μ (S (f L))) : 0 < μ T := by
  have hfin : ∃ L, μ (S L) ≠ ⊤ := ⟨0, measure_ne_top μ _⟩
  have hEq : μ T = ⨅ L, μ (S L) := by
    rw [← hInter]
    exact Antitone.measure_iInter hanti (fun L => (hS L).nullMeasurableSet) hfin
  have hcof : ∀ k, ∃ L, k ≤ f L := fun k => (tendsto_atTop.1 hf k).exists
  have hEq' : (⨅ L, μ (S L)) = ⨅ L, μ (S (f L)) := by
    refine le_antisymm ?_ ?_
    · refine le_iInf fun L => ?_
      exact iInf_le _ (f L)
    · refine le_iInf fun k => ?_
      obtain ⟨L, hL⟩ := hcof k
      exact le_trans (iInf_le _ L) (measure_mono (hanti hL))
  rw [hEq, hEq']
  exact lt_of_lt_of_le hc (le_iInf h)

/-- **It is enough to bound the horizons eventually.**  A finite-block argument typically
controls `P(strictPosUpto L)` only for large `L`.  Since the horizon truncations are antitone,
bounds for all `L ≥ L₀` already give a positive lower bound for *every* horizon (for `L < L₀`
the mass is at least the mass at `L₀`). -/
theorem seed_pos_of_eventually_lower {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {T : Set α} {S : ℕ → Set α}
    (hS : ∀ L, MeasurableSet (S L)) (hanti : Antitone S) (hInter : (⋂ L, S L) = T)
    {c : ℝ≥0∞} (hc : 0 < c) (L₀ : ℕ) (h : ∀ L, L₀ ≤ L → c ≤ μ (S L)) : 0 < μ T := by
  refine seed_pos_of_uniform_lower hS hanti hInter hc ?_
  intro L
  rcases le_total L₀ L with hL | hL
  · exact h L hL
  · exact le_trans (h L₀ le_rfl) (measure_mono (hanti hL))

/-- **Seed positivity of the paper's `V`** in the shape consumed by `FreshLaw`: it suffices to
exhibit a single `c > 0` bounding every finite-horizon seed mass. -/
theorem seed_pos_strict {c : ℝ≥0∞} (hc : 0 < c)
    (h : ∀ L, c ≤ (Swarming.Uniform.arrayMeasure N)
      {U : Swarming.Uniform.Array N |
        SwarmRestart.posPath p m U ∈ strictPosUpto (N := N) L}) :
    0 < (Swarming.Uniform.arrayMeasure N)
      {U : Swarming.Uniform.Array N |
        SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)} := by
  have : IsProbabilityMeasure (Swarming.Uniform.arrayMeasure N) :=
    Swarming.Uniform.arrayMeasure_isProbabilityMeasure N
  have hset : {U : Swarming.Uniform.Array N |
      SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)}
      = ⋂ L, {U : Swarming.Uniform.Array N |
        SwarmRestart.posPath p m U ∈ strictPosUpto (N := N) L} := by
    ext U
    simp only [mem_ofPred_eq, mem_iInter]
    rw [← iInter_strictPosUpto, mem_iInter]
  rw [hset]
  exact seed_pos_of_uniform_lower
    (fun L => (SwarmRestart.measurable_posPath p m N) (measurableSet_strictPosUpto L))
    (fun L L' hLL' => preimage_mono (strictPosUpto_antitone hLL'))
    (by ext U; simp [mem_iInter]) hc h

/-- `seed_pos_strict` along a cofinal sequence of horizons. -/
theorem seed_pos_strict_cofinal {c : ℝ≥0∞} (hc : 0 < c) {f : ℕ → ℕ}
    (hf : Tendsto f atTop atTop)
    (h : ∀ L, c ≤ (Swarming.Uniform.arrayMeasure N)
      {U : Swarming.Uniform.Array N |
        SwarmRestart.posPath p m U ∈ strictPosUpto (N := N) (f L)}) :
    0 < (Swarming.Uniform.arrayMeasure N)
      {U : Swarming.Uniform.Array N |
        SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)} := by
  haveI : IsProbabilityMeasure (Swarming.Uniform.arrayMeasure N) :=
    Swarming.Uniform.arrayMeasure_isProbabilityMeasure N
  have hset : {U : Swarming.Uniform.Array N |
      SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)}
      = ⋂ L, {U : Swarming.Uniform.Array N |
        SwarmRestart.posPath p m U ∈ strictPosUpto (N := N) L} := by
    ext U
    simp only [mem_ofPred_eq, mem_iInter]
    rw [← iInter_strictPosUpto, mem_iInter]
  rw [hset]
  exact seed_pos_of_uniform_lower_cofinal
    (fun L => (SwarmRestart.measurable_posPath p m N) (measurableSet_strictPosUpto L))
    (fun L L' hLL' => preimage_mono (strictPosUpto_antitone hLL'))
    (by ext U; simp [mem_iInter]) hf hc h

/-- `seed_pos_strict` with the horizon bounds required only for `L ≥ L₀`. -/
theorem seed_pos_strict_eventually {c : ℝ≥0∞} (hc : 0 < c) (L₀ : ℕ)
    (h : ∀ L, L₀ ≤ L → c ≤ (Swarming.Uniform.arrayMeasure N)
      {U : Swarming.Uniform.Array N |
        SwarmRestart.posPath p m U ∈ strictPosUpto (N := N) L}) :
    0 < (Swarming.Uniform.arrayMeasure N)
      {U : Swarming.Uniform.Array N |
        SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)} := by
  haveI : IsProbabilityMeasure (Swarming.Uniform.arrayMeasure N) :=
    Swarming.Uniform.arrayMeasure_isProbabilityMeasure N
  have hset : {U : Swarming.Uniform.Array N |
      SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)}
      = ⋂ L, {U : Swarming.Uniform.Array N |
        SwarmRestart.posPath p m U ∈ strictPosUpto (N := N) L} := by
    ext U
    simp only [mem_ofPred_eq, mem_iInter]
    rw [← iInter_strictPosUpto, mem_iInter]
  rw [hset]
  exact seed_pos_of_eventually_lower
    (fun L => (SwarmRestart.measurable_posPath p m N) (measurableSet_strictPosUpto L))
    (fun L L' hLL' => preimage_mono (strictPosUpto_antitone hLL'))
    (by ext U; simp [mem_iInter]) hc L₀ h

/-- The same bridge for the non-strict seed event `nonnegPath` used by `freshlaw_hfac`. -/
def nonnegUpto (L : ℕ) : Set (ℕ → Fin N → ℤ) := {X | ∀ n ≤ L, ∀ i, (0 : ℤ) ≤ X n i}

theorem measurableSet_nonnegUpto (L : ℕ) : MeasurableSet (nonnegUpto (N := N) L) := by
  have h : nonnegUpto (N := N) L
      = ⋂ n, ⋂ (_ : n ≤ L), ⋂ i, {X : ℕ → Fin N → ℤ | (0 : ℤ) ≤ X n i} := by
    ext X; simp [nonnegUpto]
  rw [h]
  exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun i =>
      (by fun_prop : Measurable fun X : ℕ → Fin N → ℤ => X n i) measurableSet_Ici

theorem nonnegUpto_antitone : Antitone (nonnegUpto (N := N)) := by
  intro L L' hLL' X hX n hn i
  exact hX n (le_trans hn hLL') i

theorem iInter_nonnegUpto : (⋂ L, nonnegUpto (N := N) L) = SwarmFresh.nonnegPath (N := N) := by
  apply Set.Subset.antisymm
  · intro X hX n i
    exact Set.iInter_subset (fun L => nonnegUpto (N := N) L) n hX n le_rfl i
  · intro X hX
    refine Set.mem_iInter.mpr fun L => ?_
    exact fun n _ i => hX n i

theorem seed_pos_nonneg {c : ℝ≥0∞} (hc : 0 < c)
    (h : ∀ L, c ≤ (Swarming.Uniform.arrayMeasure N)
      {U : Swarming.Uniform.Array N |
        SwarmRestart.posPath p m U ∈ nonnegUpto (N := N) L}) :
    0 < (Swarming.Uniform.arrayMeasure N)
      {U : Swarming.Uniform.Array N |
        SwarmRestart.posPath p m U ∈ SwarmFresh.nonnegPath (N := N)} := by
  have : IsProbabilityMeasure (Swarming.Uniform.arrayMeasure N) :=
    Swarming.Uniform.arrayMeasure_isProbabilityMeasure N
  have hset : {U : Swarming.Uniform.Array N |
      SwarmRestart.posPath p m U ∈ SwarmFresh.nonnegPath (N := N)}
      = ⋂ L, {U : Swarming.Uniform.Array N |
        SwarmRestart.posPath p m U ∈ nonnegUpto (N := N) L} := by
    ext U
    simp only [mem_ofPred_eq, mem_iInter]
    rw [← iInter_nonnegUpto, mem_iInter]
  rw [hset]
  exact seed_pos_of_uniform_lower
    (fun L => (SwarmRestart.measurable_posPath p m N) (measurableSet_nonnegUpto L))
    (fun L L' hLL' => preimage_mono (nonnegUpto_antitone hLL'))
    (by ext U; simp [mem_iInter]) hc h

/-! ### The paper's `P^*` as a probability measure

`freshlawStrict_hfac` states `(freshlaw)` with the seed law written out as an
`ENNReal`-scaled restricted map.  Below is the same identity with the paper's `P^*` named,
together with the proof that it *is* a probability measure.  This is the law of the fresh
segment conditioned on `V`; `SeedHorizon`/`freshlawStrict_hfac_seedLaw` make the exact object
that the paper's `P^*` denotes explicit in Lean. -/

/-- The paper's `P^*`: the law of the fresh path conditioned on being strictly positive after
time `0`.  Only a probability measure when the seed mass is nonzero; that is proved in
`isProbabilityMeasure_seedLaw`. -/
noncomputable def seedLaw (p : ℝ) (m N : ℕ) : Measure (ℕ → Fin N → ℤ) :=
  ((Swarming.Uniform.arrayMeasure N)
      {U : Swarming.Uniform.Array N |
        SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)})⁻¹ •
    ((Swarming.Uniform.arrayMeasure N).restrict
      {U : Swarming.Uniform.Array N |
        SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)}).map
      (fun U => SwarmRestart.posPath p m U)

theorem measurableSet_strictSeed : MeasurableSet
    {U : Swarming.Uniform.Array N |
      SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)} :=
  (SwarmRestart.measurable_posPath p m N) SwarmFresh.measurableSet_strictPos

/-- The seed law has total mass one as soon as the seed event has positive probability. -/
theorem isProbabilityMeasure_seedLaw (hV : (Swarming.Uniform.arrayMeasure N)
    {U : Swarming.Uniform.Array N |
      SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)} ≠ 0) :
    IsProbabilityMeasure (seedLaw p m N) := by
  have : IsProbabilityMeasure (Swarming.Uniform.arrayMeasure N) :=
    Swarming.Uniform.arrayMeasure_isProbabilityMeasure N
  refine ⟨?measure_univ⟩
  have hmass : (Swarming.Uniform.arrayMeasure N).restrict
      {U : Swarming.Uniform.Array N |
        SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)} univ
      = (Swarming.Uniform.arrayMeasure N)
        {U : Swarming.Uniform.Array N |
          SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)} := by
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
  simp only [seedLaw, Measure.smul_apply, Measure.map_apply
    (SwarmRestart.measurable_posPath p m N) MeasurableSet.univ, preimage_univ,
    smul_eq_mul, hmass]
  exact ENNReal.inv_mul_cancel hV (measure_ne_top _ _)

/-! ### `(freshlaw)` with a single positive-probability hypothesis, in `P^*` form -/

/-- **`freshlawStrict_hfac` with the seed hypothesis as `0 < P(V)`, and no `hVtop`.**

`hVtop` (`P(V) ≠ ⊤`) is not a hypothesis of the paper: it is automatic because `P` is a
probability measure.  Discharging it here leaves the seed positivity as the single residual
premise of the strict factorisation. -/
theorem freshlawStrict_hfac_of_pos (hVpos : 0 < (Swarming.Uniform.arrayMeasure N)
    {U : Swarming.Uniform.Array N |
      SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)})
    (t : ℕ) (d : ℤ) {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (Swarming.Uniform.arrayMeasure N)
        {U : Swarming.Uniform.Array N |
          SwarmFresh.RegenAtStrict p m U t d ∧ SwarmFresh.relFuture p m U t d ∈ B}
      = (Swarming.Uniform.arrayMeasure N)
          {U : Swarming.Uniform.Array N | SwarmFresh.RegenAtStrict p m U t d}
        * (((Swarming.Uniform.arrayMeasure N)
              {U : Swarming.Uniform.Array N |
                SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)})⁻¹
          * ((Measure.restrict (Swarming.Uniform.arrayMeasure N)
              {U : Swarming.Uniform.Array N |
                SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)}).map
              (fun U => SwarmRestart.posPath p m U)) B) := by
  have : IsProbabilityMeasure (Swarming.Uniform.arrayMeasure N) :=
    Swarming.Uniform.arrayMeasure_isProbabilityMeasure N
  exact SwarmFresh.freshlawStrict_hfac p m t d (ne_of_gt hVpos) (measure_ne_top _ _) hB

/-- **The paper's `(factor)` in `P^*` form**: the translated future at a strict regeneration
time is independent of the past and has the seed law `P^*`. -/
theorem freshlawStrict_hfac_seedLaw (hVpos : 0 < (Swarming.Uniform.arrayMeasure N)
    {U : Swarming.Uniform.Array N |
      SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)})
    (t : ℕ) (d : ℤ) {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (Swarming.Uniform.arrayMeasure N)
        {U : Swarming.Uniform.Array N |
          SwarmFresh.RegenAtStrict p m U t d ∧ SwarmFresh.relFuture p m U t d ∈ B}
      = (Swarming.Uniform.arrayMeasure N)
          {U : Swarming.Uniform.Array N | SwarmFresh.RegenAtStrict p m U t d}
        * seedLaw p m N B := by
  rw [freshlawStrict_hfac_of_pos hVpos t d hB]
  rfl

end SwarmSeed


