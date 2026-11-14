/-
# The actual common speed from the neutral (P*) regeneration law

## What the tree already proves

* `Swarm.actualProjectedBallistic` (Proposition `ball`, lower half) — for the actual array
  model, unconditionally: `kappa > 0` (uniform in `N`) with `kappa <= liminf X_n^i/n` a.s.
* `SwarmDens.actual_ae_limsup_pos_div_le` — the upper half `limsup X_n^i/n <= 2p-1` a.s.
* `Swarm.ae_tendsto_of_regen` — SLLN for the increments + the paper's sandwich interlacing
  give `X_n^i/n -> E D_0 / E T_0` a.s., for every walker, under the measure carrying the
  i.i.d. increments.
* `Swarm.tendsto_div_of_translate` — a finite spatial/temporal translation does not change
  the limit of `y n / n`.
* `Swarm.main_theorem_actual_of_actual_regeneration` — the paper's Theorem 1.1 for the
  concrete array model, from `Swarm.ActualRegen` (i.i.d. increments under the *actual* law).

## What is added here

Proposition `regen` of the source produces the i.i.d. increments under `P^* = P(. | V)`,
and proves under `P` only that *after an almost surely finite regeneration time the
translated future has law `P^*`*.  The neutral measure `P^*` is the measure in which the
Kac bound (`exists_kappa_record_ED_uniform` of `areas/tightness/ActualInvariant.lean`) and
the stationary record law produce finiteness.  So the missing consumer is the passage

  (i.i.d. increments under `P^*`) + (translated future after the initial regeneration has
  law `P^*`)  =>  (the paper's common speed under the original law `P`).

That passage is *not* a special case of `ActualRegen` (which asks for the i.i.d. structure
under `P` itself, something the paper never proves); it is the paper's own argument, and it
is formalised here:

* `measurable_uncurry_of_forall`, `measurable_shiftPath` — the randomly translated future
  is a measurable function of the array;
* `measurableSet_forall_tendsto_div` — the set of paths having the common limit is Borel;
* `ae_forall_tendsto_div_of_map_eq` — **transfer of a path limit along a law identity**;
* `actual_common_speed_of_neutral_regen` — **the capstone**: from `RegenLaw nu D T`,
  `Sandwich nu X D T` under a probability `nu` on the same sample space, plus the law
  identity `law(shifted future under P) = law(nu-path)`, the paper's Theorem 1.1 conclusion
  holds for the actual array law, with `kappa` from the ballistic theorem and `v <= 2p-1`
  from the density upper bound.
* `actual_common_speed_of_actual_regen` — the same statement with `nu = P`, `S = 0`, `c = 0`,
  showing the neutral interface is *weaker* than `Swarm.ActualRegen`;
* `actual_common_speed_of_neutral_ED` — the same conclusion from `RegenLawWeak` (distance
  integrability, pairwise independence, identical distribution, `T >= 1`) plus the neutral
  lower speed: the duration integrability `E_nu T_0 < inf` is **derived** from the positive
  lower speed by the source's §3.4 contradiction (`Swarm.integrable_duration_of_regenLawWeak`);
* `actual_common_speed_of_neutral_ac` — the same with the lower-speed premises *discharged*:
  for any neutral measure absolutely continuous with respect to the original law (which is
  the case for `P^* = P(. | V)` when `P(V) > 0`) the bounds hold by
  `Swarm.actualProjectedBallistic` and `Swarm.abs_le_time_of_law`.  Its premise list is then
  exactly `nu << P`, the neutral increment structure with `Sandwich`, and the law of the
  translated future.

Only `propext`, `Classical.choice`, `Quot.sound` are used (see the audit at the end).
-/
import Swarm.ActualMain
import Mathlib.MeasureTheory.Order.Group.Lattice
import Swarm.DensityInterface
import Swarm.DurationIntegrable
import Swarm.SandwichBridge

open MeasureTheory ProbabilityTheory Filter Topology
open Swarming.Uniform
open scoped ENNReal BigOperators

set_option maxHeartbeats 1000000

namespace M6Star

/-! ## 1. Measurability toolkit -/

section Toolkit

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- A family that is measurable in the space variable for every index is jointly measurable
when the index type is countable and has measurable singletons. -/
lemma measurable_uncurry_of_forall [Countable α] [MeasurableSingletonClass α]
    {f : α → β → γ} (hf : ∀ a, Measurable (f a)) :
    Measurable (fun q : α × β => f q.1 q.2) := by
  intro s hs
  have hset : (fun q : α × β => f q.1 q.2) ⁻¹' s = ⋃ a, {a} ×ˢ (f a ⁻¹' s) := by
    ext q
    constructor
    · intro h
      exact Set.mem_iUnion.2 ⟨q.1, rfl, h⟩
    · intro h
      obtain ⟨a, ha⟩ := Set.mem_iUnion.1 h
      obtain ⟨hq1, hq2⟩ := Set.mem_prod.1 ha
      rw [Set.mem_singleton_iff] at hq1
      simpa [hq1] using hq2
  rw [hset]
  exact MeasurableSet.iUnion fun a =>
    MeasurableSet.prod (measurableSet_singleton a) (hf a hs)

end Toolkit

/-- `Tendsto` of a real sequence written with the countably many radii `1/(k+1)`. -/
lemma tendsto_iff_forall_one_div (u : ℕ → ℝ) (v : ℝ) :
    Tendsto u atTop (𝓝 v) ↔
      ∀ k : ℕ, ∀ᶠ n : ℕ in atTop, |u n - v| < 1 / ((k : ℝ) + 1) := by
  constructor
  · intro h k
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    filter_upwards [h.eventually (Metric.ball_mem_nhds v hpos)] with n hn
    simpa [Real.dist_eq] using hn
  · intro h
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    obtain ⟨M, hM⟩ := eventually_atTop.1 (h k)
    exact ⟨M, fun n hn => by rw [Real.dist_eq]; exact lt_trans (hM n hn) hk⟩

variable {N : ℕ} {m : ℕ} {p : ℝ}

/-- The set of paths whose `i`-th coordinate has the limiting speed `v` is Borel. -/
lemma measurableSet_tendsto_div (v : ℝ) (i : Fin N) :
    MeasurableSet {x : ℕ → Fin N → ℝ |
      Tendsto (fun n : ℕ => x n i / (n : ℝ)) atTop (𝓝 v)} := by
  have hbasic : ∀ (n : ℕ) (ε : ℝ),
      MeasurableSet {x : ℕ → Fin N → ℝ | |x n i / (n : ℝ) - v| < ε} := by
    intro n ε
    have hf : Measurable (fun x : ℕ → Fin N → ℝ => |x n i / (n : ℝ) - v|) := by
      have h1 : Measurable (fun x : ℕ → Fin N → ℝ => x n i) := by
        have hn : Measurable (fun x : ℕ → Fin N → ℝ => x n) := measurable_pi_apply n
        have hi : Measurable (fun g : Fin N → ℝ => g i) := measurable_pi_apply i
        exact hi.comp hn
      exact ((h1.div_const (n : ℝ)).sub_const v).abs
    simpa using measurableSet_lt hf measurable_const
  have hset : {x : ℕ → Fin N → ℝ | Tendsto (fun n : ℕ => x n i / (n : ℝ)) atTop (𝓝 v)}
      = ⋂ k : ℕ, ⋃ M : ℕ, ⋂ n : ℕ,
          {x : ℕ → Fin N → ℝ | M ≤ n → |x n i / (n : ℝ) - v| < 1 / ((k : ℝ) + 1)} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion]
    rw [tendsto_iff_forall_one_div]
    constructor
    · intro h k
      obtain ⟨M, hM⟩ := eventually_atTop.1 (h k)
      exact ⟨M, fun n hn => hM n hn⟩
    · intro h k
      obtain ⟨M, hM⟩ := h k
      exact eventually_atTop.2 ⟨M, fun n hn => hM n hn⟩
  rw [hset]
  refine MeasurableSet.iInter fun k => MeasurableSet.iUnion fun M =>
    MeasurableSet.iInter fun n => ?_
  by_cases hn : M ≤ n
  · have hEq : {x : ℕ → Fin N → ℝ | M ≤ n → |x n i / (n : ℝ) - v| < 1 / ((k : ℝ) + 1)}
        = {x : ℕ → Fin N → ℝ | |x n i / (n : ℝ) - v| < 1 / ((k : ℝ) + 1)} := by
      ext x
      simp [hn]
    rw [hEq]
    exact hbasic n _
  · have hEq : {x : ℕ → Fin N → ℝ | M ≤ n → |x n i / (n : ℝ) - v| < 1 / ((k : ℝ) + 1)}
        = Set.univ := by
      ext x
      simp [hn]
    rw [hEq]
    exact MeasurableSet.univ

/-- The set of paths whose every coordinate has the common limiting speed `v` is Borel. -/
lemma measurableSet_forall_tendsto_div (v : ℝ) :
    MeasurableSet {x : ℕ → Fin N → ℝ |
      ∀ i : Fin N, Tendsto (fun n : ℕ => x n i / (n : ℝ)) atTop (𝓝 v)} := by
  have hset : {x : ℕ → Fin N → ℝ |
      ∀ i : Fin N, Tendsto (fun n : ℕ => x n i / (n : ℝ)) atTop (𝓝 v)}
      = ⋂ i : Fin N, {x : ℕ → Fin N → ℝ |
          Tendsto (fun n : ℕ => x n i / (n : ℝ)) atTop (𝓝 v)} := by
    ext x
    simp
  rw [hset]
  exact MeasurableSet.iInter fun i => measurableSet_tendsto_div v i

/-! ## 2. The actual path and its random translation, as measurable path-space maps -/

open Swarming in
/-- The actual array path, read as an element of the real path space. -/
noncomputable def actPath (p : ℝ) (m : ℕ) (U : Array N) : ℕ → Fin N → ℝ :=
  fun n i => Swarm.pos (Swarm.actualX (N := N) p m) n i U

lemma measurable_actualX_pos (p : ℝ) (m n : ℕ) (i : Fin N) :
    Measurable (fun U : Array N => Swarm.pos (Swarm.actualX (N := N) p m) n i U) := by
  have h : (fun U : Array N => Swarm.pos (Swarm.actualX (N := N) p m) n i U)
      = fun U : Array N => (((Swarming.Trajectory.trajectory p m U n).pos i : ℤ) : ℝ) := by
    funext U
    rfl
  rw [h]
  exact (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
    ((Swarming.Fair.measurable_trajectory p m n).1 i)

lemma measurable_actPath (p : ℝ) (m : ℕ) :
    Measurable (actPath (N := N) p m) := by
  rw [measurable_pi_iff]
  intro n
  rw [measurable_pi_iff]
  intro i
  exact measurable_actualX_pos p m n i

/-- The randomly translated path `n |-> X_{n+S}^i - c` is measurable in the array. -/
lemma measurable_shiftPath (p : ℝ) (m : ℕ) (S : Array N → ℕ) (c : Array N → ℝ)
    (hS : Measurable S) (hc : Measurable c) :
    Measurable (fun U : Array N => fun (n : ℕ) (i : Fin N) =>
      Swarm.pos (Swarm.actualX (N := N) p m) (n + S U) i U - c U) := by
  rw [measurable_pi_iff]
  intro n
  rw [measurable_pi_iff]
  intro i
  have hG : Measurable (fun q : ℕ × Array N =>
      Swarm.pos (Swarm.actualX (N := N) p m) (n + q.1) i q.2) := by
    refine measurable_uncurry_of_forall (f := fun (k : ℕ) (U : Array N) =>
      Swarm.pos (Swarm.actualX (N := N) p m) (n + k) i U) (fun k => ?_)
    exact measurable_actualX_pos p m (n + k) i
  have hid : Measurable (fun U : Array N => U) := measurable_id
  have hpair : Measurable (fun U : Array N => (S U, U)) := by
    refine Measurable.prod ?_ ?_
    · simpa using hS
    · simpa using hid
  exact (hG.comp hpair).sub hc

/-! ## 3. Transfer of a path limit along a law identity -/

/-- **The limit set transfers along a law identity.**  If the law of `Φ` under `μ` is the law of
`Ψ` under `ν`, and `Ψ`-almost every path has the common speed `v`, then `Φ`-almost every path
under `μ` has the common speed `v`.  This is the measure-theoretic content of the source's
"the translated future has law `P^*`, and finite translations do not change the limit". -/
theorem ae_forall_tendsto_div_of_map_eq {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}
    {Ψ Φ : Ω → (ℕ → Fin N → ℝ)} {v : ℝ}
    (hΨ : Measurable Ψ) (hΦ : Measurable Φ) (hmap : μ.map Φ = ν.map Ψ)
    (hν : ∀ᵐ U ∂ν, ∀ i : Fin N, Tendsto (fun n : ℕ => Ψ U n i / (n : ℝ)) atTop (𝓝 v)) :
    ∀ᵐ U ∂μ, ∀ i : Fin N, Tendsto (fun n : ℕ => Φ U n i / (n : ℝ)) atTop (𝓝 v) := by
  have hmeas : MeasurableSet {x : ℕ → Fin N → ℝ |
      ∀ i : Fin N, Tendsto (fun n : ℕ => x n i / (n : ℝ)) atTop (𝓝 v)} :=
    measurableSet_forall_tendsto_div v
  have h1 : ∀ᵐ x ∂(ν.map Ψ), ∀ i : Fin N, Tendsto (fun n : ℕ => x n i / (n : ℝ)) atTop (𝓝 v) :=
    (MeasureTheory.ae_map_iff hΨ.aemeasurable hmeas).2 hν
  rw [← hmap] at h1
  exact (MeasureTheory.ae_map_iff hΦ.aemeasurable hmeas).1 h1

/-! ## 4. The capstone: the source's common speed from the neutral regeneration law

The source's Proposition `regen` produces the i.i.d. increments under `P^* = P(. | V)` and,
under `P`, an almost surely finite regeneration time after which the translated future has
law `P^*`.  The theorem below is exactly the assembly of those two facts into the paper's
Theorem 1.1.  The measure `nu` plays the role of `P^*`; the hypothesis `hmap` is the
statement "the translated future has law `P^*`", written as an identity of path laws. -/

/-- **The paper's Theorem 1.1 for the actual array model, from the neutral regeneration law.**

Let `nu` be a probability measure on the sample space (the source's `P^*`) under which the
successive regeneration increments `(D, T)` satisfy `Swarm.RegenLaw` — integrable,
pairwise independent, identically distributed distances and durations with `T >= 1` — and
the source's path structure `Swarm.Sandwich` holds.  Assume moreover that the law of the
translated actual future `n |-> X_{n+S}^i - c` is the law of the `nu`-path (the source's
"after an almost surely finite regeneration time the translated future has law `P^*`").
Then there are `kappa > 0` (the ballistic constant, uniform in `N`) and
`v = E_nu D_0 / E_nu T_0` with `kappa <= v <= 2p-1` such that, under the **original** law,
almost surely every walker satisfies `X_n^i / n -> v`.

Nothing here is assumed about the law of the initial block under the original measure: the
shift `(S, c)` absorbs it, which is exactly the source's initial-regeneration step. -/
theorem actual_common_speed_of_neutral_regen
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N)
    (ν : Measure (Array N)) [IsProbabilityMeasure ν]
    (D T : ℕ → Array N → ℕ)
    (hreg : Swarm.RegenLaw ν D T)
    (hsand : Swarm.Sandwich ν (Swarm.actualX (N := N) p m) D T)
    (S : Array N → ℕ) (c : Array N → ℝ) (hS : Measurable S) (hc : Measurable c)
    (hmap : Measure.map (fun U : Array N => fun (n : ℕ) (i : Fin N) =>
        Swarm.pos (Swarm.actualX (N := N) p m) (n + S U) i U - c U) (arrayMeasure N)
      = Measure.map (actPath (N := N) p m) ν) :
    ∃ κ : ℝ, 0 < κ ∧
      κ ≤ (∫ U, (D 0 U : ℝ) ∂ν) / (∫ U, (T 0 U : ℝ) ∂ν) ∧
      (∫ U, (D 0 U : ℝ) ∂ν) / (∫ U, (T 0 U : ℝ) ∂ν) ≤ 2 * p - 1 ∧
      ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
        Tendsto (fun n : ℕ => Swarm.pos (Swarm.actualX (N := N) p m) n i U / (n : ℝ)) atTop
          (𝓝 ((∫ U, (D 0 U : ℝ) ∂ν) / (∫ U, (T 0 U : ℝ) ∂ν))) := by
  classical
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  obtain ⟨κ, hκpos, hκlim⟩ := Swarm.actualProjectedBallistic hp0 hp1 hm
  set v : ℝ := (∫ U, (D 0 U : ℝ) ∂ν) / (∫ U, (T 0 U : ℝ) ∂ν) with hv
  have hνlim : ∀ᵐ U ∂ν, ∀ i : Fin N,
      Tendsto (fun n : ℕ => actPath (N := N) p m U n i / (n : ℝ)) atTop (𝓝 v) := by
    filter_upwards [Swarm.ae_tendsto_of_regen (μ := ν)
      (X := Swarm.actualX (N := N) p m) hreg hsand] with U hU i
    exact hU i
  have hshift : ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
      Tendsto (fun n : ℕ =>
        (Swarm.pos (Swarm.actualX (N := N) p m) (n + S U) i U - c U) / (n : ℝ)) atTop (𝓝 v) :=
    ae_forall_tendsto_div_of_map_eq (μ := arrayMeasure N) (ν := ν)
      (Ψ := actPath (N := N) p m)
      (Φ := fun U : Array N => fun (n : ℕ) (i : Fin N) =>
        Swarm.pos (Swarm.actualX (N := N) p m) (n + S U) i U - c U)
      (measurable_actPath p m) (measurable_shiftPath p m S c hS hc) hmap hνlim
  have hmain : ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
      Tendsto (fun n : ℕ => Swarm.pos (Swarm.actualX (N := N) p m) n i U / (n : ℝ)) atTop
        (𝓝 v) := by
    filter_upwards [hshift] with U hU i
    exact Swarm.tendsto_div_of_translate
      (y := fun n => Swarm.pos (Swarm.actualX (N := N) p m) n i U) (c := c U) (S := S U) (hU i)
  refine ⟨κ, hκpos, ?_, ?_, ?_⟩
  · by_cases hcase : κ ≤ v
    · simpa [hv] using hcase
    · exfalso
      have hall : ∀ᵐ U ∂(arrayMeasure N), κ ≤ v := by
        have i₀ : Fin N := ⟨0, by omega⟩
        filter_upwards [hκlim N hN, hmain] with U hb hcl
        exact Swarm.le_of_le_liminf_of_tendsto (hcl i₀) (by simpa using hb i₀)
      exact absurd (MeasureTheory.ae_iff.1 hall) (by simp [hcase])
  · by_cases hcase : v ≤ 2 * p - 1
    · simpa [hv] using hcase
    · exfalso
      have i₀ : Fin N := ⟨0, by omega⟩
      have hall : ∀ᵐ U ∂(arrayMeasure N), v ≤ 2 * p - 1 := by
        filter_upwards [hmain, SwarmDens.actual_ae_limsup_pos_div_le (N := N) hp0 hp1 m i₀]
          with U hcl hsup
        rw [← (hcl i₀).limsup_eq]
        exact hsup
      exact absurd (MeasureTheory.ae_iff.1 hall) (by simp [hcase])
  · simpa [hv] using hmain

/-- **The neutral interface is weaker than `Swarm.ActualRegen`.**  Taking `nu` to be the
original law itself and `(S, c) = (0, 0)`, the capstone reproduces the paper's Theorem 1.1
from i.i.d. increments under the original law: the hypothesis set of
`Swarm.main_theorem_actual_of_actual_regeneration` implies the one used here. -/
theorem actual_common_speed_of_actual_regen
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N)
    (D T : ℕ → Array N → ℕ)
    (hreg : Swarm.RegenLaw (arrayMeasure N) D T)
    (hsand : Swarm.Sandwich (arrayMeasure N) (Swarm.actualX (N := N) p m) D T) :
    ∃ κ : ℝ, 0 < κ ∧
      κ ≤ (∫ U, (D 0 U : ℝ) ∂(arrayMeasure N)) / (∫ U, (T 0 U : ℝ) ∂(arrayMeasure N)) ∧
      (∫ U, (D 0 U : ℝ) ∂(arrayMeasure N)) / (∫ U, (T 0 U : ℝ) ∂(arrayMeasure N)) ≤ 2 * p - 1 ∧
      ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
        Tendsto (fun n : ℕ => Swarm.pos (Swarm.actualX (N := N) p m) n i U / (n : ℝ)) atTop
          (𝓝 ((∫ U, (D 0 U : ℝ) ∂(arrayMeasure N))
            / (∫ U, (T 0 U : ℝ) ∂(arrayMeasure N)))) := by
  classical
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  refine actual_common_speed_of_neutral_regen (N := N) hp0 hp1 hm hN
    (arrayMeasure N) D T hreg hsand (fun _ => 0) (fun _ => 0) measurable_const measurable_const ?_
  have hzero : (fun U : Array N => fun (n : ℕ) (i : Fin N) =>
      Swarm.pos (Swarm.actualX (N := N) p m) (n + (fun _ => 0) U) i U - (fun _ => 0) U)
      = actPath (N := N) p m := by
    funext U n i
    simp [actPath]
  rw [hzero]


/-- **The common speed from the neutral *exponential-defect* data only.**

This is the shape in which the frontier produces the regeneration input: under the neutral
measure `nu` (the source's `P^*`) one has the distance increments `D` integrable, pairwise
independent and identically distributed, `T >= 1`, the path structure `Sandwich`, and the
paper's positive lower speed.  The duration integrability `E_nu T_0 < inf` is **derived**
from the positive lower speed by the source's §3.4 contradiction argument
(`Swarm.integrable_duration_of_regenLawWeak`), so it is not a premise.  With the
initial-regeneration law identity `hmap` this gives the paper's Theorem 1.1 under the
original law.

So the only stochastic inputs are: the neutral-measure increment structure, the neutral-measure
lower speed, and the law of the translated future — no `hmass`, no `hfac`, no i.i.d. claim
under the original law. -/
theorem actual_common_speed_of_neutral_ED
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N)
    (ν : Measure (Array N)) [IsProbabilityMeasure ν]
    (D T : ℕ → Array N → ℕ)
    {κ : ℝ} (hκ : 0 < κ)
    (hreg : Swarm.RegenLawWeak ν D T)
    (hsand : Swarm.Sandwich ν (Swarm.actualX (N := N) p m) D T)
    (hballν : ∀ᵐ U ∂ν, ∀ i : Fin N,
      κ ≤ liminf (fun n : ℕ => Swarm.pos (Swarm.actualX (N := N) p m) n i U / (n : ℝ)) atTop)
    (hbdν : ∀ᵐ U ∂ν, ∀ (i : Fin N) (n : ℕ),
      -(1 : ℝ) ≤ Swarm.pos (Swarm.actualX (N := N) p m) n i U / (n : ℝ))
    (S : Array N → ℕ) (c : Array N → ℝ) (hS : Measurable S) (hc : Measurable c)
    (hmap : Measure.map (fun U : Array N => fun (n : ℕ) (i : Fin N) =>
        Swarm.pos (Swarm.actualX (N := N) p m) (n + S U) i U - c U) (arrayMeasure N)
      = Measure.map (actPath (N := N) p m) ν) :
    0 < (∫ U, (D 0 U : ℝ) ∂ν) / (∫ U, (T 0 U : ℝ) ∂ν) ∧
      (∫ U, (D 0 U : ℝ) ∂ν) / (∫ U, (T 0 U : ℝ) ∂ν) ≤ 2 * p - 1 ∧
      ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
        Tendsto (fun n : ℕ => Swarm.pos (Swarm.actualX (N := N) p m) n i U / (n : ℝ)) atTop
          (𝓝 ((∫ U, (D 0 U : ℝ) ∂ν) / (∫ U, (T 0 U : ℝ) ∂ν))) := by
  classical
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hintT : Integrable (fun U => (T 0 U : ℝ)) ν :=
    Swarm.integrable_duration_of_regenLawWeak (X := Swarm.actualX (N := N) p m)
      hκ (by omega) hreg hsand hballν hbdν
  have hreg' : Swarm.RegenLaw ν D T := Swarm.regenLaw_of_regenLawWeak hreg hintT
  obtain ⟨κ', hκ'pos, _hκ'le, hκ'up, hlim⟩ :=
    actual_common_speed_of_neutral_regen (N := N) hp0 hp1 hm hN ν D T hreg' hsand S c hS hc hmap
  -- positivity of the neutral speed from the neutral lower bound
  have hvpos : 0 < (∫ U, (D 0 U : ℝ) ∂ν) / (∫ U, (T 0 U : ℝ) ∂ν) := by
    by_cases hcase : κ ≤ (∫ U, (D 0 U : ℝ) ∂ν) / (∫ U, (T 0 U : ℝ) ∂ν)
    · exact lt_of_lt_of_le hκ hcase
    · exfalso
      have hall : ∀ᵐ U ∂ν, κ ≤
          (∫ U, (D 0 U : ℝ) ∂ν) / (∫ U, (T 0 U : ℝ) ∂ν) := by
        have i₀ : Fin N := ⟨0, by omega⟩
        filter_upwards [Swarm.ae_tendsto_of_regen (μ := ν)
          (X := Swarm.actualX (N := N) p m) hreg' hsand, hballν] with U hc hb
        exact Swarm.le_of_le_liminf_of_tendsto (hc i₀) (hb i₀)
      exact absurd (MeasureTheory.ae_iff.1 hall) (by simp [hcase])
  exact ⟨hvpos, hκ'up, hlim⟩


/-- **The paper's Theorem 1.1 with the ballistic bounds discharged at the actual law.**

The neutral speed bounds `hballν` and `hbdν` of `actual_common_speed_of_neutral_ED` are *not*
extra hypotheses when the neutral measure is absolutely continuous with respect to the
original law — which is exactly the case for the source's `P^* = P(. | V)` when `P(V) > 0`.
The positive lower speed and the trivial bound `|X_n| <= n` are theorems of the tree for the
actual array law (`Swarm.actualProjectedBallistic`, `Swarm.abs_le_time_of_law`), and pass to
every absolutely continuous measure.

So the complete premise list is: `nu ≪ P`, the i.i.d. regeneration increments with the
`Sandwich` structure under `nu`, and the law of the translated future — the source's
Proposition `front` + `regen` + initial regeneration, and nothing else. -/
theorem actual_common_speed_of_neutral_ac
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N)
    (ν : Measure (Array N)) [IsProbabilityMeasure ν]
    (hac : ν ≪ arrayMeasure N)
    (D T : ℕ → Array N → ℕ)
    (hreg : Swarm.RegenLawWeak ν D T)
    (hsand : Swarm.Sandwich ν (Swarm.actualX (N := N) p m) D T)
    (S : Array N → ℕ) (c : Array N → ℝ) (hS : Measurable S) (hc : Measurable c)
    (hmap : Measure.map (fun U : Array N => fun (n : ℕ) (i : Fin N) =>
        Swarm.pos (Swarm.actualX (N := N) p m) (n + S U) i U - c U) (arrayMeasure N)
      = Measure.map (actPath (N := N) p m) ν) :
    0 < (∫ U, (D 0 U : ℝ) ∂ν) / (∫ U, (T 0 U : ℝ) ∂ν) ∧
      (∫ U, (D 0 U : ℝ) ∂ν) / (∫ U, (T 0 U : ℝ) ∂ν) ≤ 2 * p - 1 ∧
      ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
        Tendsto (fun n : ℕ => Swarm.pos (Swarm.actualX (N := N) p m) n i U / (n : ℝ)) atTop
          (𝓝 ((∫ U, (D 0 U : ℝ) ∂ν) / (∫ U, (T 0 U : ℝ) ∂ν))) := by
  classical
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  obtain ⟨κ, hκpos, hκlim⟩ := Swarm.actualProjectedBallistic hp0 hp1 hm
  -- the actual law satisfies the marginal model law, hence `|X_n| <= n`
  obtain ⟨𝓕, hlaw⟩ : ∃ 𝓕 : Filtration ℕ (inferInstanceAs (MeasurableSpace (Array N))),
      Swarm.IsInteractingLaw 𝓕 (arrayMeasure N) (Swarm.actualX (N := N) p m) m p :=
    ⟨_, SwarmCross.Actual.actual_isInteractingLaw (N := N) hp0 hp1 m⟩
  have hbdμ : ∀ᵐ U ∂(arrayMeasure N), ∀ (i : Fin N) (n : ℕ),
      -(1 : ℝ) ≤ Swarm.pos (Swarm.actualX (N := N) p m) n i U / (n : ℝ) := by
    have hb := Swarm.abs_le_time_of_law hlaw
    refine Eventually.of_forall fun U i n => ?_
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [Swarm.pos]
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hX : -(n : ℝ) ≤ ((Swarm.actualX (N := N) p m n U i : ℤ) : ℝ) := by
        have h := (abs_le.mp (hb n U i)).1
        have h' : (-(n : ℤ) : ℤ) ≤ Swarm.actualX (N := N) p m n U i := by omega
        exact_mod_cast h'
      have hdiv : -(1 : ℝ) ≤ ((Swarm.actualX (N := N) p m n U i : ℤ) : ℝ) / (n : ℝ) := by
        rw [le_div_iff₀ hnpos]
        nlinarith
      simpa [Swarm.pos] using hdiv
  exact actual_common_speed_of_neutral_ED (N := N) hp0 hp1 hm hN ν D T hκpos hreg hsand
    (hac.ae_le (hκlim N hN)) (hac.ae_le hbdμ) S c hS hc hmap


/-- **The neutral speed does not depend on the chosen `P^*` / regeneration construction.**

Two neutral regeneration laws satisfying the capstone's hypotheses produce the same speed,
because both are the almost sure limit of the *same* actual path.  This is the actual-law
counterpart of `Swarm.mean_speed_unique`: `v_{N,m}(p) = E^*D_1 / E^*T_1` is a property of
the model, not of the construction of the neutral measure. -/
theorem neutral_speed_unique
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N)
    {ν₁ ν₂ : Measure (Array N)} [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    {D₁ T₁ D₂ T₂ : ℕ → Array N → ℕ}
    (hreg₁ : Swarm.RegenLaw ν₁ D₁ T₁) (hsand₁ : Swarm.Sandwich ν₁ (Swarm.actualX (N := N) p m) D₁ T₁)
    (hreg₂ : Swarm.RegenLaw ν₂ D₂ T₂) (hsand₂ : Swarm.Sandwich ν₂ (Swarm.actualX (N := N) p m) D₂ T₂)
    (S₁ : Array N → ℕ) (c₁ : Array N → ℝ) (hS₁ : Measurable S₁) (hc₁ : Measurable c₁)
    (S₂ : Array N → ℕ) (c₂ : Array N → ℝ) (hS₂ : Measurable S₂) (hc₂ : Measurable c₂)
    (hmap₁ : Measure.map (fun U : Array N => fun (n : ℕ) (i : Fin N) =>
        Swarm.pos (Swarm.actualX (N := N) p m) (n + S₁ U) i U - c₁ U) (arrayMeasure N)
      = Measure.map (actPath (N := N) p m) ν₁)
    (hmap₂ : Measure.map (fun U : Array N => fun (n : ℕ) (i : Fin N) =>
        Swarm.pos (Swarm.actualX (N := N) p m) (n + S₂ U) i U - c₂ U) (arrayMeasure N)
      = Measure.map (actPath (N := N) p m) ν₂) :
    (∫ U, (D₁ 0 U : ℝ) ∂ν₁) / (∫ U, (T₁ 0 U : ℝ) ∂ν₁)
      = (∫ U, (D₂ 0 U : ℝ) ∂ν₂) / (∫ U, (T₂ 0 U : ℝ) ∂ν₂) := by
  classical
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  obtain ⟨_, _, _, _, hlim₁⟩ :=
    actual_common_speed_of_neutral_regen (N := N) hp0 hp1 hm hN ν₁ D₁ T₁ hreg₁ hsand₁
      S₁ c₁ hS₁ hc₁ hmap₁
  obtain ⟨_, _, _, _, hlim₂⟩ :=
    actual_common_speed_of_neutral_regen (N := N) hp0 hp1 hm hN ν₂ D₂ T₂ hreg₂ hsand₂
      S₂ c₂ hS₂ hc₂ hmap₂
  by_contra hne
  have hall : ∀ᵐ U ∂(arrayMeasure N),
      (∫ U, (D₁ 0 U : ℝ) ∂ν₁) / (∫ U, (T₁ 0 U : ℝ) ∂ν₁)
        = (∫ U, (D₂ 0 U : ℝ) ∂ν₂) / (∫ U, (T₂ 0 U : ℝ) ∂ν₂) := by
    have i₀ : Fin N := ⟨0, by omega⟩
    filter_upwards [hlim₁, hlim₂] with U h1 h2
    exact tendsto_nhds_unique (h1 i₀) (h2 i₀)
  exact absurd (MeasureTheory.ae_iff.1 hall) (by simp [hne])


/-! ## 5. The source-faithful form: `Sandwich` is derived from the regeneration sequence -/

/-- **`Swarm.Sandwich` from a random regeneration sequence.**  Pointwise
`M6Star.sandwich_of_regenSequence`, transported to the almost sure form the assembly uses. -/
theorem Sandwich_of_regenSequence_ae (p : ℝ) (m : ℕ) {ν : Measure (Array N)}
    [IsProbabilityMeasure ν] (σ z : ℕ → Array N → ℕ)
    (hσ0 : ∀ᵐ U ∂ν, σ 0 U = 0) (hz0 : ∀ᵐ U ∂ν, z 0 U = 0)
    (hσmono : ∀ᵐ U ∂ν, Monotone fun k => σ k U)
    (hzmono : ∀ᵐ U ∂ν, Monotone fun k => z k U)
    (hlevel : ∀ᵐ U ∂ν, ∀ (k : ℕ) (i : Fin N),
      Swarm.actualX (N := N) p m (σ k U) U i = (z k U : ℤ))
    (hnoReturn : ∀ᵐ U ∂ν, ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, σ k U < n → ∀ i : Fin N,
      (z k U : ℤ) < Swarm.actualX (N := N) p m n U i)
    (hfirst : ∀ᵐ U ∂ν, ∀ (k n : ℕ) (i : Fin N),
      n < σ (k + 1) U → Swarm.actualX (N := N) p m n U i < (z (k + 1) U : ℤ)) :
    Swarm.Sandwich ν (Swarm.actualX (N := N) p m)
      (fun k U => z (k + 1) U - z k U) (fun k U => σ (k + 1) U - σ k U) := by
  filter_upwards [hσ0, hz0, hσmono, hzmono, hlevel, hnoReturn, hfirst]
    with U h0σ h0z hmσ hmz hl hnr hf
  exact sandwich_of_regenSequence (x := fun n i => Swarm.actualX (N := N) p m n U i)
    h0σ h0z hmσ hmz hl hnr hf

/-- **The paper's Theorem 1.1 from the source's own regeneration data.**

The abstract `Sandwich` premise is replaced by the source's regeneration sequence: times
`sigma k`, levels `z k`, with `sigma 0 = z 0 = 0`, both monotone, the level attained at the
regeneration time, no return to or below the level afterwards, and the level `z (k+1)` first
reached at `sigma (k+1)`.  The increments are the successive differences
`D k = z (k+1) - z k`, `T k = sigma (k+1) - sigma k`, and the neutral law gives them to us
with distance integrability, pairwise independence, identical distributions and `T >= 1`. -/
theorem actual_common_speed_of_regen_sequence
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N)
    (ν : Measure (Array N)) [IsProbabilityMeasure ν] (hac : ν ≪ arrayMeasure N)
    (σ z : ℕ → Array N → ℕ)
    (hreg : Swarm.RegenLawWeak ν (fun k U => z (k + 1) U - z k U)
      (fun k U => σ (k + 1) U - σ k U))
    (hσ0 : ∀ᵐ U ∂ν, σ 0 U = 0) (hz0 : ∀ᵐ U ∂ν, z 0 U = 0)
    (hσmono : ∀ᵐ U ∂ν, Monotone fun k => σ k U)
    (hzmono : ∀ᵐ U ∂ν, Monotone fun k => z k U)
    (hlevel : ∀ᵐ U ∂ν, ∀ (k : ℕ) (i : Fin N),
      Swarm.actualX (N := N) p m (σ k U) U i = (z k U : ℤ))
    (hnoReturn : ∀ᵐ U ∂ν, ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, σ k U < n → ∀ i : Fin N,
      (z k U : ℤ) < Swarm.actualX (N := N) p m n U i)
    (hfirst : ∀ᵐ U ∂ν, ∀ (k n : ℕ) (i : Fin N),
      n < σ (k + 1) U → Swarm.actualX (N := N) p m n U i < (z (k + 1) U : ℤ))
    (S : Array N → ℕ) (c : Array N → ℝ) (hS : Measurable S) (hc : Measurable c)
    (hmap : Measure.map (fun U : Array N => fun (n : ℕ) (i : Fin N) =>
        Swarm.pos (Swarm.actualX (N := N) p m) (n + S U) i U - c U) (arrayMeasure N)
      = Measure.map (actPath (N := N) p m) ν) :
    0 < (∫ U, ((z (0 + 1) U - z 0 U : ℕ) : ℝ) ∂ν)
        / (∫ U, ((σ (0 + 1) U - σ 0 U : ℕ) : ℝ) ∂ν) ∧
      (∫ U, ((z (0 + 1) U - z 0 U : ℕ) : ℝ) ∂ν)
          / (∫ U, ((σ (0 + 1) U - σ 0 U : ℕ) : ℝ) ∂ν) ≤ 2 * p - 1 ∧
      ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
        Tendsto (fun n : ℕ => Swarm.pos (Swarm.actualX (N := N) p m) n i U / (n : ℝ)) atTop
          (𝓝 ((∫ U, ((z (0 + 1) U - z 0 U : ℕ) : ℝ) ∂ν)
            / (∫ U, ((σ (0 + 1) U - σ 0 U : ℕ) : ℝ) ∂ν))) := by
  have hsand := Sandwich_of_regenSequence_ae (N := N) p m σ z hσ0 hz0 hσmono hzmono
    hlevel hnoReturn hfirst
  exact actual_common_speed_of_neutral_ac (N := N) hp0 hp1 hm hN ν hac
    (fun k U => z (k + 1) U - z k U) (fun k U => σ (k + 1) U - σ k U)
    hreg hsand S c hS hc hmap

end M6Star

/-! ### Axiom audit -/


