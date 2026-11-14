/-
# Clock-fibre random-start Azuma: the record-time truncation is not needed

    stall  ⊆  {defect at the fibre ≥ θ}  ∪  ⋃_i {|M^i jump| ≥ θ},   θ = c L / (2N),

and then bounds the second alternative only on the *truncated* clock event
`{recTimeA r ≤ K}`, at the cost of a `(K+1)·N·2exp(-θ²/(16TL))` factor
(`stall_measure_le_trunc`).  Its own README names the record-time tail as the
remaining input.

This file removes `K`: there is **no** record-time tail in the martingale
alternative.  The precise mechanism, and the reason the naive countable sum
does *not* give this, are as follows.

The clock fibres `clockFibre r n = {U | runMax (actX U) n = r ∧ ∀ j < n, runMax (actX U) j ≠ r}`
are `ℱ_n`-measurable (the record time is a stopping time with respect to the
enlarged filtration), pairwise disjoint, and cover `ReachAll`, which is almost
sure.  Hence the martingale-jump event is the disjoint union of the pieces
`clockFibre r n ∩ A_n`, where `A_n` is the fixed-start deviation event at the
deterministic start `n`.

* Subadditivity alone does **not** prove the claim: it gives
  `μ(A_τ) ≤ Σ_n min (μ(fibre n), b) ≤ 1` with `b = 2exp(-θ²/(16W))`, since the
  fibre masses are not controlled.  Summing the *unconditional* fixed-start
  bounds `μ(A_n) ≤ b` over `n` diverges.  This is exactly the gap that made the
  `(K+1)` truncation necessary.

* What closes the gap is a **conditional** (per-fibre) statement, which is
  available because the fibre belongs to `ℱ_n`: conditionally on the fibre, the
  future increments `martIncr (n+k) i` are still martingale differences for the
  same enlarged filtration.  Formally, for `ν = (μ (fibre n))⁻¹ • μ.restrict (fibre n)`,
  every `ℱ_{n+k}`-measurable set `s` satisfies
  `∫_s martIncr (n+k) i dν = 0`, because `s ∩ fibre n ∈ ℱ_{n+k}` and the
  increments are conditionally centred under `μ`.  The abstract Azuma--Hoeffding
  bound `LocMart.measure_abs_psum_ge_le` is already stated for an *arbitrary*
  probability measure, so it applies verbatim to `ν`, and gives
  `μ (fibre n ∩ A_n) = μ (fibre n) · ν (A_n) ≤ μ (fibre n) · b`.
  The countable sum then collapses because `Σ_n μ (fibre n) ≤ 1`.

No optional stopping theorem is used, and no statement about `E[M_τ]` is made:
the bound is a Chernoff estimate for the future window at the random clock,
proved fibre by fibre.  The almost-sure record statement enters only through
`ReachAllᶜ` being null (proved, not assumed).

Consequences:

* `martJumpSet_measure_le` : `μ.real (martJumpSet θ) ≤ N · 2 exp (-θ² / (16 W))`
  for **every** record level `r`, window `W ≥ 1` and `0 < θ ≤ 4W` — the same
  bound as the truncated form but with no `K`.
* `stall_measure_le_full` : the full swarm-stall tail is at most the defect tail
  at the fibre plus `N · 2 exp (-θ²/(16 T L))`; the record-clock tail is gone.
* `recordAdvance_measure_le` / `recordAdvance_measure_le_defectHigh` : the literal
  record-advance exception `τ_r + T*L < τ_{r+B*L}` (`QuantitativeRestrictedBand.timeLag`)
  inherits the bound, and the defect term may be taken at the paper's `L/8` scale
  once `c ≥ N/4`.

What remains, explicitly: the defect tail at the fibre (the first alternative),
and the numerical choice of `T` making `c = (2p-1)(N-2m)T - NB > 0` (possible
exactly when `N > 2m`).  Nothing here asserts tightness, an invariant law, or
`MainClaim`.
-/
import Swarm.ExcOccupation
import Mathlib.MeasureTheory.Order.Group.Lattice
import Swarm.RecordMeas

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped ENNReal BigOperators

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory
open RecordDefect
open SwarmRecordMeas SwarmRecordMeas.Actual

namespace ClockFibre

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 0. The clock fibres of the canonical record clock -/

/-- **The level-`r` clock fibre at time `n`**: `n` is the first time the running maximum
of the actual swarm reaches `r`. -/
def clockFibre (p : ℝ) (m r n : ℕ) : Set (Array N) :=
  {U | runMax (RecordoSupply.actX p m U) n = (r : ℤ) ∧
    ∀ j : ℕ, j < n → runMax (RecordoSupply.actX p m U) j ≠ (r : ℤ)}

/-- `runMax` at a time inside the horizon is measurable for the enlarged filtration. -/
theorem measurable_runMax_enl (p : ℝ) (m n k : ℕ) (hk : k ≤ n) :
    Measurable[Enl.enlFilt p m n] fun U : Array N => runMax (RecordoSupply.actX p m U) k := by
  letI : MeasurableSpace (Array N) := Enl.enlFilt p m n
  refine measurable_to_countable' fun r => ?_
  have hf : ∀ i : Fin N, Measurable fun U : Array N => RecordoSupply.actX p m U i k :=
    fun i => Enl.enl_pos_measurable p m n hk i
  have hsup : Measurable fun U : Array N =>
      Finset.univ.sup' Finset.univ_nonempty (fun i => RecordoSupply.actX p m U i k) :=
    SwarmRecordMeas.measurable_finset_sup' hf
  simpa only [RecordDefect.runMax] using hsup (measurableSet_singleton r)

/-- **The clock fibre is measurable at its own time**: `recTimeA r` is a stopping time for
the enlarged filtration, expressed through the finite first-hit description. -/
theorem measurableSet_clockFibre (p : ℝ) (m r n : ℕ) :
    MeasurableSet[Enl.enlFilt p m n] (clockFibre (N := N) p m r n) := by
  have h1 : MeasurableSet[Enl.enlFilt p m n]
      {U : Array N | runMax (RecordoSupply.actX p m U) n = (r : ℤ)} := by
    have h := measurable_runMax_enl (N := N) p m n n le_rfl
      (t := ({((r : ℤ))} : Set ℤ)) (measurableSet_singleton _)
    exact h
  have h2 : MeasurableSet[Enl.enlFilt p m n]
      (⋂ j ∈ Finset.range n,
        {U : Array N | runMax (RecordoSupply.actX p m U) j ≠ (r : ℤ)}) := by
    refine MeasurableSet.biInter (Finset.countable_toSet _) fun j hj => ?_
    have hj' : j ≤ n := le_of_lt (Finset.mem_range.1 hj)
    have h := measurable_runMax_enl (N := N) p m n j hj'
      (t := ({((r : ℤ))} : Set ℤ)) (measurableSet_singleton _)
    have h' : MeasurableSet[Enl.enlFilt p m n]
        {U : Array N | runMax (RecordoSupply.actX p m U) j ≠ (r : ℤ)} := h.compl
    exact h'
  have hset : clockFibre (N := N) p m r n =
      {U : Array N | runMax (RecordoSupply.actX p m U) n = (r : ℤ)} ∩
        ⋂ j ∈ Finset.range n,
          {U : Array N | runMax (RecordoSupply.actX p m U) j ≠ (r : ℤ)} := by
    ext U
    simp only [clockFibre, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
      Finset.mem_range]
  rw [hset]
  exact h1.inter h2

/-- The clock fibres of distinct times are disjoint. -/
theorem disjoint_clockFibre (p : ℝ) (m r n n' : ℕ) (h : n ≠ n') :
    Disjoint (clockFibre (N := N) p m r n) (clockFibre (N := N) p m r n') := by
  rw [Set.disjoint_left]
  intro U h1 h2
  rcases lt_or_gt_of_ne h with hlt | hlt
  · exact h2.2 n hlt h1.1
  · exact h1.2 n' hlt h2.1

/-- A clock fibre is contained in the event that level `r` is reached at its time. -/
theorem clockFibre_subset_reach (p : ℝ) (m r n : ℕ) :
    clockFibre (N := N) p m r n ⊆
      {U : Array N | runMax (RecordoSupply.actX p m U) n = (r : ℤ)} :=
  fun _ h => h.1

/-- On `ReachAll` the clock fibres cover the whole space. -/
theorem reachAll_subset_iUnion_clockFibre (p : ℝ) (m r : ℕ) :
    ReachAll p m ⊆ ⋃ n : ℕ, clockFibre (N := N) p m r n := by
  intro U hU
  refine Set.mem_iUnion.2 ⟨recTimeA p m U r, ?_, ?_⟩
  · exact (recTimeA_spec p m U r).resolve_left (fun h => h hU)
  · intro j hj hval
    exact recTimeA_min p m U r j hj (Or.inr hval)

/-- On `ReachAll`, inside the clock fibre of time `n`, the canonical record time is `n`. -/
theorem recTimeA_eq_of_mem_clockFibre {p : ℝ} {m r n : ℕ} {U : Array N}
    (hU : U ∈ ReachAll p m) (h : U ∈ clockFibre (N := N) p m r n) :
    recTimeA p m U r = n :=
  (recTimeA_eq_iff p m U r n hU).2 ⟨h.1, h.2⟩

/-- **`ReachAll` holds almost surely** (proved from the actual ballistic lower bound; no
extra hypothesis beyond `2 ≤ m`, `2 ≤ N`). -/
theorem ae_mem_reachAll {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) :
    ∀ᵐ U ∂(arrayMeasure N), U ∈ ReachAll p m := by
  filter_upwards [ae_isRecord_recTimeA (N := N) hp0 hp1 hm hN] with U hU r
  exact ⟨recTimeA p m U r, (hU r).2⟩

/-! ## 1. The drift-martingale tail at an arbitrary probability measure -/

variable {μ : Measure (Swarming.Uniform.Array N)}

/-- Integrability of the drift-martingale increment under the array measure. -/
theorem integrable_martIncr {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m t : ℕ)
    (i : Fin N) :
    Integrable (fun U : Array N => ExcOcc.martIncr p m t i U) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hinc : Integrable (Increment.inc p m t i) (arrayMeasure N) :=
    (ExcOcc.integrable_pos_cast p m (t + 1) (t + 1) (le_rfl) i).sub
      (ExcOcc.integrable_pos_cast p m (t + 1) t (by omega) i)
  have hα : Integrable (fun U : Array N => 2 * SwarmCross.alphaFun p m t i U - 1)
      (arrayMeasure N) :=
    ((ExcOcc.integrable_alphaFun (N := N) hp0 hp1 m t i).const_mul 2).sub
      (integrable_const (1 : ℝ))
  have hfun : ExcOcc.martIncr p m t i =
      fun U => Increment.inc p m t i U - (2 * SwarmCross.alphaFun p m t i U - 1) := rfl
  rw [hfun]
  exact hinc.sub hα

/-- **Azuma–Hoeffding for the drift martingale at an arbitrary probability measure.**
This is `ExcOcc.driftMartingale_tail` with `arrayMeasure` replaced by an arbitrary probability
measure `μ`: the only probabilistic input is that each increment is conditionally centred on
the enlarged filtration. -/
theorem driftMartingale_tail_of_prob [IsProbabilityMeasure μ] {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m n W : ℕ) (hW : 1 ≤ W) (i : Fin N) {ε : ℝ}
    (hε : 0 < ε) (hεW : ε ≤ 4 * W)
    (hmean : ∀ k : ℕ, μ[(fun U : Array N => ExcOcc.martIncr p m (n + k) i U) |
      Enl.enlFilt p m (n + k)] =ᵐ[μ] 0) :
    μ.real {U : Array N | ε ≤ |driftMartingale p m U (n + W) i - driftMartingale p m U n i|}
      ≤ 2 * Real.exp (-(ε ^ 2) / (16 * (W : ℝ))) := by
  have hmeas : ∀ k : ℕ, StronglyMeasurable[(ExcOcc.shiftFilt (N := N) p m n) (k + 1)]
      (fun U : Array N => ExcOcc.martIncr p m (n + k) i U) :=
    fun k => ExcOcc.stronglyMeasurable_martIncr p m (n + k) i
  have hmean' : ∀ k : ℕ, μ[(fun U : Array N => ExcOcc.martIncr p m (n + k) i U) |
      (ExcOcc.shiftFilt (N := N) p m n) k] =ᵐ[μ] 0 := hmean
  have hmain := LocMart.measure_abs_psum_ge_le (μ := μ)
    (ℱ := ExcOcc.shiftFilt (N := N) p m n) (ξ := fun k U => ExcOcc.martIncr p m (n + k) i U)
    (C := 2) hmeas (by norm_num)
    (fun k U => ExcOcc.martIncr_abs_le (N := N) hp0 hp1 m (n + k) i U) hmean' hW hε
    (by
      have h2 : (2 : ℝ) * (W : ℝ) * 2 = 4 * (W : ℝ) := by ring
      linarith)
  have hset : {U : Array N |
        ε ≤ |LocMart.psum (fun k (U : Array N) => ExcOcc.martIncr p m (n + k) i U) W U|}
      = {U : Array N |
        ε ≤ |driftMartingale p m U (n + W) i - driftMartingale p m U n i|} := by
    ext U
    simp only [Set.mem_ofPred_eq]
    rw [ExcOcc.psum_martIncr]
  rw [hset] at hmain
  have hexp : -(ε ^ 2) / (4 * (W : ℝ) * 2 ^ 2) = -(ε ^ 2) / (16 * (W : ℝ)) := by
    have : 4 * (W : ℝ) * 2 ^ 2 = 16 * (W : ℝ) := by ring
    rw [this]
  rwa [hexp] at hmain

/-! ## 2. Conditioning on a fibre of the filtration -/

/-- Ambient measurability of the drift-martingale increment. -/
theorem measurable_martIncr (p : ℝ) (m t : ℕ) (i : Fin N) :
    Measurable fun U : Array N => ExcOcc.martIncr p m t i U := by
  have hcast : Measurable (fun z : ℤ => (z : ℝ)) := by fun_prop
  have h1 : Measurable[Enl.enlFilt p m (t + 1)]
      (fun U : Array N => ((trajectory p m U (t + 1)).pos i : ℝ)) :=
    hcast.comp (Enl.enl_pos_measurable p m (t + 1) (le_refl (t + 1)) i)
  have h0 : Measurable[Enl.enlFilt p m (t + 1)]
      (fun U : Array N => ((trajectory p m U t).pos i : ℝ)) :=
    hcast.comp (Enl.enl_pos_measurable p m (t + 1) (by omega) i)
  have hα : Measurable[Enl.enlFilt p m (t + 1)] (SwarmCross.alphaFun p m t i) :=
    (Enl.measurable_alphaFun_enl p m t i).mono ((Enl.enlFilt p m).mono (Nat.le_succ t)) le_rfl
  have hfun : ExcOcc.martIncr p m t i = fun U : Array N =>
      (((trajectory p m U (t + 1)).pos i : ℝ) - ((trajectory p m U t).pos i : ℝ))
        - (2 * SwarmCross.alphaFun p m t i U - 1) := rfl
  rw [hfun]
  exact ((h1.sub h0).sub ((hα.const_mul 2).sub measurable_const)).mono
    ((Enl.enlFilt p m).le (t + 1)) le_rfl

/-- **The increments stay conditionally centred on the intersection with a filtration set.**  For
`s ∈ ℱ_{n+k}` and `S ∈ ℱ_n`, the array-measure integral of `martIncr (n+k) i` over `s ∩ S`
vanishes.  This is the only structural input to the fibre-conditional Azuma bound. -/
theorem setIntegral_martIncr_inter {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m n : ℕ} {S : Set (Array N)} (hS : MeasurableSet[Enl.enlFilt p m n] S) (k : ℕ) (i : Fin N)
    {s : Set (Array N)} (hs : MeasurableSet[Enl.enlFilt p m (n + k)] s) :
    ∫ x in (s ∩ S), ExcOcc.martIncr p m (n + k) i x ∂(arrayMeasure N) = 0 := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hle : Enl.enlFilt p m (n + k) ≤ (inferInstance : MeasurableSpace (Array N)) :=
    (Enl.enlFilt p m).le (n + k)
  have hSle : MeasurableSet[Enl.enlFilt p m (n + k)] S :=
    (Enl.enlFilt p m).mono (Nat.le_add_right n k) S hS
  rw [← setIntegral_condExp hle (integrable_martIncr (N := N) hp0 hp1 m (n + k) i)
    (hs.inter hSle)]
  refine setIntegral_eq_zero_of_ae_eq_zero ?_
  filter_upwards [ExcOcc.condExp_martIncr (N := N) hp0 hp1 m (n + k) i] with x hx _
  exact hx

/-- The same integral under the fibre-conditional measure `c • μ.restrict S`. -/
theorem setIntegral_martIncr_smul_restrict {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m n : ℕ} {S : Set (Array N)} (hS : MeasurableSet[Enl.enlFilt p m n] S) (k : ℕ) (i : Fin N)
    {c : ℝ≥0∞} {s : Set (Array N)} (hs : MeasurableSet[Enl.enlFilt p m (n + k)] s) :
    ∫ x in s, ExcOcc.martIncr p m (n + k) i x ∂(c • (arrayMeasure N).restrict S) = 0 := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hle : Enl.enlFilt p m (n + k) ≤ (inferInstance : MeasurableSpace (Array N)) :=
    (Enl.enlFilt p m).le (n + k)
  have hs' : MeasurableSet s := hle s hs
  have hzero := setIntegral_martIncr_inter (N := N) hp0 hp1 hS k i hs
  calc ∫ x in s, ExcOcc.martIncr p m (n + k) i x ∂(c • (arrayMeasure N).restrict S)
      = ∫ x, ExcOcc.martIncr p m (n + k) i x
          ∂((c • (arrayMeasure N).restrict S).restrict s) := rfl
    _ = ∫ x, ExcOcc.martIncr p m (n + k) i x
          ∂(c • ((arrayMeasure N).restrict S).restrict s) := by rw [Measure.restrict_smul]
    _ = c.toReal • ∫ x, ExcOcc.martIncr p m (n + k) i x
          ∂(((arrayMeasure N).restrict S).restrict s) := by rw [integral_smul_measure]
    _ = c.toReal • ∫ x, ExcOcc.martIncr p m (n + k) i x
          ∂((arrayMeasure N).restrict (s ∩ S)) := by rw [Measure.restrict_restrict hs']
    _ = c.toReal • ∫ x in (s ∩ S), ExcOcc.martIncr p m (n + k) i x ∂(arrayMeasure N) := rfl
    _ = 0 := by rw [hzero, smul_zero]

/-- **Conditioning on a set of the filtration keeps martingale differences centred.**  For every
`S ∈ ℱ_n` and every `c ≠ ⊤`, the increments `martIncr (n+k) i` are conditionally centred under the
restricted measure `c • μ.restrict S`.  The proof is the set-integral characterisation of
`condExp`: for `s ∈ ℱ_{n+k}` the intersection `s ∩ S` still lies in `ℱ_{n+k}`, and there the
array-measure conditional expectation vanishes. -/
theorem condExp_martIncr_smul_restrict {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m n : ℕ} {S : Set (Array N)} (hS : MeasurableSet[Enl.enlFilt p m n] S) (k : ℕ) (i : Fin N)
    {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    (c • (arrayMeasure N).restrict S)[(fun U : Array N => ExcOcc.martIncr p m (n + k) i U) |
        Enl.enlFilt p m (n + k)] =ᵐ[c • (arrayMeasure N).restrict S] 0 := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hle : Enl.enlFilt p m (n + k) ≤ (inferInstance : MeasurableSpace (Array N)) :=
    (Enl.enlFilt p m).le (n + k)
  have hSle : MeasurableSet[Enl.enlFilt p m (n + k)] S :=
    (Enl.enlFilt p m).mono (Nat.le_add_right n k) S hS
  have hSamb : MeasurableSet S := hle S hSle
  -- the restricted measure is finite
  haveI : IsFiniteMeasure (c • (arrayMeasure N).restrict S) := by
    refine ⟨?_⟩
    rw [Measure.smul_apply, smul_eq_mul]
    refine ENNReal.mul_lt_top hc.lt_top ?_
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact measure_lt_top _ _
  haveI : IsFiniteMeasure ((c • (arrayMeasure N).restrict S).trim hle) := isFiniteMeasure_trim hle
  have hfint : Integrable (fun U : Array N => ExcOcc.martIncr p m (n + k) i U)
      (c • (arrayMeasure N).restrict S) := by
    refine Integrable.of_bound (measurable_martIncr (N := N) p m (n + k) i).aestronglyMeasurable 2 ?_
    filter_upwards with U
    rw [Real.norm_eq_abs]
    exact ExcOcc.martIncr_abs_le (N := N) hp0 hp1 m (n + k) i U
  refine ae_eq_comm.1 (ae_eq_condExp_of_forall_setIntegral_eq (μ := c • (arrayMeasure N).restrict S)
    (m := Enl.enlFilt p m (n + k)) (m₀ := (inferInstance : MeasurableSpace (Array N)))
    (f := fun U : Array N => ExcOcc.martIncr p m (n + k) i U) (g := fun _ => (0 : ℝ)) hle hfint
    (fun s _ _ => integrableOn_zero) ?_ aestronglyMeasurable_zero)
  intro s hs _
  rw [setIntegral_martIncr_smul_restrict (N := N) hp0 hp1 (n := n) hS k i (c := c) hs]
  simp

/-! ## 3. The per-fibre Azuma bound -/

/-- Measurability of the drift martingale in the array. -/
theorem measurable_driftMartingale (p : ℝ) (m n : ℕ) (i : Fin N) :
    Measurable fun U : Array N => driftMartingale p m U n i := by
  induction n with
  | zero =>
      have hzero : (fun U : Array N => driftMartingale p m U 0 i) = fun _ => (0 : ℝ) := by
        funext U
        simp [Swarming.Trajectory.driftMartingale, Swarming.Trajectory.excitedSteps]
      rw [hzero]
      exact measurable_const
  | succ n ih =>
      have hfun : (fun U : Array N => driftMartingale p m U (n + 1) i)
          = fun U => driftMartingale p m U n i + ExcOcc.martIncr p m n i U := by
        funext U
        rw [ExcOcc.martIncr_eq_driftMartingale]
        ring
      rw [hfun]
      exact ih.add (measurable_martIncr p m n i)

/-- The drift-martingale displacement event of walker `i` over the window starting at the
deterministic time `n`. -/
def martJumpAt (p : ℝ) (m n W : ℕ) (θ : ℝ) (i : Fin N) : Set (Array N) :=
  {U | θ ≤ |driftMartingale p m U (n + W) i - driftMartingale p m U n i|}

theorem measurableSet_martJumpAt (p : ℝ) (m n W : ℕ) (θ : ℝ) (i : Fin N) :
    MeasurableSet (martJumpAt (N := N) p m n W θ i) :=
  measurableSet_le measurable_const
    ((measurable_driftMartingale p m (n + W) i).sub (measurable_driftMartingale p m n i)).abs

/-- **The fibre-conditional Azuma bound, per walker.**  Inside the clock fibre of time `n`, the
mass of walker `i`'s displacement event is at most the fibre mass times the fixed-start Azuma
bound.  This is where conditioning on the fibre — rather than a union bound over starts —
enters. -/
theorem clockFibre_martJumpAt_measure_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m r n W : ℕ) (hW : 1 ≤ W) (i : Fin N) {θ : ℝ} (hθ : 0 < θ) (hθW : θ ≤ 4 * W) :
    (arrayMeasure N) (clockFibre (N := N) p m r n ∩ martJumpAt (N := N) p m n W θ i)
      ≤ (arrayMeasure N) (clockFibre (N := N) p m r n) *
          ENNReal.ofReal (2 * Real.exp (-(θ ^ 2) / (16 * (W : ℝ)))) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  set S : Set (Array N) := clockFibre (N := N) p m r n with hSdef
  have hS : MeasurableSet[Enl.enlFilt p m n] S := measurableSet_clockFibre p m r n
  have hmA : MeasurableSet (martJumpAt (N := N) p m n W θ i) := measurableSet_martJumpAt p m n W θ i
  by_cases hzero : (arrayMeasure N) S = 0
  · have hle : (arrayMeasure N) (S ∩ martJumpAt (N := N) p m n W θ i) ≤ (arrayMeasure N) S :=
      measure_mono (Set.inter_subset_left)
    rw [hzero, zero_mul]
    exact le_trans hle (le_of_eq hzero)
  · set c : ℝ≥0∞ := ((arrayMeasure N) S)⁻¹ with hcdef
    have hc : c ≠ ⊤ := ENNReal.inv_ne_top.2 hzero
    set ν : Measure (Array N) := c • (arrayMeasure N).restrict S with hνdef
    have hνprob : ν Set.univ = 1 := by
      rw [hνdef, Measure.smul_apply, smul_eq_mul,
        Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, hcdef,
        ENNReal.inv_mul_cancel hzero (measure_ne_top _ _)]
    haveI : IsProbabilityMeasure ν := ⟨hνprob⟩
    have hmean : ∀ k : ℕ, ν[(fun U : Array N => ExcOcc.martIncr p m (n + k) i U) |
        Enl.enlFilt p m (n + k)] =ᵐ[ν] 0 :=
      fun k => condExp_martIncr_smul_restrict (N := N) hp0 hp1 hS k i hc
    have hAz := driftMartingale_tail_of_prob (N := N) (μ := ν) hp0 hp1 m n W hW i hθ hθW hmean
    have hνA : ν (martJumpAt (N := N) p m n W θ i)
        ≤ ENNReal.ofReal (2 * Real.exp (-(θ ^ 2) / (16 * (W : ℝ)))) := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top ν _)]
      exact ENNReal.ofReal_le_ofReal hAz
    have htransfer : (arrayMeasure N) (S ∩ martJumpAt (N := N) p m n W θ i)
        = (arrayMeasure N) S * ν (martJumpAt (N := N) p m n W θ i) := by
      have h1 : ν (martJumpAt (N := N) p m n W θ i)
          = ((arrayMeasure N) S)⁻¹ *
              (arrayMeasure N) (martJumpAt (N := N) p m n W θ i ∩ S) := by
        rw [hνdef, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hmA]
      rw [h1, Set.inter_comm (martJumpAt (N := N) p m n W θ i) S, ← mul_assoc,
        ENNReal.mul_inv_cancel hzero (measure_ne_top _ _), one_mul]
    rw [htransfer]
    gcongr

/-- **The fibre-conditional Azuma bound for the whole swarm** (finite union over walkers). -/
theorem clockFibre_martJump_measure_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m r n W : ℕ) (hW : 1 ≤ W) {θ : ℝ} (hθ : 0 < θ) (hθW : θ ≤ 4 * W) :
    (arrayMeasure N) (clockFibre (N := N) p m r n ∩
        ⋃ i : Fin N, martJumpAt (N := N) p m n W θ i)
      ≤ (N : ℝ≥0∞) * ((arrayMeasure N) (clockFibre (N := N) p m r n) *
          ENNReal.ofReal (2 * Real.exp (-(θ ^ 2) / (16 * (W : ℝ))))) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hsub : clockFibre (N := N) p m r n ∩ ⋃ i : Fin N, martJumpAt (N := N) p m n W θ i
      = ⋃ i : Fin N, (clockFibre (N := N) p m r n ∩ martJumpAt (N := N) p m n W θ i) := by
    rw [Set.inter_iUnion]
  rw [hsub, show (⋃ i : Fin N,
        (clockFibre (N := N) p m r n ∩ martJumpAt (N := N) p m n W θ i))
      = ⋃ i ∈ (Finset.univ : Finset (Fin N)),
        (clockFibre (N := N) p m r n ∩ martJumpAt (N := N) p m n W θ i) from by simp]
  calc (arrayMeasure N) (⋃ i ∈ (Finset.univ : Finset (Fin N)),
        (clockFibre (N := N) p m r n ∩ martJumpAt (N := N) p m n W θ i))
      ≤ ∑ i ∈ (Finset.univ : Finset (Fin N)), (arrayMeasure N)
          (clockFibre (N := N) p m r n ∩ martJumpAt (N := N) p m n W θ i) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin N)), (arrayMeasure N) (clockFibre (N := N) p m r n) *
          ENNReal.ofReal (2 * Real.exp (-(θ ^ 2) / (16 * (W : ℝ)))) :=
        Finset.sum_le_sum (fun i _ =>
          clockFibre_martJumpAt_measure_le hp0 hp1 m r n W hW i hθ hθW)
    _ = (N : ℝ≥0∞) * ((arrayMeasure N) (clockFibre (N := N) p m r n) *
          ENNReal.ofReal (2 * Real.exp (-(θ ^ 2) / (16 * (W : ℝ))))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `↑N · ofReal b = ofReal (N b)`. -/
theorem natCast_mul_ofReal (n : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    (n : ℝ≥0∞) * ENNReal.ofReal b = ENNReal.ofReal ((n : ℝ) * b) := by
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]

/-! ## 4. Removing the record-time truncation -/

/-- **The martingale-jump event is covered by the clock fibres.**  On `ReachAll` the canonical
record clock is a genuine first-hitting time, so the array sits in the fibre of its own time; off
`ReachAll` there is nothing to cover because that event is null. -/
theorem martJumpSet_subset (p : ℝ) (m r W : ℕ) (θ : ℝ) :
    ExcOcc.martJumpSet (N := N) p m r W θ ⊆
      (ReachAll p m)ᶜ ∪ ⋃ n : ℕ, (clockFibre (N := N) p m r n ∩
        ⋃ i : Fin N, martJumpAt (N := N) p m n W θ i) := by
  intro U hU
  by_cases hR : U ∈ ReachAll p m
  · obtain ⟨i, hi⟩ := hU
    have hfib : U ∈ clockFibre (N := N) p m r (recTimeA p m U r) := by
      refine ⟨(recTimeA_spec p m U r).resolve_left (fun h => h hR), ?_⟩
      intro j hj hval
      exact recTimeA_min p m U r j hj (Or.inr hval)
    exact Or.inr (Set.mem_iUnion.2 ⟨recTimeA p m U r, hfib, Set.mem_iUnion.2 ⟨i, hi⟩⟩)
  · exact Or.inl hR

/-- **The martingale-jump tail at the actual record clock, with no truncation.**  For every
record level `r`, window length `W ≥ 1` and `0 < θ ≤ 4W`:

    μ.real (martJumpSet θ) ≤ N · 2 exp (-θ² / (16 W)),

with no factor depending on the record time.  The almost-sure record statement enters only
through `ReachAllᶜ` being null. -/
theorem martJumpSet_measure_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) (r W : ℕ) (hW : 1 ≤ W) {θ : ℝ} (hθ : 0 < θ)
    (hθW : θ ≤ 4 * W) :
    (arrayMeasure N).real (ExcOcc.martJumpSet (N := N) p m r W θ)
      ≤ (N : ℝ) * (2 * Real.exp (-(θ ^ 2) / (16 * (W : ℝ)))) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hb0 : (0 : ℝ) ≤ 2 * Real.exp (-(θ ^ 2) / (16 * (W : ℝ))) := by positivity
  have hnull : (arrayMeasure N) (ReachAll p m)ᶜ = 0 := by
    have h : (arrayMeasure N) {U : Array N | ¬ U ∈ ReachAll p m} = 0 := by
      rw [← ae_iff]
      exact ae_mem_reachAll (N := N) hp0 hp1 hm hN
    convert h using 2
    ext U
    simp
  -- the fibres are null-measurable and pairwise disjoint
  have hfib_meas : ∀ n : ℕ, NullMeasurableSet (clockFibre (N := N) p m r n) (arrayMeasure N) :=
    fun n => (measurableSet_clockFibre p m r n |> fun h => (Enl.enlFilt p m).le n _ h).nullMeasurableSet
  have hfib_disj : Pairwise (fun i j =>
      AEDisjoint (arrayMeasure N) (clockFibre (N := N) p m r i) (clockFibre (N := N) p m r j)) :=
    fun i j hij => (disjoint_clockFibre (N := N) p m r i j hij).aedisjoint
  have hsum_le : ∑' n : ℕ, (arrayMeasure N) (clockFibre (N := N) p m r n) ≤ 1 := by
    have h := tsum_measure_le_measure_univ hfib_meas hfib_disj
    rwa [measure_univ] at h
  have hENN : (arrayMeasure N) (ExcOcc.martJumpSet (N := N) p m r W θ)
      ≤ ENNReal.ofReal ((N : ℝ) * (2 * Real.exp (-(θ ^ 2) / (16 * (W : ℝ))))) := by
    calc (arrayMeasure N) (ExcOcc.martJumpSet (N := N) p m r W θ)
        ≤ (arrayMeasure N) ((ReachAll p m)ᶜ ∪ ⋃ n : ℕ, (clockFibre (N := N) p m r n ∩
            ⋃ i : Fin N, martJumpAt (N := N) p m n W θ i)) :=
          measure_mono (martJumpSet_subset p m r W θ)
      _ ≤ (arrayMeasure N) (ReachAll p m)ᶜ + (arrayMeasure N)
            (⋃ n : ℕ, (clockFibre (N := N) p m r n ∩
              ⋃ i : Fin N, martJumpAt (N := N) p m n W θ i)) := measure_union_le _ _
      _ = (arrayMeasure N) (⋃ n : ℕ, (clockFibre (N := N) p m r n ∩
              ⋃ i : Fin N, martJumpAt (N := N) p m n W θ i)) := by rw [hnull, zero_add]
      _ ≤ ∑' n : ℕ, (arrayMeasure N) (clockFibre (N := N) p m r n ∩
              ⋃ i : Fin N, martJumpAt (N := N) p m n W θ i) := measure_iUnion_le _
      _ ≤ ∑' n : ℕ, (N : ℝ≥0∞) * ((arrayMeasure N) (clockFibre (N := N) p m r n) *
              ENNReal.ofReal (2 * Real.exp (-(θ ^ 2) / (16 * (W : ℝ))))) :=
          ENNReal.tsum_le_tsum (fun n =>
            clockFibre_martJump_measure_le hp0 hp1 m r n W hW hθ hθW)
      _ = (N : ℝ≥0∞) * ENNReal.ofReal (2 * Real.exp (-(θ ^ 2) / (16 * (W : ℝ)))) *
              ∑' n : ℕ, (arrayMeasure N) (clockFibre (N := N) p m r n) := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
          ring
      _ ≤ (N : ℝ≥0∞) * ENNReal.ofReal (2 * Real.exp (-(θ ^ 2) / (16 * (W : ℝ)))) * 1 := by
          gcongr
      _ = ENNReal.ofReal ((N : ℝ) * (2 * Real.exp (-(θ ^ 2) / (16 * (W : ℝ))))) := by
          rw [mul_one, natCast_mul_ofReal N hb0]
  calc (arrayMeasure N).real (ExcOcc.martJumpSet (N := N) p m r W θ)
      = ((arrayMeasure N) (ExcOcc.martJumpSet (N := N) p m r W θ)).toReal := rfl
    _ ≤ (ENNReal.ofReal ((N : ℝ) * (2 * Real.exp (-(θ ^ 2) / (16 * (W : ℝ)))))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hENN
    _ = (N : ℝ) * (2 * Real.exp (-(θ ^ 2) / (16 * (W : ℝ)))) :=
        ENNReal.toReal_ofReal (by positivity)

/-! ## 5. The stall and record-advance tails with no record-time hypothesis -/

/-- **The stall reduction as a set statement** (the union of the two alternatives). -/
theorem stallSet_subset {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) {m B T r L : ℕ}
    (hmN : 2 * m ≤ N) (hNpos : 0 < N) :
    ExcOcc.stallSet (N := N) p m B T r L ⊆
      ExcOcc.defectSet (N := N) p m r (ExcOcc.cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ))) ∪
        ExcOcc.martJumpSet (N := N) p m r (T * L)
          (ExcOcc.cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ))) := by
  intro U hU
  by_cases h : U ∈ ExcOcc.defectSet (N := N) p m r
      (ExcOcc.cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ)))
  · exact Or.inl h
  · exact Or.inr (ExcOcc.stall_subset_defect_union_mart (N := N) hp0 hmN hNpos hU h)

/-- **The full swarm-stall tail.**  The swarm-stall mass at the record fibre of level `r` is at
most the defect mass at the fibre plus the *untruncated* martingale-jump bound.  There is no
record-time tail and no `K`, hence no implicit assumption on `recTimeA`. -/
theorem stall_measure_le_full {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m B T r L : ℕ}
    (hm2 : 2 ≤ m) (hmN : 2 * m ≤ N) (hN2 : 2 ≤ N) (hNpos : 0 < N) (hW : 1 ≤ T * L)
    (hθ : 0 < ExcOcc.cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ)))
    (hθW : ExcOcc.cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ)) ≤ 4 * ((T * L : ℕ) : ℝ)) :
    (arrayMeasure N).real (ExcOcc.stallSet (N := N) p m B T r L)
      ≤ (arrayMeasure N).real (ExcOcc.defectSet (N := N) p m r
            (ExcOcc.cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ))))
        + (N : ℝ) * (2 * Real.exp (-((ExcOcc.cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ))) ^ 2)
              / (16 * ((T * L : ℕ) : ℝ)))) := by
  calc (arrayMeasure N).real (ExcOcc.stallSet (N := N) p m B T r L)
      ≤ (arrayMeasure N).real (ExcOcc.defectSet (N := N) p m r
            (ExcOcc.cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ))) ∪
          ExcOcc.martJumpSet (N := N) p m r (T * L)
            (ExcOcc.cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ)))) :=
        measureReal_mono (stallSet_subset (N := N) hp0 hmN hNpos) (by simp)
    _ ≤ (arrayMeasure N).real (ExcOcc.defectSet (N := N) p m r
            (ExcOcc.cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ))))
          + (arrayMeasure N).real (ExcOcc.martJumpSet (N := N) p m r (T * L)
            (ExcOcc.cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ)))) :=
        measureReal_union_le _ _
    _ ≤ (arrayMeasure N).real (ExcOcc.defectSet (N := N) p m r
            (ExcOcc.cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ))))
          + (N : ℝ) * (2 * Real.exp (-((ExcOcc.cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ))) ^ 2)
              / (16 * ((T * L : ℕ) : ℝ)))) := by
        gcongr
        exact martJumpSet_measure_le hp0 hp1 hm2 hN2 r (T * L) hW hθ hθW

/-- The literal record-advance exception `τ_r + T*L < τ_{r+B*L}`.  This is the same term as
`QuantitativeRestrictedBand.timeLag`; that module's build artefacts are not required here. -/
def recordAdvance (p : ℝ) (m B T r L : ℕ) : Set (Array N) :=
  {U | recTimeA p m U r + T * L < recTimeA p m U (r + B * L)}

/-- The record-advance exception is a swarm stall (`ExcOcc.timeLag_subset_stallSet`). -/
theorem recordAdvance_subset_stall (p : ℝ) (m B T r L : ℕ) :
    recordAdvance (N := N) p m B T r L ⊆ ExcOcc.stallSet (N := N) p m B T r L :=
  ExcOcc.timeLag_subset_stallSet p m B T r L

/-- **The record-advance tail with no record-time hypothesis.** -/
theorem recordAdvance_measure_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m B T r L : ℕ}
    (hm2 : 2 ≤ m) (hmN : 2 * m ≤ N) (hN2 : 2 ≤ N) (hNpos : 0 < N) (hW : 1 ≤ T * L)
    (hθ : 0 < ExcOcc.cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ)))
    (hθW : ExcOcc.cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ)) ≤ 4 * ((T * L : ℕ) : ℝ)) :
    (arrayMeasure N).real (recordAdvance (N := N) p m B T r L)
      ≤ (arrayMeasure N).real (ExcOcc.defectSet (N := N) p m r
            (ExcOcc.cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ))))
        + (N : ℝ) * (2 * Real.exp (-((ExcOcc.cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ))) ^ 2)
              / (16 * ((T * L : ℕ) : ℝ)))) :=
  le_trans (measureReal_mono (recordAdvance_subset_stall p m B T r L) (by simp))
    (stall_measure_le_full hp0 hp1 hm2 hmN hN2 hNpos hW hθ hθW)

/-- The paper's absolute defect tail at threshold `L/8` (`QuantitativeRestrictedBand.defectHigh`,
same term). -/
def defectHigh (p : ℝ) (m s L : ℕ) : Set (Array N) :=
  {U | (L : ℝ) / 8 ≤ (defect (RecordoSupply.actX p m U) (recTimeA p m U) s : ℝ)}

/-- A defect tail at the threshold `θ` implies the paper's `L/8` tail as soon as `L/8 ≤ θ`. -/
theorem defectSet_subset_defectHigh {p : ℝ} {m r L : ℕ} {θ : ℝ} (h : (L : ℝ) / 8 ≤ θ) :
    ExcOcc.defectSet (N := N) p m r θ ⊆ defectHigh (N := N) p m r L :=
  fun _ hU => le_trans h hU

/-- **The record-advance tail at the paper's defect scale.**  If the drift coefficient dominates
`N/4`, the defect term of the stall reduction may be taken at the paper's own `L/8` threshold,
so the only defect input is `defectHigh r L`. -/
theorem recordAdvance_measure_le_defectHigh {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m B T r L : ℕ} (hm2 : 2 ≤ m) (hmN : 2 * m ≤ N) (hN2 : 2 ≤ N) (hNpos : 0 < N)
    (hW : 1 ≤ T * L) (hθ : 0 < ExcOcc.cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ)))
    (hθW : ExcOcc.cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ)) ≤ 4 * ((T * L : ℕ) : ℝ))
    (h8 : (L : ℝ) / 8 ≤ ExcOcc.cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ))) :
    (arrayMeasure N).real (recordAdvance (N := N) p m B T r L)
      ≤ (arrayMeasure N).real (defectHigh (N := N) p m r L)
        + (N : ℝ) * (2 * Real.exp (-((ExcOcc.cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ))) ^ 2)
              / (16 * ((T * L : ℕ) : ℝ)))) := by
  refine le_trans (recordAdvance_measure_le hp0 hp1 hm2 hmN hN2 hNpos hW hθ hθW) ?_
  have : (arrayMeasure N).real (ExcOcc.defectSet (N := N) p m r
        (ExcOcc.cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ))))
      ≤ (arrayMeasure N).real (defectHigh (N := N) p m r L) :=
    measureReal_mono (defectSet_subset_defectHigh (N := N) h8) (by simp)
  linarith

/-! ## 6. The numerical hypotheses are satisfiable -/

/-- The drift coefficient is at most `8 N T`, hence the Azuma side condition `θ ≤ 4 W` is
automatic. -/
theorem cCoef_le_eight {p : ℝ} (hp : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m B T : ℕ)
    (hmN : 2 * m ≤ N) :
    ExcOcc.cCoef N p m B T ≤ 8 * (N : ℝ) * (T : ℝ) := by
  have h2p0 : (0 : ℝ) ≤ 2 * p - 1 := by linarith
  have h2p1 : 2 * p - 1 ≤ 1 := by linarith
  have hNle : ((N : ℝ) - 2 * (m : ℝ)) ≤ (N : ℝ) := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hT0 : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
  have hsub : (0 : ℝ) ≤ (N : ℝ) - 2 * (m : ℝ) := by
    have h2m : (2 * m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hmN
    linarith
  have h1 : (2 * p - 1) * ((N : ℝ) - 2 * (m : ℝ)) * (T : ℝ) ≤ 1 * (N : ℝ) * (T : ℝ) := by
    refine mul_le_mul (mul_le_mul h2p1 hNle hsub (by norm_num)) le_rfl hT0 (by positivity)
  have h2 : (0 : ℝ) ≤ (N : ℝ) * (B : ℝ) := by positivity
  rw [ExcOcc.cCoef]
  nlinarith

/-- The Azuma side condition `θ ≤ 4 (T L)` holds automatically. -/
theorem theta_le_four {p : ℝ} (hp : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m B T L : ℕ)
    (hmN : 2 * m ≤ N) (hNpos : 0 < N) :
    ExcOcc.cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ)) ≤ 4 * ((T * L : ℕ) : ℝ) := by
  have hc := cCoef_le_eight (N := N) hp hp1 m B T hmN
  have hN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hL : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hTL : ((T * L : ℕ) : ℝ) = (T : ℝ) * (L : ℝ) := by push_cast; ring
  rw [hTL]
  have h1 : ExcOcc.cCoef N p m B T * (L : ℝ)
      ≤ (8 * (N : ℝ) * (T : ℝ)) * (L : ℝ) :=
    mul_le_mul_of_nonneg_right hc hL
  have h2 : ExcOcc.cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ))
      ≤ (8 * (N : ℝ) * (T : ℝ)) * (L : ℝ) / (2 * (N : ℝ)) :=
    div_le_div_of_nonneg_right h1 (by positivity)
  have h3 : (8 * (N : ℝ) * (T : ℝ)) * (L : ℝ) / (2 * (N : ℝ))
      = 4 * ((T : ℝ) * (L : ℝ)) := by
    field_simp
    ring
  linarith

/-- **Any prescribed drift threshold is attainable exactly in the regime `N > 2m`.**  For
`2m < N`, `1/2 < p` and any `A ≥ 0` there is `T ≥ 1` with `A < c = (2p-1)(N-2m)T - NB`. -/
theorem exists_T_gt {p : ℝ} (hp : (1 : ℝ) / 2 < p) {m B : ℕ} (h2m : 2 * m < N)
    {A : ℝ} (hA : 0 ≤ A) :
    ∃ T : ℕ, 1 ≤ T ∧ A < ExcOcc.cCoef N p m B T := by
  have hN : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hgap : (0 : ℝ) < ((N : ℝ) - 2 * (m : ℝ)) := by
    have : (2 * m : ℝ) < (N : ℝ) := by exact_mod_cast h2m
    linarith
  have hpos : (0 : ℝ) < (2 * p - 1) * ((N : ℝ) - 2 * (m : ℝ)) := by
    have : (0 : ℝ) < 2 * p - 1 := by linarith
    positivity
  obtain ⟨T, hT⟩ := exists_nat_gt (max 1 ((A + (N : ℝ) * (B : ℝ))
    / ((2 * p - 1) * ((N : ℝ) - 2 * (m : ℝ))) + 1))
  refine ⟨T, ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ (T : ℝ) := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hT)
    exact_mod_cast h1
  · have hT0 : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
    have hle : (A + (N : ℝ) * (B : ℝ))
          / ((2 * p - 1) * ((N : ℝ) - 2 * (m : ℝ))) + 1
        ≤ max 1 ((A + (N : ℝ) * (B : ℝ))
            / ((2 * p - 1) * ((N : ℝ) - 2 * (m : ℝ))) + 1) := le_max_right _ _
    have h2 : A + (N : ℝ) * (B : ℝ)
        < (2 * p - 1) * ((N : ℝ) - 2 * (m : ℝ)) * (T : ℝ) := by
      have h3 : (A + (N : ℝ) * (B : ℝ))
          / ((2 * p - 1) * ((N : ℝ) - 2 * (m : ℝ))) < (T : ℝ) := by linarith
      rw [div_lt_iff₀ hpos] at h3
      linarith
    rw [ExcOcc.cCoef]
    have hcomm : ((N : ℝ) - 2 * (m : ℝ)) * (T : ℝ) = (T : ℝ) * ((N : ℝ) - 2 * (m : ℝ)) := by
      ring
    nlinarith

/-- **Positive drift is available exactly in the regime `N > 2m`.** -/
theorem exists_T_pos {p : ℝ} (hp : (1 : ℝ) / 2 < p) {m B : ℕ} (h2m : 2 * m < N) :
    ∃ T : ℕ, 1 ≤ T ∧ 0 < ExcOcc.cCoef N p m B T :=
  exists_T_gt (N := N) hp h2m le_rfl

/-- **The `L/8`-scale hypothesis `c ≥ N/4` is attainable**: for `2m < N` there is `T ≥ 1`
with `N/4 ≤ c`, so that `recordAdvance_uniform_defectHigh` applies at every scale `L`. -/
theorem exists_T_quarter {p : ℝ} (hp : (1 : ℝ) / 2 < p) {m B : ℕ} (h2m : 2 * m < N) :
    ∃ T : ℕ, 1 ≤ T ∧ (N : ℝ) / 4 ≤ ExcOcc.cCoef N p m B T := by
  obtain ⟨T, hT, hlt⟩ := exists_T_gt (N := N) hp h2m (B := B) (A := (N : ℝ) / 4)
    (by positivity)
  exact ⟨T, hT, le_of_lt hlt⟩

/-! ## 7. Capstone forms with the numerical side conditions discharged -/

/-- **The record-advance tail with every side condition derived from the parameters.**  For
`2 ≤ m ≤ N/2`, `N ≥ 2`, `1 ≤ T`, `1 ≤ L` and a *positive* drift coefficient `c = cCoef`,
the record-advance exception at the actual record clock is bounded by the defect tail at the
fibre plus `N · 2 exp(-c² L / (64 T N²))`.  No record-time tail, no truncation, no optional
stopping. -/
theorem recordAdvance_measure_le_exp {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m B T r L : ℕ} (hm2 : 2 ≤ m) (hmN : 2 * m ≤ N) (hN2 : 2 ≤ N) (hNpos : 0 < N)
    (hT : 1 ≤ T) (hL : 1 ≤ L) (hc : 0 < ExcOcc.cCoef N p m B T) :
    (arrayMeasure N).real (recordAdvance (N := N) p m B T r L)
      ≤ (arrayMeasure N).real (ExcOcc.defectSet (N := N) p m r
            (ExcOcc.cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ))))
        + (N : ℝ) * (2 * Real.exp (-((ExcOcc.cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ))) ^ 2)
              / (16 * ((T * L : ℕ) : ℝ)))) := by
  have hN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hL0 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hW : 1 ≤ T * L := Nat.one_le_iff_ne_zero.2 (by positivity)
  refine recordAdvance_measure_le hp0 hp1 hm2 hmN hN2 hNpos hW ?_
    (theta_le_four (N := N) hp0 hp1 m B T L hmN hNpos)
  exact div_pos (mul_pos hc hL0) (by positivity)

/-- **The same bound, uniformly in the starting level `r`.**  Given a defect tail at the
fibre that is uniform in `r` (value `q`), the record-advance tail is at most
`q + N · 2 exp(-c² L / (64 T N²))`, and the exponential term does not depend on `r`.  This is
exactly the `h₃` input of the frontier ledger `advanceClauseAt_of_three_tails`, with an
explicit profile. -/
theorem recordAdvance_uniform {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m B T L : ℕ} (hm2 : 2 ≤ m) (hmN : 2 * m ≤ N) (hN2 : 2 ≤ N) (hNpos : 0 < N)
    (hT : 1 ≤ T) (hL : 1 ≤ L) (hc : 0 < ExcOcc.cCoef N p m B T) (q : ℝ)
    (hq : ∀ r : ℕ, (arrayMeasure N).real (ExcOcc.defectSet (N := N) p m r
      (ExcOcc.cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ)))) ≤ q) :
    ∀ r : ℕ, (arrayMeasure N).real (recordAdvance (N := N) p m B T r L)
      ≤ q + (N : ℝ) * (2 * Real.exp (-((ExcOcc.cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ))) ^ 2)
            / (16 * ((T * L : ℕ) : ℝ)))) :=
  fun r => le_trans (recordAdvance_measure_le_exp (N := N) hp0 hp1 hm2 hmN hN2 hNpos hT hL hc)
    (add_le_add (hq r) le_rfl)

/-- **The `L/8`-scale form, uniformly in `r`**: if the drift coefficient dominates `N/4`, the
defect term of the record-advance tail may be taken at the paper's own threshold `L/8`. -/
theorem recordAdvance_uniform_defectHigh {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m B T L : ℕ} (hm2 : 2 ≤ m) (hmN : 2 * m ≤ N) (hN2 : 2 ≤ N) (hNpos : 0 < N)
    (hT : 1 ≤ T) (hL : 1 ≤ L) (hc : 0 < ExcOcc.cCoef N p m B T) (q : ℝ)
    (hq : ∀ r : ℕ, (arrayMeasure N).real (defectHigh (N := N) p m r L) ≤ q)
    (h4 : (N : ℝ) / 4 ≤ ExcOcc.cCoef N p m B T) :
    ∀ r : ℕ, (arrayMeasure N).real (recordAdvance (N := N) p m B T r L)
      ≤ q + (N : ℝ) * (2 * Real.exp (-((ExcOcc.cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ))) ^ 2)
            / (16 * ((T * L : ℕ) : ℝ)))) := by
  have hN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have h8 : (L : ℝ) / 8 ≤ ExcOcc.cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ)) := by
    rw [show (L : ℝ) / 8 = ((N : ℝ) / 4) * (L : ℝ) / (2 * (N : ℝ)) by field_simp; ring]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h4 hL0) (by positivity)
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hW : 1 ≤ T * L := Nat.one_le_iff_ne_zero.2 (by positivity)
  intro r
  refine le_trans (recordAdvance_measure_le_defectHigh (N := N) hp0 hp1 hm2 hmN hN2 hNpos hW
    (div_pos (mul_pos hc hLpos) (by positivity))
    (theta_le_four (N := N) hp0 hp1 m B T L hmN hNpos) h8) ?_
  exact add_le_add (hq r) le_rfl

/-- **The record-advance tail in the exact shape of the frontier's `h₃` input.**  The profile
`q₃ ℓ = q ℓ + ofReal (N · 2 exp (-(c ℓ/(2N))² / (16 T ℓ)))` bounds the ENNReal measure of the
record-advance exception at scale `ℓ`, *uniformly in the starting level* `r` (indeed for every
`r`, not only `r ≥ C₀ ℓ`), and its second summand has no dependence on `r`.  Hypothesis `hq` is
a defect tail at the fibre, the only remaining array-side input. -/
theorem recordAdvance_profile {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m B T : ℕ} (hm2 : 2 ≤ m) (hmN : 2 * m ≤ N) (hN2 : 2 ≤ N) (hNpos : 0 < N)
    (hT : 1 ≤ T) (hc : 0 < ExcOcc.cCoef N p m B T) (q : ℕ → ℝ≥0∞)
    (hq : ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ r : ℕ, (arrayMeasure N) (ExcOcc.defectSet (N := N) p m r
      (ExcOcc.cCoef N p m B T * (ℓ : ℝ) / (2 * (N : ℝ)))) ≤ q ℓ) :
    ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ r : ℕ,
      (arrayMeasure N) (recordAdvance (N := N) p m B T r ℓ) ≤
        q ℓ + ENNReal.ofReal ((N : ℝ) * (2 * Real.exp
          (-((ExcOcc.cCoef N p m B T * (ℓ : ℝ) / (2 * (N : ℝ))) ^ 2)
            / (16 * ((T * ℓ : ℕ) : ℝ))))) := by
  intro ℓ hℓ r
  set b : ℝ := (N : ℝ) * (2 * Real.exp
    (-((ExcOcc.cCoef N p m B T * (ℓ : ℝ) / (2 * (N : ℝ))) ^ 2)
      / (16 * ((T * ℓ : ℕ) : ℝ)))) with hbdef
  have hb0 : (0 : ℝ) ≤ b := by rw [hbdef]; positivity
  have hsplit := recordAdvance_measure_le_exp (N := N) hp0 hp1 hm2 hmN hN2 hNpos hT hℓ hc
    (r := r)
  by_cases hqtop : q ℓ = ⊤
  · rw [hqtop, top_add]
    exact le_top
  · have hdef : (arrayMeasure N).real (ExcOcc.defectSet (N := N) p m r
        (ExcOcc.cCoef N p m B T * (ℓ : ℝ) / (2 * (N : ℝ)))) ≤ (q ℓ).toReal := by
      calc (arrayMeasure N).real (ExcOcc.defectSet (N := N) p m r
            (ExcOcc.cCoef N p m B T * (ℓ : ℝ) / (2 * (N : ℝ))))
          = ((arrayMeasure N) (ExcOcc.defectSet (N := N) p m r
              (ExcOcc.cCoef N p m B T * (ℓ : ℝ) / (2 * (N : ℝ))))).toReal := rfl
        _ ≤ (q ℓ).toReal := ENNReal.toReal_mono hqtop (hq ℓ hℓ r)
    have hreal : (arrayMeasure N).real (recordAdvance (N := N) p m B T r ℓ)
        ≤ (q ℓ).toReal + b := by
      rw [hbdef]
      linarith
    have hstep : (arrayMeasure N) (recordAdvance (N := N) p m B T r ℓ)
        ≤ ENNReal.ofReal ((q ℓ).toReal + b) := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top (arrayMeasure N) _)]
      exact ENNReal.ofReal_le_ofReal hreal
    calc (arrayMeasure N) (recordAdvance (N := N) p m B T r ℓ)
        ≤ ENNReal.ofReal ((q ℓ).toReal + b) := hstep
      _ = ENNReal.ofReal (q ℓ).toReal + ENNReal.ofReal b :=
          ENNReal.ofReal_add (by positivity) hb0
      _ = q ℓ + ENNReal.ofReal b := by rw [ENNReal.ofReal_toReal hqtop]

end ClockFibre
