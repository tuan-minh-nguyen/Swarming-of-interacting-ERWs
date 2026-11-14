/-  `pairK a {b | CompatPair a b} = if a ∈ CompatSet then 1 else 0`.

This file draws the consequences that `InfSeg` states but does not prove — all-index almost sure
compatibility of the trajectory, and the resulting *actual* chain law of `ChainAssemble`:

* `pairK_compatSet` : the mass-one half of `pairK_compat` in the applicability form needed here
  (`CompatSet` carries full `pairK a` mass for **every** `a`, because `asegK`'s segment always ends
  one level above its endpoint record state).
* `measure_compatSet_coord` : for **every** `n`, the `n`-th enriched step lies in `CompatSet`
  with probability one under `infLaw`.  Base `n = 0` is the exact initial law
  (`map_eval_zero` + `pairLaw_compatSet`); the step uses the cylinder identity `cyl_measure`
  disintegrated over the prefix history (`n` coordinates) and the current state, with the
  state-dependence carried by `pairK_compatSet` — *not* by any "true for every `a`" shortcut.
* `ae_compatPair` : for **every** `n`, the coordinate event
  `{x | CompatPair (x n) (x (n+1))}` has `infLaw`-measure one; the probability-zero branch of
  `pairK_compat` is used only through the a.e. `CompatSet` statement above.
* `trajCompat_ae` : `TrajCompat` holds `infLaw`-almost surely, by feeding those countably many
  coordinate events into `ChainAssemble.ae_trajCompat_of_step`.
* `chainLaw_apply_A_eq_segMass` / `chainLaw_apply_A_eq_pathMass` : the assembled chain law
  `chainLaw (infLaw …)` is a genuine probability law on `SwarmConcat.Chain N`, and its
  regeneration mass is the ambient segment-coordinate mass (resp. the strict-positivity path
  mass).  This is the *unconditional* half of the bridge; stationarity needs `Invariant π` for
  the true record kernel and lives in `InfSegStat.lean`.

Scope ledger (see `SCOPE.md` for the full ledger): this file proves compatibility, not
stationarity, not `hstruct`, not positivity of `π(srSet)`, and it creates no `π`: `π` is an
arbitrary probability measure on `RecState N m` throughout.
-/
import Swarm.InfSeg
import Swarm.ChainAssemble

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal
open SimJump

namespace SwarmInfSeg

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

variable {N m : ℕ}

/-! ## 1. The mass-one half of the one-state computation -/

/-- **Every enriched step is consistent with its own endpoint, at every state.**  This is the
`CompatSet` part of `DHStruct.ae_compat_step` read through `pairK`, whose value at `a` is by
definition `asegK a.2`. -/
theorem pairK_compatSet (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (a : Pair N m) :
    (SwarmSegKernel.pairK (N := N) (m := m) p hm a) (SwarmDHStruct.CompatSet N m) = 1 := by
  rw [SwarmSegKernel.pairK_apply]
  exact SwarmDHStruct.ae_compat_step p hm hp hp1 a.2

/-! ## 2. Every coordinate lies in `CompatSet` almost surely -/

/-- **The `n`-th enriched step is consistent almost surely**, for every index `n`.

`n = 0`: the exact initial law `map_eval_zero` reduces this to `pairLaw_compatSet`.
`n + 1`: the cylinder identity `cyl_measure` writes the event as the `pairK`-mass of `CompatSet`
integrated over the law of the prefix history *and* the state at time `n`; that mass is `1` at
every state, so the integral is the total mass of the prefix law. -/
theorem measure_compatSet_coord (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π] (n : ℕ) :
    (infLaw (N := N) (m := m) p hm hp hp1 π)
      {x : ℕ → Pair N m | x n ∈ SwarmDHStruct.CompatSet N m} = 1 := by
  haveI hK : IsMarkovKernel (SwarmSegKernel.pairK (N := N) (m := m) p hm) :=
    SwarmSegKernel.isMarkovKernel_pairK (N := N) (m := m) p hm hp hp1
  haveI hπ : IsProbabilityMeasure (SwarmSegKernel.pairLaw (N := N) (m := m) p hm π) :=
    isProbabilityMeasure_pairLaw p hm hp hp1 π
  haveI hinf : IsProbabilityMeasure (infLaw (N := N) (m := m) p hm hp hp1 π) :=
    isProbabilityMeasure_infLaw p hm hp hp1 π
  induction n with
  | zero =>
      rw [show {x : ℕ → Pair N m | x 0 ∈ SwarmDHStruct.CompatSet N m}
            = (fun x : ℕ → Pair N m => x 0) ⁻¹' (SwarmDHStruct.CompatSet N m) from rfl,
        ← Measure.map_apply (measurable_pi_apply (0 : ℕ))
          (SwarmDHStruct.measurableSet_compatSet (N := N) (m := m)),
        map_eval_zero (N := N) (m := m) p hm hp hp1 π]
      exact pairLaw_compatSet p hm hp hp1 π
  | succ n _ =>
      rw [measure_succ_mem (N := N) (m := m) p hm hp hp1 π n
        (SwarmDHStruct.measurableSet_compatSet (N := N) (m := m))]
      have hstep : ∀ v : Π _i : Finset.Iic n, Pair N m,
          (SwarmSegKernel.pairK (N := N) (m := m) p hm
              (v ⟨n, Finset.mem_Iic.2 le_rfl⟩)) (SwarmDHStruct.CompatSet N m) = 1 :=
        fun v => pairK_compatSet p hm hp hp1 _
      simp only [hstep, lintegral_one]
      haveI hprob : IsProbabilityMeasure
          ((infLaw (N := N) (m := m) p hm hp hp1 π).map
            (Preorder.frestrictLe (π := fun _ => Pair N m) n)) :=
        Measure.isProbabilityMeasure_map
          (Preorder.measurable_frestrictLe (X := fun _ => Pair N m) n).aemeasurable
      rw [measure_univ]

/-! ## 3. Consecutive coordinates are compatible almost surely -/

/-- The set of `(prefix history, next enriched step)` pairs whose next step is `CompatPair` with
the state at the end of the prefix. -/
theorem measurableSet_compatPair_cyl (n : ℕ) :
    MeasurableSet {q : (Π _i : Finset.Iic n, Pair N m) × Pair N m |
      CompatPair (q.1 ⟨n, Finset.mem_Iic.2 le_rfl⟩) q.2} := by
  have hf : Measurable (fun q : (Π _i : Finset.Iic n, Pair N m) × Pair N m =>
      (q.1 ⟨n, Finset.mem_Iic.2 le_rfl⟩, q.2)) :=
    ((measurable_pi_apply _).comp measurable_fst).prodMk measurable_snd
  exact hf measurableSet_compatPair

/-- **Consecutive enriched steps are compatible, at every index, almost surely.**

This is *not* a statement that `CompatPair a b` holds for every `a`; `pairK_compat` is used in its
exact form `if a ∈ CompatSet then 1 else 0`, and the off-`CompatSet` branch is killed by
`measure_compatSet_coord`. -/
theorem ae_compatPair (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π] (n : ℕ) :
    (infLaw (N := N) (m := m) p hm hp hp1 π)
      {x : ℕ → Pair N m | CompatPair (x n) (x (n + 1))} = 1 := by
  classical
  haveI hK : IsMarkovKernel (SwarmSegKernel.pairK (N := N) (m := m) p hm) :=
    SwarmSegKernel.isMarkovKernel_pairK (N := N) (m := m) p hm hp hp1
  haveI hπ : IsProbabilityMeasure (SwarmSegKernel.pairLaw (N := N) (m := m) p hm π) :=
    isProbabilityMeasure_pairLaw p hm hp hp1 π
  haveI hinf : IsProbabilityMeasure (infLaw (N := N) (m := m) p hm hp hp1 π) :=
    isProbabilityMeasure_infLaw p hm hp hp1 π
  have hC := measurableSet_compatPair_cyl (N := N) (m := m) (n := n)
  have hpre : (fun x : ℕ → Pair N m =>
        (Preorder.frestrictLe (π := fun _ => Pair N m) n x, x (n + 1))) ⁻¹'
        {q : (Π _i : Finset.Iic n, Pair N m) × Pair N m |
          CompatPair (q.1 ⟨n, Finset.mem_Iic.2 le_rfl⟩) q.2}
      = {x : ℕ → Pair N m | CompatPair (x n) (x (n + 1))} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Preorder.frestrictLe_apply]
  rw [← hpre, cyl_measure (N := N) (m := m) p hm hp hp1 π n hC]
  have hfib : ∀ v : Π _i : Finset.Iic n, Pair N m,
      (Prod.mk v ⁻¹' {q : (Π _i : Finset.Iic n, Pair N m) × Pair N m |
          CompatPair (q.1 ⟨n, Finset.mem_Iic.2 le_rfl⟩) q.2})
        = {b : Pair N m | CompatPair (v ⟨n, Finset.mem_Iic.2 le_rfl⟩) b} := fun v => rfl
  simp only [hfib]
  have hstep : ∀ v : Π _i : Finset.Iic n, Pair N m,
      (SwarmSegKernel.pairK (N := N) (m := m) p hm
          (v ⟨n, Finset.mem_Iic.2 le_rfl⟩))
        {b : Pair N m | CompatPair (v ⟨n, Finset.mem_Iic.2 le_rfl⟩) b}
      = if v ⟨n, Finset.mem_Iic.2 le_rfl⟩ ∈ SwarmDHStruct.CompatSet N m then 1 else 0 :=
    fun v => pairK_compat p hm hp hp1 _
  simp only [hstep]
  have hS : MeasurableSet {v : Π _i : Finset.Iic n, Pair N m |
      v ⟨n, Finset.mem_Iic.2 le_rfl⟩ ∈ SwarmDHStruct.CompatSet N m} :=
    (SwarmDHStruct.measurableSet_compatSet (N := N) (m := m)).preimage (measurable_pi_apply _)
  have hInt : (∫⁻ v, (if v ⟨n, Finset.mem_Iic.2 le_rfl⟩ ∈ SwarmDHStruct.CompatSet N m
        then (1 : ℝ≥0∞) else 0)
      ∂((infLaw (N := N) (m := m) p hm hp hp1 π).map
        (Preorder.frestrictLe (π := fun _ => Pair N m) n)))
      = ((infLaw (N := N) (m := m) p hm hp hp1 π).map
          (Preorder.frestrictLe (π := fun _ => Pair N m) n))
        {v : Π _i : Finset.Iic n, Pair N m |
          v ⟨n, Finset.mem_Iic.2 le_rfl⟩ ∈ SwarmDHStruct.CompatSet N m} := by
    rw [← lintegral_indicator_one (s := {v : Π _i : Finset.Iic n, Pair N m |
      v ⟨n, Finset.mem_Iic.2 le_rfl⟩ ∈ SwarmDHStruct.CompatSet N m}) hS]
    rfl
  rw [hInt]
  have hmap : ((infLaw (N := N) (m := m) p hm hp hp1 π).map
        (Preorder.frestrictLe (π := fun _ => Pair N m) n))
      {v : Π _i : Finset.Iic n, Pair N m |
        v ⟨n, Finset.mem_Iic.2 le_rfl⟩ ∈ SwarmDHStruct.CompatSet N m}
      = (infLaw (N := N) (m := m) p hm hp hp1 π)
        {x : ℕ → Pair N m | x n ∈ SwarmDHStruct.CompatSet N m} := by
    rw [Measure.map_apply (Preorder.measurable_frestrictLe (X := fun _ => Pair N m) n) hS]
    rfl
  rw [hmap]
  exact measure_compatSet_coord p hm hp hp1 π n

/-! ## 4. All-index compatibility and the actual chain law -/

/-- **The canonical enriched trajectory is compatible almost surely.**

`ae_trajCompat_of_step` is applied only after the countably many coordinate events of
`ae_compatPair` are established; nothing is assumed about an individual trajectory. -/
theorem trajCompat_ae (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π] :
    ∀ᵐ A ∂(infLaw (N := N) (m := m) p hm hp hp1 π),
      SwarmChainAssemble.TrajCompat A := by
  haveI hinf : IsProbabilityMeasure (infLaw (N := N) (m := m) p hm hp hp1 π) :=
    isProbabilityMeasure_infLaw p hm hp hp1 π
  refine SwarmChainAssemble.ae_trajCompat_of_step
    (infLaw (N := N) (m := m) p hm hp hp1 π) (fun k => ?_)
  exact ae_compatPair p hm hp hp1 π k

/-- The assembled chain law of the canonical enriched trajectory is a probability measure on
`SwarmConcat.Chain N`: the pushforward of a probability along a measurable map. -/
theorem isProbabilityMeasure_chainLaw_infLaw (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p)
    (hp1 : p ≤ 1) (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π] :
    IsProbabilityMeasure (SwarmChainAssemble.chainLaw
      (infLaw (N := N) (m := m) p hm hp hp1 π)) := by
  haveI hinf : IsProbabilityMeasure (infLaw (N := N) (m := m) p hm hp hp1 π) :=
    isProbabilityMeasure_infLaw p hm hp hp1 π
  infer_instance

/-- **The chain's regeneration mass is the ambient segment-coordinate mass.**  For the canonical
enriched trajectory law, the mass of the paper's event `Chain.A` under the assembled chain law is
exactly the probability that the trajectory's own segments satisfy the level-`0` regeneration
condition `SegRegen0`. -/
theorem chainLaw_infLaw_apply_A_eq_segMass (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π] :
    SwarmChainAssemble.chainLaw (infLaw (N := N) (m := m) p hm hp hp1 π)
        SwarmConcat.Chain.A
      = (infLaw (N := N) (m := m) p hm hp hp1 π)
          {A | SwarmChainAssemble.SegRegen0 (fun k => (A k).1)} := by
  haveI hinf : IsProbabilityMeasure (infLaw (N := N) (m := m) p hm hp hp1 π) :=
    isProbabilityMeasure_infLaw p hm hp hp1 π
  exact SwarmChainAssemble.chainLaw_apply_A_eq_segMass _ (trajCompat_ae p hm hp hp1 π)

/-- **Path form of the same identity.**  The chain's regeneration mass is the `infLaw`-mass of the
set of trajectories whose assembled concatenated path lies in the model's `strictPos` event. -/
theorem chainLaw_infLaw_apply_A_eq_pathMass (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p)
    (hp1 : p ≤ 1) (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π] :
    SwarmChainAssemble.chainLaw (infLaw (N := N) (m := m) p hm hp hp1 π)
        SwarmConcat.Chain.A
      = (infLaw (N := N) (m := m) p hm hp hp1 π)
          {A | (fun n i => (SwarmChainAssemble.chainOf A).X n i) ∈
            SwarmFresh.strictPos (N := N)} :=
  SwarmChainAssemble.chainLaw_apply_A_eq_pathMass _

/-- The assembled chain law is the pushforward of the trajectory law along the assembly map (the
defining identity, recorded here for the canonical law so that the scope of the two mass
identities above is unambiguous). -/
theorem chainLaw_infLaw_def (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π] :
    SwarmChainAssemble.chainLaw (infLaw (N := N) (m := m) p hm hp hp1 π)
      = (infLaw (N := N) (m := m) p hm hp hp1 π).map SwarmChainAssemble.chainOf := rfl

end SwarmInfSeg
