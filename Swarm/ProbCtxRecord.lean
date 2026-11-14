/-
# `ProbCtx` for the actual record chain: the paper's `Good` as a path event

`Tightness.lean` (m5) reduces the tightness input `htight` of
`Swarm/InfKernel.lean` to an abstract `RecordTight.ProbCtx`, whose field `Good` is an
*uninterpreted* relation together with the hypothesis `hS` linking it to the process `d`.

Here the abstract `ProbCtx` is **inhabited by the actual record chain**: on the trajectory space
`ℕ → RecState N m × ℕ` of `RecordChain.lean` we set

  `dT ω r  = max_i d_i(ω r)`   (the paper's `d_r`, `RecordChain.dmax`)
  `τT ω r  = (ω r).2`          (the paper's record time `τ_r`)
  `GoodT ω r L = (τT ω (r+BL) - τT ω r ≤ T L) ∧ (dT ω (r+BL) ≤ L/2) ∧
                  (∀ u ∈ [r, r+BL], dT ω u ≤ C₀ L)`,

the paper's three block inequalities, and we **prove** the fields `hd`, `hdR`, `hg`, `hS`; `hS` is
no longer a hypothesis because `GoodT` is an explicit conjunction.  The remaining fields
`hterm`, `hR`, `hblk` become genuine path probabilities of `recordTrajT`, i.e. the paper's
`(recordo)` and `(blkprob)` for the real process, and `htail`/`hsum` is the elementary summability
of `(4Bℓ+1) p ℓ`.

Consequently `htight` for `hitKKernel` follows from those three path-probability statements.  This
is a **conditional reduction**: it does not assert `exists_invariant_measure_pos_hitKInf`, and it
does not assert `Swarm.Ballistic`, `Swarm.RegenAvailable`, `Swarm.InitialRegen` or
`Swarm.MainClaim`.

No proof holes.  Imports `RecordChain` and m5's `Tightness`.
-/
import Swarm.RecordChain
import Swarm.Tightness

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology
open Classical
open scoped ENNReal BigOperators

namespace SimJump
namespace RecKernel

open SwarmRec

variable {N m : ℕ}

/-! ### Measurability of the record-distance statistic -/

theorem measurable_dist2 (i : Fin N) : Measurable (fun y : RecState N m => dist2 y i) := by
  have h : (fun y : RecState N m => dist2 y i)
      = (fun p : Amb N m => p.1 i) ∘ Subtype.val := rfl
  rw [h]
  exact (measurable_pi_apply i).comp (measurable_fst.comp measurable_subtype_coe)

theorem measurable_dmax : Measurable (dmax (N := N) (m := m)) := by
  have h : ∀ s : Finset (Fin N), Measurable (fun y : RecState N m => s.sup (fun i => dist2 y i)) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
        have hs : (fun y : RecState N m => (insert a s).sup (fun i => dist2 y i))
            = fun y => max (dist2 y a) (s.sup (fun i => dist2 y i)) := by
          funext y
          rw [Finset.sup_insert]
        rw [hs]
        exact (measurable_dist2 a).max ih
  exact h Finset.univ

/-- Evaluation of a `ℕ`-valued function at a measurable `ℕ`-valued index is measurable. -/
theorem measurable_nat_eval : Measurable (fun p : (ℕ → ℕ) × ℕ => p.1 p.2) :=
  measurable_from_prod_countable_left (fun y => measurable_pi_apply y)

theorem measurable_nat_eval_comp {α : Type*} [MeasurableSpace α] {g : α → ℕ → ℕ}
    (hg : Measurable g) {R : α → ℕ} (hR : Measurable R) :
    Measurable (fun a => g a (R a)) :=
  measurable_nat_eval.comp (hg.prodMk hR)

/-! ### The record-distance and record-time processes -/

/-- The paper's raw record defect `d_r = max_i d_i` on the extended record trajectory.
The compact state stores half-distances, so it must be doubled to recover the paper's
lattice-step distance `r - min_i X^i_{\tau_r}`. -/
noncomputable def dT (ω : ℕ → RecState N m × ℕ) (r : ℕ) : ℕ := 2 * dmax ((ω r).1)

/-- The paper's record time `τ_r` on the extended record trajectory. -/
def tauT (ω : ℕ → RecState N m × ℕ) (r : ℕ) : ℕ := (ω r).2

theorem measurable_evFst (k : ℕ) :
    Measurable (fun ω : ℕ → RecState N m × ℕ => (ω k).1) :=
  measurable_fst.comp (measurable_pi_apply k)

theorem measurable_evSnd (k : ℕ) :
    Measurable (fun ω : ℕ → RecState N m × ℕ => (ω k).2) :=
  measurable_snd.comp (measurable_pi_apply k)

theorem measurable_dT : Measurable (dT (N := N) (m := m)) :=
  measurable_pi_iff.2 fun r => (measurable_dmax.comp (measurable_evFst r)).const_mul 2

theorem measurable_tauT : Measurable (tauT (N := N) (m := m)) :=
  measurable_pi_iff.2 fun r => measurable_evSnd r

theorem measurable_dT_eval (r : ℕ) :
    Measurable fun ω : ℕ → RecState N m × ℕ => dT ω r :=
  measurable_pi_iff.1 measurable_dT r

theorem measurable_tauT_eval (r : ℕ) :
    Measurable fun ω : ℕ → RecState N m × ℕ => tauT ω r :=
  measurable_pi_iff.1 measurable_tauT r

/-! ### The paper's good-block event -/

/-- The paper's `Good r L`: the three block inequalities for the block `[r, r + B L]`. -/
def GoodT (B C₀ T : ℕ) (ω : ℕ → RecState N m × ℕ) (r L : ℕ) : Prop :=
  (tauT ω (r + B * L) ≤ tauT ω r + T * L) ∧
  (dT ω (r + B * L) ≤ L / 2) ∧
  (∀ u, r ≤ u → u ≤ r + B * L → dT ω u ≤ C₀ * L)

theorem measurableSet_goodT (B C₀ T r L : ℕ) :
    MeasurableSet {ω : ℕ → RecState N m × ℕ | GoodT B C₀ T ω r L} := by
  have h1 : MeasurableSet {ω : ℕ → RecState N m × ℕ |
      tauT ω (r + B * L) ≤ tauT ω r + T * L} :=
    measurableSet_le (measurable_tauT_eval _)
      ((measurable_tauT_eval _).add_const (T * L))
  have h2 : MeasurableSet {ω : ℕ → RecState N m × ℕ | dT ω (r + B * L) ≤ L / 2} :=
    measurableSet_le (measurable_dT_eval _) measurable_const
  have h3 : MeasurableSet {ω : ℕ → RecState N m × ℕ |
      ∀ u, r ≤ u → u ≤ r + B * L → dT ω u ≤ C₀ * L} := by
    have hEq : {ω : ℕ → RecState N m × ℕ |
        ∀ u, r ≤ u → u ≤ r + B * L → dT ω u ≤ C₀ * L}
        = ⋂ u : ℕ, {ω : ℕ → RecState N m × ℕ |
            (r ≤ u → u ≤ r + B * L → dT ω u ≤ C₀ * L)} := by
      ext ω
      simp
    rw [hEq]
    refine MeasurableSet.iInter fun u => ?_
    by_cases hu : r ≤ u ∧ u ≤ r + B * L
    · have hset : {ω : ℕ → RecState N m × ℕ | (r ≤ u → u ≤ r + B * L → dT ω u ≤ C₀ * L)}
          = {ω | dT ω u ≤ C₀ * L} := by
        ext ω
        simp only [Set.mem_ofPred_eq]
        exact ⟨fun h => h hu.1 hu.2, fun h _ _ => h⟩
      rw [hset]
      exact measurableSet_le (measurable_dT_eval u) measurable_const
    · have hset : {ω : ℕ → RecState N m × ℕ | (r ≤ u → u ≤ r + B * L → dT ω u ≤ C₀ * L)}
          = Set.univ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        exact fun h1 h2 => absurd ⟨h1, h2⟩ hu
      rw [hset]
      exact MeasurableSet.univ
  exact h1.inter (h2.inter h3)

theorem goodT_hS (B C₀ T : ℕ) (ω : ℕ → RecState N m × ℕ) (r L : ℕ)
    (hG : GoodT B C₀ T ω r L) :
    dT ω (r + B * L) ≤ L / 2 ∧ ∀ u, r ≤ u → u ≤ r + B * L → dT ω u ≤ C₀ * L :=
  ⟨hG.2.1, hG.2.2⟩

/-! ### The `ProbCtx` of the actual record chain -/

instance instIsProbabilityMeasure_recordTrajT (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (hm : 1 ≤ m) (ν : Measure (RecState N m × ℕ)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (recordTrajT p hp hp1 hm ν) := by
  refine ⟨?_⟩
  have h := recordTrajT_eval p hp hp1 hm ν 0
  have h2 : ((recordTrajT p hp hp1 hm ν).map (fun ω : ℕ → RecState N m × ℕ => ω 0)) Set.univ
      = (recordTrajT p hp hp1 hm ν) Set.univ := by
    rw [Measure.map_apply (measurable_pi_apply 0) MeasurableSet.univ]
    rfl
  rw [← h2, h, Function.iterate_zero_apply]
  exact measure_univ

/-- **`ProbCtx` for the actual record chain.**  The process `d` is the paper's record distance,
`Good` is the paper's conjunction of the three block inequalities on the extended trajectory
(so the record time `τ` is available), and the fields `hd`, `hdR`, `hg`, `hS` are *proved*.
`hterm`, `hR` and `hblk` are handed in as genuine path probabilities of `recordTrajT`, i.e. the
paper's `(recordo)` and `(blkprob)` for the real process. -/
noncomputable def probCtxT (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    (ν : Measure (RecState N m × ℕ)) [IsProbabilityMeasure ν]
    (B C₀ T : ℕ) (hB : 1 ≤ B) (hC₀ : 1 ≤ C₀)
    (R : (ℕ → RecState N m × ℕ) → ℕ) (hRmeas : Measurable R)
    (pfun : ℕ → ℝ≥0∞)
    (hterm : ∀ r L, 1 ≤ L → ∀ᵐ ω ∂(recordTrajT p hp hp1 hm ν),
      ∃ j, GoodT B C₀ T ω r (2 ^ j * L))
    (hR : ∀ᵐ ω ∂(recordTrajT p hp hp1 hm ν), ∀ r, R ω ≤ r → ∀ ℓ, 1 ≤ ℓ →
      dT ω r ≤ ℓ → ¬ GoodT B C₀ T ω r ℓ → 2 * C₀ * ℓ ≤ r)
    (hblk : ∀ ℓ, 1 ≤ ℓ → ∀ r, C₀ * ℓ ≤ r →
      (recordTrajT p hp hp1 hm ν)
        ({ω | dT ω r ≤ ℓ} ∩ {ω | ¬ GoodT B C₀ T ω r ℓ}) ≤ pfun ℓ) :
    RecordTight.ProbCtx (ℕ → RecState N m × ℕ) where
  μ := recordTrajT p hp hp1 hm ν
  hprob := instIsProbabilityMeasure_recordTrajT p hp hp1 hm ν
  B := B
  C₀ := C₀
  d := dT
  Good := GoodT B C₀ T
  R := R
  p := pfun
  hB := hB
  hC₀ := hC₀
  hd := measurable_dT
  hdR := measurable_nat_eval_comp measurable_dT hRmeas
  hg := fun r ℓ => measurableSet_goodT B C₀ T r ℓ
  hRmeas := hRmeas
  hS := fun ω r L hG _ => goodT_hS B C₀ T ω r L hG
  hterm := hterm
  hR := hR
  hblk := hblk

/-- **Conditional reduction of `htight` to the paper's two analytic inputs.**

The paper's `(recordo)` (as `hterm` and `hR`) and its fluid-limit block estimate `(blkprob)`
(as `hblk`), stated as path probabilities of the actual record chain, together with the
elementary summability of `(4Bℓ+1) p ℓ`, imply the tightness input `htight` of
`exists_invariant_measure_pos_hitKInf`.  Nothing here is unconditional: the three hypotheses
are exactly the residual analytic content of Prop. "tight".

The initial law `μ` of the record chain is arbitrary and enters only through the extension
`y ↦ (y,0)`; the conclusion is uniform in it. -/
theorem htight_of_blocks (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    (μ : Measure (RecState N m)) [IsProbabilityMeasure μ]
    (B C₀ T : ℕ) (hB : 1 ≤ B) (hC₀ : 1 ≤ C₀)
    (R : (ℕ → RecState N m × ℕ) → ℕ) (hRmeas : Measurable R)
    (pfun : ℕ → ℝ≥0∞)
    (hterm : ∀ r L, 1 ≤ L → ∀ᵐ ω ∂(recordTrajT p hp hp1 hm
      (μ.map (fun y : RecState N m => (y, 0)))), ∃ j, GoodT B C₀ T ω r (2 ^ j * L))
    (hR : ∀ᵐ ω ∂(recordTrajT p hp hp1 hm (μ.map (fun y : RecState N m => (y, 0)))),
      ∀ r, R ω ≤ r → ∀ ℓ, 1 ≤ ℓ → dT ω r ≤ ℓ → ¬ GoodT B C₀ T ω r ℓ → 2 * C₀ * ℓ ≤ r)
    (hblk : ∀ ℓ, 1 ≤ ℓ → ∀ r, C₀ * ℓ ≤ r →
      (recordTrajT p hp hp1 hm (μ.map (fun y : RecState N m => (y, 0))))
        ({ω | dT ω r ≤ ℓ} ∩ {ω | ¬ GoodT B C₀ T ω r ℓ}) ≤ pfun ℓ)
    (hsum : (∑' ℓ : ℕ, ((4 * B * ℓ + 1 : ℕ) : ℝ≥0∞) * pfun ℓ) ≠ ⊤) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ r : ℕ,
      (SwarmKB.step (hitKKernel p hm))^[r] μ (exh N m K)ᶜ ≤ ε := by
  classical
  set ν : Measure (RecState N m × ℕ) := μ.map (fun y => (y, 0)) with hνdef
  haveI : IsProbabilityMeasure ν := by
    rw [hνdef]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  let c := probCtxT p hp hp1 hm ν B C₀ T hB hC₀ R hRmeas pfun hterm hR hblk
  have hfst : ν.map Prod.fst = μ := by
    rw [hνdef, Measure.map_map measurable_fst
      (by fun_prop : Measurable fun y : RecState N m => (y, (0 : ℕ)))]
    rw [show (Prod.fst ∘ (fun y : RecState N m => (y, (0 : ℕ)))) = id from rfl, Measure.map_id]
  intro ε hε
  obtain ⟨K, hK⟩ := c.tightness (by simpa [c, probCtxT, RecordTight.ProbCtx.w] using hsum) ε hε
  refine ⟨K, fun r => ?_⟩
  have h1 : (recordTrajT p hp hp1 hm ν) {ω : ℕ → RecState N m × ℕ | 2 * K < dT ω r}
      = (SwarmKB.step (hitKKernel p hm))^[r] μ (exh N m K)ᶜ := by
    have hset : {ω : ℕ → RecState N m × ℕ | 2 * K < dT ω r}
        = {ω | (ω r).1 ∈ exh N m K}ᶜ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, dT]
      rw [show 2 * K < 2 * dmax ((ω r).1) ↔ K < dmax ((ω r).1) by omega]
      exact dmax_lt_iff_not_mem_exh ((ω r).1) K
    rw [hset, recordTrajT_tail p hp hp1 hm ν r K, hfst]
  calc (SwarmKB.step (hitKKernel p hm))^[r] μ (exh N m K)ᶜ
      = (recordTrajT p hp hp1 hm ν) {ω : ℕ → RecState N m × ℕ | 2 * K < dT ω r} := h1.symm
    _ = c.μ {ω | 2 * K < c.d ω r} := rfl
    _ ≤ c.μ {ω | K < c.d ω r} := measure_mono fun ω hω => by
      change K < dT ω r
      change 2 * K < dT ω r at hω
      omega
    _ ≤ ε := hK r

end RecKernel
end SimJump
