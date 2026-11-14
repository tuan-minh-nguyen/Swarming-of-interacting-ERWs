/-Strengthening of `M7Block.actual_block_law` from the terminal `(state, time)` pair to the whole
`Fin (r+1)` path of partial record endpoints, matching `M6Aggr.blockPathLaw` / `pathOf`.  Same
repaired box family, so no geometric hypothesis is left.
-/
import Swarm.ActualBlockDecomp
import Swarm.BlockPathLaw

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped ENNReal BigOperators

namespace M7Block

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model Swarming.FairWalk
open Swarming.Transition SimJump SimJump.RecKernel RecordoSupply Swarming.CurrentState
open SwarmRec M5FirstBlock M6Aggr
open SwarmRecordMeas SwarmRecordMeas.Actual RecordDefect

variable {N : ℕ} [Nonempty (Fin N)]

/-- The totalised actual record path up to level `r`. -/
noncomputable def actPath (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N) (hm : 1 ≤ m)
    (r : ℕ) : (i : Fin (r + 1)) → RecState N m × ℕ :=
  fun i => (actRecStateT p m U hm i, recTimeA p m U i)

/-- `pathOf` agrees with the nested chain and the prefix lengths. -/
theorem pathOf_eq {m : ℕ} (hm : 1 ≤ m) :
    ∀ (r : ℕ) (y : RecState N m) (t : ℕ) (w : Fin r → Word N) (i : Fin (r + 1)),
      pathOf hm y t r w i = (recStateF hm y r w i, t + preLen r w i)
  | 0, y, t, w, i => by
      have hi : i = 0 := Fin.ext (by omega)
      rw [hi]
      simp [pathOf_zero_coord, recStateF_zero, preLen_zero_right]
  | r + 1, y, t, w, i => by
      rw [pathOf_succ]
      rcases Fin.eq_zero_or_eq_succ i with h0 | ⟨j, hj⟩
      · subst h0
        rw [Fin.cons_zero]
        simp only [Fin.val_zero, recStateF_zero, preLen_zero_right, Nat.add_zero]
      · subst hj
        rw [Fin.cons_succ]
        rw [pathOf_eq hm r (SimJump.RecKernel.out hm (w 0).2 y) (t + (w 0).1)
          (fun i => w i.succ) j]
        simp only [Fin.val_succ, recStateF_succ, preLen_succ]
        congr 1
        omega

/-- The array piece of the repaired family on which the block path falls in `A`. -/
noncomputable def rpath {m : ℕ} (hm : 1 ≤ m) (p : ℝ) (r : ℕ)
    (A : Set ((i : Fin (r + 1)) → RecState N m × ℕ)) (w : Fin r → Word N) : Set (Array N) :=
  if pathOf hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w ∈ A then rbox p m r w else ∅

theorem measurableSet_rpath {m : ℕ} (hm : 1 ≤ m) {p : ℝ} {r : ℕ}
    {A : Set ((i : Fin (r + 1)) → RecState N m × ℕ)} (w : Fin r → Word N) :
    MeasurableSet (rpath (N := N) hm p r A w) := by
  rw [rpath]
  split
  · exact measurableSet_rbox
  · exact MeasurableSet.empty

/-- On the repaired box, the totalised actual path is exactly `pathOf` of the tuple. -/
theorem actPath_eq_pathOf {p : ℝ} {m : ℕ} (hm : 1 ≤ m) {r : ℕ} {w : Fin r → Word N}
    (hFR : FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w)
    {U : Swarming.Uniform.Array N} (hU : U ∈ rbox p m r w) :
    actPath p m U hm r = pathOf hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w := by
  funext i
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have hi : i = 0 := Fin.ext (by omega)
    rw [hi]
    rw [show actPath p m U hm 0 0 = (actRecStateT p m U hm 0, recTimeA p m U 0) from rfl,
      actRecStateT_zero, recTimeA_zero]
    rw [show pathOf hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 0 w 0
      = (SwarmRecordMeas.StartLaw.zeroState hm, (0 : ℕ)) from pathOf_zero_coord hm _ 0 0 w]
  · have hreach : U ∈ ReachAll p m := rbox_subset_reach hm hFR hr hU
    obtain ⟨h1, h2⟩ := box_det hm hreach hFR hU.1 (i : ℕ) (by omega)
    rw [show actPath p m U hm r i = (actRecStateT p m U hm (i : ℕ), recTimeA p m U (i : ℕ)) from rfl,
      actRecStateT_of_reach hm hreach (i : ℕ), h1, h2, pathOf_eq hm r _ 0 w i]
    simp

/-- **The unconditional finite record *path* law at the actual array**: the law of the whole
`Fin (r+1)`-path of partial record endpoints is the `M6Aggr.blockPathLaw` from the compatible start
law.  No geometric hypothesis is left. -/
theorem actual_blockPath_law {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 1 ≤ m) (hm2 : 2 ≤ m) (hN : 2 ≤ N) (r : ℕ)
    {A : Set ((i : Fin (r + 1)) → RecState N m × ℕ)} (hA : MeasurableSet A) :
    (arrayMeasure N) {U : Array N | actPath p m U hm r ∈ A}
      = blockPathLaw p hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r A := by
  classical
  have hpiece_sub : ∀ w : {w : Fin r → Word N //
      FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w},
      rpath hm p r A w.1 ⊆ {U : Array N | actPath p m U hm r ∈ A} := by
    intro w U hU
    simp only [rpath] at hU
    by_cases hmem : pathOf hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w.1 ∈ A
    · rw [if_pos hmem] at hU
      show actPath p m U hm r ∈ A
      rw [actPath_eq_pathOf hm w.2 hU]
      exact hmem
    · rw [if_neg hmem] at hU
      exact absurd hU (Set.notMem_empty U)
  have hdisj : Pairwise (fun w w' : {w : Fin r → Word N //
      FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w} =>
      Disjoint (rpath hm p r A w.1) (rpath hm p r A w'.1)) := by
    intro w w' hne
    simp only [rpath]
    by_cases hmem : pathOf hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w.1 ∈ A
    · by_cases hmem' : pathOf hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w'.1 ∈ A
      · rw [if_pos hmem, if_pos hmem']
        exact rbox_disjoint (p := p) (m := m) hm r hne
      · rw [if_pos hmem, if_neg hmem']
        exact disjoint_bot_right
    · rw [if_neg hmem]
      exact disjoint_bot_left
  have hae : {U : Array N | actPath p m U hm r ∈ A}
      =ᵐ[arrayMeasure N] ⋃ w : {w : Fin r → Word N //
          FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w}, rpath hm p r A w.1 := by
    filter_upwards [M4RecordGeom.ae_reachAll (N := N) hp0 hp1 hm2 hN] with U hU
    apply propext
    constructor
    · intro hSA
      obtain ⟨w, hw⟩ := rbox_covered hm r hU
      refine Set.mem_iUnion.mpr ⟨w, ?_⟩
      simp only [rpath]
      by_cases hmem : pathOf hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w.1 ∈ A
      · rw [if_pos hmem]
        exact hw
      · rw [if_neg hmem]
        exact absurd (by rw [← actPath_eq_pathOf hm w.2 hw]; exact hSA) hmem
    · intro hmem
      obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hmem
      exact hpiece_sub w hw
  have hcard : ∀ w : {w : Fin r → Word N //
      FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w},
      (arrayMeasure N) (rpath hm p r A w.1)
        = ENNReal.ofReal (blockProdF p hm (SwarmRecordMeas.StartLaw.zeroState hm) r w.1) *
            (if pathOf hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w.1 ∈ A then 1 else 0) := by
    intro w
    simp only [rpath]
    by_cases hmem : pathOf hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w.1 ∈ A
    · rw [if_pos hmem, if_pos hmem, mul_one, measure_rbox hp0 hp1 hm hm2 hN w.2]
    · rw [if_neg hmem, if_neg hmem, measure_empty, mul_zero]
  calc (arrayMeasure N) {U : Array N | actPath p m U hm r ∈ A}
      = (arrayMeasure N) (⋃ w : {w : Fin r → Word N //
          FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w},
          rpath hm p r A w.1) := measure_congr hae
    _ = ∑' w : {w : Fin r → Word N //
          FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w},
          (arrayMeasure N) (rpath hm p r A w.1) :=
        measure_iUnion hdisj (fun w => measurableSet_rpath hm w.1)
    _ = blockPathLaw p hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r A := by
        rw [blockPathLaw_apply p hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r hA,
          ← tsum_subtype_eq_of_eq_zero
            {w : Fin r → Word N | FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w}
            (fun w => ENNReal.ofReal (blockProdF p hm (SwarmRecordMeas.StartLaw.zeroState hm) r w) *
              (if pathOf hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w ∈ A then 1 else 0))
            (fun w hw => by
              rw [blockProdF_eq_zero_of_not_frChain p hm r
                (SwarmRecordMeas.StartLaw.zeroState hm) w hw, ENNReal.ofReal_zero, zero_mul])]
        exact tsum_congr hcard

/-- **The `r = 1` instance is the accepted first-iterate law's right-hand side.**  Consistency check
of `actual_block_law` against `M5FirstBlock.first_iterate_law`: the `r = 1` iterate is the single
stopped-record kernel step `hitKInfT`. -/
theorem actual_block_law_one {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 1 ≤ m) (hm2 : 2 ≤ m) (hN : 2 ≤ N)
    {A : Set (RecState N m × ℕ)} (hA : MeasurableSet A) :
    (arrayMeasure N) {U : Array N | (actRecStateT p m U hm 1, recTimeA p m U 1) ∈ A}
      = SimJump.RecKernel.hitKInfT p hm (SwarmRecordMeas.StartLaw.zeroState hm, 0) A := by
  rw [actual_block_law hp0 hp1 hm hm2 hN 1 hA, Function.iterate_one, M6Aggr.step_dirac,
    SimJump.RecKernel.hitKKernelT_apply]

end M7Block
