/-`areas/kac/REGEN_CONCAT.md` lists, as its gap (3), the *fidelity bridge*: `SwarmConcat.Chain N`
is an abstract segment sequence, and nothing turns the actual enriched record trajectory into one.
This file builds that bridge:

* `TrajCompat` is the trajectory-level form of `SwarmConcat.Chain.compat`
  (`0 + p_k(dur_k) = 1 + p_{k+1}(0)` at every level `k`), `trajCompat_iff_level` shows it is
  literally `Chain.compat` after the level shift, and `trajCompat_record_irrel` shows it never
  reads the record states — the exact structural reason why compatibility alone cannot supply the
  `π(F)` factor of the paper's `hstruct` identity.
* `chainOf` assembles a `Chain N` from **any** trajectory `ℕ → Seg N × RecState N m` (junk
  fallback off the compatible set), `chainOf_seg_of_compat` identifies its segments, and
  `chainOf_X_record` / `chainOf_X_cum_add` read the concatenated path `c.X` back through the
  ambient trajectory: at the record time `cum k` it is `k` plus the record state's own normalised
  array.
* `ModelTraj` is the model side: record states `y k`, first-record jump paths `q k` of length
  `len k`, and `y (k+1) = out (q k) (y k)`.  `ModelTraj.trajCompat` **proves** the compatibility
  from the model's own `segOfFirst_p_dur` / `segOf_p_zero` (no hypothesis), so `modelChain` is the
  missing actual record chain `→ Chain N` map.
* `modelChain_X_eq_pos` identifies the assembled chain's path inside every segment with the model's
  own relative positions `relP`, so the chain carries the whole path, not just its records.
* `chainLaw μ` is the pushforward of an ambient trajectory law; `chainLaw_apply_A_eq_segMass`
  computes the mass of the paper's regeneration event `A` as the ambient mass of a *segment-level*
  event, and `chainLaw_measurePreserving_shift` shows a shift-stationary compatible ambient law
  assembles into a shift-stationary chain law, so `chainLaw_kac_tsum` gives the Kac regeneration sum.
* `chain_hstruct_iff_stateMass`, `chain_hstruct_mass_necessary(_stateMass)` and the Dirac
  obstructions `chain_hstruct_dirac_false` / `constChain_not_hstruct` /
  `constTraj_kac_and_not_hstruct` pin the remaining `hstruct` input to a genuine mass/fresh-law
  identity: it is not implied by compatibility, measurability or Kac stationarity.
-/


import Swarm.DForward

set_option linter.unusedVariables false

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal
open SimJump
open Swarming.Uniform

attribute [local instance] Classical.propDecidable

/-!
## Contents

1. Trajectory-level compatibility (`TrajCompat`, `trajCompat_iff_level`, `trajCompat_record_irrel`,
   `measurableSet_stepCompat`, `measurableSet_trajCompat`, `ae_trajCompat_dirac`,
   `ae_trajCompat_of_step`).
2. The assembled chain (`segFun`, `chainOf`, `chainOf_seg_of_compat`, `chain_ext`, `chainOf_congr`)
   and its concatenated path (`chainOf_X_record`, `chainOf_X_cum_add`, `chainOf_X_record_eq_pos`,
   `chainOf_X_record_eq_level`).
3. The model-side trajectory (`ModelTraj`), its proved compatibility (`ModelTraj.trajCompat`) and the
   resulting chain (`modelChain`, `modelChain_seg`, `modelChain_X_record`, `modelChain_X_record_le`,
   `modelChain_X_eq_pos`, `modelChain_mem_A_iff`).
4. Measurability and the ambient chain law (`measurable_recPos_pi`, `measurable_dummySeg`,
   `measurable_segFun`, `measurable_chainOf`, `chainLaw`, `isProbabilityMeasure_chainLaw`,
   `chainLaw_apply`, `chainLaw_apply_A`, `chainLaw_apply_A_eq_pathMass`, `SegRegen0`,
   `mem_A_iff_segRegen`, `chainLaw_apply_A_eq_segMass`, `chainLaw_dirac`,
   `chainLaw_dirac_apply_A`).
5. `hstruct`: reductions and obstructions (`chain_hstruct_iff_stateMass`,
   `chain_hstruct_mass_necessary`, `chain_hstruct_mass_necessary_stateMass`,
   `chain_hstruct_dirac_false`, `chain_hstruct_dirac_ambient_false`).
6. An explicitly inhabited shift-invariant chain law on `A` (`constSeg`, `constChain`,
   `constChain_mem_A`, `constChain_shift`, `constChain_measurePreserving`, `constChain_kac`,
   `constChain_not_hstruct`).
7. Shift-equivariance and the Kac payoff (`trajShift`, `measurable_trajShift`, `trajCompat_shift`,
   `chainOf_shift`, `chainLaw_measurePreserving_shift`, `chainLaw_kac_tsum`).
8. End to end on an explicit ambient law (`constTraj`, `constTraj_compat`, `constTraj_shift`,
   `chainOf_constTraj`, `constTraj_measurePreserving`, `constTraj_kac_and_not_hstruct`).
-/

namespace SwarmChainAssemble

set_option autoImplicit false

variable {N m : ℕ}

/-! ## 1. Trajectory-level compatibility -/

/-- The trajectory-level form of `SwarmConcat.Chain.compat`: the segment at level `k` ends exactly
one level above the starting array of the segment at level `k+1`.  It is the `k`-indexed form of
`SwarmDHStruct.compat_step_ae`'s conclusion. -/
def TrajCompat (A : ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m) : Prop :=
  ∀ (k : ℕ) (i : Fin N), (A k).1.p (A k).1.dur i = 1 + (A (k + 1)).1.p 0 i

/-- **`TrajCompat` is exactly `Chain.compat` after the level shift.** -/
theorem trajCompat_iff_level (A : ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m) :
    TrajCompat A ↔ ∀ (k : ℕ) (i : Fin N),
      (k : ℤ) + (A k).1.p (A k).1.dur i = ((k + 1 : ℕ) : ℤ) + (A (k + 1)).1.p 0 i := by
  constructor
  · intro h k i
    have hk := h k i
    push_cast
    linarith
  · intro h k i
    have hk := h k i
    push_cast at hk
    linarith

/-- **Compatibility is blind to the record states.**  `TrajCompat` only reads the segment component
of the trajectory, so *no* compatibility hypothesis — a.e. or pointwise — can constrain the law of
the endpoint record states.  This is the structural reason why `hstruct` (whose right-hand side
carries `π(F)`) is not a consequence of compatibility: the `π(F)` factor lives entirely in the
`RecState` component, which the assembled chain forgets. -/
theorem trajCompat_record_irrel (S : ℕ → SwarmConcat.Seg N) (y y' : ℕ → SwarmRec.RecState N m) :
    TrajCompat (fun k => (S k, y k)) ↔ TrajCompat (fun k => (S k, y' k)) :=
  Iff.rfl

/-- One step of the trajectory-level compatibility, as a measurable set. -/
theorem measurableSet_stepCompat (k : ℕ) :
    MeasurableSet {A : ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m |
      ∀ i : Fin N, (A k).1.p (A k).1.dur i = 1 + (A (k + 1)).1.p 0 i} := by
  have hset : {A : ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m |
        ∀ i : Fin N, (A k).1.p (A k).1.dur i = 1 + (A (k + 1)).1.p 0 i}
      = ⋂ (i : Fin N), ⋃ (n : ℕ),
          ({A | (A k).1.dur = n} ∩
            {A | (A k).1.p n i = 1 + (A (k + 1)).1.p 0 i}) := by
    ext A
    simp only [mem_iInter, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro h i
      exact ⟨(A k).1.dur, rfl, h i⟩
    · rintro h i
      obtain ⟨n, hn, hp⟩ := h i
      rw [← hn] at hp
      exact hp
  rw [hset]
  refine MeasurableSet.iInter fun i => MeasurableSet.iUnion fun n => ?_
  refine MeasurableSet.inter ?_ ?_
  · have : Measurable fun A : ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m => (A k).1.dur :=
      SwarmConcat.measurable_seg_dur.comp
        (measurable_fst.comp (measurable_pi_apply k))
    exact MeasurableSet.preimage (measurableSet_singleton n) this
  · refine measurableSet_eq_fun ?_ ?_
    · exact (SwarmConcat.measurable_seg_p (N := N) n i).comp
        (measurable_fst.comp (measurable_pi_apply k))
    · exact measurable_const.add
        ((SwarmConcat.measurable_seg_p (N := N) 0 i).comp
          (measurable_fst.comp (measurable_pi_apply (k + 1))))

/-- The compatibility of a trajectory, as a measurable set. -/
theorem measurableSet_trajCompat :
    MeasurableSet {A : ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m | TrajCompat A} := by
  have hset : {A : ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m | TrajCompat A}
      = ⋂ (k : ℕ), {A | ∀ i : Fin N, (A k).1.p (A k).1.dur i = 1 + (A (k + 1)).1.p 0 i} := by
    ext A
    simp only [TrajCompat, mem_iInter, mem_ofPred_eq]
  rw [hset]
  exact MeasurableSet.iInter (fun k => measurableSet_stepCompat k)

/-- A compatible trajectory is compatible almost surely for its own Dirac law. -/
theorem ae_trajCompat_dirac (A : ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m)
    (h : TrajCompat A) : ∀ᵐ x ∂(Measure.dirac A), TrajCompat x := by
  rw [MeasureTheory.ae_iff]
  rw [show {x : ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m | ¬ TrajCompat x}
      = {x | TrajCompat x}ᶜ from rfl,
    Measure.dirac_apply' A measurableSet_trajCompat.compl, Set.indicator_apply]
  simp [h]

/-- **The all-levels a.e. compatibility is a countably many finite-window statement.**  If every
two-coordinate compatibility event (one segment and the next one) carries full mass, then the
trajectory is compatible almost surely.  The pairwise statements are exactly the shape of
`SwarmDHStruct.compat_step_ae`; what remains for an ambient law is their disintegration against the
two-coordinate marginal. -/
theorem ae_trajCompat_of_step (μ : Measure (ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m))
    [IsProbabilityMeasure μ]
    (h : ∀ k, μ {A : ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m |
          ∀ i : Fin N, (A k).1.p (A k).1.dur i = 1 + (A (k + 1)).1.p 0 i} = 1) :
    ∀ᵐ A ∂μ, TrajCompat A := by
  rw [MeasureTheory.ae_iff]
  have hset : {A : ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m | ¬ TrajCompat A}
      = ⋃ (k : ℕ), {A | ¬ ∀ i : Fin N,
          (A k).1.p (A k).1.dur i = 1 + (A (k + 1)).1.p 0 i} := by
    ext A
    simp only [TrajCompat, mem_iUnion, mem_ofPred_eq, not_forall]
  rw [hset]
  refine measure_iUnion_null fun k => ?_
  have hmeas : MeasurableSet {A : ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m |
      ∀ i : Fin N, (A k).1.p (A k).1.dur i = 1 + (A (k + 1)).1.p 0 i} :=
    measurableSet_stepCompat k
  have hcompl : {A : ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m | ¬ ∀ i : Fin N,
        (A k).1.p (A k).1.dur i = 1 + (A (k + 1)).1.p 0 i}
      = {A | ∀ i : Fin N, (A k).1.p (A k).1.dur i = 1 + (A (k + 1)).1.p 0 i}ᶜ := rfl
  rw [hcompl, measure_compl hmeas (measure_ne_top μ _), h k, measure_univ]
  simp

/-! ## 2. The assembled chain -/

/-- The segment sequence of an ambient trajectory: the trajectory's own segments on the compatible
set, and the constant junk segment of the first record state off it (where no mass is claimed). -/
noncomputable def segFun (A : ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m) :
    ℕ → SwarmConcat.Seg N :=
  fun k => if TrajCompat A then (A k).1 else SwarmSegKernel.dummySeg (A 0).2

/-- **The assembled chain.**  Every trajectory of the ambient space maps to a genuine
`SwarmConcat.Chain`: on the compatible set its segments are the trajectory's, off it a constant
junk chain of the first record state.  `Chain.compat` is *proved*, using the level additivity of
the trajectory in the first case and the explicit form of `dummySeg` in the second. -/
noncomputable def chainOf (A : ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m) :
    SwarmConcat.Chain N where
  seg := segFun A
  compat := by
    intro k i
    by_cases h : TrajCompat A
    · have hseg : ∀ j, segFun A j = (A j).1 := fun j => by simp [segFun, h]
      rw [hseg k, hseg (k + 1)]
      have hk := h k i
      push_cast
      linarith
    · have hseg : ∀ j, segFun A j = SwarmSegKernel.dummySeg (A 0).2 := fun j => by
        simp [segFun, h]
      rw [hseg k, hseg (k + 1)]
      have hp1 : (SwarmSegKernel.dummySeg (A 0).2).p
            (SwarmSegKernel.dummySeg (A 0).2).dur i
          = (Record.ofRecState (A 0).2).pos i + 1 := by
        simp [SwarmSegKernel.dummySeg]
      have hp0 : (SwarmSegKernel.dummySeg (A 0).2).p 0 i
          = (Record.ofRecState (A 0).2).pos i :=
        SwarmSegKernel.dummySeg_p_zero (A 0).2 i
      rw [hp1, hp0]
      push_cast
      ring

/-- On the compatible set the assembled chain's segments are the trajectory's own. -/
theorem chainOf_seg_of_compat {A : ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m}
    (h : TrajCompat A) (k : ℕ) : (chainOf A).seg k = (A k).1 := by
  simp [chainOf, segFun, h]

/-- Structure extensionality for chains: a chain is determined by its segment sequence (the
compatibility field is a proof). -/
theorem chain_ext {c d : SwarmConcat.Chain N} (h : ∀ k, c.seg k = d.seg k) : c = d := by
  rcases c with ⟨s, hs⟩
  rcases d with ⟨t, ht⟩
  rw [SwarmConcat.Chain.mk.injEq]
  exact funext h

/-- Two compatible trajectories with the same segments assemble to the same chain — in particular
the assembled chain does not see the endpoint record states. -/
theorem chainOf_congr {A A' : ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m}
    (h : TrajCompat A) (h' : TrajCompat A') (hseg : ∀ k, (A k).1 = (A' k).1) :
    chainOf A = chainOf A' := by
  refine chain_ext fun k => ?_
  rw [chainOf_seg_of_compat h k, chainOf_seg_of_compat h' k, hseg k]

/-! ## 3. The concatenated path `c.X` read through the trajectory -/

/-- The concatenated path at the record time of level `k` is the level plus the trajectory's own
start array. -/
theorem chainOf_X_record {A : ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m} (h : TrajCompat A)
    (k : ℕ) (i : Fin N) :
    (chainOf A).X ((chainOf A).cum k) i = (k : ℤ) + (A k).1.p 0 i := by
  rw [SwarmConcat.Chain.X_record, chainOf_seg_of_compat h k]

/-- The concatenated path inside segment `j`, at any positive local time up to the segment's end. -/
theorem chainOf_X_cum_add {A : ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m} (h : TrajCompat A)
    {j n : ℕ} (hn : 1 ≤ n) (hnd : n ≤ (A j).1.dur) (i : Fin N) :
    (chainOf A).X ((chainOf A).cum j + n) i = (j : ℤ) + (A j).1.p n i := by
  have hnd' : n ≤ ((chainOf A).seg j).dur := by rw [chainOf_seg_of_compat h j]; exact hnd
  rw [SwarmConcat.Chain.X_cum_add (c := chainOf A) hn hnd' i, chainOf_seg_of_compat h j]

/-- **The normalisation bridge.**  If every segment of the trajectory starts at its own record
state's normalised position array (the `SwarmDHStruct.StartSet` condition, true for every atom of
`SwarmSegKernel.asegK` by `segOf_p_zero`), then the concatenated path at the level-`k` record time
is exactly `k` plus that array — the paper's "subtract `1` from every position" applied `k` times. -/
theorem chainOf_X_record_eq_pos {A : ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m}
    (h : TrajCompat A)
    (hstart : ∀ (k : ℕ) (i : Fin N), (A k).1.p 0 i = (Record.ofRecState (A k).2).pos i)
    (k : ℕ) (i : Fin N) :
    (chainOf A).X ((chainOf A).cum k) i
      = (k : ℤ) + (Record.ofRecState (A k).2).pos i := by
  rw [chainOf_X_record h k i, hstart k i]

/-- At a simultaneous record (all walkers at the record level) the concatenated path sits exactly
at the level. -/
theorem chainOf_X_record_eq_level {A : ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m}
    (h : TrajCompat A)
    (hstart : ∀ (k : ℕ) (i : Fin N), (A k).1.p 0 i = (Record.ofRecState (A k).2).pos i)
    (hsr : ∀ (k : ℕ) (i : Fin N), (Record.ofRecState (A k).2).pos i = 0)
    (k : ℕ) (i : Fin N) :
    (chainOf A).X ((chainOf A).cum k) i = (k : ℤ) := by
  rw [chainOf_X_record_eq_pos h hstart k i, hsr k i, add_zero]

/-! ## 4. The model-side enriched record trajectory

The hypothesis `TrajCompat` of §2 is *not* an extra assumption on the model: a genuine record
trajectory of the interacting walk — record states `y k`, the first-record jump paths `q k` of
length `len k`, and the model's own next-record state `RecKernel.out` — always assembles into a
`Chain`, with `Chain.compat` proved from `segOfFirst_p_dur` and `segOf_p_zero`. -/

/-- A record trajectory of the model: the record states, the first-record jump path of each
record step and its length, with the model's own deterministic next-record update. -/
structure ModelTraj (N m : ℕ) (hm : 1 ≤ m) where
  /-- the record state at level `k` -/
  y : ℕ → SwarmRec.RecState N m
  /-- the duration of the record step starting at level `k` -/
  len : ℕ → ℕ
  /-- the jump vectors of the record step at level `k` -/
  q : (k : ℕ) → Fin (len k) → JumpVec N
  /-- the step ends at the first time the maximum reaches the next level -/
  first : ∀ k, Record.FirstRecord (Record.extendPath (q k)) (len k) (Record.ofRecState (y k))
  /-- the next record state is the model's own normalised record state -/
  next : ∀ k, y (k + 1) = RecKernel.out hm (q k) (y k)

namespace ModelTraj

variable {hm : 1 ≤ m}

/-- The enriched trajectory of a model record trajectory: the segment of each record step together
with the next record state.  This is the `SwarmSegKernel.asegK` atom shape. -/
noncomputable def traj (M : ModelTraj N m hm) :
    ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m :=
  fun k => (SwarmSegKernel.segOf (M.y k) (M.len k) (M.q k), M.y (k + 1))

/-- The trajectory is a path of genuine `asegK` atoms: the segment and the endpoint record state
are the model's own. -/
theorem traj_eq_atom (M : ModelTraj N m hm) (k : ℕ) :
    M.traj k = (SwarmSegKernel.segOf (M.y k) (M.len k) (M.q k),
      RecKernel.out hm (M.q k) (M.y k)) := by
  simp only [traj, M.next k]

/-- The endpoint record state of step `k` is the base record state of step `k+1` (definitionally:
the trajectory's second component *is* the next state). -/
theorem traj_snd (M : ModelTraj N m hm) (k : ℕ) : (M.traj k).2 = M.y (k + 1) := rfl

/-- **The model's own level additivity.**  Every record trajectory of the model is compatible, so
the abstraction of §2 loses nothing: `TrajCompat` is discharged from `FirstRecord`, `segOf_p_zero`
and the record update. -/
theorem trajCompat (M : ModelTraj N m hm) : TrajCompat M.traj := by
  intro k i
  have hk : 0 < M.len k := SwarmDHStruct.firstRecord_ne_zero (M.first k)
  have hseg : (M.traj k).1
      = SwarmSegKernel.segOfFirst (M.y k) (M.len k) (M.q k) hk (M.first k) :=
    SwarmDHStruct.segOf_of_firstRecord hk (M.first k)
  have hlhs : (M.traj k).1.p (M.traj k).1.dur i
      = 1 + (Record.ofRecState (RecKernel.out hm (M.q k) (M.y k))).pos i := by
    rw [hseg]
    exact SwarmSegKernel.segOfFirst_p_dur (M.y k) hm (M.q k) hk (M.first k) i
  have hrhs : (M.traj (k + 1)).1.p 0 i
      = (Record.ofRecState (RecKernel.out hm (M.q k) (M.y k))).pos i := by
    show (SwarmSegKernel.segOf (M.y (k + 1)) (M.len (k + 1)) (M.q (k + 1))).p 0 i = _
    rw [SwarmSegKernel.segOf_p_zero (M.y (k + 1)) (M.len (k + 1)) (M.q (k + 1)) i,
      M.next k]
  show (M.traj k).1.p (M.traj k).1.dur i = 1 + (M.traj (k + 1)).1.p 0 i
  rw [hlhs, hrhs]

end ModelTraj

/-- **The actual record chain of the model, as a `Chain`.**  This is `REGEN_CONCAT.md`'s gap (3):
the model's enriched record trajectory is turned into the abstract segment chain, with
`Chain.compat` proved (not assumed). -/
noncomputable def modelChain {hm : 1 ≤ m} (M : ModelTraj N m hm) : SwarmConcat.Chain N :=
  chainOf M.traj

/-- The assembled model chain's segments are the model's own record segments. -/
theorem modelChain_seg {hm : 1 ≤ m} (M : ModelTraj N m hm) (k : ℕ) :
    (modelChain M).seg k = SwarmSegKernel.segOf (M.y k) (M.len k) (M.q k) :=
  chainOf_seg_of_compat M.trajCompat k

/-- **The normalisation identify at the record times, on the model side.**  At the level-`k`
record time the concatenated path is the level `k` plus the record state's own normalised array
`-2 d_i` — i.e. the paper's "subtract `1` from every position", iterated. -/
theorem modelChain_X_record {hm : 1 ≤ m} (M : ModelTraj N m hm) (k : ℕ) (i : Fin N) :
    (modelChain M).X ((modelChain M).cum k) i
      = (k : ℤ) + (Record.ofRecState (M.y k)).pos i := by
  show (chainOf M.traj).X ((chainOf M.traj).cum k) i = _
  rw [chainOf_X_record M.trajCompat k i]
  exact congrArg ((k : ℤ) + ·) (SwarmSegKernel.segOf_p_zero (M.y k) (M.len k) (M.q k) i)

/-- At a record time of the model chain the walkers sit at the level plus `-2 d_i`, hence at or
below the level, with at least one walker exactly at the level: the record-state conditions are
the concatenated path's own. -/
theorem modelChain_X_record_le {hm : 1 ≤ m} (M : ModelTraj N m hm) (k : ℕ) (i : Fin N) :
    (modelChain M).X ((modelChain M).cum k) i ≤ (k : ℤ) := by
  rw [modelChain_X_record]
  have h := SwarmSegKernel.ofRecState_pos_nonpos (M.y k) i
  linarith

/-- The model chain's regeneration event in segment form. -/
theorem modelChain_mem_A_iff {hm : 1 ≤ m} (M : ModelTraj N m hm) :
    modelChain M ∈ SwarmConcat.Chain.A ↔
      (∀ i, (SwarmSegKernel.segOf (M.y 0) (M.len 0) (M.q 0)).p 0 i = 0) ∧
        ∀ (j n : ℕ), 1 ≤ n → n ≤ (SwarmSegKernel.segOf (M.y j) (M.len j) (M.q j)).dur →
          ∀ i, (0 : ℤ) < (j : ℤ) + (SwarmSegKernel.segOf (M.y j) (M.len j) (M.q j)).p n i := by
  rw [SwarmConcat.Chain.mem_A_iff]
  show SwarmConcat.Chain.Regen (modelChain M) 0 ↔ _
  simp only [SwarmConcat.Chain.Regen, modelChain_seg, Nat.zero_le, forall_const]
  tauto

/-! ## 5. Measurability of the assembly and the ambient chain law -/

/-- The record state's normalised position array, as one measurable map. -/
theorem measurable_recPos_pi :
    Measurable fun y : SwarmRec.RecState N m => fun i : Fin N => (Record.ofRecState y).pos i :=
  measurable_pi_iff.mpr (fun i => SwarmDHStruct.measurable_ofRecState_pos N m i)

/-- The junk segment is a measurable function of the record state. -/
theorem measurable_dummySeg : Measurable (SwarmSegKernel.dummySeg (N := N) (m := m)) := by
  rw [SwarmSegKernel.measurable_seg_iff]
  constructor
  · have hdur : (fun y : SwarmRec.RecState N m => (SwarmSegKernel.dummySeg y).dur)
        = fun _ => 1 := rfl
    rw [hdur]
    exact measurable_const
  · have hp : (fun y : SwarmRec.RecState N m => (SwarmSegKernel.dummySeg y).p)
        = fun y => fun (n : ℕ) (i : Fin N) => (Record.ofRecState y).pos i + (n : ℤ) := rfl
    rw [hp]
    refine measurable_pi_iff.mpr (fun n => measurable_pi_iff.mpr (fun i => ?_))
    exact (SwarmDHStruct.measurable_ofRecState_pos N m i).add measurable_const

/-- The segment sequence of the assembly is measurable in the trajectory. -/
theorem measurable_segFun (k : ℕ) :
    Measurable fun A : ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m => segFun A k := by
  have hs : MeasurableSet {A : ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m | TrajCompat A} :=
    measurableSet_trajCompat
  refine Measurable.ite hs ?_ ?_
  · exact measurable_fst.comp (measurable_pi_apply k)
  · exact measurable_dummySeg.comp (measurable_snd.comp (measurable_pi_apply 0))

/-- **The assembly is measurable**, so an ambient trajectory law pushes forward to a chain law. -/
theorem measurable_chainOf : Measurable (chainOf (N := N) (m := m)) := by
  rw [measurable_iff_comap_le]
  have hcomp : MeasurableSpace.comap (chainOf (N := N) (m := m))
        (inferInstance : MeasurableSpace (SwarmConcat.Chain N))
      = MeasurableSpace.comap
          (fun A : ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m => fun k => segFun A k)
          (inferInstance : MeasurableSpace (ℕ → SwarmConcat.Seg N)) := by
    rw [show (inferInstance : MeasurableSpace (SwarmConcat.Chain N))
        = MeasurableSpace.comap (fun c : SwarmConcat.Chain N => c.seg)
          (inferInstance : MeasurableSpace (ℕ → SwarmConcat.Seg N)) from rfl]
    rw [MeasurableSpace.comap_comp]
    rfl
  rw [hcomp]
  exact Measurable.comap_le (measurable_pi_iff.mpr fun k => measurable_segFun k)

/-- The chain law of an ambient trajectory law. -/
noncomputable def chainLaw (μ : Measure (ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m)) :
    Measure (SwarmConcat.Chain N) :=
  μ.map chainOf

instance isProbabilityMeasure_chainLaw
    (μ : Measure (ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (chainLaw μ) :=
  Measure.isProbabilityMeasure_map measurable_chainOf.aemeasurable

/-- The chain law is the pushforward along the assembly. -/
theorem chainLaw_apply (μ : Measure (ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m))
    {s : Set (SwarmConcat.Chain N)} (hs : MeasurableSet s) :
    chainLaw μ s = μ (chainOf ⁻¹' s) :=
  Measure.map_apply measurable_chainOf hs

/-- **The mass of the paper's regeneration event, read on the ambient trajectory space.** -/
theorem chainLaw_apply_A (μ : Measure (ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m)) :
    chainLaw μ SwarmConcat.Chain.A = μ {A | chainOf A ∈ SwarmConcat.Chain.A} := by
  rw [chainLaw_apply μ SwarmConcat.Chain.measurableSet_A]
  rfl

/-- **Path form.**  `Chain.A` is exactly the `strictPos` event of the concatenated path
(`SwarmDHStruct.ChainStep.A_eq_preimage`), so the chain's regeneration mass is the ambient mass of
the assembled concatenated path's strict positivity. -/
theorem chainLaw_apply_A_eq_pathMass
    (μ : Measure (ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m)) :
    chainLaw μ SwarmConcat.Chain.A
      = μ {A | (fun n i => (chainOf A).X n i) ∈ SwarmFresh.strictPos (N := N)} := by
  rw [chainLaw_apply_A, SwarmDHStruct.ChainStep.A_eq_preimage]
  rfl

/-- The regeneration event of the chain, written in the ambient trajectory's own segment
coordinates: all walkers at the level at time `0`, and above it at every positive time of every
segment. -/
def SegRegen0 (S : ℕ → SwarmConcat.Seg N) : Prop :=
  (∀ i, (S 0).p 0 i = 0) ∧
    ∀ (j n : ℕ), 1 ≤ n → n ≤ (S j).dur → ∀ i, (0 : ℤ) < (j : ℤ) + (S j).p n i

/-- On the compatible set, membership in `Chain.A` is a property of the trajectory's segments
alone — the endpoint record states are invisible to it. -/
theorem mem_A_iff_segRegen {A : ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m}
    (h : TrajCompat A) :
    chainOf A ∈ SwarmConcat.Chain.A ↔ SegRegen0 (fun k => (A k).1) := by
  rw [SwarmConcat.Chain.mem_A_iff]
  show SwarmConcat.Chain.Regen (chainOf A) 0 ↔ SegRegen0 (fun k => (A k).1)
  simp only [SwarmConcat.Chain.Regen, SegRegen0, chainOf_seg_of_compat h]
  simp only [Nat.zero_le, true_implies]
  exact Iff.rfl

/-- **The normalisation / PathOntoChain bridge.**  For an ambient probability law that is
compatible almost surely, the mass of the chain's regeneration event is exactly the ambient
probability of the segment-coordinate regeneration event.  This is the form consumed by the Kac
layer: the chain mass is computed without knowing the chain law, only the segment law. -/
theorem chainLaw_apply_A_eq_segMass
    (μ : Measure (ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m)) [IsProbabilityMeasure μ]
    (hcompat : ∀ᵐ A ∂μ, TrajCompat A) :
    chainLaw μ SwarmConcat.Chain.A = μ {A | SegRegen0 (fun k => (A k).1)} := by
  rw [chainLaw_apply_A]
  refine measure_congr ?_
  filter_upwards [hcompat] with A hA
  exact propext (mem_A_iff_segRegen hA)

/-! ## 6. What the assembly does and does not give for the paper's `hstruct`

`SwarmDHStruct.chain_hstruct_iff` reduces the paper's structural mass identity to a path-mass
identity for a chain law `ν`.  The assembly above supplies `ν = μ.map chainOf` from an ambient
trajectory law; the theorems below record exactly what that buys and what it cannot buy.
-/

/-- **`hstruct` is an identity between a chain mass and a `π`-average of per-record-state array
masses.**  With `SwarmFreshState.fresh_mass_integral_srSet`, the paper's right-hand side
`π(F)·P(V ∩ B)` is an integral over the record states in `F = srSet` of the actual array model
started from that state.  So the chain side must match the *array model* state by state; this is
the fresh-law identification, not a compatibility or measurability statement. -/
theorem chain_hstruct_iff_stateMass {hm : 1 ≤ m} (p : ℝ) (π : Measure (SwarmRec.RecState N m))
    (ν : Measure (SwarmConcat.Chain N)) :
    (∀ B : Set (ℕ → Fin N → ℤ), MeasurableSet B →
        ν ((fun c : SwarmConcat.Chain N => (fun n i => c.X n i)) ⁻¹'
            (SwarmFresh.strictPos (N := N) ∩ B))
          = π (SwarmRec.srSet N m) * (arrayMeasure N) {U : Array N |
              SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N) ∩ B})
      ↔ ∀ B : Set (ℕ → Fin N → ℤ), MeasurableSet B →
          ν ((fun c : SwarmConcat.Chain N => (fun n i => c.X n i)) ⁻¹'
              (SwarmFresh.strictPos (N := N) ∩ B))
            = ∫⁻ y in SwarmRec.srSet N m, (arrayMeasure N) {U : Array N |
                SwarmFreshState.FromV p m U (SwarmFreshState.walkStateOf y) ∧
                  (fun n i => (SwarmRestart.trajFrom p m U
                    (SwarmFreshState.walkStateOf y) n).pos i) ∈ B} ∂π := by
  constructor
  · intro h B hB
    rw [h B hB, ← SwarmFreshState.fresh_mass_integral_srSet (N := N) hm p π (B := B)]
  · intro h B hB
    rw [h B hB, ← SwarmFreshState.fresh_mass_integral_srSet (N := N) hm p π (B := B)]

/-- **`hstruct` forces the total mass of the regeneration event**: at `B = univ` it reads
`ν(A) = π(F)·P(V)`, because `A = Φ ⁻¹' strictPos` (`ChainStep.A_eq_preimage`).  Any chain law whose
`A`-mass is wrong therefore falsifies `hstruct`, however compatible its segments are. -/
theorem chain_hstruct_mass_necessary (p : ℝ) (π : Measure (SwarmRec.RecState N m))
    (ν : Measure (SwarmConcat.Chain N))
    (h : ∀ B : Set (ℕ → Fin N → ℤ), MeasurableSet B →
        ν ((fun c : SwarmConcat.Chain N => (fun n i => c.X n i)) ⁻¹'
            (SwarmFresh.strictPos (N := N) ∩ B))
          = π (SwarmRec.srSet N m) * (arrayMeasure N) {U : Array N |
              SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N) ∩ B}) :
    ν SwarmConcat.Chain.A
      = π (SwarmRec.srSet N m) * (arrayMeasure N) {U : Array N |
          SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)} := by
  have h1 := h Set.univ MeasurableSet.univ
  rwa [Set.inter_univ, ← SwarmDHStruct.ChainStep.A_eq_preimage] at h1

/-- **A Dirac chain law on `A` falsifies `hstruct`** as soon as the paper's mass product
`π(F)·P(V)` is not `1`.  Compatibility, measurability and even membership of `A` are all satisfied;
what fails is precisely the fresh-law mass identity. -/
theorem chain_hstruct_dirac_false (p : ℝ) (π : Measure (SwarmRec.RecState N m))
    {c : SwarmConcat.Chain N} (hc : c ∈ SwarmConcat.Chain.A)
    (hne : π (SwarmRec.srSet N m) * (arrayMeasure N) {U : Array N |
        SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)} ≠ 1) :
    ¬ ∀ B : Set (ℕ → Fin N → ℤ), MeasurableSet B →
        (Measure.dirac c) ((fun c : SwarmConcat.Chain N => (fun n i => c.X n i)) ⁻¹'
            (SwarmFresh.strictPos (N := N) ∩ B))
          = π (SwarmRec.srSet N m) * (arrayMeasure N) {U : Array N |
              SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N) ∩ B} := by
  intro h
  have hmass := chain_hstruct_mass_necessary p π (Measure.dirac c) h
  rw [Measure.dirac_apply' c SwarmConcat.Chain.measurableSet_A] at hmass
  simp only [Set.indicator_of_mem hc, Pi.one_apply] at hmass
  exact hne hmass.symm

/-! ## 7. A shift-invariant chain law on `A`: the Kac layer holds, `hstruct` fails

The obstruction above is not vacuous: there *is* a shift-invariant probability on `Chain N`
concentrated on `A`, so every Kac display of `RegenConcat.lean` applies to it, and it still violates
`hstruct`.  This separates the Kac/regeneration topology from the fresh-law mass identity. -/

/-- The all-right segment: one step, every walker one level up. -/
noncomputable def constSeg (hN : 0 < N) : SwarmConcat.Seg N where
  dur := 1
  dur_pos := Nat.one_pos
  p := fun n _ => (n : ℤ)
  start_le := by
    intro i
    simp
  start_min := ⟨⟨0, hN⟩, rfl⟩
  lt_one := by
    intro n hn i
    have hn0 : n = 0 := by omega
    subst hn0
    norm_num
  step := by
    intro n hn i
    left
    push_cast
    ring

/-- The constant all-right chain: every level-`k` record is one step after the previous one. -/
noncomputable def constChain (hN : 0 < N) : SwarmConcat.Chain N where
  seg := fun _ => constSeg hN
  compat := by
    intro k i
    show (k : ℤ) + ((1 : ℕ) : ℤ) = ((k + 1 : ℕ) : ℤ) + ((0 : ℕ) : ℤ)
    push_cast
    ring

/-- The constant chain is a regeneration point: it lies in the paper's `A`. -/
theorem constChain_mem_A (hN : 0 < N) : constChain hN ∈ SwarmConcat.Chain.A := by
  rw [SwarmConcat.Chain.mem_A_iff]
  show SwarmConcat.Chain.Regen (constChain hN) 0
  constructor
  · intro i
    show ((0 : ℕ) : ℤ) = 0
    norm_num
  · intro j _ n hn hnd i
    show (0 : ℤ) < (j : ℤ) + ((n : ℕ) : ℤ)
    have hnd1 : n ≤ 1 := hnd
    have hn1 : n = 1 := by omega
    subst hn1
    push_cast
    have hj : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
    linarith

/-- The constant chain is a fixed point of the record shift. -/
theorem constChain_shift (hN : 0 < N) : (constChain hN).shift = constChain hN :=
  chain_ext (fun k => rfl)

/-- Hence the Dirac law at the constant chain is shift-invariant: a genuine probability measure on
the segment chains, concentrated on `A`, invariant under the record shift. -/
theorem constChain_measurePreserving (hN : 0 < N) :
    MeasurePreserving (fun c : SwarmConcat.Chain N => c.shift)
      (Measure.dirac (constChain hN)) (Measure.dirac (constChain hN)) := by
  refine ⟨SwarmConcat.Chain.measurable_shift, ?_⟩
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply SwarmConcat.Chain.measurable_shift hs,
    Measure.dirac_apply' _ (SwarmConcat.Chain.measurable_shift hs), Measure.dirac_apply' _ hs]
  by_cases hmem : constChain hN ∈ s
  · have hpre : constChain hN ∈ (fun c : SwarmConcat.Chain N => c.shift) ⁻¹' s := by
      show (constChain hN).shift ∈ s
      rw [constChain_shift]
      exact hmem
    rw [Set.indicator_of_mem hpre, Set.indicator_of_mem hmem]
  · have hpre : ¬ (constChain hN ∈ (fun c : SwarmConcat.Chain N => c.shift) ⁻¹' s) := by
      show ¬ ((constChain hN).shift ∈ s)
      rw [constChain_shift]
      exact hmem
    rw [Set.indicator_of_notMem hpre, Set.indicator_of_notMem hmem]

/-- The Kac layer applies: the regeneration sum of `RegenConcat.lean` holds for this law. -/
theorem constChain_kac (hN : 0 < N) :
    (∑' k : ℕ, (Measure.dirac (constChain hN))
        (SwarmConcat.Chain.A ∩ KacFormula.noReturn
          (fun c : SwarmConcat.Chain N => c.shift) SwarmConcat.Chain.A k)) ≤ 1 :=
  SwarmConcat.kac_tsum_regeneration (Measure.dirac (constChain hN))
    (constChain_measurePreserving hN)

/-- **The separation.**  A shift-invariant chain law on the regeneration event — Kac holds — yet
`hstruct` fails whenever `π(F)·P(V) ≠ 1`.  So `hstruct` needs the fresh-law mass identity; the chain
topology, the a.e. compatibility and the Kac stationarity cannot supply it. -/
theorem constChain_not_hstruct (hN : 0 < N) (p : ℝ) (π : Measure (SwarmRec.RecState N m))
    (hne : π (SwarmRec.srSet N m) * (arrayMeasure N) {U : Array N |
        SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)} ≠ 1) :
    ¬ ∀ B : Set (ℕ → Fin N → ℤ), MeasurableSet B →
        (Measure.dirac (constChain hN)) ((fun c : SwarmConcat.Chain N => (fun n i => c.X n i)) ⁻¹'
            (SwarmFresh.strictPos (N := N) ∩ B))
          = π (SwarmRec.srSet N m) * (arrayMeasure N) {U : Array N |
              SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N) ∩ B} :=
  chain_hstruct_dirac_false p π (constChain_mem_A hN) hne

/-- The assembly does not manufacture randomness: a Dirac ambient law assembles to the Dirac law at
the assembled chain.  So an ambient law concentrated on one (however compatible) trajectory cannot
supply the paper's mass identity either. -/
theorem chainLaw_dirac (A : ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m) :
    chainLaw (Measure.dirac A) = Measure.dirac (chainOf A) := by
  refine Measure.ext fun s hs => ?_
  rw [chainLaw_apply _ hs, Measure.dirac_apply' A (measurable_chainOf hs),
    Measure.dirac_apply' _ hs]
  by_cases h : chainOf A ∈ s
  · rw [Set.indicator_of_mem h,
      Set.indicator_of_mem (show A ∈ chainOf ⁻¹' s from h)]
    simp
  · rw [Set.indicator_of_notMem h,
      Set.indicator_of_notMem (show ¬ (A ∈ chainOf ⁻¹' s) from h)]

/-- The regeneration mass of a Dirac ambient law. -/
theorem chainLaw_dirac_apply_A (A : ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m) :
    chainLaw (Measure.dirac A) SwarmConcat.Chain.A
      = if chainOf A ∈ SwarmConcat.Chain.A then 1 else 0 := by
  rw [chainLaw_dirac, Measure.dirac_apply' _ SwarmConcat.Chain.measurableSet_A,
    Set.indicator_apply]
  simp

/-- **A single model trajectory is not enough.**  For the Dirac law at a compatible trajectory whose
assembled chain lies in `A`, `hstruct` fails unless the paper's mass product is `1` — so the fresh
mass identity cannot be produced by any amount of trajectory-level compatibility, only by the law of
the initial record state together with the fresh future. -/
theorem chain_hstruct_dirac_ambient_false
    (A : ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m)
    (hA : chainOf A ∈ SwarmConcat.Chain.A) (p : ℝ) (π : Measure (SwarmRec.RecState N m))
    (hne : π (SwarmRec.srSet N m) * (arrayMeasure N) {U : Array N |
        SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)} ≠ 1) :
    ¬ ∀ B : Set (ℕ → Fin N → ℤ), MeasurableSet B →
        chainLaw (Measure.dirac A)
            ((fun c : SwarmConcat.Chain N => (fun n i => c.X n i)) ⁻¹'
              (SwarmFresh.strictPos (N := N) ∩ B))
          = π (SwarmRec.srSet N m) * (arrayMeasure N) {U : Array N |
              SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N) ∩ B} := by
  intro h
  have h2 : chainLaw (Measure.dirac A) SwarmConcat.Chain.A
      = π (SwarmRec.srSet N m) * (arrayMeasure N) {U : Array N |
          SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)} :=
    chain_hstruct_mass_necessary p π (chainLaw (Measure.dirac A)) h
  rw [chainLaw_dirac_apply_A, if_pos hA] at h2
  exact hne h2.symm

/-- **The concatenated path of the model chain is the model's own position path.**  Inside the
`k`-th record segment, at local time `n ≤ len k`, `Chain.X` is the level `k` plus the model's
relative position `relP` along the segment's actual jump path.  Together with `modelChain_seg` this
says the assembled chain carries the *whole* interacting-walk path, not merely its record skeleton. -/
theorem modelChain_X_eq_pos {hm : 1 ≤ m} (M : ModelTraj N m hm) {k n : ℕ} (hn : n ≤ M.len k)
    (i : Fin N) :
    (modelChain M).X ((modelChain M).cum k + n) i
      = (k : ℤ) + (SwarmSegKernel.relP (M.y k) (Record.extendPath (M.q k)) n) i := by
  have hk : 0 < M.len k := SwarmDHStruct.firstRecord_ne_zero (M.first k)
  have hseg : SwarmSegKernel.segOf (M.y k) (M.len k) (M.q k)
      = SwarmSegKernel.segOfFirst (M.y k) (M.len k) (M.q k) hk (M.first k) :=
    SwarmDHStruct.segOf_of_firstRecord hk (M.first k)
  have hp : ∀ j, (SwarmSegKernel.segOf (M.y k) (M.len k) (M.q k)).p j i
      = (SwarmSegKernel.relP (M.y k) (Record.extendPath (M.q k)) j) i := by
    intro j
    rw [hseg]
    rfl
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst hn0
    rw [Nat.add_zero]
    show (chainOf M.traj).X ((chainOf M.traj).cum k) i = _
    rw [chainOf_X_record M.trajCompat k i]
    exact congrArg ((k : ℤ) + ·) (hp 0)
  · have hdur : n ≤ (M.traj k).1.dur := by
      show n ≤ (SwarmSegKernel.segOf (M.y k) (M.len k) (M.q k)).dur
      rw [hseg]
      exact hn
    show (chainOf M.traj).X ((chainOf M.traj).cum k + n) i = _
    rw [chainOf_X_cum_add M.trajCompat hn0 hdur i]
    exact congrArg ((k : ℤ) + ·) (hp n)

/-! ## 8. The assembly commutes with the record shift: stationarity is inherited -/

/-- The shift of the ambient trajectory space (drop the first record step). -/
def trajShift (A : ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m) :
    ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m :=
  fun k => A (k + 1)

theorem measurable_trajShift : Measurable (trajShift (N := N) (m := m)) :=
  measurable_pi_iff.mpr fun k => measurable_pi_apply (k + 1)

/-- Compatibility is shift-invariant. -/
theorem trajCompat_shift {A : ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m}
    (h : TrajCompat A) : TrajCompat (trajShift A) := by
  intro k i
  exact h (k + 1) i

/-- **The assembly is shift-equivariant**: dropping the first record step of a compatible trajectory
is the same as shifting the assembled chain.  This is why a stationary trajectory law gives a
stationary chain law, with no extra input. -/
theorem chainOf_shift {A : ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m} (h : TrajCompat A) :
    chainOf (trajShift A) = (chainOf A).shift := by
  refine chain_ext fun k => ?_
  rw [chainOf_seg_of_compat (trajCompat_shift h) k, SwarmConcat.Chain.shift_seg,
    chainOf_seg_of_compat h (k + 1)]
  rfl

/-- **Stationarity is inherited.**  A shift-stationary ambient trajectory law which is compatible
almost surely pushes forward to a shift-stationary chain law — exactly the hypothesis
`MeasurePreserving Chain.shift ν ν` that the Kac layer of `RegenConcat.lean` consumes. -/
theorem chainLaw_measurePreserving_shift
    (μ : Measure (ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m)) [IsProbabilityMeasure μ]
    (hcompat : ∀ᵐ A ∂μ, TrajCompat A)
    (hstat : MeasurePreserving (trajShift (N := N) (m := m)) μ μ) :
    MeasurePreserving (fun c : SwarmConcat.Chain N => c.shift) (chainLaw μ) (chainLaw μ) := by
  refine ⟨SwarmConcat.Chain.measurable_shift, ?_⟩
  have heq : (fun c : SwarmConcat.Chain N => c.shift) ∘ chainOf
      =ᵐ[μ] chainOf ∘ (trajShift (N := N) (m := m)) := by
    filter_upwards [hcompat] with A hA
    show (chainOf A).shift = chainOf (trajShift A)
    exact (chainOf_shift hA).symm
  calc Measure.map (fun c : SwarmConcat.Chain N => c.shift) (chainLaw μ)
      = Measure.map ((fun c : SwarmConcat.Chain N => c.shift) ∘ chainOf) μ :=
        Measure.map_map SwarmConcat.Chain.measurable_shift measurable_chainOf
    _ = Measure.map (chainOf ∘ (trajShift (N := N) (m := m))) μ := Measure.map_congr heq
    _ = Measure.map chainOf (Measure.map (trajShift (N := N) (m := m)) μ) :=
        (Measure.map_map measurable_chainOf measurable_trajShift).symm
    _ = Measure.map chainOf μ := by rw [hstat.map_eq]
    _ = chainLaw μ := rfl

/-- **The Kac regeneration sum for the assembled chain law.**  Conditionally on nothing more than a
compatible, shift-stationary ambient trajectory law, the paper's Kac display `Σ_k P_π(A ∩ {D > k}) ≤ 1`
holds for the assembled chain law, with `D` the return time to the concrete regeneration event. -/
theorem chainLaw_kac_tsum
    (μ : Measure (ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m)) [IsProbabilityMeasure μ]
    (hcompat : ∀ᵐ A ∂μ, TrajCompat A)
    (hstat : MeasurePreserving (trajShift (N := N) (m := m)) μ μ) :
    (∑' k : ℕ, chainLaw μ
        (SwarmConcat.Chain.A ∩ KacFormula.noReturn
          (fun c : SwarmConcat.Chain N => c.shift) SwarmConcat.Chain.A k)) ≤ 1 :=
  SwarmConcat.kac_tsum_regeneration (chainLaw μ)
    (chainLaw_measurePreserving_shift μ hcompat hstat)

/-- **The necessary mass identity in per-state form.**  Combining the previous theorem with
`SwarmFreshState.mass_identity_srSet`: `hstruct` forces the chain's regeneration mass to equal the
`π`-average over the simultaneous-record states of the *array model's own* probability of staying
strictly above the record level.  That average is the fresh-law content; nothing in the chain
topology computes it. -/
theorem chain_hstruct_mass_necessary_stateMass {hm : 1 ≤ m} (p : ℝ)
    (π : Measure (SwarmRec.RecState N m)) (ν : Measure (SwarmConcat.Chain N))
    (h : ∀ B : Set (ℕ → Fin N → ℤ), MeasurableSet B →
        ν ((fun c : SwarmConcat.Chain N => (fun n i => c.X n i)) ⁻¹'
            (SwarmFresh.strictPos (N := N) ∩ B))
          = π (SwarmRec.srSet N m) * (arrayMeasure N) {U : Array N |
              SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N) ∩ B}) :
    ν SwarmConcat.Chain.A
      = ∫⁻ y in SwarmRec.srSet N m,
          (arrayMeasure N) {U : Array N |
            SwarmFreshState.FromV p m U (SwarmFreshState.walkStateOf y)} ∂π := by
  rw [chain_hstruct_mass_necessary p π ν h,
    ← SwarmFreshState.mass_identity_srSet (N := N) hm p π]

/-! ## 9. The whole bridge, end to end, on an explicit ambient law -/

/-- The constant ambient trajectory at a record state: every step is the all-right segment. -/
noncomputable def constTraj (hN : 0 < N) (y : SwarmRec.RecState N m) :
    ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m :=
  fun _ => (constSeg hN, y)

theorem constTraj_compat (hN : 0 < N) (y : SwarmRec.RecState N m) :
    TrajCompat (constTraj (N := N) (m := m) hN y) := by
  intro k i
  show ((1 : ℕ) : ℤ) = 1 + ((0 : ℕ) : ℤ)
  norm_num

theorem constTraj_shift (hN : 0 < N) (y : SwarmRec.RecState N m) :
    trajShift (constTraj (N := N) (m := m) hN y) = constTraj hN y := rfl

/-- The assembly of the constant ambient trajectory is the constant chain. -/
theorem chainOf_constTraj (hN : 0 < N) (y : SwarmRec.RecState N m) :
    chainOf (constTraj (N := N) (m := m) hN y) = constChain hN := by
  refine chain_ext fun k => ?_
  rw [chainOf_seg_of_compat (constTraj_compat hN y) k]
  rfl

/-- The Dirac law at the constant ambient trajectory is shift-stationary. -/
theorem constTraj_measurePreserving (hN : 0 < N) (y : SwarmRec.RecState N m) :
    MeasurePreserving (trajShift (N := N) (m := m))
      (Measure.dirac (constTraj (N := N) (m := m) hN y))
      (Measure.dirac (constTraj (N := N) (m := m) hN y)) := by
  refine ⟨measurable_trajShift, ?_⟩
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply measurable_trajShift hs,
    Measure.dirac_apply' _ (measurable_trajShift hs), Measure.dirac_apply' _ hs]
  by_cases hmem : constTraj (N := N) (m := m) hN y ∈ s
  · have hpre : constTraj (N := N) (m := m) hN y ∈ trajShift (N := N) (m := m) ⁻¹' s := by
      show trajShift (constTraj (N := N) (m := m) hN y) ∈ s
      rw [constTraj_shift]
      exact hmem
    rw [Set.indicator_of_mem hpre, Set.indicator_of_mem hmem]
  · have hpre : ¬ (constTraj (N := N) (m := m) hN y ∈ trajShift (N := N) (m := m) ⁻¹' s) := by
      show ¬ (trajShift (constTraj (N := N) (m := m) hN y) ∈ s)
      rw [constTraj_shift]
      exact hmem
    rw [Set.indicator_of_notMem hpre, Set.indicator_of_notMem hmem]

/-- **The separation, end to end, on an explicitly inhabited law.**  For any record state `y` and
`0 < N`, the Dirac law at the constant ambient trajectory is compatible almost surely and
shift-stationary, so the Kac regeneration sum holds for its assembled chain law; and that same
chain law violates the paper's `hstruct` as soon as `π(F)·P(V) ≠ 1`.  Every hypothesis of
`chainLaw_kac_tsum` is therefore inhabited, and `hstruct` is not implied by it. -/
theorem constTraj_kac_and_not_hstruct (hN : 0 < N) (y : SwarmRec.RecState N m) (p : ℝ)
    (π : Measure (SwarmRec.RecState N m))
    (hne : π (SwarmRec.srSet N m) * (arrayMeasure N) {U : Array N |
        SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)} ≠ 1) :
    ((∑' k : ℕ, chainLaw (Measure.dirac (constTraj (N := N) (m := m) hN y))
        (SwarmConcat.Chain.A ∩ KacFormula.noReturn
          (fun c : SwarmConcat.Chain N => c.shift) SwarmConcat.Chain.A k)) ≤ 1) ∧
      ¬ ∀ B : Set (ℕ → Fin N → ℤ), MeasurableSet B →
          chainLaw (Measure.dirac (constTraj (N := N) (m := m) hN y))
              ((fun c : SwarmConcat.Chain N => (fun n i => c.X n i)) ⁻¹'
                (SwarmFresh.strictPos (N := N) ∩ B))
            = π (SwarmRec.srSet N m) * (arrayMeasure N) {U : Array N |
                SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N) ∩ B} := by
  refine ⟨chainLaw_kac_tsum _
    (ae_trajCompat_dirac _ (constTraj_compat hN y))
    (constTraj_measurePreserving hN y), ?_⟩
  rw [chainLaw_dirac, chainOf_constTraj]
  exact constChain_not_hstruct hN p π hne

end SwarmChainAssemble
