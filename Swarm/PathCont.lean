/-
# Continuity of the stopped-record path data

Continuity half of the stopped record kernel `SimJump.RecKernel.hitKernel` of
`Swarm/StoppedKernel.lean`.  `Measurable.lean` proves measurability in the starting
record state by structural induction; here the same objects are shown to be *continuous* in the
starting record state, in the product topology induced by the position and capped local-time
coordinates (the topology introduced locally in `Swarm/Continuity.lean`).

Two structural facts are used, neither of them an assumption on the model:
positions are `ℤ`-valued, so every position coordinate is locally constant in the starting state,
and every capped local-time coordinate depends on the starting profile through finitely many
coordinates, hence is again locally constant in the starting state.  Continuity into the
function-space factor of the ambient record space is then checked coordinatewise.

Main results: `continuous_step`, `continuous_evolveFun`, `continuous_pathW`,
`continuous_hitW`, `continuous_out`.
-/
import Swarm.StoppedKernel
import Mathlib.Topology.LocallyConstant.Basic
import Swarm.Continuity

open MeasureTheory ProbabilityTheory Topology
open scoped ENNReal

namespace SimJump.RecKernel

open SimJump
open SwarmRec

variable {N m : ℕ}

/-- The topology on `SimJump.State` used by `Swarm/Continuity.lean`: the product
topology induced by the position and capped local-time coordinates.  Declared local, so that this
file does not change the model's global topological structure. -/
local instance stateTopology : TopologicalSpace (SimJump.State N m) :=
  TopologicalSpace.induced (fun s : SimJump.State N m => (s.pos, s.eta)) inferInstance

/-! ### General continuity lemmas -/

section General

variable {Y : Type*} [TopologicalSpace Y] {Z : Type*} [TopologicalSpace Z]

/-- A locally constant function pulls back any set to a clopen set. -/
theorem isClopen_preimage_of_isLocallyConstant {ι : Type*} {f : Y → ι}
    (hf : IsLocallyConstant f) (s : Set ι) : IsClopen (f ⁻¹' s) :=
  ⟨⟨by simpa using hf sᶜ⟩, hf s⟩

/-- An `if`-then-else with clopen test and continuous branches is continuous. -/
theorem continuous_ite_of_isClopen {p : Y → Prop} [DecidablePred p] (hp : IsClopen {y | p y})
    {f g : Y → Z} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun y => if p y then f y else g y := by
  have h : ContinuousOn (fun y => if p y then f y else g y) (Set.univ : Set Y) := by
    refine ContinuousOn.if (s := Set.univ) ?_ ?_ ?_
    · intro a ha
      rw [hp.frontier_eq] at ha
      exact absurd ha.2 (Set.notMem_empty a)
    · exact hf.continuousOn.mono (Set.inter_subset_left)
    · exact hg.continuousOn.mono (Set.inter_subset_left)
  simpa using h

/-- A predicate that is eventually constant near every point has a clopen truth set. -/
theorem isClopen_of_eventually_const {p : Y → Prop}
    (hp : ∀ y, ∀ᶠ z in 𝓝 y, (p z ↔ p y)) : IsClopen {y | p y} := by
  have hopen : IsOpen {y | p y} := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    exact (hp y).mono fun z hz => hz.mpr hy
  have hclosed : IsOpen {y | p y}ᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    exact (hp y).mono fun z hz hc => hy (hz.mp hc)
  exact ⟨⟨hclosed⟩, hopen⟩

/-- Continuity of an `if`-then-else whose test is eventually constant near every point. -/
theorem continuous_ite_of_eventually_const {p : Y → Prop} [DecidablePred p]
    (hp : ∀ y, ∀ᶠ z in 𝓝 y, (p z ↔ p y)) {f g : Y → Z}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous fun y => if p y then f y else g y :=
  continuous_ite_of_isClopen (isClopen_of_eventually_const hp) hf hg

/-- A continuous map into a discrete space is locally constant. -/
theorem isLocallyConstant_of_continuous {ι : Type*} [TopologicalSpace ι] [DiscreteTopology ι]
    {g : Y → ι} (hg : Continuous g) : IsLocallyConstant g :=
  (IsLocallyConstant.iff_continuous g).2 hg

/-- Evaluation of a continuous family at a locally constant index is continuous. -/
theorem continuous_comp_eval_of_isLocallyConstant {ι : Type*} [TopologicalSpace ι]
    {β : Type*} [TopologicalSpace β] {φ : Y → ι → β} (hφ : Continuous φ) {p : Y → ι}
    (hp : IsLocallyConstant p) : Continuous fun y => φ y (p y) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hfix : ContinuousAt (fun z => φ z (p y)) y :=
    ((continuous_apply (p y)).comp hφ).continuousAt
  refine ContinuousAt.congr hfix ?_
  filter_upwards [hp.eventually_eq y] with z hz
  rw [hz]

/-- A map into `Fin n` is continuous as soon as its `ℕ`-valued unfold is, because `Fin n` carries
the discrete topology and the unfold is then locally constant. -/
theorem continuous_fin_of_continuous_coe {n : ℕ} {f : Y → Fin n}
    (hf : Continuous fun y => (f y : ℕ)) : Continuous f := by
  have hlc : IsLocallyConstant fun y => (f y : ℕ) :=
    (IsLocallyConstant.iff_continuous _).2 hf
  refine (IsLocallyConstant.iff_continuous _).1 ?_
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun y => ?_
  filter_upwards [hlc.eventually_eq y] with z hz
  exact Fin.ext hz

end General

/-! ### Coordinates of the chain state -/

theorem isLocallyConstant_pos (i : Fin N) :
    IsLocallyConstant fun s : SimJump.State N m => s.pos i :=
  isLocallyConstant_of_continuous (ι := ℤ) ((continuous_apply i).comp Record.cont_pos)

theorem continuous_eta_coord (i : Fin N) (x : ℤ) :
    Continuous fun s : SimJump.State N m => s.eta i x :=
  (continuous_apply x).comp ((continuous_apply i).comp Record.cont_eta)

theorem continuous_eta (i : Fin N) :
    Continuous fun s : SimJump.State N m => s.eta i :=
  (continuous_apply i).comp Record.cont_eta

theorem isLocallyConstant_stepPos (v : JumpVec N) (i : Fin N) :
    IsLocallyConstant fun s : SimJump.State N m => stepPos s v i :=
  (isLocallyConstant_pos i).comp (fun z : ℤ => z + (if v i = true then (1 : ℤ) else -1))

/-- The excitation count `otherVisits` is continuous in the state. -/
theorem continuous_otherVisits (i : Fin N) :
    Continuous fun s : SimJump.State N m => otherVisits s i := by
  unfold otherVisits
  refine continuous_finsetSum _ fun j _ => ?_
  exact continuous_comp_eval_of_isLocallyConstant (φ := fun s : SimJump.State N m => s.eta j)
    (p := fun s => s.pos i) (continuous_eta j) (isLocallyConstant_pos i)

theorem continuous_qRight (p : ℝ) (i : Fin N) :
    Continuous fun s : SimJump.State N m => qRight p m s i := by
  have hlc : IsLocallyConstant fun s : SimJump.State N m => otherVisits s i :=
    isLocallyConstant_of_continuous (ι := ℕ) (continuous_otherVisits i)
  have htest : IsClopen {s : SimJump.State N m | m ≤ otherVisits s i} :=
    isClopen_preimage_of_isLocallyConstant hlc {a : ℕ | m ≤ a}
  unfold qRight
  exact continuous_ite_of_isClopen htest continuous_const continuous_const

theorem continuous_stepFactor (p : ℝ) (i : Fin N) (b : Bool) :
    Continuous fun s : SimJump.State N m => stepFactor p m s i b := by
  unfold stepFactor
  by_cases h : b = true
  · simp only [h, if_true]
    exact continuous_qRight p i
  · simp only [h, if_false]
    exact continuous_const.sub (continuous_qRight p i)

/-- The one-step joint weight is continuous in the state. -/
theorem continuous_stepW (p : ℝ) (v : JumpVec N) :
    Continuous fun s : SimJump.State N m => stepW p m s v := by
  simp only [stepW_eq_prod]
  exact continuous_finsetProd _ fun i _ => continuous_stepFactor p i (v i)

/-- **One step of the capped-step chain is continuous in the state.** -/
theorem continuous_step (v : JumpVec N) :
    Continuous fun s : SimJump.State N m => step m s v := by
  refine continuous_induced_rng.2 (Continuous.prodMk ?_ ?_)
  · refine continuous_pi fun i => ?_
    have h : (fun s : SimJump.State N m => (step m s v).pos i) =
        fun s => s.pos i + (if v i = true then (1 : ℤ) else -1) := by
      funext s
      rw [step_pos]
      rfl
    rw [h]
    exact ((continuous_apply i).comp Record.cont_pos).add continuous_const
  · refine continuous_pi fun i => continuous_pi fun x => ?_
    have h : (fun s : SimJump.State N m => (step m s v).eta i x) =
        fun s => if x = stepPos s v i then cap m (s.eta i x + 1) else s.eta i x := by
      funext s
      rfl
    rw [h]
    have htest : ∀ s : SimJump.State N m,
        ∀ᶠ z in 𝓝 s, ((x = stepPos z v i) ↔ (x = stepPos s v i)) := by
      intro s
      exact (isLocallyConstant_stepPos v i).eventually_eq s |>.mono fun z hz => by rw [hz]
    refine continuous_ite_of_eventually_const htest
      (f := fun s => cap m (s.eta i x + 1)) (g := fun s => s.eta i x) ?_
      (continuous_eta_coord i x)
    have hlc : IsLocallyConstant fun s : SimJump.State N m => cap m (s.eta i x + 1) :=
      (isLocallyConstant_of_continuous (ι := ℕ) (continuous_eta_coord i x)).comp
        (fun a : ℕ => cap m (a + 1))
    exact hlc.continuous

/-! ### Iterated steps and path weights -/

theorem continuous_evolveFun (u : ℕ → JumpVec N) (k : ℕ) :
    Continuous fun y : RecState N m => evolveFun (m := m) u k (Record.ofRecState y) := by
  induction k with
  | zero => exact Record.continuous_ofRecState
  | succ k ih =>
      have h : (fun y : RecState N m => evolveFun (m := m) u (k + 1) (Record.ofRecState y)) =
          fun y => step m (evolveFun (m := m) u k (Record.ofRecState y)) (u k) := by
        funext y
        rw [evolveFun_succ]
      rw [h]
      exact (continuous_step (u k)).comp ih

theorem continuous_pos_evolveFun (u : ℕ → JumpVec N) (k : ℕ) (i : Fin N) :
    Continuous fun y : RecState N m =>
      (evolveFun (m := m) u k (Record.ofRecState y)).pos i :=
  ((continuous_apply i).comp Record.cont_pos).comp (continuous_evolveFun u k)

theorem continuous_eta_evolveFun (u : ℕ → JumpVec N) (k : ℕ) (i : Fin N) (x : ℤ) :
    Continuous fun y : RecState N m =>
      (evolveFun (m := m) u k (Record.ofRecState y)).eta i x :=
  (continuous_eta_coord i x).comp (continuous_evolveFun u k)

theorem continuous_pathWFun (p : ℝ) (u : ℕ → JumpVec N) (k : ℕ) :
    Continuous fun y : RecState N m => pathWFun p u k (Record.ofRecState y) := by
  induction k with
  | zero => exact continuous_const
  | succ k ih =>
      have h : (fun y : RecState N m => pathWFun p u (k + 1) (Record.ofRecState y)) =
          fun y => pathWFun p u k (Record.ofRecState y) *
            stepW p m (evolveFun (m := m) u k (Record.ofRecState y)) (u k) := by
        funext y
        rw [pathWFun_succ]
      rw [h]
      exact ih.mul ((continuous_stepW p (u k)).comp (continuous_evolveFun u k))

theorem continuous_pathW (p : ℝ) (k : ℕ) (q : Fin k → JumpVec N) :
    Continuous fun y : RecState N m => pathW p k q (Record.ofRecState y) := by
  classical
  let u : ℕ → JumpVec N := fun n => if h : n < k then q ⟨n, h⟩ else fun _ => true
  have hqi : (fun i : Fin k => u i) = q := by
    funext i
    have hi : u (i : ℕ) = q ⟨(i : ℕ), i.isLt⟩ := by
      simp only [u, dif_pos i.isLt]
    rw [hi]
  have h : (fun y : RecState N m => pathW p k q (Record.ofRecState y)) =
      (fun y => pathWFun p u k (Record.ofRecState y)) := by
    funext y
    rw [← hqi, pathW_eq_pathWFun]
  rw [h]
  exact continuous_pathWFun p u k

/-! ### The first-record event as a clopen condition -/

/-- All positions up to time `k`, as a vector depending on the starting record state. -/
noncomputable def posVec (u : ℕ → JumpVec N) (k : ℕ) :
    RecState N m → (Fin (k + 1) → Fin N → ℤ) :=
  fun y t i => (evolveFun (m := m) u (t : ℕ) (Record.ofRecState y)).pos i

theorem continuous_posVec (u : ℕ → JumpVec N) (k : ℕ) :
    Continuous (posVec (m := m) u k) :=
  continuous_pi fun t => continuous_pi fun i => continuous_pos_evolveFun u (t : ℕ) i

/-- The first-record condition, read off the position vector. -/
def firstRecordVec (k : ℕ) (v : Fin (k + 1) → Fin N → ℤ) : Prop :=
  (∃ i : Fin N, v (Fin.last k) i = 1) ∧ ∀ t : Fin k, ∀ i : Fin N, v (Fin.castSucc t) i ≤ 0

theorem firstRecord_iff_posVec (u : ℕ → JumpVec N) (k : ℕ) (y : RecState N m) :
    Record.FirstRecord u k (Record.ofRecState y) ↔
      firstRecordVec k (posVec (m := m) u k y) := by
  simp only [Record.FirstRecord, firstRecordVec, posVec, Fin.val_last, Fin.val_castSucc]
  constructor
  · rintro ⟨⟨i, hi⟩, hprev⟩
    exact ⟨⟨i, hi⟩, fun t i => hprev t t.isLt i⟩
  · rintro ⟨⟨i, hi⟩, hprev⟩
    exact ⟨⟨i, hi⟩, fun t ht i => hprev ⟨t, ht⟩ i⟩

theorem isClopen_firstRecord (k : ℕ) (q : Fin k → JumpVec N) :
    IsClopen {y : RecState N m |
      Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y)} := by
  have hlc : IsLocallyConstant (posVec (m := m) (Record.extendPath q) k) :=
    isLocallyConstant_of_continuous (ι := Fin (k + 1) → Fin N → ℤ)
      (continuous_posVec _ k)
  have h := isClopen_preimage_of_isLocallyConstant hlc
    {v : Fin (k + 1) → Fin N → ℤ | firstRecordVec k v}
  have hset : {y : RecState N m |
        Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y)} =
      posVec (m := m) (Record.extendPath q) k ⁻¹'
        {v : Fin (k + 1) → Fin N → ℤ | firstRecordVec k v} := by
    ext y
    exact firstRecord_iff_posVec _ _ y
  rw [hset]
  exact h

/-! ### The stopped record map -/

theorem continuous_hitW (p : ℝ) (k : ℕ) (q : Fin k → JumpVec N) :
    Continuous fun y : RecState N m => hitW p q y := by
  classical
  have hfun : (fun y : RecState N m => hitW p q y) =
      fun y => if Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y)
        then pathW p k q (Record.ofRecState y) else 0 := rfl
  rw [hfun]
  exact continuous_ite_of_isClopen (isClopen_firstRecord k q) (continuous_pathW p k q)
    continuous_const

/-- The normalized ambient record coordinates of the state reached along `u` at time `k`. -/
theorem continuous_toRecordAmb_evolveFun (u : ℕ → JumpVec N) (k : ℕ) :
    Continuous fun y : RecState N m =>
      Record.toRecordAmb (evolveFun (m := m) u k (Record.ofRecState y)) := by
  refine Continuous.prodMk ?_ ?_
  · refine continuous_pi fun i => ?_
    exact ((isLocallyConstant_of_continuous (ι := ℤ) (continuous_pos_evolveFun u k i)).comp
      Record.halfDist).continuous
  · refine continuous_pi fun i => continuous_pi fun x => ?_
    have hnat : Continuous fun y : RecState N m =>
        (evolveFun (m := m) u k (Record.ofRecState y)).eta i (x + 1) :=
      continuous_eta_evolveFun u k i (x + 1)
    refine continuous_fin_of_continuous_coe (f := fun y : RecState N m =>
      ⟨(evolveFun (m := m) u k (Record.ofRecState y)).eta i (x + 1),
        Nat.lt_succ_of_le ((evolveFun (m := m) u k (Record.ofRecState y)).hcap i (x + 1))⟩) ?_
    simpa using hnat

theorem continuous_out (hm : 1 ≤ m) (k : ℕ) (q : Fin k → JumpVec N) :
    Continuous fun y : RecState N m => out hm q y := by
  classical
  refine continuous_induced_rng.2 ?_
  have hcomp : (Subtype.val ∘ fun y : RecState N m => out hm q y) =
      fun y => (out hm q y).val := rfl
  rw [hcomp]
  have hval : (fun y : RecState N m => (out hm q y).val) =
      fun y => if Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y)
        then Record.toRecordAmb (evolveFun (m := m) (Record.extendPath q) k
          (Record.ofRecState y))
        else y.val := by
    funext y
    by_cases h : Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y)
    · rw [out_of_firstRecord hm q y h, recState_val, if_pos h]
    · rw [out_of_not_firstRecord hm q y h, if_neg h]
  rw [hval]
  refine continuous_ite_of_isClopen (p := fun y => Record.FirstRecord (Record.extendPath q) k
    (Record.ofRecState y)) (isClopen_firstRecord k q) ?_ continuous_subtype_val
  exact continuous_toRecordAmb_evolveFun (Record.extendPath q) k

end SimJump.RecKernel


