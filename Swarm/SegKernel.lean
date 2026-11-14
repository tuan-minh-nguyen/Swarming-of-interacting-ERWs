/-
# The path-enriched record step of the actual record chain

The record chain of `main_1d_revised.tex` §3.1 stores, at each record time, the
half-distances below the record and the capped local times.  `areas/recordkernel` builds it as the
probability kernel `hitKKernel p hm` on `RecState N m`, the countable sum over first-record jump
paths `(k, q)` of the weights `hitW p q y` at the endpoints `out hm q y`.

This file *enriches* that kernel with the whole path of the record step, so that the paper's
finite path segment and the regeneration statistic can be read off the chain.
-/
import Swarm.MassOne
import Swarm.InfKernel
import Swarm.ChainWindow
import Swarm.RegenConcat

open MeasureTheory Set
open Classical
open scoped ENNReal
open SimJump ProbabilityTheory

namespace SwarmSegKernel

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {N m : ℕ}

/-! ## 1. The record state's positions -/

theorem ofRecState_pos (y : SwarmRec.RecState N m) (i : Fin N) :
    (Record.ofRecState y).pos i = -((2 * (y.val.1 i : ℕ)) : ℤ) := rfl

theorem ofRecState_pos_nonpos (y : SwarmRec.RecState N m) (i : Fin N) :
    (Record.ofRecState y).pos i ≤ 0 := by
  rw [ofRecState_pos]
  have h : (0 : ℤ) ≤ ((2 * (y.val.1 i : ℕ)) : ℤ) := Int.natCast_nonneg _
  omega

/-! ## 2. Position arrays relative to the record level -/

/-- The positions of the model's trajectory along the jump sequence `u`, started from the record
state `y`, relative to the current record level: at time `0` walker `i` sits at `-2 d_i`. -/
noncomputable def relP (y : SwarmRec.RecState N m) (u : ℕ → JumpVec N) : ℕ → Fin N → ℤ :=
  fun n i => (evolveFun (m := m) u n (Record.ofRecState y)).pos i

theorem relP_zero (y : SwarmRec.RecState N m) (u : ℕ → JumpVec N) (i : Fin N) :
    relP y u 0 i = (Record.ofRecState y).pos i := rfl

/-- The junk segment of a record state: every walker steps right at every step, for one step.
Its start array is the state's own position array, so the record compatibility
`SwarmConcat.Chain.compat` survives the junk branch. -/
noncomputable def dummySeg (y : SwarmRec.RecState N m) : SwarmConcat.Seg N where
  dur := 1
  dur_pos := Nat.one_pos
  p := fun n i => (Record.ofRecState y).pos i + (n : ℤ)
  start_le := by
    intro i
    show (Record.ofRecState y).pos i + ((0 : ℕ) : ℤ) ≤ 0
    rw [Nat.cast_zero, add_zero]
    exact ofRecState_pos_nonpos y i
  start_min := by
    obtain ⟨i, hi⟩ := y.property.1
    refine ⟨i, ?_⟩
    show (Record.ofRecState y).pos i + ((0 : ℕ) : ℤ) = 0
    rw [Nat.cast_zero, add_zero, ofRecState_pos]
    rw [hi]
    simp
  lt_one := by
    intro n hn i
    have hn0 : n = 0 := by omega
    subst hn0
    show (Record.ofRecState y).pos i + ((0 : ℕ) : ℤ) < 1
    rw [Nat.cast_zero, add_zero]
    have h := ofRecState_pos_nonpos y i
    omega
  step := by
    intro n hn i
    left
    show (Record.ofRecState y).pos i + ((n + 1 : ℕ) : ℤ)
      = (Record.ofRecState y).pos i + (n : ℤ) + 1
    push_cast
    ring

theorem dummySeg_p_zero (y : SwarmRec.RecState N m) (i : Fin N) :
    (dummySeg y).p 0 i = (Record.ofRecState y).pos i := by
  show (Record.ofRecState y).pos i + ((0 : ℕ) : ℤ) = _
  rw [Nat.cast_zero, add_zero]

/-! ## 3. The segment of a first-record path -/

/-- The `SwarmConcat.Seg N` of one record step, read off a first-record path `q` of length `k`
driven from the record state `y`.  All five fields are proved from the model's own deterministic
facts (`FirstRecord`, `step_pos`, the record state's constraints). -/
noncomputable def segOfFirst (y : SwarmRec.RecState N m) (k : ℕ) (q : Fin k → JumpVec N)
    (hk : 0 < k) (h : Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y)) :
    SwarmConcat.Seg N where
  dur := k
  dur_pos := hk
  p := relP y (Record.extendPath q)
  start_le := by
    intro i
    show relP y (Record.extendPath q) 0 i ≤ 0
    rw [relP_zero]
    exact ofRecState_pos_nonpos y i
  start_min := by
    obtain ⟨i, hi⟩ := y.property.1
    refine ⟨i, ?_⟩
    show relP y (Record.extendPath q) 0 i = 0
    rw [relP_zero, ofRecState_pos]
    rw [hi]
    simp
  lt_one := by
    intro n hn i
    have hle : relP y (Record.extendPath q) n i ≤ 0 := h.2 n hn i
    omega
  step := by
    intro n hn i
    have hs : relP y (Record.extendPath q) (n + 1) i
        = relP y (Record.extendPath q) n i +
            (if Record.extendPath q n i = true then (1 : ℤ) else -1) := by
      show (evolveFun (m := m) (Record.extendPath q) (n + 1) (Record.ofRecState y)).pos i = _
      rw [evolveFun_succ, step_pos]
      rfl
    rw [hs]
    split_ifs with hb
    · left; omega
    · right; omega

/-- The segment of an arbitrary finite jump path: the first-record branch, or the junk segment.
Off the first-record set the weight `hitW` is zero, so the junk branch never contributes mass. -/
noncomputable def segOf (y : SwarmRec.RecState N m) (k : ℕ) (q : Fin k → JumpVec N) :
    SwarmConcat.Seg N := by
  classical
  exact if h : 0 < k ∧ Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y) then
    segOfFirst y k q h.1 h.2
  else dummySeg y

/-- **The segment starts at the record state's own positions** — junk branch included.  This is
the identity that makes consecutive model segments satisfy `SwarmConcat.Chain.compat`. -/
theorem segOf_p_zero (y : SwarmRec.RecState N m) (k : ℕ) (q : Fin k → JumpVec N) (i : Fin N) :
    (segOf y k q).p 0 i = (Record.ofRecState y).pos i := by
  unfold segOf
  split_ifs with h
  · exact relP_zero y (Record.extendPath q) i
  · exact dummySeg_p_zero y i

/-- **The level-additive end position of a model segment.**  At the first-record time the walkers
sit at odd positions at most `1` and some walker sits at `1`; normalising subtracts `1` from every
position and records the half-distances.  Hence the end position in the segment's own coordinates
is `1` plus the new record state's start position. -/
theorem segOfFirst_p_dur (y : SwarmRec.RecState N m) (hm : 1 ≤ m) {k : ℕ}
    (q : Fin k → JumpVec N) (hk : 0 < k)
    (h : Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y)) (i : Fin N) :
    (segOfFirst y k q hk h).p k i
      = 1 + (Record.ofRecState (RecKernel.out hm q y)).pos i := by
  have hval : (RecKernel.out hm q y).val.1 i
      = Record.halfDist ((evolveFun (m := m) (Record.extendPath q) k
          (Record.ofRecState y)).pos i) := by
    rw [RecKernel.out_of_firstRecord hm q y h, RecKernel.recState_val]
    rfl
  have hpos : (Record.ofRecState (RecKernel.out hm q y)).pos i
      = -((2 * (Record.halfDist ((evolveFun (m := m) (Record.extendPath q) k
          (Record.ofRecState y)).pos i)) : ℕ) : ℤ) := by
    rw [ofRecState_pos, hval]
    push_cast
    ring
  have hstart : Record.RecordStart (Record.ofRecState y) := Record.ofRecState_recordStart y hm
  have hnorm : Record.RecordStart (Record.normalize (evolveFun (m := m) (Record.extendPath q) k
      (Record.ofRecState y))) :=
    Record.normalized_recordStart (Record.extendPath q) k (Record.ofRecState y) hstart hm h
  have hhd := Record.normalized_pos_halfDist_of_valid
    (s := evolveFun (m := m) (Record.extendPath q) k (Record.ofRecState y)) hnorm i
  have hstep : (Record.normalize (evolveFun (m := m) (Record.extendPath q) k
      (Record.ofRecState y))).pos i
      = (evolveFun (m := m) (Record.extendPath q) k (Record.ofRecState y)).pos i - 1 := rfl
  rw [hstep] at hhd
  show (evolveFun (m := m) (Record.extendPath q) k (Record.ofRecState y)).pos i = _
  rw [hpos]
  have hcast : ((2 * Record.halfDist ((evolveFun (m := m) (Record.extendPath q) k
      (Record.ofRecState y)).pos i) : ℕ) : ℤ)
      = 2 * (Record.halfDist ((evolveFun (m := m) (Record.extendPath q) k
      (Record.ofRecState y)).pos i) : ℤ) := by push_cast; ring
  rw [hcast] at hhd ⊢
  omega

/-- **The paper's level additivity for one record step** (`Chain.compat` shape): the end position
of segment `k`, translated by the level `k`, is the start position of the next segment translated
by the level `k+1`. -/
theorem compat_pair (y y' : SwarmRec.RecState N m) (hm : 1 ≤ m) {k : ℕ}
    (q : Fin k → JumpVec N) (hk : 0 < k)
    (h : Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y))
    (hy' : y' = RecKernel.out hm q y) (i : Fin N) :
    (k : ℤ) + (segOfFirst y k q hk h).p k i
      = ((k + 1 : ℕ) : ℤ) + (segOf y' k q).p 0 i := by
  rw [segOf_p_zero y' k q i, segOfFirst_p_dur y hm q hk h i, ← hy']
  push_cast
  ring

/-! ## 4. The path-enriched record kernel -/

/-- The record step enriched with its whole path: given the current record state `y`, the law of
the pair `(segment, next record state)`.  Same weights and same endpoints as the true record kernel
`hitKKernel`; only the path data has been added. -/
noncomputable def asegK (p : ℝ) (hm : 1 ≤ m) (y : SwarmRec.RecState N m) :
    Measure (SwarmConcat.Seg N × SwarmRec.RecState N m) :=
  Measure.sum (fun pq : (k : ℕ) × (Fin k → JumpVec N) =>
    ENNReal.ofReal (RecKernel.hitW p pq.2 y) •
      Measure.dirac (segOf y pq.1 pq.2, RecKernel.out hm pq.2 y))

theorem asegK_apply (p : ℝ) (hm : 1 ≤ m) (y : SwarmRec.RecState N m) {A : Set
    (SwarmConcat.Seg N × SwarmRec.RecState N m)} (hA : MeasurableSet A) :
    asegK p hm y A = ∑' pq : (k : ℕ) × (Fin k → JumpVec N),
      ENNReal.ofReal (RecKernel.hitW p pq.2 y) *
        (if (segOf y pq.1 pq.2, RecKernel.out hm pq.2 y) ∈ A then 1 else 0) := by
  classical
  rw [asegK, Measure.sum_apply _ hA]
  refine tsum_congr fun pq => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hA]
  simp only [Set.indicator_apply, Pi.one_apply]

/-- **The state marginal of the enriched step is the true record kernel.** -/
theorem asegK_snd (p : ℝ) (hm : 1 ≤ m) (y : SwarmRec.RecState N m) :
    (asegK p hm y).map Prod.snd = RecKernel.hitKKernel (N := N) (m := m) p hm y := by
  ext A hA
  rw [Measure.map_apply measurable_snd hA, asegK_apply p hm y (measurable_snd hA),
    RecKernel.hitKKernel_apply p hm y, RecKernel.hitKInf_apply p hm y hA]
  refine tsum_congr fun pq => ?_
  simp only [Set.mem_preimage]

theorem asegK_univ (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (y : SwarmRec.RecState N m) : (asegK p hm y) univ = 1 := by
  have hmarkov : IsMarkovKernel (RecKernel.hitKKernel (N := N) (m := m) p hm) :=
    RecKernel.isMarkovKernel_hitKKernel (N := N) (m := m) p hp hp1 hm
  haveI := hmarkov
  have hmap := congrArg (fun ν : Measure (SwarmRec.RecState N m) => ν univ) (asegK_snd p hm y)
  have h1 : ((asegK p hm y).map Prod.snd) univ = (asegK p hm y) univ := by
    rw [Measure.map_apply measurable_snd MeasurableSet.univ]
    simp
  rw [h1] at hmap
  rw [hmap, measure_univ]

theorem isProbabilityMeasure_asegK (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (y : SwarmRec.RecState N m) : IsProbabilityMeasure (asegK (N := N) (m := m) p hm y) :=
  ⟨asegK_univ p hm hp hp1 y⟩

/-- The segment marginal of the enriched step. -/
noncomputable def segK (p : ℝ) (hm : 1 ≤ m) (y : SwarmRec.RecState N m) :
    Measure (SwarmConcat.Seg N) :=
  (asegK p hm y).map Prod.fst

theorem segK_univ (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (y : SwarmRec.RecState N m) : (segK p hm y) univ = 1 := by
  rw [segK, Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ]
  exact asegK_univ p hm hp hp1 y

theorem isProbabilityMeasure_segK (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (y : SwarmRec.RecState N m) : IsProbabilityMeasure (segK (N := N) (m := m) p hm y) :=
  ⟨segK_univ p hm hp hp1 y⟩

/-! ## 5. Measurability in the record state -/

theorem measurable_seg_p_fun : Measurable (fun s : SwarmConcat.Seg N => s.p) := by
  have h1 : Measurable (fun s : SwarmConcat.Seg N => (s.dur, s.p)) :=
    measurable_iff_comap_le.mpr le_rfl
  exact measurable_snd.comp h1

theorem measurable_seg_iff {α : Type*} [MeasurableSpace α] {f : α → SwarmConcat.Seg N} :
    Measurable f ↔ Measurable (fun a => (f a).dur) ∧ Measurable (fun a => (f a).p) := by
  constructor
  · intro h
    exact ⟨SwarmConcat.measurable_seg_dur.comp h, measurable_seg_p_fun.comp h⟩
  · rintro ⟨h1, h2⟩
    have h3 : Measurable (fun a => ((f a).dur, (f a).p)) := h1.prodMk h2
    have h4 : MeasurableSpace.comap (fun a => ((f a).dur, (f a).p))
        (inferInstance : MeasurableSpace (ℕ × (ℕ → Fin N → ℤ))) ≤ ‹MeasurableSpace α› :=
      measurable_iff_comap_le.mp h3
    rw [measurable_iff_comap_le]
    show MeasurableSpace.comap f
      (MeasurableSpace.comap (fun s : SwarmConcat.Seg N => (s.dur, s.p)) inferInstance) ≤ _
    rw [MeasurableSpace.comap_comp]
    exact h4

theorem measurableSet_firstRecordSet (k : ℕ) (q : Fin k → JumpVec N) :
    MeasurableSet {y : SwarmRec.RecState N m |
      0 < k ∧ Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y)} := by
  by_cases hk : 0 < k
  · simpa [hk] using RecKernel.measurableSet_firstRecord (N := N) (m := m) k q
  · simp [hk]

theorem measurable_segOf (k : ℕ) (q : Fin k → JumpVec N) :
    Measurable (fun y : SwarmRec.RecState N m => segOf y k q) := by
  classical
  rw [measurable_seg_iff]
  have hP := measurableSet_firstRecordSet (N := N) (m := m) k q
  constructor
  · have heq : (fun y : SwarmRec.RecState N m => (segOf y k q).dur)
        = fun y => if 0 < k ∧ Record.FirstRecord (Record.extendPath q) k
            (Record.ofRecState y) then k else 1 := by
      funext y
      unfold segOf
      split_ifs <;> rfl
    rw [heq]
    exact Measurable.ite hP measurable_const measurable_const
  · have heq : (fun y : SwarmRec.RecState N m => (segOf y k q).p)
        = fun y => if 0 < k ∧ Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y)
            then relP y (Record.extendPath q)
            else fun n i => (Record.ofRecState y).pos i + (n : ℤ) := by
      funext y
      unfold segOf
      split_ifs <;> rfl
    rw [heq]
    refine Measurable.ite hP ?_ ?_
    · exact measurable_pi_lambda _ fun n => measurable_pi_lambda _ fun i =>
        (RecKernel.measurable_pos_eta (m := m) (Record.extendPath q) n).1 i
    · exact measurable_pi_lambda _ fun n => measurable_pi_lambda _ fun i =>
        ((RecKernel.measurable_pos_eta (m := m) (Record.extendPath q) 0).1 i).add_const _

/-- **The enriched step is a measurable function of the record state** — the property the kernel
construction needs. -/
theorem measurable_asegK (p : ℝ) (hm : 1 ≤ m) :
    Measurable (fun y : SwarmRec.RecState N m => asegK p hm y) := by
  classical
  refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
  have heq : (fun y => (asegK p hm y) A) = fun y =>
      ∑' pq : (k : ℕ) × (Fin k → JumpVec N),
        ENNReal.ofReal (RecKernel.hitW p pq.2 y) *
          (if (segOf y pq.1 pq.2, RecKernel.out hm pq.2 y) ∈ A then 1 else 0) := by
    funext y
    exact asegK_apply p hm y hA
  rw [heq]
  refine Measurable.tsum fun pq => ?_
  have hg : Measurable fun y : SwarmRec.RecState N m =>
      (segOf y pq.1 pq.2, RecKernel.out hm pq.2 y) :=
    (measurable_segOf pq.1 pq.2).prodMk (RecKernel.measurable_out hm pq.1 pq.2)
  have hset : MeasurableSet {y : SwarmRec.RecState N m |
      (segOf y pq.1 pq.2, RecKernel.out hm pq.2 y) ∈ A} := hg hA
  exact (RecKernel.measurable_hitW p pq.1 pq.2).ennreal_ofReal.mul
    (Measurable.ite hset measurable_const measurable_const)

/-! ## 6. The stationary enriched (segment) chain

The one-step law `asegK` has the true record kernel as its state marginal, so invariance of `π`
for `hitKKernel` makes the enriched step stationary.  This is the statistical content of the
paper's stationary "states and segments" sequence, at the level of one step and of finite windows.
-/

/-- The law of `(segment, next record state)` when the current record state has law `π`. -/
noncomputable def pairLaw (p : ℝ) (hm : 1 ≤ m) (π : Measure (SwarmRec.RecState N m)) :
    Measure (SwarmConcat.Seg N × SwarmRec.RecState N m) :=
  π.bind (fun y => asegK p hm y)

/-- The one-step transition of the enriched chain: re-draw the segment from the endpoint state. -/
noncomputable def pairK (p : ℝ) (hm : 1 ≤ m) :
    Kernel (SwarmConcat.Seg N × SwarmRec.RecState N m)
      (SwarmConcat.Seg N × SwarmRec.RecState N m) :=
  Kernel.mk (fun a => asegK p hm a.2) ((measurable_asegK (N := N) (m := m) p hm).comp
    measurable_snd)

theorem pairK_apply (p : ℝ) (hm : 1 ≤ m) (a : SwarmConcat.Seg N × SwarmRec.RecState N m) :
    pairK p hm a = asegK p hm a.2 := rfl

theorem isMarkovKernel_pairK (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) :
    IsMarkovKernel (pairK (N := N) (m := m) p hm) :=
  ⟨fun a => isProbabilityMeasure_asegK p hm hp hp1 a.2⟩

/-- Pushing a measure forward and then binding is the same as binding the composition. -/
theorem bind_map_eq {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure α} {f : α → β} (hf : Measurable f) {g : β → Measure γ} (hg : Measurable g) :
    (μ.map f).bind g = μ.bind (fun a => g (f a)) := by
  rw [← Measure.bind_dirac_eq_map (m := μ) hf]
  have hdir : Measurable (fun x : α => Measure.dirac (f x)) := Measure.measurable_dirac.comp hf
  rw [Measure.bind_bind hdir.aemeasurable hg.aemeasurable]
  simp only [Measure.dirac_bind hg]

theorem asegK_bind (p : ℝ) (hm : 1 ≤ m) (y : SwarmRec.RecState N m) :
    (asegK p hm y).bind (fun a => asegK p hm a.2)
      = (RecKernel.hitKKernel (N := N) (m := m) p hm y).bind (fun y' => asegK p hm y') := by
  rw [← bind_map_eq measurable_snd (measurable_asegK (N := N) (m := m) p hm), asegK_snd]

/-- **Stationarity of the enriched step** from invariance of `π` for the true record kernel. -/
theorem pairLaw_bind (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    {π : Measure (SwarmRec.RecState N m)} [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant (RecKernel.hitKKernel (N := N) (m := m) p hm) π) :
    (pairLaw p hm π).bind (fun a => asegK p hm a.2) = pairLaw p hm π := by
  have hmeas := measurable_asegK (N := N) (m := m) p hm
  have hg : Measurable (fun a : SwarmConcat.Seg N × SwarmRec.RecState N m =>
      asegK p hm a.2) := hmeas.comp measurable_snd
  have hκ : Measurable (fun y : SwarmRec.RecState N m =>
      RecKernel.hitKKernel (N := N) (m := m) p hm y) :=
    Kernel.measurable (RecKernel.hitKKernel (N := N) (m := m) p hm)
  calc (pairLaw p hm π).bind (fun a => asegK p hm a.2)
      = π.bind (fun y => (asegK p hm y).bind (fun a => asegK p hm a.2)) := by
        rw [pairLaw, Measure.bind_bind (m := π) hmeas.aemeasurable hg.aemeasurable]
    _ = π.bind (fun y =>
          (RecKernel.hitKKernel (N := N) (m := m) p hm y).bind (fun y' => asegK p hm y')) := by
        rw [show (fun y => (asegK p hm y).bind (fun a => asegK p hm a.2))
            = (fun y => (RecKernel.hitKKernel (N := N) (m := m) p hm y).bind
                (fun y' => asegK p hm y')) from funext fun y => asegK_bind p hm y]
    _ = (π.bind (RecKernel.hitKKernel (N := N) (m := m) p hm)).bind
          (fun y' => asegK p hm y') := by
        rw [← Measure.bind_bind (m := π) hκ.aemeasurable hmeas.aemeasurable]
    _ = pairLaw p hm π := by
        rw [Kernel.Invariant.def hinv, pairLaw]

/-- **The enriched chain is stationary** whenever `π` is invariant for the true record kernel. -/
theorem pairLaw_invariant (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    {π : Measure (SwarmRec.RecState N m)} [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant (RecKernel.hitKKernel (N := N) (m := m) p hm) π) :
    Kernel.Invariant (pairK (N := N) (m := m) p hm) (pairLaw p hm π) := by
  show (pairLaw p hm π).bind (pairK (N := N) (m := m) p hm) = pairLaw p hm π
  exact pairLaw_bind p hm hp hp1 hinv

/-- **The sequence of segments is shift-stationary in finite windows.**  The law of the segments
of the states `1, …, M` equals the law of the segments of the states `0, …, M-1`. -/
theorem chainStep_shift_seg (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    {π : Measure (SwarmRec.RecState N m)} [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant (RecKernel.hitKKernel (N := N) (m := m) p hm) π) (M : ℕ) :
    ((SwarmChain.chainStep (pairLaw p hm π) (pairK (N := N) (m := m) p hm) M).map
        (fun v : Fin (M + 1) → SwarmConcat.Seg N × SwarmRec.RecState N m =>
          fun i : Fin M => (v i.succ).1))
      = ((SwarmChain.chainVec (pairLaw p hm π) (pairK (N := N) (m := m) p hm) M).map
        (fun v : Fin M → SwarmConcat.Seg N × SwarmRec.RecState N m => fun i => (v i).1)) := by
  haveI hk : IsMarkovKernel (pairK (N := N) (m := m) p hm) :=
    isMarkovKernel_pairK (N := N) (m := m) p hm hp hp1
  haveI hprob : IsProbabilityMeasure (pairLaw p hm π) := by
    constructor
    rw [pairLaw, Measure.bind_apply MeasurableSet.univ
      (measurable_asegK (N := N) (m := m) p hm).aemeasurable]
    simp only [asegK_univ p hm hp hp1, lintegral_one, measure_univ]
  have h := SwarmChain.chainStep_shift (pairLaw p hm π) (pairK (N := N) (m := m) p hm)
    (pairLaw_invariant p hm hp hp1 hinv) M
  have hproj : Measurable (fun w : Fin M → SwarmConcat.Seg N × SwarmRec.RecState N m =>
      fun i => (w i).1) :=
    measurable_pi_lambda _ fun i => measurable_fst.comp (measurable_pi_apply i)
  calc ((SwarmChain.chainStep (pairLaw p hm π) (pairK (N := N) (m := m) p hm) M).map
        (fun v : Fin (M + 1) → SwarmConcat.Seg N × SwarmRec.RecState N m =>
          fun i : Fin M => (v i.succ).1))
      = ((SwarmChain.chainStep (pairLaw p hm π) (pairK (N := N) (m := m) p hm) M).map
          SwarmChain.tailF).map (fun w : Fin M → SwarmConcat.Seg N × SwarmRec.RecState N m =>
            fun i => (w i).1) := by
        rw [Measure.map_map hproj SwarmChain.measurable_tailF]
        rfl
    _ = _ := by rw [h]

/-- **On the paper's `F` the segment starts from the all-zero position array**: every walker is
exactly at the record level, so relative position `0` is occupied by all of them.  This is the
segment-level form of the source's "its capped local times at `0` are all `1`" starting point. -/
theorem segOf_p_zero_srSet {y : SwarmRec.RecState N m} (hy : y ∈ SwarmRec.srSet N m)
    (k : ℕ) (q : Fin k → JumpVec N) (i : Fin N) : (segOf y k q).p 0 i = 0 := by
  rw [segOf_p_zero, ofRecState_pos]
  have hle : y.val.1 i ≤ 0 := hy i
  have hz : y.val.1 i = 0 := Nat.le_zero.mp hle
  rw [hz]
  simp

end SwarmSegKernel
