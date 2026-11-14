/-
# the first-segment path-mass identity at a simultaneous record

The paper's `(freshlaw)` at a regeneration time has two halves.

* *Translation* — after a simultaneous record the translated future is the fresh path.  This is
  `SwarmRestart.restart_agreement` / `relFuture_eq` in the reviewed tree.
* *Independence* — the future is independent of the past, with the fresh law.  At the level of the
  i.i.d. array this is `SwarmPast`/`FreshPast`'s factorisation; the array block structure is
  `SwarmRestart.cylinder_mul` and the level shift is measure preserving and injective
  (`SwarmRestart.shiftCoord`, `measurePreserving_levelShift`).

What the record chain consumes is neither of those objects directly: the one-step enriched kernel
`SwarmSegKernel.asegK p hm y` is a countable sum over first-record *jump words* `q` with weights
`RecKernel.hitW p q y = pathW p k q (ofRecState y)`.  This file proves, at that interface,

* `pathW_eq_fresh` / `hitW_eq_fresh` — the mass of a first-record word that keeps every walker
  strictly above the record level (`SwarmFreshPos.PosSeqFin`) is *the same at every fresh start*,
  in particular the fresh chain's own word mass.  This is the finite-prefix path-mass identity
  between the record chain's segment weight and the fresh path weight;
* `segOf_eq_of_srSet` — the segment read off such a word is literally the same
  `SwarmConcat.Seg` from every simultaneous-record start state `y ∈ srSet` (positions of a word are
  state independent, and on `srSet` the start positions are all `0`);
* `segKpos_eq_of_srSet` — consequently the strict-positivity part `segKpos` of the first-segment
  law is a *single* measure on `Seg N`, independent of the record state `y ∈ srSet`, with no
  invariant law, no stationary system and no initial distribution assumed.

Scope.  `srSet` membership is an honest typed parameter, exactly as the paper's "for an evolution
started from any state in `F`".  Nothing here asserts `hstruct`, an invariant law `π`, regeneration,
`(ED)` or a speed; the residual ledger is in `LEDGER.md`.  In particular the endpoint component
`RecKernel.out hm q y` of the atom is *not* claimed to be state independent: the record state keeps
the local times at the sites strictly below the level, which the future never reads but which do
depend on the past.
-/
import Swarm.SegKernel
import Swarm.FreshPos

open MeasureTheory Set
open Classical
open scoped ENNReal
open SimJump ProbabilityTheory

namespace SwarmFreshCyl

open SimJump.Record SwarmRec

variable {N m : ℕ}

/-! ## 0. The two word-continuation conventions agree on the first `k` jumps -/

theorem seqOf_eq_extendPath {k : ℕ} (q : Fin k → JumpVec N) {j : ℕ} (hj : j < k) :
    SwarmFreshPos.seqOf q j = Record.extendPath q j := by
  simp only [SwarmFreshPos.seqOf, dif_pos hj, Record.extendPath]

theorem posAt_seqOf_eq_extendPath {k : ℕ} (q : Fin k → JumpVec N) :
    ∀ (n : ℕ) (i : Fin N), n ≤ k →
      SwarmFreshPos.posAt (SwarmFreshPos.seqOf q) n i
        = SwarmFreshPos.posAt (Record.extendPath q) n i := by
  intro n i hn
  simp only [SwarmFreshPos.posAt]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [seqOf_eq_extendPath q (by omega)]

/-- `PosSeqFin` read with the record chain's own continuation `Record.extendPath`. -/
theorem posWord_iff {k : ℕ} (q : Fin k → JumpVec N) :
    SwarmFreshPos.PosSeqFin (N := N) q ↔
      ∀ n, 1 ≤ n → n ≤ k → ∀ i, 0 < SwarmFreshPos.posAt (Record.extendPath q) n i := by
  rw [SwarmFreshPos.posSeqFin_iff, SwarmFreshPos.PosSeq]
  constructor
  · intro h n h1 h2 i
    rw [← posAt_seqOf_eq_extendPath q n i h2]
    exact h n h1 h2 i
  · intro h n h1 h2 i
    rw [posAt_seqOf_eq_extendPath q n i h2]
    exact h n h1 h2 i

/-! ## 1. A record state in `srSet` sits at the record level -/

theorem ofRecState_pos_eq_zero {y : RecState N m} (hy : y ∈ srSet N m) (i : Fin N) :
    (Record.ofRecState y).pos i = 0 := by
  rw [SwarmSegKernel.ofRecState_pos]
  have hd : y.val.1 i = 0 := Nat.le_zero.mp (hy i)
  rw [hd]
  simp

/-- The relative position path of a record state in `srSet` is the net displacement of the jump
word alone: it does not depend on the state. -/
theorem relP_eq_posAt {y : RecState N m} (hy : y ∈ srSet N m) (u : ℕ → JumpVec N) (n : ℕ)
    (i : Fin N) : SwarmSegKernel.relP y u n i = SwarmFreshPos.posAt u n i := by
  rw [SwarmSegKernel.relP, SwarmFreshPos.pos_evolveFun, ofRecState_pos_eq_zero hy i, zero_add]

/-- On `srSet` the first-record condition is a condition on the jump word alone. -/
theorem firstRecord_iff_posAt {y : RecState N m} (hy : y ∈ srSet N m) (u : ℕ → JumpVec N)
    (k : ℕ) :
    Record.FirstRecord u k (Record.ofRecState y) ↔
      (∃ i, SwarmFreshPos.posAt u k i = 1) ∧
        ∀ t < k, ∀ i, SwarmFreshPos.posAt u t i ≤ 0 := by
  have hp : ∀ i : Fin N, (Record.ofRecState y).pos i = 0 := ofRecState_pos_eq_zero hy
  constructor
  · rintro ⟨⟨i, hi⟩, hlt⟩
    refine ⟨⟨i, ?_⟩, fun t ht i => ?_⟩
    · rw [SwarmFreshPos.pos_evolveFun, hp i, zero_add] at hi
      exact hi
    · have := hlt t ht i
      rw [SwarmFreshPos.pos_evolveFun, hp i, zero_add] at this
      exact this
  · rintro ⟨⟨i, hi⟩, hlt⟩
    refine ⟨⟨i, ?_⟩, fun t ht i => ?_⟩
    · rw [SwarmFreshPos.pos_evolveFun, hp i, zero_add]
      exact hi
    · rw [SwarmFreshPos.pos_evolveFun, hp i, zero_add]
      exact hlt t ht i

theorem firstRecord_ofRecState_iff {y y' : RecState N m} (hy : y ∈ srSet N m)
    (hy' : y' ∈ srSet N m) (u : ℕ → JumpVec N) (k : ℕ) :
    Record.FirstRecord u k (Record.ofRecState y) ↔
      Record.FirstRecord u k (Record.ofRecState y') := by
  rw [firstRecord_iff_posAt hy u k, firstRecord_iff_posAt hy' u k]

/-! ## 2. The path weight of a finite word, read on the chain's continuation -/

theorem pathW_eq_pathWFun_extendPath (p : ℝ) (k : ℕ) (q : Fin k → JumpVec N)
    (s : State N m) :
    pathW p k q s = pathWFun p (Record.extendPath q) k s := by
  rw [← SimJump.pathW_eq_pathWFun p (Record.extendPath q) k s]
  congr 1
  funext i
  simp only [Record.extendPath, dif_pos i.isLt]

/-- **The word weight is the same at every fresh start.**  This is the finite-prefix form of the
paper's "for an evolution started from any state in `F` the identity at `d = t = 0` holds": along a
word that keeps every walker strictly above the level at times `1, …, k`, the past local times at
and below the level are never read. -/
theorem pathW_eq_fresh (p : ℝ) {s s' : State N m} (hs : SwarmFreshPos.FreshStart s)
    (hs' : SwarmFreshPos.FreshStart s') {k : ℕ} (q : Fin k → JumpVec N)
    (hq : SwarmFreshPos.PosSeqFin (N := N) q) : pathW p k q s = pathW p k q s' := by
  have hpos := (posWord_iff q).mp hq
  rw [pathW_eq_pathWFun_extendPath p k q s, pathW_eq_pathWFun_extendPath p k q s']
  exact SwarmFreshPos.pathWFun_eq p hs hs' (Record.extendPath q) k hpos

/-- **The first-segment mass is state independent on `srSet`**, and equals the fresh word mass. -/
theorem hitW_eq_of_srSet {p : ℝ} (hm : 1 ≤ m) {y y' : RecState N m} (hy : y ∈ srSet N m)
    (hy' : y' ∈ srSet N m) {k : ℕ} (q : Fin k → JumpVec N)
    (hq : SwarmFreshPos.PosSeqFin (N := N) q) :
    RecKernel.hitW p q y = RecKernel.hitW p q y' := by
  have hiff := firstRecord_ofRecState_iff hy hy' (Record.extendPath q) k
  by_cases hfr : Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y)
  · rw [RecKernel.hitW_of_firstRecord p q y hfr,
      RecKernel.hitW_of_firstRecord p q y' (hiff.mp hfr)]
    exact pathW_eq_fresh p (SwarmFreshPos.freshStart_ofRecState hy hm)
      (SwarmFreshPos.freshStart_ofRecState hy' hm) q hq
  · rw [RecKernel.hitW_of_not_firstRecord p q y hfr,
      RecKernel.hitW_of_not_firstRecord p q y' (fun h => hfr (hiff.mpr h))]

/-- **The first-segment path-mass identity.**  For a first-record word that keeps every walker
strictly above the record level, the atom weight of the enriched record step at any simultaneous
record state is the fresh chain's word mass `pathW p k q s`, for *every* fresh start `s` — in
particular for the canonical one.  Nothing about the past state enters. -/
theorem hitW_eq_fresh {p : ℝ} (hm : 1 ≤ m) {y : RecState N m} (hy : y ∈ srSet N m)
    {s : State N m} (hs : SwarmFreshPos.FreshStart s) {k : ℕ} (q : Fin k → JumpVec N)
    (hfr : Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y))
    (hq : SwarmFreshPos.PosSeqFin (N := N) q) :
    RecKernel.hitW p q y = pathW p k q s := by
  rw [RecKernel.hitW_of_firstRecord p q y hfr]
  exact pathW_eq_fresh p (SwarmFreshPos.freshStart_ofRecState hy hm) hs q hq

/-! ## 3. The segment of a strict record step is the same at every state of `srSet` -/

theorem segOf_dur_of_firstRecord {y : RecState N m} {k : ℕ} (hk : 0 < k)
    (q : Fin k → JumpVec N) (hfr : Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y)) :
    (SwarmSegKernel.segOf y k q).dur = k := by
  rw [SwarmSegKernel.segOf, dif_pos ⟨hk, hfr⟩]
  rfl

theorem segOf_p_of_firstRecord {y : RecState N m} {k : ℕ} (hk : 0 < k)
    (q : Fin k → JumpVec N) (hfr : Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y)) :
    (SwarmSegKernel.segOf y k q).p = SwarmSegKernel.relP y (Record.extendPath q) := by
  rw [SwarmSegKernel.segOf, dif_pos ⟨hk, hfr⟩]
  rfl

/-- **The segment read off a first-record word is state independent on `srSet`.** -/
theorem segOf_eq_of_srSet {y y' : RecState N m} (hy : y ∈ srSet N m) (hy' : y' ∈ srSet N m)
    {k : ℕ} (hk : 0 < k) (q : Fin k → JumpVec N)
    (hfr : Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y)) :
    SwarmSegKernel.segOf y k q = SwarmSegKernel.segOf y' k q := by
  have hfr' : Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y') :=
    (firstRecord_ofRecState_iff hy hy' (Record.extendPath q) k).mp hfr
  rw [SwarmSegKernel.segOf, SwarmSegKernel.segOf, dif_pos ⟨hk, hfr⟩, dif_pos ⟨hk, hfr'⟩,
    SwarmSegKernel.segOfFirst, SwarmSegKernel.segOfFirst, SwarmConcat.Seg.mk.injEq]
  refine ⟨rfl, ?_⟩
  funext n i
  exact (relP_eq_posAt hy (Record.extendPath q) n i).trans
    (relP_eq_posAt hy' (Record.extendPath q) n i).symm

/-! ## 4. The strict-positivity part of the first-segment law is state independent -/

/-- The first-segment law of the enriched record step, restricted to the words that keep every
walker strictly above the record level — the paper's no-return clause `V`, at the finite horizon
of one segment.  This is the `Prod.fst` image of `SwarmSegKernel.asegK` cut down to those atoms. -/
noncomputable def segKpos (p : ℝ) (hm : 1 ≤ m) (y : RecState N m) : Measure (SwarmConcat.Seg N) := by
  classical
  exact Measure.sum (fun pq : (k : ℕ) × (Fin k → JumpVec N) =>
    if SwarmFreshPos.PosSeqFin (N := N) pq.2 then
      ENNReal.ofReal (RecKernel.hitW p pq.2 y) • Measure.dirac (SwarmSegKernel.segOf y pq.1 pq.2)
    else 0)

theorem segKpos_apply (p : ℝ) (hm : 1 ≤ m) (y : RecState N m) {A : Set (SwarmConcat.Seg N)}
    (hA : MeasurableSet A) :
    segKpos p hm y A = ∑' pq : (k : ℕ) × (Fin k → JumpVec N),
      (if SwarmFreshPos.PosSeqFin (N := N) pq.2 then
        ENNReal.ofReal (RecKernel.hitW p pq.2 y) *
          (if SwarmSegKernel.segOf y pq.1 pq.2 ∈ A then 1 else 0) else 0) := by
  classical
  rw [segKpos, Measure.sum_apply _ hA]
  refine tsum_congr fun pq => ?_
  by_cases hq : SwarmFreshPos.PosSeqFin (N := N) pq.2
  · rw [if_pos hq, if_pos hq, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hA]
    simp only [Set.indicator_apply, Pi.one_apply]
  · rw [if_neg hq, if_neg hq]
    simp

/-- **The strict-positivity first-segment law does not depend on the simultaneous-record start
state.**  This is the independence half of `(freshlaw)` read on the object the record chain
actually consumes: the sub-kernel of `segK` whose segments never return to the record level. -/
theorem segKpos_eq_of_srSet (p : ℝ) (hm : 1 ≤ m) {y y' : RecState N m} (hy : y ∈ srSet N m)
    (hy' : y' ∈ srSet N m) : segKpos p hm y = segKpos p hm y' := by
  classical
  ext A hA
  rw [segKpos_apply p hm y hA, segKpos_apply p hm y' hA]
  refine tsum_congr fun pq => ?_
  by_cases hq : SwarmFreshPos.PosSeqFin (N := N) pq.2
  · rw [if_pos hq, if_pos hq]
    have hiff := firstRecord_ofRecState_iff hy hy' (Record.extendPath pq.2) pq.1
    by_cases hfr : Record.FirstRecord (Record.extendPath pq.2) pq.1 (Record.ofRecState y)
    · have hk : 0 < pq.1 := by
        rcases pq with ⟨k, q⟩
        rcases (firstRecord_iff_posAt hy (Record.extendPath q) k).mp hfr with ⟨⟨i, hi⟩, _⟩
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · exfalso
          subst hk0
          rw [SwarmFreshPos.posAt_zero] at hi
          exact zero_ne_one hi
        · exact hkpos
      rw [hitW_eq_of_srSet hm hy hy' pq.2 hq, segOf_eq_of_srSet hy hy' hk pq.2 hfr]
    · have hfr' : ¬ Record.FirstRecord (Record.extendPath pq.2) pq.1
          (Record.ofRecState y') := fun h => hfr (hiff.mpr h)
      rw [RecKernel.hitW_of_not_firstRecord p pq.2 y hfr,
        RecKernel.hitW_of_not_firstRecord p pq.2 y' hfr']
      simp
  · rw [if_neg hq, if_neg hq]

/-- The measurable-set form: every finite measurable path cylinder of segments has the same
strict-positivity mass from every simultaneous-record start state. -/
theorem segKpos_measure_eq_of_srSet (p : ℝ) (hm : 1 ≤ m) {y y' : RecState N m}
    (hy : y ∈ srSet N m) (hy' : y' ∈ srSet N m) {A : Set (SwarmConcat.Seg N)}
    (hA : MeasurableSet A) : segKpos p hm y A = segKpos p hm y' A := by
  rw [segKpos_eq_of_srSet p hm hy hy']


/-! ## 5. `segKpos` is the strict-positivity part of the accepted first-segment law -/

theorem segKpos_le_segK (p : ℝ) (hm : 1 ≤ m) (y : RecState N m) :
    segKpos p hm y ≤ SwarmSegKernel.segK p hm y := by
  classical
  rw [Measure.le_iff]
  intro A hA
  rw [segKpos_apply p hm y hA, SwarmSegKernel.segK, Measure.map_apply measurable_fst hA,
    SwarmSegKernel.asegK_apply p hm y (measurable_fst hA)]
  refine ENNReal.tsum_le_tsum fun pq => ?_
  have hmem : ((SwarmSegKernel.segOf y pq.1 pq.2, RecKernel.out hm pq.2 y) ∈ Prod.fst ⁻¹' A)
      ↔ SwarmSegKernel.segOf y pq.1 pq.2 ∈ A := Iff.rfl
  by_cases hq : SwarmFreshPos.PosSeqFin (N := N) pq.2
  · rw [if_pos hq]
    by_cases hin : SwarmSegKernel.segOf y pq.1 pq.2 ∈ A
    · have h' : (SwarmSegKernel.segOf y pq.1 pq.2, RecKernel.out hm pq.2 y) ∈ Prod.fst ⁻¹' A :=
        hmem.mpr hin
      rw [if_pos hin, if_pos h']
    · have h' : ¬ ((SwarmSegKernel.segOf y pq.1 pq.2, RecKernel.out hm pq.2 y)
          ∈ Prod.fst ⁻¹' A) := fun h => hin (hmem.mp h)
      rw [if_neg hin, if_neg h']
  · rw [if_neg hq]
    exact bot_le

/-! ## 6. Finite path cylinders: the exact first-segment mass -/

/-- The finite path cylinder of the jump word `q` in the segment space: duration `k` and relative
position path the net displacement of `q`.  A measurable set of the segment σ-algebra. -/
def wordCyl {k : ℕ} (q : Fin k → JumpVec N) : Set (SwarmConcat.Seg N) :=
  {s | s.dur = k ∧ s.p = fun n i => SwarmFreshPos.posAt (Record.extendPath q) n i}

theorem measurableSet_wordCyl {k : ℕ} (q : Fin k → JumpVec N) :
    MeasurableSet (wordCyl (N := N) q) := by
  have hpair : Measurable (fun s : SwarmConcat.Seg N => (s.dur, s.p)) :=
    measurable_iff_comap_le.mpr le_rfl
  have hF : MeasurableSet {f : ℕ → Fin N → ℤ |
      f = fun n i => SwarmFreshPos.posAt (Record.extendPath q) n i} := by
    rw [show {f : ℕ → Fin N → ℤ |
        f = fun n i => SwarmFreshPos.posAt (Record.extendPath q) n i}
        = ⋂ n, ⋂ i, {f | f n i = SwarmFreshPos.posAt (Record.extendPath q) n i} from by
      ext f
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      exact ⟨fun h n i => by rw [h], fun h => funext fun n => funext fun i => h n i⟩]
    refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun i => ?_
    exact measurableSet_eq_fun ((measurable_pi_apply i).comp (measurable_pi_apply n))
      measurable_const
  have hEq : wordCyl (N := N) q = (fun s : SwarmConcat.Seg N => (s.dur, s.p)) ⁻¹'
      ({k} ×ˢ {f : ℕ → Fin N → ℤ | f = fun n i => SwarmFreshPos.posAt (Record.extendPath q) n i}) := by
    ext s
    simp [wordCyl]
  rw [hEq]
  exact hpair ((measurableSet_singleton k).prod hF)

theorem mem_wordCyl_self {k : ℕ} (q : Fin k → JumpVec N) :
    (fun n i => SwarmFreshPos.posAt (Record.extendPath q) n i) ∈
      ({f : ℕ → Fin N → ℤ | f = fun n i => SwarmFreshPos.posAt (Record.extendPath q) n i}) :=
  rfl

/-- The position path of a word determines the word. -/
theorem extendPath_eq_of_posAt_eq {k : ℕ} {q q' : Fin k → JumpVec N}
    (h : ∀ (n : ℕ) (i : Fin N), SwarmFreshPos.posAt (Record.extendPath q) n i
      = SwarmFreshPos.posAt (Record.extendPath q') n i) : q = q' := by
  funext j i
  have h1 := h ((j : ℕ) + 1) i
  have h2 := h (j : ℕ) i
  rw [SwarmFreshPos.posAt_succ, SwarmFreshPos.posAt_succ, h2] at h1
  have hstep := add_left_cancel h1
  have key : ∀ b b' : Bool, (if b = true then (1 : ℤ) else -1)
      = (if b' = true then (1 : ℤ) else -1) → b = b' := by
    intro b b' h
    cases b <;> cases b' <;> simp_all
  have hb : Record.extendPath q (j : ℕ) i = Record.extendPath q' (j : ℕ) i :=
    key _ _ hstep
  simpa only [Record.extendPath, dif_pos j.isLt] using hb

/-- **The exact first-segment mass of a finite path cylinder.**  For a simultaneous-record start
state `y ∈ srSet` and a first-record word `q` that keeps every walker strictly above the record
level, the strict-positivity part of the first-segment law gives the cylinder of `q` exactly the
fresh word mass `hitW p q y = pathW p k q (ofRecState y)` — which by `hitW_eq_fresh` is
`pathW p k q s` for every fresh start `s`. -/
theorem segKpos_wordCyl (p : ℝ) (hm : 1 ≤ m) {y : RecState N m} (hy : y ∈ srSet N m)
    {k : ℕ} (hk : 0 < k) (q : Fin k → JumpVec N)
    (hfr : Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y))
    (hq : SwarmFreshPos.PosSeqFin (N := N) q) :
    segKpos p hm y (wordCyl q) = ENNReal.ofReal (RecKernel.hitW p q y) := by
  classical
  have hmem : SwarmSegKernel.segOf y k q ∈ wordCyl q := by
    constructor
    · rw [SwarmSegKernel.segOf, dif_pos ⟨hk, hfr⟩]
      rfl
    · rw [SwarmSegKernel.segOf, dif_pos ⟨hk, hfr⟩]
      funext n i
      exact relP_eq_posAt hy (Record.extendPath q) n i
  rw [segKpos_apply p hm y (measurableSet_wordCyl q)]
  trans (if SwarmFreshPos.PosSeqFin (N := N) q then
      ENNReal.ofReal (RecKernel.hitW p q y) *
        (if SwarmSegKernel.segOf y k q ∈ wordCyl q then 1 else 0) else 0)
  · refine tsum_eq_single (b := (⟨k, q⟩ : (k : ℕ) × (Fin k → JumpVec N))) ?_
    rintro ⟨k', q'⟩ hpq
    by_cases hq' : SwarmFreshPos.PosSeqFin (N := N) q'
    · rw [if_pos hq']
      by_cases hfr' : Record.FirstRecord (Record.extendPath q') k' (Record.ofRecState y)
      · have hk' : 0 < k' := by
          rcases (firstRecord_iff_posAt hy (Record.extendPath q') k').mp hfr' with ⟨⟨i, hi⟩, _⟩
          rcases Nat.eq_zero_or_pos k' with hk0 | hkpos
          · exfalso
            subst hk0
            rw [SwarmFreshPos.posAt_zero] at hi
            exact zero_ne_one hi
          · exact hkpos
        have hnot : SwarmSegKernel.segOf y k' q' ∉ wordCyl q := by
          rintro ⟨hdur, hp⟩
          have hkk : k' = k := by
            rw [← segOf_dur_of_firstRecord hk' q' hfr']
            exact hdur
          subst hkk
          rw [segOf_p_of_firstRecord hk' q' hfr'] at hp
          have hq'q : q' = q := extendPath_eq_of_posAt_eq fun n i => by
            rw [← relP_eq_posAt hy (Record.extendPath q') n i]
            exact congrFun (congrFun hp n) i
          exact hpq (by rw [hq'q])
        rw [if_neg hnot, mul_zero]
      · rw [RecKernel.hitW_of_not_firstRecord p q' y hfr', ENNReal.ofReal_zero, zero_mul]
    · rw [if_neg hq']
  · rw [if_pos hq, if_pos hmem, mul_one]


/-! ## 7. The strict-positivity record step stays in `srSet` -/

/-- If a first-record word keeps every walker strictly above the level then every walker is at the
record level at the end: at time `k-1` all are at or below the level, so at time `k` all are at or
below the next one, and strict positivity forces all of them onto it. -/
theorem hitsFAt_of_firstRecord_pos {y : RecState N m} (hy : y ∈ srSet N m) {k : ℕ}
    (q : Fin k → JumpVec N)
    (hfr : Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y))
    (hq : SwarmFreshPos.PosSeqFin (N := N) q) :
    HitsFAt q (Record.ofRecState y) := by
  obtain ⟨-, hlt⟩ := (firstRecord_iff_posAt hy (Record.extendPath q) k).mp hfr
  have hpos := (posWord_iff q).mp hq
  have hk : 0 < k := by
    rcases firstRecord_iff_posAt (y := y) hy (Record.extendPath q) k |>.mp hfr with ⟨⟨i, hi⟩, _⟩
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · exfalso
      subst hk0
      rw [SwarmFreshPos.posAt_zero] at hi
      exact zero_ne_one hi
    · exact hkpos
  have hstate : ∀ (n : ℕ) (hn : n ≤ k) (i : Fin N),
      (stateAt q n hn (Record.ofRecState y)).pos i
        = SwarmFreshPos.posAt (Record.extendPath q) n i := by
    intro n hn i
    rw [← Record.evolveFun_extendPath_le q (Record.ofRecState y) n hn,
      SwarmFreshPos.pos_evolveFun, ofRecState_pos_eq_zero hy i, zero_add]
  constructor
  · intro i
    have hlast : SwarmFreshPos.posAt (Record.extendPath q) k i
        = SwarmFreshPos.posAt (Record.extendPath q) (k - 1) i
            + (if Record.extendPath q (k - 1) i = true then (1 : ℤ) else -1) := by
      rw [← SwarmFreshPos.posAt_succ (Record.extendPath q) (k - 1) i]
      congr 1
      omega
    have hle : SwarmFreshPos.posAt (Record.extendPath q) (k - 1) i ≤ 0 := hlt (k - 1) (by omega) i
    have hup : SwarmFreshPos.posAt (Record.extendPath q) k i ≤ 1 := by
      rw [hlast]
      split_ifs <;> omega
    have hgt : 0 < SwarmFreshPos.posAt (Record.extendPath q) k i := hpos k (by omega) (by omega) i
    rw [hstate k le_rfl i]
    omega
  · intro n hn i
    rw [hstate n (le_of_lt hn) i]
    exact hlt n hn i

/-- **The enriched record step from a simultaneous record along a strict-positivity word lands in
`srSet` again** — the record chain closes the regeneration loop on `F`. -/
theorem out_mem_srSet_of_pos (hm : 1 ≤ m) (hN : 0 < N) {y : RecState N m}
    (hy : y ∈ srSet N m) {k : ℕ} (q : Fin k → JumpVec N)
    (hfr : Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y))
    (hq : SwarmFreshPos.PosSeqFin (N := N) q) :
    RecKernel.out hm q y ∈ srSet N m :=
  RecKernel.out_mem_srSet hm hN q y (hitsFAt_of_firstRecord_pos hy q hfr hq)

end SwarmFreshCyl


