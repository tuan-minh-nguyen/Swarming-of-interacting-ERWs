/-
# the finite two-segment fresh-mass step on the record side

The accepted `Swarm/FreshCyl.lean` proves the *first*-segment identity at a simultaneous record
(`y ∈ srSet N m`): the weight `hitW p q y` of a first-record word that keeps every walker strictly
above the level does not depend on `y`, and the strict-positivity part `segKpos p hm y` of the
one-step segment law is a single measure on `Seg N`.  What was open — and what this file proves —
is the *second* segment: the fact that the endpoint record state `RecKernel.out hm q₀ y` of such a
word is again in `srSet`, so that the conditional law of the next positive first-record segment is
*the same function of the whole second word* and not of the endpoint state, and hence that the
two-step segment-cylinder mass is the product of the two first-segment word weights.

The objects are the true ones:

* `asegK p hm y` — the path-enriched one-step record kernel (`segOf`, `RecKernel.out`, `hitW`);
* `pairK p hm` — its induced transition on the enriched state space `Seg N × RecState N m`;
* `SwarmChain.chainVec μ κ 2` — the law of `(x 0, x 1)` of the chain started from `μ` with kernel
  `κ`, so `chainVec (asegK p hm y) (pairK p hm) 2` is the law of the two consecutive enriched
  segment atoms when the chain starts at the genuine record state `y`.

Main results.

* `firstRecord_length_pos`, `seg_end_eq_one`, `segOf_inj_of_srSet` — elementary algebra of the
  atoms on `srSet`.
* `asegK_atom` / `asegK_segCyl` — the exact mass of one atom, respectively of the state-free
  segment cylinder `{b | b.1 = segOf y k q}`, under the true one-step law: `ofReal (hitW p q y)`.
* `hitW_step2_eq`, `segOf_step2_eq`, `asegK_step2_segCyl` — **the endpoint independence**: for a
  genuine `y ∈ srSet`, a positive first-record word `q₀` and its endpoint `y₁ = out hm q₀ y ∈ srSet`,
  the second-segment cylinder mass at `y₁` equals the first-segment word weight `hitW p q y` read at
  the start state `y`, and the segment itself is the same `segOf y k q`.
* `chainVec_two_apply` — the general two-step cylinder computation of `chainVec μ κ 2` for a Markov
  kernel `κ`, as an integral of the one-step kernel over the first atom.
* `twoSeg_joint_of_step2` and its two corollaries `twoSeg_joint_mass` (state-free second segment
  cylinder) and `twoSeg_atom_mass` (literal `(a,b)` atom pair) — the joint two-step mass is
  `ofReal (hitW p q₀ y) * ofReal (hitW p q₁ y)`, i.e. the product of the first-segment word weights
  at the start state, and in particular equals the product of the two first-segment cylinder masses
  of `segKpos` (`twoSeg_joint_mass_segKpos`).
* `twoSeg_compat` — the literal `SwarmConcat.Chain.compat` boundary identity at those atoms:
  `0 + (segOf y k₀ q₀).p dur = 1 + (segOf y k₁ q₁).p 0`, so the two atoms really concatenate as
  levels `0` and `1` of one path.

Scope (see `SCOPE.md`, and no stronger claim is made anywhere in this file): this is the finite
two-segment composition.  It is not `hstruct`, not a global no-return statement, not an arbitrary
future event law, and it does not construct an infinite trajectory, an invariant `π` or a positive
`π (srSet)`.  The conditional independence it uses is exactly the proved one: the *endpoint record
state is in `srSet`*, which is what makes the next positive segment weight state-independent; it is
not an assertion that arbitrary endpoint record states agree.
-/
import Swarm.FreshCyl

open MeasureTheory Set
open Classical
open scoped ENNReal
open SimJump ProbabilityTheory

namespace SwarmFreshTwoSeg

open SimJump.Record SwarmRec

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

variable {N m : ℕ}

/-! ## 1. Words and atoms on `srSet` -/

/-- A first-record word driven from a record state has positive length: at time `0` every walker
is at or below the record level, at time `k` some walker is at level `1`. -/
theorem firstRecord_length_pos {y : RecState N m} {k : ℕ} (q : Fin k → JumpVec N)
    (hfr : Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y)) : 0 < k := by
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h
    obtain ⟨i, hi⟩ := hfr.1
    rw [SwarmFreshPos.evolveFun_zero] at hi
    have := SwarmSegKernel.ofRecState_pos_nonpos y i
    omega
  · exact h

/-- The end of a positive first-record segment sits exactly at the next record level: all walkers
are at the level `1` of the segment's own coordinates. -/
theorem seg_end_eq_one (hm : 1 ≤ m) (hN : 0 < N) {y : RecState N m} (hy : y ∈ srSet N m)
    {k : ℕ} (hk : 0 < k) (q : Fin k → JumpVec N)
    (hfr : Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y))
    (hq : SwarmFreshPos.PosSeqFin (N := N) q) (i : Fin N) :
    (SwarmSegKernel.segOf y k q).p k i = 1 := by
  have hmem := SwarmFreshCyl.out_mem_srSet_of_pos hm hN hy q hfr hq
  have hpos : (Record.ofRecState (RecKernel.out hm q y)).pos i = 0 :=
    SwarmFreshCyl.ofRecState_pos_eq_zero hmem i
  have h1 := SwarmSegKernel.segOfFirst_p_dur y hm q hk hfr i
  have h2 : (SwarmSegKernel.segOfFirst y k q hk hfr).p k i
      = (evolveFun (m := m) (Record.extendPath q) k (Record.ofRecState y)).pos i := rfl
  rw [SwarmFreshCyl.segOf_p_of_firstRecord hk q hfr]
  show (evolveFun (m := m) (Record.extendPath q) k (Record.ofRecState y)).pos i = 1
  rw [← h2, h1, hpos, add_zero]

/-- **A segment of a first-record word determines the word**, on `srSet`: the map
`(k, q) ↦ segOf y k q` is injective on positive-length first-record words. -/
theorem pq_eq_of_segOf_eq {y y' : RecState N m} (hy : y ∈ srSet N m) (hy' : y' ∈ srSet N m)
    {k k' : ℕ} (hk : 0 < k) (hk' : 0 < k') (q : Fin k → JumpVec N) (q' : Fin k' → JumpVec N)
    (hfr : Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y))
    (hfr' : Record.FirstRecord (Record.extendPath q') k' (Record.ofRecState y'))
    (heq : SwarmSegKernel.segOf y k q = SwarmSegKernel.segOf y' k' q') :
    (⟨k, q⟩ : (k : ℕ) × (Fin k → JumpVec N)) = ⟨k', q'⟩ := by
  have hd1 : (SwarmSegKernel.segOf y k q).dur = k :=
    SwarmFreshCyl.segOf_dur_of_firstRecord hk q hfr
  have hd2 : (SwarmSegKernel.segOf y' k' q').dur = k' :=
    SwarmFreshCyl.segOf_dur_of_firstRecord hk' q' hfr'
  have hk_eq : k = k' := by rw [← hd1, ← hd2, heq]
  cases hk_eq
  have hp1 : (SwarmSegKernel.segOf y k q).p = SwarmSegKernel.relP y (Record.extendPath q) :=
    SwarmFreshCyl.segOf_p_of_firstRecord hk q hfr
  have hp2 : (SwarmSegKernel.segOf y' k q').p = SwarmSegKernel.relP y' (Record.extendPath q') :=
    SwarmFreshCyl.segOf_p_of_firstRecord hk q' hfr'
  have hpp : SwarmSegKernel.relP y (Record.extendPath q)
      = SwarmSegKernel.relP y' (Record.extendPath q') := by
    rw [← hp1, ← hp2]
    exact congrArg SwarmConcat.Seg.p heq
  have hq_eq : q = q' := by
    refine SwarmFreshCyl.extendPath_eq_of_posAt_eq (fun n i => ?_)
    have h1 := congrFun (congrFun hpp n) i
    rw [SwarmFreshCyl.relP_eq_posAt hy (Record.extendPath q) n i,
      SwarmFreshCyl.relP_eq_posAt hy' (Record.extendPath q') n i] at h1
    exact h1
  rw [hq_eq]

/-- Single points of the segment space are measurable (its σ-algebra is the comap of
`(dur, p)`, and a segment is determined by those two fields). -/
theorem measurableSet_seg_singleton (s : SwarmConcat.Seg N) :
    MeasurableSet ({s} : Set (SwarmConcat.Seg N)) := by
  have hpair : Measurable (fun s : SwarmConcat.Seg N => (s.dur, s.p)) :=
    measurable_iff_comap_le.mpr le_rfl
  have hF : MeasurableSet {f : ℕ → Fin N → ℤ | f = s.p} := by
    rw [show {f : ℕ → Fin N → ℤ | f = s.p} = ⋂ n, ⋂ i, {f | f n i = s.p n i} from by
      ext f
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      exact ⟨fun h n i => by rw [h], fun h => funext fun n => funext fun i => h n i⟩]
    exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun i =>
      measurableSet_eq_fun ((measurable_pi_apply i).comp (measurable_pi_apply n)) measurable_const
  have hinj : ∀ s' : SwarmConcat.Seg N, s'.dur = s.dur → s'.p = s.p → s' = s := by
    intro s' h1 h2
    cases s
    cases s'
    simp_all
  have hmeas : MeasurableSet ((fun s' : SwarmConcat.Seg N => (s'.dur, s'.p)) ⁻¹'
      ({s.dur} ×ˢ {f : ℕ → Fin N → ℤ | f = s.p})) :=
    hpair ((measurableSet_singleton s.dur).prod hF)
  convert hmeas using 1
  ext s'
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  exact ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun h => hinj s' h.1 h.2⟩

/-! ## 2. Exact masses of one enriched atom and of a segment cylinder -/

/-- **The exact mass of one enriched atom.**  From a simultaneous-record state, the one-step
enriched law charges the atom `(segOf y k q, out hm q y)` exactly its word weight `hitW p q y`. -/
theorem asegK_atom (p : ℝ) (hm : 1 ≤ m) {y : RecState N m} (hy : y ∈ srSet N m)
    {k : ℕ} (hk : 0 < k) (q : Fin k → JumpVec N)
    (hfr : Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y)) :
    (SwarmSegKernel.asegK p hm y)
        {(SwarmSegKernel.segOf y k q, RecKernel.out hm q y)}
      = ENNReal.ofReal (RecKernel.hitW p q y) := by
  classical
  have hmeas : MeasurableSet ({(SwarmSegKernel.segOf y k q, RecKernel.out hm q y)} :
      Set (SwarmConcat.Seg N × RecState N m)) := by
    have h := (measurableSet_seg_singleton (SwarmSegKernel.segOf y k q)).prod
      (measurableSet_singleton (RecKernel.out hm q y))
    rwa [Set.singleton_prod_singleton] at h
  rw [SwarmSegKernel.asegK_apply p hm y hmeas]
  refine (tsum_eq_single (⟨k, q⟩) ?_).trans ?_
  · rintro ⟨k', q'⟩ hne
    by_cases hfr' : Record.FirstRecord (Record.extendPath q') k' (Record.ofRecState y)
    · rw [if_neg, mul_zero]
      intro hmem
      simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      exact hne (pq_eq_of_segOf_eq hy hy (firstRecord_length_pos q' hfr') hk
        q' q hfr' hfr hmem.1)
    · rw [RecKernel.hitW_of_not_firstRecord p q' y hfr', ENNReal.ofReal_zero, zero_mul]
  · simp

/-- **The exact mass of a state-free segment cylinder.**  The second component of the atom is
forgotten: from a simultaneous-record state the one-step law puts exactly the word weight on the
set of atoms whose segment is the one read off that word. -/
theorem asegK_segCyl (p : ℝ) (hm : 1 ≤ m) {y : RecState N m} (hy : y ∈ srSet N m)
    {k : ℕ} (hk : 0 < k) (q : Fin k → JumpVec N)
    (hfr : Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y)) :
    (SwarmSegKernel.asegK p hm y)
        {b : SwarmConcat.Seg N × RecState N m | b.1 = SwarmSegKernel.segOf y k q}
      = ENNReal.ofReal (RecKernel.hitW p q y) := by
  classical
  have hmeas : MeasurableSet
      {b : SwarmConcat.Seg N × RecState N m | b.1 = SwarmSegKernel.segOf y k q} :=
    measurable_fst (measurableSet_seg_singleton _)
  rw [SwarmSegKernel.asegK_apply p hm y hmeas]
  refine (tsum_eq_single (⟨k, q⟩) ?_).trans ?_
  · rintro ⟨k', q'⟩ hne
    by_cases hfr' : Record.FirstRecord (Record.extendPath q') k' (Record.ofRecState y)
    · rw [if_neg, mul_zero]
      intro hmem
      simp only [Set.mem_ofPred_eq] at hmem
      exact hne (pq_eq_of_segOf_eq hy hy (firstRecord_length_pos q' hfr') hk
        q' q hfr' hfr hmem)
    · rw [RecKernel.hitW_of_not_firstRecord p q' y hfr', ENNReal.ofReal_zero, zero_mul]
  · simp

/-- The one-step cylinder mass of a positive first-record word does not depend on the
simultaneous-record state it is started from. -/
theorem asegK_segCyl_eq_of_srSet (p : ℝ) (hm : 1 ≤ m) {y y' : RecState N m}
    (hy : y ∈ srSet N m) (hy' : y' ∈ srSet N m) {k : ℕ} (hk : 0 < k) (q : Fin k → JumpVec N)
    (hfr : Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y))
    (hq : SwarmFreshPos.PosSeqFin (N := N) q) :
    (SwarmSegKernel.asegK p hm y)
        {b : SwarmConcat.Seg N × RecState N m | b.1 = SwarmSegKernel.segOf y k q}
      = (SwarmSegKernel.asegK p hm y')
        {b : SwarmConcat.Seg N × RecState N m | b.1 = SwarmSegKernel.segOf y' k q} := by
  have hfr' : Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y') :=
    (SwarmFreshCyl.firstRecord_ofRecState_iff hy hy' (Record.extendPath q) k).mp hfr
  rw [asegK_segCyl p hm hy hk q hfr, asegK_segCyl p hm hy' hk q hfr',
    SwarmFreshCyl.hitW_eq_of_srSet hm hy hy' q hq]

/-! ## 3. The endpoint record state of a positive word is again in `srSet` -/

/-- **The second-segment conditional mass is independent of the endpoint record state.**  The
endpoint `out hm q₀ y` of a positive first-record word from `srSet` is again in `srSet`
(`SwarmFreshCyl.out_mem_srSet_of_pos`), so the word weight of the *next* positive first-record word
`q₁` is the same there as at the start state `y`. -/
theorem hitW_step2_eq {p : ℝ} (hm : 1 ≤ m) (hN : 0 < N) {y : RecState N m} (hy : y ∈ srSet N m)
    {k0 : ℕ} (q0 : Fin k0 → JumpVec N)
    (hfr0 : Record.FirstRecord (Record.extendPath q0) k0 (Record.ofRecState y))
    (hq0 : SwarmFreshPos.PosSeqFin (N := N) q0)
    {k1 : ℕ} (q1 : Fin k1 → JumpVec N) (hq1 : SwarmFreshPos.PosSeqFin (N := N) q1) :
    RecKernel.hitW p q1 (RecKernel.out hm q0 y) = RecKernel.hitW p q1 y :=
  SwarmFreshCyl.hitW_eq_of_srSet hm
    (SwarmFreshCyl.out_mem_srSet_of_pos hm hN hy q0 hfr0 hq0) hy q1 hq1

/-- The segment read off the second word is literally the same segment whether it is read at the
endpoint of the first word or at the start state. -/
theorem segOf_step2_eq (hm : 1 ≤ m) (hN : 0 < N) {y : RecState N m} (hy : y ∈ srSet N m)
    {k0 : ℕ} (q0 : Fin k0 → JumpVec N)
    (hfr0 : Record.FirstRecord (Record.extendPath q0) k0 (Record.ofRecState y))
    (hq0 : SwarmFreshPos.PosSeqFin (N := N) q0)
    {k1 : ℕ} (hk1 : 0 < k1) (q1 : Fin k1 → JumpVec N)
    (hfr1 : Record.FirstRecord (Record.extendPath q1) k1
      (Record.ofRecState (RecKernel.out hm q0 y))) :
    SwarmSegKernel.segOf (RecKernel.out hm q0 y) k1 q1
      = SwarmSegKernel.segOf y k1 q1 :=
  SwarmFreshCyl.segOf_eq_of_srSet
    (SwarmFreshCyl.out_mem_srSet_of_pos hm hN hy q0 hfr0 hq0) hy hk1 q1 hfr1

/-- **The one-step cylinder mass of the second word, read at the endpoint of the first word.**
This is the conditional mass of the second segment given the first atom; it equals the
first-segment word weight of `q₁` at the start state `y`. -/
theorem asegK_step2_segCyl (p : ℝ) (hm : 1 ≤ m) (hN : 0 < N) {y : RecState N m}
    (hy : y ∈ srSet N m) {k0 : ℕ} (_hk0 : 0 < k0) (q0 : Fin k0 → JumpVec N)
    (hfr0 : Record.FirstRecord (Record.extendPath q0) k0 (Record.ofRecState y))
    (hq0 : SwarmFreshPos.PosSeqFin (N := N) q0)
    {k1 : ℕ} (hk1 : 0 < k1) (q1 : Fin k1 → JumpVec N)
    (hfr1 : Record.FirstRecord (Record.extendPath q1) k1 (Record.ofRecState y))
    (hq1 : SwarmFreshPos.PosSeqFin (N := N) q1) :
    (SwarmSegKernel.asegK p hm (RecKernel.out hm q0 y))
        {b : SwarmConcat.Seg N × RecState N m | b.1 = SwarmSegKernel.segOf y k1 q1}
      = ENNReal.ofReal (RecKernel.hitW p q1 y) := by
  have hy1 : RecKernel.out hm q0 y ∈ srSet N m :=
    SwarmFreshCyl.out_mem_srSet_of_pos hm hN hy q0 hfr0 hq0
  have hfr1' : Record.FirstRecord (Record.extendPath q1) k1
      (Record.ofRecState (RecKernel.out hm q0 y)) :=
    (SwarmFreshCyl.firstRecord_ofRecState_iff hy1 hy (Record.extendPath q1) k1).mpr hfr1
  have hseg := segOf_step2_eq hm hN hy q0 hfr0 hq0 hk1 q1 hfr1'
  rw [← hseg, asegK_segCyl p hm hy1 hk1 q1 hfr1']
  exact congrArg ENNReal.ofReal (hitW_step2_eq hm hN hy q0 hfr0 hq0 q1 hq1)

/-! ## 4. The two-step law of the enriched chain

`SwarmChain.chainVec μ κ 2` is the law of `(x 0, x 1)` for the chain with start law `μ` and kernel
`κ`.  Its defining recursion is via `Measure.compProd` and the append map `snocF`; the next lemma
identifies the measure of a two-coordinate cylinder with the integral of the one-step kernel over
the first atom. -/

section ChainTwo

variable {β : Type*} [MeasurableSpace β]

/-- The first coordinate of `snocF v b` is the first coordinate of `v`. -/
theorem snocF_const_zero (a b : β) : SwarmChain.snocF (fun _ : Fin 1 => a) b 0 = a := by
  rw [show (0 : Fin 2) = (0 : Fin 1).castSucc from rfl, SwarmChain.snocF_castSucc]

/-- The second coordinate of `snocF v b` is `b`. -/
theorem snocF_const_one (a b : β) : SwarmChain.snocF (fun _ : Fin 1 => a) b 1 = b := by
  rw [show (1 : Fin 2) = Fin.last 1 from rfl, SwarmChain.snocF_last]

/-- A pushforward of an s-finite measure is s-finite.  (Not an instance in Mathlib; it is what
`Measure.compProd_apply` needs for the first coordinate of the two-step chain law.) -/
theorem sfinite_map {γ : Type*} [MeasurableSpace γ] (μ : Measure β) [SFinite μ] (f : β → γ)
    (hf : Measurable f) : SFinite (μ.map f) := by
  obtain ⟨m, hm, hμ⟩ := SFinite.out' (μ := μ)
  have hfin : ∀ n, IsFiniteMeasure ((m n).map f) := fun n => by
    constructor
    rw [Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ]
    exact (hm n).measure_univ_lt_top
  refine ⟨(fun n => (m n).map f), hfin, ?_⟩
  rw [hμ]
  ext s hs
  rw [Measure.map_apply hf hs, Measure.sum_apply _ (hf hs), Measure.sum_apply _ hs]
  exact tsum_congr fun n => (Measure.map_apply hf hs).symm

/-- **The two-step cylinder formula.**  For any s-finite start law `μ` and s-finite kernel `κ`,
the law of `(x 0, x 1)` charges a measurable two-coordinate cylinder `C` by integrating the
one-step kernel of the first atom over `μ`. -/
theorem chainVec_two_apply (μ : Measure β) [SFinite μ] (κ : Kernel β β) [IsSFiniteKernel κ]
    {C : Set (Fin 2 → β)} (hC : MeasurableSet C) :
    (SwarmChain.chainVec μ κ 2) C
      = ∫⁻ a, (κ a) {b : β | SwarmChain.snocF (fun _ : Fin 1 => a) b ∈ C} ∂μ := by
  classical
  have hS : MeasurableSet ((fun p : (Fin 1 → β) × β => SwarmChain.snocF p.1 p.2) ⁻¹' C) :=
    SwarmChain.measurable_snocF hC
  haveI hlast : IsSFiniteKernel (SwarmChain.lastK κ 0) := by
    unfold SwarmChain.lastK
    infer_instance
  have hg : Measurable (fun w : Fin 1 → β => (SwarmChain.lastK κ 0 w)
      (Prod.mk w ⁻¹' ((fun p : (Fin 1 → β) × β => SwarmChain.snocF p.1 p.2) ⁻¹' C))) :=
    Kernel.measurable_kernel_prodMk_left (κ := SwarmChain.lastK κ 0) hS
  have hconst : Measurable (fun b : β => fun _ : Fin 1 => b) :=
    measurable_pi_lambda _ fun _ => measurable_id
  haveI hmap : SFinite (Measure.map (fun b : β => fun _ : Fin 1 => b) μ) :=
    sfinite_map μ _ hconst
  rw [SwarmChain.chainVec_succ_succ (μ := μ) (κ := κ) 0, SwarmChain.chainVec_succ,
    SwarmChain.chainStep_zero, Measure.map_apply SwarmChain.measurable_snocF hC,
    Measure.compProd_apply hS, lintegral_map hg hconst]
  refine lintegral_congr fun a => ?_
  rw [SwarmChain.lastK_apply]
  rfl

end ChainTwo

/-! ## 5. The finite two-segment fresh-mass step -/

/-- **The two-segment fresh-mass identity, conditional form.**  Start the enriched chain at the
genuine record state `y ∈ srSet`.  The first atom is fixed to `(segOf y k₀ q₀, out hm q₀ y)`; the
second atom is required to lie in a measurable set `B` whose one-step mass *at the endpoint*
`out hm q₀ y` is the stated word weight `ofReal (hitW p q₁ y)`.  Then the joint two-step mass is the
product of the first-segment word weights.

The mathematical content is that the endpoint `out hm q₀ y` is again a simultaneous-record state
(`SwarmFreshCyl.out_mem_srSet_of_pos`), so the second-segment weight is the same function of `q₁` as
at the start state; the hypothesis `hBmass` is exactly that single fact, specialised to `B`. -/
theorem twoSeg_joint_of_step2 (p : ℝ) (hm : 1 ≤ m) (hp : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1)
    {y : RecState N m} (hy : y ∈ srSet N m) {k0 : ℕ} (hk0 : 0 < k0) (q0 : Fin k0 → JumpVec N)
    (hfr0 : Record.FirstRecord (Record.extendPath q0) k0 (Record.ofRecState y))
    {k1 : ℕ} (q1 : Fin k1 → JumpVec N) {B : Set (SwarmConcat.Seg N × RecState N m)}
    (hB : MeasurableSet B)
    (hBmass : (SwarmSegKernel.asegK p hm (RecKernel.out hm q0 y)) B
      = ENNReal.ofReal (RecKernel.hitW p q1 y)) :
    (SwarmChain.chainVec (SwarmSegKernel.asegK p hm y) (SwarmSegKernel.pairK p hm) 2)
        {v : Fin 2 → (SwarmConcat.Seg N × RecState N m) |
          v 0 = (SwarmSegKernel.segOf y k0 q0, RecKernel.out hm q0 y) ∧ v 1 ∈ B}
      = ENNReal.ofReal (RecKernel.hitW p q0 y) * ENNReal.ofReal (RecKernel.hitW p q1 y) := by
  classical
  haveI hmark : IsMarkovKernel (SwarmSegKernel.pairK p hm) :=
    SwarmSegKernel.isMarkovKernel_pairK (N := N) (m := m) p hm hp hp1
  haveI hfin : IsFiniteMeasure (SwarmSegKernel.asegK p hm y) :=
    ⟨by rw [SwarmSegKernel.asegK_univ (N := N) (m := m) p hm hp hp1 y]
        exact ENNReal.one_lt_top⟩
  haveI hsf : SFinite (SwarmSegKernel.asegK p hm y) := inferInstance
  have hA0 : MeasurableSet
      ({(SwarmSegKernel.segOf y k0 q0, RecKernel.out hm q0 y)} :
        Set (SwarmConcat.Seg N × RecState N m)) := by
    have h := (measurableSet_seg_singleton (SwarmSegKernel.segOf y k0 q0)).prod
      (measurableSet_singleton (RecKernel.out hm q0 y))
    rwa [Set.singleton_prod_singleton] at h
  have hC : MeasurableSet {v : Fin 2 → (SwarmConcat.Seg N × RecState N m) |
      v 0 = (SwarmSegKernel.segOf y k0 q0, RecKernel.out hm q0 y) ∧ v 1 ∈ B} := by
    have h1 : MeasurableSet ((fun v : Fin 2 → (SwarmConcat.Seg N × RecState N m) => v 0) ⁻¹'
        ({(SwarmSegKernel.segOf y k0 q0, RecKernel.out hm q0 y)} :
          Set (SwarmConcat.Seg N × RecState N m))) :=
      (measurable_pi_apply (0 : Fin 2)) hA0
    have h2 : MeasurableSet ((fun v : Fin 2 → (SwarmConcat.Seg N × RecState N m) => v 1) ⁻¹'
        B) := (measurable_pi_apply (1 : Fin 2)) hB
    exact h1.inter h2
  rw [chainVec_two_apply _ _ hC]
  have hsection : ∀ a : SwarmConcat.Seg N × RecState N m,
      {b : SwarmConcat.Seg N × RecState N m |
        SwarmChain.snocF (fun _ : Fin 1 => a) b ∈ {v : Fin 2 → (SwarmConcat.Seg N ×
          RecState N m) | v 0 = (SwarmSegKernel.segOf y k0 q0, RecKernel.out hm q0 y) ∧ v 1 ∈ B}}
        = if a = (SwarmSegKernel.segOf y k0 q0, RecKernel.out hm q0 y) then B else ∅ := by
    intro a
    by_cases ha : a = (SwarmSegKernel.segOf y k0 q0, RecKernel.out hm q0 y)
    · rw [if_pos ha]
      ext b
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨-, h2⟩
        rwa [snocF_const_one] at h2
      · intro h
        exact ⟨by rw [snocF_const_zero]; exact ha, by rwa [snocF_const_one]⟩
    · rw [if_neg ha]
      ext b
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false]
      exact ⟨fun h => absurd (by rw [← snocF_const_zero a b]; exact h.1) ha, fun h => absurd h (by simp)⟩
  have hpoint : ∀ a : SwarmConcat.Seg N × RecState N m,
      (SwarmSegKernel.asegK p hm a.2)
        {b : SwarmConcat.Seg N × RecState N m |
          SwarmChain.snocF (fun _ : Fin 1 => a) b ∈ {v : Fin 2 → (SwarmConcat.Seg N ×
            RecState N m) | v 0 = (SwarmSegKernel.segOf y k0 q0, RecKernel.out hm q0 y) ∧ v 1 ∈ B}}
        = if a = (SwarmSegKernel.segOf y k0 q0, RecKernel.out hm q0 y) then
            ENNReal.ofReal (RecKernel.hitW p q1 y) else 0 := by
    intro a
    by_cases ha : a = (SwarmSegKernel.segOf y k0 q0, RecKernel.out hm q0 y)
    · rw [if_pos ha, hsection a, if_pos ha, ha]
      exact hBmass
    · rw [if_neg ha, hsection a, if_neg ha]
      exact MeasureTheory.measure_empty
  have hgi : (fun a : SwarmConcat.Seg N × RecState N m =>
        (SwarmSegKernel.pairK p hm a)
          {b : SwarmConcat.Seg N × RecState N m |
            SwarmChain.snocF (fun _ : Fin 1 => a) b ∈ {v : Fin 2 → (SwarmConcat.Seg N ×
              RecState N m) | v 0 = (SwarmSegKernel.segOf y k0 q0, RecKernel.out hm q0 y)
                ∧ v 1 ∈ B}})
      = ({(SwarmSegKernel.segOf y k0 q0, RecKernel.out hm q0 y)} :
          Set (SwarmConcat.Seg N × RecState N m)).indicator
        (fun _ => ENNReal.ofReal (RecKernel.hitW p q1 y)) := by
    funext a
    rw [SwarmSegKernel.pairK_apply]
    by_cases ha : a = (SwarmSegKernel.segOf y k0 q0, RecKernel.out hm q0 y)
    · rw [hsection a, if_pos ha, ha]
      simp [Set.indicator, ha, hBmass]
    · rw [hsection a, if_neg ha]
      simp [Set.indicator, ha, MeasureTheory.measure_empty]
  rw [hgi, lintegral_indicator_const hA0, asegK_atom p hm hy hk0 q0 hfr0]
  exact mul_comm _ _

/-- **The exact two-step mass of a segment cylinder.**  The second atom is constrained only in its
segment component, so this is the sum over the (state-dependent) second atom of the joint mass; it
factors into the two first-segment word weights. -/
theorem twoSeg_joint_mass (p : ℝ) (hm : 1 ≤ m) (hp : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1)
    (hN : 0 < N) {y : RecState N m} (hy : y ∈ srSet N m) {k0 : ℕ} (hk0 : 0 < k0)
    (q0 : Fin k0 → JumpVec N)
    (hfr0 : Record.FirstRecord (Record.extendPath q0) k0 (Record.ofRecState y))
    (hq0 : SwarmFreshPos.PosSeqFin (N := N) q0)
    {k1 : ℕ} (hk1 : 0 < k1) (q1 : Fin k1 → JumpVec N)
    (hfr1 : Record.FirstRecord (Record.extendPath q1) k1 (Record.ofRecState y))
    (hq1 : SwarmFreshPos.PosSeqFin (N := N) q1) :
    (SwarmChain.chainVec (SwarmSegKernel.asegK p hm y) (SwarmSegKernel.pairK p hm) 2)
        {v : Fin 2 → (SwarmConcat.Seg N × RecState N m) |
          v 0 = (SwarmSegKernel.segOf y k0 q0, RecKernel.out hm q0 y) ∧
          (v 1).1 = SwarmSegKernel.segOf y k1 q1}
      = ENNReal.ofReal (RecKernel.hitW p q0 y) * ENNReal.ofReal (RecKernel.hitW p q1 y) := by
  refine twoSeg_joint_of_step2 p hm hp hp1 hy hk0 q0 hfr0 (k1 := k1) (q1 := q1)
    (B := {b : SwarmConcat.Seg N × RecState N m | b.1 = SwarmSegKernel.segOf y k1 q1})
    (measurable_fst (measurableSet_seg_singleton _)) ?_
  exact asegK_step2_segCyl p hm hN hy hk0 q0 hfr0 hq0 hk1 q1 hfr1 hq1

/-- **The exact two-step mass of a literal pair of enriched atoms.**  The second atom is the true
atom of the second word at the endpoint of the first, `(segOf (out hm q₀ y) k₁ q₁,
out hm q₁ (out hm q₀ y))`, which is the same segment as `segOf y k₁ q₁`. -/
theorem twoSeg_atom_mass (p : ℝ) (hm : 1 ≤ m) (hp : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1)
    (hN : 0 < N) {y : RecState N m} (hy : y ∈ srSet N m) {k0 : ℕ} (hk0 : 0 < k0)
    (q0 : Fin k0 → JumpVec N)
    (hfr0 : Record.FirstRecord (Record.extendPath q0) k0 (Record.ofRecState y))
    (hq0 : SwarmFreshPos.PosSeqFin (N := N) q0)
    {k1 : ℕ} (hk1 : 0 < k1) (q1 : Fin k1 → JumpVec N)
    (hfr1 : Record.FirstRecord (Record.extendPath q1) k1 (Record.ofRecState y))
    (hq1 : SwarmFreshPos.PosSeqFin (N := N) q1) :
    (SwarmChain.chainVec (SwarmSegKernel.asegK p hm y) (SwarmSegKernel.pairK p hm) 2)
        {v : Fin 2 → (SwarmConcat.Seg N × RecState N m) |
          v 0 = (SwarmSegKernel.segOf y k0 q0, RecKernel.out hm q0 y) ∧
          v 1 = (SwarmSegKernel.segOf y k1 q1,
            RecKernel.out hm q1 (RecKernel.out hm q0 y))}
      = ENNReal.ofReal (RecKernel.hitW p q0 y) * ENNReal.ofReal (RecKernel.hitW p q1 y) := by
  have hy1 : RecKernel.out hm q0 y ∈ srSet N m :=
    SwarmFreshCyl.out_mem_srSet_of_pos hm hN hy q0 hfr0 hq0
  have hfr1' : Record.FirstRecord (Record.extendPath q1) k1
      (Record.ofRecState (RecKernel.out hm q0 y)) :=
    (SwarmFreshCyl.firstRecord_ofRecState_iff hy1 hy (Record.extendPath q1) k1).mpr hfr1
  have hseg := segOf_step2_eq hm hN hy q0 hfr0 hq0 hk1 q1 hfr1'
  refine twoSeg_joint_of_step2 p hm hp hp1 hy hk0 q0 hfr0 (k1 := k1) (q1 := q1)
    (B := {(SwarmSegKernel.segOf y k1 q1,
      RecKernel.out hm q1 (RecKernel.out hm q0 y))}) ?_ ?_
  · have h := (measurableSet_seg_singleton (SwarmSegKernel.segOf y k1 q1)).prod
      (measurableSet_singleton (RecKernel.out hm q1 (RecKernel.out hm q0 y)))
    rwa [Set.singleton_prod_singleton] at h
  · have hatom : (SwarmSegKernel.segOf (RecKernel.out hm q0 y) k1 q1,
        RecKernel.out hm q1 (RecKernel.out hm q0 y))
        = (SwarmSegKernel.segOf y k1 q1, RecKernel.out hm q1 (RecKernel.out hm q0 y)) := by
      rw [hseg]
    rw [← hatom, ← hitW_step2_eq hm hN hy q0 hfr0 hq0 q1 hq1]
    exact asegK_atom p hm hy1 hk1 q1 hfr1'

/-- **The two-step mass is the product of the two first-segment cylinder masses** of the restricted
strict-positivity law `segKpos` (the accepted one-step interface of `Swarm/FreshCyl.lean`). -/
theorem twoSeg_joint_mass_segKpos (p : ℝ) (hm : 1 ≤ m) (hp : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1)
    (hN : 0 < N) {y : RecState N m} (hy : y ∈ srSet N m) {k0 : ℕ} (hk0 : 0 < k0)
    (q0 : Fin k0 → JumpVec N)
    (hfr0 : Record.FirstRecord (Record.extendPath q0) k0 (Record.ofRecState y))
    (hq0 : SwarmFreshPos.PosSeqFin (N := N) q0)
    {k1 : ℕ} (hk1 : 0 < k1) (q1 : Fin k1 → JumpVec N)
    (hfr1 : Record.FirstRecord (Record.extendPath q1) k1 (Record.ofRecState y))
    (hq1 : SwarmFreshPos.PosSeqFin (N := N) q1) :
    (SwarmChain.chainVec (SwarmSegKernel.asegK p hm y) (SwarmSegKernel.pairK p hm) 2)
        {v : Fin 2 → (SwarmConcat.Seg N × RecState N m) |
          v 0 = (SwarmSegKernel.segOf y k0 q0, RecKernel.out hm q0 y) ∧
          (v 1).1 = SwarmSegKernel.segOf y k1 q1}
      = (SwarmFreshCyl.segKpos p hm y) (SwarmFreshCyl.wordCyl q0) *
        (SwarmFreshCyl.segKpos p hm y) (SwarmFreshCyl.wordCyl q1) := by
  rw [twoSeg_joint_mass p hm hp hp1 hN hy hk0 q0 hfr0 hq0 hk1 q1 hfr1 hq1,
    SwarmFreshCyl.segKpos_wordCyl p hm hy hk0 q0 hfr0 hq0,
    SwarmFreshCyl.segKpos_wordCyl p hm hy hk1 q1 hfr1 hq1]

/-! ## 6. The `Chain.compat` boundary at the two atoms -/

/-- **The two atoms concatenate as levels `0` and `1` of one path.**  With the segments
`segOf y k₀ q₀` and `segOf y k₁ q₁`, the level-shift compatibility `SwarmConcat.Chain.compat` at
`k = 0` holds: the end of the first segment is exactly one level above the start of the second.
This uses both that the first segment ends at the next record level (`seg_end_eq_one`, via the
endpoint being in `srSet`) and that the second segment starts at the record level
(`segOf_p_zero_srSet`). -/
theorem twoSeg_compat (hm : 1 ≤ m) (hN : 0 < N) {y : RecState N m} (hy : y ∈ srSet N m)
    {k0 : ℕ} (hk0 : 0 < k0) (q0 : Fin k0 → JumpVec N)
    (hfr0 : Record.FirstRecord (Record.extendPath q0) k0 (Record.ofRecState y))
    (hq0 : SwarmFreshPos.PosSeqFin (N := N) q0)
    {k1 : ℕ} (q1 : Fin k1 → JumpVec N) (i : Fin N) :
    (0 : ℤ) + (SwarmSegKernel.segOf y k0 q0).p (SwarmSegKernel.segOf y k0 q0).dur i
      = ((0 + 1 : ℕ) : ℤ) + (SwarmSegKernel.segOf y k1 q1).p 0 i := by
  rw [SwarmFreshCyl.segOf_dur_of_firstRecord hk0 q0 hfr0,
    seg_end_eq_one hm hN hy hk0 q0 hfr0 hq0 i, SwarmSegKernel.segOf_p_zero_srSet hy k1 q1 i]
  push_cast

/-! ## 7. Independence corollaries: endpoint and start state -/

/-- **The conditional second-segment mass does not depend on the endpoint record state.**  Given the
first atom (a positive first-record word `q₀` from `y ∈ srSet`), the mass of the second segment
cylinder at the endpoint `out hm q₀ y` is the *same* first-segment cylinder mass read at any
simultaneous-record state `y'`.  This is the cylinder-level independence behind the product
identity: the condition "the first segment is the atom of `q₀`" changes nothing about the mass of
the second segment's cylinder. -/
theorem step2_segCyl_eq_start (p : ℝ) (hm : 1 ≤ m) (hN : 0 < N) {y y' : RecState N m}
    (hy : y ∈ srSet N m) (hy' : y' ∈ srSet N m) {k0 : ℕ} (hk0 : 0 < k0)
    (q0 : Fin k0 → JumpVec N)
    (hfr0 : Record.FirstRecord (Record.extendPath q0) k0 (Record.ofRecState y))
    (hq0 : SwarmFreshPos.PosSeqFin (N := N) q0)
    {k1 : ℕ} (hk1 : 0 < k1) (q1 : Fin k1 → JumpVec N)
    (hfr1 : Record.FirstRecord (Record.extendPath q1) k1 (Record.ofRecState y))
    (hq1 : SwarmFreshPos.PosSeqFin (N := N) q1) :
    (SwarmSegKernel.asegK p hm (RecKernel.out hm q0 y))
        {b : SwarmConcat.Seg N × RecState N m | b.1 = SwarmSegKernel.segOf y k1 q1}
      = (SwarmSegKernel.asegK p hm y')
        {b : SwarmConcat.Seg N × RecState N m | b.1 = SwarmSegKernel.segOf y' k1 q1} := by
  have hfr1' : Record.FirstRecord (Record.extendPath q1) k1 (Record.ofRecState y') :=
    (SwarmFreshCyl.firstRecord_ofRecState_iff hy' hy (Record.extendPath q1) k1).mpr hfr1
  rw [asegK_step2_segCyl p hm hN hy hk0 q0 hfr0 hq0 hk1 q1 hfr1 hq1,
    asegK_segCyl p hm hy' hk1 q1 hfr1',
    SwarmFreshCyl.hitW_eq_of_srSet hm hy hy' q1 hq1]

/-- **The two-step segment-cylinder mass does not depend on the start state either**, as long as the
start state is in `srSet` (and the two words are positive first-record words from it).  Both factors
of the product are state independent by `SwarmFreshCyl.hitW_eq_of_srSet`. -/
theorem twoSeg_joint_mass_state_indep (p : ℝ) (hm : 1 ≤ m) (hp : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1)
    (hN : 0 < N) {y y' : RecState N m} (hy : y ∈ srSet N m) (hy' : y' ∈ srSet N m)
    {k0 : ℕ} (hk0 : 0 < k0) (q0 : Fin k0 → JumpVec N)
    (hfr0 : Record.FirstRecord (Record.extendPath q0) k0 (Record.ofRecState y))
    (hq0 : SwarmFreshPos.PosSeqFin (N := N) q0)
    {k1 : ℕ} (hk1 : 0 < k1) (q1 : Fin k1 → JumpVec N)
    (hfr1 : Record.FirstRecord (Record.extendPath q1) k1 (Record.ofRecState y))
    (hq1 : SwarmFreshPos.PosSeqFin (N := N) q1) :
    (SwarmChain.chainVec (SwarmSegKernel.asegK p hm y) (SwarmSegKernel.pairK p hm) 2)
        {v : Fin 2 → (SwarmConcat.Seg N × RecState N m) |
          v 0 = (SwarmSegKernel.segOf y k0 q0, RecKernel.out hm q0 y) ∧
          (v 1).1 = SwarmSegKernel.segOf y k1 q1}
      = (SwarmChain.chainVec (SwarmSegKernel.asegK p hm y') (SwarmSegKernel.pairK p hm) 2)
        {v : Fin 2 → (SwarmConcat.Seg N × RecState N m) |
          v 0 = (SwarmSegKernel.segOf y' k0 q0, RecKernel.out hm q0 y') ∧
          (v 1).1 = SwarmSegKernel.segOf y' k1 q1} := by
  have hfr0' : Record.FirstRecord (Record.extendPath q0) k0 (Record.ofRecState y') :=
    (SwarmFreshCyl.firstRecord_ofRecState_iff hy' hy (Record.extendPath q0) k0).mpr hfr0
  have hfr1' : Record.FirstRecord (Record.extendPath q1) k1 (Record.ofRecState y') :=
    (SwarmFreshCyl.firstRecord_ofRecState_iff hy' hy (Record.extendPath q1) k1).mpr hfr1
  rw [twoSeg_joint_mass p hm hp hp1 hN hy hk0 q0 hfr0 hq0 hk1 q1 hfr1 hq1,
    twoSeg_joint_mass p hm hp hp1 hN hy' hk0 q0 hfr0' hq0 hk1 q1 hfr1' hq1,
    SwarmFreshCyl.hitW_eq_of_srSet hm hy hy' q0 hq0,
    SwarmFreshCyl.hitW_eq_of_srSet hm hy hy' q1 hq1]

end SwarmFreshTwoSeg
