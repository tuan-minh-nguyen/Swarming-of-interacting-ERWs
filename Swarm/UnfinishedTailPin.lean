/-
Completed enriched record prefixes followed by a genuinely unfinished raw tail.

The new section `unfinishedTailSet` observes the actual segment positions through
raw time `r`; it does not normalise the state at the cut.  The measured theorem
extends the accepted completed-prefix pin by exactly one `asegK` step.  No claim
is made that the section mass has already been summed to `pathW`.
-/
import Swarm.MeasuredEnrichedRawJoin
import Swarm.RawPositiveCover

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators
open SimJump

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace SwarmUnfinishedTail

open SimJump.Record SwarmRec SwarmRawRecord SwarmArrayWords SwarmSegKernel
open SwarmMeasuredJoin SwarmFreshPrefix

attribute [local instance] Classical.propDecidable

variable {N m : ℕ}

/-- The enriched next-record atoms whose genuine raw positions agree with `q`
through the cut.  The strict duration inequality puts the cut before completion
of the record, including when `r = 0`.  The state at time `r` remains the raw
`evolveFun` state; in particular it is not replaced by `RecKernel.out`. -/
noncomputable def unfinishedTailSet (z : RecState N m) {r : ℕ}
    (q : Fin r → JumpVec N) : Set (SwarmInfSeg.Pair N m) :=
  {a | r < a.1.dur ∧ ∀ t : Fin (r + 1), ∀ i : Fin N,
    a.1.p (t : ℕ) i = relP z (extendPath q) (t : ℕ) i}

/-- The cylinder with a fixed old prefix and an arbitrary measurable set for
its one new final atom. -/
def pinNext {β : Type*} (A : ℕ → β) (n : ℕ) (E : Set β) :
    Set (Fin (n + 1) → β) :=
  {v | SwarmChain.initF v ∈ pin A n ∧ v (Fin.last n) ∈ E}

@[simp] theorem mem_pinNext {β : Type*} {A : ℕ → β} {n : ℕ} {E : Set β}
    {v : Fin (n + 1) → β} :
    v ∈ pinNext A n E ↔ SwarmChain.initF v ∈ pin A n ∧ v (Fin.last n) ∈ E := Iff.rfl

/-- Measurability of the raw-cut enriched section. -/
theorem measurableSet_unfinishedTailSet (z : RecState N m) {r : ℕ}
    (q : Fin r → JumpVec N) : MeasurableSet (unfinishedTailSet z q) := by
  rw [show unfinishedTailSet z q =
      {a : SwarmInfSeg.Pair N m | r < a.1.dur} ∩
        ⋂ (t : Fin (r + 1)), ⋂ (i : Fin N),
          {a : SwarmInfSeg.Pair N m |
            a.1.p (t : ℕ) i = relP z (extendPath q) (t : ℕ) i} from by
    ext a
    simp [unfinishedTailSet]]
  refine MeasurableSet.inter ?_ ?_
  · exact measurableSet_lt measurable_const
      (SwarmConcat.measurable_seg_dur.comp measurable_fst)
  · exact MeasurableSet.iInter fun t => MeasurableSet.iInter fun i =>
      measurableSet_eq_fun
        ((SwarmConcat.measurable_seg_p (N := N) (t : ℕ) i).comp measurable_fst)
        measurable_const

/-- The totalised block sequence really ends at the accepted compact terminal
state. -/
theorem ep_blockSeq_length (hm : 1 ≤ m) (y : RecState N m) :
    ∀ bs : List (RawBlock N),
      ep hm y (blockSeq bs) bs.length = terminal hm y bs
  | [] => rfl
  | b :: bs => by
      rw [List.length_cons, ep_blockSeq_cons_succ, ep_blockSeq_length]
      rfl

/-- The second component of the last atom of a nonempty completed prefix is
its actual terminal state. -/
theorem atom_last_snd_terminal (hm : 1 ≤ m) (y : RecState N m)
    (b : RawBlock N) (bs : List (RawBlock N)) :
    (atom hm y (blockSeq (b :: bs)) bs.length).2 = terminal hm y (b :: bs) := by
  change ep hm y (blockSeq (b :: bs)) (bs.length + 1) = terminal hm y (b :: bs)
  exact ep_blockSeq_length hm y (b :: bs)

/-- **Exact pin-times-unfinished-section join.**  The first factor is the
accepted completed-record mass and the second is the actual next `asegK` law at
its actual terminal state.  `E` is arbitrary and measurable. -/
theorem chainVec_rawPrefix_pinNext_mass (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (y : RecState N m)
    (bs : List (RawBlock N)) (hbs : AllFirst hm y bs)
    {E : Set (SwarmInfSeg.Pair N m)} (hE : MeasurableSet E) :
    (SwarmChain.chainVec (SwarmSegKernel.asegK (N := N) p hm y)
        (SwarmSegKernel.pairK (N := N) p hm) (bs.length + 1))
        (pinNext (atom hm y (blockSeq bs)) bs.length E) =
      ENNReal.ofReal (prefixW p hm y bs) *
        (SwarmSegKernel.asegK (N := N) p hm (terminal hm y bs)) E := by
  classical
  letI hmark : IsMarkovKernel (SwarmSegKernel.pairK (N := N) (m := m) p hm) :=
    SwarmSegKernel.isMarkovKernel_pairK (N := N) (m := m) p hm hp hp1
  letI hprob : IsProbabilityMeasure (SwarmSegKernel.asegK (N := N) p hm y) :=
    SwarmSegKernel.isProbabilityMeasure_asegK p hm hp hp1 y
  have hpin : MeasurableSet (pin (atom hm y (blockSeq bs)) bs.length) :=
    measurableSet_pin (measurableSet_atom_singleton hm y (blockSeq bs)) bs.length
  have hnext : MeasurableSet (pinNext (atom hm y (blockSeq bs)) bs.length E) :=
    (SwarmChain.measurable_initF hpin).inter ((measurable_pi_apply _) hE)
  cases bs with
  | nil =>
      simp only [List.length_nil, Nat.zero_add] at hpin hnext ⊢
      have hpre : (fun a : SwarmInfSeg.Pair N m => fun _ : Fin 1 => a) ⁻¹'
          pinNext (atom hm y (blockSeq [])) 0 E = E := by
        ext a
        simp [pinNext, pin]
      rw [SwarmChain.chainVec_succ, SwarmChain.chainStep_zero,
        Measure.map_apply SwarmChain.measurable_fin1_const hnext, hpre]
      simp [prefixW, terminal]
  | cons b bs =>
      rw [List.length_cons]
      change (SwarmChain.chainVec (SwarmSegKernel.asegK (N := N) p hm y)
        (SwarmSegKernel.pairK (N := N) p hm) (bs.length + 2))
        {v | SwarmChain.initF v ∈ pin (atom hm y (blockSeq (b :: bs))) (bs.length + 1) ∧
          v (Fin.last (bs.length + 1)) ∈ E} = _
      have hpin' : MeasurableSet (pin (atom hm y (blockSeq (b :: bs))) (bs.length + 1)) := by
        simpa using hpin
      rw [chainVec_snoc_apply _ _ _ hpin' hE]
      rw [setLIntegral_congr_fun hpin'  (fun w hw => by rw [mem_pin_last hw])]
      rw [setLIntegral_const]
      have hcompleted :
          (SwarmChain.chainVec (SwarmSegKernel.asegK (N := N) p hm y)
            (SwarmSegKernel.pairK (N := N) p hm) (bs.length + 1))
            (pin (atom hm y (blockSeq (b :: bs))) (bs.length + 1)) =
            ENNReal.ofReal (prefixW p hm y (b :: bs)) := by
        simpa using chainVec_rawPrefix_pin_mass p hm hp hp1 y (b :: bs) hbs
      rw [hcompleted, SwarmSegKernel.pairK_apply, atom_last_snd_terminal]
      exact mul_comm _ _

/-- Specialisation to the genuinely unfinished raw-cut section. -/
theorem chainVec_rawPrefix_unfinishedTail_mass (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (y : RecState N m)
    (bs : List (RawBlock N)) (hbs : AllFirst hm y bs)
    {r : ℕ} (q : Fin r → JumpVec N) :
    (SwarmChain.chainVec (SwarmSegKernel.asegK (N := N) p hm y)
        (SwarmSegKernel.pairK (N := N) p hm) (bs.length + 1))
        (pinNext (atom hm y (blockSeq bs)) bs.length
          (unfinishedTailSet (terminal hm y bs) q)) =
      ENNReal.ofReal (prefixW p hm y bs) *
        (SwarmSegKernel.asegK (N := N) p hm (terminal hm y bs))
          (unfinishedTailSet (terminal hm y bs) q) := by
  exact chainVec_rawPrefix_pinNext_mass p hm hp hp1 y bs hbs
    (measurableSet_unfinishedTailSet (terminal hm y bs) q)

/-- A first-record completion of a no-record prefix lands in the geometric
raw-cut section.  Only positions through `r` are constrained; duration, later
positions, and the final `RecKernel.out` are retained freely. -/
theorem segOf_catWord_mem_unfinishedTailSet (hm : 1 ≤ m) (z : RecState N m)
    {r s : ℕ} (q : Fin r → JumpVec N) (qs : Fin s → JumpVec N)
    (hq : NoRecordPrefix (ofRecState z) q)
    (hfr : FirstRecord (extendPath (catWord q qs)) (r + s) (ofRecState z)) :
    (SwarmSegKernel.segOf z (r + s) (catWord q qs),
      RecKernel.out hm (catWord q qs) z) ∈ unfinishedTailSet z q := by
  have hk : 0 < r + s := SwarmDHStruct.firstRecord_ne_zero hfr
  have he : ∀ t, t ≤ r →
      evolveFun (extendPath (catWord q qs)) t (ofRecState z) =
        evolveFun (extendPath q) t (ofRecState z) := by
    intro t ht
    exact evolveFun_congr_prefix
      (fun j hj => extendPath_catWord_left q qs (by omega)) (ofRecState z)
  have hcut : r < r + s := by
    by_contra h
    have hle : r + s ≤ r := by omega
    apply hq (r + s) hk hle
    rcases hfr with ⟨⟨i, hi⟩, hlt⟩
    refine ⟨⟨i, ?_⟩, ?_⟩
    · rw [← he (r + s) hle]
      exact hi
    · intro t ht j
      have htr : t ≤ r := by omega
      rw [← he t htr]
      exact hlt t ht j
  have hseg : SwarmSegKernel.segOf z (r + s) (catWord q qs) =
      SwarmSegKernel.segOfFirst z (r + s) (catWord q qs) hk hfr := by
    rw [SwarmSegKernel.segOf, dif_pos ⟨hk, hfr⟩]
  refine ⟨?_, ?_⟩
  · change r < (SwarmSegKernel.segOf z (r + s) (catWord q qs)).dur
    rw [hseg]
    exact hcut
  · intro t i
    change (SwarmSegKernel.segOf z (r + s) (catWord q qs)).p (t : ℕ) i = _
    rw [hseg]
    change relP z (extendPath (catWord q qs)) (t : ℕ) i = _
    have ht : (t : ℕ) ≤ r := by omega
    unfold relP
    rw [he (t : ℕ) ht]

/-- Every `segOf` atom has positive duration, including the zero-weight junk
branch. -/
theorem segOf_dur_pos (z : RecState N m) (k : ℕ) (q : Fin k → JumpVec N) :
    0 < (SwarmSegKernel.segOf z k q).dur := by
  rw [SwarmSegKernel.segOf]
  split_ifs with h
  · exact h.1
  · exact (SwarmSegKernel.dummySeg z).dur_pos

/-- Zero-length tails impose only the genuine common start, which every actual
`segOf` atom satisfies. -/
theorem segOf_mem_unfinishedTailSet_zero (hm : 1 ≤ m) (z : RecState N m)
    (k : ℕ) (qs : Fin k → JumpVec N) :
    (SwarmSegKernel.segOf z k qs, RecKernel.out hm qs z) ∈
      unfinishedTailSet z (fun i : Fin 0 => Fin.elim0 i) := by
  refine ⟨segOf_dur_pos z k qs, ?_⟩
  intro t i
  have ht : (t : ℕ) = 0 := by omega
  rw [ht, SwarmSegKernel.segOf_p_zero, relP_zero]


/-- The measured zero-length marginal is exactly one: no completion sum or
normalisation at the cut is needed. -/
theorem asegK_unfinishedTailSet_zero (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (z : RecState N m) :
    (SwarmSegKernel.asegK (N := N) p hm z)
      (unfinishedTailSet z (fun i : Fin 0 => Fin.elim0 i)) = 1 := by
  calc
    (SwarmSegKernel.asegK (N := N) p hm z)
        (unfinishedTailSet z (fun i : Fin 0 => Fin.elim0 i)) =
        (SwarmSegKernel.asegK (N := N) p hm z) Set.univ := by
      rw [SwarmSegKernel.asegK_apply p hm z
          (measurableSet_unfinishedTailSet z (fun i : Fin 0 => Fin.elim0 i)),
        SwarmSegKernel.asegK_apply p hm z MeasurableSet.univ]
      apply tsum_congr
      rintro ⟨k, qs⟩
      simp [segOf_mem_unfinishedTailSet_zero hm z k qs]
    _ = 1 := SwarmSegKernel.asegK_univ p hm hp hp1 z

/-- The same zero-length marginal is the genuine empty raw-path weight. -/
theorem asegK_unfinishedTailSet_zero_eq_pathW (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (z : RecState N m) :
    (SwarmSegKernel.asegK (N := N) p hm z)
      (unfinishedTailSet z (fun i : Fin 0 => Fin.elim0 i)) =
        ENNReal.ofReal (pathW p 0 (fun i : Fin 0 => Fin.elim0 i) (ofRecState z)) := by
  rw [asegK_unfinishedTailSet_zero p hm hp hp1 z]
  simp [pathW]

end SwarmUnfinishedTail
