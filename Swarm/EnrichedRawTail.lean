/-
The enriched marginal of a genuinely unfinished finite raw tail.

The event reads the jumps decoded from the next genuine record segment up to
an interior cut. It does not invent a compact record state at that cut.
`NoRecordPrefix` supplies the first-passage geometry needed to split the next
record at the actual, unnormalised raw successor. All later durations and
endpoints are summed.
-/
import Swarm.ReturnMass
import Swarm.RawPositivePartition

open MeasureTheory Set
open scoped ENNReal BigOperators
open SimJump

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace SwarmEnrichedRawTail

open SimJump.Record SwarmRec SwarmFreshArray SwarmArrayWords SwarmRawRecord

attribute [local instance] Classical.propDecidable

variable {N m : ℕ}

/-- The `n`-th jump decoded from the nearest-neighbour steps of a segment.
Beyond the duration this is merely a totalisation; the tail event below is
strictly inside the segment. -/
def segJump (s : SwarmConcat.Seg N) (n : ℕ) : JumpVec N :=
  fun i => decide (s.p (n + 1) i = s.p n i + 1)

/-- The fixed raw prefix of a segment, with its duration left entirely free. -/
def TailPrefixSet {r : ℕ} (q : Fin r → JumpVec N) : Set (SwarmInfSeg.Pair N m) :=
  {a | r < a.1.dur ∧ ∀ j : Fin r, segJump a.1 j = q j}

/-- The first `r` jumps of a raw word, totalised only through a strict-length
proof. -/
def HasRawPrefix {r k : ℕ} (q : Fin r → JumpVec N) (w : Fin k → JumpVec N) : Prop :=
  ∃ h : r < k, ∀ j : Fin r, w ⟨j.1, Nat.lt_trans j.2 h⟩ = q j

/-- Every decoded coordinate is measurable. -/
theorem measurable_segJump (n : ℕ) : Measurable (fun s : SwarmConcat.Seg N => segJump s n) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_to_bool
  have hset : (fun s : SwarmConcat.Seg N => segJump s n i) ⁻¹' {true} =
      {s | s.p (n + 1) i = s.p n i + 1} := by
    ext s
    simp [segJump]
  rw [hset]
  exact measurableSet_eq_fun (SwarmConcat.measurable_seg_p (n + 1) i)
    ((SwarmConcat.measurable_seg_p n i).add measurable_const)

/-- An unfinished decoded-prefix cylinder is measurable. -/
theorem measurableSet_tailPrefixSet {r : ℕ} (q : Fin r → JumpVec N) :
    MeasurableSet (TailPrefixSet (N := N) (m := m) q) := by
  rw [show TailPrefixSet (N := N) (m := m) q =
      {a : SwarmInfSeg.Pair N m | r < a.1.dur} ∩
        ⋂ j : Fin r, {a : SwarmInfSeg.Pair N m | segJump a.1 j = q j} from by
    ext a
    simp [TailPrefixSet]]
  exact (measurableSet_lt measurable_const
    (SwarmConcat.measurable_seg_dur.comp measurable_fst)).inter
      (MeasurableSet.iInter fun j => measurableSet_eq_fun
        ((measurable_segJump j.1).comp measurable_fst) measurable_const)

/-- Decoding a genuine first-record segment recovers each original jump. -/
theorem segJump_segOf (z : RecState N m) {k : ℕ} (hk : 0 < k)
    (w : Fin k → JumpVec N)
    (hw : FirstRecord (extendPath w) k (ofRecState z)) (j : Fin k) :
    segJump (SwarmSegKernel.segOf z k w) j.1 = w j := by
  change (fun i => decide
    ((SwarmSegKernel.segOf z k w).p (j.1 + 1) i =
      (SwarmSegKernel.segOf z k w).p j.1 i + 1)) = w j
  rw [SwarmSegKernel.segOf, dif_pos ⟨hk, hw⟩]
  change (fun i => decide
    ((evolveFun (extendPath w) (j.1 + 1) (ofRecState z)).pos i =
      (evolveFun (extendPath w) j.1 (ofRecState z)).pos i + 1)) = w j
  funext i
  rw [evolveFun_succ, step_pos]
  unfold stepPos
  simp only [extendPath, dif_pos j.2]
  cases w j i <;> simp

/-- For genuine first-record atoms, the enriched decoded-prefix event is
literally the raw-prefix predicate. -/
theorem mem_tailPrefixSet_segOf_iff (hm : 1 ≤ m) (z : RecState N m) {k : ℕ} (hk : 0 < k)
    (w : Fin k → JumpVec N)
    (hw : FirstRecord (extendPath w) k (ofRecState z)) {r : ℕ}
    (q : Fin r → JumpVec N) :
    (SwarmSegKernel.segOf z k w, RecKernel.out hm w z) ∈ TailPrefixSet q ↔
      HasRawPrefix q w := by
  have hd : (SwarmSegKernel.segOf z k w).dur = k :=
    SwarmFreshCyl.segOf_dur_of_firstRecord hk w hw
  constructor
  · rintro ⟨hr, hjw⟩
    refine ⟨hd ▸ hr, ?_⟩
    intro j
    have hj := hjw j
    rw [segJump_segOf z hk w hw ⟨j.1, Nat.lt_trans j.2 (hd ▸ hr)⟩] at hj
    exact hj
  · rintro ⟨hr, hjw⟩
    refine ⟨hd.symm ▸ hr, ?_⟩
    intro j
    rw [segJump_segOf z hk w hw ⟨j.1, Nat.lt_trans j.2 hr⟩]
    exact hjw j

/-- The genuine segment's position path through the cut is exactly the raw
path of the fixed prefix, including at time `r`. -/
theorem segOf_p_of_rawPrefix (z : RecState N m) {k r : ℕ} (hk : 0 < k)
    (w : Fin k → JumpVec N) (hw : FirstRecord (extendPath w) k (ofRecState z))
    {q : Fin r → JumpVec N} (hpre : HasRawPrefix q w) {t : ℕ} (ht : t ≤ r) (i : Fin N) :
    (SwarmSegKernel.segOf z k w).p t i =
      (evolveFun (extendPath q) t (ofRecState z)).pos i := by
  obtain ⟨hr, hq⟩ := hpre
  rw [SwarmFreshCyl.segOf_p_of_firstRecord hk w hw]
  apply congrArg (fun s : State N m => s.pos i)
  apply evolveFun_congr_prefix (k := t)
  intro j hj
  have hjr : j < r := Nat.lt_of_lt_of_le hj ht
  have hjk : j < k := Nat.lt_trans hjr hr
  simp only [extendPath, dif_pos hjr, dif_pos hjk]
  exact hq ⟨j, hjr⟩

/-- The exact enriched tail-cylinder expansion before summing over completions. -/
theorem asegK_tailPrefixSet_eq_tsum (p : ℝ) (hm : 1 ≤ m) (z : RecState N m)
    {r : ℕ} (q : Fin r → JumpVec N) :
    SwarmSegKernel.asegK (N := N) p hm z (TailPrefixSet q) =
      ∑' pq : (k : ℕ) × (Fin k → JumpVec N),
        ENNReal.ofReal (RecKernel.hitW p pq.2 z) *
          if HasRawPrefix q pq.2 then 1 else 0 := by
  classical
  rw [SwarmSegKernel.asegK_apply p hm z (measurableSet_tailPrefixSet q)]
  apply tsum_congr
  rintro ⟨k, w⟩
  by_cases hw : FirstRecord (extendPath w) k (ofRecState z)
  · rw [(mem_tailPrefixSet_segOf_iff (hm := hm) z
      (SwarmDHStruct.firstRecord_ne_zero hw) w hw q)]
  · rw [RecKernel.hitW_of_not_firstRecord p w z hw]
    simp


/-- Reindex a raw completion by its suffix after the fixed prefix. -/
noncomputable def prependRawBlock {r : ℕ} (q : Fin r → JumpVec N)
    (c : (s : ℕ) × (Fin s → JumpVec N)) : (k : ℕ) × (Fin k → JumpVec N) :=
  ⟨r + c.1, catWord q c.2⟩

/-- Prefixing the same fixed word is injective on dependent word pairs. -/
theorem prependRawBlock_injective {r : ℕ} (q : Fin r → JumpVec N) :
    Function.Injective (prependRawBlock (N := N) q) := by
  rintro ⟨s, qs⟩ ⟨t, qt⟩ h
  have hst : s = t := by
    have hlen := congrArg Sigma.fst h
    dsimp [prependRawBlock] at hlen
    omega
  subst t
  have hcat : catWord q qs = catWord q qt := by
    injection h
  have hsuff := congrArg
    (fun w : Fin (r + s) → JumpVec N => suffWord (k1 := r) (k2 := s) w) hcat
  rw [suffWord_catWord, suffWord_catWord] at hsuff
  cases hsuff
  rfl

/-- A raw word with the fixed strict prefix has a unique suffix representation. -/
theorem prependRawBlock_surjective_on_prefix {r : ℕ} (q : Fin r → JumpVec N)
    {k : ℕ} (w : Fin k → JumpVec N) (hw : HasRawPrefix q w) :
    ∃ c, prependRawBlock q c = ⟨k, w⟩ := by
  obtain ⟨hr, hpre⟩ := hw
  let qs : Fin (k - r) → JumpVec N := fun j => w ⟨r + j.1, by omega⟩
  refine ⟨⟨k - r, qs⟩, ?_⟩
  dsimp [prependRawBlock]
  apply rawBlock_ext (show r + (k - r) = k by omega)
  intro j
  have hjraw : (j : ℕ) < r + (k - r) := j.2
  have hjk : (j : ℕ) < k := by omega
  by_cases hj : (j : ℕ) < r
  · change (catWord q qs) j = w ⟨j.1, hjk⟩
    rw [catWord, dif_pos hj]
    exact (hpre ⟨j.1, hj⟩).symm
  · change (catWord q qs) j = w ⟨j.1, hjk⟩
    rw [catWord, dif_neg hj]
    simp only [qs]
    congr 1
    apply Fin.ext
    simp only
    omega

/-- A no-record-prefix word stays below the record level at every time through
its endpoint. This is a first-passage consequence, not part of the defining
syntax of `NoRecordPrefix`. -/
theorem noRecordPrefix_pos_nonpos {r : ℕ} (q : Fin r → JumpVec N) (z : RecState N m)
    (hq : NoRecordPrefix (ofRecState z) q) :
    ∀ t, t ≤ r → ∀ i, (evolveFun (extendPath q) t (ofRecState z)).pos i ≤ 0 := by
  have hstart : ∀ i, (ofRecState z).pos i ≤ 0 :=
    SwarmSegKernel.ofRecState_pos_nonpos z
  have hno : ∀ n ≤ r, ¬ RecKernel.IsRec (evolveFun (extendPath q) n (ofRecState z)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro hn hrec
        cases n with
        | zero =>
            obtain ⟨i, hi⟩ := hrec
            have hle := hstart i
            change (ofRecState z).pos i = 1 at hi
            omega
        | succ n =>
            apply hq (n + 1) (Nat.succ_pos n) hn
            apply RecKernel.firstRecord_of_isRec hstart
            refine ⟨hrec, ?_⟩
            intro l hl hlr
            exact ih l hl (by omega) hlr
  intro t ht
  exact RecKernel.pos_nonpos_of_no_rec hstart t
    (fun n hn => hno n (Nat.le_trans hn ht))

/-- Evolution after the prefix of a concatenation, at any intermediate suffix time. -/
theorem evolveFun_catWord_right {r s : ℕ} (q : Fin r → JumpVec N)
    (qs : Fin s → JumpVec N) (z : State N m) (t : ℕ) :
    evolveFun (extendPath (catWord q qs)) (r + t) z =
      evolveFun (extendPath qs) t (evolveFun (extendPath q) r z) := by
  rw [SwarmArrayWords.evolveFun_shift]
  have hleft : ∀ j, j < r → extendPath (catWord q qs) j = extendPath q j :=
    fun _ hj => extendPath_catWord_left q qs hj
  have hright : (fun n => extendPath (catWord q qs) (r + n)) = extendPath qs := by
    funext n
    by_cases hn : n < s
    · exact extendPath_catWord_right q qs hn
    · simp only [extendPath, dif_neg hn,
        dif_neg (show ¬ r + n < r + s by omega)]
  rw [hright, evolveFun_congr_prefix hleft]

/-- Split the next genuine first record at an unfinished prefix. The right
side uses the actual raw successor; in particular it is not `ofRecState` of a
new compact state. -/
theorem firstRecord_catWord_of_noRecordPrefix {r s : ℕ} (q : Fin r → JumpVec N)
    (qs : Fin s → JumpVec N) (z : RecState N m)
    (hq : NoRecordPrefix (ofRecState z) q) :
    FirstRecord (extendPath (catWord q qs)) (r + s) (ofRecState z) ↔
      0 < s ∧ FirstRecord (extendPath qs) s
        (evolveFun (extendPath q) r (ofRecState z)) := by
  have hnonpos := noRecordPrefix_pos_nonpos q z hq
  constructor
  · intro hfull
    have hs : 0 < s := by
      by_contra hs
      have hs0 : s = 0 := Nat.eq_zero_of_not_pos hs
      subst s
      have hcat : catWord q qs = q := by
        funext j
        simp [catWord]
      have hfirst : FirstRecord (extendPath q) r (ofRecState z) := by
        simpa only [Nat.add_zero, hcat] using hfull
      exact hq r (SwarmDHStruct.firstRecord_ne_zero hfirst) le_rfl hfirst
    refine ⟨hs, ?_⟩
    constructor
    · obtain ⟨i, hi⟩ := hfull.1
      refine ⟨i, ?_⟩
      rw [← evolveFun_catWord_right q qs]
      exact hi
    · intro t ht i
      rw [← evolveFun_catWord_right q qs]
      exact hfull.2 (r + t) (by omega) i
  · rintro ⟨hs, ⟨hend, hprev⟩⟩
    constructor
    · obtain ⟨i, hi⟩ := hend
      refine ⟨i, ?_⟩
      rw [evolveFun_catWord_right q qs]
      exact hi
    · intro t ht i
      rcases Nat.lt_or_ge t r with htr | hrt
      · rw [evolveFun_congr_prefix (k := t)
          (u := extendPath (catWord q qs)) (v := extendPath q)
          (fun j hj => extendPath_catWord_left q qs (Nat.lt_trans hj htr))]
        exact hnonpos t (Nat.le_of_lt htr) i
      · have heq : t = r + (t - r) := by omega
        rw [heq, evolveFun_catWord_right q qs]
        exact hprev (t - r) (by omega) i

/-- Pointwise weight after completing an unfinished prefix. -/
theorem prependRawBlock_weight (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    {r s : ℕ} (q : Fin r → JumpVec N) (qs : Fin s → JumpVec N) (z : RecState N m)
    (hq : NoRecordPrefix (ofRecState z) q) :
    ENNReal.ofReal (RecKernel.hitW p (catWord q qs) z) *
        (if HasRawPrefix q (catWord q qs) then 1 else 0) =
      if 0 < s then
        ENNReal.ofReal (pathW p r q (ofRecState z)) *
          ENNReal.ofReal (SwarmFinHorizon.Return.hitWState p qs
            (evolveFun (extendPath q) r (ofRecState z)))
      else 0 := by
  by_cases hs : 0 < s
  · have hprefix : HasRawPrefix q (catWord q qs) := by
      refine ⟨by omega, ?_⟩
      intro j
      simp only [catWord, dif_pos j.2]
    rw [if_pos hprefix, if_pos hs, mul_one]
    by_cases hfr : FirstRecord (extendPath qs) s
        (evolveFun (extendPath q) r (ofRecState z))
    · have hfull : FirstRecord (extendPath (catWord q qs)) (r + s) (ofRecState z) :=
        (firstRecord_catWord_of_noRecordPrefix q qs z hq).mpr ⟨hs, hfr⟩
      rw [RecKernel.hitW_of_firstRecord p _ z hfull,
        SwarmFinHorizon.Return.hitWState_of_firstRecord p _ _ hfr,
        pathW_catWord, ENNReal.ofReal_mul (pathW_nonneg p hp hp1 r q _)]
    · have hfull : ¬ FirstRecord (extendPath (catWord q qs)) (r + s) (ofRecState z) :=
        fun h => hfr ((firstRecord_catWord_of_noRecordPrefix q qs z hq).mp h).2
      rw [RecKernel.hitW_of_not_firstRecord p _ z hfull]
      simp [SwarmFinHorizon.Return.hitWState, hfr]
  · have hs0 : s = 0 := Nat.eq_zero_of_not_pos hs
    subst s
    have hprefix : ¬ HasRawPrefix q (catWord q qs) := by
      rintro ⟨hr, -⟩
      omega
    rw [if_neg hprefix, if_neg hs]
    simp


/-- There is no stopped zero-step continuation at the raw endpoint of an
unfinished prefix. -/
theorem hitWState_zero_of_noRecordPrefix {r : ℕ} (q : Fin r → JumpVec N)
    (z : RecState N m) (hq : NoRecordPrefix (ofRecState z) q)
    (qs : Fin 0 → JumpVec N) (p : ℝ) :
    SwarmFinHorizon.Return.hitWState p qs
      (evolveFun (extendPath q) r (ofRecState z)) = 0 := by
  rw [SwarmFinHorizon.Return.hitWState, if_neg]
  intro h
  obtain ⟨i, hi⟩ := h.1
  have hle := noRecordPrefix_pos_nonpos q z hq r le_rfl i
  change (evolveFun (extendPath q) r (ofRecState z)).pos i = 1 at hi
  omega

/-- **Measured enriched marginal of a genuinely unfinished raw tail.**  The
set charges exactly the next enriched record atoms whose decoded jumps agree
with `q` through the strict interior cut. Its mass is the raw `pathW` at the
fixed compact start. All remaining duration, jumps and compact endpoints are
summed; no record-state normalization is imposed at the cut. -/
theorem asegK_tailPrefixSet_mass (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (hm : 1 ≤ m) (z : RecState N m) {r : ℕ} (q : Fin r → JumpVec N)
    (hq : NoRecordPrefix (ofRecState z) q) :
    SwarmSegKernel.asegK (N := N) p hm z (TailPrefixSet q) =
      ENNReal.ofReal (pathW p r q (ofRecState z)) := by
  classical
  let f : ((k : ℕ) × (Fin k → JumpVec N)) → ℝ≥0∞ := fun pq =>
    ENNReal.ofReal (RecKernel.hitW p pq.2 z) * if HasRawPrefix q pq.2 then 1 else 0
  have hsupp : Function.support f ⊆ Set.range (prependRawBlock (N := N) q) := by
    rintro ⟨k, w⟩ hf
    have hpre : HasRawPrefix q w := by
      by_contra hn
      exact hf (by simp [f, hn])
    exact prependRawBlock_surjective_on_prefix q w hpre
  have hreindex :
      (∑' c : (s : ℕ) × (Fin s → JumpVec N), f (prependRawBlock q c)) = ∑' pq, f pq :=
    (prependRawBlock_injective q).tsum_eq hsupp
  rw [asegK_tailPrefixSet_eq_tsum p hm z q, ← hreindex]
  let raw : State N m := evolveFun (extendPath q) r (ofRecState z)
  let g : ((s : ℕ) × (Fin s → JumpVec N)) → ℝ≥0∞ := fun c =>
    ENNReal.ofReal (SwarmFinHorizon.Return.hitWState p c.2 raw)
  calc
    (∑' c : (s : ℕ) × (Fin s → JumpVec N), f (prependRawBlock q c)) =
        ∑' c : (s : ℕ) × (Fin s → JumpVec N),
          (if 0 < c.1 then ENNReal.ofReal (pathW p r q (ofRecState z)) * g c else 0) := by
      apply tsum_congr
      rintro ⟨s, qs⟩
      exact prependRawBlock_weight p hp hp1 q qs z hq
    _ = ∑' c : (s : ℕ) × (Fin s → JumpVec N),
          ENNReal.ofReal (pathW p r q (ofRecState z)) * g c := by
      rw [ENNReal.tsum_sigma']
      rw [ENNReal.tsum_sigma' (fun c : (s : ℕ) × (Fin s → JumpVec N) =>
        ENNReal.ofReal (pathW p r q (ofRecState z)) * g c)]
      apply tsum_congr
      intro s
      by_cases hs : 0 < s
      · simp only [hs, if_true]
      · have hs0 : s = 0 := Nat.eq_zero_of_not_pos hs
        subst s
        have hzero : ∀ qs : Fin 0 → JumpVec N,
            SwarmFinHorizon.Return.hitWState p qs raw = 0 := by
          intro qs
          exact hitWState_zero_of_noRecordPrefix q z hq qs p
        simp [g, hzero]
    _ = ENNReal.ofReal (pathW p r q (ofRecState z)) * ∑' c, g c := by
      rw [← ENNReal.tsum_mul_left]
    _ = ENNReal.ofReal (pathW p r q (ofRecState z)) := by
      have hraw : ∀ i, raw.pos i ≤ 0 := by
        intro i
        exact noRecordPrefix_pos_nonpos q z hq r le_rfl i
      obtain ⟨i₀, -⟩ := (Record.ofRecState_recordStart z hm).exists_zero
      let b : ℕ := (1 - raw.pos i₀).toNat
      have hbz : 0 ≤ 1 - raw.pos i₀ := by
        have := hraw i₀
        omega
      have hbcast : (b : ℤ) = 1 - raw.pos i₀ := Int.toNat_of_nonneg hbz
      have hb : 1 ≤ b := by
        have hb' : (1 : ℤ) ≤ (b : ℤ) := by
          rw [hbcast]
          have hi := hraw i₀
          linarith
        exact_mod_cast hb'
      have hpos : raw.pos i₀ = 1 - (b : ℤ) := by
        rw [hbcast]
        ring
      rw [show (∑' c, g c) = 1 from
        SwarmFinHorizon.Return.tsum_hitWState_ofReal_eq_one
          p hp hp1 raw hraw hb hpos, mul_one]

/-- The empty-tail event has unit mass: on first-record support its length
condition is automatic, and its raw prefix weight is one. -/
theorem asegK_tailPrefixSet_mass_zero (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (hm : 1 ≤ m) (z : RecState N m) (q : Fin 0 → JumpVec N) :
    SwarmSegKernel.asegK (N := N) p hm z (TailPrefixSet q) = 1 := by
  have hq : NoRecordPrefix (ofRecState z) q := by
    intro k hk hkr
    omega
  rw [asegK_tailPrefixSet_mass p hp hp1 hm z q hq]
  change ENNReal.ofReal (pathW p 0 q (ofRecState z)) = 1
  rw [show pathW p 0 q (ofRecState z) = 1 from rfl]
  simp

/-- If the fixed raw prefix itself has zero weight, then so does its enriched
marginal; no positive completion is manufactured by the continuation sum. -/
theorem asegK_tailPrefixSet_mass_of_pathW_eq_zero (p : ℝ)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m) (z : RecState N m)
    {r : ℕ} (q : Fin r → JumpVec N) (hq : NoRecordPrefix (ofRecState z) q)
    (hw : pathW p r q (ofRecState z) = 0) :
    SwarmSegKernel.asegK (N := N) p hm z (TailPrefixSet q) = 0 := by
  rw [asegK_tailPrefixSet_mass p hp hp1 hm z q hq, hw]
  simp

end SwarmEnrichedRawTail
