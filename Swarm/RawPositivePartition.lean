/-
Disjoint maximal-record decomposition of arbitrary finite raw words.

The cover module supplies existence.  Here first-record time uniqueness is used
to show that the decomposition is unique, so its fibres are genuinely disjoint.
Positivity and arbitrary terminal pattern conditions are predicates on the
reassembled whole word, never on individual excursions.
-/
import Swarm.RawPositiveCover

open MeasureTheory Set
open scoped ENNReal BigOperators
open SimJump

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace SwarmRawRecord

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Transition Swarming.CurrentState
open SimJump.Record SwarmRec SwarmFreshArray SwarmArrayWords SwarmFinHorizon SwarmFreshPos SwarmRestart

attribute [local instance] Classical.propDecidable

variable {N m : ℕ}

/-- Two first-record times on one infinite path and one initial state agree. -/
theorem firstRecord_time_unique {u : ℕ → JumpVec N} {k l : ℕ} {s : State N m}
    (hk : FirstRecord u k s) (hl : FirstRecord u l s) : k = l := by
  rcases lt_trichotomy k l with hkl | hkl | hlk
  · obtain ⟨i, hi⟩ := hk.1
    have hle := hl.2 k hkl i
    omega
  · exact hkl
  · obtain ⟨i, hi⟩ := hl.1
    have hle := hk.2 l hlk i
    omega

/-- A first record at a genuine record state cannot occur at time zero, even
when the recorded time is internal to a longer finite word. -/
theorem firstRecord_time_pos_recordState {hm : 1 ≤ m} {y : RecState N m} {K k : ℕ}
    (q : Fin K → JumpVec N) (h : FirstRecord (extendPath q) k (ofRecState y)) : 0 < k := by
  cases k with
  | succ k => exact Nat.succ_pos k
  | zero =>
      obtain ⟨i, hi⟩ := h.1
      change (ofRecState y).pos i = 1 at hi
      have hle := (ofRecState_recordStart y hm).nonpos i
      omega

/-- Length transport does not change the infinite extension before the horizon. -/
theorem extendPath_castWord {K L : ℕ} (h : K = L) (q : Fin K → JumpVec N)
    {j : ℕ} (hj : j < L) :
    extendPath (castWord h q) j = extendPath q j := by
  simp [extendPath, castWord, hj, show j < K by omega]

/-- A first-record initial block stays first-record after arbitrary continuation. -/
theorem firstRecord_catWord_left {k r : ℕ} (qf : Fin k → JumpVec N)
    (q : Fin r → JumpVec N) (s : State N m)
    (h : FirstRecord (extendPath qf) k s) :
    FirstRecord (extendPath (catWord qf q)) k s := by
  have he : ∀ t, t ≤ k → evolveFun (extendPath (catWord qf q)) t s =
      evolveFun (extendPath qf) t s := by
    intro t ht
    exact evolveFun_congr_prefix
      (fun j hj => extendPath_catWord_left qf q (by omega)) s
  constructor
  · obtain ⟨i, hi⟩ := h.1
    refine ⟨i, ?_⟩
    rw [he k le_rfl]
    exact hi
  · intro t ht i
    rw [he t (Nat.le_of_lt ht)]
    exact h.2 t ht i

/-- A length-transported word has exactly the same first-record property. -/
theorem firstRecord_castWord {K L k : ℕ} (h : K = L) (q : Fin K → JumpVec N)
    (s : State N m) (hk : k ≤ L) :
    FirstRecord (extendPath (castWord h q)) k s ↔ FirstRecord (extendPath q) k s := by
  have he : ∀ t, t ≤ k → evolveFun (extendPath (castWord h q)) t s =
      evolveFun (extendPath q) t s := by
    intro t ht
    exact evolveFun_congr_prefix
      (fun j hj => extendPath_castWord h q (by omega)) s
  constructor <;> intro hq
  · constructor
    · obtain ⟨i, hi⟩ := hq.1
      refine ⟨i, ?_⟩
      rw [← he k le_rfl]
      exact hi
    · intro t ht i
      rw [← he t (Nat.le_of_lt ht)]
      exact hq.2 t ht i
  · constructor
    · obtain ⟨i, hi⟩ := hq.1
      refine ⟨i, ?_⟩
      rw [he k le_rfl]
      exact hi
    · intro t ht i
      rw [he t (Nat.le_of_lt ht)]
      exact hq.2 t ht i

/-- On a decomposition whose completed list starts with `b`, its reassembled
word has the same first-record excursion `b`. -/
theorem firstRecord_decompWord_of_completed_cons {hm : 1 ≤ m} {y : RecState N m}
    {K : ℕ} (d : MaxRecordDecomp (N := N) hm y K) {b : RawBlock N}
    {bs : List (RawBlock N)} (hd : d.completed = b :: bs) :
    FirstRecord (extendPath (decompWord d)) b.1 (ofRecState y) := by
  have hall := d.allFirst
  rw [hd] at hall
  have hb : b.1 ≤ K := by
    have hlen := d.len_eq
    rw [hd] at hlen
    simp only [rawLen] at hlen
    omega
  have hext : ∀ j, j < b.1 →
      extendPath (decompWord d) j = extendPath b.2 j := by
    intro j hj
    rw [decompWord, extendPath_castWord _ _ (by omega : j < K)]
    rw [hd]
    change extendPath (catWord (catWord b.2 (rawWord bs)) d.tail.2) j = extendPath b.2 j
    rw [extendPath_catWord_left _ _ (show j < b.1 + rawLen bs by omega)]
    exact extendPath_catWord_left b.2 (rawWord bs) hj
  have he : ∀ t, t ≤ b.1 →
      evolveFun (extendPath (decompWord d)) t (ofRecState y) =
        evolveFun (extendPath b.2) t (ofRecState y) := by
    intro t ht
    exact evolveFun_congr_prefix (fun j hj => hext j (by omega)) _
  constructor
  · obtain ⟨i, hi⟩ := hall.1.1
    refine ⟨i, ?_⟩
    rw [he b.1 le_rfl]
    exact hi
  · intro t ht i
    rw [he t (Nat.le_of_lt ht)]
    exact hall.1.2 t ht i


/-- Extensionality of raw blocks uses their common numerical indices. -/
theorem rawBlock_ext {b c : RawBlock N} (hlen : b.1 = c.1)
    (hword : ∀ j : Fin b.1, b.2 j = c.2 ⟨j.1, by omega⟩) : b = c := by
  cases b with
  | mk k q =>
      cases c with
      | mk l r =>
          dsimp at hlen
          subst l
          congr
          funext j
          simpa using hword j

/-- First-record status depends only on jumps strictly before its asserted time. -/
theorem firstRecord_of_extendPath_congr {K L k : ℕ}
    (q : Fin K → JumpVec N) (r : Fin L → JumpVec N) (s : State N m)
    (h : ∀ j, j < k → extendPath q j = extendPath r j)
    (hq : FirstRecord (extendPath q) k s) : FirstRecord (extendPath r) k s := by
  have he : ∀ t, t ≤ k → evolveFun (extendPath q) t s = evolveFun (extendPath r) t s := by
    intro t ht
    exact evolveFun_congr_prefix (fun j hj => h j (by omega)) s
  constructor
  · obtain ⟨i, hi⟩ := hq.1
    refine ⟨i, ?_⟩
    rw [← he k le_rfl]
    exact hi
  · intro t ht i
    rw [← he t (Nat.le_of_lt ht)]
    exact hq.2 t ht i

/-- The leading block of a decomposition is literally the corresponding prefix
of its reassembled infinite extension. -/
theorem extendPath_decompWord_of_completed_cons {hm : 1 ≤ m} {y : RecState N m}
    {K : ℕ} (d : MaxRecordDecomp (N := N) hm y K) {b : RawBlock N}
    {bs : List (RawBlock N)} (hd : d.completed = b :: bs) {j : ℕ} (hj : j < b.1) :
    extendPath (decompWord d) j = extendPath b.2 j := by
  have hb : b.1 ≤ K := by
    have hlen := d.len_eq
    rw [hd] at hlen
    simp only [rawLen] at hlen
    omega
  rw [decompWord, extendPath_castWord _ _ (by omega : j < K), hd]
  change extendPath (catWord (catWord b.2 (rawWord bs)) d.tail.2) j = extendPath b.2 j
  rw [extendPath_catWord_left _ _ (show j < b.1 + rawLen bs by omega)]
  exact extendPath_catWord_left b.2 (rawWord bs) hj

/-- With no completed block, the reassembled extension is just the unfinished tail. -/
theorem extendPath_decompWord_of_completed_nil {hm : 1 ≤ m} {y : RecState N m}
    {K : ℕ} (d : MaxRecordDecomp (N := N) hm y K)
    (hd : d.completed = []) {j : ℕ} (hj : j < K) :
    extendPath (decompWord d) j = extendPath d.tail.2 j := by
  have hlen := d.len_eq
  rw [hd] at hlen
  simp only [rawLen, Nat.zero_add] at hlen
  rw [decompWord, extendPath_castWord _ _ hj, hd]
  change extendPath (catWord (rawWord ([] : List (RawBlock N))) d.tail.2) j =
    extendPath d.tail.2 j
  simpa only [rawLen, Nat.zero_add] using
    extendPath_catWord_right (rawWord ([] : List (RawBlock N))) d.tail.2
      (show j < d.tail.1 by omega)

/-- A decomposition with empty completed list has no first-record prefix at all. -/
theorem noRecordPrefix_decompWord_of_completed_nil {hm : 1 ≤ m} {y : RecState N m}
    {K : ℕ} (d : MaxRecordDecomp (N := N) hm y K) (hd : d.completed = []) :
    NoRecordPrefix (ofRecState y) (decompWord d) := by
  intro k hk hkK hfr
  have htail := d.tail_unfinished
  rw [hd] at htail
  apply htail k hk (by have := d.len_eq; rw [hd] at this; simp [rawLen] at this; omega)
  exact firstRecord_of_extendPath_congr (decompWord d) d.tail.2 (ofRecState y)
    (fun j hj => extendPath_decompWord_of_completed_nil d hd (by omega)) hfr

/-- Remove the first completed excursion, retaining the same unfinished tail. -/
noncomputable def dropHead {hm : 1 ≤ m} {y : RecState N m} {K : ℕ}
    (d : MaxRecordDecomp (N := N) hm y K) {b : RawBlock N}
    {bs : List (RawBlock N)} (hd : d.completed = b :: bs) :
    MaxRecordDecomp (N := N) hm (RecKernel.out hm b.2 y) (K - b.1) where
  completed := bs
  tail := d.tail
  len_eq := by
    have hlen := d.len_eq
    rw [hd] at hlen
    simp only [rawLen] at hlen
    omega
  allFirst := by
    have hall := d.allFirst
    rw [hd] at hall
    exact hall.2
  tail_unfinished := by
    have htail := d.tail_unfinished
    rw [hd] at htail
    exact htail

/-- The dropped-head word is exactly the shifted suffix of the original word. -/
theorem decompWord_dropHead {hm : 1 ≤ m} {y : RecState N m} {K : ℕ}
    (d : MaxRecordDecomp (N := N) hm y K) {b : RawBlock N}
    {bs : List (RawBlock N)} (hd : d.completed = b :: bs) (j : Fin (K - b.1)) :
    decompWord (dropHead d hd) j = decompWord d ⟨b.1 + j.1, by
      have hlen := d.len_eq
      rw [hd] at hlen
      simp only [rawLen] at hlen
      omega⟩ := by
  rcases d with ⟨dc, dt, dl, da, du⟩
  cases dc with
  | nil => contradiction
  | cons b' bs' =>
      injection hd with hb hbs
      subst b'
      subst bs'
      have hbpos : 0 < b.1 := SwarmDHStruct.firstRecord_ne_zero da.1
      by_cases hj : j.1 < rawLen bs
      · simp [decompWord, dropHead, castWord, catWord, rawWord, rawLen, hj,
          show ¬ b.1 + j.1 < b.1 by omega, Nat.add_sub_cancel_left]
      · simp [decompWord, dropHead, castWord, catWord, rawWord, rawLen, hj,
          show ¬ b.1 + j.1 < b.1 by omega, Nat.add_sub_cancel_left, Nat.sub_sub,
          show b.1 + j.1 - (b.1 + rawLen bs) = j.1 - rawLen bs by omega]

/-- Two decompositions with the same completed list and unfinished tail are equal. -/
theorem maxRecordDecomp_ext {hm : 1 ≤ m} {y : RecState N m} {K : ℕ}
    {d e : MaxRecordDecomp (N := N) hm y K}
    (hc : d.completed = e.completed) (ht : d.tail = e.tail) : d = e := by
  cases d
  cases e
  cases hc
  cases ht
  rfl


/-- **Unique maximal-record decomposition.**  Hence distinct decomposition
indices have disjoint reassembled-word fibres. -/
theorem maxRecordDecomp_unique {hm : 1 ≤ m} (y : RecState N m) :
    ∀ (K : ℕ) (d e : MaxRecordDecomp (N := N) hm y K),
      decompWord d = decompWord e → d = e := by
  intro K
  induction K using Nat.strong_induction_on generalizing y with
  | h K ih =>
      intro d e hde
      cases hdcomp : d.completed with
      | nil =>
          cases hecomp : e.completed with
          | nil =>
              have hdlen : d.tail.1 = K := by
                have hlen := d.len_eq
                rw [hdcomp] at hlen
                simpa [rawLen] using hlen
              have helen : e.tail.1 = K := by
                have hlen := e.len_eq
                rw [hecomp] at hlen
                simpa [rawLen] using hlen
              apply maxRecordDecomp_ext (hdcomp.trans hecomp.symm)
              apply rawBlock_ext (hdlen.trans helen.symm)
              intro j
              have hjK : j.1 < K := by omega
              have hjd := extendPath_decompWord_of_completed_nil d hdcomp hjK
              have hje := extendPath_decompWord_of_completed_nil e hecomp hjK
              simp only [extendPath, dif_pos hjK, dif_pos j.isLt] at hjd
              simp only [extendPath, dif_pos hjK,
                dif_pos (show j.1 < e.tail.1 by omega)] at hje
              calc
                d.tail.2 j = decompWord d ⟨j.1, hjK⟩ := hjd.symm
                _ = decompWord e ⟨j.1, hjK⟩ := congrFun hde _
                _ = e.tail.2 ⟨j.1, by omega⟩ := hje
          | cons c cs =>
              exfalso
              have hfc := firstRecord_decompWord_of_completed_cons e hecomp
              have hfd : FirstRecord (extendPath (decompWord d)) c.1 (ofRecState y) := by
                rw [hde]
                exact hfc
              have hcK : c.1 ≤ K := by
                have hlen := e.len_eq
                rw [hecomp] at hlen
                simp only [rawLen] at hlen
                omega
              exact noRecordPrefix_decompWord_of_completed_nil d hdcomp c.1
                (firstRecord_time_pos_recordState (hm := hm) _ hfc) hcK hfd
      | cons b bs =>
          cases hecomp : e.completed with
          | nil =>
              exfalso
              have hfb := firstRecord_decompWord_of_completed_cons d hdcomp
              have hfe : FirstRecord (extendPath (decompWord e)) b.1 (ofRecState y) := by
                rw [← hde]
                exact hfb
              have hbK : b.1 ≤ K := by
                have hlen := d.len_eq
                rw [hdcomp] at hlen
                simp only [rawLen] at hlen
                omega
              exact noRecordPrefix_decompWord_of_completed_nil e hecomp b.1
                (firstRecord_time_pos_recordState (hm := hm) _ hfb) hbK hfe
          | cons c cs =>
              have hfb := firstRecord_decompWord_of_completed_cons d hdcomp
              have hfc := firstRecord_decompWord_of_completed_cons e hecomp
              have hfb' : FirstRecord (extendPath (decompWord e)) b.1 (ofRecState y) := by
                rw [← hde]
                exact hfb
              have hlen : b.1 = c.1 := firstRecord_time_unique hfb' hfc
              have hbK : b.1 ≤ K := by
                have hKlen := d.len_eq
                rw [hdcomp] at hKlen
                simp only [rawLen] at hKlen
                omega
              have hbc : b = c := by
                apply rawBlock_ext hlen
                intro j
                have hjK : j.1 < K := by omega
                have hjd := extendPath_decompWord_of_completed_cons d hdcomp j.isLt
                have hje := extendPath_decompWord_of_completed_cons e hecomp
                  (show j.1 < c.1 by omega)
                simp only [extendPath, dif_pos hjK, dif_pos j.isLt] at hjd
                simp only [extendPath, dif_pos hjK,
                  dif_pos (show j.1 < c.1 by omega)] at hje
                calc
                  b.2 j = decompWord d ⟨j.1, hjK⟩ := hjd.symm
                  _ = decompWord e ⟨j.1, hjK⟩ := congrFun hde _
                  _ = c.2 ⟨j.1, by omega⟩ := hje
              subst c
              have hbpos : 0 < b.1 :=
                firstRecord_time_pos_recordState (hm := hm) _ hfb
              have hdrop : dropHead d hdcomp = dropHead e hecomp := by
                apply ih (K - b.1) (by omega) (RecKernel.out hm b.2 y)
                funext j
                calc
                  decompWord (dropHead d hdcomp) j =
                      decompWord d ⟨b.1 + j.1, by
                        have hKlen := d.len_eq
                        rw [hdcomp] at hKlen
                        simp only [rawLen] at hKlen
                        omega⟩ := decompWord_dropHead d hdcomp j
                  _ = decompWord e ⟨b.1 + j.1, by
                        have hKlen := d.len_eq
                        rw [hdcomp] at hKlen
                        simp only [rawLen] at hKlen
                        omega⟩ := congrFun hde _
                  _ = decompWord (dropHead e hecomp) j :=
                    (decompWord_dropHead e hecomp j).symm
              have hbs : bs = cs := by
                have h := congrArg (fun z => z.completed) hdrop
                exact h
              have ht : d.tail = e.tail := by
                have h := congrArg (fun z => z.tail) hdrop
                exact h
              apply maxRecordDecomp_ext _ ht
              rw [hdcomp, hecomp, hbs]

/-- Reassembly is a bijection between maximal decompositions at a fixed initial
state and all raw words of the same duration. -/
noncomputable def maxRecordDecompEquiv {hm : 1 ≤ m} (y : RecState N m) (K : ℕ) :
    MaxRecordDecomp (N := N) hm y K ≃ (Fin K → JumpVec N) :=
  Equiv.ofBijective decompWord ⟨maxRecordDecomp_unique y K, exists_maxRecordDecomp y K⟩

@[simp] theorem maxRecordDecompEquiv_apply {hm : 1 ≤ m} (y : RecState N m) (K : ℕ)
    (d : MaxRecordDecomp (N := N) hm y K) : maxRecordDecompEquiv y K d = decompWord d := rfl

/-- Positivity, and any additional terminal pattern predicate, selects whole-word
subtypes on both sides of the canonical decomposition equivalence. -/
noncomputable def positiveMaxRecordDecompEquiv {hm : 1 ≤ m} (y : RecState N m) (K : ℕ)
    (P : (Fin K → JumpVec N) → Prop) :
    {d : MaxRecordDecomp (N := N) hm y K //
      SwarmFreshPos.PosSeqFin (N := N) (decompWord d) ∧ P (decompWord d)} ≃
      {q : Fin K → JumpVec N // SwarmFreshPos.PosSeqFin (N := N) q ∧ P q} :=
  (maxRecordDecompEquiv y K).subtypeEquiv fun _d => Iff.rfl


/-- The raw-word fibre indexed by one maximal decomposition. -/
def decompFibre {hm : 1 ≤ m} {y : RecState N m} {K : ℕ}
    (d : MaxRecordDecomp (N := N) hm y K) : Set (Fin K → JumpVec N) :=
  {q | decompWord d = q}

/-- Distinct decomposition indices give disjoint raw-word cylinders. -/
theorem pairwise_disjoint_decompFibre {hm : 1 ≤ m} (y : RecState N m) (K : ℕ) :
    Pairwise (fun d e : MaxRecordDecomp (N := N) hm y K =>
      Disjoint (decompFibre d) (decompFibre e)) := by
  intro d e hne
  rw [Set.disjoint_left]
  intro q hqd hqe
  apply hne
  exact maxRecordDecomp_unique y K d e (hqd.trans hqe.symm)

/-- The decomposition fibres exhaust every raw word, without a positivity restriction. -/
theorem iUnion_decompFibre {hm : 1 ≤ m} (y : RecState N m) (K : ℕ) :
    (⋃ d : MaxRecordDecomp (N := N) hm y K, decompFibre d) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  obtain ⟨d, hd⟩ := exists_maxRecordDecomp y K q
  exact Set.mem_iUnion.2 ⟨d, hd⟩

/-- **Exact shifted positivity across the record/future split.**  The completed
raw prefix is positive on its own times; every unfinished-tail time is positive
above the actual boundary level.  There is no positivity or first-record
hypothesis on an individual excursion or on the unfinished tail. -/
theorem posSeqFin_decompWord_iff_blockCond {hm : 1 ≤ m} {y : RecState N m}
    {K : ℕ} (d : MaxRecordDecomp (N := N) hm y K) :
    SwarmFreshPos.PosSeqFin (N := N) (decompWord d) ↔
      SwarmArrayWords.blockCond (rawWord d.completed) d.tail.2 := by
  rw [posSeqFin_decompWord_iff]
  simpa only [SwarmArrayWords.prefWord_catWord, SwarmArrayWords.suffWord_catWord] using
    SwarmArrayWords.blockCond_iff_of_word (catWord (rawWord d.completed) d.tail.2)

/-- A finite enumeration induced by the word equivalence; no finiteness axiom is assumed. -/
@[instance_reducible] noncomputable def maxRecordDecompFintype {hm : 1 ≤ m} (y : RecState N m) (K : ℕ) :
    Fintype (MaxRecordDecomp (N := N) hm y K) :=
  Fintype.ofEquiv (Fin K → JumpVec N) (maxRecordDecompEquiv y K).symm

attribute [local instance] maxRecordDecompFintype

/-- **Measured positive maximal-record partition.**  The left side is an arbitrary
word-predicate array cylinder with whole-word strict positivity.  The right side
runs exactly once over all maximal completed-record/unfinished-tail decompositions.
No individual excursion is required positive, and no suffix is truncated. -/
theorem arrayMeasure_positiveWord_maxRecordDecomp
    (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (y : RecState N m) (hy : ofRecState y = SwarmFreshArray.startState (N := N) m)
    (K : ℕ) (P : (Fin K → JumpVec N) → Prop) :
    (arrayMeasure N) {U : Array N |
        SwarmFreshPos.PosSeqFin (N := N) (jumpWord p m K U) ∧
          P (jumpWord p m K U)} =
      ∑ d : MaxRecordDecomp (N := N) hm y K,
        if SwarmFreshPos.PosSeqFin (N := N) (decompWord d) ∧ P (decompWord d) then
          ENNReal.ofReal
            (prefixW p hm y d.completed *
              pathW p d.tail.1 d.tail.2 (ofRecState (terminal hm y d.completed)))
        else 0 := by
  rw [SwarmArrayWords.mass_wordSet p hp0 hp1 m K
    (fun q => SwarmFreshPos.PosSeqFin (N := N) q ∧ P q)]
  symm
  refine Fintype.sum_equiv (maxRecordDecompEquiv y K) _ _ ?_
  intro d
  rw [maxRecordDecompEquiv_apply]
  by_cases hcond : SwarmFreshPos.PosSeqFin (N := N) (decompWord d) ∧ P (decompWord d)
  · rw [if_pos hcond, if_pos hcond]
    congr 1
    rw [← hy, pathW_decompWord]
  · rw [if_neg hcond, if_neg hcond]


/-- The arbitrary-pattern horizon mass, reindexed by maximal record decompositions.
This is an array-side finite identity only; it asserts no chain `hstruct`,
stationary law, regeneration, or raw/enriched joined-window theorem. -/
theorem arrayMeasure_finStrict_pattern_maxRecordDecomp
    (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (y : RecState N m) (hy : ofRecState y = SwarmFreshArray.startState (N := N) m)
    (K : ℕ) (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    (arrayMeasure N) {U : Array N |
        posPath p m U ∈ finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C} =
      ∑ d : MaxRecordDecomp (N := N) hm y K,
        if SwarmFreshPos.PosSeqFin (N := N) (decompWord d) ∧
            patOf (N := N) (decompWord d) ∈ C then
          ENNReal.ofReal
            (prefixW p hm y d.completed *
              pathW p d.tail.1 d.tail.2 (ofRecState (terminal hm y d.completed)))
        else 0 := by
  rw [SwarmArrayWords.finStrict_pattern_eq_wordSet]
  exact arrayMeasure_positiveWord_maxRecordDecomp p hp0 hp1 hm y hy K
    (fun q => patOf (N := N) q ∈ C)

/-- Canonical fresh-start specialization of the arbitrary-pattern partition. -/
theorem arrayMeasure_finStrict_pattern_maxRecordDecomp_fresh
    (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (i₀ : Fin N) (K : ℕ) (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    (arrayMeasure N) {U : Array N |
        posPath p m U ∈ finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C} =
      ∑ d : MaxRecordDecomp (N := N) hm (freshRecState (N := N) hm i₀) K,
        if SwarmFreshPos.PosSeqFin (N := N) (decompWord d) ∧
            patOf (N := N) (decompWord d) ∈ C then
          ENNReal.ofReal
            (prefixW p hm (freshRecState (N := N) hm i₀) d.completed *
              pathW p d.tail.1 d.tail.2
                (ofRecState (terminal hm (freshRecState (N := N) hm i₀) d.completed)))
        else 0 :=
  arrayMeasure_finStrict_pattern_maxRecordDecomp p hp0 hp1 hm _
    (ofRecState_freshRecState hm i₀) K C


end SwarmRawRecord
