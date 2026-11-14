/-
Arbitrary finite prefixes of genuine record excursions, in raw coordinates.

A `RawBlock` packages a finite word with its length.  For every list of blocks,
`rawWord` is their actual concatenation and `terminal` is the compact state after
following the successive record kernel endpoints.  The results below are purely
pathwise: there is no invariant law, no fresh-future assertion and no summation.
-/
import Swarm.RawRecordBlocks

open MeasureTheory Set
open scoped ENNReal BigOperators
open SimJump

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace SwarmRawRecord

open SimJump.Record SwarmRec SwarmFreshArray SwarmArrayWords

attribute [local instance] Classical.propDecidable

variable {N m : ℕ}

/-- A finite raw jump word, with its length stored in the dependent pair. -/
abbrev RawBlock (N : ℕ) := Σ k : ℕ, Fin k → JumpVec N

/-- Total raw duration of a list of blocks. -/
def rawLen : List (RawBlock N) → ℕ
  | [] => 0
  | b :: bs => b.1 + rawLen bs

/-- Actual concatenation of all the raw blocks. -/
noncomputable def rawWord : (bs : List (RawBlock N)) → Fin (rawLen bs) → JumpVec N
  | [] => fun i => Fin.elim0 i
  | b :: bs => catWord b.2 (rawWord bs)

/-- Compact state after following every record block in order. -/
noncomputable def terminal (hm : 1 ≤ m) (y : RecState N m) : List (RawBlock N) → RecState N m
  | [] => y
  | b :: bs => terminal hm (RecKernel.out hm b.2 y) bs

/-- Every block is a first-record excursion at the actual preceding compact state. -/
def AllFirst (hm : 1 ≤ m) (y : RecState N m) : List (RawBlock N) → Prop
  | [] => True
  | b :: bs => FirstRecord (extendPath b.2) b.1 (ofRecState y) ∧
      AllFirst hm (RecKernel.out hm b.2 y) bs

/-- Product of the stopped weights of all record blocks, at their actual states. -/
noncomputable def prefixW (p : ℝ) (hm : 1 ≤ m) (y : RecState N m) :
    List (RawBlock N) → ℝ
  | [] => 1
  | b :: bs => RecKernel.hitW p b.2 y * prefixW p hm (RecKernel.out hm b.2 y) bs

/-- Move the record origin down `n` successive record levels. -/
def lower : ℕ → State N m → State N m
  | 0, s => s
  | n + 1, s => normalize (lower n s)

@[simp] theorem lower_zero (s : State N m) : lower 0 s = s := rfl

@[simp] theorem lower_succ (n : ℕ) (s : State N m) :
    lower (n + 1) s = normalize (lower n s) := rfl

/-- Finite evolution depends only on the jumps before the horizon. -/
theorem evolveFun_congr_prefix {u v : ℕ → JumpVec N} {k : ℕ}
    (h : ∀ j, j < k → u j = v j) (s : State N m) :
    evolveFun u k s = evolveFun v k s := by
  unfold evolveFun
  congr 1
  funext j
  exact h j j.2

/-- Finite path weight depends only on the jumps before the horizon. -/
theorem pathWFun_congr_prefix (p : ℝ) {u v : ℕ → JumpVec N} {k : ℕ}
    (h : ∀ j, j < k → u j = v j) (s : State N m) :
    pathWFun p u k s = pathWFun p v k s := by
  have hj : (fun j : Fin k => u j) = (fun j : Fin k => v j) := by
    funext j
    exact h j j.2
  simp only [pathWFun, hj]

/-- The first block of `catWord` agrees with the concatenated continuation. -/
theorem extendPath_catWord_left {k r : ℕ} (qf : Fin k → JumpVec N)
    (q : Fin r → JumpVec N) {j : ℕ} (hj : j < k) :
    extendPath (catWord qf q) j = extendPath qf j := by
  simp only [extendPath, dif_pos hj, dif_pos (show j < k + r by omega), catWord,
    dif_pos hj]

/-- The second block of `catWord` agrees with the shifted concatenated continuation. -/
theorem extendPath_catWord_right {k r : ℕ} (qf : Fin k → JumpVec N)
    (q : Fin r → JumpVec N) {j : ℕ} (hj : j < r) :
    extendPath (catWord qf q) (k + j) = extendPath q j := by
  have hkj : ¬ k + j < k := by omega
  simp only [extendPath, dif_pos hj, dif_pos (show k + j < k + r by omega), catWord,
    dif_neg hkj, Nat.add_sub_cancel_left]

/-- Raw state after a concatenation, at an arbitrary start state. -/
theorem evolveFun_catWord {k r : ℕ} (qf : Fin k → JumpVec N)
    (q : Fin r → JumpVec N) (s : State N m) :
    evolveFun (extendPath (catWord qf q)) (k + r) s =
      evolveFun (extendPath q) r (evolveFun (extendPath qf) k s) := by
  rw [SwarmArrayWords.evolveFun_shift]
  rw [evolveFun_congr_prefix (fun j hj => extendPath_catWord_left qf q hj),
    evolveFun_congr_prefix (fun j hj => extendPath_catWord_right qf q hj)]

/-- Raw weight after a concatenation, at an arbitrary start state. -/
theorem pathW_catWord (p : ℝ) {k r : ℕ} (qf : Fin k → JumpVec N)
    (q : Fin r → JumpVec N) (s : State N m) :
    pathW p (k + r) (catWord qf q) s = pathW p k qf s *
      pathW p r q (evolveFun (extendPath qf) k s) := by
  rw [SwarmFreshCyl.pathW_eq_pathWFun_extendPath,
    SwarmFreshCyl.pathW_eq_pathWFun_extendPath,
    SwarmFreshCyl.pathW_eq_pathWFun_extendPath, SwarmArrayWords.pathWFun_add]
  rw [pathWFun_congr_prefix p (fun j hj => extendPath_catWord_left qf q hj),
    pathWFun_congr_prefix p (fun j hj => extendPath_catWord_right qf q hj),
    evolveFun_congr_prefix (fun j hj => extendPath_catWord_left qf q hj)]

/-- The order of the normalization steps in `lower` is immaterial. -/
theorem lower_normalize (n : ℕ) (s : State N m) :
    lower n (normalize s) = normalize (lower n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      change normalize (lower n (normalize s)) = normalize (normalize (lower n s))
      rw [ih]

/-- Lowering commutes with every finite raw evolution. -/
theorem evolveFun_lower (n : ℕ) (u : ℕ → JumpVec N) (k : ℕ) (s : State N m) :
    lower n (evolveFun u k s) = evolveFun u k (lower n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      change normalize (lower n (evolveFun u k s)) = evolveFun u k (normalize (lower n s))
      rw [ih, evolveFun_normalize]

/-- Every finite word weight is invariant under lowering any number of record levels. -/
theorem pathW_lower (p : ℝ) (n : ℕ) {k : ℕ} (q : Fin k → JumpVec N) (s : State N m) :
    pathW p k q (lower n s) = pathW p k q s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      change pathW p k q (normalize (lower n s)) = pathW p k q s
      rw [pathW_normalize, ih]

/-- **Arbitrary record-prefix weight.**  The raw weight of the entire concatenation is
exactly the product of the stopped weights at the successive actual record states. -/
theorem pathW_rawWord (p : ℝ) (hm : 1 ≤ m) (y : RecState N m)
    (bs : List (RawBlock N)) (h : AllFirst hm y bs) :
    pathW p (rawLen bs) (rawWord bs) (ofRecState y) = prefixW p hm y bs := by
  induction bs generalizing y with
  | nil => rfl
  | cons b bs ih =>
      rcases h with ⟨hb, hbs⟩
      change pathW p (b.1 + rawLen bs) (catWord b.2 (rawWord bs)) (ofRecState y) =
        RecKernel.hitW p b.2 y * prefixW p hm (RecKernel.out hm b.2 y) bs
      rw [pathW_catWord, RecKernel.hitW_of_firstRecord p b.2 y hb]
      congr 1
      have hout := ofRecState_out hm b.2 y hb
      have hnorm := pathW_normalize p (rawWord bs)
        (evolveFun (extendPath b.2) b.1 (ofRecState y))
      rw [← hout] at hnorm
      exact hnorm.symm.trans (ih (RecKernel.out hm b.2 y) hbs)

/-- **Exact terminal raw state.**  After a list of genuine record excursions, expansion of
the compact terminal state is the actual raw successor lowered once per completed record. -/
theorem ofRecState_terminal (hm : 1 ≤ m) (y : RecState N m)
    (bs : List (RawBlock N)) (h : AllFirst hm y bs) :
    ofRecState (terminal hm y bs) = lower bs.length
      (evolveFun (extendPath (rawWord bs)) (rawLen bs) (ofRecState y)) := by
  induction bs generalizing y with
  | nil => rfl
  | cons b bs ih =>
      rcases h with ⟨hb, hbs⟩
      change ofRecState (terminal hm (RecKernel.out hm b.2 y) bs) =
        lower (bs.length + 1) (evolveFun (extendPath (catWord b.2 (rawWord bs)))
          (b.1 + rawLen bs) (ofRecState y))
      rw [ih (RecKernel.out hm b.2 y) hbs, evolveFun_catWord, ofRecState_out hm b.2 y hb,
        ← evolveFun_normalize, lower_normalize]
      rfl

/-- **Arbitrary record prefix followed by an unrestricted raw future.**  The final factor
uses the actual raw successor after all records, not a refreshed or unrelated state. -/
theorem pathW_rawWord_future (p : ℝ) (hm : 1 ≤ m) (y : RecState N m)
    (bs : List (RawBlock N)) (h : AllFirst hm y bs)
    {s : ℕ} (qs : Fin s → JumpVec N) :
    pathW p (rawLen bs + s) (catWord (rawWord bs) qs) (ofRecState y) =
      prefixW p hm y bs * pathW p s qs
        (evolveFun (extendPath (rawWord bs)) (rawLen bs) (ofRecState y)) := by
  rw [pathW_catWord, pathW_rawWord p hm y bs h]

/-- The same arbitrary raw suffix can equally be evaluated at the compact terminal state.
No first-record or positivity condition is imposed on the suffix. -/
theorem pathW_rawWord_future_terminal (p : ℝ) (hm : 1 ≤ m) (y : RecState N m)
    (bs : List (RawBlock N)) (h : AllFirst hm y bs)
    {s : ℕ} (qs : Fin s → JumpVec N) :
    pathW p (rawLen bs + s) (catWord (rawWord bs) qs) (ofRecState y) =
      prefixW p hm y bs * pathW p s qs (ofRecState (terminal hm y bs)) := by
  rw [pathW_rawWord_future p hm y bs h qs, ofRecState_terminal hm y bs h, pathW_lower]

/-- The position coordinate after `n` lowerings is shifted by exactly `n`. -/
theorem lower_pos (n : ℕ) (s : State N m) (i : Fin N) :
    (lower n s).pos i = s.pos i - (n : ℤ) := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
      change (lower n s).pos i - 1 = s.pos i - ((n + 1 : ℕ) : ℤ)
      rw [ih]
      push_cast
      ring

/-- The local-time coordinate after `n` lowerings is shifted by exactly `n`. -/
theorem lower_eta (n : ℕ) (s : State N m) (i : Fin N) (x : ℤ) :
    (lower n s).eta i x = s.eta i (x + (n : ℤ)) := by
  induction n generalizing s x with
  | zero => simp
  | succ n ih =>
      change (lower n s).eta i (x + 1) = s.eta i (x + ((n + 1 : ℕ) : ℤ))
      rw [ih]
      congr 1
      push_cast
      ring

/-- **Cumulative record-level bookkeeping.**  At the end of an arbitrary record prefix,
the raw position is the number of completed records plus the compact terminal position. -/
theorem raw_terminal_pos (hm : 1 ≤ m) (y : RecState N m)
    (bs : List (RawBlock N)) (h : AllFirst hm y bs) (i : Fin N) :
    (evolveFun (extendPath (rawWord bs)) (rawLen bs) (ofRecState y)).pos i =
      (bs.length : ℤ) + (ofRecState (terminal hm y bs)).pos i := by
  have heq := congrArg (fun s : State N m => s.pos i) (ofRecState_terminal hm y bs h)
  rw [lower_pos] at heq
  omega

/-- **Local-time transport at the terminal raw boundary.**  No local times below the new
record are erased; they are read at the exact shift given by the number of records. -/
theorem raw_terminal_eta (hm : 1 ≤ m) (y : RecState N m)
    (bs : List (RawBlock N)) (h : AllFirst hm y bs) (i : Fin N) (x : ℤ) :
    (ofRecState (terminal hm y bs)).eta i x =
      (evolveFun (extendPath (rawWord bs)) (rawLen bs) (ofRecState y)).eta i
        (x + (bs.length : ℤ)) := by
  have heq := congrArg (fun s : State N m => s.eta i x) (ofRecState_terminal hm y bs h)
  rw [lower_eta] at heq
  exact heq

end SwarmRawRecord


namespace SwarmRawRecord

open SimJump.Record SwarmRec SwarmFreshArray SwarmArrayWords

variable {N m : ℕ}

/-- **Raw positions inside a record after an arbitrarily shifted raw prefix.**  The premise
`hy` says precisely that the current compact state is the `j`-fold lowering of the actual
raw prefix endpoint.  The raw position at `k+t` is then `j` plus the enriched segment
position, including its genuine below-record start. -/
theorem patOf_lower_record_suffix {s : State N m} (hs : ∀ i, s.pos i = 0)
    (y : RecState N m) (j : ℕ) {k r : ℕ} (qf : Fin k → JumpVec N)
    (hy : ofRecState y = lower j (evolveFun (extendPath qf) k s))
    (q : Fin r → JumpVec N) (hr : 0 < r)
    (hq : FirstRecord (extendPath q) r (ofRecState y))
    {t : ℕ} (ht : t ≤ r) (i : Fin N) :
    SwarmFinHorizon.patOf (N := N) (catWord qf q) ⟨k + t, by omega⟩ i =
      (j : ℤ) + (SwarmSegKernel.segOf y r q).p t i := by
  have hsplit := posAt_boundary (N := N) (catWord qf q) ht i
  have hpre := posAt_boundary_pref (N := N) (catWord qf q) i
  rw [suffWord_catWord] at hsplit
  rw [prefWord_catWord] at hpre
  rw [hpre] at hsplit
  have hpref := SwarmFreshPos.pos_evolveFun (extendPath qf) k s i
  rw [hs i, zero_add] at hpref
  have hraw := SwarmFreshPos.pos_evolveFun (extendPath q) t
    (evolveFun (extendPath qf) k s) i
  have hseg : (SwarmSegKernel.segOf y r q).p t i =
      (evolveFun (extendPath q) t (evolveFun (extendPath qf) k s)).pos i - (j : ℤ) := by
    rw [SwarmFreshCyl.segOf_p_of_firstRecord hr q hq]
    change (evolveFun (extendPath q) t (ofRecState y)).pos i = _
    rw [hy, ← evolveFun_lower, lower_pos]
  change SwarmFreshPos.posAt (SwarmFreshPos.seqOf (catWord qf q)) (k + t) i = _
  rw [SwarmFreshCyl.posAt_seqOf_eq_extendPath (catWord qf q) (k + t) i (by omega), hsplit]
  omega

/-- Specialisation to an arbitrary completed record list.  This covers the interior of the
next record after any number of earlier records, without imposing an all-right or
`PosSeqFin` restriction on any record excursion. -/
theorem patOf_rawWord_record_suffix (hm : 1 ≤ m) {y : RecState N m}
    (hy : y ∈ srSet N m) (bs : List (RawBlock N)) (hbs : AllFirst hm y bs)
    {r : ℕ} (q : Fin r → JumpVec N) (hr : 0 < r)
    (hq : FirstRecord (extendPath q) r (ofRecState (terminal hm y bs)))
    {t : ℕ} (ht : t ≤ r) (i : Fin N) :
    SwarmFinHorizon.patOf (N := N) (catWord (rawWord bs) q)
        ⟨rawLen bs + t, by omega⟩ i =
      (bs.length : ℤ) + (SwarmSegKernel.segOf (terminal hm y bs) r q).p t i := by
  exact patOf_lower_record_suffix
    (s := ofRecState y) (fun i => SwarmFreshCyl.ofRecState_pos_eq_zero hy i)
    (terminal hm y bs) bs.length (rawWord bs) (ofRecState_terminal hm y bs hbs)
    q hr hq ht i

/-- **Exact overlap of strict raw positivity and a later first record.**  Strict positivity
of the concatenated raw word is equivalent to strict positivity of the old prefix together
with positivity of the final segment after adding the actual cumulative record level.  The
latter is not `PosSeqFin q`, and no positivity of the individual earlier excursions is
silently substituted for positivity of the whole raw prefix. -/
theorem posSeqFin_cat_lower_record_iff {s : State N m} (hs : ∀ i, s.pos i = 0)
    (y : RecState N m) (j : ℕ) {k r : ℕ} (qf : Fin k → JumpVec N)
    (hy : ofRecState y = lower j (evolveFun (extendPath qf) k s))
    (q : Fin r → JumpVec N) (hr : 0 < r)
    (hq : FirstRecord (extendPath q) r (ofRecState y)) :
    SwarmFreshPos.PosSeqFin (N := N) (catWord qf q) ↔
      SwarmFreshPos.PosSeqFin (N := N) qf ∧
        ∀ t, 1 ≤ t → t ≤ r → ∀ i,
          0 < (j : ℤ) + (SwarmSegKernel.segOf y r q).p t i := by
  constructor
  · intro hpos
    have hg := (SwarmFreshCyl.posWord_iff (catWord qf q)).mp hpos
    refine ⟨?_, ?_⟩
    · apply (SwarmFreshCyl.posWord_iff qf).mpr
      intro n hn hnk i
      have h := hg n hn (by omega) i
      rw [posAt_prefWord_eq (catWord qf q) hnk i, prefWord_catWord] at h
      exact h
    · intro t ht htr i
      have hp := hg (k + t) (by omega) (by omega) i
      have hpat := patOf_lower_record_suffix hs y j qf hy q hr hq htr i
      change SwarmFreshPos.posAt (SwarmFreshPos.seqOf (catWord qf q)) (k + t) i = _ at hpat
      rw [SwarmFreshCyl.posAt_seqOf_eq_extendPath (catWord qf q) (k + t) i (by omega)] at hpat
      rw [← hpat]
      exact hp
  · rintro ⟨hpre, hpos⟩
    have hp := (SwarmFreshCyl.posWord_iff qf).mp hpre
    apply (SwarmFreshCyl.posWord_iff (catWord qf q)).mpr
    intro n hn hnk i
    by_cases hle : n ≤ k
    · rw [posAt_prefWord_eq (catWord qf q) hle i, prefWord_catWord]
      exact hp n hn hle i
    · have ht : 1 ≤ n - k := by omega
      have htr : n - k ≤ r := by omega
      have hpat := patOf_lower_record_suffix hs y j qf hy q hr hq htr i
      rw [show n = k + (n - k) by omega]
      change SwarmFreshPos.posAt (SwarmFreshPos.seqOf (catWord qf q)) (k + (n - k)) i = _
        at hpat
      rw [SwarmFreshCyl.posAt_seqOf_eq_extendPath (catWord qf q) (k + (n - k)) i (by omega)]
        at hpat
      rw [show k + (n - k) = n by omega] at hpat
      rw [show k + (n - k) = n by omega, hpat]
      exact hpos (n - k) ht htr i

/-- The same exact positivity overlap after an arbitrary list of completed records. -/
theorem posSeqFin_rawWord_record_suffix_iff (hm : 1 ≤ m) {y : RecState N m}
    (hy : y ∈ srSet N m) (bs : List (RawBlock N)) (hbs : AllFirst hm y bs)
    {r : ℕ} (q : Fin r → JumpVec N) (hr : 0 < r)
    (hq : FirstRecord (extendPath q) r (ofRecState (terminal hm y bs))) :
    SwarmFreshPos.PosSeqFin (N := N) (catWord (rawWord bs) q) ↔
      SwarmFreshPos.PosSeqFin (N := N) (rawWord bs) ∧
        ∀ t, 1 ≤ t → t ≤ r → ∀ i,
          0 < (bs.length : ℤ) +
            (SwarmSegKernel.segOf (terminal hm y bs) r q).p t i := by
  exact posSeqFin_cat_lower_record_iff
    (s := ofRecState y) (fun i => SwarmFreshCyl.ofRecState_pos_eq_zero hy i)
    (terminal hm y bs) bs.length (rawWord bs) (ofRecState_terminal hm y bs hbs)
    q hr hq

end SwarmRawRecord


namespace SwarmRawRecord

open SimJump.Record SwarmRec SwarmFreshArray SwarmArrayWords

variable {N m : ℕ}

/-- Before the next first-record time, the raw path cannot exceed the cumulative record
level reached by the arbitrary completed prefix. -/
theorem patOf_rawWord_record_suffix_le (hm : 1 ≤ m) {y : RecState N m}
    (hy : y ∈ srSet N m) (bs : List (RawBlock N)) (hbs : AllFirst hm y bs)
    {r : ℕ} (q : Fin r → JumpVec N) (hr : 0 < r)
    (hq : FirstRecord (extendPath q) r (ofRecState (terminal hm y bs)))
    {t : ℕ} (ht : t < r) (i : Fin N) :
    SwarmFinHorizon.patOf (N := N) (catWord (rawWord bs) q)
        ⟨rawLen bs + t, by omega⟩ i ≤ (bs.length : ℤ) := by
  rw [patOf_rawWord_record_suffix hm hy bs hbs q hr hq (Nat.le_of_lt ht) i]
  have hle := hq.2 t ht i
  have hp : (SwarmSegKernel.segOf (terminal hm y bs) r q).p t i ≤ 0 := by
    rw [SwarmFreshCyl.segOf_p_of_firstRecord hr q hq]
    exact hle
  omega

/-- At the end of an arbitrary record prefix, some walker is exactly at the cumulative
record level.  Thus the offset in `raw_terminal_pos` is the actual new record maximum. -/
theorem exists_raw_terminal_eq_length (hm : 1 ≤ m) (y : RecState N m)
    (bs : List (RawBlock N)) (h : AllFirst hm y bs) :
    ∃ i : Fin N,
      (evolveFun (extendPath (rawWord bs)) (rawLen bs) (ofRecState y)).pos i =
        (bs.length : ℤ) := by
  obtain ⟨i, hi⟩ := (terminal hm y bs).property.1
  refine ⟨i, ?_⟩
  rw [raw_terminal_pos hm y bs h i, SwarmSegKernel.ofRecState_pos, hi]
  simp

end SwarmRawRecord
