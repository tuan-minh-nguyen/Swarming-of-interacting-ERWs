/-
Measured arbitrary raw futures after a fixed finite record prefix.

The strict-positivity horizon is the actual raw duration of the prefix.  The
pattern set is arbitrary and reads the complete raw future.  On the exact raw
prefix cylinder, the array mass is a finite sum with the recovered record
product weight and the unrestricted suffix weight at the actual compact
terminal state.  This is not a full decomposition of all positive prefixes.
-/
import Swarm.RawRecordPrefix
import Swarm.MeasuredRecordSections
import Swarm.ArrayThreeFuture

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators
open SimJump

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace SwarmMeasuredRawRecord

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Transition Swarming.CurrentState
open SimJump.Record SwarmRec SwarmFreshArray SwarmArrayWords SwarmRawRecord
open SwarmFinHorizon SwarmFreshPos SwarmFreshCyl SwarmRestart SwarmFresh

attribute [local instance] Classical.propDecidable

variable {N m : ℕ}

/-- The raw window conditioned on one exact finite word prefix. -/
def rawPrefixWindow (p : ℝ) (m : ℕ) {K : ℕ} (qf : Fin K → JumpVec N)
    (s : ℕ) (C : Set (Fin (K + s + 1) → Fin N → ℤ)) : Set (Array N) :=
  {U | jumpWord p m K U = qf ∧ posPath p m U ∈
    finStrict (N := N) K ∩ pathPat (N := N) (K + s) ⁻¹' C}

/-- On the actual array, the fixed-prefix window is a two-block word event. -/
theorem rawPrefixWindow_eq_wordSet (p : ℝ) (m : ℕ) {K : ℕ}
    (qf : Fin K → JumpVec N) (s : ℕ)
    (C : Set (Fin (K + s + 1) → Fin N → ℤ)) :
    rawPrefixWindow p m qf s C =
      {U : Array N | prefWord (jumpWord p m (K + s) U) = qf ∧
        PosSeqFin (N := N) (prefWord (jumpWord p m (K + s) U)) ∧
        patOf (N := N) (catWord (prefWord (jumpWord p m (K + s) U))
          (suffWord (jumpWord p m (K + s) U))) ∈ C} := by
  ext U
  have hbox := mem_jbox_jumpWord p m (K + s) U
  have hpat := pathPat_posPath_eq_patOf p m (K + s)
    (jumpWord p m (K + s) U) hbox
  have hpos := SwarmArrayFuture.posPath_mem_finStrict_pref_iff p m K s
    (jumpWord p m (K + s) U) hbox
  have hprefix : prefWord (N := N) (k1 := K) (k2 := s)
      (jumpWord p m (K + s) U) = jumpWord p m K U := by
    funext j i
    rfl
  change jumpWord p m K U = qf ∧
      (posPath p m U ∈ finStrict (N := N) K ∧
        pathPat (N := N) (K + s) (posPath p m U) ∈ C) ↔ _
  rw [hpat, hpos, ← catWord_pref_suff (jumpWord p m (K + s) U)]
  simp only [prefWord_catWord, Set.mem_ofPred_eq, hprefix]

/-- Exact measured two-block sum on any fixed raw-prefix cylinder. -/
theorem arrayMeasure_rawPrefixWindow_twoBlock
    (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) {K : ℕ}
    (qf : Fin K → JumpVec N) (s : ℕ)
    (C : Set (Fin (K + s + 1) → Fin N → ℤ)) :
    (arrayMeasure N) (rawPrefixWindow p m qf s C) =
      ∑ qs : Fin s → JumpVec N,
        if PosSeqFin (N := N) qf ∧ patOf (N := N) (catWord qf qs) ∈ C then
          ENNReal.ofReal
            (pathW p K qf (startState (N := N) m) *
              pathW p s qs (capState m (runJ m (extendPath qf) K)))
        else 0 := by
  rw [rawPrefixWindow_eq_wordSet]
  rw [mass_wordSet_split_factored p hp0 hp1 m K s
    (fun q₁ q₂ => q₁ = qf ∧ PosSeqFin (N := N) q₁ ∧
      patOf (N := N) (catWord q₁ q₂) ∈ C)]
  rw [sum_split_words (N := N) (fun q₁ q₂ =>
    if q₁ = qf ∧ PosSeqFin (N := N) q₁ ∧
        patOf (N := N) (catWord q₁ q₂) ∈ C then
      ENNReal.ofReal
        (pathW p K q₁ (startState (N := N) m) *
          pathW p s q₂ (capState m (runJ m (extendPath q₁) K)))
    else 0)]
  rw [Finset.sum_eq_single qf]
  · apply Finset.sum_congr rfl
    intro qs hqs
    by_cases hpos : PosSeqFin (N := N) qf
    · by_cases hC : patOf (N := N) (catWord qf qs) ∈ C
      · rw [if_pos ⟨rfl, hpos, hC⟩, if_pos ⟨hpos, hC⟩]
      · rw [if_neg (fun h => hC h.2.2), if_neg (fun h => hC h.2)]
    · rw [if_neg (fun h => hpos h.2.1), if_neg (fun h => hpos h.1)]
  · intro q₁ hq₁ hne
    apply Finset.sum_eq_zero
    intro qs hqs
    exact if_neg (fun h => hne h.1)
  · intro hnot
    exact absurd (Finset.mem_univ qf) hnot

/-- **Measured fixed-record-prefix identity.**  The initial compact state is
required only to expand to the actual raw-array start.  Every record block is
first-record at its actual predecessor.  The whole-prefix `PosSeqFin` test and
every unrestricted suffix weight remain in the sum. -/
theorem arrayMeasure_rawPrefixWindow_terminal
    (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (y : RecState N m) (hy : ofRecState y = SwarmFreshArray.startState (N := N) m)
    (bs : List (RawBlock N)) (hbs : AllFirst hm y bs) (s : ℕ)
    (C : Set (Fin (rawLen bs + s + 1) → Fin N → ℤ)) :
    (arrayMeasure N) (rawPrefixWindow p m (rawWord bs) s C) =
      ∑ qs : Fin s → JumpVec N,
        if PosSeqFin (N := N) (rawWord bs) ∧
            patOf (N := N) (catWord (rawWord bs) qs) ∈ C then
          ENNReal.ofReal
            (prefixW p hm y bs *
              pathW p s qs (ofRecState (terminal hm y bs)))
        else 0 := by
  rw [arrayMeasure_rawPrefixWindow_twoBlock p hp0 hp1 m]
  apply Finset.sum_congr rfl
  intro qs hqs
  by_cases hcond : PosSeqFin (N := N) (rawWord bs) ∧
      patOf (N := N) (catWord (rawWord bs) qs) ∈ C
  · rw [if_pos hcond, if_pos hcond]
    congr 1
    calc
      pathW p (rawLen bs) (rawWord bs) (startState (N := N) m) *
          pathW p s qs (capState m (runJ m (extendPath (rawWord bs)) (rawLen bs))) =
        pathW p (rawLen bs + s) (catWord (rawWord bs) qs)
          (startState (N := N) m) := by
            symm
            simpa only [prefWord_catWord, suffWord_catWord] using
              (pathW_split p m (rawLen bs) s (catWord (rawWord bs) qs))
      _ = pathW p (rawLen bs + s) (catWord (rawWord bs) qs) (ofRecState y) := by rw [hy]
      _ = prefixW p hm y bs * pathW p s qs (ofRecState (terminal hm y bs)) :=
        pathW_rawWord_future_terminal p hm y bs hbs qs
  · rw [if_neg hcond, if_neg hcond]

/-- Canonical-start specialisation.  No fresh initial law beyond the accepted
`freshRecState` compatibility is introduced. -/
theorem arrayMeasure_rawPrefixWindow_fresh
    (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (i₀ : Fin N) (bs : List (RawBlock N))
    (hbs : AllFirst hm (freshRecState (N := N) hm i₀) bs) (s : ℕ)
    (C : Set (Fin (rawLen bs + s + 1) → Fin N → ℤ)) :
    (arrayMeasure N) (rawPrefixWindow p m (rawWord bs) s C) =
      ∑ qs : Fin s → JumpVec N,
        if PosSeqFin (N := N) (rawWord bs) ∧
            patOf (N := N) (catWord (rawWord bs) qs) ∈ C then
          ENNReal.ofReal
            (prefixW p hm (freshRecState (N := N) hm i₀) bs *
              pathW p s qs
                (ofRecState (terminal hm (freshRecState (N := N) hm i₀) bs)))
        else 0 :=
  arrayMeasure_rawPrefixWindow_terminal p hp0 hp1 hm _
    (ofRecState_freshRecState hm i₀) bs hbs s C

/-- The fixed-record-prefix theorem has genuine nonempty positive data: one
all-right jump is a first record and is strictly positive. -/
theorem exists_canonical_positive_recordPrefix {m : ℕ} (hm : 1 ≤ m) (i₀ : Fin N) :
    ∃ (y : RecState N m) (bs : List (RawBlock N)),
      ofRecState y = SwarmFreshArray.startState (N := N) m ∧ AllFirst hm y bs ∧
        bs.length = 1 ∧ rawLen bs = 1 ∧ PosSeqFin (N := N) (rawWord bs) := by
  let y : RecState N m := freshRecState (N := N) hm i₀
  let b : RawBlock N := ⟨1, fun _ => (fun _ => true : JumpVec N)⟩
  have hraw : rawWord [b] = b.2 := by
    funext j
    change Fin 1 at j
    fin_cases j
    simp [rawWord, catWord, b]
  refine ⟨y, [b], ofRecState_freshRecState hm i₀, ?_, rfl, rfl, ?_⟩
  · change FirstRecord (extendPath b.2) b.1 (ofRecState y) ∧ True
    refine ⟨?_, trivial⟩
    simpa [b, y] using firstRecord_one_allRight
      (freshRecState_mem_srSet (N := N) hm i₀) i₀
  · rw [hraw]
    simpa [rawLen, b] using (posSeqFin_one_allRight (N := N))

end SwarmMeasuredRawRecord
