/-
# `(factor)` for an arbitrary low-block event inside the record event

`FreshLaw.freshlaw` factorises the regeneration event, because `RegenAt` is *exactly*
`RecordAt` plus a condition on the fresh path.  The paper's own decomposition
(`RegenPath.first_block_identity`) instead sums over the pairwise disjoint events
`C_{d,t} ∩ V_{d,t}`, and `C_{d,t}` is not literally `RecordAt` — it is a *smaller* low-block
event (it also records that the earlier levels fail to regenerate).

This file states the factorization at that level of generality:

**for any measurable set `L₀` of low-block coordinates whose preimage is contained in the record
event `RecordAt`, the future factorises.**  `L = lowProj ⁻¹' L₀` plays the role of `C_{d,t}`;
containment in `RecordAt` is what `SwarmFresh.Cdt_recordAt` supplies.  Hence no new probability
estimate is needed to pass from `RecordAt` to the paper's `C_{d,t}`, and the sum over `(d,t)`
reduces to disjointness bookkeeping.

Also here: the same statement with an arbitrary set `S ⊆ nonnegPath` of allowed fresh paths, so
that both `nonnegPath` (`RegenAt`) and `strictPos` (the paper's `V`) are covered.
-/
import Swarm.PaperV

open MeasureTheory Set ProbabilityTheory
open Swarming Swarming.Uniform Swarming.Trajectory SwarmRestart
open scoped ENNReal

namespace SwarmFresh

variable {N : ℕ}

/-! ### The high-block version for an arbitrary set of allowed fresh paths -/

/-- The future event as a condition on the high block, for an arbitrary set `S` of fresh paths. -/
def highFutureGen (p : ℝ) (m : ℕ) (d : ℤ) (S B : Set (ℕ → Fin N → ℤ)) :
    Set (highSet (N := N) d → ℝ) :=
  {W | posPath p m (levelShift d (highExtend d W)) ∈ S ∩ B}

theorem measurableSet_highFutureGen (p : ℝ) (m : ℕ) (d : ℤ) {S B : Set (ℕ → Fin N → ℤ)}
    (hS : MeasurableSet S) (hB : MeasurableSet B) :
    MeasurableSet (highFutureGen (N := N) p m d S B) := by
  have hSB : MeasurableSet (S ∩ B) := hS.inter hB
  have hΦ : Measurable fun U : Array N => posPath p m (levelShift d U) :=
    (measurable_posPath p m N).comp (measurable_levelShift N d)
  have hset : highFutureGen (N := N) p m d S B
      = highExtend (N := N) d ⁻¹' {U : Array N | posPath p m (levelShift d U) ∈ S ∩ B} := by
    ext W
    simp only [highFutureGen, Set.mem_preimage, Set.mem_ofPred_eq]
  rw [hset]
  exact (measurable_highExtend d) (hΦ hSB)

/-- **The future condition is a high-block condition**, for any `S ⊆ nonnegPath`. -/
theorem highFutureGen_eq (p : ℝ) (m : ℕ) (d : ℤ) {S B : Set (ℕ → Fin N → ℤ)}
    (hSsub : S ⊆ nonnegPath (N := N)) :
    (highSet d).domRestrict ⁻¹' highFutureGen (N := N) p m d S B
      = {U : Array N | posPath p m (levelShift d U) ∈ S ∩ B} := by
  ext U
  simp only [highFutureGen, Set.mem_preimage, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    have hstay : ∀ n i,
        0 ≤ (trajectory p m (levelShift d (highExtend (N := N) d
          ((highSet d).domRestrict U))) n).pos i := hSsub h1
    have heq := posPath_shift_congr (p := p) (m := m) (d := d)
      (U := highExtend (N := N) d ((highSet d).domRestrict U)) (U' := U)
      (fun i x k hx => highExtend_domRestrict_agree d U i x k hx) hstay
    rw [← heq]
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    have hstay : ∀ n i, 0 ≤ (trajectory p m (levelShift d U) n).pos i := hSsub h1
    have heq := posPath_shift_congr (p := p) (m := m) (d := d)
      (U := U) (U' := highExtend (N := N) d ((highSet d).domRestrict U))
      (fun i x k hx => (highExtend_domRestrict_agree d U i x k hx).symm) hstay
    rw [← heq]
    exact ⟨h1, h2⟩

/-- The mass of the high-block future event is the mass of the fresh event, uniformly in `d`. -/
theorem highFutureGen_measure (p : ℝ) (m : ℕ) (d : ℤ) {S B : Set (ℕ → Fin N → ℤ)}
    (hSsub : S ⊆ nonnegPath (N := N)) (hS : MeasurableSet S) (hB : MeasurableSet B) :
    (arrayMeasure N) ((highSet d).domRestrict ⁻¹' highFutureGen (N := N) p m d S B)
      = (arrayMeasure N) {U : Array N | posPath p m U ∈ S ∩ B} := by
  rw [highFutureGen_eq p m d hSsub]
  exact measure_posPath_levelShift p m N d (hS.inter hB)


/-- On the record event, if the *shifted* path stays nonnegative then the relative future is that
path.  (The non-circular direction: `shiftAgree_while_nonneg`, not `restart_pos`.) -/
theorem relFuture_eq_of_record {p : ℝ} {m : ℕ} {U : Array N} {t : ℕ} {d : ℤ}
    (hrec : RecordAt p m U t d)
    (hnn : ∀ n i, 0 ≤ (trajectory p m (levelShift d U) n).pos i) :
    relFuture p m U t d = posPath p m (levelShift d U) := by
  funext n i
  have hsa := shiftAgree_while_nonneg (N := N) p m U hrec.1 hrec.2 n (fun k _ => hnn k)
  have h := hsa.1 i
  show (trajectory p m U (t + n)).pos i - d = (trajectory p m (levelShift d U) n).pos i
  omega

/-! ### The main statement -/

/-- **`(factor)` for an arbitrary low-block event contained in the record event.**  If
`L = (lowSet d).domRestrict ⁻¹' L₀` and every array in `L` has a record at `(t, d)`, then for any
`S ⊆ nonnegPath` of allowed fresh paths and any measurable `B`,

`P(L ∩ {relFuture ∈ S ∩ B}) = P(L) · P{posPath ∈ S ∩ B}`.

This is the exact shape needed by the paper's `(factor)`, with `L` playing the role of `C_{d,t}`
(`Cdt_recordAt` supplies the containment) and `S = strictPos` the paper's `V`. -/
theorem freshlaw_lowEvent (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ)
    {L₀ : Set (lowSet (N := N) d → ℝ)} {S B : Set (ℕ → Fin N → ℤ)}
    (hL : MeasurableSet L₀)
    (hLsub : ∀ U : Array N, (lowSet d).domRestrict U ∈ L₀ → RecordAt p m U t d)
    (hS : MeasurableSet S) (hSsub : S ⊆ nonnegPath (N := N)) (hB : MeasurableSet B) :
    (arrayMeasure N) {U : Array N | (lowSet d).domRestrict U ∈ L₀ ∧
        relFuture p m U t d ∈ S ∩ B}
      = (arrayMeasure N) {U : Array N | (lowSet d).domRestrict U ∈ L₀}
        * (arrayMeasure N) {U : Array N | posPath p m U ∈ S ∩ B} := by
  have hP : (arrayMeasure N) = Measure.infinitePi (fun _ : Fin N × ℤ × ℕ => uniform01) := rfl
  have hblock := SwarmBlock.block_measure_inter (fun _ : Fin N × ℤ × ℕ => uniform01)
    (disjoint_lowSet_highSet (N := N) d) hL (measurableSet_highFutureGen p m d hS hB)
  have hset : {U : Array N | (lowSet d).domRestrict U ∈ L₀ ∧ relFuture p m U t d ∈ S ∩ B}
      = (lowSet d).domRestrict ⁻¹' L₀
        ∩ (highSet d).domRestrict ⁻¹' highFutureGen (N := N) p m d S B := by
    ext U
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, highFutureGen]
    constructor
    · rintro ⟨hL₀, hin, hB'⟩
      have hrec := hLsub U hL₀
      have hstay : ∀ n i, d ≤ (trajectory p m U (t + n)).pos i := by
        intro n i
        have h1 : 0 ≤ relFuture p m U t d n i := hSsub hin n i
        simp only [relFuture] at h1
        omega
      have heq := relFuture_eq p m U ⟨hrec.1, hrec.2, hstay⟩
      have hstayL : ∀ n i, 0 ≤ (trajectory p m (levelShift d U) n).pos i := by
        intro n i
        have h1 : 0 ≤ relFuture p m U t d n i := hSsub hin n i
        have h2 : relFuture p m U t d n i = (trajectory p m (levelShift d U) n).pos i := by
          show (fun n i => (trajectory p m U (t + n)).pos i - d) n i
            = (trajectory p m (levelShift d U) n).pos i
          rw [heq]
          rfl
        omega
      have heq2 := posPath_shift_congr (p := p) (m := m) (d := d)
        (U := U) (U' := highExtend (N := N) d ((highSet d).domRestrict U))
        (fun i x k hx => (highExtend_domRestrict_agree d U i x k hx).symm) hstayL
      refine ⟨hL₀, ?_, ?_⟩
      · rw [← heq2, ← heq]; exact hin
      · rw [← heq2, ← heq]; exact hB'
    · rintro ⟨hL₀, h1, h2⟩
      have hrec := hLsub U hL₀
      have hnnE : ∀ n i,
          0 ≤ (trajectory p m (levelShift d (highExtend (N := N) d
            ((highSet d).domRestrict U))) n).pos i := hSsub h1
      have heq2 := posPath_shift_congr (p := p) (m := m) (d := d)
        (U := highExtend (N := N) d ((highSet d).domRestrict U)) (U' := U)
        (fun i x k hx => highExtend_domRestrict_agree d U i x k hx) hnnE
      have hnn : ∀ n i, 0 ≤ (trajectory p m (levelShift d U) n).pos i := by
        intro n i
        have h := hnnE n i
        have h2 : (trajectory p m (levelShift d (highExtend (N := N) d
            ((highSet d).domRestrict U))) n).pos i
            = (trajectory p m (levelShift d U) n).pos i := by
          have hc := congrFun (congrFun heq2 n) i
          simpa only [posPath] using hc
        omega
      have heq := relFuture_eq_of_record hrec hnn
      refine ⟨hL₀, ?_, ?_⟩
      · rw [heq, ← heq2]; exact h1
      · rw [heq, ← heq2]; exact h2
  rw [hset, hP, hblock, ← hP, highFutureGen_measure p m d hSsub hS hB]
  rfl

end SwarmFresh
