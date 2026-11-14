/-
  **Below-record information for the actual enlarged filtration.**

  At a fixed nonnegative site strictly below the running record, a mark forces the
  revelation gate.  Passing the gate puts all mark coordinates in `prefRead`; if it fails,
  the piece has no marked arrays.  The corresponding finite-prefix computation shows that
  `h_j(x)` restricted below the record is `enlFilt`-measurable.  The random predecessor at
  the record is handled by countably many fixed-site pieces.
-/
import Swarm.RecordAbove
import Swarm.EnlReveal

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory

variable {N : ℕ}

/-- The below-record cylinder for a mark on a nonempty prefix. -/
lemma measurableSet_markSet_prefRead {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p)
    {n : ℕ} {γ : Pref N n} {U₀ : Array N} (hU₀ : U₀ ∈ prefAgree p m γ)
    (j : Fin N) {x : ℕ} (hx : (x : ℤ) < recVal j γ) :
    MeasurableSet[cylAt (N := N) (prefRead n γ)]
      (markSet p m n j γ x) := by
  classical
  have hxne : (x : ℤ) ≠ recVal j γ := ne_of_lt hx
  rw [markSet, if_neg hxne]
  by_cases hg : m ≤ localTime (fun t => ext γ t j) n (x : ℤ)
  · have hgate : m ≤ (trajectory p m U₀ n).ell j (x : ℤ) := by
      rw [ell_eq_localTime_of_prefAgree p m n hU₀ le_rfl j (x : ℤ)]
      exact hg
    have hmark := measurableSet_cylAt_mark p m n le_rfl hU₀ j (x : ℤ) hgate
    have hset : {U : Array N | m ≤ localTime (fun t => ext γ t j) n (x : ℤ)
          ∧ SiteMark p m U j (x : ℤ)} = {U : Array N | SiteMark p m U j (x : ℤ)} := by
      ext U
      exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩
    rw [hset]
    exact hmark
  · have hset : {U : Array N | m ≤ localTime (fun t => ext γ t j) n (x : ℤ)
          ∧ SiteMark p m U j (x : ℤ)} = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr ?_
      rintro U ⟨hg', -⟩
      exact hg hg'
    rw [hset]
    exact (cylAt (prefRead n γ)).measurableSet_empty

/-- The actual fixed-site value below the record, set to zero elsewhere. -/
noncomputable def belowSeed (p : ℝ) (m n : ℕ) (j : Fin N) (x : ℕ) : Array N → ℝ :=
  {U : Array N | (x : ℤ) < recVal j (prefOf p m n U)}.indicator
    (fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x)

/-- A finite-cylinder computation of `belowSeed` over a fixed prefix. -/
noncomputable def belowSeedPiece (p : ℝ) (m n : ℕ) (j : Fin N)
    (γ : Pref N n) (x : ℕ) : Array N → ℝ := by
  classical
  exact if (∃ U' : Array N, U' ∈ prefAgree p m γ) ∧ (x : ℤ) < recVal j γ then
    (fun U : Array N => SwarmMarks.hof p (fun k : ℕ =>
      if k ≤ x then (if U ∈ markSet p m n j γ k then true else false)
      else false) x)
  else 0

/-- On nonempty prefixes, the below-record computation is an ordinary revealed cylinder. -/
lemma measurable_belowSeedPiece {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m n : ℕ)
    (j : Fin N) {γ : Pref N n} {U₀ : Array N} (hU₀ : U₀ ∈ prefAgree p m γ)
    {x : ℕ} (hx : (x : ℤ) < recVal j γ) :
    Measurable[cylAt (N := N) (prefRead n γ)] (belowSeedPiece p m n j γ x) := by
  classical
  have hcomp : ∀ k : ℕ, Measurable[cylAt (N := N) (prefRead n γ)]
      (fun U : Array N => if k ≤ x then
        (if U ∈ markSet p m n j γ k then true else false) else false) := by
    intro k
    by_cases hk : k ≤ x
    · have heq : (fun U : Array N => if k ≤ x then
          (if U ∈ markSet p m n j γ k then true else false) else false)
          = fun U : Array N => if U ∈ markSet p m n j γ k then true else false := by
        funext U
        rw [if_pos hk]
      rw [heq]
      exact Measurable.ite (p := fun U : Array N => U ∈ markSet p m n j γ k)
        (measurableSet_markSet_prefRead hp hU₀ j (lt_of_le_of_lt (by exact_mod_cast hk) hx))
        measurable_const measurable_const
    · have heq : (fun U : Array N => if k ≤ x then
          (if U ∈ markSet p m n j γ k then true else false) else false)
          = fun _ : Array N => false := by
        funext U
        rw [if_neg hk]
      rw [heq]
      exact measurable_const
  have hseq : Measurable[cylAt (N := N) (prefRead n γ)] (fun U : Array N => (fun k : ℕ =>
      if k ≤ x then (if U ∈ markSet p m n j γ k then true else false) else false)) := by
    letI : MeasurableSpace (Array N) := cylAt (N := N) (prefRead n γ)
    exact measurable_pi_iff.2 hcomp
  have hne : (∃ U' : Array N, U' ∈ prefAgree p m γ) ∧ (x : ℤ) < recVal j γ :=
    ⟨⟨U₀, hU₀⟩, hx⟩
  unfold belowSeedPiece
  rw [if_pos hne]
  exact fun s hs => hseq (measurable_hof_any p x hs)

/-- The prefix computation agrees pointwise with the restricted value below the record. -/
lemma belowSeed_eq_piece {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m n : ℕ) (j : Fin N)
    {γ : Pref N n} {U : Array N} (hU : U ∈ prefAgree p m γ) (x : ℕ) :
    belowSeed p m n j x U = belowSeedPiece p m n j γ x U := by
  classical
  have hrec : recVal j (prefOf p m n U) = recVal j γ := recVal_prefOf_of_mem hU j
  by_cases hx : (x : ℤ) < recVal j γ
  · have hne : (∃ U' : Array N, U' ∈ prefAgree p m γ) ∧ (x : ℤ) < recVal j γ :=
      ⟨⟨U, hU⟩, hx⟩
    have hR : U ∈ {U : Array N | (x : ℤ) < recVal j (prefOf p m n U)} := by
      show (x : ℤ) < recVal j (prefOf p m n U)
      rwa [hrec]
    rw [belowSeed, Set.indicator_of_mem hR, belowSeedPiece, if_pos hne]
    refine SwarmMarks.hof_congr x (fun k hk => ?_)
    rw [if_pos hk]
    have hxk : (k : ℤ) < recVal j γ := lt_of_le_of_lt (by exact_mod_cast hk) hx
    simp only [SwarmLogRatio.siteMarks]
    by_cases hm : U ∈ markSet p m n j γ k
    · rw [if_pos hm, decide_eq_true ((mem_markSet_iff hp m n j hU hxk.le).mp hm)]
    · rw [if_neg hm, decide_eq_false (fun hmark => hm ((mem_markSet_iff hp m n j hU hxk.le).mpr hmark))]
  · have hnot : ¬ U ∈ {U : Array N | (x : ℤ) < recVal j (prefOf p m n U)} := by
      intro hh
      have hh' : (x : ℤ) < recVal j (prefOf p m n U) := hh
      have hh'' : (x : ℤ) < recVal j γ := by rw [← hrec]; exact hh'
      exact hx hh''
    rw [belowSeed, Set.indicator_of_notMem hnot]
    by_cases hne : (∃ U' : Array N, U' ∈ prefAgree p m γ) ∧ (x : ℤ) < recVal j γ
    · exact False.elim (hx hne.2)
    · rw [belowSeedPiece, if_neg hne]
      change (0 : ℝ) = 0
      rfl

/-- The actual below-record value is measurable for the ordinary enlarged filtration. -/
theorem measurable_belowSeed {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m n : ℕ)
    (j : Fin N) (x : ℕ) :
    Measurable[enlFilt p m n] (belowSeed p m n j x) := by
  intro S hS γ
  by_cases hne : ∃ U' : Array N, U' ∈ prefAgree p m γ
  · obtain ⟨U₀, hU₀⟩ := hne
    by_cases hx : (x : ℤ) < recVal j γ
    · refine ⟨(belowSeedPiece p m n j γ x) ⁻¹' S,
        measurable_belowSeedPiece hp m n j hU₀ hx hS, ?_⟩
      ext U
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      exact and_congr_right (fun hU => by rw [belowSeed_eq_piece hp m n j hU x])
    · refine ⟨(fun _ : Array N => (0 : ℝ)) ⁻¹' S, measurable_const hS, ?_⟩
      ext U
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      exact and_congr_right (fun hU => by
        rw [belowSeed_eq_piece hp m n j hU x, belowSeedPiece, if_neg (by
          intro hh
          exact hx hh.2)]
        rfl)
  · refine ⟨(fun _ : Array N => (0 : ℝ)) ⁻¹' S, measurable_const hS, ?_⟩
    ext U
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    exact and_congr_right (fun hU => False.elim (hne ⟨U, hU⟩))

/-- Restricted integrability follows from the deterministic fixed-index bound. -/
lemma integrable_belowSeed {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n : ℕ) (j : Fin N) (x : ℕ) :
    Integrable (belowSeed p m n j x) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hmeas : Measurable (belowSeed p m n j x) := by
    intro s hs
    exact (enlFilt p m).le n _ (measurable_belowSeed hp1.le m n j x hs)
  refine Integrable.of_bound hmeas.aestronglyMeasurable (2 * (x : ℝ) + 3) ?_
  filter_upwards with U
  by_cases hR : U ∈ {U : Array N | (x : ℤ) < recVal j (prefOf p m n U)}
  · rw [belowSeed, Set.indicator_of_mem hR, Real.norm_eq_abs]
    exact SwarmShiftMarks.abs_hof_le' hp1 hp2 (by linarith) (SwarmLogRatio.siteMarks p m U j) x
  · rw [belowSeed, Set.indicator_of_notMem hR]
    simp
    positivity

/-- Conditional expectation of the actual value below the record is its restricted value. -/
theorem condExp_belowSeed {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n : ℕ) (j : Fin N) (x : ℕ) :
    condExp (enlFilt p m n) (arrayMeasure N)
        (fun U => {U : Array N | (x : ℤ) < recVal j (prefOf p m n U)}.indicator
          (fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x) U)
      = belowSeed p m n j x := by
  have hmeas := measurable_belowSeed hp1.le m n j x
  exact condExp_of_stronglyMeasurable ((enlFilt p m).le n) hmeas.stronglyMeasurable
    (integrable_belowSeed hp1 hp2 m n j x)

/-- Equality of the natural-valued record to a fixed index is enlarged-filtration measurable. -/
lemma measurableSet_recNat_eq_enl (p : ℝ) (m n : ℕ) (j : Fin N) (y : ℕ) :
    MeasurableSet[enlFilt p m n]
      {U : Array N | (recVal j (prefOf p m n U)).toNat = y} := by
  classical
  intro γ
  by_cases hy : (recVal j γ).toNat = y
  · refine ⟨Set.univ, MeasurableSet.univ, ?_⟩
    rw [Set.inter_univ]
    refine Set.Subset.antisymm Set.inter_subset_left ?_
    intro U hU
    refine ⟨hU, ?_⟩
    show (recVal j (prefOf p m n U)).toNat = y
    rw [recVal_prefOf_of_mem hU j]
    exact hy
  · refine ⟨∅, (cylAt (prefRead n γ)).measurableSet_empty, ?_⟩
    rw [Set.inter_empty]
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro U ⟨hU, hUy⟩
    show False
    apply hy
    have hUy' : (recVal j (prefOf p m n U)).toNat = y := hUy
    rwa [recVal_prefOf_of_mem hU j] at hUy'

/-- The potential at the predecessor of the running record is already measurable for the
ordinary enlarged filtration, without adjoining any additional record information. -/
theorem measurable_HprevAt_enlFilt {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m n : ℕ) (j : Fin N) :
    Measurable[enlFilt p m n] (HprevAt p m n j) := by
  classical
  letI : MeasurableSpace (Array N) := enlFilt p m n
  have hpiece : ∀ y : ℕ, Measurable fun U : Array N =>
      if y = 0 then (1 : ℝ) else belowSeed p m n j (y - 1) U := by
    intro y
    by_cases hy : y = 0
    · simp only [hy, if_true]
      exact measurable_const
    · simp only [hy, if_false]
      exact measurable_belowSeed hp m n j (y - 1)
  have hfibre : ∀ y : ℕ, MeasurableSet {U : Array N |
      (recVal j (prefOf p m n U)).toNat = y} :=
    fun y => measurableSet_recNat_eq_enl p m n j y
  have h := SwarmIID.measurable_of_countable_pieces (Ω := Array N) (ι := ℕ)
    (U := fun y : ℕ => fun U : Array N =>
      if y = 0 then (1 : ℝ) else belowSeed p m n j (y - 1) U)
    hpiece (fun U => (recVal j (prefOf p m n U)).toNat) hfibre
  have hfun : (fun U : Array N =>
      if (recVal j (prefOf p m n U)).toNat = 0 then (1 : ℝ)
      else belowSeed p m n j ((recVal j (prefOf p m n U)).toNat - 1) U) = HprevAt p m n j := by
    funext U
    by_cases hzero : (recVal j (prefOf p m n U)).toNat = 0
    · simp [HprevAt, hzero]
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hzero
      have hcast : ((recVal j (prefOf p m n U)).toNat : ℤ) = recVal j (prefOf p m n U) :=
        Int.toNat_of_nonneg (zero_le_recVal_prefOf p m U j n)
      have hkrec : (k : ℤ) < recVal j (prefOf p m n U) := by
        have hk' : (k : ℤ) + 1 = recVal j (prefOf p m n U) := by
          rw [← hcast, hk]
          push_cast
          ring
        omega
      have hR : U ∈ {U : Array N | (k : ℤ) < recVal j (prefOf p m n U)} := hkrec
      simp only [HprevAt, hk, belowSeed, Nat.succ_ne_zero, if_false]
      exact Set.indicator_of_mem
        (s := {U : Array N | (k : ℤ) < recVal j (prefOf p m n U)})
        (f := fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) (k.succ - 1)) hR
  rw [← hfun]
  exact h

/-- The paper's upper seed bound is now unconditional for the actual enlarged filtration. -/
theorem eRec_zero_le_bRec_unconditional {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n : ℕ) (j : Fin N) :
    eRec p m n j 0 ≤ᵐ[arrayMeasure N] bRec p m n j :=
  eRec_zero_le_bRec hp1 hp2 m (n := n) j (measurable_HprevAt_enlFilt hp1.le m n j)

/-- The above-record drift bound with the paper's cap, without the former information input. -/
theorem zdrift_above_eRec_bRec_unconditional {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (n : ℕ) (j : Fin N) {α : ℝ} (hα : 1 / 2 ≤ α) (k : ℕ) :
    (-bRec p m n j * fun _ : Array N => aRec p m ^ (k + 1))
      ≤ᵐ[arrayMeasure N]
        fun U => α * eRec p m n j (k + 1) U - (1 - α) * eRec p m n j k U :=
  zdrift_above_eRec_bRec hp1 hp2 m (n := n) j hm (measurable_HprevAt_enlFilt hp1.le m n j) hα k

/-- The record-boundary drift estimate with the paper's cap, without side hypotheses. -/
theorem zdrift_at_eRec_unconditional {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n : ℕ) (j : Fin N) {α : ℝ} (hα : 1 / 2 ≤ α) :
    (fun U => 1 - bRec p m n j U)
      ≤ᵐ[arrayMeasure N] fun U => α * eRec p m n j 0 U
        - (1 - α) * HprevAt p m n j U :=
  zdrift_at_eRec hp1 hp2 m (n := n) j (measurable_HprevAt_enlFilt hp1.le m n j) hα

end Swarming.Enl


