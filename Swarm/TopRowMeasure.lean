/-
# The record-time top row, measure level

`TopRowLaw.lean` proves, deterministically, the exact right-jump probability of a walker
standing at the record level.  This file upgrades that identity to the probability space of the
actual array, on the pieces of the enlarged filtration.

For a position prefix `γ` of length `n` that has **not yet reached** level `s` before `n`
(`∀ t < n, ext γ t i < s`), the local time at `s` is the indicator of standing there
(`pref_localTime`), so a walker standing at `s` has exactly the peers standing there as its
peer-visit count (`pref_otherVisits`), and

  `alphaOf p m n γ i = if m ≤ #topRowPref - 1 then p else 1 / 2`   (`alphaOf_top`),

with the cold specialisation `alphaOf_top_cold` for a thin top row.  Feeding this into the
enlarged-filtration fresh-coordinate law `Swarming.Enl.enl_fresh_law_piece` gives the exact
measure of "the whole top row steps left" jointly with any past event `B` read before time `n`:

  `measure_topLeftAll`:
    `μ (prefAgree γ ∩ B ∩ {all of topRowPref steps left at n})
       = ofReal ((1/2) ^ #topRowPref) * μ (prefAgree γ ∩ B)`.

"All of the top row steps left" is exactly the complement (inside the piece) of "the record level
advances at step `n`", so we also obtain the exact one-step record-advance law

  `measure_record_advance`:
    `μ (prefAgree γ ∩ B ∩ {some top-row walker steps right at n})
       = (1 - ofReal ((1/2) ^ #topRowPref)) * μ (prefAgree γ ∩ B)`,

and its unconditional `m ≥ N` form `measure_topLeftAll_of_N_le_m` (there the top row is cold for
*every* prefix, thin or not), and the unique-leader form (`#topRowPref = 1`, factor `1/2`).

Scope.  These are one-step, prefix-indexed laws: a consumer must additionally sum over the
prefixes of a random record time (the clock-fibre decomposition).  No halving clause, no
`BadTime`/`BadHalf` profile, no invariant law and no multi-step estimate is proved here.

No `sorry`, no `admit`, no custom axiom, no `native_decide`.
-/
import Swarm.EnlRight
import Swarm.RecEnv
import Swarm.TopRowLaw

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open Finset

namespace TopRow

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory Swarming.Enl RecordDefect

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. The top row of a position prefix -/

/-- The walkers standing at level `s` at time `n` of the prefix `γ`. -/
noncomputable def topRowPref (n : ℕ) (γ : Pref N n) (s : ℤ) : Finset (Fin N) :=
  univ.filter (fun j => ext γ n j = s)

theorem mem_topRowPref {n : ℕ} {γ : Pref N n} {s : ℤ} {j : Fin N} :
    j ∈ topRowPref n γ s ↔ ext γ n j = s := by
  simp [topRowPref]

/-- Peer count at the level, in top-row form. -/
theorem prefPeerCount {n : ℕ} (γ : Pref N n) {s : ℤ} {i : Fin N} (hi : ext γ n i = s) :
    ((univ.erase i).filter (fun j => ext γ n j = s)).card = (topRowPref n γ s).card - 1 := by
  classical
  have hi' : i ∈ topRowPref n γ s := mem_topRowPref.mpr hi
  have herase : (topRowPref n γ s).erase i
      = (univ.erase i).filter (fun j => ext γ n j = s) := by
    ext j
    simp only [topRowPref, mem_erase, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hji, hpj⟩
      exact ⟨⟨hji, trivial⟩, hpj⟩
    · rintro ⟨⟨hji, -⟩, hpj⟩
      exact ⟨hji, hpj⟩
  rw [← herase, card_erase_of_mem hi']

/-- A local time at a level the prefix has not reached is the standing indicator. -/
theorem pref_localTime {n : ℕ} (γ : Pref N n) {s : ℤ} (i : Fin N)
    (hlt : ∀ t, t < n → ext γ t i < s) :
    localTime (fun t => ext γ t i) n s = if ext γ n i = s then 1 else 0 :=
  localTime_level_of_lt (X := fun j t => ext γ t j) hlt

/-- The peer-visit count of a walker standing at an unreached level, in prefix form. -/
theorem pref_otherVisits {n : ℕ} (γ : Pref N n) {s : ℤ}
    (hlt : ∀ t, t < n → ∀ j : Fin N, ext γ t j < s) (i : Fin N) :
    otherVisits (fun j x => localTime (fun t => ext γ t j) n x) i s
      = ((univ.erase i).filter (fun j => ext γ n j = s)).card := by
  classical
  have hell : ∀ j : Fin N, localTime (fun t => ext γ t j) n s
      = if ext γ n j = s then 1 else 0 :=
    fun j => pref_localTime γ j (fun t ht => hlt t ht j)
  unfold otherVisits
  calc ∑ j, (if j = i then 0 else localTime (fun t => ext γ t j) n s)
      = ∑ j ∈ univ.erase i, localTime (fun t => ext γ t j) n s := by
        rw [← sum_erase_add _ _ (mem_univ i), if_pos rfl, Nat.add_zero]
        exact sum_congr rfl (fun j hj => by rw [if_neg (ne_of_mem_erase hj)])
    _ = ∑ j ∈ univ.erase i, (if ext γ n j = s then 1 else 0) :=
        sum_congr rfl (fun j _ => hell j)
    _ = ((univ.erase i).filter (fun j => ext γ n j = s)).card := by
        rw [card_eq_sum_ones, sum_filter]

/-- **The exact right probability of a top-row walker at a record prefix.** -/
theorem alphaOf_top {p : ℝ} {m n : ℕ} (γ : Pref N n) {s : ℤ}
    (hlt : ∀ t, t < n → ∀ j : Fin N, ext γ t j < s) {i : Fin N} (hi : ext γ n i = s) :
    alphaOf p m n γ i = if m ≤ (topRowPref n γ s).card - 1 then p else 1 / 2 := by
  classical
  unfold alphaOf
  rw [hi]
  unfold rightProbability
  have hov : otherVisits (fun j x => localTime (fun t => ext γ t j) n x) i s
      = (topRowPref n γ s).card - 1 := by
    rw [pref_otherVisits γ hlt i, prefPeerCount γ hi]
  by_cases h : Excited m (fun j x => localTime (fun t => ext γ t j) n x) i s
  · rw [if_pos h, if_pos ?_]
    unfold Excited at h
    rwa [hov] at h
  · rw [if_neg h, if_neg ?_]
    intro hc
    exact h (by unfold Excited; rw [hov]; exact hc)

/-- Thin top row at a record prefix: every top-row walker has right probability exactly `1/2`. -/
theorem alphaOf_top_cold {p : ℝ} {m n : ℕ} (γ : Pref N n) {s : ℤ}
    (hlt : ∀ t, t < n → ∀ j : Fin N, ext γ t j < s) (hm : 1 ≤ m)
    (hthin : (topRowPref n γ s).card ≤ m) {i : Fin N} (hi : ext γ n i = s) :
    alphaOf p m n γ i = 1 / 2 := by
  rw [alphaOf_top γ hlt hi, if_neg (by omega)]

/-! ## 2. The left-step cylinder and its exact mass -/

/-- The event that every walker of the top row steps left at time `n`. -/
def topLeftAll (p : ℝ) (m n : ℕ) (γ : Pref N n) (s : ℤ) : Set (Array N) :=
  {U | ∀ i ∈ topRowPref n γ s,
    (trajectory p m U (n + 1)).pos i = (trajectory p m U n).pos i - 1}

/-- The same event expressed through the fresh coordinates. -/
def topLeftCyl (n : ℕ) (γ : Pref N n) (s : ℤ) : Set (Array N) :=
  ⋂ i, {U : Array N | U (fr (N := N) n γ i) ∈
    (if i ∈ topRowPref n γ s then Set.Ioi (1 / 2 : ℝ) else Set.univ)}

theorem prefAgree_topLeftAll_eq {p : ℝ} {m n : ℕ} (γ : Pref N n) {s : ℤ} {B : Set (Array N)}
    (hlt : ∀ t, t < n → ∀ j : Fin N, ext γ t j < s) (hm : 1 ≤ m)
    (hthin : (topRowPref n γ s).card ≤ m) :
    prefAgree p m γ ∩ B ∩ topLeftAll p m n γ s
      = prefAgree p m γ ∩ B ∩ topLeftCyl n γ s := by
  classical
  ext U
  simp only [topLeftAll, topLeftCyl, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter]
  constructor
  · rintro ⟨⟨hU, hB⟩, hleft⟩
    refine ⟨⟨hU, hB⟩, fun i => ?_⟩
    by_cases hiT : i ∈ topRowPref n γ s
    · rw [if_pos hiT]
      have hstep : (trajectory p m U (n + 1)).pos i
          = (trajectory p m U n).pos i + drivenStep (U (fr (N := N) n γ i)) (alphaOf p m n γ i) :=
        jumpStep_of_prefAgree p m hU i
      have halpha : alphaOf p m n γ i = 1 / 2 :=
        alphaOf_top_cold γ hlt hm hthin (mem_topRowPref.mp hiT)
      rw [halpha, hleft i hiT] at hstep
      have hds : drivenStep (U (fr (N := N) n γ i)) (1 / 2 : ℝ) = -1 := by omega
      exact (drivenStep_eq_neg_one_iff _ _).mp hds
    · rw [if_neg hiT]
      exact Set.mem_univ _
  · rintro ⟨⟨hU, hB⟩, hcyl⟩
    refine ⟨⟨hU, hB⟩, fun i hiT => ?_⟩
    have hci := hcyl i
    rw [if_pos hiT] at hci
    have hstep : (trajectory p m U (n + 1)).pos i
        = (trajectory p m U n).pos i + drivenStep (U (fr (N := N) n γ i)) (alphaOf p m n γ i) :=
      jumpStep_of_prefAgree p m hU i
    have halpha : alphaOf p m n γ i = 1 / 2 :=
      alphaOf_top_cold γ hlt hm hthin (mem_topRowPref.mp hiT)
    rw [halpha] at hstep
    have hds : drivenStep (U (fr (N := N) n γ i)) (1 / 2 : ℝ) = -1 :=
      (drivenStep_eq_neg_one_iff _ _).mpr hci
    rw [hds] at hstep
    omega

theorem hI_measurable (n : ℕ) (γ : Pref N n) (s : ℤ) :
    ∀ i : Fin N, MeasurableSet (if i ∈ topRowPref n γ s then Set.Ioi (1 / 2 : ℝ)
      else (Set.univ : Set ℝ)) := by
  intro i
  by_cases h : i ∈ topRowPref n γ s
  · rw [if_pos h]; exact measurableSet_Ioi
  · rw [if_neg h]; exact MeasurableSet.univ

/-- The product of the fresh-coordinate weights of the top row. -/
theorem prod_topRow (n : ℕ) (γ : Pref N n) (s : ℤ) :
    ∏ i : Fin N, uniform01 (if i ∈ topRowPref n γ s then Set.Ioi (1 / 2 : ℝ)
        else (Set.univ : Set ℝ))
      = ENNReal.ofReal ((1 / 2 : ℝ) ^ (topRowPref n γ s).card) := by
  classical
  have hstep : ∀ i : Fin N,
      uniform01 (if i ∈ topRowPref n γ s then Set.Ioi (1 / 2 : ℝ)
        else (Set.univ : Set ℝ))
        = if i ∈ topRowPref n γ s then (ENNReal.ofReal (1 / 2 : ℝ)) else 1 := by
    intro i
    by_cases h : i ∈ topRowPref n γ s
    · rw [if_pos h, if_pos h, uniform01_Ioi (by norm_num) (by norm_num)]
      norm_num
    · rw [if_neg h, if_neg h, measure_univ]
  calc ∏ i : Fin N, uniform01 (if i ∈ topRowPref n γ s then Set.Ioi (1 / 2 : ℝ)
        else (Set.univ : Set ℝ))
      = ∏ i : Fin N, (if i ∈ topRowPref n γ s then (ENNReal.ofReal (1 / 2 : ℝ)) else 1) :=
        Finset.prod_congr rfl (fun i _ => hstep i)
    _ = ∏ _i ∈ topRowPref n γ s, (ENNReal.ofReal (1 / 2 : ℝ)) := by
        rw [← Finset.prod_filter]
        congr 1
        ext i
        simp
    _ = (ENNReal.ofReal (1 / 2 : ℝ)) ^ (topRowPref n γ s).card := by simp
    _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ (topRowPref n γ s).card) := by
        rw [← ENNReal.ofReal_pow (by norm_num)]

/-- **The exact mass of the cold top row.**  On any record prefix with a thin top row, the joint
event "the whole top row steps left" has exactly the product weight `(1/2)^a`, on every past
event `B` read before time `n`. -/
theorem measure_topLeftAll {p : ℝ} {m n : ℕ} (γ : Pref N n) {s : ℤ} {B : Set (Array N)}
    (hB : MeasurableSet[cylAt (N := N) (prefRead n γ)] B)
    (hlt : ∀ t, t < n → ∀ j : Fin N, ext γ t j < s) (hm : 1 ≤ m)
    (hthin : (topRowPref n γ s).card ≤ m) :
    arrayMeasure N (prefAgree p m γ ∩ B ∩ topLeftAll p m n γ s)
      = ENNReal.ofReal ((1 / 2 : ℝ) ^ (topRowPref n γ s).card) *
          arrayMeasure N (prefAgree p m γ ∩ B) := by
  classical
  rw [prefAgree_topLeftAll_eq γ hlt hm hthin]
  simp only [topLeftCyl]
  have hlaw := enl_fresh_law_piece (N := N) p m n γ hB
    (fun i => if i ∈ topRowPref n γ s then Set.Ioi (1 / 2 : ℝ) else (Set.univ : Set ℝ))
    (hI_measurable n γ s)
  rw [hlaw, prod_topRow]

/-- **The `m ≥ N` regime: no thinness hypothesis.**  When `N ≤ m` every top row of every prefix
is cold, so the cold-left mass is `(1/2)^a` for every record prefix. -/
theorem measure_topLeftAll_of_N_le_m {p : ℝ} {m n : ℕ} (γ : Pref N n) {s : ℤ} {B : Set (Array N)}
    (hB : MeasurableSet[cylAt (N := N) (prefRead n γ)] B)
    (hlt : ∀ t, t < n → ∀ j : Fin N, ext γ t j < s) (hm : 1 ≤ m) (hNm : N ≤ m) :
    arrayMeasure N (prefAgree p m γ ∩ B ∩ topLeftAll p m n γ s)
      = ENNReal.ofReal ((1 / 2 : ℝ) ^ (topRowPref n γ s).card) *
          arrayMeasure N (prefAgree p m γ ∩ B) := by
  refine measure_topLeftAll γ hB hlt hm ?_
  calc (topRowPref n γ s).card ≤ N := by
        rw [topRowPref]
        calc (univ.filter (fun j => ext γ n j = s)).card
            ≤ (univ : Finset (Fin N)).card := card_le_card (filter_subset _ _)
          _ = N := by simp
    _ ≤ m := hNm

/-- **The record level advances as a fair coin.**  If the top row of a record prefix is thin
(`1 ≤ m`) and a chosen walker `i` stands at the level, the probability that `i` steps right —
equivalently, that the record level advances — is exactly `1/2`.  For a unique leader this is an
equivalence, so the record advance at a unique-leader record time is exactly a fair coin. -/
theorem measure_record_advance_unique {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m n : ℕ}
    (γ : Pref N n) {s : ℤ} {B : Set (Array N)}
    (hB : MeasurableSet[cylAt (N := N) (prefRead n γ)] B)
    (hlt : ∀ t, t < n → ∀ j : Fin N, ext γ t j < s) (hm : 1 ≤ m)
    (hthin : (topRowPref n γ s).card ≤ m) {i : Fin N} (hi : ext γ n i = s) :
    arrayMeasure N (prefAgree p m γ ∩ B ∩ Swarming.StepCross.stepUp p m n i)
      = ENNReal.ofReal (1 / 2 : ℝ) * arrayMeasure N (prefAgree p m γ ∩ B) := by
  rw [enl_measure_right_piece p hp0 hp1 γ hB i, alphaOf_top_cold γ hlt hm hthin hi]

/-- **The `m ≥ N` advance form.**  In the `m ≥ N` regime the advance probability of a top-row
walker at *any* record prefix is exactly `1/2`. -/
theorem measure_record_advance_of_N_le_m {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m n : ℕ}
    (γ : Pref N n) {s : ℤ} {B : Set (Array N)}
    (hB : MeasurableSet[cylAt (N := N) (prefRead n γ)] B)
    (hlt : ∀ t, t < n → ∀ j : Fin N, ext γ t j < s) (hm : 1 ≤ m) (hNm : N ≤ m)
    {i : Fin N} (hi : ext γ n i = s) :
    arrayMeasure N (prefAgree p m γ ∩ B ∩ Swarming.StepCross.stepUp p m n i)
      = ENNReal.ofReal (1 / 2 : ℝ) * arrayMeasure N (prefAgree p m γ ∩ B) := by
  refine measure_record_advance_unique hp0 hp1 γ hB hlt hm ?_ hi
  calc (topRowPref n γ s).card ≤ N := by
        rw [topRowPref]
        calc (univ.filter (fun j => ext γ n j = s)).card
            ≤ (univ : Finset (Fin N)).card := card_le_card (filter_subset _ _)
          _ = N := by simp
    _ ≤ m := hNm

/-! ## 3. The exact record-advance law -/

/-- The event that the record level advances at step `n`, i.e. that some top-row walker steps
right. -/
def topAdvance (p : ℝ) (m n : ℕ) (γ : Pref N n) (s : ℤ) : Set (Array N) :=
  ⋃ i ∈ topRowPref n γ s, Swarming.StepCross.stepUp p m n i

theorem measurableSet_topLeftCyl (n : ℕ) (γ : Pref N n) (s : ℤ) :
    MeasurableSet (topLeftCyl (N := N) n γ s) := by
  classical
  have hset : topLeftCyl (N := N) n γ s
      = ⋂ i, (fun U : Array N => U (fr (N := N) n γ i)) ⁻¹'
          (if i ∈ topRowPref n γ s then Set.Ioi (1 / 2 : ℝ) else Set.univ) := rfl
  rw [hset]
  refine MeasurableSet.iInter (fun i => ?_)
  exact (hI_measurable n γ s i).preimage (measurable_pi_apply _)

theorem measurableSet_topAdvance (p : ℝ) (m n : ℕ) (γ : Pref N n) (s : ℤ) :
    MeasurableSet (topAdvance p m n γ s) := by
  classical
  exact Finset.measurableSet_biUnion _ (fun i _ => Swarming.StepCross.measurable_stepUp p m n i)

/-- Every step of every walker is a right step or a left step (unconditional in `U`). -/
theorem step_cases_top (p : ℝ) (m n : ℕ) (U : Array N) (i : Fin N) :
    U ∈ Swarming.StepCross.stepUp p m n i ∨ U ∈ Swarming.StepCross.stepDown p m n i := by
  classical
  have hstep : (trajectory p m U (n + 1)).pos i
      = (trajectory p m U n).pos i + drivenStep (U (departureCoord p m U n i))
        (rightProbability p m (trajectory p m U n).ell i ((trajectory p m U n).pos i)) := rfl
  by_cases h : U (departureCoord p m U n i) ≤
      rightProbability p m (trajectory p m U n).ell i ((trajectory p m U n).pos i)
  · left
    rw [Swarming.StepCross.mem_stepUp, hstep, drivenStep_eq_one_of_le h]
  · right
    rw [Swarming.StepCross.mem_stepDown, hstep, drivenStep_eq_neg_one_of_not_le h]
    omega

/-- Either the whole top row steps left, or the record level advances. -/
theorem topLeftAll_union_topAdvance (p : ℝ) (m n : ℕ) (γ : Pref N n) (s : ℤ) :
    topLeftAll p m n γ s ∪ topAdvance p m n γ s = Set.univ := by
  classical
  refine Set.eq_univ_iff_forall.mpr (fun U => ?_)
  by_cases hall : ∀ i ∈ topRowPref n γ s,
      (trajectory p m U (n + 1)).pos i = (trajectory p m U n).pos i - 1
  · exact Or.inl hall
  · rw [not_forall] at hall
    obtain ⟨i, hall⟩ := hall
    rw [not_forall] at hall
    obtain ⟨hiT, hine⟩ := hall
    refine Or.inr (Set.mem_iUnion₂.mpr ⟨i, hiT, ?_⟩)
    rcases step_cases_top p m n U i with h | h
    · exact h
    · exact absurd h hine

theorem disjoint_topLeftAll_topAdvance (p : ℝ) (m n : ℕ) (γ : Pref N n) (s : ℤ) :
    Disjoint (topLeftAll p m n γ s) (topAdvance p m n γ s) := by
  classical
  rw [Set.disjoint_left]
  intro U hl hr
  obtain ⟨i, hiT, hup⟩ := Set.mem_iUnion₂.mp hr
  rw [Swarming.StepCross.mem_stepUp] at hup
  exact absurd (hl i hiT) (by omega)

/-- **The exact record-advance law.**  On a record prefix with a thin top row, the mass of "some
top-row walker steps right" is exactly `(1 - (1/2)^a)` times the mass of the past event: the
record level advances with probability exactly `1 - (1/2)^a`. -/
theorem measure_record_advance {p : ℝ} {m n : ℕ} (γ : Pref N n) {s : ℤ} {B : Set (Array N)}
    (hB : MeasurableSet[cylAt (N := N) (prefRead n γ)] B)
    (hlt : ∀ t, t < n → ∀ j : Fin N, ext γ t j < s) (hm : 1 ≤ m)
    (hthin : (topRowPref n γ s).card ≤ m) :
    arrayMeasure N (prefAgree p m γ ∩ B ∩ topAdvance p m n γ s)
      = (1 - ENNReal.ofReal ((1 / 2 : ℝ) ^ (topRowPref n γ s).card)) *
          arrayMeasure N (prefAgree p m γ ∩ B) := by
  classical
  set A : Set (Array N) := prefAgree p m γ ∩ B with hA
  have hAmeas : MeasurableSet A :=
    (measurableSet_prefAgree_ambient p m γ).inter (cylAt_le_ambient (prefRead n γ) B hB)
  have hLmeas : MeasurableSet (A ∩ topLeftAll p m n γ s) := by
    have heq : A ∩ topLeftAll p m n γ s = A ∩ topLeftCyl (N := N) n γ s := by
      rw [hA]
      exact prefAgree_topLeftAll_eq γ hlt hm hthin
    rw [heq]
    exact hAmeas.inter (measurableSet_topLeftCyl n γ s)
  have hRmeas : MeasurableSet (A ∩ topAdvance p m n γ s) :=
    hAmeas.inter (measurableSet_topAdvance p m n γ s)
  have hdisj : Disjoint (A ∩ topLeftAll p m n γ s) (A ∩ topAdvance p m n γ s) :=
    (disjoint_topLeftAll_topAdvance p m n γ s).mono Set.inter_subset_right Set.inter_subset_right
  have hunion : A ∩ topLeftAll p m n γ s ∪ A ∩ topAdvance p m n γ s = A := by
    rw [← Set.inter_union_distrib_left, topLeftAll_union_topAdvance, Set.inter_univ]
  have hsum : arrayMeasure N (A ∩ topAdvance p m n γ s)
      + arrayMeasure N (A ∩ topLeftAll p m n γ s) = arrayMeasure N A := by
    rw [add_comm, ← measure_union hdisj hRmeas, hunion]
  have hL : arrayMeasure N (A ∩ topLeftAll p m n γ s)
      = ENNReal.ofReal ((1 / 2 : ℝ) ^ (topRowPref n γ s).card) * arrayMeasure N A := by
    rw [hA]
    exact measure_topLeftAll γ hB hlt hm hthin
  have hMtop : arrayMeasure N A ≠ ⊤ := measure_ne_top _ _
  have hR : arrayMeasure N (A ∩ topAdvance p m n γ s)
      = arrayMeasure N A - ENNReal.ofReal ((1 / 2 : ℝ) ^ (topRowPref n γ s).card)
          * arrayMeasure N A := by
    refine ENNReal.eq_sub_of_add_eq
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hMtop) ?_
    rw [← hL]
    exact hsum
  rw [hA] at hR
  rw [hR]
  rw [ENNReal.sub_mul (a := 1) (b := ENNReal.ofReal ((1 / 2 : ℝ) ^ (topRowPref n γ s).card))
    (c := arrayMeasure N (prefAgree p m γ ∩ B)) (fun _ _ => measure_ne_top _ _), one_mul]

end TopRow
