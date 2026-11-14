/-
Raw-path regeneration distance on an actual record-segment chain.

The statistic `firstRegenLevel` is the least positive raw regeneration level,
with value one when no such level exists.  The exceptional branch is kept
explicit.  No probability, stationarity, or existence of a regeneration is
assumed here.
-/
import Swarm.RawTimeStrict
import Swarm.ChainFiniteFutureKernel

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

attribute [local instance] Classical.propDecidable

namespace SwarmChainRegen

open SwarmConcat SwarmFinFuture

variable {N : ℕ}

/-- `cum k` is the first hitting time of level `k` by the concatenated path. -/
theorem tau_chainPath (c : Chain N) (k : ℕ) :
    RegenPath.tau (chainPath c) (k : ℤ) = (c.cum k : ℕ∞) := by
  rw [RegenPath.tau_eq_iff]
  constructor
  · exact c.X_record_max k
  · intro n hn i
    change c.X n i ≠ (k : ℤ)
    cases k with
    | zero => simp at hn
    | succ k =>
        have hle : c.X n i ≤ (k : ℤ) := c.X_le_record hn i
        intro heq
        push_cast at heq
        omega

/-- Raw-path regeneration and the chain's path regeneration are the same event. -/
theorem reg_chainPath_iff (c : Chain N) (k : ℕ) :
    RegenPath.Reg (chainPath c) (k : ℤ) ↔ c.RegenPath k := by
  constructor
  · rintro ⟨t, htau, hXt, hafter⟩
    have hcast : (c.cum k : ℕ∞) = (t : ℕ∞) := (tau_chainPath c k).symm.trans htau
    have htk : c.cum k = t := by exact_mod_cast hcast
    subst t
    exact ⟨hXt, hafter⟩
  · rintro ⟨hXt, hafter⟩
    exact ⟨c.cum k, tau_chainPath c k, hXt, hafter⟩

/-- Existence can be transferred between the raw and chain formulations. -/
theorem exists_reg_chainPath_iff (c : Chain N) :
    (∃ k : ℕ, 0 < k ∧ c.RegenPath k) ↔
      ∃ r : ℕ, 1 ≤ r ∧ RegenPath.Reg (chainPath c) (r : ℤ) := by
  constructor
  · rintro ⟨k, hk, hreg⟩
    exact ⟨k, hk, (reg_chainPath_iff c k).mpr hreg⟩
  · rintro ⟨k, hk, hreg⟩
    exact ⟨k, hk, (reg_chainPath_iff c k).mp hreg⟩

/-- The first positive raw regeneration level, with fallback one if none exists. -/
noncomputable def firstRegenLevel (X : RegenPath.Path N) : ℕ :=
  if h : ∃ r : ℕ, 1 ≤ r ∧ RegenPath.Reg X (r : ℤ) then Nat.find h else 1

theorem firstRegenLevel_eq_find (X : RegenPath.Path N)
    (h : ∃ r : ℕ, 1 ≤ r ∧ RegenPath.Reg X (r : ℤ)) :
    firstRegenLevel X = Nat.find h := by
  simp only [firstRegenLevel, dif_pos h]

theorem firstRegenLevel_eq_one_of_not_exists (X : RegenPath.Path N)
    (h : ¬ ∃ r : ℕ, 1 ≤ r ∧ RegenPath.Reg X (r : ℤ)) :
    firstRegenLevel X = 1 := by
  simp only [firstRegenLevel, dif_neg h]

theorem one_le_firstRegenLevel (X : RegenPath.Path N) : 1 ≤ firstRegenLevel X := by
  classical
  by_cases h : ∃ r : ℕ, 1 ≤ r ∧ RegenPath.Reg X (r : ℤ)
  · rw [firstRegenLevel_eq_find X h]
    exact (Nat.find_spec h).1
  · rw [firstRegenLevel_eq_one_of_not_exists X h]

/-- The raw `D` never takes the value zero. -/
theorem raw_D_ne_zero (X : RegenPath.Path N) : RegenPath.D X ≠ 0 := by
  classical
  unfold RegenPath.D
  split_ifs with h
  · have hk := (Nat.find_spec h).1
    exact_mod_cast (show Nat.find h ≠ 0 by omega)
  · simp

/-- On the existence branch, `firstRegenLevel` is exactly the raw `D`. -/
theorem raw_D_eq_firstRegenLevel_of_exists (X : RegenPath.Path N)
    (h : ∃ r : ℕ, 1 ≤ r ∧ RegenPath.Reg X (r : ℤ)) :
    RegenPath.D X = (firstRegenLevel X : ℕ∞) := by
  simp only [RegenPath.D, dif_pos h, firstRegenLevel_eq_find X h]

/-- A concrete value of the fallback statistic is either that finite raw `D`,
or the unique fallback value one at `D = ⊤`. -/
theorem firstRegenLevel_eq_iff (X : RegenPath.Path N) (d : ℕ) (hd : 1 ≤ d) :
    firstRegenLevel X = d ↔
      RegenPath.D X = (d : ℕ∞) ∨ (RegenPath.D X = ⊤ ∧ d = 1) := by
  classical
  by_cases h : ∃ r : ℕ, 1 ≤ r ∧ RegenPath.Reg X (r : ℤ)
  · simp only [firstRegenLevel, RegenPath.D, dif_pos h]
    constructor
    · intro heq
      exact Or.inl (congrArg (fun n : ℕ => (n : ℕ∞)) heq)
    · rintro (heq | heq)
      · exact_mod_cast heq
      · simp at heq
  · simp [firstRegenLevel, RegenPath.D, h, eq_comm]

/-- The raw extended-natural first regeneration level is measurable. -/
theorem measurable_raw_D : Measurable (RegenPath.D (N := N)) := by
  rw [ENat.measurable_iff]
  intro d
  change MeasurableSet {X : RegenPath.Path N | RegenPath.D X = (d : ℕ∞)}
  by_cases hd : 1 ≤ d
  · exact SwarmRawTimeStrict.measurableSet_D_eq d hd
  · have hd0 : d = 0 := by omega
    subst d
    have heq : {X : RegenPath.Path N | RegenPath.D X = (0 : ℕ∞)} = ∅ := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact raw_D_ne_zero X
    simp only [Nat.cast_zero]
    rw [heq]
    exact MeasurableSet.empty

/-- The Nat-valued statistic with its no-regeneration fallback is measurable. -/
theorem measurable_firstRegenLevel : Measurable (firstRegenLevel (N := N)) := by
  classical
  refine measurable_to_countable' (fun d => ?_)
  change MeasurableSet {X : RegenPath.Path N | firstRegenLevel X = d}
  by_cases hd : 1 ≤ d
  · by_cases hd1 : d = 1
    · subst d
      have heq : {X : RegenPath.Path N | firstRegenLevel X = 1} =
          {X : RegenPath.Path N | RegenPath.D X = (1 : ℕ∞)} ∪
            {X : RegenPath.Path N | RegenPath.D X = ⊤} := by
        ext X
        simpa using firstRegenLevel_eq_iff X 1 le_rfl
      rw [heq]
      exact (SwarmRawTimeStrict.measurableSet_D_eq 1 le_rfl).union
        (measurable_raw_D (measurableSet_singleton ⊤))
    · have heq : {X : RegenPath.Path N | firstRegenLevel X = d} =
          {X : RegenPath.Path N | RegenPath.D X = (d : ℕ∞)} := by
        ext X
        simpa [hd1] using firstRegenLevel_eq_iff X d hd
      rw [heq]
      exact SwarmRawTimeStrict.measurableSet_D_eq d hd
  · have heq : {X : RegenPath.Path N | firstRegenLevel X = d} = ∅ := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro heq
      have hone := one_le_firstRegenLevel X
      omega
    rw [heq]
    exact MeasurableSet.empty

/-- Away from the infinite-return exceptional event, the chain return time is
exactly the Nat-valued raw first regeneration level. -/
theorem retTime_eq_firstRegenLevel_of_ne_top (c : Chain N)
    (hret : KacFormula.retTime (fun d : Chain N => d.shift) Chain.A c ≠ ⊤) :
    KacFormula.retTime (fun d : Chain N => d.shift) Chain.A c =
      (firstRegenLevel (chainPath c) : ℕ∞) := by
  classical
  have hchain : ∃ k : ℕ, 0 < k ∧ c.RegenPath k := by
    by_contra hno
    exact hret ((Chain.retTime_eq_top_iff c).mpr hno)
  have hraw : ∃ r : ℕ, 1 ≤ r ∧ RegenPath.Reg (chainPath c) (r : ℤ) :=
    (exists_reg_chainPath_iff c).mp hchain
  let k := Nat.find hraw
  have hk := Nat.find_spec hraw
  have hleast : IsLeast {j : ℕ | 0 < j ∧ c.RegenPath j} k := by
    constructor
    · exact ⟨hk.1, (reg_chainPath_iff c k).mp hk.2⟩
    · intro j hj
      exact Nat.find_min' hraw ⟨hj.1, (reg_chainPath_iff c j).mpr hj.2⟩
  rw [Chain.retTime_eq_of_isLeast c k hleast, firstRegenLevel_eq_find _ hraw]

end SwarmChainRegen
