/-
Focused filtration theory for the actual canonical record clock.

This is a dependency extraction of definitions in `RecordoSupply` and
`RecordMeas`: definition bodies and namespaces are unchanged, but no analytic
front, stopped-law, or tightness module is imported. Integration should make
those broad modules import this core rather than duplicate it.

At a positive candidate time, a `recTimeA` fibre is exactly
`ReachAll ∩ firstRecordAt`. The finite-prefix factor and its defect band are
adapted; `ReachAll` is the exact future-dependent residual. At zero and for a
positive level, the fibre is exactly the complement of `ReachAll`. There is no
unconditional stopping-time assertion for this zero-defaulted function.
-/
import Swarm.EnlFilt
import Swarm.RecordDefect

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Classical
open scoped BigOperators ENNReal
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory

namespace RecordoSupply

/-- The actual trajectory in the shape of the abstract development.
This is the original `RecordoSupply.actX` definition, extracted unchanged. -/
noncomputable def actX {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) :
    Fin N → ℕ → ℤ :=
  fun i n => (trajectory p m U n).pos i

/-- The actual trajectory starts at the origin. -/
theorem actX_zero {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) :
    actX p m U i 0 = 0 := by
  simp [actX]

open RecordDefect
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The running swarm maximum at time zero vanishes. -/
theorem runMax_zero (X : ι → ℕ → ℤ) (h0 : ∀ i, X i 0 = 0) : runMax X 0 = 0 := by
  refine le_antisymm ?_ ?_
  · exact Finset.sup'_le (s := Finset.univ) (f := fun i => X i 0)
      Finset.univ_nonempty (fun i _ => by rw [h0 i])
  · have hle := le_runMax (X := X) 0 (Classical.arbitrary ι)
    rw [h0 (Classical.arbitrary ι)] at hle
    exact hle

end RecordoSupply

namespace SwarmRecordMeas

open RecordDefect RecordoSupply Swarming.Uniform

section Toolkit
variable {α : Type*} [MeasurableSpace α] {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Level-set characterisation of a nonempty finite supremum. -/
theorem finset_sup'_eq_iff {s : Finset ι} (H : s.Nonempty) (f : ι → ℤ) (k : ℤ) :
    s.sup' H f = k ↔ (∀ i ∈ s, f i ≤ k) ∧ ∃ i ∈ s, f i = k := by
  constructor
  · intro h
    refine ⟨(Finset.sup'_le_iff H f).1 h.le, ?_⟩
    obtain ⟨i, hi, hval⟩ := Finset.exists_mem_eq_sup' H f
    exact ⟨i, hi, hval.symm.trans h⟩
  · rintro ⟨h1, i, hi, hik⟩
    refine le_antisymm ((Finset.sup'_le_iff H f).2 h1) ?_
    have hle : f i ≤ s.sup' ⟨i, hi⟩ f := Finset.le_sup' f hi
    rw [show (⟨i, hi⟩ : s.Nonempty) = H from Subsingleton.elim _ _] at hle
    exact hik ▸ hle

/-- Level-set characterisation of a nonempty finite infimum. -/
theorem finset_inf'_eq_iff {s : Finset ι} (H : s.Nonempty) (f : ι → ℤ) (k : ℤ) :
    s.inf' H f = k ↔ (∀ i ∈ s, k ≤ f i) ∧ ∃ i ∈ s, f i = k := by
  constructor
  · intro h
    refine ⟨(Finset.le_inf'_iff H f).1 h.ge, ?_⟩
    obtain ⟨i, hi, hval⟩ := Finset.exists_mem_eq_inf' H f
    exact ⟨i, hi, hval.symm.trans h⟩
  · rintro ⟨h1, i, hi, hik⟩
    refine le_antisymm ?_ ((Finset.le_inf'_iff H f).2 h1)
    have hle : s.inf' ⟨i, hi⟩ f ≤ f i := Finset.inf'_le f hi
    rw [show (⟨i, hi⟩ : s.Nonempty) = H from Subsingleton.elim _ _] at hle
    exact hik ▸ hle

/-- A finite supremum of measurable integer-valued functions is measurable. -/
theorem measurable_finset_sup' {f : ι → α → ℤ} (hf : ∀ i, Measurable (f i)) :
    Measurable fun a => Finset.univ.sup' Finset.univ_nonempty (fun i => f i a) := by
  refine measurable_to_countable' fun k => ?_
  change MeasurableSet {a | Finset.univ.sup' Finset.univ_nonempty (fun i => f i a) = k}
  have hset : {a | Finset.univ.sup' Finset.univ_nonempty (fun i => f i a) = k} =
      (⋂ i : ι, {a | f i a ≤ k}) ∩ (⋃ i : ι, {a | f i a = k}) := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_iUnion]
    rw [finset_sup'_eq_iff]
    constructor
    · rintro ⟨h1, i, -, h2⟩
      exact ⟨fun j => h1 j (Finset.mem_univ j), i, h2⟩
    · rintro ⟨h1, i, h2⟩
      exact ⟨fun j _ => h1 j, i, Finset.mem_univ i, h2⟩
  rw [hset]
  exact (MeasurableSet.iInter fun i => measurableSet_le (hf i) measurable_const).inter
    (MeasurableSet.iUnion fun i => (hf i) (measurableSet_singleton k))

/-- A finite infimum of measurable integer-valued functions is measurable. -/
theorem measurable_finset_inf' {f : ι → α → ℤ} (hf : ∀ i, Measurable (f i)) :
    Measurable fun a => Finset.univ.inf' Finset.univ_nonempty (fun i => f i a) := by
  refine measurable_to_countable' fun k => ?_
  change MeasurableSet {a | Finset.univ.inf' Finset.univ_nonempty (fun i => f i a) = k}
  have hset : {a | Finset.univ.inf' Finset.univ_nonempty (fun i => f i a) = k} =
      (⋂ i : ι, {a | k ≤ f i a}) ∩ (⋃ i : ι, {a | f i a = k}) := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_iUnion]
    rw [finset_inf'_eq_iff]
    constructor
    · rintro ⟨h1, i, -, h2⟩
      exact ⟨fun j => h1 j (Finset.mem_univ j), i, h2⟩
    · rintro ⟨h1, i, h2⟩
      exact ⟨fun j _ => h1 j, i, Finset.mem_univ i, h2⟩
  rw [hset]
  exact (MeasurableSet.iInter fun i => measurableSet_le measurable_const (hf i)).inter
    (MeasurableSet.iUnion fun i => (hf i) (measurableSet_singleton k))

/-- `runMax` of a measurable family is measurable. -/
theorem measurable_runMax {f : ι → α → ℤ} (hf : ∀ i, Measurable (f i)) (n : ℕ) :
    Measurable fun a => runMax (fun i _ => f i a) n :=
  measurable_finset_sup' hf

/-- `runMin` of a measurable family is measurable. -/
theorem measurable_runMin {f : ι → α → ℤ} (hf : ∀ i, Measurable (f i)) (n : ℕ) :
    Measurable fun a => runMin (fun i _ => f i a) n :=
  measurable_finset_inf' hf

end Toolkit

section Patch
variable {α : Type*}

/-- The least witness of a family of predicates, with decidability fixed. -/
noncomputable def firstHit (P : α → ℕ → Prop) (h : ∀ a, ∃ n, P a n) (a : α) : ℕ :=
  @Nat.find (P a) (Classical.decPred (P a)) (h a)

theorem firstHit_eq (P : α → ℕ → Prop) (h : ∀ a, ∃ n, P a n) (a : α) :
    firstHit P h a = @Nat.find (P a) (Classical.decPred (P a)) (h a) := rfl

theorem firstHit_spec (P : α → ℕ → Prop) (h : ∀ a, ∃ n, P a n) (a : α) :
    P a (firstHit P h a) := by
  rw [firstHit_eq]
  exact Nat.find_spec (h a)

theorem firstHit_min (P : α → ℕ → Prop) (h : ∀ a, ∃ n, P a n) (a : α) {n : ℕ}
    (hn : n < firstHit P h a) : ¬ P a n := by
  rw [firstHit_eq] at hn
  exact Nat.find_min (h a) hn

theorem firstHit_min' (P : α → ℕ → Prop) (h : ∀ a, ∃ n, P a n) (a : α) {n : ℕ}
    (hn : P a n) : firstHit P h a ≤ n := by
  rw [firstHit_eq]
  exact Nat.find_min' (h a) hn

end Patch

namespace Actual
open RecordDefect RecordoSupply Swarming.Uniform
variable {N : ℕ} [Nonempty (Fin N)]

/-- Every level is eventually attained by the actual running maximum. -/
def ReachAll (p : ℝ) (m : ℕ) : Set (Array N) :=
  {U | ∀ r : ℕ, ∃ n : ℕ, runMax (actX p m U) n = (r : ℤ)}

/-- The defaulting predicate used by the original canonical record clock. -/
def hitPred (p : ℝ) (m : ℕ) (r : ℕ) (U : Array N) (n : ℕ) : Prop :=
  U ∉ ReachAll (N := N) p m ∨ runMax (actX p m U) n = (r : ℤ)

/-- The defaulting predicate always has a witness. -/
theorem hitExists (p : ℝ) (m : ℕ) (r : ℕ) :
    ∀ U : Array N, ∃ n : ℕ, hitPred p m r U n := by
  intro U
  by_cases hU : U ∈ ReachAll (N := N) p m
  · obtain ⟨n, hn⟩ := hU r
    exact ⟨n, Or.inr hn⟩
  · exact ⟨0, Or.inl hU⟩

/-- The original canonical record time, with zero fallback off `ReachAll`. -/
noncomputable def recTimeA (p : ℝ) (m : ℕ) (U : Array N) (r : ℕ) : ℕ :=
  firstHit (hitPred p m r) (hitExists p m r) U

theorem recTimeA_spec (p : ℝ) (m : ℕ) (U : Array N) (r : ℕ) :
    hitPred p m r U (recTimeA p m U r) :=
  firstHit_spec (hitPred p m r) (hitExists p m r) U

theorem recTimeA_min (p : ℝ) (m : ℕ) (U : Array N) (r n : ℕ)
    (hn : n < recTimeA p m U r) : ¬ hitPred p m r U n :=
  firstHit_min (hitPred p m r) (hitExists p m r) U hn

/-- The level-zero record time is zero pointwise. -/
theorem recTimeA_zero (p : ℝ) (m : ℕ) (U : Array N) :
    recTimeA p m U 0 = 0 := by
  have hz : runMax (actX p m U) 0 = ((0 : ℕ) : ℤ) := by
    simpa using runMax_zero (actX p m U) (actX_zero p m U)
  have hle := firstHit_min' (hitPred p m 0) (hitExists p m 0) U (Or.inr hz)
  exact le_antisymm (by simpa only [recTimeA] using hle) (Nat.zero_le _)

/-- On `ReachAll`, a record fibre is its finite first-hit description. -/
theorem recTimeA_eq_iff (p : ℝ) (m : ℕ) (U : Array N) (r k : ℕ)
    (hU : U ∈ ReachAll (N := N) p m) :
    recTimeA p m U r = k ↔
      runMax (actX p m U) k = (r : ℤ) ∧
        ∀ j : ℕ, j < k → runMax (actX p m U) j ≠ (r : ℤ) := by
  have hspec : runMax (actX p m U) (recTimeA p m U r) = (r : ℤ) :=
    (recTimeA_spec p m U r).resolve_left (fun h => h hU)
  constructor
  · intro h
    refine ⟨by rw [← h]; exact hspec, ?_⟩
    intro j hj hval
    exact recTimeA_min p m U r j (by omega) (Or.inr hval)
  · rintro ⟨h1, h2⟩
    refine le_antisymm
      (firstHit_min' (hitPred p m r) (hitExists p m r) U (Or.inr h1)) ?_
    exact Nat.le_of_not_lt fun hlt => h2 (recTimeA p m U r) hlt hspec

/-- Off `ReachAll` every level of the defaulted record clock is zero. -/
theorem recTimeA_eq_zero_of_not_reach {p : ℝ} {m : ℕ} {U : Array N}
    (hU : U ∉ ReachAll p m) (r : ℕ) : recTimeA p m U r = 0 := by
  have hle : firstHit (hitPred p m r) (hitExists p m r) U ≤ 0 :=
    firstHit_min' _ _ U (Or.inl hU)
  exact le_antisymm hle (Nat.zero_le _)

/-- Evaluating the defect at a known record time uses only that time slice. -/
theorem defectA_eq_of_recTimeA_eq (p : ℝ) (m : ℕ) (U : Array N) (r k : ℕ)
    (h : recTimeA p m U r = k) :
    defect (actX p m U) (recTimeA p m U) r = (r : ℤ) - runMin (actX p m U) k := by
  rw [defect, h]

end Actual
end SwarmRecordMeas

namespace ActualRecordFiltration
open RecordDefect RecordoSupply SwarmRecordMeas SwarmRecordMeas.Actual
variable {N : ℕ} [Nonempty (Fin N)]

/-- The finite-prefix event that the running maximum first equals `r` at `s`. -/
def firstRecordAt (p : ℝ) (m : ℕ) (r s : ℕ) : Set (Array N) :=
  {U | runMax (actX p m U) s = (r : ℤ) ∧
    ∀ t < s, runMax (actX p m U) t ≠ (r : ℤ)}

/-- The first-hit prefix together with its candidate-time defect band. -/
def recordPrefixBand (p : ℝ) (m : ℕ) (r s L : ℕ) : Set (Array N) :=
  firstRecordAt p m r s ∩ {U | ((r : ℤ) - runMin (actX p m U) s).toNat ≤ L}

/-- The actual running maximum at a revealed time is adapted. -/
theorem enl_measurable_runMax_actX (p : ℝ) (m : ℕ) {k s : ℕ} (hk : k ≤ s) :
    Measurable[Swarming.Enl.enlFilt p m s] (fun U : Array N => runMax (actX p m U) k) := by
  exact @SwarmRecordMeas.measurable_runMax (Array N)
    (Swarming.Enl.enlFilt p m s) (Fin N) _ _
    (fun i (U : Array N) => actX p m U i k)
    (fun i => Swarming.Enl.enl_pos_measurable p m s hk i) k

/-- The actual running minimum at a revealed time is adapted. -/
theorem enl_measurable_runMin_actX (p : ℝ) (m : ℕ) {k s : ℕ} (hk : k ≤ s) :
    Measurable[Swarming.Enl.enlFilt p m s] (fun U : Array N => runMin (actX p m U) k) := by
  exact @SwarmRecordMeas.measurable_runMin (Array N)
    (Swarming.Enl.enlFilt p m s) (Fin N) _ _
    (fun i (U : Array N) => actX p m U i k)
    (fun i => Swarming.Enl.enl_pos_measurable p m s hk i) k

/-- The finite first-hit event is adapted, with no `ReachAll` hypothesis. -/
theorem measurableSet_firstRecordAt (p : ℝ) (m : ℕ) (r s : ℕ) :
    MeasurableSet[Swarming.Enl.enlFilt p m s] (firstRecordAt (N := N) p m r s) := by
  have heq : firstRecordAt (N := N) p m r s =
      {U : Array N | runMax (actX p m U) s = (r : ℤ)} ∩
        ⋂ t ∈ Finset.range s, {U : Array N | runMax (actX p m U) t ≠ (r : ℤ)} := by
    ext U
    simp only [firstRecordAt, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
      Finset.mem_range]
  rw [heq]
  refine ((enl_measurable_runMax_actX p m (Nat.le_refl s))
    (measurableSet_singleton (r : ℤ))).inter ?_
  refine MeasurableSet.biInter (Finset.countable_toSet _) fun t ht => ?_
  exact ((enl_measurable_runMax_actX p m (Nat.le_of_lt (Finset.mem_range.1 ht)))
    (measurableSet_singleton (r : ℤ))).compl

/-- `Int.toNat` preserves adapted measurability on the countable integers. -/
theorem measurable_toNat_of_measurable {mS : MeasurableSpace (Array N)}
    {f : Array N → ℤ} (hf : Measurable[mS] f) :
    Measurable[mS] (fun U => (f U).toNat) :=
  (measurable_of_countable (fun z : ℤ => z.toNat)).comp hf

/-- The candidate-time defect-band prefix is adapted for arbitrary `r,s,L`. -/
theorem measurableSet_recordPrefixBand (p : ℝ) (m : ℕ) (r s L : ℕ) :
    MeasurableSet[Swarming.Enl.enlFilt p m s] (recordPrefixBand (N := N) p m r s L) := by
  refine (measurableSet_firstRecordAt p m r s).inter ?_
  exact measurableSet_le
    (measurable_toNat_of_measurable
      (measurable_const.sub (enl_measurable_runMin_actX p m (Nat.le_refl s)))) measurable_const

/-- Exact positive-time record-fibre decomposition. -/
theorem recTimeA_eq_iff_reach_all_firstRecordAt {p : ℝ} {m : ℕ} {r s : ℕ}
    (hs : 1 ≤ s) (U : Array N) :
    recTimeA p m U r = s ↔ U ∈ ReachAll p m ∧ U ∈ firstRecordAt p m r s := by
  constructor
  · intro hτ
    have hreach : U ∈ ReachAll p m := by
      by_contra hU
      rw [recTimeA_eq_zero_of_not_reach hU r] at hτ
      omega
    exact ⟨hreach, (recTimeA_eq_iff p m U r s hreach).1 hτ⟩
  · rintro ⟨hreach, hhit⟩
    exact (recTimeA_eq_iff p m U r s hreach).2 hhit

/-- The defect-band fibre has the measurable prefix band and exactly `ReachAll`
as its residual at every positive candidate time. -/
theorem defectBand_recTimeA_eq_reach_all_prefix {p : ℝ} {m : ℕ} {r s L : ℕ}
    (hs : 1 ≤ s) :
    {U : Array N | recTimeA p m U r = s ∧
        (defect (actX p m U) (recTimeA p m U) r).toNat ≤ L} =
      ReachAll p m ∩ recordPrefixBand p m r s L := by
  ext U
  constructor
  · rintro ⟨hτ, hband⟩
    obtain ⟨hreach, hhit⟩ := (recTimeA_eq_iff_reach_all_firstRecordAt hs U).1 hτ
    refine ⟨hreach, hhit, ?_⟩
    rw [defectA_eq_of_recTimeA_eq p m U r s hτ] at hband
    exact hband
  · rintro ⟨hreach, hhit, hband⟩
    have hτ : recTimeA p m U r = s :=
      (recTimeA_eq_iff_reach_all_firstRecordAt hs U).2 ⟨hreach, hhit⟩
    refine ⟨hτ, ?_⟩
    rw [defectA_eq_of_recTimeA_eq p m U r s hτ]
    exact hband

/-- For a positive level, the zero fibre is exactly the off-`ReachAll` event. -/
theorem recTimeA_eq_zero_iff_not_reach {p : ℝ} {m : ℕ} {r : ℕ}
    (hr : 1 ≤ r) (U : Array N) :
    recTimeA p m U r = 0 ↔ U ∉ ReachAll p m := by
  constructor
  · intro hτ hreach
    have hhit := ((recTimeA_eq_iff p m U r 0 hreach).1 hτ).1
    have hz : runMax (actX p m U) 0 = 0 := runMax_zero _ (actX_zero p m U)
    rw [hz] at hhit
    have hr' : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
    omega
  · intro hU
    exact recTimeA_eq_zero_of_not_reach (N := N) hU r

/-- At positive level, adaptedness of the zero fibre at `F_0` is exactly
adaptedness of the future-dependent `ReachAll` event. -/
theorem measurableSet_recTimeA_zero_iff_reachAll (p : ℝ) (m : ℕ) {r : ℕ}
    (hr : 1 ≤ r) :
    MeasurableSet[Swarming.Enl.enlFilt p m 0] {U : Array N | recTimeA p m U r = 0} ↔
      MeasurableSet[Swarming.Enl.enlFilt p m 0] (ReachAll (N := N) p m) := by
  have heq : {U : Array N | recTimeA p m U r = 0} = (ReachAll p m)ᶜ := by
    ext U
    exact recTimeA_eq_zero_iff_not_reach hr U
  rw [heq]
  exact ⟨fun h => by simpa using h.compl, fun h => h.compl⟩

/-- Measurable `ReachAll` is sufficient for every fibre of a positive-level
record clock to be adapted. Zero and positive times use separate exact formulas. -/
theorem measurableSet_recTimeA_eq_of_reachAll (p : ℝ) (m : ℕ) {r s : ℕ}
    (hr : 1 ≤ r)
    (hR : MeasurableSet[Swarming.Enl.enlFilt p m s] (ReachAll (N := N) p m)) :
    MeasurableSet[Swarming.Enl.enlFilt p m s] {U : Array N | recTimeA p m U r = s} := by
  cases s with
  | zero =>
      have heq : {U : Array N | recTimeA p m U r = 0} = (ReachAll p m)ᶜ := by
        ext U
        exact recTimeA_eq_zero_iff_not_reach hr U
      rw [heq]
      exact hR.compl
  | succ s =>
      have heq : {U : Array N | recTimeA p m U r = s + 1} =
          ReachAll p m ∩ firstRecordAt p m r (s + 1) := by
        ext U
        exact recTimeA_eq_iff_reach_all_firstRecordAt (Nat.succ_pos s) U
      rw [heq]
      exact hR.inter (measurableSet_firstRecordAt p m r (s + 1))

/-- If `ReachAll` is known at time zero, positive-level `recTimeA` is a genuine
stopping time. This conditional statement exposes the future dependence. -/
theorem isStoppingTime_recTimeA_of_reachAll_zero (p : ℝ) (m : ℕ) {r : ℕ}
    (hr : 1 ≤ r)
    (hR : MeasurableSet[Swarming.Enl.enlFilt p m 0] (ReachAll (N := N) p m)) :
    IsStoppingTime (Swarming.Enl.enlFilt p m)
      (fun U : Array N => (recTimeA p m U r : WithTop ℕ)) := by
  intro s
  have heq : {U : Array N | (recTimeA p m U r : WithTop ℕ) ≤ s} =
      ⋃ k : Fin (s + 1), {U : Array N | recTimeA p m U r = k.1} := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro h
      have hnat : recTimeA p m U r ≤ s := by exact_mod_cast h
      exact ⟨⟨recTimeA p m U r, Nat.lt_succ_of_le hnat⟩, rfl⟩
    · rintro ⟨k, hk⟩
      rw [hk]
      exact_mod_cast Nat.le_of_lt_succ k.2
  change MeasurableSet[Swarming.Enl.enlFilt p m s]
    {U : Array N | (recTimeA p m U r : WithTop ℕ) ≤ s}
  rw [heq]
  refine MeasurableSet.iUnion fun k => ?_
  have hRk : MeasurableSet[Swarming.Enl.enlFilt p m k.1] (ReachAll (N := N) p m) :=
    MeasurableSpace.le_def.1
      ((Swarming.Enl.enlFilt p m).mono (Nat.zero_le k.1)) _ hR
  have hk := measurableSet_recTimeA_eq_of_reachAll p m hr hRk (s := k.1)
  exact MeasurableSpace.le_def.1
    ((Swarming.Enl.enlFilt p m).mono (Nat.le_of_lt_succ k.2)) _ hk

end ActualRecordFiltration
