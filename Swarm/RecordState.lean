/-
The record-state space of `main_1d_revised.tex`, §3.1 (eq. (state)-(states)).

State of the record chain at a record time: the distances `d_i` of the walkers below the
record (multiples of two, represented here as half-distances `d_i ∈ ℕ`) and the local times
`η_i(x)` capped at `m` at relative positions `x ≤ 0`.

Contains no proof holes; imports Mathlib and `KrylovBogoliubov`.
-/
import Swarm.Imports
import Swarm.KrylovBogoliubov

open MeasureTheory Set Topology
open scoped ENNReal

namespace SwarmRec

/-- Ambient space: half-distances below the record and capped local times. -/
abbrev Amb (N m : ℕ) := (Fin N → ℕ) × (Fin N → ℤ → Fin (m + 1))

/-- The local-time constraints of eq. (states) at a fixed distance vector `v`. -/
def secSet (N m : ℕ) (v : Fin N → ℕ) : Set (Fin N → ℤ → Fin (m + 1)) :=
  {η | (∀ (i : Fin N) (x : ℤ), 0 < x → η i x = 0) ∧
       (∀ i, (1 : Fin (m + 1)) ≤ η i (-(2 * (v i : ℤ)))) ∧
       (∀ i, η i 0 = if v i = 0 then 1 else 0)}

/-- The admissible record states of eq. (states). -/
def recSet (N m : ℕ) : Set (Amb N m) :=
  {p | (∃ i, p.1 i = 0) ∧ p.2 ∈ secSet N m p.1}

/-- The record-state space of §3.1. -/
abbrev RecState (N m : ℕ) := {p : Amb N m // p ∈ recSet N m}

/-- The half-distance of walker `i` below the current record. -/
def dist2 {N m : ℕ} (y : RecState N m) (i : Fin N) : ℕ := y.val.1 i

/-- The compact exhaustion `{max_i d_i ≤ K}` of the record-state space. -/
def exh (N m : ℕ) (K : ℕ) : Set (RecState N m) := {y | ∀ i, dist2 y i ≤ K}

/-! ## Closedness of the local-time constraints -/

lemma isClosed_zero_above (N m : ℕ) :
    IsClosed {η : Fin N → ℤ → Fin (m + 1) | ∀ (i : Fin N) (x : ℤ), 0 < x → η i x = 0} := by
  have hEq : {η : Fin N → ℤ → Fin (m + 1) | ∀ (i : Fin N) (x : ℤ), 0 < x → η i x = 0}
      = ⋂ (i : Fin N), ⋂ (x : ℤ), {η : Fin N → ℤ → Fin (m + 1) | (0 < x → η i x = 0)} := by
    ext η
    simp
  rw [hEq]
  refine isClosed_iInter fun i => isClosed_iInter fun x => ?_
  by_cases hx : 0 < x
  · have hEq2 : {η : Fin N → ℤ → Fin (m + 1) | (0 < x → η i x = 0)} = {η | η i x = 0} := by
      ext η
      simp [hx]
    rw [hEq2]
    have hcont : Continuous fun η : Fin N → ℤ → Fin (m + 1) => η i x :=
      (continuous_apply x).comp (continuous_apply i)
    exact isClosed_singleton.preimage hcont
  · have hEq2 : {η : Fin N → ℤ → Fin (m + 1) | (0 < x → η i x = 0)} = univ := by
      ext η
      simp [hx]
    rw [hEq2]
    exact isClosed_univ

lemma isClosed_lower_sec (N m : ℕ) (v : Fin N → ℕ) :
    IsClosed {η : Fin N → ℤ → Fin (m + 1) | ∀ i, (1 : Fin (m + 1)) ≤ η i (-(2 * (v i : ℤ)))} := by
  have hEq : {η : Fin N → ℤ → Fin (m + 1) | ∀ i, (1 : Fin (m + 1)) ≤ η i (-(2 * (v i : ℤ)))}
      = ⋂ (i : Fin N), {η : Fin N → ℤ → Fin (m + 1) |
          η i (-(2 * (v i : ℤ))) ∈ {c : Fin (m + 1) | (1 : Fin (m + 1)) ≤ c}} := by
    ext η
    simp
  rw [hEq]
  refine isClosed_iInter fun i => ?_
  have hc : IsClosed {c : Fin (m + 1) | (1 : Fin (m + 1)) ≤ c} := (Set.toFinite _).isClosed
  have hcont : Continuous fun η : Fin N → ℤ → Fin (m + 1) => η i (-(2 * (v i : ℤ))) :=
    (continuous_apply _).comp (continuous_apply i)
  exact hc.preimage hcont

lemma isClosed_zero_sec (N m : ℕ) (v : Fin N → ℕ) :
    IsClosed {η : Fin N → ℤ → Fin (m + 1) | ∀ i, η i 0 = if v i = 0 then 1 else 0} := by
  have hEq : {η : Fin N → ℤ → Fin (m + 1) | ∀ i, η i 0 = if v i = 0 then 1 else 0}
      = ⋂ (i : Fin N), {η : Fin N → ℤ → Fin (m + 1) |
          η i 0 ∈ ({if v i = 0 then (1 : Fin (m + 1)) else 0} : Set (Fin (m + 1)))} := by
    ext η
    simp
  rw [hEq]
  refine isClosed_iInter fun i => ?_
  have hcont : Continuous fun η : Fin N → ℤ → Fin (m + 1) => η i 0 :=
    (continuous_apply _).comp (continuous_apply i)
  exact isClosed_singleton.preimage hcont

/-- The set of admissible local-time profiles at fixed distances is closed. -/
lemma isClosed_secSet (N m : ℕ) (v : Fin N → ℕ) : IsClosed (secSet N m v) := by
  have h := (isClosed_zero_above N m).inter
    ((isClosed_lower_sec N m v).inter (isClosed_zero_sec N m v))
  have hEq : secSet N m v
      = {η : Fin N → ℤ → Fin (m + 1) | ∀ (i : Fin N) (x : ℤ), 0 < x → η i x = 0}
        ∩ ({η : Fin N → ℤ → Fin (m + 1) |
              ∀ i, (1 : Fin (m + 1)) ≤ η i (-(2 * (v i : ℤ)))}
           ∩ {η : Fin N → ℤ → Fin (m + 1) | ∀ i, η i 0 = if v i = 0 then 1 else 0}) := by
    ext η
    simp only [secSet, mem_inter_iff, mem_ofPred_eq]
  rw [hEq]
  exact h

/-- The set of admissible local-time profiles at fixed distances is compact. -/
lemma isCompact_secSet (N m : ℕ) (v : Fin N → ℕ) : IsCompact (secSet N m v) :=
  (isClosed_secSet N m v).isCompact

end SwarmRec

namespace SwarmRec

/-! ## Closedness of the record-state set -/

lemma isOpen_dist_ne (N m : ℕ) (i : Fin N) (v : ℕ) :
    IsOpen {p : Amb N m | p.1 i ≠ v} :=
  (isOpen_discrete (({v} : Set ℕ)ᶜ)).preimage
    (by fun_prop : Continuous fun p : Amb N m => p.1 i)

lemma isOpen_eta_ne (N m : ℕ) (i : Fin N) (x : ℤ) (c : Fin (m + 1)) :
    IsOpen {p : Amb N m | p.2 i x ≠ c} :=
  (isOpen_discrete (({c} : Set (Fin (m + 1)))ᶜ)).preimage
    (by fun_prop : Continuous fun p : Amb N m => p.2 i x)

/-- The complement of the record-state set is open: it is the union of the four ways in which
one of the constraints of eq. (states) can fail. -/
theorem isOpen_compl_recSet (N m : ℕ) : IsOpen (recSet N m)ᶜ := by
  have A1 : IsOpen {p : Amb N m | ∀ i, p.1 i ≠ 0} := by
    have hEq : {p : Amb N m | ∀ i, p.1 i ≠ 0} = ⋂ i : Fin N, {p : Amb N m | p.1 i ≠ 0} := by
      ext p
      simp
    rw [hEq]
    exact isOpen_iInter_of_finite fun i => isOpen_dist_ne N m i 0
  have A2 : IsOpen {p : Amb N m | ∃ (i : Fin N) (x : ℤ), 0 < x ∧ p.2 i x ≠ 0} := by
    have hEq : {p : Amb N m | ∃ (i : Fin N) (x : ℤ), 0 < x ∧ p.2 i x ≠ 0}
        = ⋃ (i : Fin N), ⋃ (x : ℤ), ({p : Amb N m | 0 < x} ∩ {p : Amb N m | p.2 i x ≠ 0}) := by
      ext p
      simp
    rw [hEq]
    refine isOpen_iUnion fun i => isOpen_iUnion fun x => ?_
    refine (isOpen_discrete {x : ℤ | 0 < x}).preimage ?_ |>.inter (isOpen_eta_ne N m i x 0)
    exact continuous_const
  have A3 : IsOpen {p : Amb N m | ∃ i, ¬ ((1 : Fin (m + 1)) ≤ p.2 i (-(2 * (p.1 i : ℤ))))} := by
    have hEq : {p : Amb N m | ∃ i, ¬ ((1 : Fin (m + 1)) ≤ p.2 i (-(2 * (p.1 i : ℤ))))}
        = ⋃ (i : Fin N), ⋃ (d : Fin N → ℕ),
            ({p : Amb N m | p.1 = d}
              ∩ {p : Amb N m | ¬ ((1 : Fin (m + 1)) ≤ p.2 i (-(2 * (d i : ℤ))))}) := by
      ext p
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, p.1, rfl, hi⟩
      · rintro ⟨i, d, hp1, hi⟩
        subst hp1
        exact ⟨i, hi⟩
    rw [hEq]
    refine isOpen_iUnion fun i => isOpen_iUnion fun d => ?_
    have hd : IsOpen {p : Amb N m | p.1 = d} := (isOpen_discrete {d}).preimage continuous_fst
    have hc : IsOpen {p : Amb N m | ¬ ((1 : Fin (m + 1)) ≤ p.2 i (-(2 * (d i : ℤ))))} :=
      (isOpen_discrete {c : Fin (m + 1) | ¬ ((1 : Fin (m + 1)) ≤ c)}).preimage
        (by fun_prop : Continuous fun p : Amb N m => p.2 i (-(2 * (d i : ℤ))))
    exact hd.inter hc
  have A4 : IsOpen {p : Amb N m | ∃ i, p.2 i 0 ≠ (if p.1 i = 0 then (1 : Fin (m + 1)) else 0)} := by
    have hEq : {p : Amb N m | ∃ i, p.2 i 0 ≠ (if p.1 i = 0 then (1 : Fin (m + 1)) else 0)}
        = ⋃ (i : Fin N), ⋃ (d : Fin N → ℕ),
            ({p : Amb N m | p.1 = d}
              ∩ {p : Amb N m | p.2 i 0 ≠ (if d i = 0 then (1 : Fin (m + 1)) else 0)}) := by
      ext p
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, p.1, rfl, hi⟩
      · rintro ⟨i, d, hp1, hi⟩
        subst hp1
        exact ⟨i, hi⟩
    rw [hEq]
    refine isOpen_iUnion fun i => isOpen_iUnion fun d => ?_
    have hd : IsOpen {p : Amb N m | p.1 = d} := (isOpen_discrete {d}).preimage continuous_fst
    have hc : IsOpen {p : Amb N m | p.2 i 0 ≠ (if d i = 0 then (1 : Fin (m + 1)) else 0)} :=
      (isOpen_discrete {c : Fin (m + 1) | c ≠ (if d i = 0 then (1 : Fin (m + 1)) else 0)}).preimage
        (by fun_prop : Continuous fun p : Amb N m => p.2 i 0)
    exact hd.inter hc
  have hA1 : ({p : Amb N m | ∃ i, p.1 i = 0})ᶜ = {p : Amb N m | ∀ i, p.1 i ≠ 0} := by
    ext p
    simp
  have hA2 : ({p : Amb N m | ∀ (i : Fin N) (x : ℤ), 0 < x → p.2 i x = 0})ᶜ
      = {p : Amb N m | ∃ (i : Fin N) (x : ℤ), 0 < x ∧ p.2 i x ≠ 0} := by
    ext p
    simp
  have hA3 : ({p : Amb N m | ∀ i, (1 : Fin (m + 1)) ≤ p.2 i (-(2 * (p.1 i : ℤ)))})ᶜ
      = {p : Amb N m | ∃ i, ¬ ((1 : Fin (m + 1)) ≤ p.2 i (-(2 * (p.1 i : ℤ))))} := by
    ext p
    simp
  have hA4 : ({p : Amb N m | ∀ i, p.2 i 0 = (if p.1 i = 0 then (1 : Fin (m + 1)) else 0)})ᶜ
      = {p : Amb N m | ∃ i, p.2 i 0 ≠ (if p.1 i = 0 then (1 : Fin (m + 1)) else 0)} := by
    ext p
    simp
  have hEq : (recSet N m)ᶜ
      = ({p : Amb N m | ∃ i, p.1 i = 0})ᶜ
        ∪ ({p : Amb N m | ∀ (i : Fin N) (x : ℤ), 0 < x → p.2 i x = 0})ᶜ
        ∪ ({p : Amb N m | ∀ i, (1 : Fin (m + 1)) ≤ p.2 i (-(2 * (p.1 i : ℤ)))})ᶜ
        ∪ ({p : Amb N m | ∀ i, p.2 i 0 = (if p.1 i = 0 then (1 : Fin (m + 1)) else 0)})ᶜ := by
    ext p
    simp only [recSet, secSet, mem_compl_iff, mem_ofPred_eq, mem_union]
    tauto
  rw [hEq, hA1, hA2, hA3, hA4]
  exact ((A1.union A2).union A3).union A4

/-- The record-state set is closed. -/
theorem isClosed_recSet (N m : ℕ) : IsClosed (recSet N m) :=
  isOpen_compl_iff.mp (isOpen_compl_recSet N m)

lemma measurableSet_recSet (N m : ℕ) : MeasurableSet (recSet N m) :=
  (isClosed_recSet N m).measurableSet

/-! ## The compact exhaustion `{max_i d_i ≤ K}` -/

lemma finite_bounded_dist (N K : ℕ) : {d : Fin N → ℕ | ∀ i, d i ≤ K}.Finite := by
  have hrange : (Set.range (fun v : Fin N → Fin (K + 1) => fun i => (v i : ℕ))).Finite :=
    Set.finite_range _
  refine hrange.subset ?_
  intro d hd
  exact ⟨fun i => ⟨d i, by have := hd i; omega⟩, by funext i; rfl⟩

theorem isCompact_bounded_amb (N m K : ℕ) :
    IsCompact {p : Amb N m | ∀ i, p.1 i ≤ K} := by
  have hEq : {p : Amb N m | ∀ i, p.1 i ≤ K}
      = {d : Fin N → ℕ | ∀ i, d i ≤ K} ×ˢ (univ : Set (Fin N → ℤ → Fin (m + 1))) := by
    ext p
    simp
  rw [hEq]
  exact (finite_bounded_dist N K).isCompact.prod isCompact_univ

/-- **The compact exhaustion.**  For every `K`, the record states whose distances are all at
most `K` form a compact subset of the ambient space. -/
theorem isCompact_recSet_bounded (N m K : ℕ) :
    IsCompact (recSet N m ∩ {p : Amb N m | ∀ i, p.1 i ≤ K}) := by
  rw [Set.inter_comm]
  exact (isCompact_bounded_amb N m K).inter_right (isClosed_recSet N m)

/-- **The compact exhaustion on the record-state space itself.**  This is the compactness used
to turn tightness of `d_r` into tightness of the laws of the record states `Y_r`. -/
theorem isCompact_dist2_le (N m K : ℕ) : IsCompact (exh N m K) := by
  have hS : exh N m K
      = Subtype.val ⁻¹' (recSet N m ∩ {p : Amb N m | ∀ i, p.1 i ≤ K}) := by
    ext y
    exact ⟨fun h => ⟨y.2, h⟩, fun h => h.2⟩
  rw [hS, IsEmbedding.subtypeVal.isCompact_iff]
  have himg : Subtype.val '' (Subtype.val ⁻¹'
        (recSet N m ∩ {p : Amb N m | ∀ i, p.1 i ≤ K}))
      = recSet N m ∩ {p : Amb N m | ∀ i, p.1 i ≤ K} :=
    Set.image_preimage_eq_of_subset (fun p hp => ⟨⟨p, hp.1⟩, rfl⟩)
  rw [himg]
  exact isCompact_recSet_bounded N m K

/-! ## Metric and Borel structure -/

lemma t2Space_recState (N m : ℕ) : T2Space (RecState N m) := inferInstance

lemma pseudoMetrizable_recState (N m : ℕ) :
    TopologicalSpace.PseudoMetrizableSpace (RecState N m) := inferInstance

lemma separable_recState (N m : ℕ) : TopologicalSpace.SeparableSpace (RecState N m) :=
  inferInstance

lemma borelSpace_recState (N m : ℕ) : BorelSpace (RecState N m) := inferInstance

lemma isClosed_exh (N m K : ℕ) : IsClosed (exh N m K) := (isCompact_dist2_le N m K).isClosed

lemma measurableSet_exh (N m K : ℕ) : MeasurableSet (exh N m K) :=
  (isClosed_exh N m K).measurableSet

/-- The simultaneous-record set `F = {d_i = 0 for all i}` of Prop. "front". -/
def srSet (N m : ℕ) : Set (RecState N m) := exh N m 0

lemma isCompact_srSet (N m : ℕ) : IsCompact (srSet N m) := isCompact_dist2_le N m 0

lemma measurableSet_srSet (N m : ℕ) : MeasurableSet (srSet N m) := measurableSet_exh N m 0

/-! ## The invariant law on the record-state space -/

/-- **Area (e), concrete form.**  Let `κ` be a Feller Markov kernel on the record-state space
(the record chain), suppose its laws are tight -- the conclusion of Prop. "tight", obtained
from tightness of `d_r` -- and suppose the prescribed-path force estimate holds on the compact
exhaustion `{max_i d_i ≤ K}`.  Then some invariant probability measure `π` satisfies `π F > 0`,
where `F` is the set of simultaneous-record states.

The only remaining inputs of the paper's Prop. "front" are therefore (i) the Feller property
of the concrete record kernel and (ii) the force estimate; both are statements about the
i.i.d.-uniform construction of the interacting walks. -/
theorem exists_invariant_measure_pos_recState {N m : ℕ}
    (κ : ProbabilityTheory.Kernel (RecState N m) (RecState N m))
    [ProbabilityTheory.IsMarkovKernel κ]
    (hF : SwarmKB.Feller κ) (μ : Measure (RecState N m)) [IsProbabilityMeasure μ]
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ r : ℕ,
      (SwarmKB.step κ)^[r] μ (exh N m K)ᶜ ≤ ε)
    {F : Set (RecState N m)} (hFm : MeasurableSet F)
    (hforce : ∀ K : ℕ, ∃ c : ℝ≥0∞, c ≠ 0 ∧ ∀ y : RecState N m, y ∈ exh N m K → c ≤ κ y F) :
    ∃ π : Measure (RecState N m), IsProbabilityMeasure π ∧
      ProbabilityTheory.Kernel.Invariant κ π ∧ 0 < π F := by
  refine SwarmKB.exists_invariant_measure_pos_of_exhaustion (κ := κ) (μ := μ) hF
    (exh N m) (fun K => isCompact_dist2_le N m K) htight hFm ?_
  intro K
  obtain ⟨c, hc, hcf⟩ := hforce K
  exact ⟨c, hc, fun y hy => hcf y hy⟩

/-- **Prop. "front", concrete form, with `F` the simultaneous-record set.**  Same as
`exists_invariant_measure_pos_recState` but with the simultaneity set `srSet N m` in place of a
general measurable `F`, so that its measurability needs no further hypothesis. -/
theorem exists_invariant_measure_pos_srSet {N m : ℕ}
    (κ : ProbabilityTheory.Kernel (RecState N m) (RecState N m))
    [ProbabilityTheory.IsMarkovKernel κ]
    (hF : SwarmKB.Feller κ) (μ : Measure (RecState N m)) [IsProbabilityMeasure μ]
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ r : ℕ,
      (SwarmKB.step κ)^[r] μ (exh N m K)ᶜ ≤ ε)
    (hforce : ∀ K : ℕ, ∃ c : ℝ≥0∞, c ≠ 0 ∧ ∀ y : RecState N m, y ∈ exh N m K → c ≤ κ y (srSet N m)) :
    ∃ π : Measure (RecState N m), IsProbabilityMeasure π ∧
      ProbabilityTheory.Kernel.Invariant κ π ∧ 0 < π (srSet N m) :=
  exists_invariant_measure_pos_recState κ hF μ htight (measurableSet_srSet N m) hforce

end SwarmRec
