/-
  # Record-time fibres: exact coverage of the defect band

  The compiled good events of `LocOccAllStarts` / `LocOccSingleWindow` are indexed by the *record time*
  `s0 = tau_r`, but the paper's Proposition `local` states one event `G_{r,L,T}` with one
  probability bound and a display that holds on `G ∩ {d_r ≤ L}` for the *random* record time.
  Turning a family of `s0`-indexed statements into one statement needs two things. Only the
  first, deterministic fibre-coverage part is proved here.

  1. **Fidelity of the carrier index, the proved scope of this file.**  `recordPrefixBand p m r s0 L` is
     `{tau_r = s0} ∩ {d_r <= L}` on `ReachAll`.  The fibres are pairwise disjoint and their union
     on `ReachAll` is *exactly* the paper's defect band restricted to `ReachAll`
     (`reachAll_inter_iUnion_recordPrefixBand_eq`), so no reachable time is lost or doubled; in particular the zero fibre is empty for `r >= 1`.

  2. **The constants must not multiply (required later, not proved in this file).**  A naive bound for the union over `s0` sums the constant
     term of the paper-scale estimate once per `s0`, which diverges.  The correct accounting is:
     every `s0`-dependent term of the compiled bounds carries the factor `mu (band s0)`
     (`musum_recordPrefixBand_le_one` makes the total of those at most `1`), while the genuinely
     constant terms (`LsBad`, the harmonic `(locmax)` defect) are *sets independent of `s0`*, so
     they are charged exactly once (`musum_inter_le`).
-/
import Swarm.LocOccSingleWindow

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace LocOccRecordFibres

open Finset
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl Swarming.Enl.ProjLedger Swarming.Enl.VdriftAssembly
open SwarmMarks SwarmLogRatio LocSumAct LocOccCarrier LocOccAllStarts LocOccCarrierAssembly
open RecordDefect RecordoSupply SwarmRecordMeas SwarmRecordMeas.Actual
open SummedSlope.Model

variable {N : ℕ} [Nonempty (Fin N)]

/-! ### 1. The record-time fibres -/

theorem runMax_actX_zero (p : ℝ) (m : ℕ) (U : Array N) :
    runMax (actX p m U) 0 = 0 :=
  runMax_zero (actX p m U) (fun i => actX_zero p m U i)

theorem runMin_actX_zero (p : ℝ) (m : ℕ) (U : Array N) :
    runMin (actX p m U) 0 = 0 := by
  refine le_antisymm ?_ ?_
  · have hle := runMin_le (X := actX p m U) 0 (Classical.arbitrary (Fin N))
    rw [actX_zero p m U (Classical.arbitrary (Fin N))] at hle
    exact hle
  · exact Finset.le_inf' (s := Finset.univ) (f := fun i => actX p m U i 0)
      Finset.univ_nonempty (fun i _ => by rw [actX_zero p m U i])

/-- The zero record fibre is empty: the running maximum starts at `0`. -/
theorem firstRecordAt_zero_eq_empty {p : ℝ} {m r L : ℕ} (hr : r ≠ 0) :
    ActualRecordFiltration.recordPrefixBand (N := N) p m r 0 L = ∅ := by
  refine Set.eq_empty_of_subset_empty ?_
  intro U hU
  rcases hU with ⟨⟨hhit, -⟩, -⟩
  exfalso
  apply hr
  have hz : (r : ℤ) = 0 := hhit.symm.trans (runMax_actX_zero p m U)
  exact_mod_cast hz

/-- Two distinct record times cannot both be first hits of the same level. -/
theorem firstRecordAt_disjoint {p : ℝ} {m r s s' : ℕ} (h : s ≠ s') :
    ActualRecordFiltration.recordPrefixBand (N := N) p m r s 0 ∩
        ActualRecordFiltration.recordPrefixBand (N := N) p m r s' 0 = ∅ := by
  ext U
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro h1 h2
  have h1' := h1.1
  have h2' := h2.1
  simp only [ActualRecordFiltration.firstRecordAt, Set.mem_ofPred_eq] at h1' h2'
  rcases lt_or_gt_of_ne h with hlt | hlt
  · exact h2'.2 s hlt h1'.1
  · exact h1'.2 s' hlt h2'.1

/-- The record fibres are pairwise disjoint, for every band width. -/
theorem recordPrefixBand_pairwiseDisjoint {p : ℝ} {m r L : ℕ} :
    Pairwise (fun s0 s0' : ℕ =>
      Disjoint (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L)
        (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0' L)) := by
  intro s s' hne
  rw [Set.disjoint_iff_inter_eq_empty]
  refine Set.eq_empty_of_subset_empty ?_
  rintro U ⟨hUs, hUs'⟩
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact hUs'.1.2 s hlt hUs.1.1
  · exact hUs.1.2 s' hlt hUs'.1.1

/-- The zero fibre is empty, so every fibre with `s0 = 0` contributes nothing. -/
theorem recordPrefixBand_subset_positive {p : ℝ} {m r L : ℕ} (hr : r ≠ 0) {s0 : ℕ} :
    ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ⊆
      {U : Array N | s0 ≠ 0} := by
  rintro U hU rfl
  have h := firstRecordAt_zero_eq_empty (N := N) (p := p) (m := m) (r := r) (L := L) hr
  rw [h] at hU
  exact hU

/-- **The union of the record fibres, restricted to `ReachAll**, is the defect band.**

The clock defaults to zero off `ReachAll`; a single finite first-record event does not identify
that future-dependent event. Hence the equality must retain `ReachAll` explicitly. On `ReachAll`,
`recTimeA` is precisely the first-hit clock and no time is lost or doubled. -/
theorem reachAll_inter_iUnion_recordPrefixBand_eq {p : ℝ} {m r L : ℕ} (hr : r ≠ 0) :
    ReachAll (N := N) p m ∩ (⋃ s0, ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L) =
      ReachAll (N := N) p m ∩
        {U : Array N | (defect (actX p m U) (recTimeA p m U) r).toNat ≤ L} := by
  ext U
  constructor
  · rintro ⟨hreach, hs0⟩
    obtain ⟨s0, hs0⟩ := Set.mem_iUnion.1 hs0
    obtain ⟨hfirst, hband⟩ := hs0
    refine ⟨hreach, ?_⟩
    have hs0pos : s0 ≠ 0 := by
      rintro rfl
      have hz : (r : ℤ) = 0 := hfirst.1.symm.trans (runMax_actX_zero p m U)
      exact hr (by exact_mod_cast hz)
    have hτ : recTimeA p m U r = s0 :=
      (ActualRecordFiltration.recTimeA_eq_iff_reach_all_firstRecordAt
        (N := N) (p := p) (m := m) (r := r) (s := s0) (Nat.pos_of_ne_zero hs0pos) U).2
        ⟨hreach, hfirst⟩
    change (defect (actX p m U) (recTimeA p m U) r).toNat ≤ L
    rw [defectA_eq_of_recTimeA_eq (p := p) (m := m) U r s0 hτ]
    exact hband
  · rintro ⟨hreach, hd⟩
    refine ⟨hreach, ?_⟩
    change (defect (actX p m U) (recTimeA p m U) r).toNat ≤ L at hd
    have hτ := (ActualRecordFiltration.recTimeA_eq_iff_reach_all_firstRecordAt
      (N := N) (p := p) (m := m) (r := r)
      (s := recTimeA p m U r) (by
        apply Nat.pos_of_ne_zero
        intro hzero
        exact ((ActualRecordFiltration.recTimeA_eq_zero_iff_not_reach
          (N := N) (p := p) (m := m) (Nat.pos_of_ne_zero hr) U).1 hzero) hreach) U).1 rfl
    refine Set.mem_iUnion.2 ⟨recTimeA p m U r, hτ.2, ?_⟩
    rw [defectA_eq_of_recTimeA_eq (p := p) (m := m) U r (recTimeA p m U r) rfl] at hd
    exact hd
