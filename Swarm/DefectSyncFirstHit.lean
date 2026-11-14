/-
# First-passage refinement of the defect synchronisation force

`DefectSync.defect_sync_force` proves that from a defect-bounded past event the swarm
follows the position-dependent synchronising word with conditional probability at least
`(1-p)^((2K+1)*N)`, and that on that event every walker is at the *same* level `ℓ + 1` at
the *same* time `n + (2K+1)`.

That statement alone does not say that `ℓ + 1` is reached for the *first* time at
`n + (2K+1)`.  The paper's `(force)` (`main_1d_revised.tex`, proof of Proposition
`front`) is used inside the record kernel, whose block stops at the first time the swarm
maximum reaches the next level, so the first-passage information is needed to identify the
block's stopping time.  This file supplies it by the same sector argument with a stronger
target:

    (1-p)^((2K+1)*N) * mu G
      <= mu (G ∩ {no walker exceeds ℓ before time n+(2K+1)}
                 ∩ {every walker is at ℓ+1 at time n+(2K+1)}).

Consequently the swarm maximum is `<= ℓ` up to time `n+2K` and `= ℓ+1` at `n+2K+1`: the
level advances by exactly one, with all walkers present and no overshoot.  The defect at
the end is zero in the strongest sense.

Scope: deterministic combinatorics plus the already-proved one-block force.  No
`RegenPath.D`, no nullity, no invariant law, no recurrence claim.
-/
import Swarm.DefectSync

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

namespace DefectSync

open Swarming.Uniform Swarming.Trajectory Swarming.Enl

variable {N : ℕ}

/-! ### Partial sums of the alternating word -/

/-- The alternating sum after `2t` letters is `0`; after `2t+1` letters it is `-1`. -/
theorem sum_range_alt_pair (t : ℕ) :
    (∑ v ∈ Finset.range (2 * t), (if v % 2 = 0 then (-1 : ℤ) else 1) = 0) ∧
      (∑ v ∈ Finset.range (2 * t + 1), (if v % 2 = 0 then (-1 : ℤ) else 1) = -1) := by
  induction t with
  | zero => constructor <;> norm_num
  | succ t ih =>
      obtain ⟨h1, h2⟩ := ih
      have heven : (2 * t + 1 + 1) % 2 = 0 := by omega
      constructor
      · have hsp : 2 * (t + 1) = 2 * t + 1 + 1 := by ring
        rw [hsp, Finset.sum_range_succ, h2]
        simp
      · have hsp : 2 * (t + 1) + 1 = 2 * t + 1 + 1 + 1 := by ring
        rw [hsp, Finset.sum_range_succ, Finset.sum_range_succ, h2]
        simp [heven]

/-- All partial sums of the alternating word are nonpositive. -/
theorem sum_range_alt_le_zero (u : ℕ) :
    ∑ v ∈ Finset.range u, (if v % 2 = 0 then (-1 : ℤ) else 1) ≤ 0 := by
  rcases Nat.mod_two_eq_zero_or_one u with h | h
  · have hu : u = 2 * (u / 2) := by
      have := Nat.div_add_mod u 2
      omega
    rw [hu, (sum_range_alt_pair (u / 2)).1]
  · have hu : u = 2 * (u / 2) + 1 := by
      have := Nat.div_add_mod u 2
      omega
    rw [hu, (sum_range_alt_pair (u / 2)).2]
    norm_num

/-- On the alternating part the partial sums never exceed `0`: no walker rises. -/
theorem sum_syncWord_prefix_le (K : ℕ) (e : Fin N → ℕ) (i : Fin N) {u : ℕ}
    (hu : u ≤ 2 * K - 2 * e i) :
    ∑ v ∈ Finset.range u, syncWord (N := N) K e v i ≤ 0 := by
  rw [show ∑ v ∈ Finset.range u, syncWord (N := N) K e v i
      = ∑ v ∈ Finset.range u, (if v % 2 = 0 then (-1 : ℤ) else 1) from ?_]
  · exact sum_range_alt_le_zero u
  · refine Finset.sum_congr rfl fun v hv => ?_
    have hv' : v < 2 * K - 2 * e i := by have := Finset.mem_range.mp hv; omega
    show (if v < 2 * K - 2 * e i then (if v % 2 = 0 then (-1 : ℤ) else 1) else 1) = _
    rw [if_pos hv']

/-- Past the alternating part every remaining letter is a right step, so the partial sum is
the number of steps taken since the end of the alternating part. -/
theorem sum_syncWord_of_le (K : ℕ) (e : Fin N → ℕ) (i : Fin N) {u : ℕ}
    (hu : 2 * K - 2 * e i ≤ u) :
    ∑ v ∈ Finset.range u, syncWord (N := N) K e v i =
      (u : ℤ) - ((2 * K - 2 * e i : ℕ) : ℤ) := by
  classical
  have hje : Even (2 * K - 2 * e i) := ⟨K - e i, by omega⟩
  have hsplit : (2 * K - 2 * e i) + (u - (2 * K - 2 * e i)) = u := by omega
  have hfirst : ∑ v ∈ Finset.range (2 * K - 2 * e i), syncWord (N := N) K e v i = 0 := by
    rw [show ∑ v ∈ Finset.range (2 * K - 2 * e i), syncWord (N := N) K e v i
        = ∑ v ∈ Finset.range (2 * K - 2 * e i),
            (if v % 2 = 0 then (-1 : ℤ) else 1) from ?_]
    · exact sum_range_alt_of_even _ hje
    · refine Finset.sum_congr rfl fun v hv => ?_
      have hv' : v < 2 * K - 2 * e i := Finset.mem_range.mp hv
      show (if v < 2 * K - 2 * e i then (if v % 2 = 0 then (-1 : ℤ) else 1) else 1) = _
      rw [if_pos hv']
  have hsecond : ∑ x ∈ Finset.range (u - (2 * K - 2 * e i)),
      syncWord (N := N) K e ((2 * K - 2 * e i) + x) i =
      ((u - (2 * K - 2 * e i) : ℕ) : ℤ) := by
    have hnone : ∀ x ∈ Finset.range (u - (2 * K - 2 * e i)),
        ¬ ((2 * K - 2 * e i) + x < 2 * K - 2 * e i) := by
      intro x hx
      have := Finset.mem_range.mp hx
      omega
    rw [show ∑ x ∈ Finset.range (u - (2 * K - 2 * e i)),
        syncWord (N := N) K e ((2 * K - 2 * e i) + x) i
        = ∑ x ∈ Finset.range (u - (2 * K - 2 * e i)), (1 : ℤ) from ?_]
    · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    · refine Finset.sum_congr rfl fun x hx => ?_
      show (if (2 * K - 2 * e i) + x < 2 * K - 2 * e i
          then (if ((2 * K - 2 * e i) + x) % 2 = 0 then (-1 : ℤ) else 1) else 1) = 1
      rw [if_neg (hnone x hx)]
  rw [← hsplit, Finset.sum_range_add, hfirst, hsecond]
  push_cast [Nat.cast_sub hu]
  ring

/-! ### The first-passage landing lemma -/

/-- **The synchronising word lands at the record level for the first time.**  If every
walker starts at `ℓ - 2 * (e i)` with `e i ≤ K` and the swarm follows `syncWord K e` for
`2K+1` steps, then no walker is above `ℓ` at any earlier time and every walker is at
`ℓ + 1` at time `n + (2K+1)`. -/
theorem evWord_sync_first_hit {p : ℝ} {m n K : ℕ} {ℓ : ℤ} {e : Fin N → ℕ} {U : Array N}
    (he : ∀ i, e i ≤ K)
    (hstart : ∀ i, (trajectory p m U n).pos i = ℓ - 2 * (e i : ℤ))
    (hword : U ∈ evWord p m n (Finset.univ : Finset (Fin N))
      (syncWord (N := N) K e) (2 * K + 1)) :
    (∀ u, u < 2 * K + 1 → ∀ i, (trajectory p m U (n + u)).pos i ≤ ℓ) ∧
      (∀ i, (trajectory p m U (n + (2 * K + 1))).pos i = ℓ + 1) := by
  classical
  have hstep : ∀ u, u < 2 * K + 1 → ∀ i,
      (trajectory p m U (n + u + 1)).pos i =
        (trajectory p m U (n + u)).pos i + syncWord (N := N) K e u i :=
    fun u hu i => evWord_step (p := p) (m := m) (n := n) (k := 2 * K + 1)
      (ε := syncWord (N := N) K e) (u := u) hword hu i
  constructor
  · intro u hu i
    have htel : (trajectory p m U (n + u)).pos i =
        (trajectory p m U n).pos i + ∑ v ∈ Finset.range u, syncWord (N := N) K e v i :=
      pos_add_sum (p := p) (m := m) (n := n) (ε := syncWord (N := N) K e) (L := u) (U := U)
        (fun v hv => hstep v (Nat.lt_trans hv hu)) i
    rw [htel, hstart i]
    by_cases hcase : u ≤ 2 * K - 2 * e i
    · have hle := sum_syncWord_prefix_le (N := N) K e i hcase
      have hnn : (0 : ℤ) ≤ 2 * (e i : ℤ) := by positivity
      linarith
    · push Not at hcase
      have hj : 2 * K - 2 * e i ≤ u := le_of_lt hcase
      rw [sum_syncWord_of_le (N := N) K e i hj]
      have hek : 2 * e i ≤ 2 * K := by
        have := he i
        omega
      have hnat : u - (2 * K - 2 * e i) ≤ 2 * e i := by omega
      have hcast : ((u - (2 * K - 2 * e i) : ℕ) : ℤ) ≤ 2 * (e i : ℤ) := by
        exact_mod_cast hnat
      have hrew : (u : ℤ) - ((2 * K - 2 * e i : ℕ) : ℤ) =
          ((u - (2 * K - 2 * e i) : ℕ) : ℤ) := by
        rw [Nat.cast_sub hj]
      rw [hrew]
      linarith
  · intro i
    have htel : (trajectory p m U (n + (2 * K + 1))).pos i =
        (trajectory p m U n).pos i +
          ∑ v ∈ Finset.range (2 * K + 1), syncWord (N := N) K e v i :=
      pos_add_sum (p := p) (m := m) (n := n) (ε := syncWord (N := N) K e)
        (L := 2 * K + 1) (U := U) hstep i
    rw [htel, hstart i, sum_syncWord K e i (he i)]
    ring

/-! ### The first-passage force -/

/-- **Defect-dependent synchronisation force, first-passage form.**  Same hypotheses as
`DefectSync.defect_sync_force`, with the stronger conclusion that the whole swarm is at the
new level `ℓ + 1` at time `n + (2K+1)` and that no walker exceeded `ℓ` at any earlier
time.  So `ℓ + 1` is the swarm maximum at that time, it was reached for the first time
there, and the defect vector of the resulting record state is identically zero. -/
theorem defect_sync_force_first_hit (p : ℝ) (hp0 : (1 : ℝ) / 2 ≤ p) (hp1 : p < 1)
    (m n K : ℕ) (ℓ : ℤ) {G : Set (Array N)} (hG : MeasurableSet[enlMeas p m n] G)
    (hsec : ∀ U ∈ G, ∃ e : Fin N → Fin (K + 1),
      ∀ i, (trajectory p m U n).pos i = ℓ - 2 * ((e i : ℕ) : ℤ)) :
    ENNReal.ofReal (1 - p) ^ ((2 * K + 1) * N) * arrayMeasure N G ≤
      arrayMeasure N (G ∩ {U : Array N |
        (∀ u, u < 2 * K + 1 → ∀ i, (trajectory p m U (n + u)).pos i ≤ ℓ) ∧
          ∀ i, (trajectory p m U (n + (2 * K + 1))).pos i = ℓ + 1}) := by
  classical
  set sec : (Fin N → Fin (K + 1)) → Set (Array N) := fun e =>
    G ∩ syncSector p m n ℓ (fun i => (e i : ℕ)) with hsecdef
  have hsec_meas : ∀ e, MeasurableSet[enlMeas p m n] (sec e) := fun e =>
    hG.inter (measurableSet_syncSector_enl p m n ℓ (fun i => (e i : ℕ)))
  have hsec_amb : ∀ e, MeasurableSet (sec e) := fun e =>
    enlMeas_le p m n (sec e) (hsec_meas e)
  have hdisj : ∀ e e' : Fin N → Fin (K + 1), e ≠ e' → Disjoint (sec e) (sec e') := by
    intro e e' hne
    rw [Set.disjoint_left]
    intro U hU hU'
    apply hne
    funext i
    have h2 : (trajectory p m U n).pos i = ℓ - 2 * ((e i : ℕ) : ℤ) := hU.2 i
    have h3 : (trajectory p m U n).pos i = ℓ - 2 * ((e' i : ℕ) : ℤ) := hU'.2 i
    have hv : ((e i : ℕ) : ℤ) = ((e' i : ℕ) : ℤ) := by rw [h2] at h3; linarith
    exact Fin.ext (Nat.cast_injective hv)
  have hcover : G = ⋃ e, sec e := by
    refine Set.Subset.antisymm ?_ (Set.iUnion_subset fun e => Set.inter_subset_left)
    intro U hU
    obtain ⟨e, he⟩ := hsec U hU
    exact Set.mem_iUnion.mpr ⟨e, hU, he⟩
  set W : (Fin N → Fin (K + 1)) → Set (Array N) := fun e =>
    sec e ∩ evWord p m n (Finset.univ : Finset (Fin N)) (syncWord K (fun i => (e i : ℕ)))
      (2 * K + 1) with hWdef
  have hW_meas : ∀ e, MeasurableSet (W e) := by
    intro e
    have h1 : MeasurableSet (sec e) := hsec_amb e
    have h2 : MeasurableSet (evWord p m n (Finset.univ : Finset (Fin N))
        (syncWord K (fun i => (e i : ℕ))) (2 * K + 1)) :=
      enlMeas_le p m (n + (2 * K + 1)) _ (measurableSet_evWord_enl p m n _ _ (2 * K + 1))
    exact h1.inter h2
  have hW_disj : ∀ e e' : Fin N → Fin (K + 1), e ≠ e' → Disjoint (W e) (W e') := by
    intro e e' hne
    rw [Set.disjoint_left]
    intro U hU hU'
    exact Set.disjoint_left.mp (hdisj e e' hne) hU.1 hU'.1
  have hforce : ∀ e, ENNReal.ofReal (1 - p) ^ ((2 * K + 1) * N) * arrayMeasure N (sec e) ≤
      arrayMeasure N (W e) := by
    intro e
    have := evWord_mass_ge_univ (N := N) p hp0 hp1 m n (syncWord K (fun i => (e i : ℕ)))
      (syncWord_unit K (fun i => (e i : ℕ))) (hsec_meas e) (2 * K + 1)
    simpa [W] using this
  have hsub : ∀ e, W e ⊆ G ∩ {U : Array N |
      (∀ u, u < 2 * K + 1 → ∀ i, (trajectory p m U (n + u)).pos i ≤ ℓ) ∧
        ∀ i, (trajectory p m U (n + (2 * K + 1))).pos i = ℓ + 1} := by
    intro e U hU
    obtain ⟨hUsec, hUword⟩ := hU
    exact ⟨hUsec.1, evWord_sync_first_hit (p := p) (m := m) (n := n) (ℓ := ℓ)
      (e := fun i => (e i : ℕ)) (U := U) (fun i => Nat.lt_succ_iff.mp (e i).isLt)
      hUsec.2 hUword⟩
  have hμG : arrayMeasure N G = ∑ e : (Fin N → Fin (K + 1)), arrayMeasure N (sec e) := by
    rw [hcover, measure_iUnion (μ := arrayMeasure N) hdisj hsec_amb, tsum_fintype]
  have hμW : arrayMeasure N (⋃ e, W e) =
      ∑ e : (Fin N → Fin (K + 1)), arrayMeasure N (W e) := by
    rw [measure_iUnion (μ := arrayMeasure N) hW_disj hW_meas, tsum_fintype]
  calc ENNReal.ofReal (1 - p) ^ ((2 * K + 1) * N) * arrayMeasure N G
      = ENNReal.ofReal (1 - p) ^ ((2 * K + 1) * N) *
          ∑ e : (Fin N → Fin (K + 1)), arrayMeasure N (sec e) := by rw [hμG]
    _ = ∑ e : (Fin N → Fin (K + 1)),
          ENNReal.ofReal (1 - p) ^ ((2 * K + 1) * N) * arrayMeasure N (sec e) :=
        Finset.mul_sum _ _ _
    _ ≤ ∑ e : (Fin N → Fin (K + 1)), arrayMeasure N (W e) :=
        Finset.sum_le_sum fun e _ => hforce e
    _ = arrayMeasure N (⋃ e, W e) := hμW.symm
    _ ≤ arrayMeasure N (G ∩ {U : Array N |
          (∀ u, u < 2 * K + 1 → ∀ i, (trajectory p m U (n + u)).pos i ≤ ℓ) ∧
            ∀ i, (trajectory p m U (n + (2 * K + 1))).pos i = ℓ + 1}) :=
        measure_mono (Set.iUnion_subset hsub)

end DefectSync


