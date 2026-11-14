/-
# Defect-dependent synchronisation force on the actual array measure

`Swarm/EvWordForce.lean` proves, for a *fixed* prescribed `±1` word `ε` of length `k`
and **any** enlarged-filtration past event `G`,

    (1-p)^(k*N) * mu G  <=  mu (G  ∩  evWord p m n univ ε k),

and its own ledger records the remaining gap: *the word that turns a record with bounded
defect into a simultaneous record has to depend on the position vector at the record
time*, so a fixed-word force does not give the paper's `(force)`
(`main_1d_revised.tex`, proof of Proposition `front`).

This file closes exactly that gap on the actual model, without changing any existing
declaration.  For a reference level `ℓ`, an even defect vector `2 * (e i)` (`e i <= K`) and
a past event `G` on which every walker stands at `ℓ - 2 * (e i)`, it prescribes the
**defect-compensating word**

    syncWord K e u i =  -1, +1, -1, +1, ...   for u < 2K - 2*(e i)  (alternating from -1)
                        +1                    for the remaining 2*(e i) + 1 steps,

of common length `2K+1` for the whole swarm.  The alternating prefix has even length, so it
returns every walker to its own starting site while keeping it at or below `ℓ`; the
trailing right steps then lift every walker to the *same* level `ℓ + 1` at the *same*
time.  The word is therefore **position dependent**, and the force is obtained by
decomposing `G` into the finitely many defect sectors (the step that
`EV_WORD_FORCE.md` records as not done) and applying the already-proved fixed-word force
sector by sector.

Scope: this is a one-block force estimate, starting from an explicit reference level and an
explicit even defect bound.  It contains no `RegenPath.D`, no nullity of `{D = ⊤}`, no
attempt tower, no invariant law and no regeneration claim.  See `RESULTS.md` for the exact
statement and the remaining-input ledger.
-/
import Swarm.EvWordForce

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

namespace DefectSync

open Swarming.Uniform Swarming.Trajectory Swarming.Enl

variable {N : ℕ}

/-! ### The driven step is a unit step -/

/-- The actual driven step is always `±1`. -/
theorem drivenStep_unit (u α : ℝ) :
    Swarming.drivenStep u α = 1 ∨ Swarming.drivenStep u α = -1 := by
  unfold Swarming.drivenStep
  split_ifs <;> simp

/-! ### The defect-compensating word -/

/-- The defect-compensating word of length `2 * K + 1`: an alternating `-1, +1, ...`
prefix of even length `2 * K - 2 * (e i)` followed by `2 * (e i) + 1` right steps. -/
noncomputable def syncWord (K : ℕ) (e : Fin N → ℕ) : ℕ → Fin N → ℤ :=
  fun u i => if u < 2 * K - 2 * e i then (if u % 2 = 0 then -1 else 1) else 1

/-- Every letter of the defect-compensating word is a unit step. -/
theorem syncWord_unit (K : ℕ) (e : Fin N → ℕ) (u : ℕ) (i : Fin N) :
    syncWord (N := N) K e u i = 1 ∨ syncWord (N := N) K e u i = -1 := by
  unfold syncWord
  split_ifs <;> simp

/-- The alternating prefix sums to zero over an even number of steps. -/
theorem sum_range_alt_of_even (j : ℕ) (hj : Even j) :
    ∑ u ∈ Finset.range j, (if u % 2 = 0 then (-1 : ℤ) else 1) = 0 := by
  obtain ⟨t, rfl⟩ := hj
  induction t with
  | zero => simp
  | succ t ih =>
      have h2 : t + 1 + (t + 1) = t + t + 1 + 1 := by ring
      rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, ih]
      have h1 : (t + t) % 2 = 0 := by omega
      have h3 : (t + t + 1) % 2 ≠ 0 := by omega
      simp [h1, h3]

/-- **The word's exact displacement.**  In `2 * K + 1` steps the word moves a walker
standing `2 * (e i)` levels below the reference level up by exactly `2 * (e i) + 1`. -/
theorem sum_syncWord (K : ℕ) (e : Fin N → ℕ) (i : Fin N) (he : e i ≤ K) :
    ∑ u ∈ Finset.range (2 * K + 1), syncWord (N := N) K e u i = 2 * (e i : ℤ) + 1 := by
  have hje : Even (2 * K - 2 * e i) := by
    refine ⟨K - e i, ?_⟩
    have h2 : 2 * e i ≤ 2 * K := Nat.mul_le_mul_left 2 he
    omega
  have hsplit : (2 * K - 2 * e i) + (2 * e i + 1) = 2 * K + 1 := by omega
  have hfirst : ∑ u ∈ Finset.range (2 * K - 2 * e i), syncWord (N := N) K e u i = 0 := by
    rw [show ∑ u ∈ Finset.range (2 * K - 2 * e i), syncWord (N := N) K e u i
        = ∑ u ∈ Finset.range (2 * K - 2 * e i),
            (if u % 2 = 0 then (-1 : ℤ) else 1) from ?_]
    · exact sum_range_alt_of_even _ hje
    · refine Finset.sum_congr rfl fun u hu => ?_
      have hlt : u < 2 * K - 2 * e i := Finset.mem_range.mp hu
      show (if u < 2 * K - 2 * e i then (if u % 2 = 0 then (-1 : ℤ) else 1) else 1) = _
      rw [if_pos hlt]
  have hsecond : ∑ x ∈ Finset.range (2 * e i + 1),
      syncWord (N := N) K e ((2 * K - 2 * e i) + x) i = 2 * (e i : ℤ) + 1 := by
    have hnone : ∀ x ∈ Finset.range (2 * e i + 1),
        ¬ ((2 * K - 2 * e i) + x < 2 * K - 2 * e i) := by
      intro x hx
      have hx' : x ≤ 2 * e i := by have := Finset.mem_range.mp hx; omega
      omega
    rw [show ∑ x ∈ Finset.range (2 * e i + 1),
        syncWord (N := N) K e ((2 * K - 2 * e i) + x) i
        = ∑ x ∈ Finset.range (2 * e i + 1), (1 : ℤ) from ?_]
    · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      push_cast
      ring
    · refine Finset.sum_congr rfl fun x hx => ?_
      show (if (2 * K - 2 * e i) + x < 2 * K - 2 * e i
          then (if ((2 * K - 2 * e i) + x) % 2 = 0 then (-1 : ℤ) else 1) else 1) = 1
      rw [if_neg (hnone x hx)]
  calc ∑ u ∈ Finset.range (2 * K + 1), syncWord (N := N) K e u i
      = ∑ u ∈ Finset.range ((2 * K - 2 * e i) + (2 * e i + 1)),
          syncWord (N := N) K e u i := by rw [hsplit]
    _ = ∑ u ∈ Finset.range (2 * K - 2 * e i), syncWord (N := N) K e u i +
          ∑ x ∈ Finset.range (2 * e i + 1), syncWord (N := N) K e ((2 * K - 2 * e i) + x) i :=
        Finset.sum_range_add (fun u => syncWord (N := N) K e u i) _ _
    _ = 0 + (2 * (e i : ℤ) + 1) := by rw [hfirst, hsecond]
    _ = 2 * (e i : ℤ) + 1 := by ring

/-! ### Reading a word off the trajectory -/

/-- Following the word for `k` steps gives the per-step jump identities at every earlier
step. -/
theorem evWord_step {p : ℝ} {m n : ℕ} {ε : ℕ → Fin N → ℤ} {k : ℕ} {U : Array N}
    (hU : U ∈ evWord p m n (Finset.univ : Finset (Fin N)) ε k) {u : ℕ} (hu : u < k)
    (i : Fin N) :
    (trajectory p m U (n + u + 1)).pos i = (trajectory p m U (n + u)).pos i + ε u i := by
  induction k with
  | zero => omega
  | succ k ih =>
      rw [evWord_succ] at hU
      obtain ⟨h1, h2⟩ := hU
      rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hlt | heq
      · exact ih h1 hlt
      · subst heq
        have hstep := h2 i (Finset.mem_univ i)
        simpa [Nat.add_assoc] using hstep

/-- Telescoping the jump identities: after `L` steps the position is the starting position
plus the word sum. -/
theorem pos_add_sum {p : ℝ} {m n : ℕ} (ε : ℕ → Fin N → ℤ) {L : ℕ} {U : Array N}
    (hstep : ∀ u, u < L → ∀ i,
      (trajectory p m U (n + u + 1)).pos i = (trajectory p m U (n + u)).pos i + ε u i)
    (i : Fin N) :
    (trajectory p m U (n + L)).pos i =
      (trajectory p m U n).pos i + ∑ u ∈ Finset.range L, ε u i := by
  induction L with
  | zero => simp
  | succ L ih =>
      have hL : (trajectory p m U (n + (L + 1))).pos i =
          (trajectory p m U (n + L)).pos i + ε L i := by
        have h := hstep L (Nat.lt_succ_self L) i
        simpa [Nat.add_assoc] using h
      have ih' := ih (fun u hu => hstep u (Nat.lt_trans hu (Nat.lt_succ_self L)))
      rw [hL, ih', Finset.sum_range_succ]
      ring

/-! ### Parity: every walker's position has the parity of the time

This is the fact used silently when `K - d_i` alternating steps are prescribed: all
walkers at one time have the same parity, so every gap below the swarm maximum is even. -/

/-- Every walker's position at time `n` is congruent to `n` modulo `2`. -/
theorem pos_parity (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) :
    ∀ n : ℕ, ∃ c : ℤ, (trajectory p m U n).pos i = (n : ℤ) + 2 * c := by
  intro n
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      have hstep : (trajectory p m U (n + 1)).pos i =
          (trajectory p m U n).pos i +
            Swarming.drivenStep (U (i, (trajectory p m U n).pos i,
              (trajectory p m U n).ell i ((trajectory p m U n).pos i)))
              (Swarming.Model.rightProbability p m (trajectory p m U n).ell i
                ((trajectory p m U n).pos i)) := by
        rw [trajectory_succ, nextWalkState_pos, nextPos]
      rcases drivenStep_unit (U (i, (trajectory p m U n).pos i,
            (trajectory p m U n).ell i ((trajectory p m U n).pos i)))
          (Swarming.Model.rightProbability p m (trajectory p m U n).ell i
            ((trajectory p m U n).pos i)) with h | h
      · refine ⟨c, ?_⟩
        rw [hstep, h, hc]
        push_cast
        ring
      · refine ⟨c - 1, ?_⟩
        rw [hstep, h, hc]
        push_cast
        ring

/-! ### The even defect sector -/

/-- The sector on which every walker stands exactly `2 * (e i)` levels below `ℓ`. -/
noncomputable def syncSector (p : ℝ) (m n : ℕ) (ℓ : ℤ) (e : Fin N → ℕ) : Set (Array N) :=
  {U | ∀ i, (trajectory p m U n).pos i = ℓ - 2 * (e i : ℤ)}

/-- Each defect sector is measurable for the enlarged filtration at time `n`. -/
theorem measurableSet_syncSector_enl (p : ℝ) (m n : ℕ) (ℓ : ℤ) (e : Fin N → ℕ) :
    MeasurableSet[enlMeas p m n] (syncSector (N := N) p m n ℓ e) := by
  rw [show syncSector (N := N) p m n ℓ e
      = ⋂ i : Fin N, {U : Array N | (trajectory p m U n).pos i = ℓ - 2 * (e i : ℤ)} from by
    ext U
    simp [syncSector]]
  exact MeasurableSet.iInter fun i =>
    (enl_pos_measurable p m n (le_refl n) i) (measurableSet_singleton _)

/-- Distinct defect sectors are disjoint (the position vector determines the sector). -/
theorem disjoint_syncSector (p : ℝ) (m n : ℕ) (ℓ : ℤ) :
    ∀ e e' : Fin N → ℕ, e ≠ e' →
      Disjoint (syncSector (N := N) p m n ℓ e) (syncSector (N := N) p m n ℓ e') := by
  intro e e' hne
  rw [Set.disjoint_left]
  intro U hU hU'
  apply hne
  funext i
  have h1 := hU i
  have h3 := hU' i
  have h4 : ((e i : ℕ) : ℤ) = ((e' i : ℕ) : ℤ) := by
    rw [h1] at h3
    linarith
  exact Nat.cast_injective h4

/-! ### The main force -/

/-- **Defect-dependent synchronisation force.**  Let `G` be an enlarged-filtration past
event at time `n` on which all walkers stand at `ℓ - 2 * (e i)` for one common reference
level `ℓ` and one even defect vector `2 * (e i)` with `e i ≤ K`.  Then on `G` the swarm
follows the position-dependent word `syncWord K e` with conditional probability at least
`(1-p)^((2K+1)*N)`, and on that event every walker is at the *same* level `ℓ + 1` at the
*same* time `n + (2K+1)`.

The word depends on the past through `e`; the force is uniform over `G` nonetheless,
because `G` is split into the finitely many defect sectors and the fixed-word force is
applied on each.  No mass-one assumption, no nullity, no invariant law. -/
theorem defect_sync_force (p : ℝ) (hp0 : (1 : ℝ) / 2 ≤ p) (hp1 : p < 1)
    (m n K : ℕ) (ℓ : ℤ) {G : Set (Array N)} (hG : MeasurableSet[enlMeas p m n] G)
    (hsec : ∀ U ∈ G, ∃ e : Fin N → Fin (K + 1),
      ∀ i, (trajectory p m U n).pos i = ℓ - 2 * ((e i : ℕ) : ℤ)) :
    ENNReal.ofReal (1 - p) ^ ((2 * K + 1) * N) * arrayMeasure N G ≤
      arrayMeasure N (G ∩ {U : Array N |
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
      ∀ i, (trajectory p m U (n + (2 * K + 1))).pos i = ℓ + 1} := by
    intro e U hU
    obtain ⟨hUsec, hUword⟩ := hU
    refine ⟨hUsec.1, ?_⟩
    intro i
    have hstep : ∀ u, u < 2 * K + 1 → ∀ i,
        (trajectory p m U (n + u + 1)).pos i =
          (trajectory p m U (n + u)).pos i + syncWord K (fun i => (e i : ℕ)) u i :=
      fun u hu i => evWord_step (p := p) (m := m) (n := n)
        (ε := syncWord K (fun i => (e i : ℕ))) (k := 2 * K + 1) (u := u) hUword hu i
    have htel := pos_add_sum (p := p) (m := m) (n := n)
      (ε := syncWord K (fun i => (e i : ℕ))) (U := U) hstep i
    have hstart : (trajectory p m U n).pos i = ℓ - 2 * ((e i : ℕ) : ℤ) := hUsec.2 i
    have hsum := sum_syncWord K (fun i => ((e i : ℕ))) i (Nat.lt_succ_iff.mp (e i).isLt)
    rw [hstart, hsum] at htel
    rw [htel]
    ring
  have hμG : arrayMeasure N G = ∑ e : (Fin N → Fin (K + 1)), arrayMeasure N (sec e) := by
    rw [hcover, measure_iUnion (μ := arrayMeasure N) hdisj hsec_amb, tsum_fintype]
  have hμW : arrayMeasure N (⋃ e, W e) = ∑ e : (Fin N → Fin (K + 1)), arrayMeasure N (W e) := by
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
          ∀ i, (trajectory p m U (n + (2 * K + 1))).pos i = ℓ + 1}) :=
        measure_mono (Set.iUnion_subset hsub)

end DefectSync


