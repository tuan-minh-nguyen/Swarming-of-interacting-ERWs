import Swarm.RawStrictTransport
import SwarmDiameter.PathDiameter

open MeasureTheory

namespace Swarming.Diameter

variable {N : ℕ}

/-- The first time a walker visits level `r`, with value `⊤` if no walker visits it. -/
noncomputable def recordTime (X : RegenPath.Path N) (r : ℕ) : ℕ∞ :=
  RegenPath.tau X (r : ℤ)

/-- Time between successive record levels, with values in the extended naturals. -/
noncomputable def recordDuration (X : RegenPath.Path N) (r : ℕ) : ℕ∞ :=
  recordTime X (r + 1) - recordTime X r

theorem measurable_recordTime (r : ℕ) : Measurable (fun X : RegenPath.Path N => recordTime X r) :=
  RawStrictTransport.measurable_tau_fixed (r : ℤ)

theorem measurable_recordDuration (r : ℕ) :
    Measurable (fun X : RegenPath.Path N => recordDuration X r) :=
  (measurable_of_countable (fun q : ℕ∞ × ℕ∞ => q.1 - q.2)).comp
    ((measurable_recordTime (N := N) (r + 1)).prodMk (measurable_recordTime r))

theorem recordTime_ne_top_iff {X : RegenPath.Path N} {r : ℕ} :
    recordTime X r ≠ ⊤ ↔ ∃ n : ℕ, ∃ i : Fin N, X n i = (r : ℤ) := by
  classical
  unfold recordTime RegenPath.tau
  split_ifs <;> simp [*]

theorem recordTime_zero [Nonempty (Fin N)] {X : RegenPath.Path N} (hX0 : ∀ i, X 0 i = 0) :
    recordTime X 0 = 0 := by
  obtain ⟨i⟩ := ‹Nonempty (Fin N)›
  exact RegenPath.tau_eq_iff.mpr ⟨⟨i, hX0 i⟩, fun n h => (Nat.not_lt_zero n h).elim⟩

theorem recordTime_lt_of_lt {X : RegenPath.Path N} (hX0 : ∀ i, X 0 i = 0)
    (hstep : ∀ n i, |X (n + 1) i - X n i| = 1) {r s : ℕ} (hrs : r < s)
    (hs : recordTime X s ≠ ⊤) : recordTime X r < recordTime X s := by
  obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp hs
  rw [← ht]
  exact RegenPath.tau_lt_of_lt hX0 hstep ht.symm (by positivity) (by exact_mod_cast hrs)

theorem recordTime_mono {X : RegenPath.Path N} (hX0 : ∀ i, X 0 i = 0)
    (hstep : ∀ n i, |X (n + 1) i - X n i| = 1) :
    Monotone (recordTime X) := by
  intro r s hrs
  by_cases hs : recordTime X s = ⊤
  · rw [hs]
    exact le_top
  · rcases hrs.eq_or_lt with rfl | hlt
    · exact le_rfl
    · exact (recordTime_lt_of_lt hX0 hstep hlt hs).le

private theorem recordTime_eq_after_pathRel_iff {X : RegenPath.Path N} {t d r s : ℕ}
    (hrec : SwarmChain.pathRec t (d : ℤ) X) :
    recordTime (SwarmChain.pathRel t (d : ℤ) X) r = (s : ℕ∞) ↔
      recordTime X (d + r) = ((t + s : ℕ) : ℕ∞) := by
  unfold recordTime
  rw [RegenPath.tau_eq_iff, RegenPath.tau_eq_iff]
  simp only [SwarmChain.pathRel, Nat.cast_add]
  constructor
  · rintro ⟨⟨i, hi⟩, hmin⟩
    refine ⟨⟨i, by omega⟩, ?_⟩
    intro u hu j hj
    by_cases hut : u < t
    · have hlt := hrec.1 u hut j
      omega
    · have hts : t + (u - t) = u := by omega
      apply hmin (u - t) (by omega) j
      rw [hts, hj]
      ring
  · rintro ⟨⟨i, hi⟩, hmin⟩
    refine ⟨⟨i, by omega⟩, ?_⟩
    intro u hu j hj
    exact hmin (t + u) (by omega) j (by omega)

/-- A simultaneous record at time `t` and level `d` shifts all subsequent first hitting times. -/
theorem recordTime_add_eq_of_pathRec {X : RegenPath.Path N} {t d : ℕ}
    (hrec : SwarmChain.pathRec t (d : ℤ) X) (r : ℕ) :
    recordTime X (d + r) = (t : ℕ∞) + recordTime (SwarmChain.pathRel t (d : ℤ) X) r := by
  by_cases hf : recordTime (SwarmChain.pathRel t (d : ℤ) X) r = ⊤
  · rw [hf, show (t : ℕ∞) + ⊤ = ⊤ from rfl]
    by_contra ha
    obtain ⟨u, hu⟩ := ENat.ne_top_iff_exists.mp ha
    have ht : t ≤ u := by
      obtain ⟨⟨i, hi⟩, _⟩ := RegenPath.tau_eq_iff.mp hu.symm
      by_contra h
      have hlt := hrec.1 u (by omega) i
      push_cast at hi
      omega
    rw [show u = t + (u - t) by omega] at hu
    have hb := (recordTime_eq_after_pathRel_iff hrec).mpr hu.symm
    rw [hf] at hb
    exact ENat.natCast_ne_top _ hb.symm
  · obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.mp hf
    rw [← hs, ← ENat.natCast_add]
    exact (recordTime_eq_after_pathRel_iff hrec).mp hs.symm

/-- The duration between two successive record levels is invariant under a shift at a
simultaneous record. -/
theorem recordDuration_pathRel {X : RegenPath.Path N} {t d : ℕ}
    (hrec : SwarmChain.pathRec t (d : ℤ) X) (r : ℕ) :
    recordDuration (SwarmChain.pathRel t (d : ℤ) X) r = recordDuration X (d + r) := by
  let Y := SwarmChain.pathRel t (d : ℤ) X
  have hnext : d + r + 1 = d + (r + 1) := by omega
  rw [recordDuration, recordDuration, hnext, recordTime_add_eq_of_pathRec hrec r,
    recordTime_add_eq_of_pathRec hrec (r + 1)]
  change recordTime Y (r + 1) - recordTime Y r =
    ((t : ℕ∞) + recordTime Y (r + 1)) - ((t : ℕ∞) + recordTime Y r)
  cases recordTime Y r with
  | top => simp
  | coe a =>
    cases recordTime Y (r + 1) with
    | top =>
      change (⊤ : ℕ∞) - (a : ℕ∞) = ⊤ - ((t : ℕ∞) + (a : ℕ∞))
      rw [← ENat.natCast_add, ENat.top_sub_natCast, ENat.top_sub_natCast]
    | coe b => simp only [← ENat.natCast_add, ← ENat.natCast_sub, Nat.add_sub_add_left]

variable [Nonempty (Fin N)]

/-- Some diameter on the interval from record level `r` up to the next record is at least `x`. -/
def recordIntervalExceeds (X : RegenPath.Path N) (r : ℕ) (x : ℝ) : Prop :=
  ∃ u : ℕ, recordTime X r ≤ (u : ℕ∞) ∧ (u : ℕ∞) < recordTime X (r + 1) ∧ x ≤ pathDiameter u X

theorem measurableSet_recordIntervalExceeds (r : ℕ) (x : ℝ) :
    MeasurableSet {X : RegenPath.Path N | recordIntervalExceeds X r x} := by
  have hset : {X : RegenPath.Path N | recordIntervalExceeds X r x} =
      ⋃ u : ℕ, {X : RegenPath.Path N | recordTime X r ≤ (u : ℕ∞)} ∩
        {X | (u : ℕ∞) < recordTime X (r + 1)} ∩ {X | x ≤ pathDiameter u X} := by
    ext X
    simp [recordIntervalExceeds, and_assoc]
  rw [hset]
  exact MeasurableSet.iUnion fun u =>
    (((measurable_recordTime r) (MeasurableSet.of_discrete (s := Set.Iic (u : ℕ∞)))).inter
      ((measurable_recordTime (r + 1)) (MeasurableSet.of_discrete (s := Set.Ioi (u : ℕ∞))))).inter
      ((measurable_pathDiameter u) measurableSet_Ici)

theorem recordIntervalExceeds_pathRel_iff {X : RegenPath.Path N} {t d : ℕ}
    (hrec : SwarmChain.pathRec t (d : ℤ) X) (r : ℕ) (x : ℝ) :
    recordIntervalExceeds (SwarmChain.pathRel t (d : ℤ) X) r x ↔
      recordIntervalExceeds X (d + r) x := by
  let Y := SwarmChain.pathRel t (d : ℤ) X
  have hnext : d + r + 1 = d + (r + 1) := by omega
  unfold recordIntervalExceeds
  rw [hnext, recordTime_add_eq_of_pathRec hrec r, recordTime_add_eq_of_pathRec hrec (r + 1)]
  change (∃ u : ℕ, recordTime Y r ≤ (u : ℕ∞) ∧ _ ∧ _) ↔ _
  constructor
  · rintro ⟨u, hu, hv, hd⟩
    refine ⟨t + u, ?_, ?_, ?_⟩
    · exact ENat.natCast_add t u ▸ add_le_add_right hu (t : ℕ∞)
    · rw [ENat.natCast_add]
      exact (ENat.add_lt_add_iff_left (ENat.natCast_ne_top t)).mpr hv
    · exact (pathDiameter_shift X t u (d : ℤ)) ▸ hd
  · rintro ⟨u, hu, hv, hd⟩
    have ht : (t : ℕ∞) ≤ (u : ℕ∞) := le_trans le_self_add hu
    have htu := ENat.natCast_le_natCast.mp ht
    obtain ⟨s, rfl⟩ : ∃ s, u = t + s := ⟨u - t, by omega⟩
    rw [ENat.natCast_add] at hu hv
    refine ⟨s, (ENat.add_le_add_iff_left (ENat.natCast_ne_top t)).mp hu,
      (ENat.add_lt_add_iff_left (ENat.natCast_ne_top t)).mp hv, ?_⟩
    exact (pathDiameter_shift X t s (d : ℤ)).symm ▸ hd

omit [Nonempty (Fin N)] in
private theorem abs_sub_le_add_steps {X : RegenPath.Path N}
    (hstep : ∀ n i, |X (n + 1) i - X n i| ≤ 1) (s k : ℕ) (i : Fin N) :
    |X (s + k) i - X s i| ≤ (k : ℤ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, Nat.add_succ]
    calc
      |X (s + k + 1) i - X s i| =
          |(X (s + k + 1) i - X (s + k) i) + (X (s + k) i - X s i)| := by congr 1; ring
      _ ≤ |X (s + k + 1) i - X (s + k) i| + |X (s + k) i - X s i| := abs_add_le ..
      _ ≤ (k : ℤ) + 1 := by linarith [hstep (s + k) i]

/-- The diameter of nearest-neighbour paths increases by at most two per time step. -/
theorem pathDiameter_add_le {X : RegenPath.Path N}
    (hstep : ∀ n i, |X (n + 1) i - X n i| ≤ 1) (s k : ℕ) :
    pathDiameter (s + k) X ≤ pathDiameter s X + 2 * (k : ℝ) := by
  let S : Finset (Fin N) := Finset.univ
  have Sne : S.Nonempty := Finset.univ_nonempty
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Sne (X (s + k))
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' Sne (X (s + k))
  have hd : pathDiameter (s + k) X = ((X (s + k) i - X (s + k) j : ℤ) : ℝ) := by
    unfold pathDiameter LeaderDescent.spreadZ
    congr 1
    exact congrArg₂ (· - ·) hi hj
  rw [hd, Int.cast_sub]
  have hij := sub_le_pathDiameter s X i j
  rw [Int.cast_sub] at hij
  have hi' : (X (s + k) i : ℝ) - X s i ≤ (k : ℝ) := by
    exact_mod_cast (abs_le.mp (abs_sub_le_add_steps hstep s k i)).2
  have hj' : -(k : ℝ) ≤ (X (s + k) j : ℝ) - X s j := by
    exact_mod_cast (abs_le.mp (abs_sub_le_add_steps hstep s k j)).1
  linarith

/-- To reach diameter `x` in a record interval, its initial diameter exceeds `x / 2`
or its duration exceeds `x / 4`. Both record times are finite. -/
theorem recordIntervalExceeds_imp_diameter_or_duration {X : RegenPath.Path N} {r s t : ℕ} {x : ℝ}
    (hstep : ∀ n i, |X (n + 1) i - X n i| ≤ 1)
    (hs : recordTime X r = (s : ℕ∞)) (ht : recordTime X (r + 1) = (t : ℕ∞))
    (h : recordIntervalExceeds X r x) :
    x / 2 < pathDiameter s X ∨ x / 4 < ((t - s : ℕ) : ℝ) := by
  obtain ⟨u, hsu, hut, hu⟩ := h
  rw [hs, ENat.natCast_le_natCast] at hsu
  rw [ht, ENat.natCast_lt_natCast] at hut
  have hd := pathDiameter_add_le hstep s (u - s)
  rw [Nat.add_sub_of_le hsu] at hd
  have hk : ((u - s : ℕ) : ℝ) < ((t - s : ℕ) : ℝ) := by
    exact_mod_cast (show u - s < t - s by omega)
  rcases lt_or_ge (x / 2) (pathDiameter s X) with h₁ | h₁
  · exact Or.inl h₁
  · right
    linarith

end Swarming.Diameter
