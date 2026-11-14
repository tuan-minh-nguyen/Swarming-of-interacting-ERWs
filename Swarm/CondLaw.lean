import Swarm.Atom

namespace SwarmCross

open MeasureTheory Set
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory
open Swarming.History Swarming.HistoryDeterminism Swarming.Transition
open Swarming.StepCross
open scoped ENNReal BigOperators

variable {N : ℕ}

set_option linter.unusedSimpArgs false
set_option warn.classDefReducibility false

/-! ### The used coordinate set of a reference trajectory -/

/-- The coordinates read by the reference trajectory before time `n`. -/
noncomputable def usedCoords (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) :
    Finset (Fin N × ℤ × ℕ) :=
  ((Finset.range n).product Finset.univ).image (fun q : ℕ × Fin N => departureCoord p m U q.1 q.2)

lemma mem_usedCoords {p : ℝ} {m : ℕ} {U : Array N} {t n : ℕ} (ht : t < n) (i : Fin N) :
    departureCoord p m U t i ∈ usedCoords p m U n := by
  refine Finset.mem_image.mpr ⟨(t, i), ?_, rfl⟩
  exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr ht, Finset.mem_univ i⟩

lemma usedCoords_mono {p : ℝ} {m : ℕ} {U : Array N} {n : ℕ} :
    usedCoords p m U n ⊆ usedCoords p m U (n + 1) := by
  intro c hc
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp hq
  rw [Finset.mem_range] at h1
  exact Finset.mem_image.mpr ⟨q, Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (by omega), h2⟩, rfl⟩

/-- The coordinates of the departure at time `n` are fresh: no earlier departure consumed them. -/
lemma departureCoord_notMem_usedCoords (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    departureCoord p m U n i ∉ usedCoords p m U n := by
  intro hmem
  obtain ⟨q, hq, hqc⟩ := Finset.mem_image.mp hmem
  obtain ⟨h1, -⟩ := Finset.mem_product.mp hq
  rw [Finset.mem_range] at h1
  obtain ⟨t, j⟩ := q
  have hpair : (j, t) = (i, n) := allDepartures_injective p m U hqc
  have htn : t = n := congrArg Prod.snd hpair
  omega

/-! ### The letter cylinder over the used coordinates -/

/-- The letter cylinder of the reference trajectory: the values of the used coordinates that
produce the reference's letters. -/
noncomputable def boxCyl (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) :
    Set (usedCoords p m U n → ℝ) :=
  {g | ∀ (t : ℕ) (ht : t < n) (i : Fin N),
    g ⟨departureCoord p m U t i, mem_usedCoords ht i⟩ ∈
      jumpSet (stepDir p m U t i) (currentAlpha p m U t i)}

lemma letterBox_eq_preimage_boxCyl (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) :
    letterBox p m U n =
      (fun ω : Array N => fun c : usedCoords p m U n => ω c) ⁻¹' boxCyl p m U n := by
  ext ω
  simp only [letterBox, boxCyl, mem_preimage, mem_ofPred_eq]

lemma measurableSet_boxCyl (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) :
    MeasurableSet (boxCyl p m U n) := by
  have heq : boxCyl p m U n = ⋂ q : Fin n × Fin N,
      {g : usedCoords p m U n → ℝ |
        g ⟨departureCoord p m U (q.1 : ℕ) q.2, mem_usedCoords (N := N) q.1.2 q.2⟩ ∈
          jumpSet (stepDir p m U (q.1 : ℕ) q.2) (currentAlpha p m U (q.1 : ℕ) q.2)} := by
    ext g
    simp only [boxCyl, mem_ofPred_eq, mem_iInter]
    exact ⟨fun h q => h (q.1 : ℕ) q.1.2 q.2, fun h t ht i => h ⟨⟨t, ht⟩, i⟩⟩
  rw [heq]
  exact MeasurableSet.iInter fun q =>
    (jumpSet_measurable _ _).preimage (measurable_pi_apply _)

/-! ### Fresh coordinates retain their product law on an atom -/

/-- **Conditional independence on an atom.**  On the letter box of the reference array, the
vector of *next* departure coordinates of all walkers is independent with product uniform law.
This is the honest (positive-mass) replacement of `Swarming.History.measure_actualHistory_and_next`,
whose history event is null. -/
theorem measure_letterBox_inter_letters (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ)
    (I : Fin N → Set ℝ) (hI : ∀ i, MeasurableSet (I i)) :
    arrayMeasure N (letterBox p m U n ∩
        ⋂ i, (fun ω : Array N => ω (departureCoord p m U n i)) ⁻¹' I i) =
      arrayMeasure N (letterBox p m U n) * ∏ i, uniform01 (I i) := by
  have hf : Function.Injective (fun i : Fin N => departureCoord p m U n i) :=
    fun i j hij => congrArg Prod.fst hij
  have hfresh : ∀ i : Fin N, departureCoord p m U n i ∉ usedCoords p m U n :=
    departureCoord_notMem_usedCoords p m U n
  have hmain := SwarmIID.indep_fresh_finset (array_independent N)
    (fun c => measurable_pi_apply c) hf hfresh (boxCyl p m U n)
    (measurableSet_boxCyl p m U n) I hI
  rw [← letterBox_eq_preimage_boxCyl] at hmain
  rw [hmain]
  congr 1
  exact Finset.prod_congr rfl fun i _ => arrayMeasure_preimage_set N _ _ (hI i)

/-! ### The one-step law on an atom -/

/-- On the letter box, "walker `i` steps right" is the letter event at the fresh coordinate. -/
lemma letterBox_inter_stepUp (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    letterBox p m U n ∩ stepUp p m n i =
      letterBox p m U n ∩ ((fun ω : Array N => ω (departureCoord p m U n i)) ⁻¹'
        jumpSet true (currentAlpha p m U n i)) := by
  ext ω
  simp only [mem_inter_iff, mem_preimage]
  constructor
  · rintro ⟨hL, hstep⟩
    refine ⟨hL, ?_⟩
    have hst : ∀ k ≤ n, (trajectory p m ω k).pos = (trajectory p m U k).pos :=
      (letterBox_iff_path p m U n ω).mp hL
    have hstate := state_eq_of_path_eq p m U ω n hst
    have hα := currentAlpha_eq_of_state (m := m) hstate
    have hcoord := departureCoord_eq_of_state (m := m) hstate
    have hnext : Trajectory.nextPos p m ω (trajectory p m ω n) i =
        (trajectory p m ω n).pos i + jumpShift true := by
      rw [mem_stepUp] at hstep
      rw [trajectory_succ, nextWalkState_pos] at hstep
      rw [hstep]; rfl
    have hmem := (nextPos_eq_iff p m ω n (fun _ => true) i).mp hnext
    rwa [hcoord, hα] at hmem
  · rintro ⟨hL, hmem⟩
    refine ⟨hL, ?_⟩
    have hst : ∀ k ≤ n, (trajectory p m ω k).pos = (trajectory p m U k).pos :=
      (letterBox_iff_path p m U n ω).mp hL
    have hstate := state_eq_of_path_eq p m U ω n hst
    have hα := currentAlpha_eq_of_state (m := m) hstate
    have hcoord := departureCoord_eq_of_state (m := m) hstate
    rw [← hcoord, ← hα] at hmem
    have hnext := (nextPos_eq_iff p m ω n (fun _ => true) i).mpr hmem
    rw [mem_stepUp, trajectory_succ, nextWalkState_pos, hnext]
    simp [jumpShift]

/-- **The exact one-step right-jump law on a path-prefix atom**: conditionally on the reference
atom, walker `i` steps right with mass exactly its actual right probability `currentAlpha`. -/
theorem measure_letterBox_inter_stepUp {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    arrayMeasure N (letterBox p m U n ∩ stepUp p m n i) =
      arrayMeasure N (letterBox p m U n) * ENNReal.ofReal (currentAlpha p m U n i) := by
  rw [letterBox_inter_stepUp]
  have hI : ∀ l : Fin N, MeasurableSet
      (if l = i then jumpSet true (currentAlpha p m U n i) else Set.univ) := by
    intro l
    by_cases hli : l = i
    · simp only [if_pos hli]; exact jumpSet_measurable _ _
    · simp only [if_neg hli]; exact MeasurableSet.univ
  have hmain := measure_letterBox_inter_letters p m U n
    (fun l => if l = i then jumpSet true (currentAlpha p m U n i) else Set.univ) hI
  have hinter : (⋂ l, (fun ω : Array N => ω (departureCoord p m U n l)) ⁻¹'
      (if l = i then jumpSet true (currentAlpha p m U n i) else Set.univ)) =
      ((fun ω : Array N => ω (departureCoord p m U n i)) ⁻¹'
        jumpSet true (currentAlpha p m U n i)) := by
    ext ω
    simp only [mem_iInter, mem_preimage]
    constructor
    · intro h
      have := h i
      simpa using this
    · intro h l
      by_cases hli : l = i
      · subst hli; simpa using h
      · simp only [if_neg hli, mem_univ]
  rw [hinter] at hmain
  rw [hmain]
  congr 1
  have hterm : ∀ l : Fin N, uniform01 (if l = i then jumpSet true (currentAlpha p m U n i)
      else Set.univ) = if l = i then ENNReal.ofReal (currentAlpha p m U n i) else 1 := by
    intro l
    by_cases hli : l = i
    · rw [if_pos hli, if_pos hli]
      simpa [jumpWeight] using uniform01_jumpSet (currentAlpha_pos hp0 hp1 m U n i)
        (currentAlpha_lt_one hp0 hp1 m U n i) true
    · rw [if_neg hli, if_neg hli]
      simp [uniform01]
  rw [Finset.prod_congr rfl (fun l _ => hterm l),
    Finset.prod_eq_single i (fun l _ hli => by simp only [if_neg hli])
      (fun h => absurd (Finset.mem_univ i) h)]
  simp

/-! ### Positivity of the atoms -/

lemma jumpWeight_pos {α : ℝ} (h0 : 0 < α) (h1 : α < 1) (b : Bool) : 0 < jumpWeight b α := by
  cases b <;> simp [jumpWeight] <;> linarith

lemma uniform01_jumpSet_pos {α : ℝ} (h0 : 0 < α) (h1 : α < 1) (b : Bool) :
    0 < uniform01 (jumpSet b α) := by
  rw [uniform01_jumpSet h0 h1]
  exact ENNReal.ofReal_pos.mpr (jumpWeight_pos h0 h1 b)

/-- The letter box at time `n + 1` is the letter box at time `n` together with the letters of the
departures at time `n`. -/
lemma letterBox_succ (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) :
    letterBox p m U (n + 1) = letterBox p m U n ∩
      ⋂ i : Fin N, (fun ω : Array N => ω (departureCoord p m U n i)) ⁻¹'
        jumpSet (stepDir p m U n i) (currentAlpha p m U n i) := by
  ext ω
  simp only [mem_letterBox, mem_inter_iff, mem_iInter, mem_preimage]
  constructor
  · rintro h
    exact ⟨fun t ht i => h t (by omega) i, fun i => h n (by omega) i⟩
  · rintro ⟨h1, h2⟩ t ht i
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with h | h
    · exact h1 t h i
    · subst h; exact h2 i

/-- **Every atom has positive mass** — unlike the exact-value histories of `HistoryNull`. -/
theorem measure_letterBox_pos {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) (U : Array N) :
    ∀ n, 0 < arrayMeasure N (letterBox p m U n) := by
  intro n
  induction n with
  | zero =>
      have h : letterBox p m U 0 = Set.univ := by
        ext ω; simp [mem_letterBox]
      rw [h, measure_univ]
      exact zero_lt_one
  | succ n ih =>
      rw [letterBox_succ, measure_letterBox_inter_letters p m U n
        (fun i => jumpSet (stepDir p m U n i) (currentAlpha p m U n i))
        (fun i => jumpSet_measurable _ _)]
      refine ENNReal.mul_pos ih.ne' (Finset.prod_ne_zero_iff.mpr ?_)
      intro i _
      exact (uniform01_jumpSet_pos (currentAlpha_pos hp0 hp1 m U n i)
        (currentAlpha_lt_one hp0 hp1 m U n i) (stepDir p m U n i)).ne'

theorem measure_letterBox_ne_zero {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) (U : Array N)
    (n : ℕ) : arrayMeasure N (letterBox p m U n) ≠ 0 :=
  (measure_letterBox_pos hp0 hp1 m U n).ne'

end SwarmCross


