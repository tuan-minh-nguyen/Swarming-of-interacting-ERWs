import SwarmDiameter.PathDiameter
import SwarmDiameter.ReflectionExcursion
import SwarmDiameter.SymmetricConfinement
import SwarmDiameter.SymmetricTrial
import SwarmDiameter.TrialBounds

open Finset MeasureTheory Set
open Swarming Swarming.Enl Swarming.Model Swarming.Trajectory Swarming.Uniform
open SwarmCross SwarmReflect SwarmRestart
open scoped ENNReal

namespace Swarming.Diameter

variable {p : ℝ} {m : ℕ}

private theorem posPath_eq_of_mem_evWord {N n k : ℕ} [Nonempty (Fin N)]
    {U : Array N} {ε f : ℕ → Fin N → ℤ}
    (h : U ∈ evWord p m n univ ε k)
    (h₀ : ∀ i, posPath p m U n i = f 0 i)
    (hstep : ∀ u < k, ∀ i, ε u i = f (u + 1) i - f u i) :
    ∀ u ≤ k, ∀ i, posPath p m U (n + u) i = f u i := by
  intro u
  induction u with
  | zero => exact fun _ i => h₀ i
  | succ u ih =>
    intro hu i
    have hu' : u < k := by omega
    have hs := SyncAttemptForce.evWord_step_of_mem h hu' (Finset.mem_univ i)
    change posPath p m U (n + u + 1) i = posPath p m U (n + u) i + ε u i at hs
    rw [Nat.add_succ, hs, ih (by omega) i, hstep u hu' i]
    omega

private def preparation (L t : ℕ) (i : Fin 2) : ℤ :=
  if i = 0 ∨ t ≤ 2 * L then (t : ℤ)
  else if t ≤ 3 * L then 4 * (L : ℤ) - t
  else (t : ℤ) - 2 * L

private def preparationStep (L t : ℕ) (i : Fin 2) : ℤ :=
  preparation L (t + 1) i - preparation L t i

private theorem preparationStep_is_unit (L t : ℕ) (i : Fin 2) :
    preparationStep L t i = 1 ∨ preparationStep L t i = -1 := by
  fin_cases i
  · change preparationStep L t 0 = 1 ∨ preparationStep L t 0 = -1
    simp [preparationStep, preparation]
  · change preparationStep L t 1 = 1 ∨ preparationStep L t 1 = -1
    unfold preparationStep preparation
    simp only [show (1 : Fin 2) ≠ 0 by decide, false_or, Nat.cast_add, Nat.cast_one]
    split_ifs <;> omega

private theorem preparation_left_le (L t : ℕ) (ht : t ≤ 4 * L) :
    preparation L t (1 : Fin 2) ≤ 2 * (L : ℤ) := by
  unfold preparation
  simp only [show (1 : Fin 2) ≠ 0 by decide, false_or]
  split_ifs <;> omega

private theorem preparation_endpoint (L : ℕ) (hL : 0 < L) :
    preparation L (4 * L) (0 : Fin 2) = 4 * (L : ℤ) ∧
      preparation L (4 * L) (1 : Fin 2) = 2 * (L : ℤ) := by
  constructor
  · simp [preparation]
  · unfold preparation
    simp only [show (1 : Fin 2) ≠ 0 by decide, false_or]
    split_ifs <;> omega

private def pairSteps (k : ℕ) : ((Fin k → Bool) × (Fin k → Bool)) ↪ (Fin k → Fin 2 → Bool) where
  toFun q u i := if i = 0 then !(q.1 u) else q.2 u
  inj' q q' h := by
    apply Prod.ext
    · funext u
      have he := congrFun (congrFun h u) (0 : Fin 2)
      change Bool.not (q.1 u) = Bool.not (q'.1 u) at he
      simpa using he
    · funext u
      exact congrFun (congrFun h u) (1 : Fin 2)

private theorem preparation_positions {n L : ℕ} {r : ℤ} {U : Array 2}
    (hrec : RecordAt p m U n r)
    (hprep : U ∈ evWord p m n univ (preparationStep L) (4 * L)) :
    ∀ t ≤ 4 * L, ∀ i, posPath p m U (n + t) i = r + preparation L t i := by
  apply posPath_eq_of_mem_evWord hprep
  · intro i
    rw [show preparation L 0 i = 0 by simp [preparation], add_zero]
    exact hrec.2 i
  · intro u _ i
    unfold preparationStep
    ring

private theorem future_positions {n L k u : ℕ} {r : ℤ} {U : Array 2}
    (hL : 0 < L) (hu : u ≤ k)
    (hrec : RecordAt p m U n r)
    (hprep : U ∈ evWord p m n univ (preparationStep L) (4 * L))
    (w v : Fin k → Bool)
    (hword : U ∈ evWord p m (n + 4 * L) univ (signedSteps (pairSteps k (w, v))) u) :
    ∀ s ≤ u,
      posPath p m U (n + 4 * L + s) (0 : Fin 2) = r + 4 * (L : ℤ) - psum w s ∧
      posPath p m U (n + 4 * L + s) (1 : Fin 2) = r + 2 * (L : ℤ) + psum v s := by
  let f (s : ℕ) (i : Fin 2) := if i = 0 then r + 4 * (L : ℤ) - psum w s
    else r + 2 * (L : ℤ) + psum v s
  have h₀ (i : Fin 2) : posPath p m U (n + 4 * L) i = f 0 i := by
    rw [preparation_positions hrec hprep _ le_rfl i]
    obtain ⟨h₀, h₁⟩ := preparation_endpoint L hL
    fin_cases i <;> simp [f, h₀, h₁]
  have hstep (s : ℕ) (hs : s < u) (i : Fin 2) :
      signedSteps (pairSteps k (w, v)) s i = f (s + 1) i - f s i := by
    have hk : s < k := hs.trans_le hu
    rw [signedSteps, dif_pos hk]
    dsimp only [f]
    by_cases hi : i = 0
    · rw [if_pos hi, if_pos hi, psum_succ_of_lt w hk]
      change step (if i = 0 then !(w ⟨s, hk⟩) else v ⟨s, hk⟩) = _
      rw [if_pos hi, step_flip]
      ring
    · rw [if_neg hi, if_neg hi, psum_succ_of_lt v hk]
      change step (if i = 0 then !(w ⟨s, hk⟩) else v ⟨s, hk⟩) = _
      rw [if_neg hi]
      ring
  intro s hs
  obtain h := posPath_eq_of_mem_evWord hword h₀ hstep s hs
  exact ⟨by simpa [f] using h 0, by simpa [f] using h 1⟩

private theorem symmetric_after_preparation {n L k u : ℕ} {r : ℤ} {U : Array 2}
    (hL : 0 < L) (hm : 2 ≤ m) (hu : u ≤ k)
    (hrec : RecordAt p m U n r)
    (hprep : U ∈ evWord p m n univ (preparationStep L) (4 * L))
    {w v : Fin k → Bool} (hw : rmax w k < (L : ℤ))
    (hv : ∀ s ≤ k, |psum v s| ≤ (L : ℤ))
    (hword : U ∈ evWord p m (n + 4 * L) univ (signedSteps (pairSteps k (w, v))) u)
    (i : Fin 2) : alphaFun p m (n + 4 * L + u) i U = 1 / 2 := by
  let t := n + 4 * L + u
  let X := posPath p m U
  have hfuture := future_positions hL hu hrec hprep w v hword
  have habove (s : ℕ) (hs : s ≤ u) : r + 3 * (L : ℤ) < X (n + 4 * L + s) 0 := by
    have h := (psum_le_rmax w s).trans (rmax_mono w (hs.trans hu))
    exact lt_of_lt_of_eq (by omega : r + 3 * (L : ℤ) < r + 4 * (L : ℤ) - psum w s)
      (hfuture s hs).1.symm
  have hconf (s : ℕ) (hs : s ≤ u) :
      r + (L : ℤ) ≤ X (n + 4 * L + s) 1 ∧ X (n + 4 * L + s) 1 ≤ r + 3 * (L : ℤ) := by
    dsimp only [X]
    rw [(hfuture s hs).2]
    have h := abs_le.mp (hv s (hs.trans hu))
    omega
  have hbelow (j : ℕ) (hj : j ≤ t) : X j 1 ≤ r + 3 * (L : ℤ) := by
    by_cases hj₀ : j < n
    · have h := hrec.1 j hj₀ (1 : Fin 2)
      change X j 1 < r at h
      omega
    · by_cases hj₁ : j ≤ n + 4 * L
      · have he : j = n + (j - n) := by omega
        dsimp only [X]
        rw [he, preparation_positions hrec hprep (j - n) (by omega) (1 : Fin 2)]
        have h := preparation_left_le L (j - n) (by omega)
        omega
      · set s := j - (n + 4 * L)
        have he : j = n + 4 * L + s := by omega
        rw [he]
        exact (hconf s (by dsimp only [t, s] at *; omega)).2
  have hvisit (j : ℕ) (hj : j ≤ t) (hjx : X j 0 = X t 1) : j ≤ n + 4 * L ∧ n ≤ j := by
    have hx : r + (L : ℤ) ≤ X t 1 ∧ X t 1 ≤ r + 3 * (L : ℤ) := hconf u le_rfl
    constructor
    · by_contra! h
      set s := j - (n + 4 * L)
      have he : j = n + 4 * L + s := by omega
      rw [he] at hjx
      have hh := habove s (by dsimp only [t, s] at *; omega)
      exact (not_lt_of_ge hx.2) (by rwa [hjx] at hh)
    · by_contra! h
      have hh := hrec.1 j h (0 : Fin 2)
      change X j 0 < r at hh
      have hh' : X t 1 < r := hjx ▸ hh
      omega
  have hℓ₀ : (trajectory p m U t).ell 1 (X t 0) = 0 := by
    rw [ell_eq_localTime]
    apply localTime_eq_zero_of_ne
    intro j hj
    change X j 1 ≠ X t 0
    have h := habove u le_rfl
    exact ne_of_lt ((hbelow j hj).trans_lt h)
  have hℓ₁ : (trajectory p m U t).ell 0 (X t 1) ≤ 1 := by
    rw [ell_eq_localTime, localTime_def]
    apply Finset.card_le_one.mpr
    intro j hj j' hj'
    simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff] at hj hj'
    change j ≤ t ∧ X j 0 = X t 1 at hj
    change j' ≤ t ∧ X j' 0 = X t 1 at hj'
    have h₁ := hvisit j hj.1 hj.2
    have h₂ := hvisit j' hj'.1 hj'.2
    have hlead (a : ℕ) (ha₀ : n ≤ a) (ha₁ : a ≤ n + 4 * L) : X a 0 = r + ((a - n : ℕ) : ℤ) := by
      have he : a = n + (a - n) := by omega
      conv_lhs => rw [he]
      dsimp only [X]
      rw [preparation_positions hrec hprep (a - n) (by omega) (0 : Fin 2)]
      simp [preparation]
    have heq : r + ((j - n : ℕ) : ℤ) = r + ((j' - n : ℕ) : ℤ) := by
      rw [← hlead j h₁.2 h₁.1, ← hlead j' h₂.2 h₂.1, hj.2, hj'.2]
    omega
  change rightProbability p m (trajectory p m U t).ell i (X t i) = _
  unfold rightProbability Excited otherVisits
  rw [if_neg]
  fin_cases i <;> simp [Fin.sum_univ_two, hℓ₀] <;> omega

/-- At a simultaneous record of the two-walker system, an event in the past
filtration has at least the stated fraction of its mass on paths with diameter
at least `L² + L` after the prescribed trial. -/
theorem two_walker_trial_mass_ge (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1)
    (hm : 2 ≤ m) (n : ℕ) {L : ℕ} (hL : 8 ≤ L)
    {G : Set (Array 2)} (hG : MeasurableSet[enlMeas p m n] G)
    (hrec : ∀ U ∈ G, ∃ r : ℤ, RecordAt p m U n r) :
    ((1 - Real.exp (-1)) * Real.exp (-12 * (L : ℝ)) / ((↑(L ^ 3 : ℕ) : ℝ) + 1)) *
        ((1 - p) ^ (8 * L) * (arrayMeasure 2).real G) ≤
      (arrayMeasure 2).real (G ∩ {U | (L : ℝ) ^ 2 + (L : ℝ) ≤
        pathDiameter (n + 4 * L + L ^ 3) (posPath p m U)}) := by
  let k := L ^ 3
  let G' := G ∩ evWord p m n univ (preparationStep L) (4 * L)
  have hG' : MeasurableSet[enlMeas p m (n + 4 * L)] G' :=
    ((enlMeas_le_add 2 p m n (4 * L)) G hG).inter
      (measurableSet_evWord_enl p m n univ (preparationStep L) (4 * L))
  have hG'mass : (1 - p) ^ (8 * L) * (arrayMeasure 2).real G ≤ (arrayMeasure 2).real G' := by
    have h := ENNReal.toReal_mono (measure_ne_top (arrayMeasure 2) G')
      (evWord_mass_ge_univ p hp₀.le hp₁ m n (preparationStep L) (preparationStep_is_unit L) hG (4 * L))
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by linarith)] at h
    rw [show 8 * L = (4 * L) * 2 by omega]
    exact h
  let A := univ.filter fun w : Fin k → Bool => rmax w k < (L : ℤ) ∧ psum w k = -((L ^ 2 : ℕ) : ℤ)
  let B := univ.filter fun v : Fin k → Bool => ∀ u ≤ k, |psum v u| ≤ (L : ℤ)
  let W := (A ×ˢ B).map (pairSteps k)
  have hW : (W.card : ℝ) = (A.card : ℝ) * (B.card : ℝ) := by
    simp [W, Finset.card_product]
  have hpair {ω} (hω : ω ∈ W) : ∃ w v : Fin k → Bool, w ∈ A ∧ v ∈ B ∧ pairSteps k (w, v) = ω := by
    obtain ⟨⟨w, v⟩, hab, he⟩ := Finset.mem_map.mp hω
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    exact ⟨w, v, ha, hb, he⟩
  have hsym : ∀ ω ∈ W, ∀ u < k, ∀ U ∈ G' ∩ evWord p m (n + 4 * L) univ (signedSteps ω) u,
      ∀ i, alphaFun p m (n + 4 * L + u) i U = 1 / 2 := by
    intro ω hω u hu U hU i
    obtain ⟨w, v, hw, hv, rfl⟩ := hpair hω
    obtain ⟨r, hr⟩ := hrec U hU.1.1
    exact symmetric_after_preparation (by omega) hm hu.le hr hU.1.2
      (Finset.mem_filter.mp hw).2.1 (Finset.mem_filter.mp hv).2 hU.2 i
  have hmass := symmetric_words_mass_eq hp₀ hp₁ (n + 4 * L) k W hG' hsym
  have hsub : (⋃ ω ∈ W, G' ∩ evWord p m (n + 4 * L) univ (signedSteps ω) k) ⊆
      G ∩ {U | (L : ℝ) ^ 2 + (L : ℝ) ≤ pathDiameter (n + 4 * L + k) (posPath p m U)} := by
    intro U hU
    obtain ⟨ω, hU⟩ := Set.mem_iUnion.mp hU
    obtain ⟨hω, hU⟩ := Set.mem_iUnion.mp hU
    obtain ⟨w, v, hw, hv, rfl⟩ := hpair hω
    refine ⟨hU.1.1, ?_⟩
    obtain ⟨r, hr⟩ := hrec U hU.1.1
    obtain ⟨h₀, h₁⟩ := future_positions (by omega) le_rfl hr hU.1.2 w v hU.2 k le_rfl
    have hu := sub_le_pathDiameter (n + 4 * L + k) (posPath p m U) 0 1
    rw [h₀, h₁, (Finset.mem_filter.mp hw).2.2] at hu
    have hv' := (abs_le.mp ((Finset.mem_filter.mp hv).2 k le_rfl)).2
    change (L : ℝ) ^ 2 + (L : ℝ) ≤ pathDiameter (n + 4 * L + k) (posPath p m U)
    push_cast at hu
    linarith [show (psum v k : ℝ) ≤ (L : ℝ) by exact_mod_cast hv']
  have hA : (1 - Real.exp (-1)) * (Real.exp (-8 * (L : ℝ)) * (2 : ℝ) ^ k) /
        ((k : ℝ) + 1) ≤ (A.card : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < (k : ℝ) + 1)).mpr
    rw [mul_comm (A.card : ℝ)]
    exact exp_neg_le_card_reflection_excursion hL
  have hB : Real.exp (-4 * (L : ℝ)) * (2 : ℝ) ^ k ≤ (B.card : ℝ) :=
    exp_neg_le_card_symmetric_confinement (by omega)
  have hpos : 0 < 1 - Real.exp (-1) := by
    linarith [Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0)]
  have hcoef : (1 - Real.exp (-1)) * Real.exp (-12 * (L : ℝ)) / ((k : ℝ) + 1) ≤
      (W.card : ℝ) * (1 / 2 : ℝ) ^ (k * 2) := by
    have hpow : (2 : ℝ) ^ k * (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ (k * 2) = 1 := by
      rw [← pow_add, ← Nat.mul_two, ← mul_pow]
      norm_num
    calc
      _ = ((1 - Real.exp (-1)) * (Real.exp (-8 * (L : ℝ)) * Real.exp (-4 * (L : ℝ))) /
          ((k : ℝ) + 1)) * ((2 : ℝ) ^ k * (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ (k * 2)) := by
        rw [hpow, mul_one, ← Real.exp_add, show -8 * (L : ℝ) + -4 * (L : ℝ) = -12 * (L : ℝ) by ring]
      _ = (((1 - Real.exp (-1)) * (Real.exp (-8 * (L : ℝ)) * (2 : ℝ) ^ k) /
            ((k : ℝ) + 1)) * (Real.exp (-4 * (L : ℝ)) * (2 : ℝ) ^ k)) *
              (1 / 2 : ℝ) ^ (k * 2) := by
        field_simp
      _ ≤ _ := by
        rw [hW]
        exact mul_le_mul_of_nonneg_right (mul_le_mul hA hB (by positivity) (by positivity)) (by positivity)
  calc
    _ ≤ ((W.card : ℝ) * (1 / 2 : ℝ) ^ (k * 2)) * (arrayMeasure 2).real G' :=
      mul_le_mul hcoef hG'mass (mul_nonneg (by positivity) measureReal_nonneg) (by positivity)
    _ = (arrayMeasure 2).real (⋃ ω ∈ W, G' ∩ evWord p m (n + 4 * L) univ (signedSteps ω) k) := by
      rw [hmass]
      ring
    _ ≤ _ := measureReal_mono hsub

private theorem exp_neg_le_two_walker_trial_coefficient
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) {L : ℕ} (hL : 1 ≤ L) :
    Real.exp (-(16 - 8 * Real.log (1 - p)) * (L : ℝ)) ≤
      ((1 - Real.exp (-1)) * Real.exp (-12 * (L : ℝ)) / ((↑(L ^ 3 : ℕ) : ℝ) + 1)) *
        (1 - p) ^ (8 * L) := by
  have hL₁ : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hconst : Real.exp (-(L : ℝ)) ≤ 1 - Real.exp (-1) := by
    apply (Real.exp_le_exp.mpr (by linarith : -(L : ℝ) ≤ -1)).trans
    rw [Real.exp_neg, le_sub_iff_add_le]
    have h := (div_le_iff₀ (Real.exp_pos 1)).mpr (by linarith [Real.add_one_le_exp 1] :
      (2 : ℝ) ≤ 1 * Real.exp 1)
    simpa only [div_eq_mul_inv, two_mul] using h
  have hden : (↑(L ^ 3 : ℕ) : ℝ) + 1 ≤ Real.exp (3 * (L : ℝ)) := by
    push_cast
    calc
      _ ≤ ((L : ℝ) + 1) ^ (3 : ℕ) := by nlinarith [sq_nonneg (L : ℝ)]
      _ ≤ (Real.exp (L : ℝ)) ^ (3 : ℕ) :=
        pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp _) _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hp : 0 < 1 - p := by linarith
  have hjump : (1 - p) ^ (8 * L) = Real.exp (8 * (L : ℝ) * Real.log (1 - p)) := by
    rw [show (8 * (L : ℝ)) = (↑(8 * L : ℕ) : ℝ) by push_cast; rfl, Real.exp_nat_mul, Real.exp_log hp]
  have hmain : Real.exp (-16 * (L : ℝ)) ≤
      (1 - Real.exp (-1)) * Real.exp (-12 * (L : ℝ)) / ((↑(L ^ 3 : ℕ) : ℝ) + 1) := by
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ ≤ Real.exp (-16 * (L : ℝ)) * Real.exp (3 * (L : ℝ)) :=
        mul_le_mul_of_nonneg_left hden (Real.exp_pos _).le
      _ = Real.exp (-(L : ℝ)) * Real.exp (-12 * (L : ℝ)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hconst (Real.exp_pos _).le
  calc
    _ = Real.exp (-16 * (L : ℝ)) * (1 - p) ^ (8 * L) := by
      rw [hjump, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hmain (pow_nonneg hp.le _)

/-- The conditional trial bound at a deterministic time in exponential form. -/
theorem two_walker_exp_trial_mass_ge (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1)
    (hm : 2 ≤ m) (n : ℕ) {L : ℕ} (hL : 8 ≤ L)
    {G : Set (Array 2)} (hG : MeasurableSet[enlMeas p m n] G)
    (hrec : ∀ U ∈ G, ∃ r : ℤ, RecordAt p m U n r) :
    Real.exp (-(16 - 8 * Real.log (1 - p)) * (L : ℝ)) * (arrayMeasure 2).real G ≤
      (arrayMeasure 2).real (G ∩ {U | (L : ℝ) ^ 2 + (L : ℝ) ≤
        pathDiameter (n + (4 * L + L ^ 3)) (posPath p m U)}) := by
  rw [← Nat.add_assoc]
  refine (mul_le_mul_of_nonneg_right
    (exp_neg_le_two_walker_trial_coefficient (p := p) hp₀ hp₁ (by omega)) measureReal_nonneg).trans ?_
  rw [mul_assoc]
  exact two_walker_trial_mass_ge hp₀ hp₁ hm n hL hG hrec

/-- The two-walker trial bound on any past event of an integer-valued simultaneous
record stopping time. -/
theorem two_walker_trial_at_stopping_time_mass_ge
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m)
    (S : Array 2 → ℕ) {L : ℕ} (hL : 8 ≤ L)
    {G : Set (Array 2)} (hG : ∀ n, MeasurableSet[enlMeas p m n] (G ∩ {U | S U = n}))
    (hrec : ∀ U ∈ G, ∃ r : ℤ, RecordAt p m U (S U) r) :
    Real.exp (-(16 - 8 * Real.log (1 - p)) * (L : ℝ)) * (arrayMeasure 2).real G ≤
      (arrayMeasure 2).real (G ∩ {U | (L : ℝ) ^ 2 + (L : ℝ) ≤
        pathDiameter (S U + (4 * L + L ^ 3)) (posPath p m U)}) := by
  let B (n : ℕ) := {U : Array 2 | (L : ℝ) ^ 2 + (L : ℝ) ≤
    pathDiameter (n + (4 * L + L ^ 3)) (posPath p m U)}
  refine stopped_trial_mass_ge (B := B) S (Real.exp_pos _).le
    (fun n => enlMeas_le p m n _ (hG n)) (fun n => ?_) (fun n => ?_)
  · exact ((measurable_pathDiameter (n + (4 * L + L ^ 3))).comp
      (measurable_posPath p m 2)) measurableSet_Ici
  · apply two_walker_exp_trial_mass_ge hp₀ hp₁ hm n hL (hG n)
    intro U hU
    have h := hrec U hU.1
    have hn : S U = n := hU.2
    rwa [hn] at h

end Swarming.Diameter
