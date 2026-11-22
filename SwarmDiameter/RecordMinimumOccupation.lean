import SwarmDiameter.MinimumOccupationTest
import SwarmDiameter.RecordWeightedMartingale
import SwarmDiameter.SparseSets
import Swarm.DeepExc
import Swarm.PaperBlock

open Finset Filter MeasureTheory Set
open Swarming.Uniform Swarming.Model Swarming.Trajectory Swarming.Transition
open SwarmRecordMeas.Actual PaperBlock Loccoord
open scoped Topology

namespace Swarming.Diameter

set_option autoImplicit false

variable {N : ℕ} [Nonempty (Fin N)]

/-- Failure of the occupation bound on an interval throughout which a
walker in `J` attains the nonnegative swarm minimum. -/
def recordMinimumOccupationBad (p : ℝ) (m r L T : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty)
    (S : Finset ℤ) (b : ℝ) : Set (Array N) :=
  RecClockLG.recordCarrier p m r L ∩ {U |
    ∃ s t : ℕ, recTimeA p m U r ≤ s ∧ s ≤ t ∧ t ≤ recTimeA p m U r + T * L ∧
      (∀ u ∈ Finset.Ico s t,
        Xmin p m U J hJ u = RecordDefect.runMin (Xa p m U) u ∧ 0 ≤ Xmin p m U J hJ u) ∧
      b < ∑ u ∈ Finset.Ico s t, (if Xmin p m U J hJ u ∈ S then (1 : ℝ) else 0)}

/-- Uniform exponential bound for occupation of any fixed finite set
by the minimum of a group attaining the swarm minimum. -/
theorem record_minimum_occupation_failure_le_exp
    {p : ℝ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) {m : ℕ} (hmN : m < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℕ, 1 ≤ T → ∀ {ε : ℝ}, 0 < ε →
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ L : ℕ in atTop, ∀ (r : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty)
        (S : Finset ℤ), (arrayMeasure N).real
          (recordMinimumOccupationBad p m r L T J hJ S (C * (S.card : ℝ) + ε * (L : ℝ)))
            ≤ Real.exp (-c * (L : ℝ)) := by
  have hN := Fintype.card_pos (α := Fin N)
  rw [Fintype.card_fin] at hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let a := 1 + (p - 1 / 2) / (N : ℝ)
  have ha : 1 < a := by
    have h := div_pos (show (0 : ℝ) < p - 1 / 2 by linarith) hNr
    dsimp only [a]
    linarith only [h]
  have ha₀ := zero_lt_one.trans ha
  have hinv := (inv_lt_one₀ ha₀).mpr ha
  let B := (a - a⁻¹) / 2 * (1 - a⁻¹)⁻¹
  have hB : 0 < B := mul_pos (div_pos (by linarith only [ha, hinv]) (by norm_num))
    (inv_pos.mpr (sub_pos.mpr hinv))
  let d := 1 - (a + a⁻¹) / 2 + (p - 1 / 2) / (N : ℝ) * (a - a⁻¹)
  have hd : 0 < d := minimumOccupation_tilt_drift_pos hp₀ hN
  let e := d / ((N : ℝ) + 1)
  have he : 0 < e := by dsimp only [e]; positivity
  refine ⟨e⁻¹, inv_pos.mpr he, ?_⟩
  intro T hT ε hε
  obtain ⟨c, hc, hprob⟩ := record_weighted_jump_failure_le_exp (N := N) hp₀ hp₁ m T hT hB (mul_pos he hε)
  refine ⟨c, hc, ?_⟩
  filter_upwards [hprob] with L hL
  intro r J hJ S
  let f (n : ℕ) (i : Fin N) (U : Array N) :=
    minimumOccupationCoeff a J S (fun j => (trajectory p m U n).pos j) i
  have hf (n : ℕ) (i : Fin N) : Measurable[Swarming.Enl.enlFilt p m n] (f n i) := by
    have hX : Measurable[Swarming.Enl.enlFilt p m n]
        (fun U : Array N => fun j : Fin N => (trajectory p m U n).pos j) := by
      let _ : MeasurableSpace (Array N) := Swarming.Enl.enlFilt (N := N) p m n
      exact measurable_pi_lambda _ (fun j => Swarming.Enl.enl_pos_measurable p m n le_rfl j)
    exact (measurable_of_countable (fun x : Fin N → ℤ => minimumOccupationCoeff a J S x i)).comp hX
  have hfB (n : ℕ) (i : Fin N) (U : Array N) : |f n i U| ≤ B :=
    abs_minimumOccupationCoeff_le ha J S _ i
  refine (measureReal_mono ?_).trans (hL r f hf hfB)
  rintro U ⟨hU, s, t, hs, hst, ht, hcond, hbad⟩
  let X (u : ℕ) (i : Fin N) := (trajectory p m U u).pos i
  let V (u : ℕ) := minimumOccupationTest a J S (X u)
  have hstep (u : ℕ) (hu : u ∈ Finset.Ico s t) : V (u + 1) - V u ≤
      weightedJump p m f u U - e * (if Xmin p m U J hJ u ∈ S then 1 else 0) := by
    obtain ⟨i, hi, hx⟩ := Finset.exists_mem_eq_inf' hJ (X u)
    change Xmin p m U J hJ u = X u i at hx
    have hm₀ : 0 ≤ X u i := hx ▸ (hcond u hu).2
    have hmi (j : Fin N) : X u i ≤ X u j :=
      (hx.symm.trans (hcond u hu).1).le.trans (RecordDefect.runMin_le (X := Xa p m U) u j)
    have hex := excited_of_isMin p m U u i hm₀ rfl hmi (show m ≤ N - 1 by omega)
    have hα (j : Fin N) : (1 : ℝ) / 2 ≤ SwarmCross.alphaFun p m u j U := by
      unfold SwarmCross.alphaFun currentAlpha rightProbability
      split <;> linarith
    have hαi : SwarmCross.alphaFun p m u i U = p := by
      unfold SwarmCross.alphaFun currentAlpha rightProbability
      exact if_pos hex
    have hjump (j : Fin N) : X (u + 1) j = X u j + 1 ∨ X (u + 1) j = X u j - 1 := by
      rcases ExcOcc.traj_step p m U j u with h | h
      · exact Or.inl h
      · exact Or.inr h
    rw [hx]
    exact minimumOccupationTest_sub_le ha hp₀.le hi S (fun j _ => hmi j) hjump hα hαi hd.le
  have hsum := Finset.sum_le_sum (s := Finset.Ico s t) hstep
  rw [Finset.sum_Ico_sub V hst, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  have hVs : V s ≤ (S.card : ℝ) := (minimumOccupationTest_bounds ha₀ J S (X s)).2
  have hVt : 0 ≤ V t := (minimumOccupationTest_bounds ha₀ J S (X t)).1
  have hscale := mul_lt_mul_of_pos_left hbad he
  rw [mul_add, ← mul_assoc, mul_inv_cancel₀ he.ne', one_mul, ← mul_assoc] at hscale
  refine ⟨hU, s, t, hs, hst, ht, ?_⟩
  exact (by linarith only [hsum, hVs, hVt, hscale] :
    e * ε * (L : ℝ) ≤ ∑ u ∈ Finset.Ico s t, weightedJump p m f u U).trans (le_abs_self _)

/-- Exponential occupation bound simultaneously for all sufficiently small
subsets of a deterministic finite set. The selected subset may depend on
the entire array. -/
theorem record_small_set_minimum_occupation_failure_le_exp
    {p : ℝ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) {m : ℕ} (hmN : m < N)
    (T : ℕ) (hT : 1 ≤ T) {D ε : ℝ} (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧ ∀ᶠ L : ℕ in atTop,
      ∀ (r : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty) (I : Finset ℤ),
        (I.card : ℝ) ≤ D * (L : ℝ) →
        (arrayMeasure N).real (⋃ S ∈ (I.powerset.filter fun S => (S.card : ℝ) ≤ δ * (L : ℝ)),
          recordMinimumOccupationBad p m r L T J hJ S (ε * (L : ℝ))) ≤ Real.exp (-c * (L : ℝ)) := by
  obtain ⟨C, hC, h⟩ := record_minimum_occupation_failure_le_exp hp₀ hp₁ hmN
  obtain ⟨c, hc, hp⟩ := h T hT (half_pos hε)
  obtain ⟨δ, hδ, hcnt⟩ := exists_small_subsets_card_le hD hc
  let e := min δ (ε / (2 * C))
  have he : 0 < e := lt_min hδ (div_pos hε (by positivity))
  refine ⟨e, c / 2, he, half_pos hc, ?_⟩
  filter_upwards [hp] with L hL
  intro r J hJ I hI
  let F := I.powerset.filter fun S => (S.card : ℝ) ≤ e * (L : ℝ)
  have hcard : (F.card : ℝ) ≤ Real.exp (c / 2 * (L : ℝ)) :=
    (by
      exact_mod_cast Finset.card_le_card (show F ⊆
          I.powerset.filter (fun S => (S.card : ℝ) ≤ δ * (L : ℝ)) from fun S hS =>
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hS).1, (Finset.mem_filter.mp hS).2.trans
          (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))⟩)
      : (F.card : ℝ) ≤ _).trans (hcnt I (Nat.cast_nonneg _) hI)
  have hb (S : Finset ℤ) (hS : S ∈ F) :
      (arrayMeasure N).real (recordMinimumOccupationBad p m r L T J hJ S (ε * (L : ℝ))) ≤
        Real.exp (-c * (L : ℝ)) := by
    have hcardS := (Finset.mem_filter.mp hS).2
    have hsmall : C * e ≤ ε / 2 := by
      have he' : e ≤ (ε / 2) / C := by
        simpa only [div_div] using min_le_right δ (ε / (2 * C))
      simpa only [mul_comm C] using (le_div_iff₀ hC).mp he'
    have hthreshold : C * (S.card : ℝ) + (ε / 2) * (L : ℝ) ≤ ε * (L : ℝ) := by
      have h₁ := mul_le_mul_of_nonneg_left hcardS hC.le
      have h₂ := mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg L)
      nlinarith only [h₁, h₂]
    refine (measureReal_mono ?_).trans (hL r J hJ S)
    rintro U ⟨hU, s, t, hs, hst, ht, hcond, hbad⟩
    exact ⟨hU, s, t, hs, hst, ht, hcond, hthreshold.trans_lt hbad⟩
  calc
    _ ≤ ∑ S ∈ F, (arrayMeasure N).real (recordMinimumOccupationBad p m r L T J hJ S (ε * (L : ℝ))) :=
      measureReal_biUnion_finset_le F _
    _ ≤ ∑ _S ∈ F, Real.exp (-c * (L : ℝ)) := Finset.sum_le_sum hb
    _ = (F.card : ℝ) * Real.exp (-c * (L : ℝ)) := by simp
    _ ≤ Real.exp (c / 2 * (L : ℝ)) * Real.exp (-c * (L : ℝ)) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Swarming.Diameter
