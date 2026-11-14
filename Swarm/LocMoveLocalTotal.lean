import Swarm.LocMoveLocalWindow
import Swarm.LocStartRange

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace LocMoveLocal

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift LocMoveMart LocSumAct

variable {N : ℕ}

/-- Split off `HMaxBad`: on a separated window with `LeaderRange`, the total drift-failure
probability is the harmonic bad-event probability plus the explicit local profile. -/
theorem measure_sep_window_dev_le_total {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty) {T L A s : ℕ}
    (hT : 1 ≤ T) (hL : 1 ≤ L) :
    (arrayMeasure N).real
        {U | (∀ k ∈ Finset.Ico s (s + T * L), SepSet p m k Jᶜ J U) ∧
          LeaderRange p m J L A s (s + T * L) U ∧
          Mnow p m (s + T * L) J hJ U - Mnow p m s J hJ U <
            (((T * L : ℕ) : ℝ)) - (L : ℝ) ^ (3 / 4 : ℝ)}
      ≤ (arrayMeasure N).real {U : Array N | HMaxBad p m L A U} +
        2 * (((T * L : ℕ) : ℝ) + 1) *
          Real.exp (-((xOf L) ^ 6 / (16 * (T : ℝ)))) := by
  set Bad : Set (Array N) := {U : Array N | HMaxBad p m L A U} with hBad
  set E : Set (Array N) :=
    {U | (∀ k ∈ Finset.Ico s (s + T * L), SepSet p m k Jᶜ J U) ∧
      LeaderRange p m J L A s (s + T * L) U ∧
      Mnow p m (s + T * L) J hJ U - Mnow p m s J hJ U <
        (((T * L : ℕ) : ℝ)) - (L : ℝ) ^ (3 / 4 : ℝ)} with hE
  have hsplit : E ⊆ Bad ∪ (Badᶜ ∩ E) := by
    intro U hU
    by_cases hbad : U ∈ Bad
    · exact Or.inl hbad
    · exact Or.inr ⟨hbad, hU⟩
  have hgood : (arrayMeasure N).real (Badᶜ ∩ E) ≤
      2 * (((T * L : ℕ) : ℝ) + 1) *
        Real.exp (-((xOf L) ^ 6 / (16 * (T : ℝ)))) := by
    have h := measure_sep_window_dev_le_of_locmax_paper_scale (p := p) hp0 hp1 m J hJ
      (T := T) (L := L) (A := A) (s := s) hT hL
    exact h
  calc
    (arrayMeasure N).real E ≤ (arrayMeasure N).real (Bad ∪ (Badᶜ ∩ E)) :=
      measureReal_mono hsplit (measure_ne_top _ _)
    _ ≤ (arrayMeasure N).real Bad + (arrayMeasure N).real (Badᶜ ∩ E) :=
      measureReal_union_le _ _
    _ ≤ (arrayMeasure N).real Bad + 2 * (((T * L : ℕ) : ℝ) + 1) *
        Real.exp (-((xOf L) ^ 6 / (16 * (T : ℝ)))) := add_le_add_right hgood _

/-- The start-range `(locmax)` estimate turns the decomposition into one unconditional
probabilistic statement, with only separation and the named leader-range geometry remaining. -/
theorem exists_measure_sep_window_dev_le_total {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (J : Finset (Fin N)) (hJ : J.Nonempty) {T s : ℕ}
    (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ A : ℕ,
      ellT (xOf L) ≤ A →
      (arrayMeasure N).real
          {U | (∀ k ∈ Finset.Ico s (s + T * L), SepSet p m k Jᶜ J U) ∧
            LeaderRange p m J L A s (s + T * L) U ∧
            Mnow p m (s + T * L) J hJ U - Mnow p m s J hJ U <
              (((T * L : ℕ) : ℝ)) - (L : ℝ) ^ (3 / 4 : ℝ)}
        ≤ Real.exp (-c * xOf L) + 2 * (((T * L : ℕ) : ℝ) + 1) *
            Real.exp (-((xOf L) ^ 6 / (16 * (T : ℝ)))) := by
  obtain ⟨c, hc, L₀, hmax⟩ := LocSumR1.array_locmax_bound_start (N := N) hp0 hp1 hm
  refine ⟨c, hc, max L₀ 1, ?_⟩
  intro L hL A hA
  have hL0 : L₀ ≤ L := le_trans (le_max_left _ _) hL
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  have hprob := hmax L hL0 A hA
  have hreal : (arrayMeasure N).real {U : Array N | HMaxBad p m L A U} ≤
      Real.exp (-c * xOf L) := by
    rw [measureReal_def]
    calc
      ((arrayMeasure N) {U : Array N | HMaxBad p m L A U}).toReal ≤
          (ENNReal.ofReal (Real.exp (-c * xOf L))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hprob
      _ = Real.exp (-c * xOf L) := ENNReal.toReal_ofReal (Real.exp_pos _).le
  exact (measure_sep_window_dev_le_total hp0 hp1 m J hJ hT hL1).trans
    (add_le_add_left hreal _)

end LocMoveLocal
