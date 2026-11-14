/-
# Connecting `(locmax)` to the predictable local maximum profile

The only additional geometric input is `LeaderRange`: at each time, some member of the
leading group has every current or neighbouring site of the separated walkers in the harmonic
`(locmax)` window.  The bad event is exactly the one bounded by `array_locmax_bound_start`.
-/
import Swarm.LocMoveLocalScale
import Swarm.LocCoord

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace LocMoveLocal

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift LocMoveMart LocSumAct

variable {N : ℕ}

/-- The harmonic `(locmax)` bad event for every walker on the window `[A-ell,A+L)`. -/
def HMaxBad (p : ℝ) (m L A : ℕ) (U : Array N) : Prop :=
  ∃ j : Fin N, ∃ y ∈ Finset.Ico (A - ellT (xOf L)) (A + L),
    xOf L ≤ SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) y

/-- At every time, some leader has every current or neighbouring site of the separated
walkers in the harmonic window.  Only sites read by the one-step estimate are quantified. -/
def LeaderRange (p : ℝ) (m : ℕ) (J : Finset (Fin N)) (L A s t : ℕ) (U : Array N) : Prop :=
  ∀ k ∈ Finset.Ico s t, ∃ i ∈ Jᶜ, ∀ j ∈ J, ∀ z ∈
    ({X p m U k j, X p m U k j + 1, X p m U k j - 1} : Finset ℤ),
    z.toNat ∈ Finset.Ico (A - ellT (xOf L)) (A + L)

/-- If every separated walker has one lattice site of margin inside the harmonic window at
each time, then the leader-range premise follows by integer arithmetic. -/
theorem leaderRange_of_position_bounds {p : ℝ} (m : ℕ) (J : Finset (Fin N))
    {L A s t : ℕ} {U : Array N}
    (hleader : ∀ k ∈ Finset.Ico s t, ∃ i : Fin N, i ∈ Jᶜ)
    (hpos : ∀ k ∈ Finset.Ico s t, ∀ j ∈ J,
      ((A - ellT (xOf L) : ℕ) : ℤ) + 1 ≤ X p m U k j ∧
        X p m U k j + 1 < ((A + L : ℕ) : ℤ)) :
    LeaderRange p m J L A s t U := by
  intro k hk
  obtain ⟨i, hi⟩ := hleader k hk
  refine ⟨i, hi, ?_⟩
  intro j hj z hz
  have hb := hpos k hk j hj
  have hzmem : z = X p m U k j ∨ z = X p m U k j + 1 ∨ z = X p m U k j - 1 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hz
  have hzlower : ((A - ellT (xOf L) : ℕ) : ℤ) ≤ z := by
    rcases hzmem with rfl | rfl | rfl <;> omega
  have hzupper : z < ((A + L : ℕ) : ℤ) := by
    rcases hzmem with rfl | rfl | rfl <;> omega
  have hz0 : 0 ≤ z := by
    have h0 : (0 : ℤ) ≤ ((A - ellT (xOf L) : ℕ) : ℤ) := by positivity
    omega
  rw [Finset.mem_Ico]
  have hlow : (((A - ellT (xOf L) : ℕ) : ℤ).toNat) ≤ z.toNat :=
    Int.toNat_le_toNat hzlower
  rw [Int.toNat_natCast] at hlow
  exact ⟨hlow, (Int.toNat_lt hz0).2 hzupper⟩

/-- Outside `HMaxBad`, separation and `LeaderRange` imply every local good-step event. -/
theorem goodSteps_of_locmax {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty) {L A s t : ℕ} {U : Array N}
    (hU : U ∉ {U : Array N | HMaxBad p m L A U})
    (hsep : ∀ k ∈ Finset.Ico s t, SepSet p m k Jᶜ J U)
    (hRange : LeaderRange p m J L A s t U) :
    ∀ k ∈ Finset.Ico s t, U ∈ {U : Array N | GoodStep p m k J (xOf L) U} := by
  intro k hk
  obtain ⟨i, hi, hmem⟩ := hRange k hk
  apply goodStep_of_sep_of_leader_bound hp0.le hp1.le hJ hi (hsep k hk)
  intro j hj z hz
  rw [Loccoord.hfix_omegaN_eq_hof (p := p) (m := m) (U := U) (by linarith) i z.toNat]
  exact le_of_not_ge (fun hbad => hU ⟨i, z.toNat, hmem j hj z hz, hbad⟩)

/-- On the complement of the harmonic bad event, a separated drift failure with the explicit
leader-range geometry inherits the non-vacuous local profile. -/
theorem measure_sep_window_dev_le_of_locmax {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty) {L A s t : ℕ}
    (hL : 1 ≤ L) (hst : s ≤ t) (hK : 1 ≤ t - s) {ε : ℝ} (hε : 0 < ε)
    (hεB : ε ≤ 4 * ((t - s : ℕ) : ℝ) * xOf L) :
    (arrayMeasure N).real
        {U | U ∉ {U : Array N | HMaxBad p m L A U} ∧
          (∀ k ∈ Finset.Ico s t, SepSet p m k Jᶜ J U) ∧
          LeaderRange p m J L A s t U ∧
          Mnow p m t J hJ U - Mnow p m s J hJ U < ((t - s : ℕ) : ℝ) - ε}
      ≤ 2 * (((t - s : ℕ) : ℝ) + 1) *
          Real.exp (-(ε ^ 2) / (4 * ((t - s : ℕ) : ℝ) * (2 * xOf L) ^ 2)) := by
  have hB : 0 < xOf L := lt_of_lt_of_le zero_lt_one (one_le_xOf hL)
  have hsub : {U : Array N | U ∉ {U : Array N | HMaxBad p m L A U} ∧
        (∀ k ∈ Finset.Ico s t, SepSet p m k Jᶜ J U) ∧
        LeaderRange p m J L A s t U ∧
        Mnow p m t J hJ U - Mnow p m s J hJ U < ((t - s : ℕ) : ℝ) - ε} ⊆
      {U : Array N | (∀ k ∈ Finset.Ico s t, U ∈ {U : Array N | GoodStep p m k J (xOf L) U}) ∧
        Mnow p m t J hJ U - Mnow p m s J hJ U < ((t - s : ℕ) : ℝ) - ε} := by
    intro U hU
    exact ⟨goodSteps_of_locmax hp0 hp1 m J hJ hU.1 hU.2.1 hU.2.2.1, hU.2.2.2⟩
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    (measure_good_window_dev_le hp0 hp1 m J hJ hB hst hK hε hεB)

/-- At the paper's scale, the good separated literal-maximum drift failure has exponential
rate `L^(3/8)/(16T)` on a horizon `TL`. -/
theorem measure_sep_window_dev_le_of_locmax_paper_scale {p : ℝ}
    (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty)
    {T L A s : ℕ} (hT : 1 ≤ T) (hL : 1 ≤ L) :
    (arrayMeasure N).real
        {U | U ∉ {U : Array N | HMaxBad p m L A U} ∧
          (∀ k ∈ Finset.Ico s (s + T * L), SepSet p m k Jᶜ J U) ∧
          LeaderRange p m J L A s (s + T * L) U ∧
          Mnow p m (s + T * L) J hJ U - Mnow p m s J hJ U <
            (((T * L : ℕ) : ℝ)) - (L : ℝ) ^ (3 / 4 : ℝ)}
      ≤ 2 * (((T * L : ℕ) : ℝ) + 1) *
          Real.exp (-((xOf L) ^ 6 / (16 * (T : ℝ)))) := by
  have hst : s ≤ s + T * L := Nat.le_add_right _ _
  have hKnat : 1 ≤ T * L := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by omega))
  have hK : 1 ≤ (s + T * L) - s := by simpa using hKnat
  have hLr : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL)
  have hside : (L : ℝ) ^ (3 / 4 : ℝ) ≤
      4 * (((s + T * L - s : ℕ) : ℝ)) * xOf L := by
    simpa using paper_side_condition hT hL
  have hmain := measure_sep_window_dev_le_of_locmax (p := p) hp0 hp1 m J hJ
    (L := L) (A := A) (s := s) (t := s + T * L) hL hst hK
    (Real.rpow_pos_of_pos hLr _) hside
  have hsub : s + T * L - s = T * L := by omega
  rw [hsub] at hmain
  rw [paper_exponent_eq hT hL] at hmain
  exact hmain

end LocMoveLocal
