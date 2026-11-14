/-
# The wide leader range: local good steps and the wide local drift-failure profile

`LocMoveLocalWindow.lean` couples the harmonic window to the scale parameter `L` through
`HMaxBad` / `LeaderRange`, and `LeaderRangeObstruction.lean` shows that `LeaderRange` is not
instantiable on a record window of length `T*L`.

This file re-runs the same two-step reduction against the decoupled window

* `LeaderRangeW p m J M Up A s t U` (`LocLeaderObstruction`, margins `M` below and `Up` above,
  anchor `A`) and
* `HMaxBadW p m L M Up A U` (`WideLocMax`, harmonic level `xOf L`, same window),

and proves, with exactly the same `GoodStep` / `hcomp` machinery and only the current and
neighbouring positions:

* `goodSteps_of_locmax_wide`: off the wide harmonic bad event, separation plus `LeaderRangeW`
  gives every local good-step event at level `xOf L`;
* `measure_sep_window_dev_le_of_locmax_wide` and `…_paper_scale`: the separated drift-failure
  bound `2*(K+1)*exp(-ε²/(4*K*(2*B)²))` is unchanged — nothing in the martingale profile
  depends on how the harmonic window was chosen — and at `ε = L^(3/4)`, `K = T*L` it reads
  `2*(T*L+1)*exp(-(xOf L)^6/(16*T))`.

No geometric premise is discharged here; that is `WideTotal.lean`.
-/
import Swarm.WideLocMax
import Swarm.LocMoveLocalTotal

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace WideRepair

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift LocMoveMart LocSumAct
open LocMoveLocal

variable {N : ℕ}

/-- At the narrow margins `M = ⌈L^(1/16)⌉`, `Up = L` the wide bad event is the old one. -/
theorem hMaxBadW_narrow (p : ℝ) (m L A : ℕ) (U : Array N) :
    HMaxBadW p m L (ellT (xOf L)) L A U ↔ HMaxBad p m L A U :=
  Iff.rfl

/-- Off the wide harmonic bad event, separation and the wide leader range imply every local
good-step event.  Only the current and neighbouring positions are read, exactly as in
`LocMoveLocal.goodSteps_of_locmax`. -/
theorem goodSteps_of_locmax_wide {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty) {L M Up A s t : ℕ} {U : Array N}
    (hU : U ∉ {U : Array N | HMaxBadW p m L M Up A U})
    (hsep : ∀ k ∈ Finset.Ico s t, SepSet p m k Jᶜ J U)
    (hRange : LocLeaderObstruction.LeaderRangeW p m J M Up A s t U) :
    ∀ k ∈ Finset.Ico s t, U ∈ {U : Array N | GoodStep p m k J (xOf L) U} := by
  intro k hk
  obtain ⟨i, hi, hmem⟩ := hRange k hk
  apply goodStep_of_sep_of_leader_bound hp0.le hp1.le hJ hi (hsep k hk)
  intro j hj z hz
  rw [Loccoord.hfix_omegaN_eq_hof (p := p) (m := m) (U := U) (by linarith) i z.toNat]
  exact le_of_not_ge (fun hbad => hU ⟨i, z.toNat, hmem j hj z hz, hbad⟩)

/-- On the complement of the wide harmonic bad event, a separated drift failure with the wide
leader-range geometry inherits the non-vacuous local profile.  Identical bound to
`LocMoveLocal.measure_sep_window_dev_le_of_locmax`, with the margins decoupled. -/
theorem measure_sep_window_dev_le_of_locmax_wide {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty) {L M Up A s t : ℕ}
    (hL : 1 ≤ L) (hst : s ≤ t) (hK : 1 ≤ t - s) {ε : ℝ} (hε : 0 < ε)
    (hεB : ε ≤ 4 * ((t - s : ℕ) : ℝ) * xOf L) :
    (arrayMeasure N).real
        {U | U ∉ {U : Array N | HMaxBadW p m L M Up A U} ∧
          (∀ k ∈ Finset.Ico s t, SepSet p m k Jᶜ J U) ∧
          LocLeaderObstruction.LeaderRangeW p m J M Up A s t U ∧
          Mnow p m t J hJ U - Mnow p m s J hJ U < ((t - s : ℕ) : ℝ) - ε}
      ≤ 2 * (((t - s : ℕ) : ℝ) + 1) *
          Real.exp (-(ε ^ 2) / (4 * ((t - s : ℕ) : ℝ) * (2 * xOf L) ^ 2)) := by
  have hB : 0 < xOf L := lt_of_lt_of_le zero_lt_one (one_le_xOf hL)
  have hsub : {U : Array N | U ∉ {U : Array N | HMaxBadW p m L M Up A U} ∧
        (∀ k ∈ Finset.Ico s t, SepSet p m k Jᶜ J U) ∧
        LocLeaderObstruction.LeaderRangeW p m J M Up A s t U ∧
        Mnow p m t J hJ U - Mnow p m s J hJ U < ((t - s : ℕ) : ℝ) - ε} ⊆
      {U : Array N | (∀ k ∈ Finset.Ico s t, U ∈ {U : Array N | GoodStep p m k J (xOf L) U}) ∧
        Mnow p m t J hJ U - Mnow p m s J hJ U < ((t - s : ℕ) : ℝ) - ε} := by
    intro U hU
    exact ⟨goodSteps_of_locmax_wide hp0 hp1 m J hJ hU.1 hU.2.1 hU.2.2.1, hU.2.2.2⟩
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    (measure_good_window_dev_le hp0 hp1 m J hJ hB hst hK hε hεB)

/-- At the paper's scale `ε = L^(3/4)`, `K = T*L`, the wide separated drift-failure bound has
rate `(xOf L)^6/(16*T)`. -/
theorem measure_sep_window_dev_le_of_locmax_wide_paper_scale {p : ℝ}
    (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty)
    {T L M Up A s : ℕ} (hT : 1 ≤ T) (hL : 1 ≤ L) :
    (arrayMeasure N).real
        {U | U ∉ {U : Array N | HMaxBadW p m L M Up A U} ∧
          (∀ k ∈ Finset.Ico s (s + T * L), SepSet p m k Jᶜ J U) ∧
          LocLeaderObstruction.LeaderRangeW p m J M Up A s (s + T * L) U ∧
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
  have hmain := measure_sep_window_dev_le_of_locmax_wide (p := p) hp0 hp1 m J hJ
    (L := L) (M := M) (Up := Up) (A := A) (s := s) (t := s + T * L) hL hst hK
    (Real.rpow_pos_of_pos hLr _) hside
  have hsub : s + T * L - s = T * L := by omega
  rw [hsub] at hmain
  rw [paper_exponent_eq hT hL] at hmain
  exact hmain

end WideRepair
