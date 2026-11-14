/-
# The wide total drift-failure bound, and its record-window instantiation

`LocMoveLocalTotal.exists_measure_sep_window_dev_le_total` splits the separated drift-failure
event into the harmonic bad event `HMaxBad` and the good-window profile, but it needs
`LocMoveLocal.LeaderRange p m J L A s (s + T*L) U`, which `LeaderRangeObstruction.lean` refutes
on a record window.

This file performs the same split with the decoupled margins `M, Up`:

* `measure_sep_window_dev_le_total_wide` — the split, consuming any bound on the wide bad event;
* `exists_measure_sep_window_dev_le_total_wide` — unconditional in the harmonic input, using
  `array_locmax_bound_wide_T` with `M + Up ≤ (2*T+4)*L`, so the result reads

    `P ≤ exp(-c·L^(1/16)) + 2·(T*L+1)·exp(-(xOf L)^6/(16·T))`

  with `c > 0` independent of `T` and `L₀` allowed to depend on `T`;
* `X_le_add_run` / `X_sub_le_run` — nearest-neighbour propagation of the record bound
  (`T*L` steps move a walker by at most `T*L`);
* `record_window_pos_bounds` — the window position bounds of
  `LocLeaderObstruction.wide_of_record_window` from the start bound `R - L ≤ X s j ≤ R`
  (i.e. record defect `d_r ≤ L`);
* `exists_measure_sep_window_dev_le_record` — the instantiation: the `LeaderRangeW` premise is
  **removed**, replaced by the exact record-position bound
  `R - L ≤ X s j ≤ R` at the window start and `R ≥ L + T*L + 1`.

Everything here is a genuine consequence of the integrated `(hcomp)`/`GoodStep` profile plus the
new wide `(locmax)` bound; the only unproved probabilistic input is the exponential moment
`exists_exp_moment_hof`, which is an integrated theorem.
-/
import Swarm.WideLeader

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

/-- Split off the wide harmonic bad event: on a separated window with `LeaderRangeW`, the total
drift-failure probability is at most the wide harmonic bad-event probability plus the explicit
local profile. -/
theorem measure_sep_window_dev_le_total_wide {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty) {T L M Up A s : ℕ}
    (hT : 1 ≤ T) (hL : 1 ≤ L) :
    (arrayMeasure N).real
        {U | (∀ k ∈ Finset.Ico s (s + T * L), SepSet p m k Jᶜ J U) ∧
          LocLeaderObstruction.LeaderRangeW p m J M Up A s (s + T * L) U ∧
          Mnow p m (s + T * L) J hJ U - Mnow p m s J hJ U <
            (((T * L : ℕ) : ℝ)) - (L : ℝ) ^ (3 / 4 : ℝ)}
      ≤ (arrayMeasure N).real {U : Array N | HMaxBadW p m L M Up A U} +
        2 * (((T * L : ℕ) : ℝ) + 1) *
          Real.exp (-((xOf L) ^ 6 / (16 * (T : ℝ)))) := by
  set Bad : Set (Array N) := {U : Array N | HMaxBadW p m L M Up A U} with hBad
  set E : Set (Array N) :=
    {U | (∀ k ∈ Finset.Ico s (s + T * L), SepSet p m k Jᶜ J U) ∧
      LocLeaderObstruction.LeaderRangeW p m J M Up A s (s + T * L) U ∧
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
    have h := measure_sep_window_dev_le_of_locmax_wide_paper_scale (p := p) hp0 hp1 m J hJ
      (T := T) (L := L) (M := M) (Up := Up) (A := A) (s := s) hT hL
    exact h
  calc
    (arrayMeasure N).real E ≤ (arrayMeasure N).real (Bad ∪ (Badᶜ ∩ E)) :=
      measureReal_mono hsplit (measure_ne_top _ _)
    _ ≤ (arrayMeasure N).real Bad + (arrayMeasure N).real (Badᶜ ∩ E) :=
      measureReal_union_le _ _
    _ ≤ (arrayMeasure N).real Bad + 2 * (((T * L : ℕ) : ℝ) + 1) *
        Real.exp (-((xOf L) ^ 6 / (16 * (T : ℝ)))) := add_le_add_right hgood _

/-- The wide `(locmax)` bound turns the decomposition into one unconditional statement, with
only separation and the wide leader-range geometry remaining as hypotheses. -/
theorem exists_measure_sep_window_dev_le_total_wide {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (J : Finset (Fin N)) (hJ : J.Nonempty) {T s : ℕ}
    (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ (A M Up : ℕ),
      M ≤ A → M + Up ≤ (2 * T + 4) * L →
      (arrayMeasure N).real
          {U | (∀ k ∈ Finset.Ico s (s + T * L), SepSet p m k Jᶜ J U) ∧
            LocLeaderObstruction.LeaderRangeW p m J M Up A s (s + T * L) U ∧
            Mnow p m (s + T * L) J hJ U - Mnow p m s J hJ U <
              (((T * L : ℕ) : ℝ)) - (L : ℝ) ^ (3 / 4 : ℝ)}
        ≤ Real.exp (-c * xOf L) + 2 * (((T * L : ℕ) : ℝ) + 1) *
            Real.exp (-((xOf L) ^ 6 / (16 * (T : ℝ)))) := by
  obtain ⟨c, hc, L₀, hmax⟩ := array_locmax_bound_wide_T (N := N) (p := p) hp0 hp1 hm T hT
  refine ⟨c, hc, max L₀ 1, ?_⟩
  intro L hL A M Up hMA hMU
  have hL0 : L₀ ≤ L := le_trans (le_max_left _ _) hL
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  have hprob := hmax L hL0 A M Up hMA hMU
  have hreal : (arrayMeasure N).real {U : Array N | HMaxBadW p m L M Up A U} ≤
      Real.exp (-c * xOf L) := by
    rw [measureReal_def]
    calc
      ((arrayMeasure N) {U : Array N | HMaxBadW p m L M Up A U}).toReal ≤
          (ENNReal.ofReal (Real.exp (-c * xOf L))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hprob
      _ = Real.exp (-c * xOf L) := ENNReal.toReal_ofReal (Real.exp_pos _).le
  exact (measure_sep_window_dev_le_total_wide hp0 hp1 m J hJ hT hL1).trans
    (add_le_add_left hreal _)

/-! ### Nearest-neighbour propagation of the record-window bound -/

/-- Along `r` steps every walker rises by at most `r`. -/
theorem X_le_add_run {p : ℝ} (m : ℕ) (U : Array N) {s r : ℕ} (j : Fin N) :
    X p m U (s + r) j ≤ X p m U s j + (r : ℤ) := by
  induction r with
  | zero => simp
  | succ k ih =>
      have h1 : X p m U (s + k + 1) j ≤ X p m U (s + k) j + 1 :=
        SwarmQVariance.X_succ_le_add_one p m U (s + k) j
      rw [show s + (k + 1) = s + k + 1 by omega]
      push_cast
      omega

/-- Along `r` steps every walker falls by at most `r`. -/
theorem X_sub_le_run {p : ℝ} (m : ℕ) (U : Array N) {s r : ℕ} (j : Fin N) :
    X p m U s j - (r : ℤ) ≤ X p m U (s + r) j := by
  induction r with
  | zero => simp
  | succ k ih =>
      have h1 : X p m U (s + k) j ≤ X p m U (s + k + 1) j + 1 :=
        SwarmQVariance.X_le_succ_add_one p m U (s + k) j
      rw [show s + (k + 1) = s + k + 1 by omega]
      push_cast
      omega

/-- **Record-window position bounds.**  If at time `s` every walker of `J` is within `L` below
the record level `R`, then throughout the window `[s, s + T*L)` it stays within
`[R - L - T*L, R + T*L]` — exactly the hypothesis of
`LocLeaderObstruction.wide_of_record_window`.  Only the nearest-neighbour property of the
trajectory is used. -/
theorem record_window_pos_bounds {p : ℝ} {m : ℕ} {J : Finset (Fin N)} {U : Array N}
    {R L T s : ℕ} (hTL : 1 ≤ T * L)
    (hstart : ∀ j ∈ J, (R : ℤ) - (L : ℤ) ≤ X p m U s j ∧ X p m U s j ≤ (R : ℤ)) :
    ∀ k ∈ Finset.Ico s (s + T * L), ∀ j ∈ J,
      (R : ℤ) - (L : ℤ) - ((T * L : ℕ) : ℤ) ≤ X p m U k j ∧
        X p m U k j ≤ (R : ℤ) + ((T * L : ℕ) : ℤ) := by
  intro k hk j hj
  rw [Finset.mem_Ico] at hk
  obtain ⟨hks, hkt⟩ := hk
  set r : ℕ := k - s with hr
  have hkEq : k = s + r := by omega
  have hrTL : r + 1 ≤ T * L := by omega
  have hcast : ((r : ℕ) : ℤ) + 1 ≤ ((T * L : ℕ) : ℤ) := by exact_mod_cast hrTL
  have hb := hstart j hj
  have hup := X_le_add_run (p := p) m U (s := s) (r := r) j
  have hdown := X_sub_le_run (p := p) m U (s := s) (r := r) j
  rw [hkEq]
  constructor <;> omega

/-- **The `LeaderRangeW` premise is discharged on a record window.**

With `R ≥ L + T*L + 1` and every walker of `J` within `L` below the record level `R` at time
`s`, the separated drift-failure probability over `[s, s + T*L)` at deviation `L^(3/4)` is at
most

  `exp(-c·L^(1/16)) + 2·(T*L+1)·exp(-(xOf L)^6/(16·T))`.

The margin geometry is `M = L + 2*T*L + 2`, `Up = L`, anchor `A = R + T*L + 1`; the hypothesis
`M + Up ≤ (2*T+4)*L` becomes `2 ≤ 2*T*L`, automatic for `T ≥ 1`, `L ≥ 1`.  Separation and the
start bound `R - L ≤ X s j ≤ R` (record defect `d_r ≤ L`) remain as the only geometric
hypotheses. -/
theorem exists_measure_sep_window_dev_le_record {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (J : Finset (Fin N)) (hJ : J.Nonempty) (hJc : Jᶜ.Nonempty)
    {T s : ℕ} (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ R : ℕ, L + T * L + 1 ≤ R →
      (arrayMeasure N).real
          {U | (∀ j ∈ J, (R : ℤ) - (L : ℤ) ≤ X p m U s j ∧ X p m U s j ≤ (R : ℤ)) ∧
            (∀ k ∈ Finset.Ico s (s + T * L), SepSet p m k Jᶜ J U) ∧
            Mnow p m (s + T * L) J hJ U - Mnow p m s J hJ U <
              (((T * L : ℕ) : ℝ)) - (L : ℝ) ^ (3 / 4 : ℝ)}
        ≤ Real.exp (-c * xOf L) + 2 * (((T * L : ℕ) : ℝ) + 1) *
            Real.exp (-((xOf L) ^ 6 / (16 * (T : ℝ)))) := by
  obtain ⟨c, hc, L₀, hw⟩ := exists_measure_sep_window_dev_le_total_wide
    (N := N) (p := p) hp0 hp1 hm J hJ (s := s) hT
  refine ⟨c, hc, max L₀ 1, ?_⟩
  intro L hL R hR
  have hL0 : L₀ ≤ L := le_trans (le_max_left _ _) hL
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  have hTL : 1 ≤ T * L := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨i₀, hi₀⟩ := hJc
  -- the geometric facts for the chosen margins
  have hMA : L + 2 * T * L + 2 ≤ R + T * L + 1 := by
    have h2 : 2 * T * L = T * L + T * L := by ring
    omega
  have hMUp : (L + 2 * T * L + 2) + L ≤ (2 * T + 4) * L := by nlinarith [hL1, hT]
  -- the inclusion into the `LeaderRangeW` event
  have hsub : {U : Array N |
        (∀ j ∈ J, (R : ℤ) - (L : ℤ) ≤ X p m U s j ∧ X p m U s j ≤ (R : ℤ)) ∧
        (∀ k ∈ Finset.Ico s (s + T * L), SepSet p m k Jᶜ J U) ∧
        Mnow p m (s + T * L) J hJ U - Mnow p m s J hJ U <
          (((T * L : ℕ) : ℝ)) - (L : ℝ) ^ (3 / 4 : ℝ)} ⊆
      {U | (∀ k ∈ Finset.Ico s (s + T * L), SepSet p m k Jᶜ J U) ∧
        LocLeaderObstruction.LeaderRangeW p m J (L + 2 * T * L + 2) L (R + T * L + 1)
          s (s + T * L) U ∧
        Mnow p m (s + T * L) J hJ U - Mnow p m s J hJ U <
          (((T * L : ℕ) : ℝ)) - (L : ℝ) ^ (3 / 4 : ℝ)} := by
    rintro U ⟨hstart, hsep, hdev⟩
    exact ⟨hsep,
      LocLeaderObstruction.wide_of_record_window (p := p) (m := m) (J := J) (U := U)
        (L := L) (R := R) (s := s) (t := s + T * L) (T := T)
        (fun _ _ => ⟨i₀, hi₀⟩) hL1 hR
        (record_window_pos_bounds (p := p) (m := m) (J := J) (U := U)
          (R := R) (L := L) (T := T) (s := s) hTL hstart),
      hdev⟩
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    (hw L hL0 (R + T * L + 1) (L + 2 * T * L + 2) L hMA hMUp)

end WideRepair

namespace WideRepair

noncomputable section

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift LocMoveMart LocSumAct SwarmMarks SwarmLogRatio
open LocMoveLocal

variable {N : ℕ}

/-- `(L^(1/16))^6 = L^(3/8)`. -/
lemma xOf_pow_six (L : ℕ) : (xOf L) ^ 6 = (L : ℝ) ^ (3 / 8 : ℝ) := by
  have hL : (0 : ℝ) ≤ (L : ℝ) := by positivity
  rw [xOf, ← Real.rpow_natCast ((L : ℝ) ^ (1 / 16 : ℝ)) 6, ← Real.rpow_mul hL]
  norm_num

/-- **The record-window bound in the paper's profile form**

  `exp(-c·L^(1/16)) + 2·(T*L+1)·exp(-L^(3/8)/(16*T))`

with `c > 0` independent of `T` and of the margins.  This is
`exists_measure_sep_window_dev_le_record` with `(xOf L)^6` rewritten as `L^(3/8)`. -/
theorem exists_measure_sep_window_dev_le_record_profile {p : ℝ} (hp0 : 1 / 2 < p)
    (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) (J : Finset (Fin N)) (hJ : J.Nonempty)
    (hJc : Jᶜ.Nonempty) {T s : ℕ} (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ R : ℕ, L + T * L + 1 ≤ R →
      (arrayMeasure N).real
          {U | (∀ j ∈ J, (R : ℤ) - (L : ℤ) ≤ X p m U s j ∧ X p m U s j ≤ (R : ℤ)) ∧
            (∀ k ∈ Finset.Ico s (s + T * L), SepSet p m k Jᶜ J U) ∧
            Mnow p m (s + T * L) J hJ U - Mnow p m s J hJ U <
              (((T * L : ℕ) : ℝ)) - (L : ℝ) ^ (3 / 4 : ℝ)}
        ≤ Real.exp (-c * xOf L) + 2 * (((T * L : ℕ) : ℝ) + 1) *
            Real.exp (-((L : ℝ) ^ (3 / 8 : ℝ) / (16 * (T : ℝ)))) := by
  obtain ⟨c, hc, L₀, h⟩ := exists_measure_sep_window_dev_le_record
    (N := N) (p := p) hp0 hp1 hm J hJ hJc (T := T) (s := s) hT
  refine ⟨c, hc, L₀, ?_⟩
  intro L hL R hR
  refine (h L hL R hR).trans ?_
  rw [xOf_pow_six L]

end

end WideRepair
