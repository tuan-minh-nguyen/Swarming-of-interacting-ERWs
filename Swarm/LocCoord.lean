/-
  **(loccoord) of Proposition `local`: the deterministic spatial-harmonic inequality.**

  The paper's display `(loccoord)` is

      H_n^A(b0) - H_n^A(a0) ≤ C (b0 - a0) + C_T L^{3/4}

  for `r - (T+2)L ≤ a0 ≤ b0 ≤ R_n^A`, and its proof (main_1d_revised.tex, proof of
  Prop. `local`) is the two-line chain

      H_n^A(b0) - H_n^A(a0) = Σ_{x=a0}^{b0-1} h_n^A(x) ≤ Σ_{x=a0}^{b0-1} h_i(x)

  for `i ∈ A` with `M_n^i = R_n^A`, using `(hcomp)` `h_n^A(x) ≤ h_i(x)` on `x < M_n^i`,
  followed by the `(locsum)` bound on `Σ h_i(x)^2`.

  This file proves that chain at the **actual** model, with no probabilistic input:

  * `hfix_omegaN_eq_hof` — the bridge that the model potential `hfix (omegaN i)` of
    `SepGroup` is the mark-recursion potential `hof (siteMarks i)` used by `(locsum)`
    (`LocSumR1.array_locsum_h`).  This is what makes `(locsum)` applicable to `h_i`.
  * `HZ_sub_eq_sum` — the telescoping identity `H^w(b) - H^w(a) = Σ_{a ≤ x < b} h^w(x)`
    on the integer extension `(Hdef)`, i.e. *which* half-open interval is summed.
  * `loccoord_fixed` — `H_n^B(b0) - H_n^B(a0) ≤ ((K+1)/2)(b0-a0) + (K/2)β` from
    `Σ h_i(x)^2 ≤ K(b0-a0) + Kβ`, `hcomp_h`, and `2h ≤ h²+1`.  The constant `K` is the
    `(locsum)` constant and the remainder is `Kβ/2`; no separate Cauchy–Schwarz constant
    appears.
  * `loccoord_two_time` — the **changing-weight** form used in the proof of `(locmove)`:
    for `s ≤ t`, the average of `H_t^A(X_t^i) - H_s^A(X_s^i)` over `A` is at most
    `H_t^A(R_t^A) - H_t^A(a0)`, i.e. the earlier weight family is eliminated by `(hmono)`
    (`H_t^A ≤ H_s^A`) *before* `(loccoord)` is applied, at the single time `t`.  This is
    the step that is wrong if one treats `w_n` as a constant family in time.

  No `sorry`, no axioms beyond `propext, Classical.choice, Quot.sound`.
-/
import Swarm.SepGroup
import Swarm.MarkMoments
import Swarm.RawLogRatio

set_option linter.unusedVariables false

open Finset
open scoped BigOperators

namespace Loccoord

noncomputable section

variable {N : ℕ}

/-! ### 1. The potential bridge `h_i = hof (siteMarks i)` -/

/-- `omegaN` is the two-valued weight of the site mark, read on `ℕ`. -/
lemma omegaN_eq {p : ℝ} {m : ℕ} {U : Swarming.Uniform.Array N} (j : Fin N) (k : ℕ) :
    SepGroup.Model.omegaN p m U j k
      = if (SwarmLogRatio.siteMarks p m U j k = true) then p else 1 / 2 := by
  have h1 : SepGroup.Model.omegaN p m U j k
      = Swarming.Trajectory.omegaAt p m U j (k : ℤ) := rfl
  rw [h1, Swarming.Trajectory.omegaAt]
  by_cases h : Swarming.Trajectory.SiteMark p m U j (k : ℤ)
  · rw [if_pos h]
    rw [if_pos (by simp [SwarmLogRatio.siteMarks, h])]
  · rw [if_neg h]
    rw [if_neg (by simp [SwarmLogRatio.siteMarks, h])]

lemma omegaN_eq_true {p : ℝ} {m : ℕ} {U : Swarming.Uniform.Array N} {j : Fin N} {k : ℕ}
    (h : SwarmLogRatio.siteMarks p m U j k = true) :
    SepGroup.Model.omegaN p m U j k = p := by
  rw [omegaN_eq, if_pos h]

lemma omegaN_eq_false {p : ℝ} {m : ℕ} {U : Swarming.Uniform.Array N} {j : Fin N} {k : ℕ}
    (h : SwarmLogRatio.siteMarks p m U j k = false) :
    SepGroup.Model.omegaN p m U j k = 1 / 2 := by
  have h' : ¬ (SwarmLogRatio.siteMarks p m U j k = true) := by rw [h]; simp
  rw [omegaN_eq, if_neg h']

/-- A Boolean which is not `true` is `false`. -/
lemma bool_eq_false_of_ne_true {b : Bool} (h : ¬ b = true) : b = false := by
  cases b with
  | true => exact absurd rfl h
  | false => rfl

/-- One step at a marked site: the `hfix` recursion is the `hstep` recursion. -/
lemma step_true (p : ℝ) (hp0 : p ≠ 0) (h : ℝ) :
    (1 + (1 - p) * h) / p = SwarmMarks.hstep p true h := by
  rw [SwarmMarks.hstep_true]
  field_simp

/-- One step at an unmarked site. -/
lemma step_false (p : ℝ) (h : ℝ) :
    (1 + (1 - 1 / 2) * h) / (1 / 2) = SwarmMarks.hstep p false h := by
  rw [SwarmMarks.hstep_false]
  ring

/-- **The bridge.**  The model potential `h_i` of `SepGroup` (the `hrec` recursion driven by
`omega_i`) is the mark-recursion potential `hof` of `SwarmMarks`, driven by the site marks
`B_j(x)`.  Hence `(locsum)`, which is proved for `hof`, applies to `h_i`. -/
theorem hfix_omegaN_eq_hof {p : ℝ} (hp0 : p ≠ 0) {m : ℕ} {U : Swarming.Uniform.Array N}
    (j : Fin N) :
    ∀ x : ℕ, Cookie.hfix (SepGroup.Model.omegaN p m U j) x
      = SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x
  | 0 => by
      rw [Cookie.hfix_eq, Cookie.hprev_zero, SwarmMarks.hof_zero, omegaN_eq]
      by_cases hm : SwarmLogRatio.siteMarks p m U j 0 = true
      · rw [if_pos hm, hm, step_true p hp0]
      · rw [if_neg hm, bool_eq_false_of_ne_true (b := SwarmLogRatio.siteMarks p m U j 0) hm,
          step_false p]
  | (x + 1) => by
      rw [Cookie.hfix_eq, Cookie.hprev_succ,
        hfix_omegaN_eq_hof hp0 j x, SwarmMarks.hof_succ, omegaN_eq]
      by_cases hm : SwarmLogRatio.siteMarks p m U j (x + 1) = true
      · rw [if_pos hm, hm, step_true p hp0]
      · rw [if_neg hm,
          bool_eq_false_of_ne_true (b := SwarmLogRatio.siteMarks p m U j (x + 1)) hm,
          step_false p]

/-! ### 2. Telescoping `H^w` over the half-open interval -/

/-- `H^w(b) - H^w(a) = Σ_{a ≤ x < b} h^w(x)` for `a ≤ b` (eq. (Hdef)). -/
theorem HZ_sub_eq_sum (w : ℕ → ℝ) (a : ℕ) :
    ∀ b : ℕ, a ≤ b →
      SepGroup.HZ w (b : ℤ) - SepGroup.HZ w (a : ℤ)
        = ∑ x ∈ Finset.Ico a b, Cookie.hfix w x
  | b, hab => by
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ b hb ih =>
        have hstep : SepGroup.HZ w ((b + 1 : ℕ) : ℤ)
            = SepGroup.HZ w (b : ℤ) + Cookie.hfix w b := by
          simpa using SepGroup.HZ_add_one (w := w) (x := (b : ℤ)) (Int.natCast_nonneg b)
        rw [hstep, Finset.sum_Ico_succ_top hb]
        linarith [ih]

/-! ### 3. `(loccoord)` at a fixed time -/

/-- **Deterministic `(loccoord)` at a fixed time.**  For a group `B`, a leader `i ∈ B`
and `a0 ≤ b0 ≤ M_n^i`, if the `(locsum)` bound `Σ_{a0 ≤ x < b0} h_i(x)^2 ≤ K(b0-a0) + Kβ`
holds, then `H_n^B(b0) - H_n^B(a0) ≤ ((K+1)/2)(b0-a0) + (K/2)β`. -/
theorem loccoord_fixed {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m : ℕ}
    (U : Swarming.Uniform.Array N) {n : ℕ} {B : Finset (Fin N)} {i : Fin N} (hiB : i ∈ B)
    {a0 b0 : ℕ} (hab : a0 ≤ b0)
    (hbR : (b0 : ℤ) ≤ Swarming.Trajectory.runMax p m U i n)
    {K β : ℝ} (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (hsum : ∑ x ∈ Finset.Ico a0 b0,
        (Cookie.hfix (SepGroup.Model.omegaN p m U i) x) ^ 2
      ≤ K * ((b0 : ℝ) - (a0 : ℝ)) + K * β) :
    SepGroup.Model.HA p m U n B (b0 : ℤ) - SepGroup.Model.HA p m U n B (a0 : ℤ)
      ≤ ((K + 1) / 2) * ((b0 : ℝ) - (a0 : ℝ)) + (K / 2) * β := by
  have htel : SepGroup.Model.HA p m U n B (b0 : ℤ) - SepGroup.Model.HA p m U n B (a0 : ℤ)
      = ∑ x ∈ Finset.Ico a0 b0, Cookie.hfix (SepGroup.Model.wA p m U n B) x :=
    HZ_sub_eq_sum (SepGroup.Model.wA p m U n B) a0 b0 hab
  rw [htel]
  -- `(hcomp)`: the group potential is dominated by the leader's mark potential.
  have hle : ∀ x ∈ Finset.Ico a0 b0,
      Cookie.hfix (SepGroup.Model.wA p m U n B) x
        ≤ Cookie.hfix (SepGroup.Model.omegaN p m U i) x := by
    intro x hx
    obtain ⟨-, hxb⟩ := Finset.mem_Ico.mp hx
    have hlt : (x : ℤ) < Swarming.Trajectory.runMax p m U i n := by
      have : (x : ℤ) < (b0 : ℤ) := by exact_mod_cast hxb
      linarith
    have hJ : i ∈ (Bᶜ)ᶜ := by simpa using hiB
    have hc := SepGroup.Model.hcomp_h p m U hp hp1 (J := Bᶜ) (i := i) hJ hlt
    simpa using hc
  -- `2h ≤ h² + 1`, summed.
  have hquad : ∀ x ∈ Finset.Ico a0 b0,
      2 * Cookie.hfix (SepGroup.Model.omegaN p m U i) x
        ≤ (Cookie.hfix (SepGroup.Model.omegaN p m U i) x) ^ 2 + 1 := by
    intro x _
    nlinarith [sq_nonneg (Cookie.hfix (SepGroup.Model.omegaN p m U i) x - 1)]
  have hcard : (((Finset.Ico a0 b0).card : ℕ) : ℝ) = (b0 : ℝ) - (a0 : ℝ) := by
    rw [Nat.card_Ico]
    push_cast [Nat.cast_sub hab]
    ring
  have hsum2 : ∑ x ∈ Finset.Ico a0 b0,
      ((Cookie.hfix (SepGroup.Model.omegaN p m U i) x) ^ 2 + 1)
      = (∑ x ∈ Finset.Ico a0 b0,
          (Cookie.hfix (SepGroup.Model.omegaN p m U i) x) ^ 2) + ((b0 : ℝ) - (a0 : ℝ)) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, hcard]
  have hdouble : 2 * ∑ x ∈ Finset.Ico a0 b0,
      Cookie.hfix (SepGroup.Model.omegaN p m U i) x
      ≤ (∑ x ∈ Finset.Ico a0 b0,
          (Cookie.hfix (SepGroup.Model.omegaN p m U i) x) ^ 2) + ((b0 : ℝ) - (a0 : ℝ)) := by
    rw [← hsum2, Finset.mul_sum]
    exact Finset.sum_le_sum hquad
  have hmono := Finset.sum_le_sum hle
  linarith

/-! ### 4. Changing weights: the two-time form -/

/-- **`(loccoord)` in the two-time, changing-weight form.**  For `s ≤ t` and a group `B`,
each term `H_t^B(X_t^k) - H_s^B(X_s^k)` is bounded by the *single-time* difference
`H_t^B(b0) - H_t^B(a0)`: monotonicity of `H_t^B` in space and `(hmono)`
`H_t^B ≤ H_s^B` pointwise eliminate the earlier weight family. -/
theorem loccoord_two_time {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m : ℕ}
    (U : Swarming.Uniform.Array N) {s t : ℕ} (hst : s ≤ t)
    {B : Finset (Fin N)} {i : Fin N} (hiB : i ∈ B) {a0 b0 : ℕ} (hab : a0 ≤ b0)
    (hXa : ∀ k ∈ B, (a0 : ℤ) ≤ SepGroup.Model.X p m U s k)
    (hXb : ∀ k ∈ B, SepGroup.Model.X p m U t k ≤ (b0 : ℤ))
    (hbR : (b0 : ℤ) ≤ Swarming.Trajectory.runMax p m U i t)
    {K β : ℝ} (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (hsum : ∑ x ∈ Finset.Ico a0 b0,
        (Cookie.hfix (SepGroup.Model.omegaN p m U i) x) ^ 2
      ≤ K * ((b0 : ℝ) - (a0 : ℝ)) + K * β) :
    ∀ k ∈ B,
      SepGroup.Model.HA p m U t B (SepGroup.Model.X p m U t k)
          - SepGroup.Model.HA p m U s B (SepGroup.Model.X p m U s k)
        ≤ ((K + 1) / 2) * ((b0 : ℝ) - (a0 : ℝ)) + (K / 2) * β := by
  intro k hk
  have hmonoT : Monotone (SepGroup.HZ (SepGroup.Model.wA p m U t B)) :=
    SepGroup.HZ_mono (SepGroup.Model.wA_pos p m U hp t B)
      (SepGroup.Model.wA_le_one p m U hp1 t B)
  -- `(hmono)`: `H_t^B ≤ H_s^B` pointwise.
  have htime : SepGroup.Model.HA p m U t B (SepGroup.Model.X p m U s k)
      ≤ SepGroup.Model.HA p m U s B (SepGroup.Model.X p m U s k) := by
    have h := SepGroup.HZ_diff_nonneg (SepGroup.Model.wA_pos p m U hp s B)
      (SepGroup.Model.wA_le_one p m U hp1 s B)
      (SepGroup.Model.wA_pos p m U hp t B)
      (SepGroup.Model.wA_le_one p m U hp1 t B)
      (SepGroup.Model.wA_mono_time p m U hp hst B) (SepGroup.Model.X p m U s k)
    exact sub_nonneg.mp h
  have h1 : SepGroup.Model.HA p m U t B (SepGroup.Model.X p m U t k)
      ≤ SepGroup.Model.HA p m U t B (b0 : ℤ) := hmonoT (hXb k hk)
  have h2 : SepGroup.Model.HA p m U t B (a0 : ℤ)
      ≤ SepGroup.Model.HA p m U t B (SepGroup.Model.X p m U s k) := hmonoT (hXa k hk)
  have h3 := loccoord_fixed hp hp1 U hiB hab hbR hK hβ hsum
  linarith

/-- The average form of `loccoord_two_time`, which is the display `(loccoord)` consumed in
the proof of `(locmove)`. -/
theorem loccoord_average {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m : ℕ}
    (U : Swarming.Uniform.Array N) {s t : ℕ} (hst : s ≤ t)
    {B : Finset (Fin N)} (hB : B.Nonempty) {i : Fin N} (hiB : i ∈ B)
    {a0 b0 : ℕ} (hab : a0 ≤ b0)
    (hXa : ∀ k ∈ B, (a0 : ℤ) ≤ SepGroup.Model.X p m U s k)
    (hXb : ∀ k ∈ B, SepGroup.Model.X p m U t k ≤ (b0 : ℤ))
    (hbR : (b0 : ℤ) ≤ Swarming.Trajectory.runMax p m U i t)
    {K β : ℝ} (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (hsum : ∑ x ∈ Finset.Ico a0 b0,
        (Cookie.hfix (SepGroup.Model.omegaN p m U i) x) ^ 2
      ≤ K * ((b0 : ℝ) - (a0 : ℝ)) + K * β) :
    Swarming.Group.average B (fun k =>
        SepGroup.Model.HA p m U t B (SepGroup.Model.X p m U t k)
          - SepGroup.Model.HA p m U s B (SepGroup.Model.X p m U s k))
      ≤ ((K + 1) / 2) * ((b0 : ℝ) - (a0 : ℝ)) + (K / 2) * β := by
  set c : ℝ := ((K + 1) / 2) * ((b0 : ℝ) - (a0 : ℝ)) + (K / 2) * β with hc
  have hcard : 0 < (B.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hB
  rw [Swarming.Group.average, div_le_iff₀ hcard]
  have hsum_le : ∑ k ∈ B, (SepGroup.Model.HA p m U t B (SepGroup.Model.X p m U t k)
      - SepGroup.Model.HA p m U s B (SepGroup.Model.X p m U s k)) ≤ ∑ _k ∈ B, c :=
    Finset.sum_le_sum (loccoord_two_time hp hp1 U hst hiB hab hXa hXb hbR hK hβ hsum)
  rw [Finset.sum_const, nsmul_eq_mul] at hsum_le
  rw [mul_comm]
  exact hsum_le

end

end Loccoord
