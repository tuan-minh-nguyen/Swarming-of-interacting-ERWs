/-
  **The static potential `hfix (omegaN)` is controlled by the longest run of unmarked sites.**

  This is the deterministic half of `(Mpot)` for `Swarm/QVarBound.lean`:
  `windowMax p m n i U = max_{u<n+2} hfix (omegaN p m U i) u`, and the two-valued weight
  `omegaN = (fun u => if SiteMark then p else 1/2)` makes `hfix` increase by exactly `2` at an
  unmarked site and contract by the factor `(1-p)/p < 1` at a marked one.  Hence

      `hfix w u ≤ (2p/(2p-1)) * (1 + L)`

  whenever every window of `L` consecutive sites inside `[0,u]` contains a marked site.

  Nothing here is probabilistic.
-/
import Swarm.QVarBound
import Swarm.BridgeReveal

set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace SwarmMpot

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmQVariance

variable {N : ℕ} {p : ℝ} {m : ℕ}

/-! ### 0. The elementary constants -/

theorem half_lt_one_div {p : ℝ} (hp : 1 / 2 < p) : (1 : ℝ) / p ≤ 2 := by
  rw [div_le_iff₀ (by linarith)]
  linarith

theorem two_p_sub_one_pos {p : ℝ} (hp : 1 / 2 < p) : (0 : ℝ) < 2 * p - 1 := by linarith

/-- `2 ≤ 2p/(2p-1)`. -/
theorem two_le_K {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) :
    (2 : ℝ) ≤ 2 * p / (2 * p - 1) := by
  rw [le_div_iff₀ (two_p_sub_one_pos hp)]
  linarith

/-- `(2-p)/p ≤ 3`. -/
theorem start_coef_le {p : ℝ} (hp : 1 / 2 < p) : (2 - p) / p ≤ 3 := by
  rw [div_le_iff₀ (by linarith : (0:ℝ) < p)]
  linarith

/-- `(2-p)/p ≤ (2p/(2p-1)) (1+L)` for every `L ≥ 1`. -/
theorem start_bound {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) {L : ℕ} (hL : 1 ≤ L) :
    (2 - p) / p ≤ (2 * p / (2 * p - 1)) * (1 + (L : ℝ)) := by
  have hK := two_le_K hp hp1
  have hLpos : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have h1 := start_coef_le hp
  have h2 : (2 : ℝ) * (1 + (L : ℝ)) ≤ (2 * p / (2 * p - 1)) * (1 + (L : ℝ)) :=
    mul_le_mul_of_nonneg_right hK (by linarith)
  nlinarith

/-- `(2-p)/p + 2(L-1) ≤ (2p/(2p-1)) (1+L)` for every `L ≥ 1`. -/
theorem run_start_bound {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) {L : ℕ} (hL : 1 ≤ L) :
    (2 - p) / p + 2 * ((L : ℝ) - 1) ≤ (2 * p / (2 * p - 1)) * (1 + (L : ℝ)) := by
  have hK := two_le_K hp hp1
  have hLpos : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have h1 := start_coef_le hp
  have h2 : (2 : ℝ) * (1 + (L : ℝ)) ≤ (2 * p / (2 * p - 1)) * (1 + (L : ℝ)) :=
    mul_le_mul_of_nonneg_right hK (by linarith)
  nlinarith

/-- `1/p + 2(L-1) ≤ (2p/(2p-1)) (1+L)`, the step paid after a marked site. -/
theorem step_bound {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) (L : ℕ) :
    1 / p + 2 * ((L : ℝ) - 1) ≤ (2 * p / (2 * p - 1)) * (1 + (L : ℝ)) := by
  have hK := two_le_K hp hp1
  have hinv := half_lt_one_div hp
  have hL : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have h2 : (2 : ℝ) * (1 + (L : ℝ)) ≤ (2 * p / (2 * p - 1)) * (1 + (L : ℝ)) :=
    mul_le_mul_of_nonneg_right hK (by linarith)
  nlinarith

/-! ### 1. One-step recursions of `hfix` at a two-valued weight -/

theorem hfix_succ_of_eq_mark {w : ℕ → ℝ} {p : ℝ} (hp0 : p ≠ 0) {n : ℕ} (h : w (n + 1) = p) :
    hfix w (n + 1) = 1 / p + ((1 - p) / p) * hfix w n := by
  rw [Cookie.hfix_eq, Cookie.hprev_succ, h]
  field_simp

theorem hfix_succ_of_eq_half {w : ℕ → ℝ} {n : ℕ} (h : w (n + 1) = 1 / 2) :
    hfix w (n + 1) = hfix w n + 2 := by
  rw [Cookie.hfix_eq, Cookie.hprev_succ, h]
  field_simp
  ring

theorem hfix_zero_of_eq_mark {w : ℕ → ℝ} {p : ℝ} (hp0 : p ≠ 0) (h : w 0 = p) :
    hfix w 0 = (2 - p) / p := by
  rw [Cookie.hfix_eq, Cookie.hprev_zero, h]
  field_simp
  ring

theorem hfix_zero_of_eq_half {w : ℕ → ℝ} (h : w 0 = 1 / 2) : hfix w 0 = 3 := by
  rw [Cookie.hfix_eq, Cookie.hprev_zero, h]
  norm_num

/-! ### 2. A run of consecutive unmarked sites adds exactly `2` per site -/

theorem hfix_add_two_mul {w : ℕ → ℝ} {j u : ℕ} (hju : j ≤ u)
    (h : ∀ x, j < x → x ≤ u → w x = 1 / 2) :
    hfix w u = hfix w j + 2 * ((u - j : ℕ) : ℝ) := by
  induction u, hju using Nat.le_induction with
  | base => norm_num
  | succ v hjv ih =>
      have hwv : w (v + 1) = 1 / 2 := h (v + 1) (by omega) (by omega)
      have ih' : hfix w v = hfix w j + 2 * ((v - j : ℕ) : ℝ) :=
        ih (fun x hx hxv => h x hx (by omega))
      rw [hfix_succ_of_eq_half hwv, ih']
      have hcast : ((v + 1 - j : ℕ) : ℝ) = ((v - j : ℕ) : ℝ) + 1 := by
        push_cast [Nat.succ_sub hjv]
        ring
      rw [hcast]
      ring

/-! ### 3. The main deterministic run bound -/

/-- **The run bound.**  If every window of `L ≥ 1` consecutive sites inside `[0,u]` contains a
site carrying weight `p`, then `hfix w u ≤ (2p/(2p-1)) (1+L)`. -/
theorem hfix_le_of_no_long_run {w : ℕ → ℝ} {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1)
    (hw : ∀ u, w u = p ∨ w u = 1 / 2) :
    ∀ (L u : ℕ), 1 ≤ L →
      (∀ a, a + L ≤ u + 1 → ∃ j, j < L ∧ w (a + j) = p) →
      hfix w u ≤ (2 * p / (2 * p - 1)) * (1 + (L : ℝ)) := by
  intro L u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hL hyp
    have hp0 : (0 : ℝ) < p := by linarith
    have hpm : (0 : ℝ) < 2 * p - 1 := two_p_sub_one_pos hp
    have hw0 : ∀ n, 0 < w n := by
      intro n
      rcases hw n with h | h <;> rw [h] <;> linarith
    have hw1 : ∀ n, w n ≤ 1 := by
      intro n
      rcases hw n with h | h <;> rw [h] <;> linarith
    have hK0 : (0 : ℝ) ≤ 2 * p / (2 * p - 1) := by positivity
    have hLpos : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    have hone : (1 : ℝ) - (2 * p - 1) / p = (1 - p) / p := by
      field_simp
      ring
    have htwo : ((2 * p - 1) / p) * (2 * p / (2 * p - 1)) = 2 := by
      field_simp
    have hru : ((1 - p) / p) * ((2 * p / (2 * p - 1)) * (1 + (L : ℝ)))
        = (2 * p / (2 * p - 1)) * (1 + (L : ℝ)) - 2 * (1 + (L : ℝ)) := by
      rw [← hone, sub_mul, one_mul, ← mul_assoc, htwo]
    have hrun : ∀ j v, j ≤ v → v ≤ u → w j = p → (∀ x, j < x → x ≤ v → w x = 1 / 2) →
        ((v - j : ℕ) : ℝ) ≤ (L : ℝ) - 1 := by
      intro j v hjv hvu hjm hunm
      have hle : v - j ≤ L - 1 := by
        rcases Nat.lt_or_ge (v - j) L with hlt | hge
        · omega
        · exfalso
          obtain ⟨i, hiL, hiw⟩ := hyp (j + 1) (by omega)
          have hji : j < j + 1 + i := by omega
          have hiv : j + 1 + i ≤ v := by omega
          have hcon := hunm (j + 1 + i) hji hiv
          rw [hcon] at hiw
          linarith [hp]
      exact_mod_cast hle
    by_cases hex : ∃ j, j ≤ u ∧ w j = p
    · obtain ⟨j0, hj0u, hj0m⟩ := hex
      obtain ⟨j, hjm, hju, hmax⟩ :
          ∃ j : ℕ, w j = p ∧ j ≤ u ∧ (∀ x, j < x → x ≤ u → w x ≠ p) := by
        classical
        refine ⟨Nat.findGreatest (fun x => w x = p) u, ?_, ?_, ?_⟩
        · exact Nat.findGreatest_spec (P := fun x => w x = p) hj0u hj0m
        · exact Nat.findGreatest_le (P := fun x => w x = p) u
        · intro x hjx hxu
          exact Nat.findGreatest_is_greatest (P := fun x => w x = p) hjx hxu
      have hunm : ∀ x, j < x → x ≤ u → w x = 1 / 2 := by
        intro x hjx hxu
        rcases hw x with h | h
        · exact absurd h (hmax x hjx hxu)
        · exact h
      rcases Nat.eq_zero_or_pos j with hjz | hjpos
      · -- the only marked site is `0`
        subst hjz
        rcases Nat.lt_or_ge 0 u with hlt | hge
        · rw [hfix_add_two_mul hju hunm, hfix_zero_of_eq_mark hp0.ne' hjm]
          have h5 := hrun 0 u (Nat.zero_le u) le_rfl hjm hunm
          linarith [run_start_bound hp hp1 hL]
        · have hu0 : u = 0 := by omega
          rw [hu0] at ⊢
          rw [hfix_zero_of_eq_mark hp0.ne' hjm]
          exact start_bound hp hp1 hL
      · -- `j ≥ 1`: one contraction step, then the tail run
        have hjj : j - 1 + 1 = j := Nat.succ_pred_eq_of_pos hjpos
        have hstep := hfix_succ_of_eq_mark (p := p) hp0.ne' (n := j - 1) (w := w)
          (by rw [hjj]; exact hjm)
        rw [hjj] at hstep
        have hIH : hfix w (j - 1) ≤ (2 * p / (2 * p - 1)) * (1 + (L : ℝ)) :=
          ih (j - 1) (by omega) hL (fun a ha => hyp a (by omega))
        have h2 : ((1 - p) / p) * hfix w (j - 1)
            ≤ ((1 - p) / p) * ((2 * p / (2 * p - 1)) * (1 + (L : ℝ))) :=
          mul_le_mul_of_nonneg_left hIH (div_nonneg (by linarith) hp0.le)
        rw [hru] at h2
        have h1 : (1 : ℝ) / p + 2 * ((L : ℝ) - 1) ≤ 2 * (1 + (L : ℝ)) := by
          have hinv := half_lt_one_div hp
          nlinarith
        have h6 : (2 : ℝ) * (1 + (L : ℝ)) ≤ (2 * p / (2 * p - 1)) * (1 + (L : ℝ)) :=
          mul_le_mul_of_nonneg_right (two_le_K hp hp1) (by linarith)
        rcases Nat.lt_or_ge j u with hlt | hge
        · rw [hfix_add_two_mul hju hunm, hstep]
          have h5 := hrun j u hju le_rfl hjm hunm
          have h7 : 2 * ((u - j : ℕ) : ℝ) ≤ 2 * ((L : ℝ) - 1) := by linarith
          nlinarith
        · have hje : j = u := by omega
          rw [← hje, hstep]
          have h1b : (1 : ℝ) / p ≤ 2 * (1 + (L : ℝ)) := by
            have hinv := half_lt_one_div hp
            nlinarith
          nlinarith
    · -- no marked site in `[0,u]`
      push Not at hex
      have hall : ∀ x, x ≤ u → w x = 1 / 2 := by
        intro x hx
        rcases hw x with h | h
        · exact absurd h (hex x hx)
        · exact h
      have huL : u + 1 ≤ L := by
        by_contra hcon
        push Not at hcon
        obtain ⟨i, hiL, hiw⟩ := hyp 0 (by omega)
        exact hex i (by omega) (by simpa using hiw)
      have h0 : hfix w u = 1 + 2 * ((u : ℝ) + 1) := by
        have hz : w 0 = 1 / 2 := hall 0 (Nat.zero_le u)
        rcases Nat.eq_zero_or_pos u with hu0 | hup
        · subst hu0; rw [hfix_zero_of_eq_half hz]; norm_num
        · have h := hfix_add_two_mul (w := w) (j := 0) (u := u) (Nat.zero_le u)
              (fun x _ hxu => hall x hxu)
          rw [h, hfix_zero_of_eq_half hz, Nat.sub_zero]
          push_cast
          ring
      rw [h0]
      have h2l : ((u : ℝ) + 1) ≤ (L : ℝ) := by
        have : u + 1 ≤ L := huL
        exact_mod_cast this
      have hfin : 1 + 2 * ((u : ℝ) + 1) ≤ (2 * p / (2 * p - 1)) * (1 + (L : ℝ)) := by
        have hK := two_le_K hp hp1
        have h2 : (2 : ℝ) * (1 + (L : ℝ)) ≤ (2 * p / (2 * p - 1)) * (1 + (L : ℝ)) :=
          mul_le_mul_of_nonneg_right hK (by linarith)
        nlinarith
      exact hfin

end SwarmMpot
