/-
  # The SUMMED above-record projected-slope interface for `(lococc)`-/
import Swarm.LocOccCarrier

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace SummedSlope

open Finset

variable {N : ℕ}

/-! ### 1. The geometric partial sum: `(1-a^g)/(1-a) = Σ_{h<g} a^h` -/

/-- The above-record correction factor is *exactly* the geometric partial sum. -/
theorem projA_eq_geom_sum {a : ℝ} (ha : a < 1) (g : ℕ) :
    (1 - a ^ g) / (1 - a) = ∑ h ∈ Finset.range g, a ^ h := by
  have hne : a ≠ 1 := by linarith
  rw [geom_sum_eq hne g]
  field_simp
  ring

/-- Difference of two correction factors is the geometric sum over the interval. -/
theorem projA_Ico_sub {a : ℝ} (ha : a < 1) {g1 g2 : ℕ} (h12 : g1 ≤ g2) :
    (1 - a ^ g2) / (1 - a) - (1 - a ^ g1) / (1 - a)
      = ∑ h ∈ Finset.Ico g1 g2, a ^ h := by
  have hne : a ≠ 1 := by linarith
  rw [geom_sum_Ico' hne h12]
  field_simp
  ring

/-- The partial sum is at most the number of terms. -/
theorem projA_le_card {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (g : ℕ) :
    ∑ h ∈ Finset.range g, a ^ h ≤ (g : ℝ) := by
  calc ∑ h ∈ Finset.range g, a ^ h ≤ ∑ _h ∈ Finset.range g, (1 : ℝ) := by
        refine Finset.sum_le_sum fun h _ => ?_
        exact pow_le_one₀ ha0 ha1
    _ = (g : ℝ) := by simp

/-- The interval geometric sum is at most `(1-a)⁻¹`. -/
theorem geom_Ico_le_inv {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {g1 g2 : ℕ} :
    ∑ h ∈ Finset.Ico g1 g2, a ^ h ≤ (1 - a)⁻¹ := by
  have hpos : (0 : ℝ) < 1 - a := by linarith
  refine le_trans (geom_sum_Ico_le_of_lt_one ha0 ha1 (m := g1) (n := g2)) ?_
  have hp : a ^ g1 ≤ 1 := pow_le_one₀ ha0 ha1.le
  have hinv : (0 : ℝ) ≤ (1 - a)⁻¹ := le_of_lt (inv_pos.mpr hpos)
  calc a ^ g1 / (1 - a) ≤ 1 / (1 - a) :=
        div_le_div_of_nonneg_right hp (le_of_lt hpos)
    _ = (1 - a)⁻¹ := one_div _

theorem geom_Ico_nonneg {a : ℝ} (ha0 : 0 ≤ a) {g1 g2 : ℕ} :
    0 ≤ ∑ h ∈ Finset.Ico g1 g2, a ^ h :=
  Finset.sum_nonneg fun h _ => pow_nonneg ha0 h

/-! ### 2. The abstract summed above-record estimate -/

theorem closed_form_sum_le {a L H0 e0 : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hL : L = (1 + a) / (1 - a)) (he0 : 0 ≤ e0) {H : ℕ → ℝ}
    (hH : ∀ g : ℕ, H g = H0 + (g : ℝ) * L + (e0 - L) * ((1 - a ^ g) / (1 - a)))
    {g1 g2 : ℕ} (h12 : g1 ≤ g2) :
    H g2 - H g1 ≤ L * ((g2 : ℝ) - (g1 : ℝ)) + e0 / (1 - a) := by
  have hden : (0 : ℝ) < 1 - a := by linarith
  have hdiff : H g2 - H g1
      = L * ((g2 : ℝ) - (g1 : ℝ)) + (e0 - L) * ∑ h ∈ Finset.Ico g1 g2, a ^ h := by
    rw [hH g2, hH g1, ← projA_Ico_sub ha1 h12]
    ring
  rw [hdiff]
  have hS0 : (0 : ℝ) ≤ ∑ h ∈ Finset.Ico g1 g2, a ^ h := geom_Ico_nonneg ha0
  have hS : ∑ h ∈ Finset.Ico g1 g2, a ^ h ≤ (1 - a)⁻¹ := geom_Ico_le_inv ha0 ha1
  have hinv : (0 : ℝ) ≤ (1 - a)⁻¹ := le_of_lt (inv_pos.mpr hden)
  have hL0 : (0 : ℝ) ≤ L := by rw [hL]; positivity
  have hdef : (e0 - L) * ∑ h ∈ Finset.Ico g1 g2, a ^ h ≤ e0 / (1 - a) := by
    have hsingle : e0 / (1 - a) = e0 * (1 - a)⁻¹ := by rw [div_eq_mul_inv]
    rw [hsingle]
    rcases le_or_gt L e0 with hLe | hLt
    · have h1 : (e0 - L) * ∑ h ∈ Finset.Ico g1 g2, a ^ h ≤ (e0 - L) * (1 - a)⁻¹ :=
        mul_le_mul_of_nonneg_left hS (by linarith)
      have h2 : (e0 - L) * (1 - a)⁻¹ ≤ e0 * (1 - a)⁻¹ :=
        mul_le_mul_of_nonneg_right (by linarith) hinv
      linarith
    · have h1 : (e0 - L) * ∑ h ∈ Finset.Ico g1 g2, a ^ h ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) hS0
      have h2 : (0 : ℝ) ≤ e0 * (1 - a)⁻¹ := mul_nonneg he0 hinv
      linarith
  linarith

/-- **The single above-record step**, exactly: `L` plus the geometrically damped seed defect. -/
theorem closed_form_step_eq {a L H0 e0 : ℝ} (ha1 : a < 1) {H : ℕ → ℝ}
    (hH : ∀ g : ℕ, H g = H0 + (g : ℝ) * L + (e0 - L) * ((1 - a ^ g) / (1 - a))) (g : ℕ) :
    H (g + 1) - H g = L + (e0 - L) * a ^ g := by
  have hI : ∑ h ∈ Finset.Ico g (g + 1), a ^ h = a ^ g := by simp
  have hA : (1 - a ^ (g + 1)) / (1 - a) - (1 - a ^ g) / (1 - a) = a ^ g := by
    rw [projA_Ico_sub ha1 (Nat.le_succ g)]
    exact hI
  rw [hH (g + 1), hH g]
  push_cast
  rw [show H0 + ((g : ℝ) + 1) * L + (e0 - L) * ((1 - a ^ (g + 1)) / (1 - a))
        - (H0 + (g : ℝ) * L + (e0 - L) * ((1 - a ^ g) / (1 - a)))
      = L * (((g : ℝ) + 1) - (g : ℝ))
        + (e0 - L) * ((1 - a ^ (g + 1)) / (1 - a) - (1 - a ^ g) / (1 - a)) from by ring]
  rw [hA]
  ring

/-- Each single above-record step is nonnegative. -/
theorem closed_form_step_nonneg {a L H0 e0 : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hL : L = (1 + a) / (1 - a)) (he0 : 0 ≤ e0) {H : ℕ → ℝ}
    (hH : ∀ g : ℕ, H g = H0 + (g : ℝ) * L + (e0 - L) * ((1 - a ^ g) / (1 - a))) (g : ℕ) :
    0 ≤ H (g + 1) - H g := by
  have hden : (0 : ℝ) < 1 - a := by linarith
  have hLpos : 0 < L := by rw [hL]; positivity
  have hstep := closed_form_step_eq ha1 hH g
  rw [hstep]
  have hpow0 : 0 ≤ a ^ g := pow_nonneg ha0 g
  have hpow1 : a ^ g ≤ 1 := pow_le_one₀ ha0 ha1.le
  rcases le_or_gt L e0 with h | h
  · have hnn : 0 ≤ (e0 - L) * a ^ g := mul_nonneg (by linarith) hpow0
    linarith
  · have h1 : (e0 - L) ≤ (e0 - L) * a ^ g := by
      have h2 := mul_le_mul_of_nonpos_left hpow1 (by linarith : e0 - L ≤ 0)
      simpa using h2
    linarith

/-- **The per-site upper bound from a seed bound.**  If `Kp ≥ L` and `e_0 ≤ Kp` then every single
above-record step is at most `Kp`.  This is the *exact* content of the accepted per-site premise:
it is a bound on the projected seed, nothing else (the converse is
`LocOccCarrier.seed_le_of_slopeHi`). -/
theorem closed_form_step_le {a L H0 e0 Kp : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hLK : L ≤ Kp) (heK : e0 ≤ Kp) {H : ℕ → ℝ}
    (hH : ∀ g : ℕ, H g = H0 + (g : ℝ) * L + (e0 - L) * ((1 - a ^ g) / (1 - a))) (g : ℕ) :
    H (g + 1) - H g ≤ Kp := by
  have hstep := closed_form_step_eq ha1 hH g
  rw [hstep]
  have hpow0 : 0 ≤ a ^ g := pow_nonneg ha0 g
  have hpow1 : a ^ g ≤ 1 := pow_le_one₀ ha0 ha1.le
  rcases le_or_gt L e0 with h | h
  · have h2 : (e0 - L) * a ^ g ≤ e0 - L := by
      have := mul_le_mul_of_nonneg_left hpow1 (by linarith : (0:ℝ) ≤ e0 - L)
      simpa using this
    linarith
  · have h2 : (e0 - L) * a ^ g ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hpow0
    linarith


/-! ### 3. The summed deterministic interface (`hdiff_le` with a summed above-record premise)

The accepted `LocOcc.hdiff_le` asks for a per-site `hslopeHi` with a constant `Kp`.  Here the
per-site upper bound is replaced by

* `hslopeHi0` — per-site *nonnegativity* (which the model does supply), and
* `hsumHi` — the **summed** bound `H w - H u ≤ Kp (w-u) + Cadd` for every `xv ≤ u ≤ w`.

The conclusion keeps the paper's shape and gains the single additive defect `Cadd`. -/

theorem hdiff_le_summed {H h : ℕ → ℝ} {xv u v : ℕ} {K β Kp Cadd : ℝ}
    (hh : ∀ x, 0 ≤ h x) (hK : 1 ≤ K) (hβ : 0 ≤ β) (hKp : 0 ≤ Kp) (hCa : 0 ≤ Cadd)
    (hslopeLo : ∀ x, x < xv → H (x + 1) - H x = h x)
    (hslopeHi0 : ∀ x, xv ≤ x → 0 ≤ H (x + 1) - H x)
    (hsumHi : ∀ u w : ℕ, xv ≤ u → u ≤ w → H w - H u ≤ Kp * ((w : ℝ) - (u : ℝ)) + Cadd)
    {A Lw : ℕ}
    (hsq : ∀ a b : ℕ, A ≤ a → b ≤ A + Lw → a ≤ b →
      ∑ x ∈ Finset.Ico a b, (h x) ^ 2 ≤ K * ((b : ℝ) - (a : ℝ)) + K * β)
    (hAle : A ≤ u) (hLw : min v xv ≤ A + Lw) :
    H v - H u ≤ (K + Kp) * max 0 ((v : ℝ) - (u : ℝ)) + K * β + Cadd := by
  have hmonoH : Monotone H := by
    refine monotone_nat_of_le_succ fun x => ?_
    rcases lt_or_ge x xv with hx | hx
    · have h := hslopeLo x hx
      linarith [hh x]
    · linarith [hslopeHi0 x hx]
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hKB : (0 : ℝ) ≤ K * β := by positivity
  rcases le_or_gt v u with hvu | huv
  · have hle : H v - H u ≤ 0 := by have := hmonoH hvu; linarith
    have h0 : (0 : ℝ) ≤ (K + Kp) * max 0 ((v : ℝ) - (u : ℝ)) := by
      have h1 : (0 : ℝ) ≤ K + Kp := by linarith
      exact mul_nonneg h1 (le_max_left _ _)
    linarith
  · have huvle : u ≤ v := le_of_lt huv
    have htel : ∑ x ∈ Finset.Ico u v, (H (x + 1) - H x) = H v - H u :=
      LocOcc.sum_Ico_telescope huvle
    have hvu_pos : (0 : ℝ) ≤ (v : ℝ) - (u : ℝ) := by
      have h1 : (u : ℝ) ≤ (v : ℝ) := by exact_mod_cast huvle
      linarith
    have hmax : max 0 ((v : ℝ) - (u : ℝ)) = (v : ℝ) - (u : ℝ) := max_eq_right hvu_pos
    rw [← htel, hmax]
    rcases le_or_gt xv u with hxu | hxu
    · -- entirely above the record: the summed bound on `[u,v]`
      have hsum := hsumHi u v hxu huvle
      have harith : Kp * ((v : ℝ) - (u : ℝ)) + Cadd
          ≤ (K + Kp) * ((v : ℝ) - (u : ℝ)) + K * β + Cadd := by
        nlinarith [hK0, hvu_pos, hKB]
      linarith
    · rcases le_or_gt v xv with hvx | hvx
      · -- entirely below the record: the `h`-sum
        have hmin : min v xv = v := min_eq_left hvx
        have hcongr : ∑ x ∈ Finset.Ico u v, (H (x + 1) - H x) = ∑ x ∈ Finset.Ico u v, h x := by
          refine Finset.sum_congr rfl fun x hx' => ?_
          rw [hslopeLo x (by have := (Finset.mem_Ico.mp hx').2; omega)]
        rw [hcongr]
        have hLw' : v ≤ A + Lw := by rw [← hmin]; exact hLw
        have hle := LocOcc.hsum_le_of_hsq (h := h) hh hK hβ huvle (hsq u v hAle hLw' huvle)
        have hKp' : (0 : ℝ) ≤ Kp * ((v : ℝ) - (u : ℝ)) := mul_nonneg hKp hvu_pos
        linarith
      · -- split at the record
        have hmin : min v xv = xv := min_eq_right (le_of_lt hvx)
        have huxv : u ≤ xv := le_of_lt hxu
        have hxvv : xv ≤ v := le_of_lt hvx
        have hlow : ∑ x ∈ Finset.Ico u xv, (H (x + 1) - H x)
            ≤ K * ((xv : ℝ) - (u : ℝ)) + K * β := by
          have hcongr : ∑ x ∈ Finset.Ico u xv, (H (x + 1) - H x) = ∑ x ∈ Finset.Ico u xv, h x := by
            refine Finset.sum_congr rfl fun x hx' => ?_
            rw [hslopeLo x (by have := (Finset.mem_Ico.mp hx').2; omega)]
          rw [hcongr]
          have hLw' : xv ≤ A + Lw := by rw [← hmin]; exact hLw
          exact LocOcc.hsum_le_of_hsq (h := h) hh hK hβ huxv (hsq u xv hAle hLw' huxv)
        have hhigh : ∑ x ∈ Finset.Ico xv v, (H (x + 1) - H x)
            ≤ Kp * ((v : ℝ) - (xv : ℝ)) + Cadd := by
          rw [LocOcc.sum_Ico_telescope hxvv]
          exact hsumHi xv v le_rfl hxvv
        have hsplit : ∑ x ∈ Finset.Ico u v, (H (x + 1) - H x)
            = (∑ x ∈ Finset.Ico u xv, (H (x + 1) - H x))
              + (∑ x ∈ Finset.Ico xv v, (H (x + 1) - H x)) :=
          (LocOcc.sum_Ico_split huxv hxvv).symm
        have hcast1 : (u : ℝ) ≤ (xv : ℝ) := by exact_mod_cast huxv
        have hcast2 : (xv : ℝ) ≤ (v : ℝ) := by exact_mod_cast hxvv
        rw [hsplit]
        nlinarith [hlow, hhigh, hK0, hKB, hKp, hCa, hcast1, hcast2]

/-! ### 4. The summed `Z_t - Z_s` and the summed `(lococc)` display -/

theorem zdiff_le_summed {Z : ℕ → ℝ} {H : ℕ → ℕ → ℝ} {h wt : ℕ → ℝ} {X Mt : ℕ → ℕ}
    {Fs Ft : ℝ} {s t : ℕ} {A Lw : ℕ} {K β Kp CH KF L34 Cadd : ℝ}
    (hZs : Z s = H s (X s) - Fs) (hZt : Z t = H t (X t) - Ft)
    (hh : ∀ x, 0 ≤ h x) (hhw : ∀ x, (h x) ^ 2 ≤ wt x)
    (hK : 1 ≤ K) (hβ : 0 ≤ β) (hKp : 0 ≤ Kp) (hCa : 0 ≤ Cadd)
    (hslopeLo : ∀ x, x < Mt t → H t (x + 1) - H t x = h x)
    (hslopeHi0 : ∀ x, Mt t ≤ x → 0 ≤ H t (x + 1) - H t x)
    (hsumHi : ∀ u w : ℕ, Mt t ≤ u → u ≤ w →
      H t w - H t u ≤ Kp * ((w : ℝ) - (u : ℝ)) + Cadd)
    (hint : ∀ a b : ℕ, A ≤ a → b ≤ A + Lw → a ≤ b →
      ∑ x ∈ Finset.Ico a b, wt x ≤ K * ((b : ℝ) - (a : ℝ)) + K * β)
    (hAle : A ≤ X s) (hLwmax : min (X t) (Mt t) ≤ A + Lw)
    (hosc : H t (X s) - H s (X s) ≤ CH * L34)
    (hFs : |Fs| ≤ KF * L34) (hFt : |Ft| ≤ KF * L34) :
    Z t - Z s ≤ (K + Kp) * max 0 ((X t : ℝ) - (X s : ℝ)) + K * β + CH * L34
      + 2 * (KF * L34) + Cadd := by
  have hspat : H t (X t) - H t (X s)
      ≤ (K + Kp) * max 0 ((X t : ℝ) - (X s : ℝ)) + K * β + Cadd := by
    refine hdiff_le_summed (xv := Mt t) (u := X s) (v := X t) hh hK hβ hKp hCa hslopeLo
      hslopeHi0 hsumHi ?_ hAle hLwmax
    intro a b ha hb hab
    exact le_trans (Finset.sum_le_sum (fun x _ => hhw x)) (hint a b ha hb hab)
  have hF : Fs - Ft ≤ KF * L34 + KF * L34 := by
    have h1 : Fs ≤ KF * L34 := (abs_le.mp hFs).2
    have h2 : -(KF * L34) ≤ Ft := (abs_le.mp hFt).1
    linarith
  have h1 : Z t - Z s = (H t (X t) - H t (X s)) + (H t (X s) - H s (X s)) + (Fs - Ft) := by
    rw [hZs, hZt]; ring
  linarith [hspat, hosc, hF]

theorem lococc_summed {X Mi Mj : ℕ → ℕ} {occ J Z Q : ℕ → ℝ} {H : ℕ → ℕ → ℝ} {Fs Ft : ℝ}
    {h wt : ℕ → ℝ} {s t A Lw : ℕ} {K β Kp CH KQ KF CJ ε L34 Cadd CaddK : ℝ}
    (hst : s ≤ t)
    (hocc : ∀ u, s ≤ u → u < t → occ u = if X u ≤ Mj u then (1 : ℝ) else 0)
    (hled : ∀ u, occ u - ε ≤ (Z (u + 1) - Z u) + J u - (Q (u + 1) - Q u))
    (hZs : Z s = H s (X s) - Fs) (hZt : Z t = H t (X t) - Ft)
    (hh : ∀ x, 0 ≤ h x) (hhw : ∀ x, (h x) ^ 2 ≤ wt x)
    (hslopeLo : ∀ x, x < Mj t → H t (x + 1) - H t x = h x)
    (hslopeHi0 : ∀ x, Mj t ≤ x → 0 ≤ H t (x + 1) - H t x)
    (hsumHi : ∀ u w : ℕ, Mj t ≤ u → u ≤ w →
      H t w - H t u ≤ Kp * ((w : ℝ) - (u : ℝ)) + Cadd)
    (hint : ∀ a b : ℕ, A ≤ a → b ≤ A + Lw → a ≤ b →
      ∑ x ∈ Finset.Ico a b, wt x ≤ K * ((b : ℝ) - (a : ℝ)) + K * β)
    (hosc : H t (X s) - H s (X s) ≤ CH * L34)
    (hQ : -(Q t - Q s) ≤ KQ * L34)
    (hFs : |Fs| ≤ KF * L34) (hFt : |Ft| ≤ KF * L34)
    (hJstruct : ∀ n, |J n| ≤ CJ * (wt (Mj n) + wt (Mj n + 1)) *
      (if Mj (n + 1) = Mj n + 1 ∧ (Mj n : ℤ) < ((X (n + 1) : ℕ) : ℤ) then 1 else 0))
    (hMjmono : ∀ n, Mj n ≤ Mj (n + 1)) (hMjstep : ∀ n, Mj (n + 1) ≤ Mj n + 1)
    (hXW : ∀ n, s ≤ n → n < t → X (n + 1) ≤ Mi t)
    (hMiw : Mi s ≤ Mi t) (hXMiS : X s ≤ Mi s) (hXtMi : X t ≤ Mi t)
    (hcont1 : A ≤ X s) (hcont2 : A ≤ Mj s)
    (hcont3 : X t ≤ A + Lw) (hcont4 : Mi t + 1 ≤ A + Lw) (hcont5 : Mj t ≤ A + Lw)
    (hK : 1 ≤ K) (hβ : 0 ≤ β) (hKp : 0 ≤ Kp) (hCJ : 0 ≤ CJ) (hCH : 0 ≤ CH)
    (hKF : 0 ≤ KF) (hKQ : 0 ≤ KQ)
    (hL34 : 0 ≤ L34) (h1L34 : 1 ≤ L34) (hβL : β ≤ L34)
    (hCa : 0 ≤ Cadd) (hCaddL : Cadd ≤ CaddK * L34) :
    ∑ u ∈ Finset.Ico s t, occ u
      ≤ ((K + Kp) + 2 * CJ * K + 1) *
          (((Mi t : ℝ) - (Mi s : ℝ)) + ((Mi s : ℝ) - (X s : ℝ))
            + max 0 ((Mi s : ℝ) - (Mj s : ℝ)))
        + ε * ((t : ℝ) - (s : ℝ))
        + (K + CH + 2 * KF + 4 * CJ * K + 2 * KQ + 1 + CaddK) * L34 := by
  have h1 : ∑ u ∈ Finset.Ico s t, occ u
      ≤ ε * ((t : ℝ) - (s : ℝ)) + (Z t - Z s) + (∑ u ∈ Finset.Ico s t, J u) - (Q t - Q s) :=
    LocOcc.window_le_of_step hst hled
  have hJsum : ∑ u ∈ Finset.Ico s t, J u ≤ ∑ u ∈ Finset.Ico s t, |J u| :=
    Finset.sum_le_sum fun u _ => le_abs_self (J u)
  have hJb : ∑ u ∈ Finset.Ico s t, |J u|
      ≤ 2 * CJ * ∑ x ∈ Finset.Ico (Mj s) (Mi t + 1), wt x := by
    refine LocOcc.jsum_le_window (X := fun n => ((X n : ℕ) : ℤ)) hMjmono hMjstep
      (fun x => le_trans (sq_nonneg (h x)) (hhw x)) hCJ hJstruct hst ?_
    intro n _ hn
    have := hXW n ‹s ≤ n› hn
    exact_mod_cast this
  have hJint : ∑ x ∈ Finset.Ico (Mj s) (Mi t + 1), wt x
      ≤ K * max 0 (((Mi t : ℝ) + 1) - (Mj s : ℝ)) + K * β := by
    rcases le_or_gt (Mj s) (Mi t + 1) with hle | hgt
    · have h := hint (Mj s) (Mi t + 1) hcont2 hcont4 hle
      have hcast : (((Mi t + 1 : ℕ) : ℝ) - (Mj s : ℝ)) = ((Mi t : ℝ) + 1) - (Mj s : ℝ) := by
        push_cast; ring
      rw [hcast] at h
      have hnn : (0 : ℝ) ≤ ((Mi t : ℝ) + 1) - (Mj s : ℝ) := by
        have h2 : (Mj s : ℝ) ≤ ((Mi t + 1 : ℕ) : ℝ) := by exact_mod_cast hle
        push_cast at h2; linarith
      rw [max_eq_right hnn]
      exact h
    · have hempty : Finset.Ico (Mj s) (Mi t + 1) = ∅ := Finset.Ico_eq_empty (by omega)
      rw [hempty, Finset.sum_empty]
      have hneg : ((Mi t : ℝ) + 1) - (Mj s : ℝ) ≤ 0 := by
        have h2 : ((Mi t + 1 : ℕ) : ℝ) ≤ (Mj s : ℝ) := by exact_mod_cast le_of_lt hgt
        push_cast at h2; linarith
      rw [max_eq_left hneg]
      have h3 : (0 : ℝ) ≤ K * β := by positivity
      linarith
  have hZ : Z t - Z s ≤ (K + Kp) * max 0 ((X t : ℝ) - (X s : ℝ)) + K * β + CH * L34
      + 2 * (KF * L34) + Cadd :=
    zdiff_le_summed hZs hZt hh hhw hK hβ hKp hCa hslopeLo hslopeHi0 hsumHi hint hcont1
      (le_trans (min_le_right _ _) hcont5) hosc hFs hFt
  have hXs : max 0 ((X t : ℝ) - (X s : ℝ))
      ≤ ((Mi t : ℝ) - (Mi s : ℝ)) + ((Mi s : ℝ) - (X s : ℝ)) := by
    have h1' : (Mi s : ℝ) ≤ (Mi t : ℝ) := by exact_mod_cast hMiw
    have h2' : (X s : ℝ) ≤ (Mi s : ℝ) := by exact_mod_cast hXMiS
    rcases le_or_gt (X t) (X s) with hle | hgt
    · have h0 : (X t : ℝ) - (X s : ℝ) ≤ 0 := by
        have h3 : (X t : ℝ) ≤ (X s : ℝ) := by exact_mod_cast hle
        linarith
      rw [max_eq_left h0]
      linarith
    · have h0 : (0 : ℝ) ≤ (X t : ℝ) - (X s : ℝ) := by
        have h3 : (X s : ℝ) ≤ (X t : ℝ) := by exact_mod_cast le_of_lt hgt
        linarith
      rw [max_eq_right h0]
      have h3 : (X t : ℝ) ≤ (Mi t : ℝ) := by exact_mod_cast hXtMi
      linarith
  have hSJ : max 0 (((Mi t : ℝ) + 1) - (Mj s : ℝ))
      ≤ (((Mi t : ℝ) - (Mi s : ℝ)) + ((Mi s : ℝ) - (X s : ℝ))
          + max 0 ((Mi s : ℝ) - (Mj s : ℝ))) + 1 := by
    have h1' : (Mi s : ℝ) ≤ (Mi t : ℝ) := by exact_mod_cast hMiw
    have h2' : (X s : ℝ) ≤ (Mi s : ℝ) := by exact_mod_cast hXMiS
    have hzero : (0 : ℝ) ≤ ((Mi t : ℝ) - (Mi s : ℝ)) + ((Mi s : ℝ) - (X s : ℝ))
        + max 0 ((Mi s : ℝ) - (Mj s : ℝ)) := by
      linarith [le_max_left (0 : ℝ) ((Mi s : ℝ) - (Mj s : ℝ))]
    rcases le_or_gt (Mj s) (Mi s) with hle | hgt
    · have h3 : (Mj s : ℝ) ≤ (Mi s : ℝ) := by exact_mod_cast hle
      have hnn : (0 : ℝ) ≤ ((Mi t : ℝ) + 1) - (Mj s : ℝ) := by linarith
      have hnn2 : (0 : ℝ) ≤ (Mi s : ℝ) - (Mj s : ℝ) := by linarith
      calc max 0 (((Mi t : ℝ) + 1) - (Mj s : ℝ))
          = ((Mi t : ℝ) + 1) - (Mj s : ℝ) := max_eq_right hnn
        _ ≤ (((Mi t : ℝ) - (Mi s : ℝ)) + ((Mi s : ℝ) - (X s : ℝ))
              + max 0 ((Mi s : ℝ) - (Mj s : ℝ))) + 1 := by
            rw [max_eq_right hnn2]; linarith
    · have h3 : (Mi s : ℝ) < (Mj s : ℝ) := by exact_mod_cast hgt
      refine max_le ?_ ?_
      · linarith [hzero, le_max_left (0 : ℝ) ((Mi s : ℝ) - (Mj s : ℝ))]
      · linarith [h3, h2', le_max_left (0 : ℝ) ((Mi s : ℝ) - (Mj s : ℝ))]
  have hCJK : (0 : ℝ) ≤ 2 * CJ * K := by
    have h0 : (0 : ℝ) ≤ K := by linarith
    have h1' : (0 : ℝ) ≤ 2 * CJ := by linarith
    nlinarith
  have hKB : (0 : ℝ) ≤ K * β := by positivity
  have hG0 : (0 : ℝ) ≤ ((Mi t : ℝ) - (Mi s : ℝ)) + ((Mi s : ℝ) - (X s : ℝ))
      + max 0 ((Mi s : ℝ) - (Mj s : ℝ)) := by
    have h1' : (Mi s : ℝ) ≤ (Mi t : ℝ) := by exact_mod_cast hMiw
    have h2' : (X s : ℝ) ≤ (Mi s : ℝ) := by exact_mod_cast hXMiS
    linarith [le_max_left (0 : ℝ) ((Mi s : ℝ) - (Mj s : ℝ))]
  have hZa : (K + Kp) * max 0 ((X t : ℝ) - (X s : ℝ))
      ≤ (K + Kp) * (((Mi t : ℝ) - (Mi s : ℝ)) + ((Mi s : ℝ) - (X s : ℝ))
          + max 0 ((Mi s : ℝ) - (Mj s : ℝ))) := by
    have h0 : (0 : ℝ) ≤ K + Kp := by linarith
    have h1' : max 0 ((X t : ℝ) - (X s : ℝ))
        ≤ ((Mi t : ℝ) - (Mi s : ℝ)) + ((Mi s : ℝ) - (X s : ℝ))
          + max 0 ((Mi s : ℝ) - (Mj s : ℝ)) := by
      linarith [hXs, le_max_left (0 : ℝ) ((Mi s : ℝ) - (Mj s : ℝ))]
    exact mul_le_mul_of_nonneg_left h1' h0
  have hZtot : Z t - Z s
      ≤ (K + Kp) * (((Mi t : ℝ) - (Mi s : ℝ)) + ((Mi s : ℝ) - (X s : ℝ))
          + max 0 ((Mi s : ℝ) - (Mj s : ℝ))) + (K + CH + 2 * KF) * L34 + Cadd := by
    have h0K : (0 : ℝ) ≤ K := by linarith
    have h4 : K * β ≤ K * L34 := mul_le_mul_of_nonneg_left hβL h0K
    have h5 : CH * L34 + 2 * (KF * L34) = (CH + 2 * KF) * L34 := by ring
    nlinarith [hZ, hZa, h4, h5]
  have hJpre : ∑ x ∈ Finset.Ico (Mj s) (Mi t + 1), wt x
      ≤ K * ((((Mi t : ℝ) - (Mi s : ℝ)) + ((Mi s : ℝ) - (X s : ℝ))
          + max 0 ((Mi s : ℝ) - (Mj s : ℝ))) + 1) + K * β := by
    nlinarith [hJint, hSJ]
  have hJtot : ∑ u ∈ Finset.Ico s t, |J u|
      ≤ 2 * CJ * K * (((Mi t : ℝ) - (Mi s : ℝ)) + ((Mi s : ℝ) - (X s : ℝ))
          + max 0 ((Mi s : ℝ) - (Mj s : ℝ))) + 4 * CJ * K * L34 := by
    have h0 : (0 : ℝ) ≤ 2 * CJ := by linarith
    have hstep : 2 * CJ * ∑ x ∈ Finset.Ico (Mj s) (Mi t + 1), wt x
        ≤ 2 * CJ * (K * ((((Mi t : ℝ) - (Mi s : ℝ)) + ((Mi s : ℝ) - (X s : ℝ))
          + max 0 ((Mi s : ℝ) - (Mj s : ℝ))) + 1) + K * β) :=
      mul_le_mul_of_nonneg_left hJpre h0
    have hCJKB : (0 : ℝ) ≤ 2 * CJ * K * β := by
      have h2CJ : (0 : ℝ) ≤ 2 * CJ := by linarith
      nlinarith [mul_nonneg h2CJ hKB]
    nlinarith [hstep, hβL, h1L34, hCJK, hKB, hCJKB]
  have hmain : ∑ u ∈ Finset.Ico s t, occ u
      ≤ ε * ((t : ℝ) - (s : ℝ))
        + ((K + Kp) + 2 * CJ * K) * (((Mi t : ℝ) - (Mi s : ℝ)) + ((Mi s : ℝ) - (X s : ℝ))
            + max 0 ((Mi s : ℝ) - (Mj s : ℝ)))
        + (K + CH + 2 * KF + 4 * CJ * K + 2 * KQ) * L34 + Cadd := by
    nlinarith [h1, hJsum, hJtot, hZtot, hQ, hG0, hL34]
  have hCeq : ((K + Kp) + 2 * CJ * K) * (((Mi t : ℝ) - (Mi s : ℝ)) + ((Mi s : ℝ) - (X s : ℝ))
        + max 0 ((Mi s : ℝ) - (Mj s : ℝ)))
      ≤ ((K + Kp) + 2 * CJ * K + 1) * (((Mi t : ℝ) - (Mi s : ℝ)) + ((Mi s : ℝ) - (X s : ℝ))
        + max 0 ((Mi s : ℝ) - (Mj s : ℝ))) := by
    nlinarith [hG0]
  have hReq : (K + CH + 2 * KF + 4 * CJ * K + 2 * KQ) * L34 + Cadd
      ≤ (K + CH + 2 * KF + 4 * CJ * K + 2 * KQ + 1 + CaddK) * L34 := by
    nlinarith [hL34, h1L34, hCaddL]
  linarith [hmain, hCeq, hReq]

/-! ### 5. The model: the summed above-record estimate from the closed form -/

namespace Model

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl
open SwarmMarks SwarmLogRatio LocSumAct

variable {N : ℕ}

/-- The paper's above-record slope `L = (1+a)/(1-a)`. -/
noncomputable def Lc (p : ℝ) (m : ℕ) : ℝ := (1 + aRec p m) / (1 - aRec p m)

theorem Lc_eq_Qpl (p : ℝ) (m : ℕ) : Lc p m = QplWindow.Lc p m := rfl

theorem Lc_pos {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) : 0 < Lc p m :=
  projL_pos hp1 hp2 m

theorem Lc_nonneg {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) : 0 ≤ Lc p m :=
  (Lc_pos hp1 hp2 m).le

/-- **The SUMMED above-record estimate at the actual record.**  From the accepted closed form,
for every site interval `[M+g1, M+g2]` above the record,

    projH (M+g2) - projH (M+g1) ≤ Lc (g2-g1) + e_0/(1-a).

The seed `e_0` enters only through the *single* additive defect `e_0/(1-a)`; there is no per-site
constant bound. -/
theorem projH_sum_above_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    {j : Fin N} {t : ℕ} {U : Array N}
    (hcl : ∀ (y : ℤ) (g : ℕ), y = recVal j (prefOf p m t U) + (g : ℤ) →
      projH p m j t U y
        = SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m t U))
          + (g : ℝ) * Lc p m
          + (eRec p m t j 0 U - Lc p m) * ((1 - aRec p m ^ g) / (1 - aRec p m)))
    (he1 : 0 ≤ eRec p m t j 0 U) {g1 g2 : ℕ} (h12 : g1 ≤ g2) :
    projH p m j t U (recVal j (prefOf p m t U) + (g2 : ℤ))
        - projH p m j t U (recVal j (prefOf p m t U) + (g1 : ℤ))
      ≤ Lc p m * ((g2 : ℝ) - (g1 : ℝ)) + eRec p m t j 0 U / (1 - aRec p m) := by
  have ha0 : 0 ≤ aRec p m := zero_le_aRec hp1 hp2 m
  have ha1 : aRec p m < 1 := aRec_lt_one hp1 hp2 m
  refine closed_form_sum_le (L := Lc p m) (H0 := SwarmOcc.Hpot (siteH p m j U)
    (recVal j (prefOf p m t U))) (e0 := eRec p m t j 0 U)
    (H := fun g => projH p m j t U (recVal j (prefOf p m t U) + (g : ℤ))) ha0 ha1 rfl he1 ?_ h12
  intro g
  exact hcl _ g (by ring)

/-- **Every single above-record step is nonnegative** — this half of the old per-site hypothesis
*is* available at the actual model. -/
theorem projH_step_above_nonneg {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    {j : Fin N} {t : ℕ} {U : Array N}
    (hcl : ∀ (y : ℤ) (g : ℕ), y = recVal j (prefOf p m t U) + (g : ℤ) →
      projH p m j t U y
        = SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m t U))
          + (g : ℝ) * Lc p m
          + (eRec p m t j 0 U - Lc p m) * ((1 - aRec p m ^ g) / (1 - aRec p m)))
    (he1 : 0 ≤ eRec p m t j 0 U) (g : ℕ) :
    0 ≤ projH p m j t U (recVal j (prefOf p m t U) + ((g + 1 : ℕ) : ℤ))
        - projH p m j t U (recVal j (prefOf p m t U) + (g : ℤ)) := by
  have ha0 : 0 ≤ aRec p m := zero_le_aRec hp1 hp2 m
  have ha1 : aRec p m < 1 := aRec_lt_one hp1 hp2 m
  have h := closed_form_step_nonneg (L := Lc p m) (H0 := SwarmOcc.Hpot (siteH p m j U)
    (recVal j (prefOf p m t U))) (e0 := eRec p m t j 0 U) ha0 ha1 rfl he1
    (H := fun g => projH p m j t U (recVal j (prefOf p m t U) + (g : ℤ)))
    (fun g => hcl _ g (by ring)) g
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- **The per-site upper bound at the actual record, from a seed bound.** -/
theorem projH_step_above_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    {j : Fin N} {t : ℕ} {U : Array N} {Kp : ℝ}
    (hcl : ∀ (y : ℤ) (g : ℕ), y = recVal j (prefOf p m t U) + (g : ℤ) →
      projH p m j t U y
        = SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m t U))
          + (g : ℝ) * Lc p m
          + (eRec p m t j 0 U - Lc p m) * ((1 - aRec p m ^ g) / (1 - aRec p m)))
    (hLK : Lc p m ≤ Kp) (heK : eRec p m t j 0 U ≤ Kp) (g : ℕ) :
    projH p m j t U (recVal j (prefOf p m t U) + ((g + 1 : ℕ) : ℤ))
        - projH p m j t U (recVal j (prefOf p m t U) + (g : ℤ)) ≤ Kp := by
  have ha0 : 0 ≤ aRec p m := zero_le_aRec hp1 hp2 m
  have ha1 : aRec p m < 1 := aRec_lt_one hp1 hp2 m
  have h := closed_form_step_le (L := Lc p m) (H0 := SwarmOcc.Hpot (siteH p m j U)
    (recVal j (prefOf p m t U))) (e0 := eRec p m t j 0 U) (Kp := Kp) ha0 ha1 hLK heK
    (H := fun g => projH p m j t U (recVal j (prefOf p m t U) + (g : ℤ)))
    (fun g => hcl _ g (by ring)) g
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- **The exact frontier.**  With `Kp ≥ Lc`, the per-site above-record premise of the accepted
interface `LocOcc.lococc_window_eighth`

    ∀ x ≥ M_t^j, 0 ≤ H(x+1) - H(x) ∧ H(x+1) - H(x) ≤ Kp

is *exactly* the seed bound `e_0 ≤ Kp`: it is supplied here from that bound, and the accepted
`LocOccCarrier.seed_le_of_slopeHi` extracts `e_0 ≤ Kp` from it.  Since `e_0 = eRec p m t j 0 U` is a
conditional mean depending on the array (only `0 ≤ e_0 ≤ b_n` is available), a `Kp` that does not
depend on `U` cannot be a per-site bound — which is why the summed premise of
`hdiff_le_summed`/`lococc_summed` is the correct replacement. -/
theorem per_site_slope_of_seed_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    {j : Fin N} {t : ℕ} {U : Array N} {Kp : ℝ}
    (hcl : ∀ (y : ℤ) (g : ℕ), y = recVal j (prefOf p m t U) + (g : ℤ) →
      projH p m j t U y
        = SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m t U))
          + (g : ℝ) * Lc p m
          + (eRec p m t j 0 U - Lc p m) * ((1 - aRec p m ^ g) / (1 - aRec p m)))
    (he1 : 0 ≤ eRec p m t j 0 U) (hLK : Lc p m ≤ Kp) (heK : eRec p m t j 0 U ≤ Kp) :
    ∀ x : ℕ, (runMax p m U j t).toNat ≤ x →
      0 ≤ projH p m j t U ((x : ℤ) + 1) - projH p m j t U (x : ℤ) ∧
        projH p m j t U ((x : ℤ) + 1) - projH p m j t U (x : ℤ) ≤ Kp := by
  intro x hx
  set g := x - (runMax p m U j t).toNat with hg
  have hxe : (runMax p m U j t).toNat + g = x := by omega
  have hrecCast : (((runMax p m U j t).toNat : ℕ) : ℤ) = recVal j (prefOf p m t U) := by
    rw [runMax_eq_recVal]
    exact Int.toNat_of_nonneg (zero_le_recVal_prefOf p m U j t)
  have h1 : ((x : ℕ) : ℤ) = recVal j (prefOf p m t U) + (g : ℤ) := by
    conv_lhs => rw [← hxe]
    push_cast
    rw [hrecCast]
  have h2 : ((x : ℕ) : ℤ) + 1 = recVal j (prefOf p m t U) + ((g + 1 : ℕ) : ℤ) := by
    rw [h1]; push_cast; ring
  rw [h2, h1]
  exact ⟨projH_step_above_nonneg hp1 hp2 hcl he1 g,
    projH_step_above_le hp1 hp2 hcl hLK heK g⟩

/-- **The below-record step is exactly the revealed site weight.** -/
theorem projH_step_below_eq {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    {j : Fin N} {t : ℕ} {U : Array N}
    (hbelow : ∀ y : ℤ, y ≤ recVal j (prefOf p m t U) →
      projH p m j t U y = SwarmOcc.Hpot (siteH p m j U) y)
    {x : ℕ} (hx : (x : ℤ) < recVal j (prefOf p m t U)) :
    projH p m j t U ((x : ℤ) + 1) - projH p m j t U (x : ℤ)
      = hof p (siteMarks p m U j) x := by
  have hx1 : (x : ℤ) + 1 ≤ recVal j (prefOf p m t U) := by omega
  have hx0 : (x : ℤ) ≤ recVal j (prefOf p m t U) := le_of_lt hx
  rw [hbelow ((x : ℤ) + 1) hx1, hbelow (x : ℤ) hx0]
  rw [Swarming.Enl.Hpot_succ_sub']
  rw [Swarming.Enl.hZpot_of_nonneg (h := siteH p m j U) (x := (x : ℤ)) (by omega)]
  rfl

/-- `b_n = h_j(M-1)+2` is bounded by the harmonic site cap plus two, on the record cell with the
cap taken on `[A-1, A+Lw)`.  This is the deterministic discharge of the additive defect. -/
theorem bRec_le_succ_cap {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} {j : Fin N}
    {t : ℕ} {U : Array N} {A Mv : ℕ} {V : ℝ} (hA : 1 ≤ A) (hV1 : 1 ≤ V)
    (hrec : A ≤ (recVal j (prefOf p m t U)).toNat ∧
      (recVal j (prefOf p m t U)).toNat < A + Mv)
    (hh : ∀ y ∈ Finset.Ico (A - 1) (A + Mv), hof p (siteMarks p m U j) y ≤ V) :
    bRec p m t j U ≤ V + 2 := by
  have h := QplWindow.HprevAt_le_of_window (N := N) hp1 hp2 (m := m) j (t := t) hA hV1
    (U := U) hrec hh
  simp only [bRec]
  linarith

/-- **The additive defect is absorbed by the paper-scale remainder.**  On the record cell,
`e_0/(1-a) ≤ b_n/(1-a) ≤ (4/(1-a)) L34`. -/
theorem bRec_div_le_L34 {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (L : ℕ)
    {Lw : ℕ} (hLw : 1 ≤ Lw) {j : Fin N} {t : ℕ} {U : Array N}
    (hb : bRec p m t j U ≤ xOf Lw + 2) :
    bRec p m t j U / (1 - aRec p m) ≤ (4 / (1 - aRec p m)) * LocOccCarrier.L34 L Lw := by
  have hden : (0 : ℝ) < 1 - aRec p m := one_sub_aRec_pos hp1 hp2 m
  have hV1 : (1 : ℝ) ≤ xOf Lw := by
    rw [xOf]
    exact Real.one_le_rpow (by exact_mod_cast hLw) (by norm_num)
  have hsq : xOf Lw ^ 2 ≤ LocOccCarrier.L34 L Lw := by
    unfold LocOccCarrier.L34
    have h3 : (0 : ℝ) ≤ 3 * ((betaT (xOf Lw) : ℕ) : ℝ) + (L : ℝ) ^ (3 / 4 : ℝ) := by
      positivity
    linarith
  have hV0 : (0 : ℝ) ≤ xOf Lw := le_trans zero_le_one hV1
  have hkey : xOf Lw + 2 ≤ 4 * LocOccCarrier.L34 L Lw := by
    nlinarith [hsq, hV0, hV1]
  have hinv : (0 : ℝ) ≤ (1 - aRec p m)⁻¹ := le_of_lt (inv_pos.mpr hden)
  have hstep : bRec p m t j U / (1 - aRec p m) ≤ (xOf Lw + 2) / (1 - aRec p m) :=
    div_le_div_of_nonneg_right hb (le_of_lt hden)
  have hstep2 : (xOf Lw + 2) / (1 - aRec p m)
      ≤ (4 / (1 - aRec p m)) * LocOccCarrier.L34 L Lw := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    calc (xOf Lw + 2) * (1 - aRec p m)⁻¹
        ≤ (4 * LocOccCarrier.L34 L Lw) * (1 - aRec p m)⁻¹ :=
          mul_le_mul_of_nonneg_right hkey hinv
      _ = 4 * (1 - aRec p m)⁻¹ * LocOccCarrier.L34 L Lw := by ring
  linarith

end Model

/-! ### 6. The actual `(lococc)` carrier with the summed slope — both slope fields discharged -/

namespace Carrier

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl Swarming.Enl.ProjLedger Swarming.Enl.VdriftAssembly
open SwarmMarks SwarmLogRatio LocSumAct LocOccCarrier
open Model

variable {N : ℕ}

/-- **The paper's `(lococc)` on the actual carrier, with the per-site slope premise replaced by
the summed bound and discharged from the closed form.**

Carrier exactly as in the accepted `LocOccCarrier.lococc_actual_carrier`
(`X = (X^i_u).toNat`, `M^i = runMax i`, `M^j = runMax j`, `h = h_j`,
`wt = h_j^2`, `H_t(y) = projH p m j t U y`, `Z = Zproj`, `J = Jcorr`, `Q = Qpl`), with

* `Kp = Lc p m` — a **constant depending only on `(p,m)`**, not on the array, and
* the single additive defect `Cadd = b_n/(1-a)`, absorbed into `L^{3/4}` via
  `bRec_div_le_L34` (the harmonic site cap `h_j ≤ Lw^{1/16}` on the cell).

No slope hypothesis remains: `hslopeLo`, the per-site nonnegativity and the *summed* upper bound
are all proved here, and the adapted projected `(Vdrift)` ledger (`LocOcc.ae_step_ledger_actual`)
together with the `Zproj` bridge (`ProjLedgerBridge.Zproj_eq_optional_projection`, used at `s` and
`t`) are *discharged* from the accepted a.e. theorems — all on one set of full
`arrayMeasure`-measure.

The remaining hypotheses are exactly the paper's **good-event** conditions, which are
positive-probability (not a.e.) statements and are not available a.e. in the tree:
`(locsum)` on the cell, the `Qpl` window, the projected oscillation window, the record cell
`(d_r ≤ L)` for walkers `i` and `j`, and the `(locmax)` cap `h_j ≤ Lw^{1/16}` on `[A-1, A+Lw)`. -/
theorem lococc_actual_carrier_summed
    {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) {C : ℝ} (hC1 : 1 ≤ C)
    {L : ℕ} (hL : 1 ≤ L) {Lw : ℕ} (hLw : 1 ≤ Lw) {A : ℕ} (hA : 1 ≤ A)
    {s0 n s t : ℕ} (hs0 : s0 ≤ s) (hst : s ≤ t) (htn : t ≤ s0 + n) :
    ∀ᵐ U ∂(arrayMeasure N),
      -- `(locsum)`: the squared-site remainder on the cell
      (∀ a b : ℕ, A ≤ a → b ≤ A + Lw → a ≤ b →
        ∑ x ∈ Finset.Ico a b, (hof p (siteMarks p m U j) x) ^ 2
          ≤ 2 * C * ((b : ℝ) - (a : ℝ)) + 6 * C * ((betaT (xOf Lw) : ℕ) : ℝ)) →
      -- the projected `Qpl` window
      (∀ k : ℕ, k ≤ n →
        |Qpl p m (1 / 8) i j (s0 + k) U - Qpl p m (1 / 8) i j s0 U| < (L : ℝ) ^ (3 / 4 : ℝ)) →
      -- the projected oscillation window
      (∀ u v : ℕ, s0 ≤ u → u ≤ v → v ≤ s0 + n →
        |projH p m j v U ((trajectory p m U u).pos i)
          - projH p m j u U ((trajectory p m U u).pos i)| < (L : ℝ) ^ (3 / 4 : ℝ)) →
      -- the record cell `{d_r <= L}` for walker `i` and the record of walker `j`
      (∀ u : ℕ, s0 ≤ u → u ≤ s0 + n →
        A ≤ ((trajectory p m U u).pos i).toNat ∧ ((trajectory p m U u).pos i).toNat < A + Lw) →
      (∀ u : ℕ, s0 ≤ u → u ≤ s0 + n →
        A ≤ (runMax p m U j u).toNat ∧ (runMax p m U j u).toNat < A + Lw) →
      (A ≤ (runMax p m U i t).toNat ∧ (runMax p m U i t).toNat + 1 ≤ A + Lw) →
      -- `(locmax)` on `[A-1, A+Lw)`: the cap on the boundary site `A-1` is what bounds `b_n`
      (∀ y ∈ Finset.Ico (A - 1) (A + Lw), hof p (siteMarks p m U j) y ≤ xOf Lw) →
      ∑ u ∈ Finset.Ico s t,
          (if (trajectory p m U u).pos i ≤ runMax p m U j u then (1 : ℝ) else 0)
        ≤ ((2 * C + Lc p m) + 2 * CJc p m * (2 * C) + 1) *
            ((((runMax p m U i t).toNat : ℝ) - ((runMax p m U i s).toNat : ℝ))
              + (((runMax p m U i s).toNat : ℝ) - (((trajectory p m U s).pos i).toNat : ℝ))
              + max 0 (((runMax p m U i s).toNat : ℝ) - ((runMax p m U j s).toNat : ℝ)))
          + ((t : ℝ) - (s : ℝ)) / 8
          + (2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 2 + 1
              + 4 / (1 - aRec p m)) * L34 L Lw := by
  filter_upwards [ae_forall_projH_eq_Hpot_of_le_record (N := N) (p := p) hp1 hp2
      (by linarith : p ≠ 0) m t j,
    ae_forall_projH_closed_form (N := N) (p := p) hp1 hp2 m (n := t) j,
    eRec_zero_bounds_ae (N := N) (p := p) hp1 hp2 m (n := t) j,
    LocOcc.ae_step_ledger_actual (N := N) hp1 hp2 hm hij (ε := 1 / 8) (by norm_num),
    Swarming.Enl.ProjLedgerBridge.Zproj_eq_optional_projection (N := N) hp1 hp2 (m := m) s i j
      (eps := 1 / 8) (by norm_num),
    Swarming.Enl.ProjLedgerBridge.Zproj_eq_optional_projection (N := N) hp1 hp2 (m := m) t i j
      (eps := 1 / 8) (by norm_num)]
    with U hbelow hcl hbnd hledger hbrS hbrT
  intro hlsq hqpl hoscGood hcellX hcellMj hcellMi hloc
  -- ### nonnegativity and casts on the window
  have hnonneg : ∀ u : ℕ, s0 ≤ u → u ≤ s0 + n → 0 ≤ (trajectory p m U u).pos i := by
    intro u h1 h2
    have hc := (hcellX u h1 h2).1
    by_contra hcon
    push Not at hcon
    have hzero : ((trajectory p m U u).pos i).toNat = 0 := Int.toNat_eq_zero.mpr (le_of_lt hcon)
    omega
  have hnonneg' : ∀ u : ℕ, s ≤ u → u ≤ t → 0 ≤ (trajectory p m U u).pos i :=
    fun u h1 h2 => hnonneg u (le_trans hs0 h1) (by omega)
  have hcast : ∀ u : ℕ, s0 ≤ u → u ≤ s0 + n →
      ((((trajectory p m U u).pos i).toNat : ℕ) : ℤ) = (trajectory p m U u).pos i :=
    fun u h1 h2 => Int.toNat_of_nonneg (hnonneg u h1 h2)
  have hrecCast : (((runMax p m U j t).toNat : ℕ) : ℤ) = recVal j (prefOf p m t U) := by
    rw [runMax_eq_recVal]
    exact Int.toNat_of_nonneg (zero_le_recVal_prefOf p m U j t)
  -- ### the summed above-record slope fields, from the closed form
  have he1 : 0 ≤ eRec p m t j 0 U := le_trans zero_le_one hbnd.1
  have hslopeLo : ∀ x : ℕ, x < (runMax p m U j t).toNat →
      projH p m j t U ((x + 1 : ℕ) : ℤ) - projH p m j t U ((x : ℕ) : ℤ)
        = hof p (siteMarks p m U j) x := by
    intro x hx
    have hx' : (x : ℤ) < recVal j (prefOf p m t U) := by
      rw [← hrecCast]
      exact_mod_cast hx
    have h := Model.projH_step_below_eq (p := p) (m := m) hp1 hp2 (t := t) (U := U) hbelow hx'
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hslopeHi0 : ∀ x : ℕ, (runMax p m U j t).toNat ≤ x →
      0 ≤ projH p m j t U ((x + 1 : ℕ) : ℤ) - projH p m j t U ((x : ℕ) : ℤ) := by
    intro x hx
    set g := x - (runMax p m U j t).toNat with hg
    have hxe : (runMax p m U j t).toNat + g = x := by omega
    have h1 : ((x : ℕ) : ℤ) = recVal j (prefOf p m t U) + (g : ℤ) := by
      conv_lhs => rw [← hxe]
      push_cast
      rw [hrecCast]
    have h2 : ((x + 1 : ℕ) : ℤ) = recVal j (prefOf p m t U) + ((g + 1 : ℕ) : ℤ) := by
      push_cast
      rw [h1]
      ring
    rw [h2, h1]
    exact Model.projH_step_above_nonneg (p := p) (m := m) hp1 hp2 (t := t) (U := U) hcl he1 g
  have hsumHi : ∀ u w : ℕ, (runMax p m U j t).toNat ≤ u → u ≤ w →
      projH p m j t U ((w : ℕ) : ℤ) - projH p m j t U ((u : ℕ) : ℤ)
        ≤ Lc p m * ((w : ℝ) - (u : ℝ)) + bRec p m t j U / (1 - aRec p m) := by
    intro u w hu huw
    set g1 := u - (runMax p m U j t).toNat with hg1
    set g2 := w - (runMax p m U j t).toNat with hg2
    have hue : (runMax p m U j t).toNat + g1 = u := by omega
    have hwe : (runMax p m U j t).toNat + g2 = w := by omega
    have hg12 : g1 ≤ g2 := by omega
    have h1 : ((u : ℕ) : ℤ) = recVal j (prefOf p m t U) + (g1 : ℤ) := by
      conv_lhs => rw [← hue]
      push_cast
      rw [hrecCast]
    have h2 : ((w : ℕ) : ℤ) = recVal j (prefOf p m t U) + (g2 : ℤ) := by
      conv_lhs => rw [← hwe]
      push_cast
      rw [hrecCast]
    have hR : ((w : ℝ) - (u : ℝ)) = ((g2 : ℝ) - (g1 : ℝ)) := by
      conv_lhs => rw [← hwe, ← hue]
      push_cast
      ring
    have hmain := Model.projH_sum_above_le (p := p) (m := m) hp1 hp2 (t := t) (U := U) hcl he1 hg12
    have hdef : eRec p m t j 0 U / (1 - aRec p m) ≤ bRec p m t j U / (1 - aRec p m) :=
      div_le_div_of_nonneg_right hbnd.2 (le_of_lt (one_sub_aRec_pos hp1 hp2 m))
    rw [hR, h1, h2]
    linarith [hmain, hdef]
  -- ### the additive defect from `b_n` and the `(locmax)` cap
  have hbrec : bRec p m t j U ≤ xOf Lw + 2 := by
    refine Model.bRec_le_succ_cap (p := p) (m := m) hp1 hp2 (j := j) (t := t) (U := U)
      (A := A) (Mv := Lw) (V := xOf Lw) hA ?_ ?_ hloc
    · rw [xOf]
      exact Real.one_le_rpow (by exact_mod_cast hLw) (by norm_num)
    · rw [← runMax_eq_recVal]
      exact hcellMj t (le_trans hs0 hst) htn
  have hCaddL : bRec p m t j U / (1 - aRec p m)
      ≤ (4 / (1 - aRec p m)) * L34 L Lw :=
    Model.bRec_div_le_L34 (p := p) (m := m) (L := L) (Lw := Lw) hp1 hp2 hLw hbrec
  have hCa : (0 : ℝ) ≤ bRec p m t j U / (1 - aRec p m) := by
    have hden : (0 : ℝ) < 1 - aRec p m := one_sub_aRec_pos hp1 hp2 m
    have h3 : (0 : ℝ) < bRec p m t j U := by linarith [Swarming.Enl.three_le_bRec hp1 hp2 m t j U]
    positivity
  -- ### the remaining good-event fields, as in the accepted carrier
  have hCJ0 : (0 : ℝ) ≤ CJc p m := CJc_nonneg hp1 hp2 m
  have hKF0 : (0 : ℝ) ≤ KFc p m := KFc_nonneg hp1 hp2 m
  have hC0 : (0 : ℝ) ≤ C := le_trans zero_le_one hC1
  have hoccP : ∀ u : ℕ, s ≤ u → u < t →
      SwarmOcc.occInd (fun r => (trajectory p m U r).pos i) (fun r => runMax p m U j r) u
        = if ((trajectory p m U u).pos i).toNat ≤ (runMax p m U j u).toNat then (1 : ℝ) else 0 :=
    fun u h1 h2 => LocOccEnd.occInd_eq_toNat_toNat (p := p) m U (hnonneg' u h1 (le_of_lt h2))
  have hcap : ∀ u : ℕ, s0 ≤ u → u ≤ s0 + n →
      (hof p (siteMarks p m U j) ((runMax p m U j u).toNat)) ^ 2 ≤ (xOf Lw) ^ 2 := by
    intro u h1 h2
    have hm := hcellMj u h1 h2
    have hloc' : ∀ y ∈ Finset.Ico A (A + Lw), hof p (siteMarks p m U j) y ≤ xOf Lw := by
      intro y hy
      obtain ⟨hy1, hy2⟩ := Finset.mem_Ico.mp hy
      exact hloc y (Finset.mem_Ico.mpr ⟨by omega, hy2⟩)
    exact hof_sq_record_le (N := N) hp1 hp2 (m := m) (U := U) (j := j) u
      (A := A) (Mv := Lw) (V := xOf Lw) (Real.rpow_nonneg (by positivity) _) hloc'
      (Finset.mem_Ico.mpr ⟨hm.1, hm.2⟩)
  -- ### the two endpoint decompositions
  have hZs : Zproj p m (1 / 8) i j s U
      = projH p m j s U ((((trajectory p m U s).pos i).toNat : ℕ) : ℤ)
        - SwarmOcc.Fcorr (aRec p m) (1 / 8) (bRec p m s j U)
            ((trajectory p m U s).pos i - runMax p m U j s) := by
    rw [← hbrS]
    show Swarming.Enl.Zproj p m (1 / 8) i j U s
      = projH p m j s U ((((trajectory p m U s).pos i).toNat : ℕ) : ℤ)
        - SwarmOcc.Fcorr (aRec p m) (1 / 8) (bRec p m s j U)
            ((trajectory p m U s).pos i - runMax p m U j s)
    rw [hcast s hs0 (by omega)]
    rfl
  have hZt : Zproj p m (1 / 8) i j t U
      = projH p m j t U ((((trajectory p m U t).pos i).toNat : ℕ) : ℤ)
        - SwarmOcc.Fcorr (aRec p m) (1 / 8) (bRec p m t j U)
            ((trajectory p m U t).pos i - runMax p m U j t) := by
    rw [← hbrT]
    show Swarming.Enl.Zproj p m (1 / 8) i j U t
      = projH p m j t U ((((trajectory p m U t).pos i).toNat : ℕ) : ℤ)
        - SwarmOcc.Fcorr (aRec p m) (1 / 8) (bRec p m t j U)
            ((trajectory p m U t).pos i - runMax p m U j t)
    rw [hcast t (le_trans hs0 hst) htn]
    rfl
  -- ### the summed `(lococc)` bound on the `occInd` carrier
  have hcore : ∑ u ∈ Finset.Ico s t,
        SwarmOcc.occInd (fun r => (trajectory p m U r).pos i)
          (fun r => runMax p m U j r) u
      ≤ (2 * C + Lc p m + 2 * CJc p m * (2 * C) + 1) *
            ((((runMax p m U i t).toNat : ℝ) - ((runMax p m U i s).toNat : ℝ))
              + (((runMax p m U i s).toNat : ℝ) - (((trajectory p m U s).pos i).toNat : ℝ))
              + max 0 (((runMax p m U i s).toNat : ℝ) - ((runMax p m U j s).toNat : ℝ)))
          + 1 / 8 * ((t : ℝ) - (s : ℝ))
          + (2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 2 + 1
              + 4 / (1 - aRec p m)) * L34 L Lw :=
    SummedSlope.lococc_summed
      (X := fun u => ((trajectory p m U u).pos i).toNat)
      (Mi := fun u => (runMax p m U i u).toNat)
      (Mj := fun u => (runMax p m U j u).toNat)
      (occ := fun u => SwarmOcc.occInd (fun r => (trajectory p m U r).pos i)
        (fun r => runMax p m U j r) u)
      (J := fun u => Jcorr p m (1 / 8) i j U u)
      (Z := fun u => Zproj p m (1 / 8) i j u U)
      (Q := fun u => Qpl p m (1 / 8) i j u U)
      (H := fun t y => projH p m j t U (y : ℤ))
      (Fs := SwarmOcc.Fcorr (aRec p m) (1 / 8) (bRec p m s j U)
        ((trajectory p m U s).pos i - runMax p m U j s))
      (Ft := SwarmOcc.Fcorr (aRec p m) (1 / 8) (bRec p m t j U)
        ((trajectory p m U t).pos i - runMax p m U j t))
      (h := fun x => hof p (siteMarks p m U j) x)
      (wt := fun x => (hof p (siteMarks p m U j) x) ^ 2)
      (A := A) (Lw := Lw) (K := 2 * C) (β := 3 * ((betaT (xOf Lw) : ℕ) : ℝ))
      (Kp := Lc p m) (CH := 1) (KQ := 2) (KF := KFc p m) (CJ := CJc p m)
      (ε := 1 / 8) (L34 := L34 L Lw) (Cadd := bRec p m t j U / (1 - aRec p m))
      (CaddK := 4 / (1 - aRec p m))
      hst hoccP hledger hZs hZt
      (fun x => LocOccEnd.hof_nonneg hp1 hp2 (siteMarks p m U j) x)
      (fun x => le_refl ((hof p (siteMarks p m U j) x) ^ 2))
      hslopeLo hslopeHi0 hsumHi
      (locsum_hint_wt (p := p) (m := m) (U := U) (j := j) (A := A) (Lw := Lw) (C := C)
        (β := ((betaT (xOf Lw) : ℕ) : ℝ)) hC0 hlsq)
      (by
        have h1 := hoscGood s t hs0 hst htn
        have e1 : (projH p m j t U (((trajectory p m U s).pos i).toNat)
            - projH p m j s U (((trajectory p m U s).pos i).toNat))
            = projH p m j t U ((trajectory p m U s).pos i)
              - projH p m j s U ((trajectory p m U s).pos i) := by
          rw [hcast s hs0 (by omega)]
        rw [e1]
        have h2 : (0 : ℝ) ≤ (L : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (by positivity) _
        have h3 := le_abs_self (projH p m j t U ((trajectory p m U s).pos i)
          - projH p m j s U ((trajectory p m U s).pos i))
        have h4 : (L : ℝ) ^ (3 / 4 : ℝ) ≤ L34 L Lw := L34_lower_rpow L Lw
        linarith [le_of_lt h1, h3, h4, h2])
      (by
        have hs' : s0 + (s - s0) = s := Nat.add_sub_cancel' hs0
        have ht' : s0 + (t - s0) = t := Nat.add_sub_cancel' (le_trans hs0 hst)
        have h1 := hqpl (s - s0) (by omega)
        have h2 := hqpl (t - s0) (by omega)
        rw [hs'] at h1
        rw [ht'] at h2
        have h3 : |Qpl p m (1 / 8) i j t U - Qpl p m (1 / 8) i j s U|
            ≤ |Qpl p m (1 / 8) i j t U - Qpl p m (1 / 8) i j s0 U|
              + |Qpl p m (1 / 8) i j s0 U - Qpl p m (1 / 8) i j s U| := by
          have e : Qpl p m (1 / 8) i j t U - Qpl p m (1 / 8) i j s U
              = (Qpl p m (1 / 8) i j t U - Qpl p m (1 / 8) i j s0 U)
                + (Qpl p m (1 / 8) i j s0 U - Qpl p m (1 / 8) i j s U) := by ring
          calc |Qpl p m (1 / 8) i j t U - Qpl p m (1 / 8) i j s U|
              = |(Qpl p m (1 / 8) i j t U - Qpl p m (1 / 8) i j s0 U)
                + (Qpl p m (1 / 8) i j s0 U - Qpl p m (1 / 8) i j s U)| := by rw [e]
            _ ≤ _ := abs_add_le _ _
        have h4 : |Qpl p m (1 / 8) i j s0 U - Qpl p m (1 / 8) i j s U|
            = |Qpl p m (1 / 8) i j s U - Qpl p m (1 / 8) i j s0 U| := abs_sub_comm _ _
        have h5 := neg_le_abs (Qpl p m (1 / 8) i j t U - Qpl p m (1 / 8) i j s U)
        have h6 : (L : ℝ) ^ (3 / 4 : ℝ) ≤ L34 L Lw := L34_lower_rpow L Lw
        have h7 : (0 : ℝ) ≤ (L : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (by positivity) _
        rw [h4] at h3
        linarith [le_of_lt h2, le_of_lt h1])
      (abs_Fcorr_endpoint_L34 (N := N) hp1 hp2 (m := m) (i := i) (j := j) U s
        (hcap s hs0 (by omega)))
      (abs_Fcorr_endpoint_L34 (N := N) hp1 hp2 (m := m) (i := i) (j := j) U t
        (hcap t (le_trans hs0 hst) htn))
      (fun nx => Jstruct_all (N := N) hp1 hp2 (m := m) (i := i) (j := j) U nx)
      (fun nx => runMax_toNat_mono (le_of_lt (Nat.lt_succ_self nx)))
      (fun nx => runMax_toNat_step nx)
      (fun nx h1 h2 =>
        calc ((trajectory p m U (nx + 1)).pos i).toNat
            ≤ (runMax p m U i (nx + 1)).toNat :=
              pos_toNat_le_runMax (hnonneg' (nx + 1) (by omega) (by omega))
          _ ≤ (runMax p m U i t).toNat := runMax_toNat_mono (by omega))
      (runMax_toNat_mono hst)
      (pos_toNat_le_runMax (hnonneg' s (le_refl s) hst))
      (pos_toNat_le_runMax (hnonneg' t hst (le_refl t)))
      (hcellX s hs0 (by omega)).1
      (hcellMj s hs0 (by omega)).1
      (le_of_lt (hcellX t (le_trans hs0 hst) htn).2)
      hcellMi.2
      (le_of_lt (hcellMj t (le_trans hs0 hst) htn).2)
      (by linarith) (by positivity) (Lc_nonneg hp1 hp2 m) hCJ0 (by norm_num) hKF0 (by norm_num)
      (L34_nonneg L Lw) (one_le_L34 hL) (three_betaT_le_L34 L Lw) hCa hCaddL
  -- ### back to the paper's literal indicator `1{X_u^i <= M_u^j}`
  have hsum : (∑ u ∈ Finset.Ico s t,
        (if (trajectory p m U u).pos i ≤ runMax p m U j u then (1 : ℝ) else 0))
      = ∑ u ∈ Finset.Ico s t,
          SwarmOcc.occInd (fun r => (trajectory p m U r).pos i)
            (fun r => runMax p m U j r) u := by
    refine Finset.sum_congr rfl (fun u hu => ?_)
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hu
    have hnn := hnonneg' u h1 (le_of_lt h2)
    have hiff := LocOccEnd.toNat_le_toNat_iff hnn (zero_le_runMax p m U j u)
    by_cases h : ((trajectory p m U u).pos i).toNat ≤ (runMax p m U j u).toNat
    · have hA1 : (if (trajectory p m U u).pos i ≤ runMax p m U j u then (1 : ℝ) else 0) = 1 :=
        if_pos (hiff.mp h)
      have hB1 : SwarmOcc.occInd (fun r => (trajectory p m U r).pos i)
          (fun r => runMax p m U j r) u = 1 := by rw [hoccP u h1 h2, if_pos h]
      rw [hA1, hB1]
    · have hA0 : (if (trajectory p m U u).pos i ≤ runMax p m U j u then (1 : ℝ) else 0) = 0 :=
        if_neg (fun hc => h (hiff.mpr hc))
      have hB0 : SwarmOcc.occInd (fun r => (trajectory p m U r).pos i)
          (fun r => runMax p m U j r) u = 0 := by rw [hoccP u h1 h2, if_neg h]
      rw [hA0, hB0]
  rw [hsum]
  have hcoef : (1 / 8 : ℝ) * ((t : ℝ) - (s : ℝ)) = ((t : ℝ) - (s : ℝ)) / 8 := by ring
  rw [hcoef] at hcore
  exact hcore

/-- **The exception set is null.**  The measure-theoretic content of
`lococc_actual_carrier_summed`: the set of arrays on which the good-event hypotheses hold but the
`(lococc)` display fails is `arrayMeasure`-null.  (`MeasureTheory.ae_iff` states precisely that the
`∀ᵐ` of the carrier theorem is this null-set assertion; the sample space is the actual iid array
space `(Array N, arrayMeasure N)`, not an abstract probability space.) -/
theorem carrier_exception_null
    {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) {C : ℝ} (hC1 : 1 ≤ C)
    {L : ℕ} (hL : 1 ≤ L) {Lw : ℕ} (hLw : 1 ≤ Lw) {A : ℕ} (hA : 1 ≤ A)
    {s0 n s t : ℕ} (hs0 : s0 ≤ s) (hst : s ≤ t) (htn : t ≤ s0 + n) :
    arrayMeasure N {U | ¬ (
      -- `(locsum)`: the squared-site remainder on the cell
      (∀ a b : ℕ, A ≤ a → b ≤ A + Lw → a ≤ b →
        ∑ x ∈ Finset.Ico a b, (hof p (siteMarks p m U j) x) ^ 2
          ≤ 2 * C * ((b : ℝ) - (a : ℝ)) + 6 * C * ((betaT (xOf Lw) : ℕ) : ℝ)) →
      -- the projected `Qpl` window
      (∀ k : ℕ, k ≤ n →
        |Qpl p m (1 / 8) i j (s0 + k) U - Qpl p m (1 / 8) i j s0 U| < (L : ℝ) ^ (3 / 4 : ℝ)) →
      -- the projected oscillation window
      (∀ u v : ℕ, s0 ≤ u → u ≤ v → v ≤ s0 + n →
        |projH p m j v U ((trajectory p m U u).pos i)
          - projH p m j u U ((trajectory p m U u).pos i)| < (L : ℝ) ^ (3 / 4 : ℝ)) →
      -- the record cell `{d_r <= L}` for walker `i` and the record of walker `j`
      (∀ u : ℕ, s0 ≤ u → u ≤ s0 + n →
        A ≤ ((trajectory p m U u).pos i).toNat ∧ ((trajectory p m U u).pos i).toNat < A + Lw) →
      (∀ u : ℕ, s0 ≤ u → u ≤ s0 + n →
        A ≤ (runMax p m U j u).toNat ∧ (runMax p m U j u).toNat < A + Lw) →
      (A ≤ (runMax p m U i t).toNat ∧ (runMax p m U i t).toNat + 1 ≤ A + Lw) →
      -- `(locmax)` on `[A-1, A+Lw)`: the cap on the boundary site `A-1` is what bounds `b_n`
      (∀ y ∈ Finset.Ico (A - 1) (A + Lw), hof p (siteMarks p m U j) y ≤ xOf Lw) →
      ∑ u ∈ Finset.Ico s t,
          (if (trajectory p m U u).pos i ≤ runMax p m U j u then (1 : ℝ) else 0)
        ≤ ((2 * C + Lc p m) + 2 * CJc p m * (2 * C) + 1) *
            ((((runMax p m U i t).toNat : ℝ) - ((runMax p m U i s).toNat : ℝ))
              + (((runMax p m U i s).toNat : ℝ) - (((trajectory p m U s).pos i).toNat : ℝ))
              + max 0 (((runMax p m U i s).toNat : ℝ) - ((runMax p m U j s).toNat : ℝ)))
          + ((t : ℝ) - (s : ℝ)) / 8
          + (2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 2 + 1
              + 4 / (1 - aRec p m)) * L34 L Lw)} = 0 := by
  rw [← MeasureTheory.ae_iff]
  exact lococc_actual_carrier_summed hp1 hp2 hm hij hC1 hL hLw hA hs0 hst htn

end Carrier
