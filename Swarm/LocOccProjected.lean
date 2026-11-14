/-
  # `(lococc)` on an explicit good record window

      sum_{u=s}^{t-1} 1{X_u^i <= M_u^j}
        <= C (M_t^i - M_s^i + M_s^i - X_s^i + (M_s^i - M_s^j)_+) + (t-s)/8 + C_T L^{3/4}

  for all integers `tau_r <= s <= t <= tau_r + floor (T L)` on `G_{r,L,T} ∩ {d_r <= L}`.

  No `sorry`, no `axiom`, no `native_decide`, no Poissonisation.
-/
import Swarm.Imports

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace LocOcc

open Finset

/-! ### 0. Telescoping helpers for `Finset.Ico` on `ℕ` -/

/-- Shifted `Ico` sum: `sum_{a <= x < b} f (x+1) = sum_{a+1 <= x < b+1} f x`. -/
theorem sum_Ico_shift_index {f : ℕ → ℝ} {a b : ℕ} :
    ∑ x ∈ Finset.Ico a b, f (x + 1) = ∑ x ∈ Finset.Ico (a + 1) (b + 1), f x := by
  rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  have h1 : b + 1 - (a + 1) = b - a := by omega
  rw [h1]
  exact Finset.sum_congr rfl fun k _ => by rw [Nat.add_right_comm]

/-- Telescoping: `sum_{a <= x < b} (f (x+1) - f x) = f b - f a` for `a <= b`. -/
theorem sum_Ico_telescope {f : ℕ → ℝ} {a b : ℕ} (hab : a ≤ b) :
    ∑ x ∈ Finset.Ico a b, (f (x + 1) - f x) = f b - f a :=
  Finset.sum_Ico_sub f hab

/-! ### 1. The window form of the summed drift ledger

`(Vdrift)` is `1{0 <= X_u^i <= M_u^j} - eps <= E[Z_{u+1} - Z_u + J_{u+1} | F_u]`, and `Q` is the
compensator `Q_n = sum_{u<n} ((Z_{u+1}-Z_u+J_{u+1}) - E[...|F_u])`, so the conditional mean on
the right *is* `(Z_{u+1}-Z_u) + J_{u+1} - (Q_{u+1}-Q_u)`.  Summing over the window gives the
paper's first display in the proof of `(lococc)`; no probability enters. -/

/-- **Summation of `(Vdrift)` over the window.** -/
theorem window_le_of_step {occ J Z Q : ℕ → ℝ} {ε : ℝ} {s t : ℕ} (hst : s ≤ t)
    (hstep : ∀ u, occ u - ε ≤ (Z (u + 1) - Z u) + J u - (Q (u + 1) - Q u)) :
    ∑ u ∈ Finset.Ico s t, occ u
      ≤ ε * ((t : ℝ) - (s : ℝ)) + (Z t - Z s) + (∑ u ∈ Finset.Ico s t, J u) - (Q t - Q s) := by
  have hsum : ∑ u ∈ Finset.Ico s t, (occ u - ε)
      ≤ ∑ u ∈ Finset.Ico s t, ((Z (u + 1) - Z u) + J u - (Q (u + 1) - Q u)) :=
    Finset.sum_le_sum fun u _ => hstep u
  have hleft : ∑ u ∈ Finset.Ico s t, (occ u - ε)
      = (∑ u ∈ Finset.Ico s t, occ u) - ε * ((t : ℝ) - (s : ℝ)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
      Nat.cast_sub hst]
    ring
  have hZ : ∑ u ∈ Finset.Ico s t, (Z (u + 1) - Z u) = Z t - Z s := sum_Ico_telescope hst
  have hQ : ∑ u ∈ Finset.Ico s t, (Q (u + 1) - Q u) = Q t - Q s := sum_Ico_telescope hst
  have hright : ∑ u ∈ Finset.Ico s t, ((Z (u + 1) - Z u) + J u - (Q (u + 1) - Q u))
      = (Z t - Z s) + (∑ u ∈ Finset.Ico s t, J u) - (Q t - Q s) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hZ, hQ]
  rw [hleft, hright] at hsum
  linarith

/-! ### 2. The record-cost (`J`) bound with walker `i`'s running maximum as spatial index -/

/-- **Advance indices are injective.**  If `r` is nondecreasing and increases by at most one per
step, two record advances with the same value of `r` are the same step. -/
theorem advance_inj {r : ℕ → ℕ} (hmono : ∀ n, r n ≤ r (n + 1))
    (hstep : ∀ n, r (n + 1) ≤ r n + 1) {a b : ℕ} (hab : a < b)
    (ha : r (a + 1) = r a + 1) (hb : r (b + 1) = r b + 1) : r a ≠ r b := by
  intro heq
  have hmono' : Monotone r := monotone_nat_of_le_succ hmono
  have h1 : r (a + 1) ≤ r b := hmono' (by omega)
  have h2 : r a + 1 ≤ r b := by rw [← ha]; exact h1
  omega

/-- **`(Jbound)` on the window.**  For a nondecreasing unit-step record `r`, record costs
supported on the paper's event `{r_{u+1} = r_u + 1, X_{u+1} > r_u}`, and positions of walker `i`
bounded by `W` up to time `t`,

    `sum_{u in [s,t)} |J_u| <= 2 CJ sum_{x in [r_s, W+1)} wt x`.

The point is the spatial index: the advance values `r_u` and their successors `r_u + 1` are
distinct and lie below `W`, the running maximum of **walker `i`**. -/
theorem jsum_le_window {r : ℕ → ℕ} {X : ℕ → ℤ} {wt : ℕ → ℝ} {CJ : ℝ} {J : ℕ → ℝ} {s t W : ℕ}
    (hmono : ∀ n, r n ≤ r (n + 1)) (hstep : ∀ n, r (n + 1) ≤ r n + 1)
    (hwt : ∀ x, 0 ≤ wt x) (hCJ : 0 ≤ CJ)
    (hJ : ∀ n, |J n| ≤ CJ * (wt (r n) + wt (r n + 1)) *
      (if r (n + 1) = r n + 1 ∧ (r n : ℤ) < X (n + 1) then 1 else 0))
    (hst : s ≤ t) (hX : ∀ n, s ≤ n → n < t → X (n + 1) ≤ (W : ℤ)) :
    ∑ n ∈ Finset.Ico s t, |J n| ≤ 2 * CJ * ∑ x ∈ Finset.Ico (r s) (W + 1), wt x := by
  classical
  set S : Finset ℕ := (Finset.Ico s t).filter
    (fun n => r (n + 1) = r n + 1 ∧ (r n : ℤ) < X (n + 1)) with hS
  -- (1) the sum is supported on `S`
  have hstep1 : ∑ n ∈ Finset.Ico s t, |J n| ≤ CJ * ∑ n ∈ S, (wt (r n) + wt (r n + 1)) := by
    have h1 : ∑ n ∈ Finset.Ico s t, |J n|
        ≤ ∑ n ∈ Finset.Ico s t, CJ * (wt (r n) + wt (r n + 1)) *
            (if r (n + 1) = r n + 1 ∧ (r n : ℤ) < X (n + 1) then 1 else 0) :=
      Finset.sum_le_sum fun n _ => hJ n
    have h2 : ∑ n ∈ Finset.Ico s t, CJ * (wt (r n) + wt (r n + 1)) *
            (if r (n + 1) = r n + 1 ∧ (r n : ℤ) < X (n + 1) then 1 else 0)
        = CJ * ∑ n ∈ S, (wt (r n) + wt (r n + 1)) := by
      rw [hS, Finset.sum_filter, Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by
        by_cases hh : r (n + 1) = r n + 1 ∧ (r n : ℤ) < X (n + 1) <;> simp [hh]
    rw [h2] at h1
    exact h1
  -- (2) every advance value lies below `W`
  have hlt : ∀ n ∈ S, r n < W := by
    intro n hn
    obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.mp hn
    have h4 : n < t := (Finset.mem_Ico.mp h1).2
    have h5 : s ≤ n := (Finset.mem_Ico.mp h1).1
    have h6 : X (n + 1) ≤ (W : ℤ) := hX n h5 h4
    omega
  have hmono' : Monotone r := monotone_nat_of_le_succ hmono
  -- (3) `n |-> r n` is injective on `S`
  have hinj : ∀ a ∈ S, ∀ b ∈ S, r a = r b → a = b := by
    intro a ha b hb heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt' | hgt'
    · have h1 : r (a + 1) = r a + 1 := (Finset.mem_filter.mp ha).2.1
      have h2 : r (b + 1) = r b + 1 := (Finset.mem_filter.mp hb).2.1
      exact advance_inj hmono hstep hlt' h1 h2 heq
    · have h1 : r (b + 1) = r b + 1 := (Finset.mem_filter.mp hb).2.1
      have h2 : r (a + 1) = r a + 1 := (Finset.mem_filter.mp ha).2.1
      exact advance_inj hmono hstep hgt' h1 h2 heq.symm
  have hinj' : ∀ a ∈ S, ∀ b ∈ S, r a + 1 = r b + 1 → a = b := by
    intro a ha b hb h
    exact hinj a ha b hb (by omega)
  have himg1 : ∑ n ∈ S, wt (r n) = ∑ x ∈ S.image r, wt x := (Finset.sum_image hinj).symm
  have himg2 : ∑ n ∈ S, wt (r n + 1) = ∑ x ∈ S.image (fun n => r n + 1), wt x :=
    (Finset.sum_image hinj').symm
  have hsub1 : S.image r ⊆ Finset.Ico (r s) (W + 1) := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    have hns : s ≤ n := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1).1
    exact Finset.mem_Ico.mpr ⟨hmono' hns, Nat.lt_succ_of_lt (hlt n hn)⟩
  have hsub2 : S.image (fun n => r n + 1) ⊆ Finset.Ico (r s) (W + 1) := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    have hns : s ≤ n := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1).1
    exact Finset.mem_Ico.mpr ⟨by have := hmono' hns; omega,
      Nat.succ_lt_succ (hlt n hn)⟩
  have hG : (0 : ℝ) ≤ ∑ x ∈ Finset.Ico (r s) (W + 1), wt x :=
    Finset.sum_nonneg fun x _ => hwt x
  have hb1 : ∑ x ∈ S.image r, wt x ≤ ∑ x ∈ Finset.Ico (r s) (W + 1), wt x :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub1 fun x _ _ => hwt x
  have hb2 : ∑ x ∈ S.image (fun n => r n + 1), wt x ≤ ∑ x ∈ Finset.Ico (r s) (W + 1), wt x :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub2 fun x _ _ => hwt x
  have hsplit : ∑ n ∈ S, (wt (r n) + wt (r n + 1))
      = (∑ n ∈ S, wt (r n)) + (∑ n ∈ S, wt (r n + 1)) := Finset.sum_add_distrib
  rw [hsplit, himg1, himg2] at hstep1
  nlinarith [hstep1, hb1, hb2, hG, hCJ]

/-- Consecutive half-open sums add: `sum_{[a,b)} + sum_{[b,c)} = sum_{[a,c)}`. -/
theorem sum_Ico_split {f : ℕ → ℝ} {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    (∑ x ∈ Finset.Ico a b, f x) + (∑ x ∈ Finset.Ico b c, f x) = ∑ x ∈ Finset.Ico a c, f x :=
  Finset.sum_Ico_consecutive f hab hbc

/-! ### 3. From the `h^2` window sum to the projected potential's spatial increment -/

/-- **The `h`-sum from the `h^2`-sum.**  `1 <= h` and `h <= h^2`, so on a window where the
`(locsum)` square sum is `K (b-a) + K β` the first power sum has the same bound. -/
theorem hsum_le_of_hsq {h : ℕ → ℝ} {a b : ℕ} {K β : ℝ}
    (hh : ∀ x, 0 ≤ h x) (hK : 1 ≤ K) (hβ : 0 ≤ β) (hab : a ≤ b)
    (hsq : ∑ x ∈ Finset.Ico a b, (h x)^2 ≤ K * ((b : ℝ) - (a : ℝ)) + K * β) :
    ∑ x ∈ Finset.Ico a b, h x ≤ K * ((b : ℝ) - (a : ℝ)) + K * β := by
  have hlen : (0 : ℝ) ≤ (b : ℝ) - (a : ℝ) := by
    have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    linarith
  have hcard : ((Finset.Ico a b).card : ℝ) = (b : ℝ) - (a : ℝ) := by
    rw [Nat.card_Ico, Nat.cast_sub hab]
  have h2 : ∑ x ∈ Finset.Ico a b, h x
      ≤ (1 / 2) * (∑ x ∈ Finset.Ico a b, (h x)^2 + ((Finset.Ico a b).card : ℝ)) := by
    have hpt : ∀ x ∈ Finset.Ico a b, h x
        ≤ (1 / 2) * ((h x)^2 + 1) := by
      intro x _
      nlinarith [hh x, sq_nonneg (h x - 1)]
    calc ∑ x ∈ Finset.Ico a b, h x
        ≤ ∑ x ∈ Finset.Ico a b, (1 / 2) * ((h x)^2 + 1) := Finset.sum_le_sum hpt
      _ = (1 / 2) * (∑ x ∈ Finset.Ico a b, (h x)^2 + ((Finset.Ico a b).card : ℝ)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hcard] at h2
  nlinarith [h2, hsq, hlen, hβ, hK]

/-- **Spatial increment of the projected potential.**

Below the record `xv` the projected potential `H` has the exact paper slope `(projh)`/`(projH)`
increment `H (x+1) - H x = h x` (so the increment is the site weight), and above the record the
slope is at most the `(projH)` slope bound `Kp`.  Then over any interval the increment of `H` is at
most `(K + Kp) * max 0 (v - u) + K β` where `K β` is the `(locsum)` remainder. -/
theorem hdiff_le {H h : ℕ → ℝ} {xv u v : ℕ} {K β Kp : ℝ}
    (hh : ∀ x, 0 ≤ h x) (hK : 1 ≤ K) (hβ : 0 ≤ β) (hKp : 0 ≤ Kp)
    (hslopeLo : ∀ x, x < xv → H (x + 1) - H x = h x)
    (hslopeHi : ∀ x, xv ≤ x → 0 ≤ H (x + 1) - H x ∧ H (x + 1) - H x ≤ Kp)
    {A Lw : ℕ}
    (hsq : ∀ a b : ℕ, A ≤ a → b ≤ A + Lw → a ≤ b →
      ∑ x ∈ Finset.Ico a b, (h x)^2 ≤ K * ((b : ℝ) - (a : ℝ)) + K * β)
    (hAle : A ≤ u) (hLw : min v xv ≤ A + Lw) :
    H v - H u ≤ (K + Kp) * max 0 ((v : ℝ) - (u : ℝ)) + K * β := by
  have hmonoH : Monotone H := by
    refine monotone_nat_of_le_succ fun x => ?_
    rcases lt_or_ge x xv with hx | hx
    · have h := hslopeLo x hx
      linarith [hh x]
    · linarith [(hslopeHi x hx).1]
  rcases le_or_gt v u with hvu | huv
  · have hle : H v - H u ≤ 0 := by have := hmonoH hvu; linarith
    have hnn : (0 : ℝ) ≤ max 0 ((v : ℝ) - (u : ℝ)) := le_max_left _ _
    have : (0 : ℝ) ≤ (K + Kp) * max 0 ((v : ℝ) - (u : ℝ)) + K * β := by
      have h1 : (0 : ℝ) ≤ K + Kp := by linarith
      have h2 : (0 : ℝ) ≤ K * β := by positivity
      nlinarith
    linarith
  · have huvle : u ≤ v := le_of_lt huv
    have htel : ∑ x ∈ Finset.Ico u v, (H (x + 1) - H x) = H v - H u :=
      sum_Ico_telescope huvle
    have hvu_pos : (0 : ℝ) ≤ (v : ℝ) - (u : ℝ) := by
      have : (u : ℝ) ≤ (v : ℝ) := by exact_mod_cast huvle
      linarith
    have hmax : max 0 ((v : ℝ) - (u : ℝ)) = (v : ℝ) - (u : ℝ) := max_eq_right hvu_pos
    rw [← htel, hmax]
    rcases lt_or_ge xv u with hx | hx
    · -- entirely above the record: every slope is at most `Kp`
      have hpt : ∀ x ∈ Finset.Ico u v, H (x + 1) - H x ≤ Kp :=
        fun x hx' => (hslopeHi x (by have := (Finset.mem_Ico.mp hx').1; omega)).2
      have hsum : ∑ x ∈ Finset.Ico u v, (H (x + 1) - H x) ≤ Kp * ((v : ℝ) - (u : ℝ)) := by
        calc ∑ x ∈ Finset.Ico u v, (H (x + 1) - H x) ≤ ∑ _x ∈ Finset.Ico u v, Kp :=
              Finset.sum_le_sum hpt
          _ = Kp * ((v : ℝ) - (u : ℝ)) := by
              rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub huvle, mul_comm]
      have h1 : (0 : ℝ) ≤ K * ((v : ℝ) - (u : ℝ)) := by
        have := hK; nlinarith
      nlinarith [hsum, h1, hβ, hKp]
    · -- split at the record
      have hmin : u ≤ min v xv := le_min huvle hx
      have hminv : min v xv ≤ v := min_le_left _ _
      have hlow : ∑ x ∈ Finset.Ico u (min v xv), (H (x + 1) - H x)
          ≤ K * (((min v xv : ℕ) : ℝ) - (u : ℝ)) + K * β := by
        have hcongr : ∑ x ∈ Finset.Ico u (min v xv), (H (x + 1) - H x)
            = ∑ x ∈ Finset.Ico u (min v xv), h x := by
          refine Finset.sum_congr rfl fun x hx' => ?_
          rw [hslopeLo x (by have := (Finset.mem_Ico.mp hx').2; omega)]
        rw [hcongr]
        exact hsum_le_of_hsq hh hK hβ hmin (hsq u (min v xv) hAle hLw hmin)
      have hhigh : ∑ x ∈ Finset.Ico (min v xv) v, (H (x + 1) - H x)
          ≤ Kp * (((v : ℕ) : ℝ) - ((min v xv : ℕ) : ℝ)) := by
        by_cases hcase : v ≤ xv
        · have : min v xv = v := min_eq_left hcase
          have hI : Finset.Ico (min v xv) v = ∅ := by rw [this, Finset.Ico_self]
          rw [hI, Finset.sum_empty]
          have hsub : ((v : ℝ) - ((min v xv : ℕ) : ℝ)) = 0 := by rw [this]; simp
          rw [hsub, mul_zero]
        · rw [not_le] at hcase
          have hminx : min v xv = xv := min_eq_right (le_of_lt hcase)
          have hpt : ∀ x ∈ Finset.Ico (min v xv) v, H (x + 1) - H x ≤ Kp := by
            intro x hx'
            rw [hminx] at hx'
            exact (hslopeHi x (Finset.mem_Ico.mp hx').1).2
          calc ∑ x ∈ Finset.Ico (min v xv) v, (H (x + 1) - H x) ≤ ∑ _x ∈ Finset.Ico (min v xv) v, Kp :=
                Finset.sum_le_sum hpt
            _ = Kp * (((v : ℕ) : ℝ) - ((min v xv : ℕ) : ℝ)) := by
                rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hminv, mul_comm]
      have hsum : ∑ x ∈ Finset.Ico u v, (H (x + 1) - H x)
          = (∑ x ∈ Finset.Ico u (min v xv), (H (x + 1) - H x))
            + (∑ x ∈ Finset.Ico (min v xv) v, (H (x + 1) - H x)) :=
        (sum_Ico_split hmin hminv).symm
      have harith : (((min v xv : ℕ) : ℝ) - (u : ℝ)) + (((v : ℕ) : ℝ) - ((min v xv : ℕ) : ℝ))
          = (v : ℝ) - (u : ℝ) := by
        have h1 : (u : ℝ) ≤ ((min v xv : ℕ) : ℝ) := by exact_mod_cast hmin
        have h2 : ((min v xv : ℕ) : ℝ) ≤ (v : ℝ) := by exact_mod_cast hminv
        ring
      have hK0 : (0 : ℝ) ≤ K := by linarith
      have ha : (0 : ℝ) ≤ ((min v xv : ℕ) : ℝ) - (u : ℝ) := by
        have : (u : ℝ) ≤ ((min v xv : ℕ) : ℝ) := by exact_mod_cast hmin
        linarith
      have hb : (0 : ℝ) ≤ (v : ℝ) - ((min v xv : ℕ) : ℝ) := by
        have : ((min v xv : ℕ) : ℝ) ≤ (v : ℝ) := by exact_mod_cast hminv
        linarith
      have hKB : (0 : ℝ) ≤ K * β := by positivity
      nlinarith [hlow, hhigh, hsum, harith, hK0, hKp, ha, hb, hKB]

/-! ### 4. The potential part `Z_t - Z_s` -/

/-- **`Z_t - Z_s` on the window.**  Decomposition
`H_{j,t}(X_t^i) - H_{j,s}(X_s^i) = [H_{j,t}(X_t^i) - H_{j,t}(X_s^i)] + [H_{j,t}(X_s^i) - H_{j,s}(X_s^i)]`. -/
theorem zdiff_le {Z : ℕ → ℝ} {H : ℕ → ℕ → ℝ} {h wt : ℕ → ℝ} {X Mt : ℕ → ℕ} {Fs Ft : ℝ}
    {s t : ℕ} {A Lw : ℕ} {K β Kp CH KF L34 : ℝ}
    (hZs : Z s = H s (X s) - Fs) (hZt : Z t = H t (X t) - Ft)
    (hh : ∀ x, 0 ≤ h x) (hhw : ∀ x, (h x) ^ 2 ≤ wt x)
    (hK : 1 ≤ K) (hβ : 0 ≤ β) (hKp : 0 ≤ Kp)
    (hslopeLo : ∀ x, x < Mt t → H t (x + 1) - H t x = h x)
    (hslopeHi : ∀ x, Mt t ≤ x → 0 ≤ H t (x + 1) - H t x ∧ H t (x + 1) - H t x ≤ Kp)
    (hint : ∀ a b : ℕ, A ≤ a → b ≤ A + Lw → a ≤ b →
      ∑ x ∈ Finset.Ico a b, wt x ≤ K * ((b : ℝ) - (a : ℝ)) + K * β)
    (hAle : A ≤ X s) (hLwmax : min (X t) (Mt t) ≤ A + Lw)
    (hosc : H t (X s) - H s (X s) ≤ CH * L34)
    (hFs : |Fs| ≤ KF * L34) (hFt : |Ft| ≤ KF * L34) :
    Z t - Z s ≤ (K + Kp) * max 0 ((X t : ℝ) - (X s : ℝ)) + K * β + CH * L34 + 2 * (KF * L34) := by
  have hspat : H t (X t) - H t (X s)
      ≤ (K + Kp) * max 0 ((X t : ℝ) - (X s : ℝ)) + K * β := by
    refine hdiff_le (xv := Mt t) (u := X s) (v := X t) hh hK hβ hKp hslopeLo hslopeHi
      (fun a b ha hb hab => le_trans (Finset.sum_le_sum (fun x _ => hhw x)) (hint a b ha hb hab))
      hAle hLwmax
  have hF : Fs - Ft ≤ KF * L34 + KF * L34 := by
    have h1 : Fs ≤ KF * L34 := (abs_le.mp hFs).2
    have h2 : -(KF * L34) ≤ Ft := (abs_le.mp hFt).1
    linarith
  have h1 : Z t - Z s = (H t (X t) - H t (X s)) + (H t (X s) - H s (X s)) + (Fs - Ft) := by
    rw [hZs, hZt]; ring
  linarith [hspat, hosc, hF]

/-! ### 5. `(lococc)` on the explicit good record window -/

/-- **`(lococc)` on the good record window.**

On the window `[A, A+Lw]` (the paper's `[r-(T+2)L, r+(T+2)L]`), under the good-event conditions
listed in the module header, for all `s <= t` in the window

    sum_{u=s}^{t-1} 1{X_u^i <= M_u^j}
      <= C (M_t^i - M_s^i + M_s^i - X_s^i + (M_s^i - M_s^j)_+) + eps (t-s) + C_T L^{3/4}

with `C = (K+Kp) + 2 CJ K + 1` and `C_T = K + CH + 2 KF + 4 CJ K + 2 KQ + 1`. -/
theorem lococc_window {X Mi Mj : ℕ → ℕ} {occ J Z Q : ℕ → ℝ} {H : ℕ → ℕ → ℝ} {Fs Ft : ℝ}
    {h wt : ℕ → ℝ} {s t A Lw : ℕ} {K β Kp CH KQ KF CJ ε L34 : ℝ}
    (hst : s ≤ t)
    (hocc : ∀ u, s ≤ u → u < t → occ u = if X u ≤ Mj u then (1 : ℝ) else 0)
    (hled : ∀ u, occ u - ε ≤ (Z (u + 1) - Z u) + J u - (Q (u + 1) - Q u))
    (hZs : Z s = H s (X s) - Fs) (hZt : Z t = H t (X t) - Ft)
    (hh : ∀ x, 0 ≤ h x) (hhw : ∀ x, (h x) ^ 2 ≤ wt x)
    (hslopeLo : ∀ x, x < Mj t → H t (x + 1) - H t x = h x)
    (hslopeHi : ∀ x, Mj t ≤ x → 0 ≤ H t (x + 1) - H t x ∧ H t (x + 1) - H t x ≤ Kp)
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
    (hL34 : 0 ≤ L34) (h1L34 : 1 ≤ L34) (hβL : β ≤ L34) :
    ∑ u ∈ Finset.Ico s t, occ u
      ≤ ((K + Kp) + 2 * CJ * K + 1) *
          (((Mi t : ℝ) - (Mi s : ℝ)) + ((Mi s : ℝ) - (X s : ℝ))
            + max 0 ((Mi s : ℝ) - (Mj s : ℝ)))
        + ε * ((t : ℝ) - (s : ℝ))
        + (K + CH + 2 * KF + 4 * CJ * K + 2 * KQ + 1) * L34 := by
  -- (1) the summed ledger
  have h1 : ∑ u ∈ Finset.Ico s t, occ u
      ≤ ε * ((t : ℝ) - (s : ℝ)) + (Z t - Z s) + (∑ u ∈ Finset.Ico s t, J u) - (Q t - Q s) :=
    window_le_of_step hst hled
  -- (2) the record cost
  have hJsum : ∑ u ∈ Finset.Ico s t, J u ≤ ∑ u ∈ Finset.Ico s t, |J u| :=
    Finset.sum_le_sum fun u _ => le_abs_self (J u)
  have hJb : ∑ u ∈ Finset.Ico s t, |J u|
      ≤ 2 * CJ * ∑ x ∈ Finset.Ico (Mj s) (Mi t + 1), wt x := by
    refine jsum_le_window (X := fun n => ((X n : ℕ) : ℤ)) hMjmono hMjstep
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
  -- (3) the potential part
  have hZ : Z t - Z s ≤ (K + Kp) * max 0 ((X t : ℝ) - (X s : ℝ)) + K * β + CH * L34
      + 2 * (KF * L34) :=
    zdiff_le hZs hZt hh hhw hK hβ hKp hslopeLo hslopeHi hint hcont1
      (le_trans (min_le_right _ _) hcont5) hosc hFs hFt
  -- (4) `(X_t - X_s)_+ <= (M^i_t - M^i_s) + (M^i_s - X_s)`
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
  -- (5) the spatial index of the record cost
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
  -- (6) nonnegativity of the reporting terms
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
  -- (7) the potential part with the reporting term
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
          + max 0 ((Mi s : ℝ) - (Mj s : ℝ))) + (K + CH + 2 * KF) * L34 := by
    have h0K : (0 : ℝ) ≤ K := by linarith
    have h4 : K * β ≤ K * L34 := mul_le_mul_of_nonneg_left hβL h0K
    have h5 : CH * L34 + 2 * (KF * L34) = (CH + 2 * KF) * L34 := by ring
    nlinarith [hZ, hZa, h4, h5]
  -- (8) the record cost with the reporting term
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
  -- (9) assembly
  have hmain : ∑ u ∈ Finset.Ico s t, occ u
      ≤ ε * ((t : ℝ) - (s : ℝ))
        + ((K + Kp) + 2 * CJ * K) * (((Mi t : ℝ) - (Mi s : ℝ)) + ((Mi s : ℝ) - (X s : ℝ))
            + max 0 ((Mi s : ℝ) - (Mj s : ℝ)))
        + (K + CH + 2 * KF + 4 * CJ * K + 2 * KQ) * L34 := by
    nlinarith [h1, hJsum, hJtot, hZtot, hQ, hG0, hL34]
  have hCeq : ((K + Kp) + 2 * CJ * K) * (((Mi t : ℝ) - (Mi s : ℝ)) + ((Mi s : ℝ) - (X s : ℝ))
        + max 0 ((Mi s : ℝ) - (Mj s : ℝ)))
      ≤ ((K + Kp) + 2 * CJ * K + 1) * (((Mi t : ℝ) - (Mi s : ℝ)) + ((Mi s : ℝ) - (X s : ℝ))
        + max 0 ((Mi s : ℝ) - (Mj s : ℝ))) := by
    nlinarith [hG0]
  have hReq : (K + CH + 2 * KF + 4 * CJ * K + 2 * KQ) * L34
      ≤ (K + CH + 2 * KF + 4 * CJ * K + 2 * KQ + 1) * L34 := by
    nlinarith [hL34]
  linarith [hmain, hCeq, hReq]

/-- **The paper's `(lococc)` display**, with `eps = 1/8` written as `(t-s)/8`:

    `sum_{u=s}^{t-1} 1{X_u^i <= M_u^j} <= C (...) + (t-s)/8 + C_T L^{3/4}`. -/
theorem lococc_window_eighth {X Mi Mj : ℕ → ℕ} {occ J Z Q : ℕ → ℝ} {H : ℕ → ℕ → ℝ} {Fs Ft : ℝ}
    {h wt : ℕ → ℝ} {s t A Lw : ℕ} {K β Kp CH KQ KF CJ L34 : ℝ}
    (hst : s ≤ t)
    (hocc : ∀ u, s ≤ u → u < t → occ u = if X u ≤ Mj u then (1 : ℝ) else 0)
    (hled : ∀ u, occ u - 1 / 8 ≤ (Z (u + 1) - Z u) + J u - (Q (u + 1) - Q u))
    (hZs : Z s = H s (X s) - Fs) (hZt : Z t = H t (X t) - Ft)
    (hh : ∀ x, 0 ≤ h x) (hhw : ∀ x, (h x) ^ 2 ≤ wt x)
    (hslopeLo : ∀ x, x < Mj t → H t (x + 1) - H t x = h x)
    (hslopeHi : ∀ x, Mj t ≤ x → 0 ≤ H t (x + 1) - H t x ∧ H t (x + 1) - H t x ≤ Kp)
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
    (hL34 : 0 ≤ L34) (h1L34 : 1 ≤ L34) (hβL : β ≤ L34) :
    ∑ u ∈ Finset.Ico s t, occ u
      ≤ ((K + Kp) + 2 * CJ * K + 1) *
          (((Mi t : ℝ) - (Mi s : ℝ)) + ((Mi s : ℝ) - (X s : ℝ))
            + max 0 ((Mi s : ℝ) - (Mj s : ℝ)))
        + ((t : ℝ) - (s : ℝ)) / 8
        + (K + CH + 2 * KF + 4 * CJ * K + 2 * KQ + 1) * L34 := by
  have h := lococc_window hst hocc hled hZs hZt hh hhw hslopeLo hslopeHi hint hosc hQ hFs hFt
    hJstruct hMjmono hMjstep hXW hMiw hXMiS hXtMi hcont1 hcont2 hcont3 hcont4 hcont5
    hK hβ hKp hCJ hCH hKF hKQ hL34 h1L34 hβL
  have he : (1 / 8 : ℝ) * ((t : ℝ) - (s : ℝ)) = ((t : ℝ) - (s : ℝ)) / 8 := by ring
  rw [he] at h
  exact h
