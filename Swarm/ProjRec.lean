/-
  The projected Poisson solution `H_{j,n}` of the occupation-time estimate (Proposition
  `ball` of *Swarming of interacting excited random walks*,
  `main_1d_revised.tex`).

  Three deterministic facts from the paper's proof are isolated here.

  1. **The branch mean.**  At a site whose mark is unseen, the two branches of `(hrec)`
     average under the mark law `P(B = 1) = q` to

         (1-q) (h+2) + q (1/p + ((1-p)/p) h) = a h + (1+a),
         a = 1 - (2p-1) q / p = `ExcitedEnv.aConst p q`.

     Since the array coordinates above the running maximum `r_n` of walker `j` are unused,
     the conditional expectations `e_g = E[h_j(r_n+g) | F_n]` satisfy `e_{g+1} = a e_g + (1+a)`.
     （The conditional-expectation step is *not* formalised here; see `PROJ_REC.md`.)

  2. **The closed form and the partial sums** (`(projh)`, `(projH)`):

         e_g = L + a^g (e_0 - L),        L = (1+a)/(1-a),
         sum_{j<g} e_j = g L + (e_0 - L) (1-a^g)/(1-a).

  3. **The potential `H^w`** (eq. `(Hdef)`) on `ℤ`, its exact increment
     `H(x+1) - H(x) = h(x)`, and the resulting upper bound
     `sum_{j<g} e_j <= g L + b/(1-a)` used in `(Vbound)` when `e_0 <= b_n`.
-/
import Swarm.Imports
import Swarm.EnvCore

open Finset
open scoped BigOperators

namespace SwarmOcc

/-! ### The branch mean -/

/-- **The conditional branch mean.**  Averaging the two branches of `(hrec)` under the mark
law with `P(B = 1) = q` gives the affine recursion with multiplier `aConst p q` and constant
`1 + aConst p q`. -/
theorem branch_mean {p q h : ℝ} (hp : p ≠ 0) :
    (1 - q) * (h + 2) + q * (1 / p + ((1 - p) / p) * h)
      = ExcitedEnv.aConst p q * h + (1 + ExcitedEnv.aConst p q) := by
  unfold ExcitedEnv.aConst
  field_simp
  ring

/-- The same identity with the paper's `q = (1-p)^{m-1}`, in the form of the projected
recursion: the next conditional mean is `a * e + (1+a)`. -/
theorem branch_mean_pow {p : ℝ} (hp : p ≠ 0) {m : ℕ} (h : ℝ) :
    (1 - (1 - p) ^ (m - 1)) * (h + 2)
        + (1 - p) ^ (m - 1) * (1 / p + ((1 - p) / p) * h)
      = ExcitedEnv.aConst p ((1 - p) ^ (m - 1)) * h
        + (1 + ExcitedEnv.aConst p ((1 - p) ^ (m - 1))) :=
  branch_mean hp

/-! ### The affine recursion and its closed form -/

/-- **`(projh)` closed form**: `e_g = L + a^g (e_0 - L)` for `e_{g+1} = a e_g + (1+a)`. -/
theorem proj_closed_form {a : ℝ} (ha : a ≠ 1) (e : ℕ → ℝ)
    (he : ∀ g, e (g + 1) = a * e g + (1 + a)) (g : ℕ) :
    e g = (1 + a) / (1 - a) + a ^ g * (e 0 - (1 + a) / (1 - a)) := by
  have h1a : (1 : ℝ) - a ≠ 0 := by
    intro h; exact ha (by linarith)
  induction g with
  | zero => simp
  | succ k ih =>
      rw [he k, ih, pow_succ]
      field_simp
      ring

/-- The **increment form** of the closed form: `e_{g+1} - e_g = (1-a) a^g (L - e_0)`. -/
theorem proj_step_sub {a : ℝ} (ha : a ≠ 1) (e : ℕ → ℝ)
    (he : ∀ g, e (g + 1) = a * e g + (1 + a)) (g : ℕ) :
    e (g + 1) - e g = (1 - a) * a ^ g * ((1 + a) / (1 - a) - e 0) := by
  have h1a : (1 : ℝ) - a ≠ 0 := by
    intro h; exact ha (by linarith)
  rw [proj_closed_form ha e he (g + 1), proj_closed_form ha e he g, pow_succ]
  field_simp
  ring

/-- **`(projH)` summed**: `sum_{j<g} e_j = g L + (e_0 - L) (1-a^g)/(1-a)`. -/
theorem proj_partial_sum {a : ℝ} (ha : a ≠ 1) (e : ℕ → ℝ)
    (he : ∀ g, e (g + 1) = a * e g + (1 + a)) (g : ℕ) :
    ∑ j ∈ Finset.range g, e j
      = g * ((1 + a) / (1 - a))
        + (e 0 - (1 + a) / (1 - a)) * ((1 - a ^ g) / (1 - a)) := by
  have h1a : (1 : ℝ) - a ≠ 0 := by
    intro h; exact ha (by linarith)
  calc ∑ j ∈ Finset.range g, e j
      = ∑ j ∈ Finset.range g,
          ((1 + a) / (1 - a) + a ^ j * (e 0 - (1 + a) / (1 - a))) :=
        Finset.sum_congr rfl fun j _ => proj_closed_form ha e he j
    _ = g * ((1 + a) / (1 - a))
          + (∑ j ∈ Finset.range g, a ^ j) * (e 0 - (1 + a) / (1 - a)) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          Finset.sum_mul]
    _ = g * ((1 + a) / (1 - a))
        + (e 0 - (1 + a) / (1 - a)) * ((1 - a ^ g) / (1 - a)) := by
        rw [ExcitedEnv.geom_partial_sum a ha g]
        ring

/-! ### The potential `H^w` on `ℤ` -/

/-- The paper's `H^w` (eq. `(Hdef)`): `H(x) = x` for `x <= 0` and
`H(x) = sum_{u=0}^{x-1} h(u)` for `x >= 0` (the two definitions agree at `x = 0`). -/
noncomputable def Hpot (h : ℕ → ℝ) (x : ℤ) : ℝ :=
  if x ≤ 0 then (x : ℝ) else ∑ u ∈ Finset.range x.toNat, h u

lemma Hpot_of_nonpos {h : ℕ → ℝ} {x : ℤ} (hx : x ≤ 0) : Hpot h x = (x : ℝ) := if_pos hx

/-- **The exact increment of `H^w`**: `H(x+1) - H(x) = h(x)` for `x >= 0` and `= 1` for
`x < 0`.  In particular `H^w(x+1) - H^w(x) = h^w(x)` for every integer `x`, because `h^w = 1`
on `x <= -1`. -/
theorem Hpot_succ_sub (h : ℕ → ℝ) (x : ℤ) :
    Hpot h (x + 1) - Hpot h x = if 0 ≤ x then h x.toNat else 1 := by
  rcases lt_or_ge x 0 with hx | hx
  · have h1 : x + 1 ≤ 0 := by omega
    have h2 : x ≤ 0 := hx.le
    rw [Hpot_of_nonpos h1, Hpot_of_nonpos h2, if_neg (by omega)]
    push_cast
    ring
  · have h1 : ¬ (x + 1 ≤ 0) := by omega
    have h2 : (x + 1).toNat = x.toNat + 1 := by omega
    have e1 : Hpot h (x + 1) = ∑ u ∈ Finset.range (x.toNat + 1), h u := by
      rw [Hpot, if_neg h1, h2]
    have e2 : Hpot h x = ∑ u ∈ Finset.range x.toNat, h u := by
      rw [Hpot]
      rcases eq_or_lt_of_le hx with h0 | hpos
      · rw [← h0]; simp
      · rw [if_neg (by omega : ¬ (x ≤ 0))]
    rw [e1, e2, if_pos hx, Finset.sum_range_succ]
    ring

/-- The paper's `H_{j,n}(r+·)` decomposition: `H(r+g) = H(r) + sum_{j<g} h(r+j)`. -/
theorem Hpot_add_nat (h : ℕ → ℝ) (r : ℕ) (g : ℕ) :
    Hpot h ((r : ℤ) + g) = Hpot h (r : ℤ) + ∑ j ∈ Finset.range g, h (r + j) := by
  have hge0 : (0 : ℤ) ≤ (r : ℤ) + g := by
    have h0 : (0 : ℤ) ≤ (r : ℤ) := by exact_mod_cast Nat.zero_le r
    omega
  have hcast : ((r : ℤ) + g).toNat = r + g := by
    apply Nat.cast_injective (R := ℤ)
    rw [Int.toNat_of_nonneg hge0]
    push_cast
    ring
  have hmain : Hpot h ((r : ℤ) + g) = ∑ u ∈ Finset.range (r + g), h u := by
    rw [Hpot, hcast]
    rcases Nat.eq_zero_or_pos (r + g) with h0 | hp
    · have hz : (r : ℤ) + g = 0 := by
        have hz' : ((r + g : ℕ) : ℤ) = 0 := by rw [h0]; simp
        push_cast at hz'
        exact hz'
      rw [hz, h0]
      simp
    · have hpos : (0 : ℤ) < (r : ℤ) + g := by
        have hh : ((r + g : ℕ) : ℤ) > 0 := by exact_mod_cast hp
        push_cast at hh
        exact hh
      rw [if_neg (by omega : ¬ ((r : ℤ) + g ≤ 0))]
  have hr : Hpot h (r : ℤ) = ∑ u ∈ Finset.range r, h u := by
    rcases Nat.eq_zero_or_pos r with h0 | hp
    · subst h0
      simp [Hpot]
    · rw [Hpot, if_neg (by omega : ¬ ((r : ℤ) ≤ 0)), Int.toNat_natCast]
  rw [hmain, hr, Finset.sum_range_add]

/-- **`(projH)`** for the potential: if the site values `h(r+·)` follow the projected
recursion `e` (i.e. `e_g` is the conditional mean `E[h_j(r_n+g) | F_n]` and `e_0 = h(r_n)`),
then

    H(r+g) = H(r) + g L + (h(r) - L) (1 - a^g)/(1-a),      L = (1+a)/(1-a).
-/
theorem projH {a : ℝ} (ha : a ≠ 1) {h : ℕ → ℝ} {e : ℕ → ℝ}
    (he : ∀ g, e (g + 1) = a * e g + (1 + a)) (r : ℕ) (hh : ∀ j, h (r + j) = e j) (g : ℕ) :
    Hpot h ((r : ℤ) + g)
      = Hpot h (r : ℤ) + g * ((1 + a) / (1 - a))
        + (h r - (1 + a) / (1 - a)) * ((1 - a ^ g) / (1 - a)) := by
  rw [Hpot_add_nat]
  have hsum : ∑ j ∈ Finset.range g, h (r + j) = ∑ j ∈ Finset.range g, e j :=
    Finset.sum_congr rfl fun j _ => hh j
  have hh0 : e 0 = h r := by
    have := hh 0
    simpa using this.symm
  rw [hsum, proj_partial_sum ha e he g, hh0]
  ring

/-- **The upper bound `(Vbound)` core**: if `1 <= e_0 <= b` then
`sum_{j<g} e_j <= g L + b/(1-a)`.  This is the bound `H_{j,n}(X^i_n) <= (L+1) M + b/(1-a) + O(1)`
of the paper (with `g = X^i_n - r_n`). -/
theorem proj_partial_sum_upper {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    {e : ℕ → ℝ} (he : ∀ g, e (g + 1) = a * e g + (1 + a))
    (_he0 : 1 ≤ e 0) (heb : e 0 ≤ b) (g : ℕ) :
    ∑ j ∈ Finset.range g, e j ≤ g * ((1 + a) / (1 - a)) + b / (1 - a) := by
  have ha : a ≠ 1 := by linarith
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have hL0 : (0 : ℝ) ≤ (1 + a) / (1 - a) := by positivity
  have hpow : (0 : ℝ) ≤ a ^ g := pow_nonneg ha0 g
  have hpow1 : a ^ g ≤ 1 := pow_le_one₀ ha0 ha1.le
  have hquot_le : (1 - a ^ g) / (1 - a) ≤ 1 / (1 - a) :=
    div_le_div_of_nonneg_right (by linarith [hpow] : (1 : ℝ) - a ^ g ≤ 1) h1a.le
  have hquot_nonneg : (0 : ℝ) ≤ (1 - a ^ g) / (1 - a) := by
    apply div_nonneg _ h1a.le
    linarith [hpow, hpow1]
  rw [proj_partial_sum ha e he g]
  have hstep : (e 0 - (1 + a) / (1 - a)) * ((1 - a ^ g) / (1 - a)) ≤ b / (1 - a) := by
    rcases lt_or_ge (e 0 - (1 + a) / (1 - a)) 0 with hneg | hpos
    · have : (e 0 - (1 + a) / (1 - a)) * ((1 - a ^ g) / (1 - a)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hneg.le hquot_nonneg
      have : (0 : ℝ) ≤ b / (1 - a) := by positivity
      linarith
    · have hle1 : e 0 - (1 + a) / (1 - a) ≤ b := by linarith
      have hmul := mul_le_mul hle1 hquot_le hquot_nonneg hb
      simpa [div_eq_mul_inv] using hmul
  linarith

/-! ### The concrete potential of the interacting model -/

/-- The paper's `h^w` on all of `ℤ`: `h^w(x) = 1` for `x <= -1` and the recursion `(hrec)` for
`x >= 0`.  (This is `ExcitedEnv.hw` on `x >= 0` and the boundary value `h(-1) = 1` below.) -/
noncomputable def hZ (ω : ℕ → ℝ) (x : ℤ) : ℝ :=
  if x ≤ -1 then 1 else ExcitedEnv.hw ω x.toNat

/-- **The exact increment of the model potential**: `H^w(x+1) - H^w(x) = h^w(x)` for *every*
integer `x`, for the actual recursive weight function `ω`. -/
theorem Hpot_hw_succ_sub (ω : ℕ → ℝ) (x : ℤ) :
    Hpot (ExcitedEnv.hw ω) (x + 1) - Hpot (ExcitedEnv.hw ω) x = hZ ω x := by
  rw [Hpot_succ_sub]
  unfold hZ
  by_cases hx : 0 ≤ x
  · rw [if_pos hx, if_neg (by omega : ¬ x ≤ -1)]
  · rw [if_neg hx, if_pos (by omega : x ≤ -1)]

/-- **`(unit)`**: `ω(x) h^w(x) - (1 - ω(x)) h^w(x-1) = 1`, the identity consumed by the
interior case `zdrift_interior` of `(Zloss)`. -/
theorem unit_hw {ω : ℕ → ℝ} {n : ℕ} (h : ω n ≠ 0) :
    ω n * ExcitedEnv.hw ω n - (1 - ω n) * ExcitedEnv.hprev ω n = 1 := by
  rw [ExcitedEnv.hw_eq]
  field_simp
  ring

/-- **`h^w >= 1` on all of `ℤ`** for the paper's two-valued weights. -/
theorem one_le_hZ {p : ℝ} (hp1 : 1 / 2 < p) (hp2 : p < 1) {ω : ℕ → ℝ}
    (hω : ∀ n, ω n = 1 / 2 ∨ ω n = p) (x : ℤ) : 1 ≤ hZ ω x := by
  unfold hZ
  by_cases hx : x ≤ -1
  · rw [if_pos hx]
  · rw [if_neg hx]
    exact ExcitedEnv.one_le_hw hp1 hp2 hω x.toNat

end SwarmOcc
