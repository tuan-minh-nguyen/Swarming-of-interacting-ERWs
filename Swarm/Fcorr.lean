/-
  The correction function `F_b` of the occupation-time estimate (Proposition `ball` of
  *Swarming of interacting excited random walks*, `main_1d_revised.tex`).

  The paper's `F_b` (eq. `(Fdef)`) is defined through its first differences

      F_b(g+1) - F_b(g) = min { 0 , 2 eps (g+1) - (2 b / (1-a)) (1 - a^{g+1}) },   g >= 0,
      F_b(g) = 0                                                                   g <= 0.

  It is the potential whose discrete Laplacian dominates the loss term
  `- b a^{X-r} 1{X >= r}` of the projected Poisson drift `(Zloss)` up to `eps`, and whose
  increments are uniformly of order `b/(1-a)`.  Nothing here is probabilistic: this file
  proves the deterministic estimates `(Fbounds)` and `(Fdrift)` of the paper.

  **N-independence.**  Every constant below is an explicit function of `a` and `eps` only:
  the absolute bound is `b^2 / (eps (1-a)^2)`, with no other quantity entering.  With the
  paper's `a = aConst p ((1-p)^(m-1))` this reads `p^2 / (eps (2p-1)^2 (1-p)^(2(m-1)))`,
  a function of `(m,p,eps)`; the walker count `N` occurs nowhere.

  Main results:
  * `SwarmOcc.Fcorr_nonpos`          : `F_b <= 0`                          (`(Fbounds)` 1)
  * `SwarmOcc.Fcorr_abs_le`          : `|F_b g| <= b^2/(eps (1-a)^2)`      (`(Fbounds)` 2)
  * `SwarmOcc.Fcorr_succ_sub_abs_le` : `|F_b(g+1) - F_b g| <= 2b/(1-a)`    (`(Fbounds)` 3)
  * `SwarmOcc.Fcorr_second_diff`     : the second-difference bound
  * `SwarmOcc.Fcorr_coin_drift`      : `(Fdrift)` for a `{+-1}` increment with
    `P(xi = 1) = alpha >= 1/2`
-/
import Swarm.Imports

open Finset
open scoped BigOperators

namespace SwarmOcc

/-! ### Definition -/

/-- The argument of the paper's `min`: `A i = 2 eps (i+1) - (2b/(1-a)) (1 - a^{i+1})`. -/
noncomputable def Farg (a ε b : ℝ) (i : ℕ) : ℝ :=
  2 * ε * ((i : ℝ) + 1) - (2 * b / (1 - a)) * (1 - a ^ (i + 1))

/-- The paper's first-difference sequence `d(i) = min {0, A i}` (eq. `(Fdef)`). -/
noncomputable def Fdiff (a ε b : ℝ) (i : ℕ) : ℝ := min 0 (Farg a ε b i)

/-- The paper's correction `F_b` (eq. `(Fdef)`), as the running sum of its first
differences.  For `g <= 0` the index set is empty (`Int.toNat _ = 0`), which is exactly the
paper's convention `F_b(g) = 0` for `g <= 0`. -/
noncomputable def Fcorr (a ε b : ℝ) (g : ℤ) : ℝ :=
  ∑ i ∈ Finset.range g.toNat, Fdiff a ε b i

/-- The right-hand side of the paper's second-difference bound, at integer `g`:
`- b a^g 1{g >= 0} + eps` (with `a^g` read as `a ^ g.toNat`, which is only used when `g >= 0`). -/
noncomputable def FbRHS (a b ε : ℝ) (g : ℤ) : ℝ :=
  if 0 ≤ g then -b * a ^ g.toNat + ε else ε

/-! ### The first difference and immediate consequences -/

lemma Farg_succ {a ε b : ℝ} (ha : a ≠ 1) (i : ℕ) :
    Farg a ε b (i + 1) = Farg a ε b i + (2 * ε - 2 * b * a ^ (i + 1)) := by
  have h1a : (1 : ℝ) - a ≠ 0 := by
    intro h; apply ha; linarith
  unfold Farg
  rw [pow_succ']
  push_cast
  field_simp
  ring

lemma Fcorr_succ_sub (a ε b : ℝ) (g : ℤ) :
    Fcorr a ε b (g + 1) - Fcorr a ε b g
      = if 0 ≤ g then Fdiff a ε b g.toNat else 0 := by
  unfold Fcorr
  rcases lt_or_ge g 0 with hg | hg
  · have h1 : (g + 1).toNat = 0 := by omega
    have h2 : g.toNat = 0 := by omega
    rw [h1, h2, if_neg (by omega)]
    simp
  · have h1 : (g + 1).toNat = g.toNat + 1 := by omega
    rw [h1, Finset.sum_range_succ, if_pos hg]
    ring

lemma Fdiff_nonpos (a ε b : ℝ) (i : ℕ) : Fdiff a ε b i ≤ 0 := min_le_left _ _

/-- **`F_b <= 0`** (`(Fbounds)`, first assertion).  No hypotheses. -/
theorem Fcorr_nonpos (a ε b : ℝ) (g : ℤ) : Fcorr a ε b g ≤ 0 :=
  Finset.sum_nonpos fun _ _ => Fdiff_nonpos a ε b _

/-- **`F_b` is nonincreasing**: the "monotonicity of `F_b`" used in the paper's derivation
of `(Fdrift)`. -/
lemma Fcorr_mono (a ε b : ℝ) (g : ℤ) : Fcorr a ε b (g + 1) ≤ Fcorr a ε b g := by
  have h := Fcorr_succ_sub a ε b g
  have h2 : (if 0 ≤ g then Fdiff a ε b g.toNat else 0) ≤ 0 := by
    split_ifs
    · exact Fdiff_nonpos a ε b _
    · exact le_rfl
  linarith

/-- The first difference is bounded below by `-2b/(1-a)`. -/
lemma Fdiff_ge_neg {a ε b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b) (hε : 0 < ε)
    (i : ℕ) : -(2 * b / (1 - a)) ≤ Fdiff a ε b i := by
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have hT : (0 : ℝ) ≤ 2 * b / (1 - a) := by positivity
  have hpow : (0 : ℝ) ≤ a ^ (i + 1) := pow_nonneg ha0 _
  have hεi : (0 : ℝ) ≤ 2 * ε * ((i : ℝ) + 1) := by
    have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    nlinarith
  have hkey : -(2 * b / (1 - a)) ≤ Farg a ε b i := by
    unfold Farg
    nlinarith [mul_nonneg hT hpow]
  exact le_min (by linarith) hkey

/-- **`|F_b(g+1) - F_b(g)| <= 2b/(1-a)`** (`(Fbounds)`, third assertion). -/
theorem Fcorr_succ_sub_abs_le {a ε b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hε : 0 < ε) (g : ℤ) :
    |Fcorr a ε b (g + 1) - Fcorr a ε b g| ≤ 2 * b / (1 - a) := by
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have hT : (0 : ℝ) ≤ 2 * b / (1 - a) := by positivity
  rw [Fcorr_succ_sub]
  split_ifs
  · rw [abs_of_nonpos (Fdiff_nonpos a ε b _)]
    have h := Fdiff_ge_neg ha0 ha1 hb hε (g.toNat)
    linarith
  · rw [abs_zero]; exact hT

/-! ### The absolute bound `|F_b| <= b^2/(eps (1-a)^2)` -/

/-- The clamping potential `Phi j = (max 0 (T - 2 eps j))^2 / (4 eps)` whose decrements
dominate the negative first differences of `F_b`. -/
noncomputable def Phi (T ε : ℝ) (j : ℕ) : ℝ := (max 0 (T - 2 * ε * ((j : ℝ)))) ^ 2 / (4 * ε)

/-- One step of the potential: `max 0 (T - 2 eps (j+1)) <= Phi j - Phi (j+1)`. -/
lemma Phi_step {T ε : ℝ} (hε : 0 < ε) (_hT : 0 ≤ T) (j : ℕ) :
    max 0 (T - 2 * ε * ((j : ℝ) + 1)) ≤ Phi T ε j - Phi T ε (j + 1) := by
  have h4ε : (0 : ℝ) < 4 * ε := by linarith
  have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
  unfold Phi
  rw [hcast]
  set x : ℝ := T - 2 * ε * ((j : ℝ) + 1) with hxdef
  have hprev : T - 2 * ε * (j : ℝ) = x + 2 * ε := by rw [hxdef]; ring
  rw [hprev]
  rcases lt_or_ge x 0 with hx | hx
  · have h1 : max 0 x = 0 := max_eq_left hx.le
    rw [h1]
    have hpos : (0 : ℝ) ≤ (max 0 (x + 2 * ε)) ^ 2 / (4 * ε) := by positivity
    norm_num
    linarith
  · have h1 : max 0 x = x := max_eq_right hx
    have h2 : max 0 (x + 2 * ε) = x + 2 * ε := max_eq_right (by linarith)
    rw [h1, h2]
    have hval : (x + 2 * ε) ^ 2 / (4 * ε) - x ^ 2 / (4 * ε) = x + ε := by
      field_simp
      ring
    rw [hval]
    linarith

/-- The tail sum bound `sum_{j<N} max 0 (T - 2 eps (j+1)) <= T^2/(4 eps)`. -/
lemma sum_Phi_le {T ε : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (N : ℕ) :
    ∑ j ∈ Finset.range N, max 0 (T - 2 * ε * ((j : ℝ) + 1)) ≤ T ^ 2 / (4 * ε) := by
  have hsum : ∑ j ∈ Finset.range N, max 0 (T - 2 * ε * ((j : ℝ) + 1))
      ≤ ∑ j ∈ Finset.range N, (Phi T ε j - Phi T ε (j + 1)) :=
    Finset.sum_le_sum fun j _ => Phi_step hε hT j
  rw [Finset.sum_range_sub'] at hsum
  have h0 : Phi T ε 0 = T ^ 2 / (4 * ε) := by
    unfold Phi
    rw [Nat.cast_zero, mul_zero, sub_zero, max_eq_right hT]
  have hN : 0 ≤ Phi T ε N := by unfold Phi; positivity
  rw [h0] at hsum
  linarith

/-- **`|F_b(g)| <= b^2/(eps (1-a)^2)`** (`(Fbounds)`, second assertion), with the explicit
constant `C_eps = 1/(eps (1-a)^2)`; only `a`, `eps` and `b` enter. -/
theorem Fcorr_abs_le {a ε b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b) (hε : 0 < ε)
    (g : ℤ) : |Fcorr a ε b g| ≤ b ^ 2 / (ε * (1 - a) ^ 2) := by
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have hT : (0 : ℝ) ≤ 2 * b / (1 - a) := by positivity
  have hneg : |Fcorr a ε b g| = ∑ i ∈ Finset.range g.toNat, (-(Fdiff a ε b i)) := by
    rw [abs_of_nonpos (Fcorr_nonpos a ε b g)]
    unfold Fcorr
    rw [Finset.sum_neg_distrib]
  have hterm : ∀ i : ℕ,
      -(Fdiff a ε b i) ≤ max 0 (2 * b / (1 - a) - 2 * ε * ((i : ℝ) + 1)) := by
    intro i
    have hpow : (0 : ℝ) ≤ a ^ (i + 1) := pow_nonneg ha0 _
    have hmono : -(Farg a ε b i) ≤ 2 * b / (1 - a) - 2 * ε * ((i : ℝ) + 1) := by
      unfold Farg
      nlinarith [mul_nonneg hT hpow]
    have hmin : -(min 0 (Farg a ε b i)) = max 0 (-(Farg a ε b i)) := by
      rcases lt_or_ge (Farg a ε b i) 0 with h | h
      · have h1 : min 0 (Farg a ε b i) = Farg a ε b i := min_eq_right h.le
        have h2 : max 0 (-(Farg a ε b i)) = -(Farg a ε b i) :=
          max_eq_right (by linarith : (0 : ℝ) ≤ -(Farg a ε b i))
        rw [h1, h2]
      · have h1 : min 0 (Farg a ε b i) = 0 := min_eq_left h
        have h2 : max 0 (-(Farg a ε b i)) = 0 :=
          max_eq_left (by linarith : -(Farg a ε b i) ≤ 0)
        rw [h1, h2]
        ring
    unfold Fdiff
    rw [hmin]
    exact max_le_max le_rfl hmono
  calc |Fcorr a ε b g|
      = ∑ i ∈ Finset.range g.toNat, (-(Fdiff a ε b i)) := hneg
    _ ≤ ∑ i ∈ Finset.range g.toNat, max 0 (2 * b / (1 - a) - 2 * ε * ((i : ℝ) + 1)) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ ≤ (2 * b / (1 - a)) ^ 2 / (4 * ε) := sum_Phi_le hε hT _
    _ = b ^ 2 / (ε * (1 - a) ^ 2) := by
        have h1a : (1 : ℝ) - a ≠ 0 := by linarith
        have hε' : ε ≠ 0 := by linarith
        field_simp
        ring

/-! ### The geometric identity and the second-difference bound -/

/-- The finite geometric sum as a quotient, in the orientation needed below. -/
lemma geom_div {a : ℝ} (ha1 : a < 1) (n : ℕ) :
    (1 - a ^ n) / (1 - a) = ∑ l ∈ Finset.range n, a ^ l := by
  rw [div_eq_iff (by linarith : (1 : ℝ) - a ≠ 0), geom_sum_mul_neg]

/-- `(2b/(1-a)) (1 - a^{i+1}) = 2b sum_{l<=i} a^l`: the loss coefficient `2b/(1-a)` is
exactly `2b` times the geometric weight. -/
lemma geom_key {a b : ℝ} (ha1 : a < 1) (i : ℕ) :
    (2 * b / (1 - a)) * (1 - a ^ (i + 1))
      = 2 * b * (∑ l ∈ Finset.range (i + 1), a ^ l) := by
  rw [div_mul_eq_mul_div, mul_div_assoc, geom_div ha1 (i + 1)]

/-- The core second-difference estimate at the level of the first differences: for `i >= 0`,
`(min 0 (A (i+1)) - min 0 (A i))/2 <= -b a^{i+1} + eps`. -/
lemma second_diff_core {a ε b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b) (_hε : 0 < ε)
    (i : ℕ) : (Fdiff a ε b (i + 1) - Fdiff a ε b i) / 2 ≤ -b * a ^ (i + 1) + ε := by
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have hFarg : Farg a ε b i
      = 2 * ε * ((i : ℝ) + 1) - 2 * b * (∑ l ∈ Finset.range (i + 1), a ^ l) := by
    unfold Farg
    rw [geom_key ha1 i]
  unfold Fdiff
  rw [Farg_succ ha1.ne i]
  set A : ℝ := Farg a ε b i with hA
  rcases lt_or_ge A 0 with hA0 | hA0
  · -- `A < 0`: the second difference is at most the increment of the arguments
    rw [min_eq_right hA0.le]
    have hle : min 0 (A + (2 * ε - 2 * b * a ^ (i + 1)))
        ≤ A + (2 * ε - 2 * b * a ^ (i + 1)) := min_le_right _ _
    linarith
  · -- `A >= 0`: both first differences vanish, and `eps >= b a^{i+1}`
    have hminA : min 0 A = 0 := min_eq_left hA0
    have hkey : b * a ^ (i + 1) ≤ ε := by
      have hAlo : 2 * b * (∑ l ∈ Finset.range (i + 1), a ^ l) ≤ 2 * ε * ((i : ℝ) + 1) := by
        rw [hFarg] at hA0
        linarith
      have hmono : ∑ _l ∈ Finset.range (i + 1), a ^ i ≤ ∑ l ∈ Finset.range (i + 1), a ^ l := by
        refine Finset.sum_le_sum fun l hl => ?_
        rw [Finset.mem_range] at hl
        exact pow_le_pow_of_le_one ha0 ha1.le (by omega)
      have hsum : ∑ _l ∈ Finset.range (i + 1), a ^ i = ((i : ℝ) + 1) * a ^ i := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
      rw [hsum] at hmono
      have hipos : (0 : ℝ) < (i : ℝ) + 1 := by positivity
      have haii : a ^ (i + 1) = a ^ i * a := by rw [pow_succ]
      have hai1 : (0 : ℝ) ≤ a ^ i := pow_nonneg ha0 i
      have haile : a ^ i * a ≤ a ^ i := by
        have h := mul_le_mul_of_nonneg_left ha1.le hai1
        simpa using h
      have hb' : b * a ^ (i + 1) ≤ b * a ^ i := by
        rw [haii]
        exact mul_le_mul_of_nonneg_left haile hb
      have hεi : (b * a ^ i) * ((i : ℝ) + 1) ≤ ε * ((i : ℝ) + 1) := by
        nlinarith [hmono, hAlo]
      have hε' : b * a ^ i ≤ ε := (mul_le_mul_iff_of_pos_right hipos).mp hεi
      linarith
    have hstep : (min 0 (A + (2 * ε - 2 * b * a ^ (i + 1))) - min 0 A) / 2 ≤ 0 := by
      rw [hminA, sub_zero]
      have hle : min 0 (A + (2 * ε - 2 * b * a ^ (i + 1))) ≤ 0 := min_le_left _ _
      linarith
    linarith

/-- **The second-difference bound** of the paper:
`(F_b(g+1) + F_b(g-1) - 2 F_b(g))/2 <= -b a^g 1{g >= 0} + eps` for every integer `g`. -/
theorem Fcorr_second_diff {a ε b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b) (hε : 0 < ε)
    (g : ℤ) :
    (Fcorr a ε b (g + 1) + Fcorr a ε b (g - 1) - 2 * Fcorr a ε b g) / 2
      ≤ FbRHS a b ε g := by
  rcases lt_or_ge g 0 with hg | hg
  · -- `g <= -1`: all three values vanish
    have e1 : Fcorr a ε b (g + 1) = 0 := by
      unfold Fcorr
      rw [show (g + 1).toNat = 0 by omega]
      simp
    have e2 : Fcorr a ε b (g - 1) = 0 := by
      unfold Fcorr
      rw [show (g - 1).toNat = 0 by omega]
      simp
    have e3 : Fcorr a ε b g = 0 := by
      unfold Fcorr
      rw [show g.toNat = 0 by omega]
      simp
    rw [e1, e2, e3, FbRHS, if_neg (by omega)]
    linarith
  · rcases eq_or_lt_of_le hg with h0 | hpos
    · -- `g = 0`
      subst h0
      have e1 : Fcorr a ε b (0 + 1) = Fdiff a ε b 0 := by
        unfold Fcorr
        rw [show ((0 : ℤ) + 1).toNat = 1 by norm_num, Finset.sum_range_one]
      have e2 : Fcorr a ε b (0 - 1) = 0 := by
        unfold Fcorr
        rw [show ((0 : ℤ) - 1).toNat = 0 by norm_num]
        simp
      have e3 : Fcorr a ε b 0 = 0 := by
        unfold Fcorr
        simp
      rw [e1, e2, e3, FbRHS, if_pos le_rfl,
        show (((0 : ℤ)).toNat) = 0 from rfl, pow_zero]
      have harg : Farg a ε b 0 = 2 * (ε - b) := by
        have h1a : (1 : ℝ) - a ≠ 0 := by linarith
        unfold Farg
        norm_num
        rw [div_mul_cancel₀ (2 * b) h1a]
        ring
      have hd : Fdiff a ε b 0 = min 0 (2 * (ε - b)) := by rw [Fdiff, harg]
      rw [hd]
      rcases lt_or_ge (2 * (ε - b)) 0 with h | h
      · rw [min_eq_right h.le]; linarith
      · rw [min_eq_left h]; linarith
    · -- `g >= 1`
      obtain ⟨i, hi⟩ : ∃ i : ℕ, g.toNat = i + 1 := ⟨g.toNat - 1, by omega⟩
      have hgm1 : (g - 1).toNat = i := by omega
      have e1 : Fcorr a ε b (g + 1) - Fcorr a ε b g = Fdiff a ε b (i + 1) := by
        rw [Fcorr_succ_sub, if_pos hg, hi]
      have e2 : Fcorr a ε b g - Fcorr a ε b (g - 1) = Fdiff a ε b i := by
        have h := Fcorr_succ_sub a ε b (g - 1)
        rw [show g - 1 + 1 = g by ring, if_pos (by omega), hgm1] at h
        exact h
      rw [FbRHS, if_pos hg, hi]
      have hcore := second_diff_core ha0 ha1 hb hε i
      linarith

/-! ### `(Fdrift)`: the coin-drift bound -/

/-- **`(Fdrift)`**: for a `{-1,1}`-valued increment `xi` with `P(xi = 1) = alpha >= 1/2`,
`alpha F_b(g+1) + (1-alpha) F_b(g-1) - F_b(g) <= -b a^g 1{g >= 0} + eps`. -/
theorem Fcorr_coin_drift {a ε b α : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b) (hε : 0 < ε)
    (hα : 1 / 2 ≤ α) (g : ℤ) :
    α * Fcorr a ε b (g + 1) + (1 - α) * Fcorr a ε b (g - 1) - Fcorr a ε b g
      ≤ FbRHS a b ε g := by
  have hsd := Fcorr_second_diff ha0 ha1 hb hε g
  have hmono1 : Fcorr a ε b (g + 1) ≤ Fcorr a ε b g := Fcorr_mono a ε b g
  have hmono2 : Fcorr a ε b g ≤ Fcorr a ε b (g - 1) := by
    have h := Fcorr_mono a ε b (g - 1)
    rwa [show g - 1 + 1 = g by ring] at h
  have hdiff : Fcorr a ε b (g + 1) - Fcorr a ε b (g - 1) ≤ 0 := by linarith
  have hkey : α * Fcorr a ε b (g + 1) + (1 - α) * Fcorr a ε b (g - 1) - Fcorr a ε b g
      = (Fcorr a ε b (g + 1) + Fcorr a ε b (g - 1) - 2 * Fcorr a ε b g) / 2
        + (α - 1 / 2) * (Fcorr a ε b (g + 1) - Fcorr a ε b (g - 1)) := by
    ring
  rw [hkey]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ α - 1 / 2) hdiff]

end SwarmOcc
