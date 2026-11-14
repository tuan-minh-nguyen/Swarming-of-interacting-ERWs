/-
  The *product decay* step of Lemma `transience` of
  *Swarming of interacting excited random walks* (main_1d_revised.tex, §2.2):

  "By the strong law of large numbers we have a.s.
     (1/r) sum_{x=1}^{r} log((1 - omega_j(x))/omega_j(x)) -> (1-p)^{m-1} log((1-p)/p) = -4c.
   We use a_k/b_k -> 1/2 to obtain (1/b_k) sum_{x=a_k+1}^{b_k} log(...) -> -2c.
   We therefore have prod_{x=a_k+1}^{b_k} (1-omega_j(x))/omega_j(x) <= e^{-c b_k}
   eventually a.s."

  This file verifies the deterministic limit transfer: from a Cesaro limit of the
  log-ratio profile at speed `-4c` and `a_k/b_k -> 1/2`, the block sums decay at speed
  `-2c`, which is what turns the exponentially small crossing probability of eq. (cross)
  into the summability used in the Borel--Cantelli step of Lemma `transience`.

  Inputs (all deterministic): a log-ratio profile `L : ℕ → ℝ` with `sum_{x<n} L x / n → -4c`,
  and level sequences `a <= b` with `b → ∞`, `a → ∞`, `a/b → 1/2`.  The strong law of large
  numbers producing the first input is the probabilistic ingredient; only its conclusion is
  used here.
-/
import Swarm.Imports
import Swarm.Levels

open Finset Filter
open scoped BigOperators Topology

namespace SwarmSpeed

/-- Partial sums of a log-ratio profile. -/
noncomputable def psum (L : ℕ → ℝ) (n : ℕ) : ℝ := ∑ x ∈ range n, L x

lemma psum_succ (L : ℕ → ℝ) (n : ℕ) : psum L (n + 1) = psum L n + L n := by
  simp [psum, sum_range_succ]

lemma psum_sub (L : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    psum L b - psum L a = ∑ x ∈ Ico a b, L x := by
  induction b with
  | zero =>
      have ha0 : a = 0 := Nat.le_zero.mp hab
      subst ha0
      simp [psum]
  | succ b ih =>
      rcases Nat.eq_or_lt_of_le hab with heq | hlt
      · subst heq; simp [psum]
      · have hb : a ≤ b := by omega
        have h1 := ih hb
        rw [psum_succ, sum_Ico_succ_top hb]
        linarith

/-- Block sums are differences of partial sums: `sum_{a < x <= b} L x = psum (b+1) - psum (a+1)`. -/
lemma sum_Ioc_eq_psum (L : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ x ∈ Ioc a b, L x = psum L (b + 1) - psum L (a + 1) := by
  have h1 : Ioc a b = Ico (a + 1) (b + 1) := by
    ext x
    simp only [mem_Ioc, mem_Ico]
    constructor <;> omega
  rw [h1, ← psum_sub L (by omega : a + 1 ≤ b + 1)]

/-! ### Auxiliary limits attached to a level sequence tending to infinity -/

section Aux

variable {b : ℕ → ℕ}

lemma tendsto_cast_of_tendsto (hb : Tendsto b atTop atTop) :
    Tendsto (fun k : ℕ => (b k : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp hb

lemma tendsto_cast_add_one (hb : Tendsto b atTop atTop) :
    Tendsto (fun k : ℕ => (b k : ℝ) + 1) atTop atTop :=
  tendsto_atTop_add_const_right _ 1 (tendsto_cast_of_tendsto hb)

lemma tendsto_div_succ_self (hb : Tendsto b atTop atTop) :
    Tendsto (fun k : ℕ => (b k : ℝ) / ((b k : ℝ) + 1)) atTop (nhds 1) := by
  have heq : ∀ k : ℕ, (b k : ℝ) / ((b k : ℝ) + 1) = 1 - 1 / ((b k : ℝ) + 1) := by
    intro k
    have h1 : ((b k : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  have hinv : Tendsto (fun k : ℕ => 1 / ((b k : ℝ) + 1)) atTop (nhds 0) :=
    (tendsto_cast_add_one hb).const_div_atTop 1
  have hmain : Tendsto (fun k : ℕ => 1 - 1 / ((b k : ℝ) + 1)) atTop (nhds (1 - 0)) :=
    Tendsto.sub tendsto_const_nhds hinv
  rw [show (1 : ℝ) - 0 = 1 by ring] at hmain
  exact hmain.congr (fun k => (heq k).symm)

lemma tendsto_succ_div_self (hb : Tendsto b atTop atTop) :
    Tendsto (fun k : ℕ => ((b k : ℝ) + 1) / (b k)) atTop (nhds 1) := by
  have hpos : ∀ᶠ k : ℕ in atTop, (0 : ℝ) < (b k : ℝ) := by
    have h1 : ∀ᶠ k : ℕ in atTop, 1 ≤ b k := hb.eventually (eventually_ge_atTop 1)
    filter_upwards [h1] with k hk
    exact_mod_cast hk
  have heq : ∀ᶠ k : ℕ in atTop, ((b k : ℝ) + 1) / (b k) = 1 + 1 / (b k) := by
    filter_upwards [hpos] with k hk
    field_simp
  have hinv : Tendsto (fun k : ℕ => 1 / (b k : ℝ)) atTop (nhds 0) :=
    (tendsto_cast_of_tendsto hb).const_div_atTop 1
  have hmain : Tendsto (fun k : ℕ => 1 + 1 / (b k : ℝ)) atTop (nhds (1 + 0)) :=
    Tendsto.add tendsto_const_nhds hinv
  rw [show (1 : ℝ) + 0 = 1 by ring] at hmain
  exact hmain.congr' (by filter_upwards [heq] with k hk; exact hk.symm)

end Aux

/-- **Product decay** (the display `prod_{x=a_k+1}^{b_k} r(x) <= e^{-c b_k}` of Lemma
`transience`): if the log-ratio profile has Cesaro limit `-4c < 0` and `a_k/b_k -> 1/2`, then
the block sums `sum_{a_k < x <= b_k} log r(x)` are eventually at most `-c b_k`, so the
products decay exponentially in the *full* level `b_k`. -/
theorem block_sum_decay {L : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hL : Tendsto (fun n : ℕ => psum L n / n) atTop (nhds (-4 * c)))
    {a b : ℕ → ℕ} (ha : Tendsto a atTop atTop) (hb : Tendsto b atTop atTop)
    (hratio : Tendsto (fun k : ℕ => (a k : ℝ) / (b k)) atTop (nhds (1 / 2))) :
    ∀ᶠ k : ℕ in atTop, ∑ x ∈ Ioc (a k) (b k), L x ≤ -c * (b k : ℝ) := by
  have hbpos1 : ∀ᶠ k : ℕ in atTop, (0 : ℝ) < (b k : ℝ) := by
    have h1 : ∀ᶠ k : ℕ in atTop, 1 ≤ b k := hb.eventually (eventually_ge_atTop 1)
    filter_upwards [h1] with k hk
    exact_mod_cast hk
  have hab_ev : ∀ᶠ k : ℕ in atTop, a k ≤ b k := by
    have h1 : ∀ᶠ k : ℕ in atTop, (a k : ℝ) / (b k) < 1 :=
      hratio.eventually (eventually_lt_nhds (by norm_num : (1 / 2 : ℝ) < 1))
    filter_upwards [h1, hbpos1] with k hk hkpos
    have h2 : (a k : ℝ) < (b k : ℝ) := by
      rw [div_lt_one hkpos] at hk
      exact hk
    exact_mod_cast h2.le
  have hb1 : Tendsto (fun k : ℕ => b k + 1) atTop atTop := by
    rw [tendsto_atTop_atTop] at hb ⊢
    intro B
    obtain ⟨K, hK⟩ := hb B
    exact ⟨K, fun k hk => by have := hK k hk; omega⟩
  have ha1 : Tendsto (fun k : ℕ => a k + 1) atTop atTop := by
    rw [tendsto_atTop_atTop] at ha ⊢
    intro B
    obtain ⟨K, hK⟩ := ha B
    exact ⟨K, fun k hk => by have := hK k hk; omega⟩
  have hSb : Tendsto (fun k : ℕ => psum L (b k + 1) / ((b k : ℝ) + 1)) atTop (nhds (-4 * c)) := by
    have h := hL.comp hb1
    have hfun : ((fun n : ℕ => psum L n / (n : ℝ)) ∘ fun k : ℕ => b k + 1)
        = fun k : ℕ => psum L (b k + 1) / ((b k : ℝ) + 1) := by
      funext k
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    rw [hfun] at h
    exact h
  have hSa : Tendsto (fun k : ℕ => psum L (a k + 1) / ((a k : ℝ) + 1)) atTop (nhds (-4 * c)) := by
    have h := hL.comp ha1
    have hfun : ((fun n : ℕ => psum L n / (n : ℝ)) ∘ fun k : ℕ => a k + 1)
        = fun k : ℕ => psum L (a k + 1) / ((a k : ℝ) + 1) := by
      funext k
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    rw [hfun] at h
    exact h
  have hratio1 : Tendsto (fun k : ℕ => ((a k : ℝ) + 1) / ((b k : ℝ) + 1)) atTop (nhds (1 / 2)) := by
    have hbpos : ∀ᶠ k : ℕ in atTop, (0 : ℝ) < (b k : ℝ) := by
      have h1 : ∀ᶠ k : ℕ in atTop, 1 ≤ b k := hb.eventually (eventually_ge_atTop 1)
      filter_upwards [h1] with k hk
      exact_mod_cast hk
    have hbeq : ∀ᶠ k : ℕ in atTop, ((a k : ℝ) + 1) / ((b k : ℝ) + 1) =
        (a k : ℝ) / (b k) * ((b k : ℝ) / ((b k : ℝ) + 1)) + 1 / ((b k : ℝ) + 1) := by
      filter_upwards [hbpos] with k hk
      have h1 : (0 : ℝ) < (b k : ℝ) + 1 := by linarith
      field_simp
    have hb_ratio := tendsto_div_succ_self hb
    have hsmall : Tendsto (fun k : ℕ => 1 / ((b k : ℝ) + 1)) atTop (nhds 0) :=
      (tendsto_cast_add_one hb).const_div_atTop 1
    have hmain : Tendsto (fun k : ℕ =>
        (a k : ℝ) / (b k) * ((b k : ℝ) / ((b k : ℝ) + 1)) + 1 / ((b k : ℝ) + 1))
        atTop (nhds ((1 / 2) * 1 + 0)) :=
      Tendsto.add (Tendsto.mul hratio hb_ratio) hsmall
    rw [show (1 / 2 : ℝ) * 1 + 0 = 1 / 2 by ring] at hmain
    exact hmain.congr' (by filter_upwards [hbeq] with k hk; exact hk.symm)
  have hblock : Tendsto (fun k : ℕ =>
      (∑ x ∈ Ioc (a k) (b k), L x) / ((b k : ℝ) + 1)) atTop (nhds (-2 * c)) := by
    have hsub : Tendsto (fun k : ℕ => psum L (b k + 1) / ((b k : ℝ) + 1) -
        (psum L (a k + 1) / ((a k : ℝ) + 1)) * (((a k : ℝ) + 1) / ((b k : ℝ) + 1)))
        atTop (nhds (-4 * c - (-4 * c) * (1 / 2))) :=
      Tendsto.sub hSb (Tendsto.mul hSa hratio1)
    have hval : -4 * c - (-4 * c) * (1 / 2) = -2 * c := by ring
    rw [hval] at hsub
    refine hsub.congr' ?_
    filter_upwards [hbpos1, hab_ev] with k hk hkab
    have hbpos : (0 : ℝ) < (b k : ℝ) := hk
    have h1 : (0 : ℝ) < (b k : ℝ) + 1 := by linarith
    have h2 : (0 : ℝ) < (a k : ℝ) + 1 := by positivity
    rw [sum_Ioc_eq_psum (L := L) hkab]
    field_simp
  have hfinal : Tendsto (fun k : ℕ => (∑ x ∈ Ioc (a k) (b k), L x) / (b k : ℝ)) atTop
      (nhds (-2 * c)) := by
    have hmul : Tendsto (fun k : ℕ =>
        (∑ x ∈ Ioc (a k) (b k), L x) / ((b k : ℝ) + 1) * (((b k : ℝ) + 1) / (b k)))
        atTop (nhds (-2 * c * 1)) := Tendsto.mul hblock (tendsto_succ_div_self hb)
    rw [show (-2 * c) * 1 = -2 * c by ring] at hmul
    refine hmul.congr' ?_
    filter_upwards [hbpos1] with k hk
    have hbpos : (0 : ℝ) < (b k : ℝ) := hk
    have h1 : (0 : ℝ) < (b k : ℝ) + 1 := by linarith
    field_simp
  have hlt : -2 * c < -c := by linarith
  have hbpos : ∀ᶠ k : ℕ in atTop, (0 : ℝ) < (b k : ℝ) := by
    have h1 : ∀ᶠ k : ℕ in atTop, 1 ≤ b k := hb.eventually (eventually_ge_atTop 1)
    filter_upwards [h1] with k hk
    exact_mod_cast hk
  filter_upwards [hfinal.eventually (eventually_lt_nhds hlt), hbpos] with k hk hkpos
  rw [div_lt_iff₀ hkpos] at hk
  linarith

/-- Exponential form of the product decay: with `r x = exp (L x)`,
`prod_{a_k < x <= b_k} r x <= exp (-c b_k)` eventually. -/
theorem prod_decay {L : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hL : Tendsto (fun n : ℕ => psum L n / n) atTop (nhds (-4 * c)))
    {a b : ℕ → ℕ} (ha : Tendsto a atTop atTop) (hb : Tendsto b atTop atTop)
    (hratio : Tendsto (fun k : ℕ => (a k : ℝ) / (b k)) atTop (nhds (1 / 2))) :
    ∀ᶠ k : ℕ in atTop,
      ∏ x ∈ Ioc (a k) (b k), Real.exp (L x) ≤ Real.exp (-c * (b k : ℝ)) := by
  filter_upwards [block_sum_decay hc hL ha hb hratio] with k hk
  rw [← Real.exp_sum]
  exact Real.exp_le_exp.mpr hk

end SwarmSpeed

/-! ### The paper's concrete levels -/

namespace SwarmSpeed

/-- `a_k/b_k -> 1/2` for the paper's levels `a_k = floor(b_k/2)`, `b_k = floor(k^{1/4}) - 1`. -/
theorem ratio_lvlA_lvlB : Tendsto (fun k : ℕ => (lvlA k : ℝ) / (lvlB k)) atTop (nhds (1 / 2)) := by
  have hb : Tendsto lvlB atTop atTop := tendsto_lvlB
  have hbpos : ∀ᶠ k : ℕ in atTop, (0 : ℝ) < (lvlB k : ℝ) := by
    have h1 : ∀ᶠ k : ℕ in atTop, 1 ≤ lvlB k := hb.eventually (eventually_ge_atTop 1)
    filter_upwards [h1] with k hk
    exact_mod_cast hk
  -- the two-sided bound `b/2 - 1 < floor(b/2) <= b/2`
  have hlow : Tendsto (fun k : ℕ => (1 / 2 : ℝ) - 1 / (lvlB k : ℝ)) atTop (nhds (1 / 2)) := by
    have h1 : Tendsto (fun k : ℕ => 1 / (lvlB k : ℝ)) atTop (nhds 0) :=
      (tendsto_cast_of_tendsto hb).const_div_atTop 1
    simpa using Tendsto.sub tendsto_const_nhds h1
  have hhigh : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (nhds (1 / 2)) := tendsto_const_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh ?_ ?_
  · -- `b/2 - 1 < floor(b/2)`, hence `1/2 - 1/b <= a/b`
    filter_upwards [hbpos] with k hk
    have h3 : lvlB k < 2 * lvlA k + 2 := by
      unfold lvlA
      have h1 := Nat.div_add_mod (lvlB k) 2
      have h2 : lvlB k % 2 ≤ 1 := by
        have h5 := Nat.mod_lt (lvlB k) (by norm_num : 0 < 2)
        omega
      omega
    have h4 : (lvlB k : ℝ) < 2 * (lvlA k : ℝ) + 2 := by exact_mod_cast h3
    have h6 : (1 / 2 : ℝ) - 1 / (lvlB k : ℝ) = ((lvlB k : ℝ) / 2 - 1) / (lvlB k : ℝ) := by
      field_simp
    rw [h6]
    have h7 : (lvlB k : ℝ) / 2 - 1 ≤ (lvlA k : ℝ) := by linarith
    exact div_le_div_of_nonneg_right h7 hk.le
  · -- `floor(b/2) <= b/2`, hence `a/b <= 1/2`
    filter_upwards [hbpos] with k hk
    have h3 : 2 * lvlA k ≤ lvlB k := by
      unfold lvlA
      have h1 := Nat.div_mul_le_self (lvlB k) 2
      omega
    have h4 : 2 * (lvlA k : ℝ) ≤ (lvlB k : ℝ) := by exact_mod_cast h3
    rw [div_le_iff₀ hk]
    linarith

/-- **The paper's product display with the paper's levels**: for a log-ratio profile whose
Cesaro mean is `-4c`, the products over `(a_k, b_k]` decay like `e^{-c b_k}` along
`b_k = floor(k^{1/4}) - 1`. -/
theorem prod_decay_paper_levels {L : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hL : Tendsto (fun n : ℕ => psum L n / n) atTop (nhds (-4 * c))) :
    ∀ᶠ k : ℕ in atTop,
      ∏ x ∈ Ioc (lvlA k) (lvlB k), Real.exp (L x) ≤ Real.exp (-c * (lvlB k : ℝ)) :=
  prod_decay hc hL tendsto_lvlA tendsto_lvlB ratio_lvlA_lvlB

end SwarmSpeed
