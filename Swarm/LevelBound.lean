/-
# Levels of the halving procedure never exceed the good scale

This file supplies the combinatorial half of the *weakening of `ProbCtx.hR`* that the record
tightness argument actually needs.

`Tightness.lean`'s union bound needs, for every certificate `(r, ℓ)` produced by
`TightCover.Ctx.exists_certificate`, the inequality `C₀ ℓ ≤ r`: only then does `hblk`
(which is stated for `C₀ ℓ ≤ r`) bound the certificate's probability.  `ProbCtx.hR` supplies it
as an almost-sure statement over *all* levels: a.e., every failing block at level `ℓ` starting at
`r ≥ R ω` has `2 C₀ ℓ ≤ r`.

That statement is stronger than the paper's mechanism.  `(recordo)` plus the block estimate and
Borel–Cantelli give, at each index `r`, one good level `Λ r ≈ r/(2C₀)` (the largest dyadic level
below `r/(2C₀)`), not goodness at all levels above it.  What the covering argument consumes is
only the level of the *failing* blocks that the halving procedure actually visits, and those are
bounded by the good scale: the procedure doubles only until it reaches a good level and then
halves, so its levels never exceed the scale at the current start.

Main results.

* `Ctx.lv_scale` — the level invariant: if `2 ^ g r * K` is good at every start `r ≥ r₀`, the
  exponent `g` never drops by more than one between consecutive starts, and the initial level
  `L₀` is `K`-dyadic and inside the scale at `r₀`, then at every step the level is `K`-dyadic and
  inside the scale, and the good level found is at most the scale.
* `Ctx.cert_level_le` — consequently every level the procedure visits, in particular the
  certificate level `2 ^ (kf n - 1) * lv n` of `exists_certificate`, satisfies `C₀ ℓ ≤ r` as soon
  as the scale satisfies `2 C₀ Λ r ≤ r`.

Thus `hR` may be replaced by the two strictly weaker inputs "`∀ r ≥ r₀, Good r (2 ^ g r * K)`"
and "`d r₀ ≤ 2 ^ g r₀ * K`" (the latter is the base case of the invariant, via
`L₀ = max K (d r₀)`).  Neither is proved here, and no other use of `hR` is made by the covering
argument.
-/
import Swarm.TightCover

open Classical
open scoped BigOperators

namespace RecordTight

namespace Ctx

/-! ## Elementary arithmetic -/

lemma pow_mul_le_pow_mul {K x y : ℕ} (hK : 0 < K) (h : 2 ^ x * K ≤ 2 ^ y * K) : x ≤ y := by
  have h2 : 2 ^ x ≤ 2 ^ y := Nat.le_of_mul_le_mul_right h hK
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h2

lemma pow_sub_mul_pow_mul {K a g : ℕ} (h : a ≤ g) :
    2 ^ (g - a) * (2 ^ a * K) = 2 ^ g * K := by
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel h]

lemma pow_eq_pow_pred_mul {a : ℕ} (ha : 0 < a) : 2 ^ a = 2 * 2 ^ (a - 1) := by
  conv_lhs => rw [← Nat.sub_add_cancel ha]
  rw [pow_succ]
  ring

/-- Halving a `K`-dyadic level: below `K` the level is capped, above it the exponent drops by one. -/
lemma max_div_two_pow_mul {K a : ℕ} (hK : 0 < K) :
    max K (2 ^ a * K / 2) = 2 ^ (max 0 (a - 1)) * K := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [pow_zero, one_mul, show max 0 (0 - 1) = 0 from by omega, pow_zero, one_mul]
    exact max_eq_left (Nat.div_le_self K 2)
  · have hsplit : 2 ^ a * K / 2 = 2 ^ (a - 1) * K := by
      rw [pow_eq_pow_pred_mul ha, mul_assoc, Nat.mul_div_right _ (by norm_num : 0 < 2)]
    rw [hsplit, max_eq_right, max_eq_right (Nat.zero_le _)]
    · simpa using Nat.mul_le_mul_right K (Nat.one_le_two_pow (n := a - 1))

/-- A `K`-dyadic level of the procedure is at most the scale, once the scale is good there. -/
lemma Mlv_le_scale_of_rep (c : Ctx) (g : ℕ → ℕ)
    (hgood : ∀ r, c.r₀ ≤ r → c.Good r (2 ^ g r * c.K))
    {n a : ℕ} (hlv : c.lv n = 2 ^ a * c.K) (hag : a ≤ g (c.ps n)) :
    c.Mlv n ≤ 2 ^ g (c.ps n) * c.K := by
  have hgrid : 2 ^ g (c.ps n) * c.K = 2 ^ (g (c.ps n) - a) * c.lv n := by
    rw [hlv]; exact (pow_sub_mul_pow_mul hag).symm
  have hgood' : c.Good (c.ps n) (2 ^ (g (c.ps n) - a) * max c.K (c.lv n)) := by
    rw [c.max_lv_eq n, ← hgrid]
    exact hgood _ (le_trans (Nat.le_add_right _ _) (le_ps_add c n))
  have hkf : c.kf n ≤ g (c.ps n) - a :=
    Nat.find_min' (c.hterm (c.ps n) (max c.K (c.lv n)) (le_max_left c.K (c.lv n))) hgood'
  have h1 : c.Mlv n = 2 ^ (c.kf n + a) * c.K := by
    rw [c.Mlv_eq n, hlv, ← mul_assoc, ← pow_add]
  rw [h1]
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))

/-! ## The scale invariant -/

/-- **The level invariant of the halving procedure.**  Suppose the level `2 ^ g r * K` is good at
every start `r ≥ r₀`, that the scale exponent never drops by more than one between two starts,
and that the initial level `L₀` is `K`-dyadic and inside the scale at `r₀`.  Then every level the
procedure visits is `K`-dyadic and inside the scale at the corresponding start, and the good level
it finds is at most the scale. -/
theorem lv_scale (c : Ctx) (g : ℕ → ℕ)
    (hgood : ∀ r, c.r₀ ≤ r → c.Good r (2 ^ g r * c.K))
    (hg : ∀ r r', c.r₀ ≤ r → r ≤ r' → g r ≤ g r' + 1)
    (h₀ : ∃ b, c.L₀ = 2 ^ b * c.K ∧ b ≤ g c.r₀) :
    ∀ n : ℕ, ∃ a, c.lv n = 2 ^ a * c.K ∧ a ≤ g (c.ps n) ∧
      c.Mlv n ≤ 2 ^ g (c.ps n) * c.K := by
  have hKL₀ : c.K ≤ c.L₀ := le_trans (le_max_left _ _) c.hstart
  intro n
  induction n with
  | zero =>
      obtain ⟨b, hb, hbg⟩ := h₀
      have hlv : c.lv 0 = 2 ^ b * c.K := by rw [lv_zero, max_eq_right hKL₀, hb]
      exact ⟨b, hlv, hbg, c.Mlv_le_scale_of_rep g hgood hlv hbg⟩
  | succ n ih =>
      obtain ⟨a, hlv, hag, hMlv⟩ := ih
      have hkfa : c.kf n + a ≤ g (c.ps n) := by
        have h1 : c.Mlv n = 2 ^ (c.kf n + a) * c.K := by
          rw [c.Mlv_eq n, hlv, ← mul_assoc, ← pow_add]
        rw [h1] at hMlv
        exact pow_mul_le_pow_mul c.hK hMlv
      have hlv' : c.lv (n + 1) = 2 ^ (max 0 (c.kf n + a - 1)) * c.K := by
        rw [lv_succ, c.Mlv_eq n, hlv, ← mul_assoc, ← pow_add]
        exact max_div_two_pow_mul c.hK
      have ha' : max 0 (c.kf n + a - 1) ≤ g (c.ps (n + 1)) := by
        have hps : c.ps n ≤ c.ps (n + 1) := c.ps_mono (Nat.le_succ n)
        have h2 : g (c.ps n) ≤ g (c.ps (n + 1)) + 1 :=
          hg _ _ (le_trans (Nat.le_add_right _ _) (le_ps_add c n)) hps
        omega
      exact ⟨_, hlv', ha', c.Mlv_le_scale_of_rep g hgood hlv' ha'⟩

/-- **Certificate levels satisfy `C₀ ℓ ≤ r`.**  Every level the procedure visits — in particular
the level `2 ^ (kf n - 1) * lv n` of the failing block in `exists_certificate` — is at most the
scale.  Hence, if the scale at `r` satisfies `2 C₀ Λ r ≤ r`, the certificate level satisfies
`C₀ ℓ ≤ r`, which is all that the union bound of `Tightness.lean` needs from `hR`. -/
theorem cert_level_le (c : Ctx) (g : ℕ → ℕ)
    (hgood : ∀ r, c.r₀ ≤ r → c.Good r (2 ^ g r * c.K))
    (hg : ∀ r r', c.r₀ ≤ r → r ≤ r' → g r ≤ g r' + 1)
    (h₀ : ∃ b, c.L₀ = 2 ^ b * c.K ∧ b ≤ g c.r₀)
    (hscale : ∀ r, c.r₀ ≤ r → 2 * c.C₀ * (2 ^ g r * c.K) ≤ r)
    {n : ℕ} (hn : 1 ≤ c.kf n) :
    c.C₀ * (2 ^ (c.kf n - 1) * c.lv n) ≤ c.ps n := by
  obtain ⟨a, hlv, hag, -⟩ := c.lv_scale g hgood hg h₀ n
  have hkfa : c.kf n + a ≤ g (c.ps n) := by
    have h1 : c.Mlv n = 2 ^ (c.kf n + a) * c.K := by
      rw [c.Mlv_eq n, hlv, ← mul_assoc, ← pow_add]
    have h2 := c.Mlv_le_scale_of_rep g hgood hlv hag
    rw [h1] at h2
    exact pow_mul_le_pow_mul c.hK h2
  have hid : 2 ^ (c.kf n - 1) * (2 ^ a * c.K) = 2 ^ (c.kf n - 1 + a) * c.K := by
    rw [← mul_assoc, ← pow_add]
  have h2ℓ : 2 * (c.C₀ * (2 ^ (c.kf n - 1) * c.lv n)) ≤ c.C₀ * (2 ^ g (c.ps n) * c.K) := by
    rw [hlv, hid]
    have hstep : 2 * (c.C₀ * (2 ^ (c.kf n - 1 + a) * c.K)) =
        c.C₀ * (2 ^ (c.kf n + a) * c.K) := by
      rw [show c.kf n + a = (c.kf n - 1 + a) + 1 from by omega, pow_succ]
      ring
    rw [hstep]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _
      (Nat.pow_le_pow_right (by norm_num) hkfa))
  have hsc := hscale (c.ps n) (le_trans (Nat.le_add_right _ _) (le_ps_add c n))
  have hsc' : 2 * (c.C₀ * (2 ^ g (c.ps n) * c.K)) ≤ c.ps n := by
    rw [← mul_assoc]; exact hsc
  omega

end Ctx

end RecordTight


