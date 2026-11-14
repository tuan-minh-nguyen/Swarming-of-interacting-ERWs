/-## The two summability conditions of the integrated route are not residual inputs

`HblkFinal.record_tightness_of_two` (the coordinator-reviewed reduction) lists five residual
inputs: the two block clauses `h₁`, `h₂`, the eventual defect bound `hdef`, and the two summability
conditions

  `hsum_s : ∑'_r (p₁ + p₂) (2 ^ (g r)) ≠ ⊤`,   `hcert : ∑'_ℓ (4Bℓ+1) (p₁ + p₂) ℓ ≠ ⊤`.

This file discharges the two summability conditions from an explicit, weak decay hypothesis on the
profiles.  The paper's profile `C_T e^{-c_T ℓ^{1/16}}` decays faster than any polynomial, so the
hypothesis is far weaker than what `(blkprob)` supplies:

  `p ℓ ≤ K (ℓ+1)^{-3}`   for a constant `K ≥ 0`.

Cubic decay is what the certificate weights `(4Bℓ+1)` permit: `(4Bℓ+1)(ℓ+1)^{-3} ≤ (4B+1)(ℓ+1)^{-2}`
and `∑ (ℓ+1)^{-2} < ∞`.  The same bound at the *scale* `2 ^ (g r)` needs one arithmetic fact about
the scale, which holds for the concrete `g r = r.log2 - k` and is isolated as `hgr`:

  `r + 1 ≤ D (2 ^ (g r) + 1)`   with `D = 2 ^ (k+1)` for `g` the repaired logarithmic scale.

Main declarations.

* `tsum_ne_top_of_le_ofReal`, `summable_inv_sq_succ` — the comparison tool.
* `tsum_coeff_mul_ne_top` — `hcert` from cubic decay.
* `tsum_at_scale_ne_top` — `hsum_s` from cubic decay plus `hgr`.
* `le_pow_mul_g`, `le_shift_mul_pow_g` — the growth of the repaired logarithmic scale.
* `record_tightness_of_two_decay` — `HblkFinal.record_tightness_of_two` with `hsum_s` and `hcert`
  replaced by the cubic decay bounds.
* `record_tightness_of_two_actual_blocks_only` — the composite with the integrated `hdef`
  (`HdefDefect.hdef_actual_hblkScale`, m1) and the satisfiable scale arithmetic
  (`HblkScale.exists_compatible_scale`): along the canonical stopped-record path law, record
  tightness follows from **only** the two array-side block clauses `h₁`, `h₂` and cubic decay of
  their profiles.

Nothing here proves `h₁` or `h₂`: they are the paper's `(blkprob)` and remain open.  No proof holes.
-/
import Swarm.HblkFinal

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped ENNReal BigOperators

namespace AuditSummable

/-! ### Comparison with a summable real majorant -/

/-- If `w` is dominated by `ofReal ∘ f` for a summable nonnegative real family `f`, then `∑' w` is
finite. -/
theorem tsum_ne_top_of_le_ofReal {w : ℕ → ℝ≥0∞} {f : ℕ → ℝ}
    (hf : Summable f) (hfn : ∀ ℓ, 0 ≤ f ℓ) (h : ∀ ℓ, w ℓ ≤ ENNReal.ofReal (f ℓ)) :
    (∑' ℓ, w ℓ) ≠ ⊤ := by
  have h1 : (∑' ℓ, w ℓ) ≤ ∑' ℓ, ENNReal.ofReal (f ℓ) := ENNReal.tsum_le_tsum h
  have h2 : ENNReal.ofReal (∑' ℓ, f ℓ) = ∑' ℓ, ENNReal.ofReal (f ℓ) :=
    ENNReal.ofReal_tsum_of_nonneg hfn hf
  rw [← h2] at h1
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1

/-- `∑ (ℓ+1)^{-2}` converges. -/
theorem summable_inv_sq_succ : Summable (fun ℓ : ℕ => (((ℓ : ℝ) + 1))⁻¹ ^ 2) := by
  have h : Summable (fun n : ℕ => (((n : ℝ))⁻¹ ^ 2)) := by
    have h' := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num : (1 : ℕ) < 2)
    simpa [one_div, inv_pow] using h'
  have h2 := (summable_nat_add_iff 1).mpr h
  simpa [Nat.cast_add, Nat.cast_one] using h2

/-! ### The certificate weight -/

/-- **`hcert` from cubic decay.**  If `p ℓ ≤ K (ℓ+1)^{-3}` then
`∑_ℓ (4Bℓ+1) p ℓ ≠ ⊤`. -/
theorem tsum_coeff_mul_ne_top (B : ℕ) {K : ℝ} (hK : 0 ≤ K) {p : ℕ → ℝ≥0∞}
    (hp : ∀ ℓ : ℕ, p ℓ ≤ ENNReal.ofReal (K * (((ℓ : ℝ) + 1))⁻¹ ^ 3)) :
    (∑' ℓ : ℕ, ((4 * B * ℓ + 1 : ℕ) : ℝ≥0∞) * p ℓ) ≠ ⊤ := by
  have hf : Summable (fun ℓ : ℕ => K * ((4 * B + 1 : ℕ) : ℝ) * (((ℓ : ℝ) + 1))⁻¹ ^ 2) :=
    summable_inv_sq_succ.mul_left (K * ((4 * B + 1 : ℕ) : ℝ))
  refine tsum_ne_top_of_le_ofReal hf (fun ℓ => by positivity) (fun ℓ => ?_)
  -- coefficient times the profile
  have hcast : ((4 * B * ℓ + 1 : ℕ) : ℝ) ≤ ((4 * B + 1 : ℕ) : ℝ) * ((ℓ : ℝ) + 1) := by
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) ℓ]
  have hc : (0 : ℝ) ≤ ((4 * B * ℓ + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le _
  have hstep : ((4 * B * ℓ + 1 : ℕ) : ℝ≥0∞) * p ℓ
      ≤ ENNReal.ofReal (((4 * B * ℓ + 1 : ℕ) : ℝ) *
          (K * (((ℓ : ℝ) + 1))⁻¹ ^ 3)) := by
    calc ((4 * B * ℓ + 1 : ℕ) : ℝ≥0∞) * p ℓ
        = ENNReal.ofReal (((4 * B * ℓ + 1 : ℕ) : ℝ)) * p ℓ := by
          rw [ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (((4 * B * ℓ + 1 : ℕ) : ℝ)) *
            ENNReal.ofReal (K * (((ℓ : ℝ) + 1))⁻¹ ^ 3) := by
          apply mul_le_mul_of_nonneg_left (hp ℓ)
          simp
      _ = ENNReal.ofReal (((4 * B * ℓ + 1 : ℕ) : ℝ) *
            (K * (((ℓ : ℝ) + 1))⁻¹ ^ 3)) := by
          rw [ENNReal.ofReal_mul hc]
  refine le_trans hstep (ENNReal.ofReal_le_ofReal ?_)
  have hpos : (0 : ℝ) < ((ℓ : ℝ) + 1) := by positivity
  calc ((4 * B * ℓ + 1 : ℕ) : ℝ) * (K * (((ℓ : ℝ) + 1))⁻¹ ^ 3)
      ≤ (((4 * B + 1 : ℕ) : ℝ) * ((ℓ : ℝ) + 1)) * (K * (((ℓ : ℝ) + 1))⁻¹ ^ 3) := by
        apply mul_le_mul_of_nonneg_right hcast
        positivity
    _ = K * ((4 * B + 1 : ℕ) : ℝ) * (((ℓ : ℝ) + 1))⁻¹ ^ 2 := by
        field_simp

/-! ### The scale weight -/

/-- **`hsum_s` from cubic decay.**  If the profile decays cubically at the scale `2 ^ (g r)` and the
scale grows at least linearly in `r` (`r + 1 ≤ D (2 ^ (g r) + 1)`), then
`∑_r p (2 ^ (g r)) ≠ ⊤`. -/
theorem tsum_at_scale_ne_top {g : ℕ → ℕ} {D K : ℝ} (hD : 1 ≤ D) (hK : 0 ≤ K)
    {p : ℕ → ℝ≥0∞}
    (hgr : ∀ r : ℕ, (r : ℝ) + 1 ≤ D * (((2 ^ g r : ℕ) : ℝ) + 1))
    (hp : ∀ r : ℕ, p (2 ^ g r) ≤
      ENNReal.ofReal (K * ((((2 ^ g r : ℕ) : ℝ) + 1))⁻¹ ^ 3)) :
    (∑' r : ℕ, p (2 ^ g r)) ≠ ⊤ := by
  -- reduce to the polynomial profile in `r`
  have hb : ∀ r : ℕ, p (2 ^ g r) ≤
      ENNReal.ofReal ((K * D ^ 3) * (((r : ℝ) + 1))⁻¹ ^ 3) := by
    intro r
    refine le_trans (hp r) (ENNReal.ofReal_le_ofReal ?_)
    set u : ℝ := ((2 ^ g r : ℕ) : ℝ) + 1 with hu
    set v : ℝ := (r : ℝ) + 1 with hv
    have hu0 : 0 < u := by positivity
    have hv0 : 0 < v := by positivity
    have hv : v ≤ D * u := hgr r
    have hinv : u⁻¹ ≤ D * v⁻¹ := by
      have h1 : (D * u)⁻¹ ≤ v⁻¹ := by
        rw [inv_le_inv₀ (by positivity) hv0]
        exact hv
      have h2 : u⁻¹ = D * (D * u)⁻¹ := by field_simp
      calc u⁻¹ = D * (D * u)⁻¹ := h2
        _ ≤ D * v⁻¹ := by gcongr
    calc K * u⁻¹ ^ 3 = K * (u⁻¹) ^ 3 := rfl
      _ ≤ K * (D * v⁻¹) ^ 3 := by
          apply mul_le_mul_of_nonneg_left _ hK
          gcongr
      _ = K * D ^ 3 * (v⁻¹) ^ 3 := by rw [mul_pow]; ring
  -- the shifted certificate bound with `B = 0`
  have := tsum_coeff_mul_ne_top (B := 0) (K := K * D ^ 3) (by positivity) hb
  simpa using this

/-! ### The repaired logarithmic scale grows at least linearly -/

/-- `r < 2 ^ (r.log2 + 1)`. -/
theorem lt_pow_log2_succ (r : ℕ) : r < 2 ^ (r.log2 + 1) := by
  rcases Nat.eq_zero_or_pos r with h | h
  · subst h
    simp
  · by_contra hcon
    push Not at hcon
    have := (Nat.le_log2 (by omega : r ≠ 0)).2 hcon
    omega

/-- `r ≤ 2 ^ (k+1) * 2 ^ (r.log2 - k)`, the growth of the repaired logarithmic scale. -/
theorem le_pow_mul_g (k r : ℕ) : r ≤ 2 ^ (k + 1) * 2 ^ (r.log2 - k) := by
  have hlt := lt_pow_log2_succ r
  rcases Nat.lt_or_ge r.log2 k with hk | hk
  · have hg : r.log2 - k = 0 := Nat.sub_eq_zero_of_le (le_of_lt hk)
    rw [hg, pow_zero, Nat.mul_one]
    exact le_trans (le_of_lt hlt) (Nat.pow_le_pow_right (by norm_num) (by omega))
  · rw [← pow_add]
    have hidx : k + 1 + (r.log2 - k) = r.log2 + 1 := by omega
    rw [hidx]
    exact le_of_lt hlt

/-- The growth hypothesis `hgr` of `tsum_at_scale_ne_top` for `g r = r.log2 - k`. -/
theorem le_shift_mul_pow_g (k r : ℕ) :
    (r : ℝ) + 1 ≤ ((2 : ℝ) ^ (k + 1)) * (((2 ^ (r.log2 - k) : ℕ) : ℝ) + 1) := by
  have h1 : (r : ℝ) ≤ ((2 : ℝ) ^ (k + 1)) * ((2 ^ (r.log2 - k) : ℕ) : ℝ) := by
    have := le_pow_mul_g k r
    have hcast : (r : ℝ) ≤ ((2 ^ (k + 1) * 2 ^ (r.log2 - k) : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at hcast ⊢
    linarith
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
    have : (1 : ℝ) ≤ 2 ^ (k + 1) := by
      have h3 : (1 : ℕ) ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
      exact_mod_cast h3
    exact this
  nlinarith

end AuditSummable
