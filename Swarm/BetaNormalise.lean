/-
  **Direction C: beta normalisation, and the explicit `L^{3/4}` remainder.**

  `LocSumAct` fixes the scales `ℓ = ⌈x⌉₊` (`ellT`), `n = ⌈x^5/8⌉₊` (`nT`) at
  `x = xOf L = L^{1/16}`, and `β = n·ℓ` (`betaT`).  Both `(locsum)`
  (`LocSumR1.array_locsum_h`) and `(loccoord)` (`Loccoord.loccoord_record_window`,
  `Loccoord.loccoord_full_window`) are stated with an additive remainder proportional to
  `β = betaT (xOf L)`, while Proposition `local` of the paper needs that remainder in the
  explicit form `C_T L^{3/4}`.  This file supplies the arithmetic:

  * `nT_le_ceil`, `ellT_le_add_one` — the upper ceiling bounds;
  * `betaT_le_poly` — `β ≤ (x^5/8 + 1)(x + 1)`;
  * `betaT_le_two_mul_pow_six_add_one` — the requested `β ≤ 2x^6 + 1` for all `x ≥ 1`;
  * `betaT_le_half_pow_six` — the sharper `β ≤ x^6/2` for `x ≥ 2` (`n ≤ x^5/4`, `ℓ ≤ 2x`),
    with `betaT_half_pow_six_threshold_needed` showing that the hypothesis cannot be weakened
    to `x ≥ 1`;
  * `xOf_pow_six` and the substitution lemmas `betaT_xOf_le`, `betaT_xOf_le_rpow34`,
    `betaT_xOf_le_half_pow_six`, `betaT_xOf_le_pow_three_quarters`, and the matching lower
    bound `betaT_xOf_ge` (`β ≥ L^{3/8}/8`, so `β = Θ(L^{3/8})`);
  * the covering arithmetic `numT_mul_betaT_le` (`numT L x * β ≤ L + β`) and
    `numT_cover_explicit` (`numT L (xOf L) * β ≤ L + L^{3/4}`);
  * six consumers, each a corollary of an already verified theorem, in which the abstract
    coefficient `betaT (xOf L)` is replaced by an explicit power of `L`:
    `array_locsum_h_explicit` (remainder `3C L^{3/8}`), `array_locsum_h_explicit34`
    (`3C L^{3/4}`), `loccoord_record_window_explicit` (`(3/2)C L^{3/8}`),
    `loccoord_record_window_explicit34` (`(3/2)C L^{3/4}`),
    `loccoord_full_window_explicit` (`(3/2)C(2T+4)^{3/8} L^{3/8}`) and
    `loccoord_full_window_explicit34` (`(3/2)C(2T+4)^{3/4} L^{3/4}`).

  Because `β = Θ(L^{3/8})`, the `L^{3/4}` remainder of `(locsum)`/`(loccoord)` is **not
  tight**; the sharp forms above are strictly stronger and are what the block decomposition
  actually delivers.  The `L^{3/4}` of `(locmart)`/`(lococc)`/`(locgroup)` is a martingale
  maximum bound and is not touched here.

  Nothing here closes the window-start gap of direction A: the side condition on `r`
  (`(T+3)L ≤ r` resp. `(3T+6)L ≤ r`) is inherited unchanged from the cited theorems, and no
  hypothesis is renamed or weakened.
-/
import Swarm.A3Scale
import Mathlib.Data.NNRat.Floor
import Swarm.LocCoordRange

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false

open scoped BigOperators ENNReal

namespace LocSumAct

noncomputable section

/-! ### Ceiling arithmetic for `nT` and `ellT` -/

/-- `nT x ≤ x^5/8 + 1`: the upper ceiling bound complementary to `nT_lower`. -/
lemma nT_le_ceil {x : ℝ} (hx : 0 ≤ x) : ((nT x : ℕ) : ℝ) ≤ x ^ 5 / 8 + 1 := by
  have h : ((⌈x ^ 5 / 8⌉₊ : ℕ) : ℝ) < x ^ 5 / 8 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  rw [nT]
  linarith

/-- `ellT x ≤ x + 1`: the upper ceiling bound complementary to `le_ellT`. -/
lemma ellT_le_add_one {x : ℝ} (hx : 0 ≤ x) : ((ellT x : ℕ) : ℝ) ≤ x + 1 := by
  have h : ((⌈x⌉₊ : ℕ) : ℝ) < x + 1 := Nat.ceil_lt_add_one hx
  rw [ellT]
  linarith

/-- The raw product bound `β = n·ℓ ≤ (x^5/8 + 1)(x + 1)`. -/
lemma betaT_le_poly {x : ℝ} (hx : 1 ≤ x) :
    ((betaT x : ℕ) : ℝ) ≤ x ^ 6 / 8 + x ^ 5 / 8 + x + 1 := by
  have h0 : (0 : ℝ) ≤ x := by linarith
  have h1 : ((nT x : ℕ) : ℝ) ≤ x ^ 5 / 8 + 1 := nT_le_ceil h0
  have h2 : ((ellT x : ℕ) : ℝ) ≤ x + 1 := ellT_le_add_one h0
  have h3 : ((betaT x : ℕ) : ℝ) = ((nT x : ℕ) : ℝ) * ((ellT x : ℕ) : ℝ) := by
    rw [betaT]; push_cast; ring
  have h4 : ((nT x : ℕ) : ℝ) * ((ellT x : ℕ) : ℝ) ≤ (x ^ 5 / 8 + 1) * (x + 1) :=
    mul_le_mul h1 h2 (by positivity) (by positivity)
  calc ((betaT x : ℕ) : ℝ) = ((nT x : ℕ) : ℝ) * ((ellT x : ℕ) : ℝ) := h3
    _ ≤ (x ^ 5 / 8 + 1) * (x + 1) := h4
    _ = x ^ 6 / 8 + x ^ 5 / 8 + x + 1 := by ring

/-- **The requested normalisation.**  With `n = ⌈x^5/8⌉` and `ℓ = ⌈x⌉`,
`β = n·ℓ` satisfies `β ≤ 2x^6 + 1` for every `x ≥ 1`.

The proof only uses the two ceiling bounds and the polynomial inequality
`x^5 + 8x ≤ 15x^6`, which holds for `x ≥ 1` because
`x^5 + 8x ≤ 15x^5·x - ...`; concretely `15x^6 - x^5 - 8x ≥ 14x^5 - 8x^5 = 6x^5 ≥ 0`. -/
theorem betaT_le_two_mul_pow_six_add_one {x : ℝ} (hx : 1 ≤ x) :
    ((betaT x : ℕ) : ℝ) ≤ 2 * x ^ 6 + 1 := by
  have h := betaT_le_poly hx
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hx4 : (1 : ℝ) ≤ x ^ 4 := one_le_pow₀ hx
  have hx5 : (1 : ℝ) ≤ x ^ 5 := one_le_pow₀ hx
  have hx6 : (0 : ℝ) < x ^ 6 := by positivity
  -- the only nontrivial polynomial step
  have key : x ^ 5 + 8 * x ≤ 15 * x ^ 6 := by nlinarith [hx, hx4, hx5, hx6]
  linarith

/-- The sharper bound used below the `2x^6 + 1` envelope: for `x ≥ 2`,
`n ≤ x^5/4` and `ℓ ≤ 2x`, so `β ≤ x^6/2`. -/
theorem betaT_le_half_pow_six {x : ℝ} (hx : 2 ≤ x) : ((betaT x : ℕ) : ℝ) ≤ x ^ 6 / 2 := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hx5 : (32 : ℝ) ≤ x ^ 5 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hx 5
    norm_num at h ⊢
    linarith
  have h1 : ((nT x : ℕ) : ℝ) ≤ x ^ 5 / 4 := by
    have h := nT_le_ceil hx0
    linarith
  have h2 : ((ellT x : ℕ) : ℝ) ≤ 2 * x := ellT_le_two (by linarith)
  have h3 : ((betaT x : ℕ) : ℝ) = ((nT x : ℕ) : ℝ) * ((ellT x : ℕ) : ℝ) := by
    rw [betaT]; push_cast; ring
  have h4 : ((nT x : ℕ) : ℝ) * ((ellT x : ℕ) : ℝ) ≤ (x ^ 5 / 4) * (2 * x) :=
    mul_le_mul h1 h2 (by positivity) (by positivity)
  calc ((betaT x : ℕ) : ℝ) = ((nT x : ℕ) : ℝ) * ((ellT x : ℕ) : ℝ) := h3
    _ ≤ (x ^ 5 / 4) * (2 * x) := h4
    _ = x ^ 6 / 2 := by ring

/-! ### Substituting the scale `x = xOf L = L^{1/16}` -/

/-- `(L^{1/16})^6 = L^{3/8}`. -/
lemma xOf_pow_six (L : ℕ) : (xOf L) ^ 6 = (L : ℝ) ^ (3 / 8 : ℝ) := by
  have hL : (0 : ℝ) ≤ (L : ℝ) := by positivity
  rw [xOf, ← Real.rpow_natCast ((L : ℝ) ^ (1 / 16 : ℝ)) 6, ← Real.rpow_mul hL]
  norm_num

/-- `(L^{1/16})^(3/4) = L^{3/64}` — recorded because the `3/4` remainder is a *different*
power of `L` from `β ≈ L^{3/8}` only through the monotonicity `L^{3/8} ≤ L^{3/4}`. -/
lemma xOf_pow_three_quarters (L : ℕ) :
    (xOf L) ^ ((3 : ℝ) / 4) = (L : ℝ) ^ (3 / 64 : ℝ) := by
  have hL : (0 : ℝ) ≤ (L : ℝ) := by positivity
  rw [xOf, ← Real.rpow_mul hL]
  norm_num

/-- `β(L^{1/16}) ≤ 2L^{3/8} + 1`. -/
lemma betaT_xOf_le {L : ℕ} (hL : 1 ≤ L) :
    ((betaT (xOf L) : ℕ) : ℝ) ≤ 2 * (L : ℝ) ^ (3 / 8 : ℝ) + 1 := by
  have h := betaT_le_two_mul_pow_six_add_one (one_le_xOf hL)
  rwa [xOf_pow_six] at h

/-- `β(L^{1/16}) ≤ 3L^{3/4}`: the `3/4` remainder of the paper, with no threshold beyond
`L ≥ 1`.  (`L^{3/8} ≤ L^{3/4}` and `1 ≤ L^{3/4}` for `L ≥ 1`.) -/
lemma betaT_xOf_le_rpow34 {L : ℕ} (hL : 1 ≤ L) :
    ((betaT (xOf L) : ℕ) : ℝ) ≤ 3 * (L : ℝ) ^ (3 / 4 : ℝ) := by
  have h := betaT_xOf_le hL
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := by positivity
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hmono : (L : ℝ) ^ (3 / 8 : ℝ) ≤ (L : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hone : (1 : ℝ) ≤ (L : ℝ) ^ (3 / 4 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  linarith

/-- `xOf L ≥ 2` as soon as `L ≥ 2^16`. -/
lemma two_le_xOf {L : ℕ} (hL : 65536 ≤ L) : 2 ≤ xOf L := by
  have hcast : ((65536 : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hpow : ((2 : ℝ)) ^ 16 ≤ (L : ℝ) := by
    have : ((2 : ℝ)) ^ 16 = (65536 : ℝ) := by norm_num
    rw [this]; exact hcast
  rw [xOf]
  calc (2 : ℝ) = ((2 : ℝ) ^ 16) ^ (1 / 16 : ℝ) := by
        rw [← Real.rpow_natCast (2 : ℝ) 16, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
    _ ≤ (L : ℝ) ^ (1 / 16 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) hpow (by norm_num)

/-- `β(L^{1/16}) ≤ L^{3/8}/2` for `L ≥ 2^16`, hence in particular `β ≤ L^{3/4}`.  This is the
thresholded form giving the sharp constant `C_T = 3C` below. -/
lemma betaT_xOf_le_half_pow_six {L : ℕ} (hL : 65536 ≤ L) :
    ((betaT (xOf L) : ℕ) : ℝ) ≤ (L : ℝ) ^ (3 / 8 : ℝ) / 2 := by
  have h := betaT_le_half_pow_six (two_le_xOf hL)
  rwa [xOf_pow_six] at h

/-- `β(L^{1/16}) ≤ L^{3/4}` for `L ≥ 2^16`. -/
lemma betaT_xOf_le_pow_three_quarters {L : ℕ} (hL : 65536 ≤ L) :
    ((betaT (xOf L) : ℕ) : ℝ) ≤ (L : ℝ) ^ (3 / 4 : ℝ) := by
  have h := betaT_xOf_le_half_pow_six hL
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by
    have : (1 : ℕ) ≤ L := le_trans (by norm_num) hL
    exact_mod_cast this
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := by positivity
  have hmono : (L : ℝ) ^ (3 / 8 : ℝ) ≤ (L : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  linarith

end

end LocSumAct

/-! ### The scale is genuinely of order `L^{3/8}`

The upper bounds above lose nothing: `β ≥ x^6/8 = L^{3/8}/8`, so the block remainder of
`(locsum)`/`(loccoord)` is `Θ(L^{3/8})` on the face of those statements.  In particular the
remainder `L^{3/4}` of Proposition `local` is *not* tight: it exceeds the available `L^{3/8}`
by a factor `L^{3/8}`.  The theorems below are therefore stated in the sharp `L^{3/8}` form,
with the paper's `L^{3/4}` form as a corollary (using `L^{3/8} ≤ L^{3/4}` for `L ≥ 1`). -/

namespace LocSumAct

/-- `β(L^{1/16}) ≥ L^{3/8}/8`: the matching lower bound for the scale. -/
lemma betaT_xOf_ge {L : ℕ} (hL : 1 ≤ L) :
    (L : ℝ) ^ (3 / 8 : ℝ) / 8 ≤ ((betaT (xOf L) : ℕ) : ℝ) := by
  have h := betaT_lower (one_le_xOf hL)
  rwa [xOf_pow_six] at h

end LocSumAct

/-! ### The explicit remainders -/

namespace LocSumR1

/-- **`(locsum)` with the sharp explicit remainder.**  For every `C > Mb p (qOf p m)` there are
`c > 0` and `L₀` such that for every `L ≥ L₀` and every window start `A ≥ L`, off an event of
probability at most `e^{-c L^{1/16}}`, every walker `j` and every interval
`[a0,b0) ⊆ [A, A+L)` satisfies

    Σ_{x∈[a0,b0)} h_j(x)² ≤ 2C(b0-a0) + 3C L^{3/8}.

(Previously the remainder was the abstract `6C·betaT (xOf L)`.) -/
theorem array_locsum_h_explicit {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) {C : ℝ} (hC1 : 1 ≤ C)
    (hCM : LocSum.Mb p (LocSumAct.qOf p m) < C) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ A : ℕ, L ≤ A →
      Swarming.Uniform.arrayMeasure N (LsBad N p m C L A)
          ≤ ENNReal.ofReal (Real.exp (-c * LocSumAct.xOf L)) ∧
      (∀ U : Swarming.Uniform.Array N, U ∉ LsBad N p m C L A → ∀ j : Fin N,
        ∀ a0 b0 : ℕ, A ≤ a0 → b0 ≤ A + L → a0 ≤ b0 →
          ∑ x ∈ Finset.Ico a0 b0,
              (SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x) ^ 2
            ≤ 2 * C * ((b0 : ℝ) - (a0 : ℝ)) + 3 * C * (L : ℝ) ^ (3 / 8 : ℝ)) := by
  obtain ⟨c, hc, L₀, hL⟩ := array_locsum_h (N := N) hp1 hp2 hm hC1 hCM
  refine ⟨c, hc, max L₀ 65536, ?_⟩
  intro L hLbig A hA
  have hL0 : L₀ ≤ L := le_trans (le_max_left _ _) hLbig
  have hLbig' : 65536 ≤ L := le_trans (le_max_right _ _) hLbig
  obtain ⟨hmeas, hbound⟩ := hL L hL0 A hA
  refine ⟨hmeas, fun U hU j a0 b0 ha hb hab => ?_⟩
  have hmain := hbound U hU j a0 b0 ha hb hab
  have hβ : ((LocSumAct.betaT (LocSumAct.xOf L) : ℕ) : ℝ) ≤ (L : ℝ) ^ (3 / 8 : ℝ) / 2 :=
    LocSumAct.betaT_xOf_le_half_pow_six hLbig'
  have hC0 : (0 : ℝ) ≤ C := by linarith
  nlinarith [hmain, hβ, hC0]

/-- `(locsum)` with the paper's `L^{3/4}` remainder (`C_T = 3C`). -/
theorem array_locsum_h_explicit34 {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) {C : ℝ} (hC1 : 1 ≤ C)
    (hCM : LocSum.Mb p (LocSumAct.qOf p m) < C) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ A : ℕ, L ≤ A →
      Swarming.Uniform.arrayMeasure N (LsBad N p m C L A)
          ≤ ENNReal.ofReal (Real.exp (-c * LocSumAct.xOf L)) ∧
      (∀ U : Swarming.Uniform.Array N, U ∉ LsBad N p m C L A → ∀ j : Fin N,
        ∀ a0 b0 : ℕ, A ≤ a0 → b0 ≤ A + L → a0 ≤ b0 →
          ∑ x ∈ Finset.Ico a0 b0,
              (SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x) ^ 2
            ≤ 2 * C * ((b0 : ℝ) - (a0 : ℝ)) + 3 * C * (L : ℝ) ^ (3 / 4 : ℝ)) := by
  obtain ⟨c, hc, L₀, hL⟩ := array_locsum_h_explicit (N := N) hp1 hp2 hm hC1 hCM
  refine ⟨c, hc, max L₀ 1, ?_⟩
  intro L hLbig A hA
  have hL0 : L₀ ≤ L := le_trans (le_max_left _ _) hLbig
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hLbig
  obtain ⟨hmeas, hbound⟩ := hL L hL0 A hA
  refine ⟨hmeas, fun U hU j a0 b0 ha hb hab => ?_⟩
  have hmain := hbound U hU j a0 b0 ha hb hab
  have hL1' : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
  have hmono : (L : ℝ) ^ (3 / 8 : ℝ) ≤ (L : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1' (by norm_num)
  have hC0 : (0 : ℝ) ≤ C := by linarith
  nlinarith [hmain, hmono, hC0]

end LocSumR1

namespace Loccoord

/-- **(loccoord) with the sharp explicit remainder, record window.**
Same statement as `Loccoord.loccoord_record_window`, with the additive remainder
`3C·betaT (xOf L)` replaced by `(3/2)·C·L^{3/8}`. -/
theorem loccoord_record_window_explicit {N : ℕ} {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m) {C : ℝ} (hC1 : 1 ≤ C)
    (hCM : LocSum.Mb p (LocSumAct.qOf p m) < C) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ T r : ℕ, (T + 3) * L ≤ r →
      Swarming.Uniform.arrayMeasure N (LocSumR1.LsBad N p m C L (r - (T + 2) * L))
          ≤ ENNReal.ofReal (Real.exp (-c * LocSumAct.xOf L)) ∧
      ∀ U : Swarming.Uniform.Array N,
      U ∉ LocSumR1.LsBad N p m C L (r - (T + 2) * L) →
      ∀ (B : Finset (Fin N)) (hB : B.Nonempty), ∀ s t : ℕ, s ≤ t →
      (hX0 : 0 ≤ Xmin p m U B hB s) →
      r - (T + 2) * L ≤ (Xmin p m U B hB s).toNat →
      (Rmax p m U B hB t).toNat ≤ r - (T + 2) * L + L →
      Swarming.Group.average B (fun k =>
          SepGroup.Model.HA p m U t B (SepGroup.Model.X p m U t k)
            - SepGroup.Model.HA p m U s B (SepGroup.Model.X p m U s k))
        ≤ ((2 * C + 1) / 2)
            * (((Rmax p m U B hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
          + (3 * C / 2) * (L : ℝ) ^ (3 / 8 : ℝ) := by
  obtain ⟨c, hc, L₀, hL⟩ := loccoord_record_window (N := N) hp1 hp2 hm hC1 hCM
  refine ⟨c, hc, max L₀ 65536, ?_⟩
  intro L hLbig T r hr
  have hL0 : L₀ ≤ L := le_trans (le_max_left _ _) hLbig
  have hLbig' : 65536 ≤ L := le_trans (le_max_right _ _) hLbig
  obtain ⟨hmeas, hbound⟩ := hL L hL0 T r hr
  refine ⟨hmeas, fun U hU B hB s t hst hX0 hAle hLb => ?_⟩
  have hmain := hbound U hU B hB s t hst hX0 hAle hLb
  have hβ : ((LocSumAct.betaT (LocSumAct.xOf L) : ℕ) : ℝ) ≤ (L : ℝ) ^ (3 / 8 : ℝ) / 2 :=
    LocSumAct.betaT_xOf_le_half_pow_six hLbig'
  have hC0 : (0 : ℝ) ≤ C := by linarith
  nlinarith [hmain, hβ, hC0]

/-- **(loccoord) with the paper's `L^{3/4}` remainder on the record window**
(`C_T = 3C/2`). -/
theorem loccoord_record_window_explicit34 {N : ℕ} {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m) {C : ℝ} (hC1 : 1 ≤ C)
    (hCM : LocSum.Mb p (LocSumAct.qOf p m) < C) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ T r : ℕ, (T + 3) * L ≤ r →
      Swarming.Uniform.arrayMeasure N (LocSumR1.LsBad N p m C L (r - (T + 2) * L))
          ≤ ENNReal.ofReal (Real.exp (-c * LocSumAct.xOf L)) ∧
      ∀ U : Swarming.Uniform.Array N,
      U ∉ LocSumR1.LsBad N p m C L (r - (T + 2) * L) →
      ∀ (B : Finset (Fin N)) (hB : B.Nonempty), ∀ s t : ℕ, s ≤ t →
      (hX0 : 0 ≤ Xmin p m U B hB s) →
      r - (T + 2) * L ≤ (Xmin p m U B hB s).toNat →
      (Rmax p m U B hB t).toNat ≤ r - (T + 2) * L + L →
      Swarming.Group.average B (fun k =>
          SepGroup.Model.HA p m U t B (SepGroup.Model.X p m U t k)
            - SepGroup.Model.HA p m U s B (SepGroup.Model.X p m U s k))
        ≤ ((2 * C + 1) / 2)
            * (((Rmax p m U B hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
          + (3 * C / 2) * (L : ℝ) ^ (3 / 4 : ℝ) := by
  obtain ⟨c, hc, L₀, hL⟩ := loccoord_record_window_explicit (N := N) hp1 hp2 hm hC1 hCM
  refine ⟨c, hc, max L₀ 1, ?_⟩
  intro L hLbig T r hr
  have hL0 : L₀ ≤ L := le_trans (le_max_left _ _) hLbig
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hLbig
  obtain ⟨hmeas, hbound⟩ := hL L hL0 T r hr
  refine ⟨hmeas, fun U hU B hB s t hst hX0 hAle hLb => ?_⟩
  have hmain := hbound U hU B hB s t hst hX0 hAle hLb
  have hL1' : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
  have hmono : (L : ℝ) ^ (3 / 8 : ℝ) ≤ (L : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1' (by norm_num)
  have hC0 : (0 : ℝ) ≤ C := by linarith
  nlinarith [hmain, hmono, hC0]

/-- **(loccoord) with the sharp explicit remainder, full record window.**
Same statement as `Loccoord.loccoord_full_window`, with the additive remainder
`3C·betaT (xOf ((2T+4)L))` replaced by the explicit `(3/2)C(2T+4)^{3/8} L^{3/8}`. -/
theorem loccoord_full_window_explicit {N : ℕ} {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m) {C : ℝ} (hC1 : 1 ≤ C)
    (hCM : LocSum.Mb p (LocSumAct.qOf p m) < C) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ T r : ℕ, (3 * T + 6) * L ≤ r →
      Swarming.Uniform.arrayMeasure N
          (LocSumR1.LsBad N p m C ((2 * T + 4) * L) (r - (T + 2) * L))
          ≤ ENNReal.ofReal (Real.exp (-c * LocSumAct.xOf ((2 * T + 4) * L))) ∧
      ∀ U : Swarming.Uniform.Array N,
      U ∉ LocSumR1.LsBad N p m C ((2 * T + 4) * L) (r - (T + 2) * L) →
      ∀ (B : Finset (Fin N)) (hB : B.Nonempty), ∀ s t : ℕ, s ≤ t →
      (hX0 : 0 ≤ Xmin p m U B hB s) →
      r - (T + 2) * L ≤ (Xmin p m U B hB s).toNat →
      (Rmax p m U B hB t).toNat ≤ r + (T + 2) * L →
      Swarming.Group.average B (fun k =>
          SepGroup.Model.HA p m U t B (SepGroup.Model.X p m U t k)
            - SepGroup.Model.HA p m U s B (SepGroup.Model.X p m U s k))
        ≤ ((2 * C + 1) / 2)
            * (((Rmax p m U B hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
          + (3 * C / 2) * ((2 * (T : ℝ) + 4) ^ (3 / 8 : ℝ) * (L : ℝ) ^ (3 / 8 : ℝ)) := by
  obtain ⟨c, hc, L₀, hL⟩ := loccoord_full_window (N := N) hp1 hp2 hm hC1 hCM
  refine ⟨c, hc, max L₀ 65536, ?_⟩
  intro L hLbig T r hr
  have hL0 : L₀ ≤ L := le_trans (le_max_left _ _) hLbig
  have hLbig' : 65536 ≤ L := le_trans (le_max_right _ _) hLbig
  obtain ⟨hmeas, hbound⟩ := hL L hL0 T r hr
  -- the window length `(2T+4)L` is itself at least `2^16`
  have hLw : 65536 ≤ (2 * T + 4) * L := by
    have h4 : 4 ≤ 2 * T + 4 := by omega
    calc 65536 ≤ 4 * L := by omega
      _ ≤ (2 * T + 4) * L := Nat.mul_le_mul_right L h4
  refine ⟨hmeas, fun U hU B hB s t hst hX0 hXmin hRmax => ?_⟩
  have hmain := hbound U hU B hB s t hst hX0 hXmin hRmax
  have hβ : ((LocSumAct.betaT (LocSumAct.xOf ((2 * T + 4) * L)) : ℕ) : ℝ)
      ≤ (((2 * T + 4) * L : ℕ) : ℝ) ^ (3 / 8 : ℝ) / 2 :=
    LocSumAct.betaT_xOf_le_half_pow_six hLw
  have hcast : (((2 * T + 4) * L : ℕ) : ℝ) = (2 * (T : ℝ) + 4) * (L : ℝ) := by
    push_cast; ring
  have hTnn : (0 : ℝ) ≤ 2 * (T : ℝ) + 4 := by positivity
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := by positivity
  have hsplit : ((2 * (T : ℝ) + 4) * (L : ℝ)) ^ (3 / 8 : ℝ)
      = (2 * (T : ℝ) + 4) ^ (3 / 8 : ℝ) * (L : ℝ) ^ (3 / 8 : ℝ) :=
    Real.mul_rpow hTnn hLnn
  rw [hcast, hsplit] at hβ
  have hC0 : (0 : ℝ) ≤ C := by linarith
  nlinarith [hmain, hβ, hC0]

/-- **(loccoord) with the paper's `L^{3/4}` remainder on the full record window**
(`C_T = (3/2)C(2T+4)^{3/4}`). -/
theorem loccoord_full_window_explicit34 {N : ℕ} {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m) {C : ℝ} (hC1 : 1 ≤ C)
    (hCM : LocSum.Mb p (LocSumAct.qOf p m) < C) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ T r : ℕ, (3 * T + 6) * L ≤ r →
      Swarming.Uniform.arrayMeasure N
          (LocSumR1.LsBad N p m C ((2 * T + 4) * L) (r - (T + 2) * L))
          ≤ ENNReal.ofReal (Real.exp (-c * LocSumAct.xOf ((2 * T + 4) * L))) ∧
      ∀ U : Swarming.Uniform.Array N,
      U ∉ LocSumR1.LsBad N p m C ((2 * T + 4) * L) (r - (T + 2) * L) →
      ∀ (B : Finset (Fin N)) (hB : B.Nonempty), ∀ s t : ℕ, s ≤ t →
      (hX0 : 0 ≤ Xmin p m U B hB s) →
      r - (T + 2) * L ≤ (Xmin p m U B hB s).toNat →
      (Rmax p m U B hB t).toNat ≤ r + (T + 2) * L →
      Swarming.Group.average B (fun k =>
          SepGroup.Model.HA p m U t B (SepGroup.Model.X p m U t k)
            - SepGroup.Model.HA p m U s B (SepGroup.Model.X p m U s k))
        ≤ ((2 * C + 1) / 2)
            * (((Rmax p m U B hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
          + (3 * C / 2) * ((2 * (T : ℝ) + 4) ^ (3 / 4 : ℝ) * (L : ℝ) ^ (3 / 4 : ℝ)) := by
  obtain ⟨c, hc, L₀, hL⟩ := loccoord_full_window_explicit (N := N) hp1 hp2 hm hC1 hCM
  refine ⟨c, hc, max L₀ 1, ?_⟩
  intro L hLbig T r hr
  have hL0 : L₀ ≤ L := le_trans (le_max_left _ _) hLbig
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hLbig
  obtain ⟨hmeas, hbound⟩ := hL L hL0 T r hr
  refine ⟨hmeas, fun U hU B hB s t hst hX0 hXmin hRmax => ?_⟩
  have hmain := hbound U hU B hB s t hst hX0 hXmin hRmax
  have hL1' : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
  have hT1' : (1 : ℝ) ≤ 2 * (T : ℝ) + 4 := by
    have h0 : (0 : ℝ) ≤ (T : ℝ) := by positivity
    linarith
  have hmonoT : (2 * (T : ℝ) + 4) ^ (3 / 8 : ℝ) ≤ (2 * (T : ℝ) + 4) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hT1' (by norm_num)
  have hmonoL : (L : ℝ) ^ (3 / 8 : ℝ) ≤ (L : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1' (by norm_num)
  have hprod : (2 * (T : ℝ) + 4) ^ (3 / 8 : ℝ) * (L : ℝ) ^ (3 / 8 : ℝ)
      ≤ (2 * (T : ℝ) + 4) ^ (3 / 4 : ℝ) * (L : ℝ) ^ (3 / 4 : ℝ) :=
    mul_le_mul hmonoT hmonoL (by positivity) (by positivity)
  have hC0 : (0 : ℝ) ≤ C := by linarith
  nlinarith [hmain, hprod, hC0]

end Loccoord

/-! ### The covering arithmetic of the block decomposition

`numT L x = L / β + 1` blocks of length `β` cover a window of `L` sites, with overlap at most
one block.  Substituting `x = L^{1/16}` bounds that overlap by `L^{3/4}`; this is the other
place where a `C_T L^{3/4}` remainder enters the block decomposition (and, as above, it is not
tight — the honest overlap is `β = Θ(L^{3/8})`). -/

namespace LocSumAct

/-- `numT L x * β ≤ L + β`. -/
lemma numT_mul_betaT_le (L : ℕ) (x : ℝ) :
    ((numT L x : ℕ) : ℝ) * ((betaT x : ℕ) : ℝ) ≤ (L : ℝ) + ((betaT x : ℕ) : ℝ) := by
  have h : (L / betaT x) * betaT x ≤ L := Nat.div_mul_le_self L _
  have hcast : (((L / betaT x) * betaT x : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast h
  have h' : ((numT L x : ℕ) : ℝ) * ((betaT x : ℕ) : ℝ)
      = (((L / betaT x) * betaT x : ℕ) : ℝ) + ((betaT x : ℕ) : ℝ) := by
    rw [numT]; push_cast; ring
  rw [h']
  linarith

/-- `numT L (L^{1/16}) * β ≤ L + L^{3/4}`. -/
lemma numT_cover_explicit {L : ℕ} (hL : 65536 ≤ L) :
    ((numT L (xOf L) : ℕ) : ℝ) * ((betaT (xOf L) : ℕ) : ℝ)
      ≤ (L : ℝ) + (L : ℝ) ^ (3 / 4 : ℝ) := by
  have h := numT_mul_betaT_le L (xOf L)
  have hβ := betaT_xOf_le_pow_three_quarters hL
  linarith

/-- `betaT 1 = 1`. -/
lemma betaT_one : betaT 1 = 1 := by norm_num [betaT, nT, ellT]

/-- The hypothesis `2 ≤ x` in `betaT_le_half_pow_six` cannot be weakened to `x ≥ 1`:
at `x = 1` the bound `x^6/2` would read `1 ≤ 1/2`.  (For `L = L^{1/16}` the threshold
`L ≥ 2^16` used above is therefore not cosmetic, although it is not shown to be optimal.) -/
theorem betaT_half_pow_six_threshold_needed :
    ¬ ∀ x : ℝ, 1 ≤ x → ((betaT x : ℕ) : ℝ) ≤ x ^ 6 / 2 := by
  intro h
  have h1 := h 1 le_rfl
  rw [betaT_one] at h1
  norm_num at h1

end LocSumAct

namespace LocSumAct

/-- The normalisation also holds on `[0,1]`, so `β ≤ 2x^6 + 1` is valid for every `x ≥ 0`:
on `[0,1]` both ceilings equal `1`, hence `β = 1 ≤ 2x^6 + 1`.  (The requested form
`betaT_le_two_mul_pow_six_add_one` restricts to `x ≥ 1`, which is the regime
`x = L^{1/16} ≥ 1`.) -/
theorem betaT_le_two_mul_pow_six_add_one_zero {x : ℝ} (hx : 0 ≤ x) :
    ((betaT x : ℕ) : ℝ) ≤ 2 * x ^ 6 + 1 := by
  rcases le_total (1 : ℝ) x with h1 | h1
  · exact betaT_le_two_mul_pow_six_add_one h1
  have hx1 : x ≤ 1 := h1
  have hx5 : x ^ 5 ≤ 1 := pow_le_one₀ hx hx1
  have hn : nT x ≤ 1 := by
    refine Nat.ceil_le.mpr ?_
    have : x ^ 5 / 8 ≤ (1 : ℝ) := by linarith
    simpa using this
  have he : ellT x ≤ 1 := by
    refine Nat.ceil_le.mpr ?_
    simpa using hx1
  have hβ : ((betaT x : ℕ) : ℝ) ≤ 1 := by
    have h : ((betaT x : ℕ) : ℝ) = ((nT x : ℕ) : ℝ) * ((ellT x : ℕ) : ℝ) := by
      rw [betaT]; push_cast; ring
    rw [h]
    have h2 : (nT x : ℝ) ≤ 1 := by exact_mod_cast hn
    have h3 : (ellT x : ℝ) ≤ 1 := by exact_mod_cast he
    have h4 : ((nT x : ℕ) : ℝ) * ((ellT x : ℕ) : ℝ) ≤ 1 * 1 := by
      refine mul_le_mul h2 h3 ?_ ?_ <;> positivity
    simpa using h4
  have h6 : (0 : ℝ) ≤ 2 * x ^ 6 := by positivity
  linarith

end LocSumAct
