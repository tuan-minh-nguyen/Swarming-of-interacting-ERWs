/-
  **`locsum`, layer A3: the scale choice `ℓ = ⌈L^{1/16}⌉`, `n = ⌈L^{5/16}/8⌉`, `β = n·ℓ`.**

  This is the paper's arithmetic: with `ℓ ≈ L^{1/16}` and `β = n·ℓ ≈ L^{3/8}` the block
  exponent is `n(C-M)²/(2 subGnn ℓ) ≈ β(C-M)²/ℓ^5 ≈ L^{1/16}`, while the number of blocks of a
  window of `L` sites is at most `8L^{5/8} + 1`.  The union factor `numT * N * ℓ` is therefore
  polynomial of degree `11` in `x = L^{1/16}` and is absorbed by the exponential.
-/
import Swarm.A2Window

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace LocSumAct

noncomputable section

open SwarmMarks SwarmLogRatio Swarming.Uniform

/-- `x = L^{1/16}`. -/
def xOf (L : ℕ) : ℝ := (L : ℝ) ^ (1 / 16 : ℝ)

/-- The truncation depth `ℓ = ⌈x⌉`. -/
def ellT (x : ℝ) : ℕ := ⌈x⌉₊

/-- The number of sites per residue class, `n = ⌈x^5/8⌉`. -/
def nT (x : ℝ) : ℕ := ⌈x ^ 5 / 8⌉₊

/-- The block length `β = n·ℓ ≈ x^6 = L^{3/8}`. -/
def betaT (x : ℝ) : ℕ := nT x * ellT x

/-- The number of blocks covering a window of `L` sites. -/
def numT (L : ℕ) (x : ℝ) : ℕ := L / betaT x + 1

lemma subGnn_coe (k : ℕ) : (LocSum.subGnn k : ℝ) = ((2 * (k : ℝ) + 1) ^ 2 / 2) ^ 2 := by
  simp [LocSum.subGnn]

lemma subGnn_pos (k : ℕ) : 0 < (LocSum.subGnn k : ℝ) := by
  rw [subGnn_coe]
  positivity

lemma sum_subGnn_coe (n k : ℕ) :
    ((∑ _i : Fin n, LocSum.subGnn k : ℝ≥0) : ℝ) = (n : ℝ) * (LocSum.subGnn k : ℝ) := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

lemma le_ellT (x : ℝ) : x ≤ (ellT x : ℝ) := Nat.le_ceil x

lemma ellT_one_le {x : ℝ} (hx : 1 ≤ x) : 1 ≤ ellT x := by
  rw [ellT, Nat.one_le_iff_ne_zero, Ne, Nat.ceil_eq_zero]
  push_neg
  linarith

lemma ellT_le_two {x : ℝ} (hx : 1 ≤ x) : (ellT x : ℝ) ≤ 2 * x := by
  have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ x by linarith)
  rw [ellT]
  linarith

lemma nT_lower (x : ℝ) : x ^ 5 / 8 ≤ (nT x : ℝ) := Nat.le_ceil _

lemma nT_one_le {x : ℝ} (hx : 1 ≤ x) : 1 ≤ nT x := by
  rw [nT, Nat.one_le_iff_ne_zero, Ne, Nat.ceil_eq_zero]
  push_neg
  have : (1 : ℝ) ≤ x ^ 5 := one_le_pow₀ hx
  linarith

lemma betaT_lower {x : ℝ} (hx : 1 ≤ x) : x ^ 6 / 8 ≤ (betaT x : ℝ) := by
  have h1 : x ≤ (ellT x : ℝ) := le_ellT x
  have h2 : x ^ 5 / 8 ≤ (nT x : ℝ) := nT_lower x
  have h3 : x ^ 5 / 8 * x ≤ (nT x : ℝ) * (ellT x : ℝ) :=
    mul_le_mul h2 h1 (by linarith) (by positivity)
  have h4 : x ^ 6 / 8 = x ^ 5 / 8 * x := by ring
  show x ^ 6 / 8 ≤ (betaT x : ℝ)
  rw [h4, betaT]
  push_cast
  linarith

lemma betaT_pos {x : ℝ} (hx : 1 ≤ x) : 0 < (betaT x : ℝ) := by
  have := betaT_lower hx
  have : (0 : ℝ) < x ^ 6 / 8 := by positivity
  linarith

lemma subGnn_le {x : ℝ} (hx : 1 ≤ x) : (LocSum.subGnn (ellT x) : ℝ) ≤ 324 * x ^ 4 := by
  have h1 : (1 : ℝ) ≤ (ellT x : ℝ) := by exact_mod_cast ellT_one_le hx
  have h2 : (ellT x : ℝ) ≤ 2 * x := ellT_le_two hx
  have h3 : (0 : ℝ) ≤ (ellT x : ℝ) := by linarith
  rw [subGnn_coe]
  have h4 : 2 * (ellT x : ℝ) + 1 ≤ 3 * (ellT x : ℝ) := by linarith
  have h5 : (0 : ℝ) ≤ 2 * (ellT x : ℝ) + 1 := by linarith
  have h6 : (2 * (ellT x : ℝ) + 1) ^ 2 ≤ (3 * (ellT x : ℝ)) ^ 2 := by
    apply pow_le_pow_left₀ h5 h4
  have h7 : (3 * (ellT x : ℝ)) ^ 2 = 9 * (ellT x : ℝ) ^ 2 := by ring
  have h8 : ((2 * (ellT x : ℝ) + 1) ^ 2 / 2) ^ 2 ≤ ((3 * (ellT x : ℝ)) ^ 2 / 2) ^ 2 := by
    gcongr
  have h9 : ((3 * (ellT x : ℝ)) ^ 2 / 2) ^ 2 = 81 / 4 * (ellT x : ℝ) ^ 4 := by
    rw [h7]; ring
  have h10 : (ellT x : ℝ) ^ 4 ≤ (2 * x) ^ 4 := by
    apply pow_le_pow_left₀ h3 h2
  have h11 : (2 * x) ^ 4 = 16 * x ^ 4 := by ring
  have h12 : (81 / 4 : ℝ) * (ellT x : ℝ) ^ 4 ≤ 81 / 4 * (16 * x ^ 4) := by
    have : (0:ℝ) < 81/4 := by norm_num
    exact mul_le_mul_of_nonneg_left (by rw [← h11]; exact h10) this.le
  linarith

lemma numT_le {L : ℕ} {x : ℝ} (hx : 1 ≤ x) :
    (numT L x : ℝ) ≤ 8 * (L : ℝ) / x ^ 6 + 1 := by
  have hβ := betaT_lower hx
  have hx6 : (0 : ℝ) < x ^ 6 := by positivity
  have h1 : ((L / betaT x : ℕ) : ℝ) ≤ (L : ℝ) / (betaT x : ℝ) := Nat.cast_div_le
  have h2 : (L : ℝ) / (betaT x : ℝ) ≤ (L : ℝ) / (x ^ 6 / 8) := by
    refine div_le_div_of_nonneg_left (by positivity) ?_ hβ
    linarith
  have h3 : (L : ℝ) / (x ^ 6 / 8) = 8 * (L : ℝ) / x ^ 6 := by
    field_simp
  rw [numT]
  push_cast
  linarith

/-- **The exponent of the block bound at the chosen scale.**  With `D = C - M ≥ 0` and
`x ≥ 1`, the block exponent `(n D)^2 / (2 ∑ subGnn)` is at least `D^2 x / 5184`. -/
lemma exp_arg_lower {x D : ℝ} (hx : 1 ≤ x) (hD : 0 ≤ D) :
    D ^ 2 * x / 5184 ≤ ((nT x : ℝ) * D) ^ 2
      / (2 * ((∑ _i : Fin (nT x), LocSum.subGnn (ellT x) : ℝ≥0) : ℝ)) := by
  have hs := subGnn_pos (ellT x)
  have hsle := subGnn_le hx
  have hn := nT_lower x
  have hnpos : (0 : ℝ) < (nT x : ℝ) := by
    have : (0:ℝ) < x ^ 5 / 8 := by positivity
    linarith
  have hx4 : (0 : ℝ) < x ^ 4 := by positivity
  rw [sum_subGnn_coe]
  have hn' : (nT x : ℝ) ≠ 0 := ne_of_gt hnpos
  have hs' : (LocSum.subGnn (ellT x) : ℝ) ≠ 0 := ne_of_gt hs
  have h3 : ((nT x : ℝ) * D) ^ 2
      / (2 * ((nT x : ℝ) * (LocSum.subGnn (ellT x) : ℝ)))
      = (nT x : ℝ) * D ^ 2 / (2 * (LocSum.subGnn (ellT x) : ℝ)) := by
    field_simp
  have h2 : (x ^ 5 / 8) * D ^ 2 / (2 * 324 * x ^ 4)
      ≤ (nT x : ℝ) * D ^ 2 / (2 * 324 * x ^ 4) := by
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    nlinarith
  have h1 : (nT x : ℝ) * D ^ 2 / (2 * 324 * x ^ 4)
      ≤ (nT x : ℝ) * D ^ 2 / (2 * (LocSum.subGnn (ellT x) : ℝ)) := by
    refine div_le_div_of_nonneg_left (by positivity) (by linarith) ?_
    linarith
  have h4 : D ^ 2 * x / 5184 = (x ^ 5 / 8) * D ^ 2 / (2 * 324 * x ^ 4) := by
    field_simp
    ring
  rw [h3, h4]
  exact le_trans h2 h1

/-! ### The scale arithmetic: `xOf`, its power identity, and the absorption of the union factor -/

/-- `(L^{1/16})^{16} = L`. -/
lemma xOf_pow (L : ℕ) : (xOf L) ^ 16 = (L : ℝ) := by
  have hL : (0 : ℝ) ≤ (L : ℝ) := by positivity
  rw [xOf, ← Real.rpow_natCast ((L : ℝ) ^ (1 / 16 : ℝ)) 16,
    ← Real.rpow_mul hL]
  norm_num

lemma one_le_xOf {L : ℕ} (hL : 1 ≤ L) : 1 ≤ xOf L := by
  rw [xOf]
  exact Real.one_le_rpow (by exact_mod_cast hL) (by norm_num)

lemma xOf_tendsto : Tendsto (fun L : ℕ => xOf L) atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 16)).comp tendsto_natCast_atTop_atTop

/-- **Absorption.**  Any fixed polynomial factor of degree at most `11` is eventually killed by
the exponential rate `e^{-c x}`: `C x^11 e^{-cx} ≤ e^{-cx/2}` eventually. -/
lemma eventually_poly_mul_exp_le {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, C * x ^ 11 * Real.exp (-c * x) ≤ Real.exp (-(c / 2) * x) := by
  set c₂ := c / 2 with hc₂def
  have hc₂ : 0 < c₂ := by rw [hc₂def]; linarith
  have hcp : (0 : ℝ) < c₂ ^ 11 := by positivity
  have ht : Tendsto (fun x : ℝ => c₂ * x) atTop atTop :=
    Filter.tendsto_id.const_mul_atTop hc₂
  have h0 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 11).comp ht
  have hεpos : (0 : ℝ) < c₂ ^ 11 / (1 + C) := by positivity
  have hev : ∀ᶠ x : ℝ in atTop,
      (c₂ * x) ^ 11 * Real.exp (-(c₂ * x)) ≤ c₂ ^ 11 / (1 + C) :=
    h0.eventually (Iic_mem_nhds hεpos)
  filter_upwards [hev] with x hx
  have hsplit : (c₂ * x) ^ 11 = c₂ ^ 11 * x ^ 11 := by ring
  rw [hsplit, div_eq_mul_one_div] at hx
  have hx11 : x ^ 11 * Real.exp (-(c₂ * x)) ≤ 1 / (1 + C) := by
    refine le_of_mul_le_mul_left ?_ hcp
    have h1 : c₂ ^ 11 * (x ^ 11 * Real.exp (-(c₂ * x)))
        = c₂ ^ 11 * x ^ 11 * Real.exp (-(c₂ * x)) := by ring
    rw [h1]
    exact hx
  have hexp : Real.exp (-c * x)
      = Real.exp (-(c₂ * x)) * Real.exp (-(c₂ * x)) := by
    rw [← Real.exp_add]
    congr 1
    rw [hc₂def]; ring
  have hpos : (0 : ℝ) < Real.exp (-(c₂ * x)) := Real.exp_pos _
  have key : C * (x ^ 11 * Real.exp (-(c₂ * x))) ≤ C * (1 / (1 + C)) :=
    mul_le_mul_of_nonneg_left hx11 hC
  have hC3 : C * (1 / (1 + C)) ≤ 1 := by
    rw [mul_one_div, div_le_one (by linarith)]
    linarith
  have hfin : C * (x ^ 11 * Real.exp (-(c₂ * x))) ≤ 1 := le_trans key hC3
  have hmul := mul_le_mul_of_nonneg_right hfin hpos.le
  calc C * x ^ 11 * Real.exp (-c * x)
      = (C * (x ^ 11 * Real.exp (-(c₂ * x)))) * Real.exp (-(c₂ * x)) := by
        rw [hexp]; ring
    _ ≤ 1 * Real.exp (-(c₂ * x)) := hmul
    _ = Real.exp (-(c₂ * x)) := one_mul _
    _ = Real.exp (-(c / 2) * x) := by
        rw [hc₂def]
        congr 1
        ring

end

end LocSumAct
