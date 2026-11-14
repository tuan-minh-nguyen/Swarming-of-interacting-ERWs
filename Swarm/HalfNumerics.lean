/-
# The numerical half package: `Numerics`, `η = ⌈C_T L^{3/4}⌉`, `HalfEps`, `HalfLmin`

`M1D.halving_measured` (= `JoinStep.halving_of_coalesce_sharp` at the actual trajectory) carries,
besides the block clauses, the martingale clause and one coalescence time, four *purely numerical*
premises in `L`:

  `hnum : Numerics C CT L`                       (`CT L^{3/4} ≤ C L`)
  `hηdef : CT L^{3/4} ≤ η`                       for an integer `η`
  `hη    : η ≤ HalfEps C |ι| L`
  `hLmin : HalfLmin C |ι| ≤ L`

All four are consequences of `L ≥ L₀` for an explicit `L₀` depending only on `C`, `C_T` and `|ι|`;
none of them is a probabilistic statement.  This file proves that, with `η` chosen as the
canonical `⌈C_T L^{3/4}⌉`, so that the residual of the halving clause is *only* the coalescence
time.

Content, in order.

* `eventually_le_mul_rpow_quarter` - for fixed `C > 0`, `C T ≤ C L^{1/4}` eventually in `L`
  (`L^{1/4} → ∞`).
* `rpow_quarter_mul_rpow_three_quarters` - `L^{1/4} L^{3/4} = L` for `L ≥ 1`.
* `eventually_numerics` - `Numerics C CT L` eventually, i.e. `CT L^{3/4} ≤ C L`.
  (Note `C_T` is *not* required to dominate `C`: the `L^{1/4}` gain pays for it.)
* `eventually_one_le_half_mul` - `1 ≤ (ε/2) L` eventually for `ε > 0`.
* `eventually_ceil_rpow_le` - `⌈C_T L^{3/4}⌉ ≤ ε L` eventually for `ε > 0`.
* `exists_halving_thresholds` - **the package**: there is `L₀` such that for all `L ≥ L₀`,
  `Numerics C CT L`, `C T L^{3/4} ≤ ⌈CT L^{3/4}⌉`, `⌈CT L^{3/4}⌉ ≤ HalfEps C |ι| L` and
  `HalfLmin C |ι| ≤ L`, with `L₀` a function of `C`, `C_T`, `|ι|` only (chosen explicitly).
* `exists_T_ge` - the companion `T`-threshold `64 ⌈C⌉₊ ≤ T`, which is a choice of `T` only.

Exact boundary.  Pure real/integer arithmetic; no trajectory, no probability, no measure, and no
use of `UniformHalfClause`, `KnotCoalesceAll` or `FluidHalfDataAll`.
-/
import Swarm.HalvingResidual
import Swarm.LagStep

open Filter
open scoped BigOperators

namespace M1DNum

/-! ## 1. `L^{1/4} → ∞` and the `rpow` identity -/

/-- For fixed `C > 0` and any real `CT`, eventually `CT ≤ C L^{1/4}`. -/
theorem eventually_le_mul_rpow_quarter {C CT : ℝ} (hC : 0 < C) :
    ∀ᶠ L : ℕ in atTop, CT ≤ C * (L : ℝ) ^ ((1 : ℝ) / 4) := by
  have htend : Tendsto (fun L : ℕ => (L : ℝ) ^ ((1 : ℝ) / 4)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 4)).comp
      tendsto_natCast_atTop_atTop
  have h2 : ∀ᶠ L : ℕ in atTop, CT / C ≤ (L : ℝ) ^ ((1 : ℝ) / 4) :=
    htend.eventually (eventually_ge_atTop (CT / C))
  filter_upwards [h2] with L hL
  rw [div_le_iff₀ hC] at hL
  linarith

/-- `L^{1/4} · L^{3/4} = L` for a positive natural `L`. -/
theorem rpow_quarter_mul_rpow_three_quarters {L : ℕ} (hL : 1 ≤ L) :
    (L : ℝ) ^ ((1 : ℝ) / 4) * (L : ℝ) ^ ((3 : ℝ) / 4) = (L : ℝ) := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  rw [← Real.rpow_add hLpos]
  norm_num

/-! ## 2. `Numerics` is eventually true -/

/-- **`CT L^{3/4} ≤ C L` eventually in `L`,** for every real `C_T` and every `C > 0`.
The proof divides by `L^{3/4}`: the inequality is `C_T ≤ C L^{1/4}`. -/
theorem eventually_numerics {C CT : ℝ} (hC : 0 < C) :
    ∀ᶠ L : ℕ in atTop, JoinStep.Numerics C CT L := by
  filter_upwards [eventually_ge_atTop (1 : ℕ), eventually_le_mul_rpow_quarter (CT := CT) hC]
    with L hL1 hL
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have h34 : (0 : ℝ) ≤ (L : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hLpos.le _
  rw [JoinStep.Numerics]
  calc CT * (L : ℝ) ^ ((3 : ℝ) / 4)
      ≤ (C * (L : ℝ) ^ ((1 : ℝ) / 4)) * (L : ℝ) ^ ((3 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right hL h34
    _ = C * ((L : ℝ) ^ ((1 : ℝ) / 4) * (L : ℝ) ^ ((3 : ℝ) / 4)) := by ring
    _ = C * (L : ℝ) := by rw [rpow_quarter_mul_rpow_three_quarters hL1]

/-! ## 3. The ceiling allowance `η = ⌈C_T L^{3/4}⌉` -/

/-- For `ε > 0`, eventually `1 ≤ (ε/2) L`. -/
theorem eventually_one_le_half_mul {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℕ in atTop, (1 : ℝ) ≤ (ε / 2) * (L : ℝ) := by
  have hε' : (0 : ℝ) < ε / 2 := by linarith
  refine eventually_atTop.2 ⟨⌈(1 : ℝ) / (ε / 2)⌉₊, fun L hL => ?_⟩
  have h1 : (1 : ℝ) / (ε / 2) ≤ (⌈(1 : ℝ) / (ε / 2)⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (1 : ℝ) / (ε / 2) ≤ (L : ℝ) := le_trans h1 (by exact_mod_cast hL)
  rw [div_le_iff₀ hε'] at h2
  linarith

/-- **The ceiling allowance is eventually below `ε L`.**  Both
`CT L^{3/4} ≤ (ε/2) L` and `1 ≤ (ε/2) L` hold eventually, and `⌈x⌉ < x + 1`. -/
theorem eventually_ceil_rpow_le {CT ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℕ in atTop,
      (((⌈CT * (L : ℝ) ^ ((3 : ℝ) / 4)⌉₊ : ℕ) : ℝ) ≤ ε * (L : ℝ)) := by
  have hε' : (0 : ℝ) < ε / 2 := by linarith
  filter_upwards [eventually_numerics (C := ε / 2) (CT := CT) hε',
    eventually_one_le_half_mul hε] with L hnum hone
  have hnum' : CT * (L : ℝ) ^ ((3 : ℝ) / 4) ≤ (ε / 2) * (L : ℝ) := hnum
  have hsum : (ε / 2) * (L : ℝ) + (ε / 2) * (L : ℝ) = ε * (L : ℝ) := by ring
  have hnn : (0 : ℝ) ≤ (ε / 2) * (L : ℝ) := le_trans zero_le_one hone
  have key : (((⌈CT * (L : ℝ) ^ ((3 : ℝ) / 4)⌉₊ : ℕ) : ℝ))
      ≤ (ε / 2) * (L : ℝ) + 1 := by
    by_cases hx : (0 : ℝ) ≤ CT * (L : ℝ) ^ ((3 : ℝ) / 4)
    · have hlt := Nat.ceil_lt_add_one hx
      linarith
    · have hz : ⌈CT * (L : ℝ) ^ ((3 : ℝ) / 4)⌉₊ = 0 :=
        Nat.ceil_eq_zero.mpr (le_of_not_ge hx)
      rw [hz]
      push_cast
      linarith
  linarith

/-! ## 4. The package -/

/-- **The numerical half package is a threshold in `L` only.**

For `C > 0` and any error coefficient `C_T`, with `n = |ι| ≥ 1` and `η = ⌈C_T L^{3/4}⌉`, there is
an explicit `L₀` (a function of `C`, `C_T` and `n` only) such that for all `L ≥ L₀`

  `C_T L^{3/4} ≤ C L`,  `C_T L^{3/4} ≤ η`,  `η ≤ HalfEps C n · L`,  `HalfLmin C n ≤ L`.

These are exactly `hnum`, `hηdef`, `hη`, `hLmin` of `JoinStep.halving_of_coalesce_sharp` /
`M1D.halving_measured` at `η = ⌈C_T L^{3/4}⌉`.  No probability, no coalescence time. -/
theorem exists_halving_thresholds {C CT : ℝ} (hC : 0 < C) (n : ℕ) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      JoinStep.Numerics C CT L ∧
      CT * (L : ℝ) ^ ((3 : ℝ) / 4) ≤ (((⌈CT * (L : ℝ) ^ ((3 : ℝ) / 4)⌉₊ : ℕ) : ℝ)) ∧
      (((⌈CT * (L : ℝ) ^ ((3 : ℝ) / 4)⌉₊ : ℕ) : ℝ)) ≤ JoinStep.HalfEps C n * (L : ℝ) ∧
      JoinStep.HalfLmin C n ≤ (L : ℝ) := by
  have hε : (0 : ℝ) < JoinStep.HalfEps C n := JoinStep.HalfEps_pos hC n
  have hLminEv : ∀ᶠ L : ℕ in atTop, JoinStep.HalfLmin C n ≤ (L : ℝ) := by
    refine eventually_atTop.2 ⟨⌈JoinStep.HalfLmin C n⌉₊, fun L hL => ?_⟩
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast hL)
  have hall := (eventually_numerics (C := C) (CT := CT) hC).and
    ((eventually_ceil_rpow_le (CT := CT) hε).and hLminEv)
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.1 hall
  refine ⟨L₀, fun L hL => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hL₀ L hL
  exact ⟨h1, Nat.le_ceil _, h2, h3⟩

/-- The `T`-threshold companion: some `T` already exceeds `64 ⌈C⌉₊` for every real `C`. -/
theorem exists_T_ge (C : ℝ) : ∃ T : ℕ, 64 * ⌈C⌉₊ ≤ T := ⟨64 * ⌈C⌉₊, le_rfl⟩

end M1DNum
