import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter MeasureTheory
open scoped ENNReal Topology

namespace Swarming.Diameter

variable {Ω : Type*} [MeasurableSpace Ω]

/-- An upper tail bound for the running maximum on the stretched-exponential
scale gives an almost sure logarithmic upper bound. -/
theorem ae_log_pow_upper_of_tail {μ : Measure Ω} [IsProbabilityMeasure μ]
    {M : ℕ → Ω → ℝ} {β : ℕ} (hβ : 0 < β) {c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ x : ℝ in atTop, ∀ n : ℕ,
      μ.real {ω | x ≤ M n ω} ≤ ((n : ℝ) + 1) * Real.exp (-c * x ^ (1 / (β : ℝ)))) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, M n ω ≤ C * (Real.log (n : ℝ)) ^ β := by
  obtain ⟨x₀, h₀⟩ := eventually_atTop.mp h
  let a : ℝ := 3 / c
  have ha : 0 < a := div_pos (by norm_num) hc
  let b (n : ℕ) := a * Real.log ((n : ℝ) + 2)
  have hb₀ (n : ℕ) : 0 ≤ b n :=
    mul_nonneg ha.le (Real.log_nonneg (by positivity))
  have hβr : (0 : ℝ) < (β : ℝ) := by exact_mod_cast hβ
  let s := max x₀ 1
  let k := ⌈Real.exp (s / a)⌉₊
  have hlarge (n : ℕ) (hn : k ≤ n) : x₀ ≤ b n ^ β := by
    have hkl : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlog : s / a ≤ Real.log ((n : ℝ) + 2) := by
      rw [← Real.log_exp (s / a)]
      have hceil : Real.exp (s / a) ≤ (k : ℝ) := Nat.le_ceil _
      exact Real.log_le_log (Real.exp_pos _) (hceil.trans (hkl.trans (by linarith)))
    have hs : s ≤ b n := by
      have hh := (div_le_iff₀ ha).mp hlog
      simpa only [b, mul_comm] using hh
    have hb₁ : 1 ≤ b n := (le_max_right x₀ 1).trans hs
    have hbp : b n ≤ b n ^ β := by
      calc
        b n = (b n) ^ (1 : ℕ) := (pow_one _).symm
        _ ≤ _ := pow_le_pow_right₀ hb₁ (by omega : 1 ≤ β)
    exact (le_max_left x₀ 1).trans (hs.trans hbp)
  have hpow (n : ℕ) : ((b n) ^ β) ^ (1 / (β : ℝ)) = b n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hb₀ n)]
    have he : (β : ℝ) * (1 / (β : ℝ)) = 1 := by field_simp
    rw [he, Real.rpow_one]
  let A (n : ℕ) : Set Ω := {ω | (b n) ^ β ≤ M n ω}
  have hprob (n : ℕ) (hn : k ≤ n) : μ.real (A n) ≤ ((n : ℝ) + 2) ^ (-2 : ℝ) := by
    have he : Real.exp (-c * ((b n) ^ β) ^ (1 / (β : ℝ))) =
        ((n : ℝ) + 2) ^ (-3 : ℝ) := by
      rw [hpow, Real.rpow_def_of_pos (by positivity)]
      congr 1
      dsimp only [b, a]
      field_simp
      <;> ring
    calc
      _ ≤ ((n : ℝ) + 1) * Real.exp (-c * ((b n) ^ β) ^ (1 / (β : ℝ))) :=
        h₀ _ (hlarge n hn) n
      _ ≤ ((n : ℝ) + 2) * (((n : ℝ) + 2) ^ (-3 : ℝ)) := by
        rw [he]
        exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by positivity) _)
      _ = (((n : ℝ) + 2) ^ (1 : ℝ)) * (((n : ℝ) + 2) ^ (-3 : ℝ)) := by
        rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add (by positivity : 0 < (n : ℝ) + 2)]
        norm_num
  have hinj : Function.Injective (fun n : ℕ => (n + k) + 2) := by
    intro i j h'
    omega
  have hs : Summable (fun n : ℕ => ((↑(n + k) : ℝ) + 2) ^ (-2 : ℝ)) := by
    have hsum := Real.summable_nat_rpow.mpr (show (-2 : ℝ) < -1 by norm_num)
    simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_ofNat] using hsum.comp_injective hinj
  have hsum : (∑' n : ℕ, μ (A (n + k))) ≠ ∞ := by
    apply ne_top_of_le_ne_top hs.tsum_ofReal_ne_top
    refine ENNReal.tsum_le_tsum (fun n => ?_)
    rw [← ofReal_measureReal (measure_ne_top μ (A (n + k)))]
    exact ENNReal.ofReal_le_ofReal (hprob (n + k) (by omega))
  refine ⟨(2 * a) ^ β, pow_pos (by positivity) _, ?_⟩
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  obtain ⟨j, hj⟩ := eventually_atTop.mp hω
  refine eventually_atTop.mpr ⟨j + k + 2, fun n hn => ?_⟩
  have hh := hj (n - k) (by omega)
  rw [Nat.sub_add_cancel (by omega : k ≤ n)] at hh
  change ¬ (b n) ^ β ≤ M n ω at hh
  have hn₂ : (2 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show (2 : ℕ) ≤ n by omega)
  have hlog : Real.log ((n : ℝ) + 2) ≤ 2 * Real.log (n : ℝ) := by
    have hsq : (n : ℝ) + 2 ≤ (n : ℝ) ^ (2 : ℕ) := by
      nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) - 2 by linarith)
        (show 0 ≤ (n : ℝ) + 1 by positivity)]
    simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log (by positivity) hsq
  calc
    _ ≤ (b n) ^ β := le_of_lt (lt_of_not_ge hh)
    _ ≤ ((2 * a) * Real.log (n : ℝ)) ^ β := by
      apply pow_le_pow_left₀ (hb₀ n)
      dsimp [b]
      linarith [mul_le_mul_of_nonneg_left hlog ha.le]
    _ = _ := mul_pow _ _ _

end Swarming.Diameter
