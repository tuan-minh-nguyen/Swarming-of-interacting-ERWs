import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Real
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
    mul_nonneg ha.le (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n]))
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
    change i + k + 2 = j + k + 2 at h'
    omega
  have hs : Summable (fun n : ℕ => ((↑(n + k) : ℝ) + 2) ^ (-2 : ℝ)) := by
    have hsum := Real.summable_nat_rpow.mpr (show (-2 : ℝ) < -1 by norm_num)
    have hh := hsum.comp_injective hinj
    change Summable (fun n : ℕ => (↑(n + k + 2) : ℝ) ^ (-2 : ℝ)) at hh
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hh
  have hsum : (∑' n : ℕ, μ (A (n + k))) ≠ ∞ := by
    apply ne_top_of_le_ne_top hs.tsum_ofReal_ne_top
    refine ENNReal.tsum_le_tsum (fun n => ?_)
    calc
      μ (A (n + k)) = ENNReal.ofReal (μ.real (A (n + k))) :=
        (ENNReal.ofReal_toReal (measure_ne_top μ (A (n + k)))).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hprob (n + k) (by omega))
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

/-- The almost sure lower bound for the running maximum transfers to a lower
tail bound through the same finite-horizon probability estimate. -/
theorem eventually_exp_le_of_ae_log_pow_lower {μ : Measure Ω} [IsProbabilityMeasure μ]
    {M : ℕ → Ω → ℝ} {β : ℕ} (hβ : 0 < β) {a : ℝ} (ha : 0 < a)
    (hM : ∀ n, Measurable (M n))
    (hlower : ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, a * (Real.log (n : ℝ)) ^ β ≤ M n ω)
    {b : ℝ → ℝ}
    (hprob : ∀ x : ℝ, ∀ n : ℕ,
      μ.real {ω | x ≤ M n ω} ≤ ((n : ℝ) + 1) * b x) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ x : ℝ in atTop, Real.exp (-C * x ^ (1 / (β : ℝ))) ≤ b x := by
  let B (k : ℕ) := {ω | ∀ n : ℕ, k ≤ n → a * (Real.log (n : ℝ)) ^ β ≤ M n ω}
  have hmono : Monotone B := fun _ _ h _ hw n hn => hw n (h.trans hn)
  have hm (k : ℕ) : MeasurableSet (B k) := by
    have he : B k = ⋂ n : ℕ, ⋂ _ : k ≤ n, (M n) ⁻¹' Set.Ici (a * (Real.log (n : ℝ)) ^ β) := by
      ext ω
      simp [B]
    rw [he]
    exact MeasurableSet.iInter (fun n => MeasurableSet.iInter (fun _ => hM n measurableSet_Ici))
  have hfull : μ (⋃ k : ℕ, B k) = 1 := by
    apply (mem_ae_iff_prob_eq_one (MeasurableSet.iUnion hm)).mp
    filter_upwards [hlower] with ω hω
    obtain ⟨k, hk⟩ := eventually_atTop.mp hω
    exact Set.mem_iUnion.mpr ⟨k, hk⟩
  have ht := tendsto_measure_iUnion_atTop (μ := μ) hmono
  rw [hfull] at ht
  have ht' : Tendsto (fun k => μ.real (B k)) atTop (𝓝 ((1 : ℝ≥0∞).toReal)) :=
    (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp ht
  rw [ENNReal.toReal_one] at ht'
  obtain ⟨J, hJ⟩ := eventually_atTop.mp
    (ht'.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)))
  have hhalf : (1 / 2 : ℝ) ≤ μ.real (B J) := (hJ J le_rfl).le
  let K : ℝ := max 1 a⁻¹
  have hK : 1 ≤ K := le_max_left _ _
  have hK₀ : 0 < K := zero_lt_one.trans_le hK
  have hKa : 1 ≤ a * K := by
    calc
      _ = a * a⁻¹ := (mul_inv_cancel₀ ha.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) ha.le
  have hKβ : 1 ≤ a * K ^ β := by
    apply hKa.trans
    apply mul_le_mul_of_nonneg_left _ ha.le
    calc
      _ = K ^ (1 : ℕ) := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hK (by omega : 1 ≤ β)
  have hβr : (0 : ℝ) < (β : ℝ) := by exact_mod_cast hβ
  let r : ℝ := 1 / (β : ℝ)
  have hr : 0 < r := div_pos (by norm_num) hβr
  refine ⟨K + 6, by linarith, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    (tendsto_rpow_atTop hr).eventually_ge_atTop ((J : ℝ) + 1)] with x hx hxJ
  let t := x ^ r
  change (J : ℝ) + 1 ≤ t at hxJ
  have ht₁ : (1 : ℝ) ≤ t := le_trans (by linarith [Nat.cast_nonneg (α := ℝ) J]) hxJ
  have ht₀ : 0 ≤ t := zero_le_one.trans ht₁
  let s := K * t
  have hs₀ : 0 ≤ s := mul_nonneg hK₀.le ht₀
  let n := ⌈Real.exp s⌉₊
  have hn : Real.exp s ≤ (n : ℝ) := Nat.le_ceil _
  have hJn : J ≤ n := by
    have hj : (J : ℝ) ≤ n := by
      have hst : t ≤ s := by simpa only [one_mul, s] using mul_le_mul_of_nonneg_right hK ht₀
      linarith [hst, Real.add_one_le_exp s, hn, hxJ]
    exact_mod_cast hj
  have hlog : s ≤ Real.log (n : ℝ) := by
    rw [← Real.log_exp s]
    exact Real.log_le_log (Real.exp_pos _) hn
  have hroot : t ^ β = x := by
    dsimp only [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    have h : r * (β : ℝ) = 1 := by
      dsimp only [r]
      field_simp
    rw [h, Real.rpow_one]
  have hxlog : x ≤ a * (Real.log (n : ℝ)) ^ β := by
    calc
      _ ≤ (a * K ^ β) * x := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hKβ hx
      _ = a * s ^ β := by rw [show s = K * t from rfl, mul_pow, hroot]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs₀ hlog β) ha.le
  have hsub : B J ⊆ {ω | x ≤ M n ω} := by
    intro ω hω
    exact hxlog.trans (hω n hJn)
  have hbound : (1 / 2 : ℝ) ≤ ((n : ℝ) + 1) * b x :=
    hhalf.trans ((measureReal_mono hsub).trans (hprob x n))
  have hn' : (n : ℝ) + 1 ≤ 3 * Real.exp s := by
    have hceil : (n : ℝ) < Real.exp s + 1 := Nat.ceil_lt_add_one (Real.exp_pos _).le
    linarith [Real.one_le_exp_iff.mpr hs₀]
  have hexp : 6 ≤ Real.exp (6 * t) := by linarith [Real.add_one_le_exp (6 * t)]
  have hsmall : 3 * Real.exp (-(6 * t)) ≤ (1 / 2 : ℝ) := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    linarith
  have htarget : ((n : ℝ) + 1) * Real.exp (-(K + 6) * t) ≤ (1 / 2 : ℝ) := by
    calc
      _ ≤ (3 * Real.exp s) * Real.exp (-(K + 6) * t) :=
        mul_le_mul_of_nonneg_right hn' (Real.exp_pos _).le
      _ = 3 * Real.exp (-(6 * t)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        dsimp only [s]
        ring
      _ ≤ _ := hsmall
  exact (mul_le_mul_iff_of_pos_left (by positivity : 0 < (n : ℝ) + 1)).mp (htarget.trans hbound)

end Swarming.Diameter
