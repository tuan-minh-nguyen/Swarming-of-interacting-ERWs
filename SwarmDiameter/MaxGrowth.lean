import SwarmDiameter.TrialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

open Filter Finset MeasureTheory Set
open scoped ENNReal Topology

namespace Swarming.Diameter

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A sequence of conditional trials with duration at most cubic in `L`,
success probability at least `exp (-C * L)`, and observed value at least
`a * L^β` on success gives an almost sure logarithmic lower bound. Records
must have positive lower density. -/
theorem ae_log_pow_lower_of_record_trials {ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)}
    {R : ℕ → Set Ω} (hR : ∀ t, MeasurableSet[ℱ t] (R t))
    {ρ : ℝ} (hρ : 0 < ρ)
    (hdensity : ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, ρ * (n : ℝ) ≤ (recordTimes R 0 n ω).card)
    {X M : ℕ → Ω → ℝ} (hX : ∀ t, Measurable[ℱ t] (X t))
    (hM : ∀ n m ω, n ≤ m → M n ω ≤ M m ω) (hXM : ∀ n ω, X n ω ≤ M n ω)
    (β : ℕ) {a C P : ℝ} (ha : 0 < a) (hC : 0 < C) (hP : 0 < P)
    (L₀ : ℕ) (d : ℕ → ℕ) (hd₀ : ∀ L ≥ L₀, 0 < d L) (hd : ∀ L ≥ L₀, (d L : ℝ) ≤ P * (L : ℝ) ^ 3)
    (htrial : ∀ L ≥ L₀, ∀ t {G}, MeasurableSet[ℱ t] G → G ⊆ R t →
      Real.exp (-C * (L : ℝ)) * μ.real G ≤ μ.real (G ∩ {ω | a * (L : ℝ) ^ β ≤ X (t + d L) ω})) :
    ∃ c : ℝ, 0 < c ∧ ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, c * (Real.log (n : ℝ)) ^ β ≤ M n ω := by
  let k (L : ℕ) := ⌈Real.exp ((C + 1) * (L : ℝ))⌉₊
  let b (L : ℕ) := k L ^ 2
  let q (L : ℕ) := Real.exp (-C * (L : ℝ))
  have hK : 0 < C + 1 := by linarith
  have hk (L : ℕ) : Real.exp ((C + 1) * (L : ℝ)) ≤ (k L : ℝ) := Nat.le_ceil _
  have hk₁ (L : ℕ) : (1 : ℝ) ≤ (k L : ℝ) :=
    (Real.one_le_exp_iff.mpr (by positivity)).trans (hk L)
  have hkb (L : ℕ) : (k L : ℝ) ≤ (b L : ℝ) := by
    dsimp only [b]
    push_cast
    nlinarith [hk₁ L]
  have hLb (L : ℕ) : L ≤ b L := by
    have h : (L : ℝ) ≤ Real.exp ((C + 1) * (L : ℝ)) := by
      have hCL : 0 ≤ C * (L : ℝ) := by positivity
      nlinarith [Real.add_one_le_exp ((C + 1) * (L : ℝ))]
    exact_mod_cast (h.trans ((hk L).trans (hkb L)))
  have hb : Tendsto b atTop atTop :=
    tendsto_atTop_atTop.mpr fun n => ⟨n, fun L hL => hL.trans (hLb L)⟩
  have hq (L : ℕ) : q L ≤ 1 := Real.exp_le_one_iff.mpr (by
    rw [neg_mul]
    exact neg_nonpos.mpr (by positivity))
  have hqk (L : ℕ) : (L : ℝ) ≤ q L * (k L : ℝ) := by
    calc
      _ ≤ Real.exp (L : ℝ) := by linarith [Real.add_one_le_exp (L : ℝ)]
      _ = q L * Real.exp ((C + 1) * (L : ℝ)) := by
        dsimp only [q]
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hk L) (Real.exp_pos _).le
  have hsmall : ∀ᶠ L : ℕ in atTop, (d L : ℝ) ≤ min ρ 1 * (k L : ℝ) := by
    have hmin : 0 < min ρ 1 := lt_min hρ zero_lt_one
    have h := (isLittleO_pow_exp_pos_mul_atTop 3 hK).bound (div_pos hmin hP)
    filter_upwards [eventually_ge_atTop L₀, (tendsto_natCast_atTop_atTop (R := ℝ)).eventually h] with L hL hL'
    change ‖(L : ℝ) ^ (3 : ℕ)‖ ≤ (min ρ 1 / P) * ‖Real.exp ((C + 1) * (L : ℝ))‖ at hL'
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_pos (Real.exp_pos _)] at hL'
    calc
      _ ≤ P * (L : ℝ) ^ 3 := hd L hL
      _ ≤ P * ((min ρ 1 / P) * Real.exp ((C + 1) * (L : ℝ))) :=
        mul_le_mul_of_nonneg_left hL' hP.le
      _ = min ρ 1 * Real.exp ((C + 1) * (L : ℝ)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hk L) hmin.le
  have hcount : ∀ᵐ ω ∂μ, ∀ᶠ L : ℕ in atTop,
      k L * d L ≤ (recordTimes R 0 (b L) ω).card := by
    filter_upwards [hdensity] with ω hω
    filter_upwards [hb.eventually hω, hsmall] with L hcount hs
    have hs' : (d L : ℝ) ≤ ρ * (k L : ℝ) :=
      hs.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
    have hle : (k L : ℝ) * (d L : ℝ) ≤ ((recordTimes R 0 (b L) ω).card : ℝ) := by
      calc
        _ ≤ (k L : ℝ) * (ρ * (k L : ℝ)) := mul_le_mul_of_nonneg_left hs' (by positivity)
        _ = ρ * (b L : ℝ) := by dsimp only [b]; push_cast; ring
        _ ≤ _ := hcount
    exact_mod_cast hle
  let E (L : ℕ) := if L₀ ≤ L then {ω | M (b L + d L) ω < a * (L : ℝ) ^ β ∧
    k L * d L ≤ (recordTimes R 0 (b L) ω).card} else ∅
  have hprob (L : ℕ) : μ.real (E L) ≤ Real.exp (-(L : ℝ)) := by
    by_cases hL : L₀ ≤ L
    · let B (t : ℕ) := {ω | a * (L : ℝ) ^ β ≤ X (t + d L) ω}
      have hB (t : ℕ) : MeasurableSet[ℱ (t + d L)] (B t) := hX _ measurableSet_Ici
      have hsub : E L ⊆ {ω | ω ∈ (Set.univ : Set Ω) ∧ (∀ t ∈ Finset.Icc 0 (b L), ω ∉ B t) ∧
          k L * d L ≤ (recordTimes R 0 (b L) ω).card} := by
        intro ω hω
        simp only [E, if_pos hL] at hω
        refine ⟨Set.mem_univ _, ?_, hω.2⟩
        intro t ht htB
        have ht₀ := (Finset.mem_Icc.mp ht).2
        exact hω.1.not_ge (htB.trans ((hXM (t + d L) ω).trans
          (hM (t + d L) (b L + d L) ω (by omega))))
      calc
        _ ≤ (1 - q L) ^ k L := by
          refine (measureReal_mono hsub (measure_ne_top μ _)).trans ?_
          simpa only [probReal_univ, mul_one] using
            no_success_prob_le_pow (μ := μ) (hd₀ L hL) (hq L) hR hB (htrial L hL)
              (k L) 0 (b L) (G := Set.univ) MeasurableSet.univ
        _ ≤ (Real.exp (-q L)) ^ k L :=
          pow_le_pow_left₀ (sub_nonneg.mpr (hq L)) (by linarith [Real.add_one_le_exp (-q L)]) _
        _ ≤ _ := by
          rw [← Real.exp_nat_mul]
          exact Real.exp_le_exp.mpr (by linarith [hqk L])
    · simp only [E, if_neg hL, measureReal_empty]
      exact (Real.exp_pos _).le
  have hsum : (∑' L : ℕ, μ (E L)) ≠ ∞ := by
    have hs : Summable (fun L : ℕ => Real.exp (-(L : ℝ))) := by
      have hs' := summable_geometric_of_lt_one (Real.exp_pos (-1)).le
        (Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0))
      convert hs' using 1
      funext L
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    apply ne_top_of_le_ne_top hs.tsum_ofReal_ne_top
    apply ENNReal.tsum_le_tsum
    intro L
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ (E L))]
    exact ENNReal.ofReal_le_ofReal (hprob L)
  let A := 2 * (C + 1) + 7
  have hA : 0 < A := by dsimp only [A]; linarith
  have htime : ∀ᶠ L : ℕ in atTop, (↑(b L + d L) : ℝ) ≤ Real.exp (A * (L : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1, hsmall] with L hL hs
    have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have h₁ : (1 : ℝ) ≤ Real.exp ((C + 1) * (L : ℝ)) := Real.one_le_exp_iff.mpr (by positivity)
    have hk' : (k L : ℝ) ≤ 2 * Real.exp ((C + 1) * (L : ℝ)) := by
      have h := Nat.ceil_lt_add_one (Real.exp_pos ((C + 1) * (L : ℝ))).le
      change (k L : ℝ) < Real.exp ((C + 1) * (L : ℝ)) + 1 at h
      linarith
    have hb' : (b L : ℝ) ≤ 4 * Real.exp (2 * (C + 1) * (L : ℝ)) := by
      dsimp only [b]
      rw [Nat.cast_pow]
      calc
        _ ≤ (2 * Real.exp ((C + 1) * (L : ℝ))) ^ (2 : ℕ) := pow_le_pow_left₀ (by positivity) hk' _
        _ = _ := by
          rw [mul_pow, ← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * ((C + 1) * (L : ℝ)) =
            2 * (C + 1) * (L : ℝ) by push_cast; ring, show (2 : ℝ) ^ 2 = 4 by norm_num]
    have hd' : (d L : ℝ) ≤ (b L : ℝ) :=
      hs.trans ((mul_le_of_le_one_left (by positivity) (min_le_right _ _)).trans (hkb L))
    have h₈ : 8 ≤ Real.exp (7 * (L : ℝ)) := by linarith [Real.add_one_le_exp (7 * (L : ℝ))]
    push_cast
    calc
      _ ≤ 2 * (b L : ℝ) := by linarith
      _ ≤ 8 * Real.exp (2 * (C + 1) * (L : ℝ)) := by linarith
      _ ≤ Real.exp (7 * (L : ℝ)) * Real.exp (2 * (C + 1) * (L : ℝ)) :=
        mul_le_mul_of_nonneg_right h₈ (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp only [A]; ring
  refine ⟨a * (1 / (2 * A)) ^ β, by positivity, ?_⟩
  filter_upwards [ae_eventually_notMem hsum, hcount] with ω hω hc
  have hgood : ∀ᶠ L : ℕ in atTop, (↑(b L + d L) : ℝ) ≤ Real.exp (A * (L : ℝ)) ∧
      a * (L : ℝ) ^ β ≤ M (b L + d L) ω := by
    filter_upwards [hω, hc, htime, eventually_ge_atTop L₀] with L hE hc' ht hL
    refine ⟨ht, le_of_not_gt (fun h => ?_)⟩
    exact hE (by simpa only [E, if_pos hL, Set.mem_ofPred_eq] using And.intro h hc')
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hgood
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / A) atTop atTop :=
    Tendsto.atTop_div_const hA (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlog.eventually_ge_atTop (max 2 ((J : ℝ) + 1))] with n hn hn'
  let x := Real.log (n : ℝ) / A
  let L := ⌊x⌋₊
  change max 2 ((J : ℝ) + 1) ≤ x at hn'
  have hx : 0 ≤ x := by linarith [(le_max_left (2 : ℝ) ((J : ℝ) + 1)).trans hn']
  have hL := Nat.lt_floor_add_one x
  have hJL : J ≤ L := by
    have h : (J : ℝ) ≤ (L : ℝ) := by linarith [(le_max_right (2 : ℝ) ((J : ℝ) + 1)).trans hn']
    exact_mod_cast h
  obtain ⟨hLtime, hLmax⟩ := hJ L hJL
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnL : b L + d L ≤ n := by
    have h : A * (L : ℝ) ≤ Real.log (n : ℝ) := by
      have hh := (le_div_iff₀ hA).mp (Nat.floor_le hx)
      simpa only [mul_comm] using hh
    exact_mod_cast (hLtime.trans ((Real.exp_le_exp.mpr h).trans_eq (Real.exp_log hn₀)))
  have hhalf : x / 2 ≤ (L : ℝ) := by
    linarith [(le_max_left (2 : ℝ) ((J : ℝ) + 1)).trans hn']
  calc
    _ = a * (x / 2) ^ β := by
      rw [mul_assoc, ← mul_pow]
      congr 2
      dsimp only [x]
      field_simp
    _ ≤ a * (L : ℝ) ^ β := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hhalf _) ha.le
    _ ≤ _ := hLmax.trans (hM (b L + d L) n ω hnL)

end Swarming.Diameter
