import SwarmDiameter.RecordCubicBlock

open Filter MeasureTheory Set
open Swarming.Uniform SwarmRestart
open scoped Topology

set_option autoImplicit false

namespace Swarming.Diameter

private theorem floor_div_bounds {J : ℕ} (hJ : 1 ≤ J) {a x : ℝ}
    (ha : 0 < a) (hx : 2 * a * (J : ℝ) ≤ x) :
    J ≤ ⌊x / a⌋₊ ∧ x / (2 * a) ≤ (⌊x / a⌋₊ : ℝ) ∧ a * (⌊x / a⌋₊ : ℝ) ≤ x := by
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hy : 2 * (J : ℝ) ≤ x / a := (le_div_iff₀ ha).mpr (by linarith only [hx])
  have h1 := Nat.lt_floor_add_one (x / a)
  have h2 := Nat.floor_le (show 0 ≤ x / a by linarith only [hy, hJr])
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast (show (J : ℝ) ≤ (⌊x / a⌋₊ : ℝ) by linarith only [hJr, hy, h1])
  · rw [show x / (2 * a) = (x / a) / 2 by ring]
    linarith only [h1, hy, hJr]
  · simpa only [mul_comm a] using (le_div_iff₀ ha).mp h2

/-- A record-block bound controls the tails of the duration of a single record
interval and the maximum diameter within that interval. -/
theorem record_interval_tails_le_of_block {N : ℕ} [Nonempty (Fin N)] {p : ℝ} {m : ℕ}
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N)
    {B T C₀ L₀ : ℕ} (hB : 1 ≤ B) (hT : 1 ≤ T) {K c γ : ℝ}
    (hK : 0 ≤ K) (hc : 0 < c) (hγ : 0 < γ)
    (hblock : ∀ L ≥ L₀, ∀ r ≥ C₀ * L, (arrayMeasure N).real (recordBlockFailure p m B T L r) ≤
      K * Real.exp (-c * (L : ℝ) ^ γ)) :
    ∃ K' c' : ℝ, 0 ≤ K' ∧ 0 < c' ∧
      (∀ᶠ x : ℝ in atTop, limsup (fun r => (arrayMeasure N).real
        {U | recordIntervalExceeds (posPath p m U) r x}) atTop ≤ K' * Real.exp (-c' * x ^ γ)) ∧
      (∀ᶠ u : ℕ in atTop, limsup (fun r => (arrayMeasure N).real
        {U | (u : ℕ∞) < recordDuration (posPath p m U) r}) atTop ≤
          K' * Real.exp (-c' * (u : ℝ) ^ γ)) := by
  let X := posPath (N := N) p m
  let μ := arrayMeasure N
  let D (x : ℝ) (r : ℕ) := μ.real {U | x < pathDiameter (recordTime (X U) r).toNat (X U)}
  let W (u r : ℕ) := μ.real {U | (u : ℕ∞) < recordDuration (X U) r}
  let E (x : ℝ) (r : ℕ) := μ.real {U | recordIntervalExceeds (X U) r x}
  let J := max 1 L₀
  let k := K / (1 - Real.exp (-c * ((2 : ℝ) ^ γ - 1)))
  have hk : 0 ≤ k := by
    have hpow : (1 : ℝ) < (2 : ℝ) ^ γ := Real.one_lt_rpow (by norm_num) hγ
    exact div_nonneg hK (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith only [hc, hpow])))
  have hD (L : ℕ) (hL : J ≤ L) : limsup (D L) atTop ≤ k * Real.exp (-c * (L : ℝ) ^ γ) := by
    have hL₀ := (le_max_right 1 L₀).trans hL
    have hL₁ := (le_max_left 1 L₀).trans hL
    apply record_diameter_tail_le_of_contraction hp₀ hp₁ hm hN hK hc hγ (B := 2 * B) ?_ hL₀ hL₁
    intro l hl
    filter_upwards [eventually_ge_atTop (C₀ * (2 * l))] with r hr
    let E₁ := recordBlockFailure (N := N) p m B T (2 * l) r
    let E₂ : Set (Array N) := {U | (2 * l : ℝ) < pathDiameter (recordTime (X U) r).toNat (X U)}
    have hcover : {U : Array N | (l : ℝ) < pathDiameter
        (recordTime (X U) (r + (2 * B) * l)).toNat (X U)} ⊆ E₂ ∪ E₁ := by
      intro U hU
      by_cases h : U ∈ E₂
      · exact Or.inl h
      · apply Or.inr
        refine ⟨?_, Or.inr ?_⟩
        · simpa only [E₂, Set.mem_ofPred_eq, not_lt, Nat.cast_mul, Nat.cast_ofNat] using h
        · change ((↑(2 * l) : ℝ) / 2) <
            pathDiameter (recordTime (X U) (r + B * (2 * l))).toNat (X U)
          rw [show r + B * (2 * l) = r + (2 * B) * l by ring,
            show (↑(2 * l) : ℝ) / 2 = (l : ℝ) by push_cast; ring]
          exact hU
    have hbound := hblock (2 * l) (by omega) r hr
    have hp : (l : ℝ) ^ γ ≤ (↑(2 * l) : ℝ) ^ γ :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (show l ≤ 2 * l by omega)) hγ.le
    have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hp (neg_nonpos.mpr hc.le))
    exact (measureReal_mono hcover (measure_ne_top μ _)).trans
      ((measureReal_union_le _ _).trans (add_le_add le_rfl (hbound.trans (mul_le_mul_of_nonneg_left he hK))))
  have hW (L u : ℕ) (hL : J ≤ L) (hTu : T * L ≤ u) :
      limsup (W u) atTop ≤ (k + K) * Real.exp (-c * (L : ℝ) ^ γ) := by
    have hL₀ := (le_max_right 1 L₀).trans hL
    have hL₁ := (le_max_left 1 L₀).trans hL
    have ht := record_duration_limsup_le_of_advance (N := N) hp₀ hp₁ hm hN
      (B := B * L) (u := u) (L := (L : ℝ)) (a := K * Real.exp (-c * (L : ℝ) ^ γ))
      (Nat.mul_le_mul hB hL₁) (by
        filter_upwards [eventually_ge_atTop (C₀ * L)] with r hr
        apply (measureReal_mono (μ := μ) ?_ (measure_ne_top _ _)).trans (hblock L hL₀ r hr)
        intro U hU
        exact ⟨hU.1, Or.inl ((ENat.natCast_le_natCast.mpr hTu).trans_lt hU.2)⟩)
    exact ht.trans (by rw [add_mul]; exact add_le_add (hD L hL) le_rfl)
  let a : ℝ := 4 * (T : ℝ)
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have ha : 0 < a := by dsimp only [a]; positivity
  let c' := c / (2 * a) ^ γ
  have hc' : 0 < c' := div_pos hc (Real.rpow_pos_of_pos (by positivity) _)
  have hlarge : ∀ᶠ x : ℝ in atTop, 2 * a * (J : ℝ) ≤ x := eventually_ge_atTop _
  have herr {x : ℝ} {L : ℕ} (hx : 0 ≤ x) (h : x / (2 * a) ≤ (L : ℝ)) :
      Real.exp (-c * (L : ℝ) ^ γ) ≤ Real.exp (-c' * x ^ γ) := by
    have hpow := Real.rpow_le_rpow (div_nonneg hx (by positivity)) h hγ.le
    apply Real.exp_le_exp.mpr
    have hn := mul_le_mul_of_nonpos_left hpow (neg_nonpos.mpr hc.le)
    rw [Real.div_rpow hx (by positivity)] at hn
    dsimp only [c']
    linarith only [hn, show -c * (x ^ γ / (2 * a) ^ γ) = -(c / (2 * a) ^ γ) * x ^ γ by ring]
  have hJ : 1 ≤ J := le_max_left _ _
  have hDlim (x : ℝ) : Tendsto (D x) atTop (𝓝 (limsup (D x) atTop)) := by
    have h := (tendsto_record_diameter_tail_occupation (N := N) hp₀ hp₁ hm hN x).2.2
    change Tendsto (D x) atTop (𝓝 _) at h
    rw [h.limsup_eq]
    exact h
  have hWlim (u : ℕ) : Tendsto (W u) atTop (𝓝 (limsup (W u) atTop)) := by
    have h := (tendsto_record_duration_tail_occupation (N := N) hp₀ hp₁ hm hN u).2.2
    change Tendsto (W u) atTop (𝓝 _) at h
    rw [h.limsup_eq]
    exact h
  refine ⟨k + (k + K), c', by positivity, hc', ?_, ?_⟩
  · filter_upwards [hlarge] with x hx
    let L := ⌊x / a⌋₊
    obtain ⟨hL, hLlo, hLhi⟩ := floor_div_bounds hJ ha hx
    have hx₀ := (show 0 ≤ 2 * a * (J : ℝ) by positivity).trans hx
    have hTL : ((T * L : ℕ) : ℝ) ≤ x / 4 := by
      change a * (L : ℝ) ≤ x at hLhi
      push_cast
      dsimp only [a] at hLhi
      linarith only [hLhi]
    have hLx : (L : ℝ) ≤ x / 2 := by
      have h₁ := le_mul_of_one_le_left (Nat.cast_nonneg (α := ℝ) L) hTr
      push_cast at hTL
      linarith only [h₁, hTL, hx₀]
    have hpoint (r : ℕ) : E x r ≤ D L r + W (T * L) r := by
      refine (record_interval_exceedance_prob_le_initial_or_duration hp₀ hp₁ hm hN r x).trans ?_
      apply add_le_add
      · exact measureReal_mono (fun _ h => hLx.trans_lt h) (measure_ne_top _ _)
      · apply measureReal_mono ?_ (measure_ne_top _ _)
        intro U hU
        have hlt : ((T * L : ℕ) : ℝ) < ((recordDuration (X U) r).toNat : ℝ) := hTL.trans_lt hU
        exact (ENat.natCast_lt_natCast.mpr (by exact_mod_cast hlt)).trans_le (ENat.natCast_toNat_le_self _)
    have hlim := ((hDlim L).add (hWlim (T * L))).limsup_eq
    have hmono : limsup (E x) atTop ≤ limsup (fun r => D L r + W (T * L) r) atTop :=
      limsup_le_limsup (Eventually.of_forall hpoint)
        (isCoboundedUnder_le_of_le atTop (fun _ => measureReal_nonneg))
        ⟨2, eventually_map.mpr (Eventually.of_forall fun r => by
          have h₁ : D L r ≤ 1 := measureReal_le_one
          have h₂ : W (T * L) r ≤ 1 := measureReal_le_one
          linarith only [h₁, h₂])⟩
    calc
      _ ≤ limsup (D L) atTop + limsup (W (T * L)) atTop := hmono.trans_eq hlim
      _ ≤ (k + (k + K)) * Real.exp (-c * (L : ℝ) ^ γ) := by
        rw [add_mul]
        exact add_le_add (hD L hL) (hW L _ hL le_rfl)
      _ ≤ _ := mul_le_mul_of_nonneg_left (herr hx₀ hLlo) (by positivity)
  · filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually hlarge] with u hu
    let L := ⌊(u : ℝ) / a⌋₊
    obtain ⟨hL, hLlo, hLhi⟩ := floor_div_bounds hJ ha hu
    have hTL : T * L ≤ u := by
      change a * (L : ℝ) ≤ (u : ℝ) at hLhi
      dsimp only [a] at hLhi
      have h : (T : ℝ) * (L : ℝ) ≤ (u : ℝ) := by
        linarith only [hLhi, mul_nonneg (Nat.cast_nonneg (α := ℝ) T) (Nat.cast_nonneg (α := ℝ) L)]
      exact_mod_cast h
    calc
      _ ≤ (k + K) * Real.exp (-c * (L : ℝ) ^ γ) := hW L u hL hTL
      _ ≤ (k + K) * Real.exp (-c' * (u : ℝ) ^ γ) :=
        mul_le_mul_of_nonneg_left (herr (Nat.cast_nonneg _) hLlo) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hk]) (Real.exp_pos _).le

end Swarming.Diameter
