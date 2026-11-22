import SwarmDiameter.GeometricGapTail
import SwarmDiameter.MarkedGapPattern
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Asymptotics.Lemmas
import Swarm.RawLogRatio

open Filter Finset MeasureTheory Set SwarmMarks
open Swarming.Uniform
open scoped ENNReal

set_option autoImplicit false

namespace Swarming.Diameter

private theorem measureReal_lt_le_exp_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℝ} (hZ : Measurable Z)
    {a M t : ℝ} (ha : 0 < a) (hM : 0 ≤ M)
    (h : (∫⁻ ω, ENNReal.ofReal (Real.exp (a * Z ω)) ∂μ) ≤ ENNReal.ofReal M) :
    μ.real {ω | t < Z ω} ≤ M * Real.exp (-a * t) := by
  let f (ω : Ω) := ENNReal.ofReal (Real.exp (a * Z ω))
  let u := ENNReal.ofReal (Real.exp (a * t))
  have hf : Measurable f := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hZ.const_mul a))
  have hsub : {ω | t < Z ω} ⊆ {ω | u ≤ f ω} := fun ω hω =>
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_of_lt hω) ha.le))
  have hu : u ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have he : ENNReal.ofReal M / u = ENNReal.ofReal (M * Real.exp (-a * t)) := by
    dsimp only [u]
    rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), neg_mul, Real.exp_neg, div_eq_mul_inv]
  have hb := (meas_ge_le_lintegral_div (μ := μ) hf.aemeasurable hu ENNReal.ofReal_ne_top).trans
    (ENNReal.div_le_div_right h u)
  rw [he] at hb
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq
      (ENNReal.toReal_ofReal (mul_nonneg hM (Real.exp_pos _).le)))

private theorem markMeasure_hof_initial_tail {p : ℝ} {m : ℕ} (hp₀ : (1 : ℝ) / 2 < p)
    (hp₁ : p < 1) (hm : 2 ≤ m) :
    ∃ a M : ℝ, 0 < a ∧ 0 < M ∧ ∀ (b : ℕ) (t : ℝ),
      (markMeasure (boolMeasure ((1 - p) ^ (m - 1)))).real
        {ω | t < (if b = 0 then 1 else hof p ω (b - 1))} ≤ M * Real.exp (-a * t) := by
  let v : ℝ := (1 - p) ^ (m - 1)
  have hv₀ : 0 < v := pow_pos (by linarith) _
  have hv₁ : v ≤ 1 := (pow_one_sub_le_half hp₀ hp₁ hm).trans (by norm_num)
  let _ : IsProbabilityMeasure (boolMeasure v) := isProbabilityMeasure_boolMeasure hv₀.le hv₁
  let μ := markMeasure (boolMeasure v)
  obtain ⟨a, ha, M, hM, hmom⟩ := exists_exp_moment_hof hp₀ hp₁ hm
  refine ⟨a, max M (Real.exp a), ha, hM.trans_le (le_max_left _ _), fun b t => ?_⟩
  let Z (ω : ℕ → Bool) : ℝ := if b = 0 then 1 else hof p ω (b - 1)
  change μ.real {ω | t < Z ω} ≤ _
  have hp : p ≠ 0 := by linarith
  have hZ : Measurable Z := by
    by_cases h : b = 0
    · simpa only [Z, if_pos h] using (measurable_const : Measurable (fun _ : ℕ → Bool => (1 : ℝ)))
    · simpa only [Z, if_neg h] using measurable_hof hp (b - 1)
  apply measureReal_lt_le_exp_moment hZ ha (hM.le.trans (le_max_left _ _))
  by_cases h : b = 0
  · simp only [Z, if_pos h, mul_one, lintegral_const, measure_univ, mul_one]
    exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
  · simp only [Z, if_neg h]
    exact (hmom (b - 1)).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))

/-- A spatial sum of powers of the marked-site potential has a stretched
exponential upper tail. The exponent is `1 / (q + 1)`, including the powers
`q = 1, 2` used in the record estimates. -/
theorem markMeasure_sum_hof_pow_tail {p : ℝ} {m : ℕ} (hp₀ : (1 : ℝ) / 2 < p)
    (hp₁ : p < 1) (hm : 2 ≤ m) (q : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (b L : ℕ) (u : ℝ), 0 < u →
      (markMeasure (boolMeasure ((1 - p) ^ (m - 1)))).real
        {ω | C * L + u < ∑ x ∈ Ico b (b + L), hof p ω x ^ q} ≤
          C * ((L : ℝ) + 1) * Real.exp (-c * u ^ (1 / (q + 1 : ℝ))) := by
  let v : ℝ := (1 - p) ^ (m - 1)
  have hv₀ : 0 < v := pow_pos (by linarith) _
  have hv₁ : v < 1 := (pow_one_sub_le_half hp₀ hp₁ hm).trans_lt (by norm_num)
  let _ : IsProbabilityMeasure (boolMeasure v) := isProbabilityMeasure_boolMeasure hv₀.le hv₁.le
  let μ := markMeasure (boolMeasure v)
  obtain ⟨a, M, ha, hM, hinit⟩ := markMeasure_hof_initial_tail hp₀ hp₁ hm
  obtain ⟨D, hD, hdet⟩ := sum_hof_pow_le_of_mem_markedGapEvent hp₀ hp₁ q
  obtain ⟨ν, hν, hsingle, d, K, H, hd, hK, hH, hgap⟩ :=
    exists_geometric_gap_sum_pow_tail v hv₀ hv₁ q
  let k : ℝ := 1 / (q + 1 : ℝ)
  let c := min a d * (2 * D)⁻¹ ^ k
  let C := max (D * K) (M + H)
  have h2D : 0 < 2 * D := by positivity
  have hc : 0 < c := mul_pos (lt_min ha hd) (Real.rpow_pos_of_pos (inv_pos.mpr h2D) _)
  have hC : 0 < C := (add_pos hM hH).trans_le (le_max_right _ _)
  refine ⟨c, C, hc, hC, fun b L u hu => ?_⟩
  let t := (u / (2 * D)) ^ k
  have ht : 0 < t := Real.rpow_pos_of_pos (div_pos hu h2D) _
  have htpu : t ^ (q + 1) = u / (2 * D) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hu.le h2D.le)]
    have he : k * ((q + 1 : ℕ) : ℝ) = 1 := by
      dsimp only [k]
      push_cast
      field_simp
    rw [he, Real.rpow_one]
  let V (ω : ℕ → Bool) : ℝ := if b = 0 then 1 else hof p ω (b - 1)
  let A : Set (Fin L → ℕ) := {g | K * L + t ^ (q + 1) < ∑ j, ((g j : ℝ) + 1) ^ (q + 1)}
  let E : Set (ℕ → Bool) := ⋃ g : A, markedGapEvent b g.1
  let G : Set (ℕ → Bool) := ⋃ g : (Set.univ : Set (Fin L → ℕ)), markedGapEvent b g.1
  have hG : ∀ᵐ ω ∂μ, ω ∈ G := by
    have he : μ G = 1 := (measure_union_markedGapEvent hv₀.le hv₁.le hsingle b L univ).trans measure_univ
    have hGm : MeasurableSet G := MeasurableSet.iUnion
      (fun g : (Set.univ : Set (Fin L → ℕ)) => measurableSet_markedGapEvent b g.1)
    exact (mem_ae_iff_prob_eq_one (μ := μ) hGm).mpr he
  have hE : μ.real E ≤ H * ((L : ℝ) + 1) * Real.exp (-d * t) := by
    rw [Measure.real_def]
    have he := measure_union_markedGapEvent hv₀.le hv₁.le hsingle b L A
    change μ E = _ at he
    rw [he]
    exact hgap L t ht
  let S : Set (ℕ → Bool) := {ω | C * L + u < ∑ x ∈ Ico b (b + L), hof p ω x ^ q}
  have hcover : ∀ᵐ ω ∂μ, ω ∈ S → ω ∈ {ω | t < V ω} ∪ E := by
    filter_upwards [hG] with ω hω hS
    obtain ⟨g, hg⟩ := mem_iUnion.mp hω
    by_cases hV : t < V ω
    · exact Or.inl hV
    by_cases hA : g.1 ∈ A
    · exact Or.inr (mem_iUnion.mpr ⟨⟨g.1, hA⟩, hg⟩)
    have hnonneg : 0 ≤ V ω := by
      by_cases he : b = 0
      · simp [V, he]
      · simpa only [V, if_neg he] using (zero_le_one.trans (one_le_hof hp₀.le hp₁ ω (b - 1)))
    have hleft : V ω ^ (q + 1) ≤ t ^ (q + 1) := pow_le_pow_left₀ hnonneg (le_of_not_gt hV) _
    have hright : (∑ j : Fin L, ((g.1 j : ℝ) + 1) ^ (q + 1)) ≤ K * L + t ^ (q + 1) :=
      le_of_not_gt hA
    have hbound := (hdet b L g.1 ω hg).trans (mul_le_mul_of_nonneg_left (add_le_add hleft hright) hD.le)
    have hDC : D * K ≤ C := le_max_left _ _
    have hDC' := mul_le_mul_of_nonneg_right hDC (Nat.cast_nonneg (α := ℝ) L)
    have hu' : D * (t ^ (q + 1) + (K * L + t ^ (q + 1))) = D * K * L + u := by
      rw [htpu]
      field_simp
      ring
    change C * (L : ℝ) + u < _ at hS
    rw [hu'] at hbound
    exact ((not_lt_of_ge (hbound.trans (add_le_add_left hDC' u))) hS).elim
  have hb : μ.real S ≤ M * Real.exp (-a * t) + H * ((L : ℝ) + 1) * Real.exp (-d * t) :=
    (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hcover)).trans
      ((measureReal_union_le _ _).trans (add_le_add (hinit b t) hE))
  have hta : t = u ^ k * (2 * D)⁻¹ ^ k := by
    dsimp only [t]
    rw [div_eq_mul_inv, Real.mul_rpow hu.le (inv_nonneg.mpr h2D.le)]
  have hct : c * u ^ k = min a d * t := by rw [hta]; dsimp only [c]; ring
  have h₁ : -a * t ≤ -c * u ^ k := by
    rw [neg_mul, neg_mul, hct]
    exact neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left a d) ht.le)
  have h₂ : -d * t ≤ -c * u ^ k := by
    rw [neg_mul, neg_mul, hct]
    exact neg_le_neg (mul_le_mul_of_nonneg_right (min_le_right a d) ht.le)
  refine hb.trans ?_
  have hL : 1 ≤ (L : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) L]
  calc
    _ ≤ M * Real.exp (-c * u ^ k) + H * ((L : ℝ) + 1) * Real.exp (-c * u ^ k) :=
      add_le_add (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h₁) hM.le)
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h₂) (by positivity))
    _ = (M + H * ((L : ℝ) + 1)) * Real.exp (-c * u ^ k) := by ring
    _ ≤ C * ((L : ℝ) + 1) * Real.exp (-c * u ^ k) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      have hMC : M + H ≤ C := le_max_right _ _
      have hM' := mul_le_mul_of_nonneg_right hL hM.le
      have hC' := mul_le_mul_of_nonneg_right hMC (show 0 ≤ (L : ℝ) + 1 by positivity)
      nlinarith

/-- The spatial estimate for each walker's actual row of site marks. -/
theorem arrayMeasure_sum_hof_pow_tail {p : ℝ} {m : ℕ} (hp₀ : (1 : ℝ) / 2 < p)
    (hp₁ : p < 1) (hm : 2 ≤ m) (q : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (N : ℕ) (i : Fin N) (b L : ℕ) (u : ℝ), 0 < u →
      (arrayMeasure N).real {U | C * L + u <
        ∑ x ∈ Ico b (b + L), hof p (SwarmLogRatio.siteMarks p m U i) x ^ q} ≤
          C * ((L : ℝ) + 1) * Real.exp (-c * u ^ (1 / (q + 1 : ℝ))) := by
  obtain ⟨c, C, hc, hC, h⟩ := markMeasure_sum_hof_pow_tail hp₀ hp₁ hm q
  refine ⟨c, C, hc, hC, fun N i b L u hu => ?_⟩
  let A : Set (ℕ → Bool) := {ω | C * L + u < ∑ x ∈ Ico b (b + L), hof p ω x ^ q}
  have hp : p ≠ 0 := by linarith
  have hA : MeasurableSet A := (Finset.measurable_sum _ (fun x _ =>
    (measurable_hof hp x).pow_const q)) measurableSet_Ioi
  have hmap := SwarmLogRatio.measurePreserving_siteMarks (show 0 < p by linarith) hp₁ m i
  change ((arrayMeasure N) ((fun U => SwarmLogRatio.siteMarks p m U i) ⁻¹' A)).toReal ≤ _
  rw [← Measure.map_apply hmap.measurable hA, hmap.map_eq]
  exact h b L u hu

/-- The spatial estimates hold simultaneously for every walker, site, and
subinterval of a deterministic interval of length at most `T * L + 1`.
The coefficient of the subinterval length depends only on `m, p`. -/
theorem arrayMeasure_local_hof_estimates {p : ℝ} {m : ℕ} (hp₀ : (1 : ℝ) / 2 < p)
    (hp₁ : p < 1) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N T : ℕ) {ε : ℝ}, 0 < ε →
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ L : ℕ in atTop, ∀ b : ℕ,
        (arrayMeasure N).real {U |
          (∃ (i : Fin N) (j : ℕ), j ≤ T * L ∧ (L : ℝ) ^ (1 / 3 : ℝ) <
            hof p (SwarmLogRatio.siteMarks p m U i) (b + j)) ∨
          (∃ (i : Fin N) (j n : ℕ), j ≤ T * L ∧ n ≤ T * L + 1 ∧
            C * n + ε * L < ∑ x ∈ Finset.Ico (b + j) (b + j + n),
              hof p (SwarmLogRatio.siteMarks p m U i) x ^ 2)}
          ≤ Real.exp (-c * (L : ℝ) ^ (1 / 3 : ℝ)) := by
  obtain ⟨d, C, hd, hC, hsum⟩ := arrayMeasure_sum_hof_pow_tail hp₀ hp₁ hm 2
  obtain ⟨a, M, ha, hM, hsite⟩ := markMeasure_hof_initial_tail hp₀ hp₁ hm
  refine ⟨C, hC, fun N T ε hε => ?_⟩
  let R (L : ℕ) := (L : ℝ) ^ (1 / 3 : ℝ)
  let k := min a (d * ε ^ (1 / 3 : ℝ))
  have hk : 0 < k := lt_min ha (mul_pos hd (Real.rpow_pos_of_pos hε _))
  let c := k / 2
  let P : ℝ := (N : ℝ) * ((T : ℝ) + 2) ^ 3 * (M + C)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hTop : Tendsto R atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp tendsto_natCast_atTop_atTop
  have hsmall := ((isLittleO_exp_mul_rpow_of_lt 9 (show -k < -c by dsimp [c]; linarith)).const_mul_left P).bound
    (show (0 : ℝ) < 1 by norm_num)
  refine ⟨c, half_pos hk, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ), hTop.eventually hsmall] with L hL hpoly
  intro b
  let μ := arrayMeasure N
  let f (i : Fin N) (j : ℕ) (U : Array N) := hof p (SwarmLogRatio.siteMarks p m U i) (b + j)
  let s := range (T * L + 1)
  let t := range (T * L + 2)
  let A (i : Fin N) (j : ℕ) : Set (Array N) := {U | R L < f i j U}
  let B (i : Fin N) (j n : ℕ) : Set (Array N) := {U |
    C * n + ε * L < ∑ x ∈ Finset.Ico (b + j) (b + j + n),
      hof p (SwarmLogRatio.siteMarks p m U i) x ^ 2}
  have hA (i : Fin N) (j : ℕ) : μ.real (A i j) ≤ M * Real.exp (-k * R L) := by
    let E : Set (ℕ → Bool) := {ω | R L < hof p ω (b + j)}
    have hp : 0 < p := by linarith
    have he : MeasurableSet E := (measurable_hof hp.ne' (b + j)) measurableSet_Ioi
    have h := SwarmLogRatio.measurePreserving_siteMarks hp hp₁ m i
    change (μ ((fun U => SwarmLogRatio.siteMarks p m U i) ⁻¹' E)).toReal ≤ _
    rw [← Measure.map_apply h.measurable he, h.map_eq]
    have h₁ := hsite (b + j + 1) (R L)
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false, Nat.add_sub_cancel] at h₁
    apply h₁.trans
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left _ _)) (Real.rpow_nonneg (Nat.cast_nonneg _) _))) hM.le
  have hB (i : Fin N) (j n : ℕ) (hn : n ∈ t) :
      μ.real (B i j n) ≤ C * ((T * L : ℕ) + 2 : ℝ) * Real.exp (-k * R L) := by
    have hLp : (0 : ℝ) < L := by exact_mod_cast (zero_lt_one.trans_le hL)
    have h := hsum N i (b + j) n (ε * L) (mul_pos hε hLp)
    have hexp : Real.exp (-d * (ε * (L : ℝ)) ^ (1 / ((2 : ℕ) + 1 : ℝ))) ≤ Real.exp (-k * R L) := by
      norm_num
      rw [Real.mul_rpow hε.le hLp.le]
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (show k ≤ d * ε ^ (1 / 3 : ℝ) from min_le_right _ _)
        (Real.rpow_nonneg hLp.le _)
    have hn' : (n : ℝ) + 1 ≤ ((T * L : ℕ) + 2 : ℝ) := by
      exact_mod_cast (show n + 1 ≤ T * L + 2 from mem_range.mp hn)
    exact h.trans (mul_le_mul (mul_le_mul_of_nonneg_left hn' hC.le) hexp
      (Real.exp_pos _).le (by positivity))
  let E := Real.exp (-k * R L)
  let G := ⋃ i ∈ (univ : Finset (Fin N)), ⋃ j ∈ s, A i j
  let H := ⋃ i ∈ (univ : Finset (Fin N)), ⋃ j ∈ s, ⋃ n ∈ t, B i j n
  have hG : μ.real G ≤ (N : ℝ) * (s.card : ℝ) * (M * E) := by
    refine (measureReal_biUnion_finset_le univ (fun i => ⋃ j ∈ s, A i j)).trans ?_
    have h := sum_le_sum (s := (univ : Finset (Fin N))) fun i _ =>
      (measureReal_biUnion_finset_le s (A i)).trans
        (sum_le_sum (g := fun _ => M * E) (fun j _ => hA i j))
    simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc] using h
  have hH : μ.real H ≤ (N : ℝ) * (s.card : ℝ) * (t.card : ℝ) * (C * ((T * L : ℕ) + 2 : ℝ) * E) := by
    refine (measureReal_biUnion_finset_le univ (fun i => ⋃ j ∈ s, ⋃ n ∈ t, B i j n)).trans ?_
    have h := sum_le_sum (s := (univ : Finset (Fin N))) fun i _ =>
      (measureReal_biUnion_finset_le s (fun j => ⋃ n ∈ t, B i j n)).trans
        (sum_le_sum fun j _ => (measureReal_biUnion_finset_le t (B i j)).trans
          (sum_le_sum (g := fun _ => C * ((T * L : ℕ) + 2 : ℝ) * E) (hB i j)))
    simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc] using h
  have hset : {U : Array N | (∃ i j, j ≤ T * L ∧ R L < f i j U) ∨
      (∃ (i : Fin N) (j n : ℕ), j ≤ T * L ∧ n ≤ T * L + 1 ∧ U ∈ B i j n)} = G ∪ H := by
    ext U
    simp only [G, H, s, t, Set.mem_union, mem_ofPred_eq, mem_iUnion, Finset.mem_range,
      Finset.mem_univ, true_and, Nat.lt_succ_iff, exists_prop]
    constructor
    · rintro (h | ⟨i, j, n, hj, hn, hB⟩)
      · exact Or.inl h
      · exact Or.inr ⟨i, j, hj, n, hn, hB⟩
    · rintro (h | ⟨i, j, hj, n, hn, hB⟩)
      · exact Or.inl h
      · exact Or.inr ⟨i, j, n, hj, hn, hB⟩
  change μ.real {U : Array N | (∃ (i : Fin N) (j : ℕ), j ≤ T * L ∧ R L < f i j U) ∨
    (∃ (i : Fin N) (j n : ℕ), j ≤ T * L ∧ n ≤ T * L + 1 ∧ U ∈ B i j n)} ≤ _
  rw [hset]
  refine (measureReal_union_le G H).trans ((add_le_add hG hH).trans ?_)
  let Q := ((T : ℝ) + 2) * L
  have hLr : 1 ≤ (L : ℝ) := by exact_mod_cast hL
  have hQ : 1 ≤ Q := by dsimp [Q]; nlinarith [Nat.cast_nonneg (α := ℝ) T, Nat.cast_nonneg (α := ℝ) L]
  have hwidth : ((T * L : ℕ) + 2 : ℝ) ≤ Q := by
    push_cast
    dsimp [Q]
    linarith [hLr]
  have hs : ((s.card : ℕ) : ℝ) ≤ Q := by
    simp only [s, card_range]
    push_cast at hwidth ⊢
    linarith
  have ht : ((t.card : ℕ) : ℝ) ≤ Q := by simpa [t] using hwidth
  have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have he : 0 ≤ E := (Real.exp_pos _).le
  have hqpow : Q ≤ Q ^ (3 : ℕ) := by
    simpa only [pow_one] using (pow_le_pow_right₀ hQ (by norm_num : (1 : ℕ) ≤ 3))
  have h₁ : (N : ℝ) * (s.card : ℝ) * (M * E) ≤ (N : ℝ) * Q ^ (3 : ℕ) * (M * E) := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hs.trans hqpow) hn)
      (mul_nonneg hM.le he)
  have h₂ : (N : ℝ) * (s.card : ℝ) * (t.card : ℝ) * (C * ((T * L : ℕ) + 2 : ℝ) * E) ≤
      (N : ℝ) * Q ^ (3 : ℕ) * (C * E) := by
    calc
      _ ≤ (N : ℝ) * Q * Q * (C * Q * E) := by gcongr
      _ = _ := by ring
  have hR : R L ^ (9 : ℝ) = (L : ℝ) ^ (3 : ℕ) := by
    dsimp only [R]
    rw [← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  refine (add_le_add h₁ h₂).trans ?_
  calc
    _ = P * (Real.exp (-k * R L) * R L ^ (9 : ℝ)) := by rw [hR]; dsimp only [P, Q, E]; ring
    _ ≤ _ := by
      change ‖P * (Real.exp (-k * R L) * R L ^ (9 : ℝ))‖ ≤
        1 * ‖Real.exp (-c * R L)‖ at hpoly
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        abs_of_pos (Real.exp_pos _), one_mul] at hpoly
      exact hpoly

end Swarming.Diameter
