import Swarm.A2Window
import Swarm.L4Indep
import Swarm.R2LocMax

open Finset Filter MeasureTheory ProbabilityTheory Set
open SwarmMarks LocSum LocSumAct
open scoped NNReal Topology

namespace Swarming.Diameter

set_option autoImplicit false

/-- Evaluate a function of the marks at `x, x-1, …, x-k+1`. -/
def markBlockValue {k : ℕ} (f : (Fin k → Bool) → ℝ) (x : ℕ) (ω : ℕ → Bool) : ℝ :=
  f (fun u => ω (x - (u : ℕ)))

theorem measurable_markBlockValue {k : ℕ} (f : (Fin k → Bool) → ℝ) (x : ℕ) :
    Measurable (markBlockValue f x) :=
  (measurable_of_finite f).comp (measurable_pi_lambda _ (fun _ => measurable_pi_apply _))

private theorem iIndepFun_markBlockValue {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    {k a n : ℕ} (hk : 1 ≤ k) (ha : k ≤ a) (f : (Fin k → Bool) → ℝ) :
    iIndepFun (fun j : Fin n => markBlockValue f (a + (j : ℕ) * k))
      (markMeasure (boolMeasure q)) := by
  let _ : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure hq₀ hq₁
  let g (j : Fin n) (ω : ℕ → Bool) (u : Fin k) := ω (bidx a k j.1 u.1)
  have hg : iIndepFun g (markMeasure (boolMeasure q)) := by
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map]
    · change _ = Measure.infinitePi (fun j : Fin n => (markMeasure (boolMeasure q)).map (g j))
      rw [show (markMeasure (boolMeasure q)).map (fun ω j => g j ω) = _ from
        map_block_family hq₀ hq₁ hk ha]
      congr 1
      funext j
      exact (map_block (j := j.1) hq₀ hq₁ ha).symm
    · intro j
      have hmeas : Measurable (g j) :=
        measurable_pi_iff.mpr (fun (u : Fin k) => measurable_pi_apply (bidx a k j.1 u.1))
      exact hmeas
  exact hg.comp (fun _ => f) (fun _ => measurable_of_finite f)

private theorem measureReal_markBlock_sum_ge {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    {k a n : ℕ} (hk : 1 ≤ k) (ha : k ≤ a) {B : ℝ≥0} (f : (Fin k → Bool) → ℝ)
    (hf : ∀ v, f v ∈ Set.Icc 0 (B : ℝ)) {C δ : ℝ} (hδ : 0 ≤ δ)
    (hmean : ∀ x : ℕ, k ≤ x → ∫ ω, markBlockValue f x ω ∂markMeasure (boolMeasure q) ≤ C) :
    (markMeasure (boolMeasure q)).real {ω |
        C * ((n * k : ℕ) : ℝ) + δ ≤ ∑ x ∈ Finset.Ico a (a + n * k), markBlockValue f x ω}
      ≤ (k : ℝ) * Real.exp (-(δ / (k : ℝ)) ^ 2 / (2 * (n : ℝ) * ((B : ℝ) / 2) ^ 2)) := by
  let _ : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure hq₀ hq₁
  let P := markMeasure (boolMeasure q)
  let c : ℝ≥0 := (B / 2) ^ 2
  let v (r : Fin k) (j : Fin n) := markBlockValue f (a + (r : ℕ) + (j : ℕ) * k)
  let E (r : Fin k) : Set (ℕ → Bool) :=
    {ω | δ / (k : ℝ) ≤ ∑ j, (v r j ω - ∫ ω', v r j ω' ∂P)}
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hsub : {ω | C * ((n * k : ℕ) : ℝ) + δ ≤
      ∑ x ∈ Finset.Ico a (a + n * k), markBlockValue f x ω} ⊆ ⋃ r, E r := by
    intro ω hω
    by_contra hnone
    have hsum (r : Fin k) : (∑ j, v r j ω) < C * (n : ℝ) + δ / (k : ℝ) := by
      have hn : ω ∉ E r := fun h => hnone (Set.mem_iUnion.mpr ⟨r, h⟩)
      have h : (∑ j, (v r j ω - ∫ ω', v r j ω' ∂P)) < δ / (k : ℝ) := not_le.mp hn
      have hμ : (∑ j, ∫ ω', v r j ω' ∂P) ≤ C * (n : ℝ) := calc
        _ ≤ ∑ _j : Fin n, C := Finset.sum_le_sum fun j _ =>
          hmean (a + (r : ℕ) + (j : ℕ) * k) (by omega)
        _ = _ := by simp [mul_comm]
      rw [Finset.sum_sub_distrib] at h
      linarith only [h, hμ]
    have hlt : (∑ r, ∑ j, v r j ω) < ∑ _r : Fin k, (C * (n : ℝ) + δ / (k : ℝ)) :=
      Finset.sum_lt_sum (fun r _ => (hsum r).le) ⟨⟨0, hk⟩, Finset.mem_univ _, hsum ⟨0, hk⟩⟩
    have heq : (∑ _r : Fin k, (C * (n : ℝ) + δ / (k : ℝ))) = C * ((n * k : ℕ) : ℝ) + δ := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin, Nat.cast_mul]
      rw [mul_add, mul_div_cancel₀ _ hkr.ne']
      ring
    rw [heq] at hlt
    change (∑ (r : Fin k), ∑ (j : Fin n), markBlockValue f (a + r.1 + j.1 * k) ω) < _ at hlt
    rw [sum_fin_residue (fun x => markBlockValue f x ω) a k n] at hlt
    exact (not_lt_of_ge hω) hlt
  have hE (r : Fin k) : P.real (E r) ≤
      Real.exp (-(δ / (k : ℝ)) ^ 2 / (2 * (n : ℝ) * ((B : ℝ) / 2) ^ 2)) := by
    have hind : iIndepFun (fun j : Fin n => v r j) P :=
      iIndepFun_markBlockValue hq₀ hq₁ hk (a := a + r.1) (by omega) f
    have hcenter := hind.comp (fun j y => y - ∫ ω, v r j ω ∂P) (fun _ => measurable_id.sub_const _)
    have hmgf (j : Fin n) : HasSubgaussianMGF (fun ω => v r j ω - ∫ ω', v r j ω' ∂P) c P := by
      have h := hasSubgaussianMGF_of_mem_Icc (μ := P)
        (measurable_markBlockValue f (a + r.1 + j.1 * k)).aemeasurable
        (Filter.Eventually.of_forall (fun ω : ℕ → Bool => hf (fun u => ω (a + r.1 + j.1 * k - u.1))))
      simpa [c] using h
    have hd := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hcenter
      (s := Finset.univ) (c := fun _ => c) (fun j _ => hmgf j) (div_nonneg hδ hkr.le)
    have hc : (2 * (((∑ _j : Fin n, c) : ℝ≥0) : ℝ)) = 2 * (n : ℝ) * ((B : ℝ) / 2) ^ 2 := by
      rw [NNReal.coe_sum]
      simp [Finset.sum_const, nsmul_eq_mul, c, mul_assoc]
    change P.real (E r) ≤ Real.exp (-(δ / (k : ℝ)) ^ 2 / (2 * (((∑ _j : Fin n, c) : ℝ≥0) : ℝ))) at hd
    rwa [hc] at hd
  refine ((measureReal_mono hsub).trans (measureReal_iUnion_fintype_le E)).trans ?_
  simpa only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin] using
    (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k))) fun r _ => hE r)

/-- A bounded function of a fixed number of consecutive independent marks
has exponential upper concentration on all subintervals of length and offset
bounded by `T * L`. -/
theorem measureReal_markBlock_intervals_gt {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    {k : ℕ} (hk : 1 ≤ k) {B : ℝ≥0} (hB : 0 < B) (f : (Fin k → Bool) → ℝ)
    (hf : ∀ v, f v ∈ Set.Icc 0 (B : ℝ)) {C : ℝ} (hC : 0 ≤ C)
    (hmean : ∀ x : ℕ, k ≤ x → ∫ ω, markBlockValue f x ω ∂markMeasure (boolMeasure q) ≤ C)
    (T : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ L : ℕ in atTop, ∀ a : ℕ, k ≤ a →
      (markMeasure (boolMeasure q)).real {ω | ∃ j ≤ T * L, ∃ n ≤ T * L,
        C * (n : ℝ) + ε * (L : ℝ) <
          ∑ x ∈ Finset.Ico (a + j) (a + j + n), markBlockValue f x ω}
        ≤ Real.exp (-c * (L : ℝ)) := by
  let _ : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure hq₀ hq₁
  let P := markMeasure (boolMeasure q)
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  let d := ε ^ 2 / (8 * (k : ℝ) ^ 2 * ((T : ℝ) + 1) * ((B : ℝ) / 2) ^ 2)
  have hd : 0 < d := by dsimp only [d]; positivity
  have htop : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hpoly := LocSumR1.eventually_poly_mul_exp_le (C := (k : ℝ) * ((T : ℝ) + 1) ^ 2)
    (by positivity) hd 2
  refine ⟨d / 2, half_pos hd, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ), htop.eventually_ge_atTop (2 * C * k / ε),
    htop.eventually hpoly] with L hL hbig hrate
  intro a ha
  let J := Fin (T * L + 1)
  let E (j n : ℕ) : Set (ℕ → Bool) := {ω |
    C * (n : ℝ) + ε * (L : ℝ) <
      ∑ x ∈ Finset.Ico (a + j) (a + j + n), markBlockValue f x ω}
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL₀ : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hLr
  have hEk (j n : J) : P.real (E j n) ≤ (k : ℝ) * Real.exp (-d * (L : ℝ)) := by
    let v := (n : ℕ) / k + 1
    have hvk : (n : ℕ) ≤ v * k ∧ v * k ≤ n + k := by
      have heq := Nat.mod_add_div n.1 k
      have hmod := Nat.mod_lt n.1 hk
      dsimp only [v]
      rw [Nat.add_mul, one_mul, Nat.mul_comm (n.1 / k)]
      omega
    have hv : v ≤ (T + 1) * L := by
      have h := Nat.div_le_self n.1 k
      have hn : n.1 ≤ T * L := Nat.le_of_lt_succ n.isLt
      dsimp only [v]
      rw [Nat.add_mul, one_mul]
      omega
    have hsub : E j n ⊆ {ω | C * ((v * k : ℕ) : ℝ) + ε * (L : ℝ) / 2 ≤
        ∑ x ∈ Finset.Ico (a + j.1) (a + j.1 + v * k), markBlockValue f x ω} := by
      intro ω hω
      have hs := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Ico_subset_Ico_right (a := a + j.1) (Nat.add_le_add_left hvk.1 (a + j.1)))
        (f := fun x => markBlockValue f x ω) (fun x _ _ => (hf (fun u => ω (x - u.1))).1)
      have hlen : ((v * k : ℕ) : ℝ) ≤ (n.1 : ℝ) + (k : ℝ) := by exact_mod_cast hvk.2
      have hsmall := (div_le_iff₀ hε).mp hbig
      change C * (n.1 : ℝ) + ε * (L : ℝ) < _ at hω
      change C * ((v * k : ℕ) : ℝ) + ε * (L : ℝ) / 2 ≤
        ∑ x ∈ Finset.Ico (a + j.1) (a + j.1 + v * k), markBlockValue f x ω
      linarith only [hs, hω, hsmall, mul_le_mul_of_nonneg_left hlen hC]
    refine (measureReal_mono hsub).trans
      ((measureReal_markBlock_sum_ge hq₀ hq₁ hk (ha.trans (Nat.le_add_right _ _)) f hf
        (by positivity : 0 ≤ ε * (L : ℝ) / 2) hmean).trans ?_)
    apply mul_le_mul_of_nonneg_left _ hkr.le
    apply Real.exp_le_exp.mpr
    have hv₀ : (0 : ℝ) < v := by exact_mod_cast Nat.succ_pos (n.1 / k)
    have hv' : (v : ℝ) ≤ ((T : ℝ) + 1) * L := by exact_mod_cast hv
    have hden : (0 : ℝ) < 2 * (v : ℝ) * ((B : ℝ) / 2) ^ 2 := by positivity
    rw [neg_div, neg_mul, neg_le_neg_iff, le_div_iff₀ hden]
    calc
      _ ≤ d * (L : ℝ) * (2 * (((T : ℝ) + 1) * L) * ((B : ℝ) / 2) ^ 2) := by gcongr
      _ = _ := by dsimp only [d]; field_simp; ring
  have hsub : {ω | ∃ j ≤ T * L, ∃ n ≤ T * L, C * (n : ℝ) + ε * (L : ℝ) <
      ∑ x ∈ Finset.Ico (a + j) (a + j + n), markBlockValue f x ω} ⊆
      ⋃ j : J, ⋃ n : J, E j n := by
    rintro ω ⟨j, hj, n, hn, h⟩
    exact Set.mem_iUnion.mpr ⟨⟨j, Nat.lt_succ_of_le hj⟩,
      Set.mem_iUnion.mpr ⟨⟨n, Nat.lt_succ_of_le hn⟩, h⟩⟩
  have hmass : P.real (⋃ j : J, ⋃ n : J, E j n) ≤
      ((T * L + 1 : ℕ) : ℝ) ^ 2 * (k : ℝ) * Real.exp (-d * (L : ℝ)) := by
    refine (measureReal_iUnion_fintype_le _).trans ?_
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset J)) (fun j _ =>
      (measureReal_iUnion_fintype_le _).trans (Finset.sum_le_sum (fun n _ => hEk j n)))
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pow_two,
      mul_assoc, J] using hsum
  refine ((measureReal_mono hsub).trans hmass).trans ?_
  have hsize : ((T * L + 1 : ℕ) : ℝ) ≤ ((T : ℝ) + 1) * L := by push_cast; linarith
  calc
    _ ≤ (((T : ℝ) + 1) * L) ^ 2 * (k : ℝ) * Real.exp (-d * (L : ℝ)) := by gcongr
    _ = (k : ℝ) * ((T : ℝ) + 1) ^ 2 * (L : ℝ) ^ 2 * Real.exp (-d * (L : ℝ)) := by ring
    _ ≤ _ := hrate

end Swarming.Diameter
