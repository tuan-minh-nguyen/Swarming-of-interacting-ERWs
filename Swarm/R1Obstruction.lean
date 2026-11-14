/-
  **`locsum` residual R1, obstruction: `hstarN` is *not* almost surely finite.**

  `B1Potential.hstarN p x ω = ⨆ k, ofReal (Q p k x ω)` is the supremum of the truncations of
  the stationary potential `h^*(x) = 1 + 2 Σ_{q≥1} Π_{u<q} rho(x-u)` on a **one-sided** mark
  row `ω : ℕ → Bool`.  On a one-sided row the product `Pz x j = Π_{u<j} rho(x-u)` uses the
  truncated subtraction `x - u`, so for `u ≥ x` every factor is `rho(0)`; consequently

  * `Pz p x j ω` is *constant* in `j` for `j ≥ x+1` as soon as site `0` is unmarked
    (`rat p ω 0 = 1`), and
  * hence `Q p k x ω ≥ 2 (k - x - 1) Pz p x (x+1) ω - 1 → ∞`, i.e. `hstarN p x ω = ⊤`.

  Site `0` is unmarked with probability `1 - q`, so

      markMeasure (boolMeasure q) {ω | hstarN p x ω = ⊤} ≥ 1 - q  (in `ℝ≥0∞`),

  which is strictly positive for `q < 1`.  Therefore the residual item
  "a.e. finiteness of `hstarN`" of `LOCSUM_ARRAY.md` (R1) is **false** with the definitions of
  `L1Trunc.lean`/`B1Potential.lean`; the correct full potential on a one-sided row is `hof`
  itself, and the exact comparison needed by `(locsum)` is `R1Identity.hof_sub_Q`.
-/
import Swarm.R1Identity
import Swarm.B1Potential

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Topology
open SwarmMarks

namespace LocSumR1

noncomputable section

lemma rat_pos {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (ω : ℕ → Bool) (n : ℕ) :
    0 < LocSum.rat p ω n := by
  unfold LocSum.rat
  split
  · exact div_pos (by linarith) (by linarith)
  · norm_num

lemma Pz_pos {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (x k : ℕ) (ω : ℕ → Bool) :
    0 < LocSum.Pz p x k ω :=
  Finset.prod_pos fun u _ => rat_pos hp1 hp2 ω (x - u)

/-- One-step factorisation of `Pz` as a product over `range (k+1)`. -/
lemma Pz_succ_right (p : ℝ) (x k : ℕ) (ω : ℕ → Bool) :
    LocSum.Pz p x (k + 1) ω = LocSum.Pz p x k ω * LocSum.rat p ω (x - k) := by
  unfold LocSum.Pz
  rw [Finset.prod_range_succ]

/-- If site `0` is unmarked, then `Pz p x j` is constant in `j` for `j ≥ x+1`. -/
theorem Pz_eq_of_le_unmarked {p : ℝ} {ω : ℕ → Bool} (h0 : ω 0 = false) (x : ℕ) :
    ∀ j : ℕ, x + 1 ≤ j → LocSum.Pz p x j ω = LocSum.Pz p x (x + 1) ω := by
  have hstep : ∀ k : ℕ, x + 1 ≤ k → LocSum.Pz p x (k + 1) ω = LocSum.Pz p x k ω := by
    intro k hk
    rw [Pz_succ_right, show x - k = 0 from by omega]
    unfold LocSum.rat
    rw [h0]
    norm_num
  have hconst : ∀ t : ℕ, LocSum.Pz p x (x + 1 + t) ω = LocSum.Pz p x (x + 1) ω := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
        rw [show x + 1 + (t + 1) = x + 1 + t + 1 from by ring,
          hstep (x + 1 + t) (by omega), ih]
  intro j hj
  obtain ⟨t, rfl⟩ : ∃ t, j = x + 1 + t := ⟨j - (x + 1), by omega⟩
  exact hconst t

/-- The truncations grow without bound once site `0` is unmarked. -/
theorem Q_ge_of_le_unmarked {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {ω : ℕ → Bool} (h0 : ω 0 = false) (x : ℕ) :
    ∀ k : ℕ, x + 1 ≤ k →
      2 * ((k - (x + 1) : ℕ) : ℝ) * LocSum.Pz p x (x + 1) ω - 1 ≤ LocSum.Q p k x ω := by
  intro k hk
  set c := LocSum.Pz p x (x + 1) ω with hc
  have hsub : (Finset.Ico (x + 1) k) ⊆ Finset.range k := by
    intro j hj
    simp only [Finset.mem_Ico] at hj
    exact Finset.mem_range.mpr hj.2
  have hnonneg : ∀ j ∈ Finset.range k, j ∉ Finset.Ico (x + 1) k → 0 ≤ LocSum.Pz p x j ω :=
    fun j _ _ => (Pz_pos hp1 hp2 x j ω).le
  have h1 : ∑ j ∈ Finset.Ico (x + 1) k, LocSum.Pz p x j ω ≤ LocSum.Gsum p k x ω := by
    unfold LocSum.Gsum
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
  have h2 : ∑ j ∈ Finset.Ico (x + 1) k, LocSum.Pz p x j ω
      = ((k - (x + 1) : ℕ) : ℝ) * c := by
    have hc' : ∀ j ∈ Finset.Ico (x + 1) k, LocSum.Pz p x j ω = c := fun j hj =>
      Pz_eq_of_le_unmarked h0 x j (Finset.mem_Ico.mp hj).1
    rw [Finset.sum_congr rfl hc', Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  unfold LocSum.Q
  rw [h2] at h1
  nlinarith [h1]

/-- **`hstarN` is infinite once site `0` is unmarked.** -/
theorem hstarN_eq_top_of_unmarked {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {ω : ℕ → Bool} (h0 : ω 0 = false) (x : ℕ) :
    LocSumAct.hstarN p x ω = ⊤ := by
  have hc : 0 < LocSum.Pz p x (x + 1) ω := Pz_pos hp1 hp2 x (x + 1) ω
  have key : ∀ n : ℕ, (n : ℝ≥0∞) ≤ ⨆ k, ENNReal.ofReal (LocSum.Q p k x ω) := by
    intro n
    obtain ⟨t, ht⟩ := exists_nat_gt (((n : ℝ) + 1) / (2 * LocSum.Pz p x (x + 1) ω))
    have h2c : 0 < 2 * LocSum.Pz p x (x + 1) ω := by linarith
    rw [div_lt_iff₀ h2c] at ht
    have hlt : (n : ℝ) < 2 * ((t : ℕ) : ℝ) * LocSum.Pz p x (x + 1) ω := by nlinarith
    have hQ := Q_ge_of_le_unmarked hp1 hp2 h0 x (x + 1 + t) (by omega)
    have hsub : x + 1 + t - (x + 1) = t := by omega
    rw [hsub] at hQ
    have hle : (n : ℝ) ≤ LocSum.Q p (x + 1 + t) x ω := by linarith
    calc (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) := (ENNReal.ofReal_natCast n).symm
      _ ≤ ENNReal.ofReal (LocSum.Q p (x + 1 + t) x ω) := ENNReal.ofReal_le_ofReal hle
      _ ≤ ⨆ k, ENNReal.ofReal (LocSum.Q p k x ω) :=
          le_iSup (fun k => ENNReal.ofReal (LocSum.Q p k x ω)) (x + 1 + t)
  unfold LocSumAct.hstarN
  refine le_antisymm le_top ?_
  rw [← ENNReal.iSup_natCast]
  exact iSup_le key

/-- **The probability of `hstarN = ⊤` is at least the probability that site `0` is unmarked.** -/
theorem markMeasure_hstarN_eq_top_ge {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (x : ℕ) :
    ENNReal.ofReal (1 - q)
      ≤ markMeasure (boolMeasure q) {ω : ℕ → Bool | LocSumAct.hstarN p x ω = ⊤} := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure hq0 hq1
  have hsub : {ω : ℕ → Bool | ω 0 = false}
      ⊆ {ω : ℕ → Bool | LocSumAct.hstarN p x ω = ⊤} := fun ω hω =>
    hstarN_eq_top_of_unmarked hp1 hp2 hω x
  calc ENNReal.ofReal (1 - q)
      = markMeasure (boolMeasure q) {ω : ℕ → Bool | ω 0 = false} := by
        rw [markMeasure_false (μB := boolMeasure q) hq0 hq1 (boolMeasure_true q) 0]
    _ ≤ markMeasure (boolMeasure q) {ω : ℕ → Bool | LocSumAct.hstarN p x ω = ⊤} :=
        measure_mono hsub

/-- **`hstarN` is not almost surely finite**: the residual item "a.e. finiteness" of
`LOCSUM_ARRAY.md` is false for `q < 1`. -/
theorem not_ae_ne_top_hstarN {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (x : ℕ) :
    ¬ (∀ᵐ ω ∂(markMeasure (boolMeasure q)), LocSumAct.hstarN p x ω ≠ ⊤) := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure hq0 hq1.le
  intro hae
  have hzero : markMeasure (boolMeasure q) {ω : ℕ → Bool | LocSumAct.hstarN p x ω = ⊤} = 0 := by
    have h := ae_iff.mp hae
    rwa [show {ω : ℕ → Bool | ¬ LocSumAct.hstarN p x ω ≠ ⊤}
          = {ω : ℕ → Bool | LocSumAct.hstarN p x ω = ⊤} from by ext ω; simp] at h
  have hge := markMeasure_hstarN_eq_top_ge hp1 hp2 hq0 hq1.le x
  rw [hzero] at hge
  have hpos : 0 < 1 - q := by linarith
  have hne : ENNReal.ofReal (1 - q) ≠ 0 := (ENNReal.ofReal_pos.mpr hpos).ne'
  exact hne (le_antisymm hge bot_le)

end

end LocSumR1
