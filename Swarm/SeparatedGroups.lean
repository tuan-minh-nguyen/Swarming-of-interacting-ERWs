/-
The separated-group part of §2.3 of `main_1d_revised.tex` (Proposition `group`), split
into the pieces that are *not* already in `Swarm/Swarming.lean`:

* `Wpos` (the paper's equation for `W_n^{I,J}`): under separation, the observable
  `W = average_{i∈I} H(X_i) - max_{j∈J} H(X_j)` dominates the actual gap
  `min_{i∈I} X_i - max_{j∈J} X_j ≥ 0`;
* `gap_div_tendsto_zero`: the deterministic squeeze that converts the supermartingale
  bound `W_n ≤ W_0 + Q_n` and the martingale strong law `Q_n = o(n)` into the paper's
  conclusion (diam), `(min_{i∈I} X_n^i - max_{j∈J} X_n^j)/n → 0`;
* `supermartingale_div_tendsto_zero`: a nonnegative supermartingale is `o(n)` a.e.,
  which is the case of (diam) where the conditional drift is nonpositive outright.

This module imports the campaign's `Swarm/Swarming.lean` (namespace `Cookie`, `Swarming`)
rather than restating its potential-theoretic core; see `verify.sh` for the exact
`LEAN_PATH` and build order.
-/
import Swarm.Swarming
import Swarm.MartingaleLimit

open Filter Topology MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SeparatedGroups

open Cookie

/-! ## Monotonicity of `Hfix` -/

/-- `Hfix w` is nondecreasing: each increment `hfix w n` is at least `1`. -/
theorem Hfix_monotone {w : ℕ → ℝ} (hw0 : ∀ n, 0 < w n) (hw1 : ∀ n, w n ≤ 1) :
    Monotone (Hfix w) := by
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b _ ih =>
      rw [Hfix_succ]
      have := one_le_hfix w hw0 hw1 b
      linarith

/-! ## Equation (Wpos) -/

/-- If `c` is a lower bound for `f` on `s`, then it is at most the average of `f`. -/
theorem le_average_of_le {s : Finset ι} (hs : s.Nonempty) {f : ι → ℝ} {c : ℝ}
    (h : ∀ i ∈ s, c ≤ f i) : c ≤ Swarming.Group.average s f := by
  have hcard : 0 < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hs
  have hsum : (s.card : ℝ) * c ≤ ∑ i ∈ s, f i := by
    have h' := Finset.card_nsmul_le_sum s f c h
    simpa [nsmul_eq_mul] using h'
  rw [Swarming.Group.average, le_div_iff₀ hcard]
  linarith

/-- For a monotone `H`, the maximum of `H ∘ x` is `H` of the maximum of `x`. -/
theorem maximumOn_comp {t : Finset ι} (ht : t.Nonempty) {H : ℕ → ℝ} (hH : Monotone H)
    (x : ι → ℕ) :
    Swarming.Group.maximumOn t ht (fun j => H (x j)) = H (t.sup' ht x) := by
  rw [Swarming.Group.maximumOn]
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le ht _ ?_
    intro j hj
    exact hH (Finset.le_sup' x hj)
  · obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup' ht x
    rw [hjeq]
    exact Finset.le_sup' (fun j => H (x j)) hj

/-- **Equation (Wpos)** of the paper: under separation of `I` (left) and `J` (right),
`W_n^{I,J} ≥ min_{i∈I} X_i - max_{j∈J} X_j ≥ 0`. -/
theorem Wpos {w : ℕ → ℝ} (hw0 : ∀ n, 0 < w n) (hw1 : ∀ n, w n ≤ 1)
    {s t : Finset ι} (hs : s.Nonempty) (ht : t.Nonempty) {x : ι → ℕ}
    (hsep : ∀ i ∈ s, ∀ j ∈ t, x j ≤ x i) :
    (((s.inf' hs x : ℕ) : ℝ) - ((t.sup' ht x : ℕ) : ℝ)) ≤
      Swarming.Group.average s (fun i => Hfix w (x i))
        - Swarming.Group.maximumOn t ht (fun j => Hfix w (x j)) := by
  have hmono : Monotone (Hfix w) := Hfix_monotone hw0 hw1
  have hle : t.sup' ht x ≤ s.inf' hs x :=
    Finset.sup'_le ht _ (fun j hj => Finset.le_inf' hs _ (fun i hi => hsep i hi j hj))
  have hcast : (((s.inf' hs x : ℕ) : ℝ) - ((t.sup' ht x : ℕ) : ℝ))
      = (((s.inf' hs x : ℕ) - (t.sup' ht x : ℕ) : ℕ) : ℝ) := by
    rw [Nat.cast_sub hle]
  have hsub := Swarming.Constants.Hfix_sub_ge w hw0 hw1 hle
  have havg : Hfix w (s.inf' hs x) ≤ Swarming.Group.average s (fun i => Hfix w (x i)) :=
    le_average_of_le hs (fun i hi => hmono (Finset.inf'_le x hi))
  have hmax := maximumOn_comp ht hmono x
  rw [hcast]
  linarith [hsub, havg]

/-! ## From the supermartingale bound to the diameter estimate -/

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Deterministic squeeze**: a nonnegative gap dominated by `W_n ≤ W_0 + Q_n` with
`Q_n = o(n)` is itself `o(n)`.  This is the passage from the supermartingale bound
in Proposition `group` to equation (diam). -/
theorem gap_div_tendsto_zero {gap W Q : ℕ → Ω → ℝ}
    (hgap0 : ∀ n ω, 0 ≤ gap n ω) (hgapW : ∀ n ω, gap n ω ≤ W n ω)
    (hWQ : ∀ n ω, W n ω ≤ W 0 ω + Q n ω)
    (hQ : ∀ᵐ ω ∂μ, Tendsto (fun n => Q n ω / n) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => gap n ω / n) atTop (𝓝 0) := by
  filter_upwards [hQ] with ω hQω
  have hupper : Tendsto (fun n : ℕ => W 0 ω / n + Q n ω / n) atTop (𝓝 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (W 0 ω)).add hQω
    simpa using h
  have hzero : Tendsto (fun n : ℕ => (0 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hzero hupper (fun n => ?_) (fun n => ?_)
  · rcases n with _ | n
    · simp
    · have hden : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      simpa using div_nonneg (hgap0 (n + 1) ω) hden
  · rcases n with _ | n
    · simp
    · have hden : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have h1 : gap (n + 1) ω ≤ W 0 ω + Q (n + 1) ω :=
        le_trans (hgapW (n + 1) ω) (hWQ (n + 1) ω)
      have h2 : gap (n + 1) ω / ((n + 1 : ℕ) : ℝ)
          ≤ (W 0 ω + Q (n + 1) ω) / ((n + 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right h1 (le_of_lt hden)
      have h3 : (W 0 ω + Q (n + 1) ω) / ((n + 1 : ℕ) : ℝ)
          = W 0 ω / ((n + 1 : ℕ) : ℝ) + Q (n + 1) ω / ((n + 1 : ℕ) : ℝ) := by
        field_simp
      linarith

/-- **A nonnegative supermartingale is `o(n)` almost surely.** -/
theorem supermartingale_div_tendsto_zero [IsProbabilityMeasure μ] {W : ℕ → Ω → ℝ}
    {ℱ : Filtration ℕ m0} (hW : Supermartingale W ℱ μ) (h0 : ∀ n, 0 ≤ W n) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => W n ω / n) atTop (𝓝 0) := by
  have h1int : Integrable (W 0) μ := hW.integrable 0
  have hmono : ∀ n, ∫ ω, W n ω ∂μ ≤ ∫ ω, W 0 ω ∂μ := by
    intro n
    have h := hW.setIntegral_le (i := 0) (j := n) (Nat.zero_le n) (s := Set.univ) MeasurableSet.univ
    simpa using h
  have hbound : ∀ n, eLpNorm (-W n) 1 μ ≤ ENNReal.ofReal (∫ ω, W 0 ω ∂μ) := by
    intro n
    have hint : Integrable (W n) μ := hW.integrable n
    have habs : ∫ ω, |W n ω| ∂μ ≤ ∫ ω, W 0 ω ∂μ := by
      rw [show (fun ω => |W n ω|) = W n from funext (fun ω => abs_of_nonneg (h0 n ω))]
      exact hmono n
    calc eLpNorm (-W n) 1 μ = ∫⁻ ω, ‖(-W) n ω‖ₑ ∂μ := eLpNorm_one_eq_lintegral_enorm
      _ = ∫⁻ ω, ‖W n ω‖ₑ ∂μ := by
          simp only [Pi.neg_apply, enorm_neg]
      _ = ∫⁻ ω, ENNReal.ofReal |W n ω| ∂μ := by simp only [Real.enorm_eq_ofReal_abs]
      _ = ENNReal.ofReal (∫ ω, |W n ω| ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal hint.abs
            (Eventually.of_forall (fun _ => abs_nonneg _))).symm
      _ ≤ ENNReal.ofReal (∫ ω, W 0 ω ∂μ) := ENNReal.ofReal_le_ofReal habs
  have hdoob : ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => (-W) n ω) atTop (𝓝 c) := by
    refine Submartingale.exists_ae_tendsto_of_bdd
      (R := Real.toNNReal (∫ ω, W 0 ω ∂μ)) hW.neg ?_
    intro n
    exact hbound n
  filter_upwards [hdoob] with ω hω
  obtain ⟨c, hc⟩ := hω
  have hWc : Tendsto (fun n => W n ω) atTop (𝓝 (-c)) := by
    have := hc.neg
    simpa using this
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hprod : Tendsto (fun n : ℕ => W n ω * ((n : ℝ))⁻¹) atTop (𝓝 (-c * 0)) :=
    hWc.mul hinv
  have hfinal : (fun n : ℕ => W n ω / n) = fun n : ℕ => W n ω * ((n : ℝ))⁻¹ := by
    funext n
    rw [div_eq_mul_inv]
  rw [hfinal]
  simpa using hprod


end SeparatedGroups
