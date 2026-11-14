/-
  **`SwarmSpatial.FluctuationVanishes` for the paper's i.i.d. Bernoulli marks.**

  For `1/2 < p < 1` and `m >= 2`, with `q = (1-p)^(m-1)` and the actual S3 process

      M_r (ω) = Σ_{n<r} (mk ω (n+1) - q) hof p ω n ,

  we prove `M_r / r -> 0` almost surely under `markMeasure (boolMeasure q)`, i.e.
  `SwarmSpatial.FluctuationVanishes p m` as defined in `S8.lean`.  Consequently
  `S10.spav` becomes unconditional (`spav_unconditional` below).

  Route.  `Msum` is a martingale for the natural finite-mark filtration
  `Gfilt r = σ(ω 0, …, ω r)` (Hall–Heyde's second-moment strong law, proved in
  `Swarm/MartingaleLimit.lean`, gives `M_r/r -> 0` a.s. when the weighted
  increment variances are summable).  The two probabilistic inputs are:

  * `E[(mk(r+1) - q) h(r) | σ(ω 0, …, ω r)] = 0`, because `ω (r+1)` is independent of
    `σ(ω 0, …, ω r)` (`indep_eval_succ`) and `E mk = q`; and
  * `E[d_r^2] = q(1-q) E[h(r)^2] <= q(1-q) C6` (S3/S4), so that
    `Σ_r E[d_r^2]/(r+1)^2 <= q(1-q) C6 Σ_r (r+1)^{-2} < ∞`.

  No proof holes and no custom axioms.
-/
import Swarm.Imports
import Mathlib.Probability.ConditionalExpectation
import Swarm.S8
import Swarm.S9
import Swarm.S10
import Swarm.MartingaleLimit

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
open SwarmMarks

namespace SwarmSpatial
noncomputable section

/-! ### 1. The natural finite-mark filtration -/

/-- The prefix projection on the mark space. -/
def pref (r : ℕ) (ω : ℕ → Bool) : Fin (r + 1) → Bool := fun i => ω i

lemma measurable_pref (r : ℕ) : Measurable (pref r) :=
  measurable_pi_iff.mpr fun i => measurable_pi_apply (i : ℕ)

/-- `sigma(omega 0, ..., omega r)`, presented as the comap of the prefix projection. -/
def Gfilt (r : ℕ) : MeasurableSpace (ℕ → Bool) :=
  MeasurableSpace.comap (pref r) (inferInstance : MeasurableSpace (Fin (r + 1) → Bool))

lemma gfilt_mono : Monotone Gfilt := by
  intro a b hab
  have hmeas : Measurable fun v : Fin (b + 1) → Bool => fun i : Fin (a + 1) => v ⟨i.val, by omega⟩ := by
    refine measurable_pi_iff.mpr fun i => ?_
    exact measurable_pi_apply _
  have heq : pref a = (fun v : Fin (b + 1) → Bool => fun i : Fin (a + 1) => v ⟨i.val, by omega⟩)
      ∘ pref b := by
    funext ω i
    rfl
  exact MeasurableSpace.comap_le_comap_of_eq_comp
    (f := pref b) (g := pref a)
    (fun v : Fin (b + 1) → Bool => fun i : Fin (a + 1) => v ⟨i.val, by omega⟩) hmeas heq

lemma gfilt_le (r : ℕ) : Gfilt r ≤ (inferInstance : MeasurableSpace (ℕ → Bool)) :=
  (measurable_pref r).comap_le

/-- The natural filtration of the i.i.d. site marks. -/
def Gfiltration : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → Bool)) where
  seq := Gfilt
  mono' := gfilt_mono
  le' := gfilt_le

@[simp] lemma Gfiltration_seq (r : ℕ) : Gfiltration.seq r = Gfilt r := rfl

/-- **Factorization.**  A function of the marks `0, ..., r` is strongly measurable for
`sigma(omega 0, ..., omega r)`. -/
theorem dependsOn_stronglyMeasurable {r : ℕ} {W : (ℕ → Bool) → ℝ}
    (hdep : DependsOn r W) (hW : Measurable W) : StronglyMeasurable[Gfilt r] W := by
  set Wr : (Fin (r + 1) → Bool) → ℝ := fun v => W (extendVec r v) with hWrdef
  have hWr : Measurable Wr := hW.comp (measurable_extendVec r)
  have hfac : W = Wr ∘ pref r := by
    funext ω
    exact hdep ω (extendVec r (pref r ω)) (fun i hi => by
      simp only [pref, extendVec, show i < r + 1 by omega, dite_true])
  rw [hfac]
  exact (hWr.comp (comap_measurable (pref r))).stronglyMeasurable

/-! ### 2. The conditional expectation of one increment vanishes -/

/-- **The key conditional expectation.**  `E[d_r | sigma(omega 0, ..., omega r)] = 0`. -/
theorem condExp_dfun_eq_zero {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hu6i : ∀ n, Integrable (fun ω => (hof p ω n) ^ 6) (markMeasure (boolMeasure q)))
    (r : ℕ) :
    condExp (Gfilt r) (markMeasure (boolMeasure q)) (dfun q p r)
      =ᵐ[markMeasure (boolMeasure q)] 0 := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure h0 h1
  set μ := markMeasure (boolMeasure q) with hμ
  have hp0 : p ≠ 0 := by linarith
  have hXm : Measurable (fun ω : ℕ → Bool => mk ω (r + 1) - q) :=
    (measurable_mk (r + 1)).sub measurable_const
  have hYm : Measurable (fun ω : ℕ → Bool => hof p ω r) := measurable_hof hp0 r
  have hYsm : StronglyMeasurable[Gfilt r] (fun ω : ℕ → Bool => hof p ω r) :=
    dependsOn_stronglyMeasurable (dependsOn_hof (le_refl r)) hYm
  have hfun : IndepFun (fun ω : ℕ → Bool => mk ω (r + 1) - q)
      (fun ω => fun i : Fin (r + 1) => ω i) μ := by
    have hbase := indep_eval_succ (μB := boolMeasure q) r
    have hφ : Measurable (fun b : Bool => ((if b then (1 : ℝ) else 0) - q)) := by fun_prop
    have hψ : Measurable (fun v : Fin (r + 1) → Bool => v) := measurable_id
    have hc := hbase.comp hφ hψ
    simpa [mk, Function.comp_def, hμ] using hc
  have hind : Indep (MeasurableSpace.comap (fun ω : ℕ → Bool => mk ω (r + 1) - q)
      (inferInstance : MeasurableSpace ℝ)) (Gfilt r) μ := hfun
  have hmeanX : ∫ ω, (mk ω (r + 1) - q) ∂μ = 0 := by
    have h := integral_dep_mul_mark_sub (q := q) h0 h1 (m := r) (W := fun _ => (1 : ℝ))
      (dependsOn_const r 1) measurable_const (integrable_const 1)
    simpa [hμ] using h
  have hle1 : MeasurableSpace.comap (fun ω : ℕ → Bool => mk ω (r + 1) - q)
      (inferInstance : MeasurableSpace ℝ) ≤ (inferInstance : MeasurableSpace (ℕ → Bool)) :=
    hXm.comap_le
  have hce : μ[(fun ω : ℕ → Bool => mk ω (r + 1) - q) | Gfilt r]
      =ᵐ[μ] fun _ => ∫ ω, (mk ω (r + 1) - q) ∂μ :=
    condExp_indep_eq hle1 (gfilt_le r)
      (comap_measurable (fun ω : ℕ → Bool => mk ω (r + 1) - q)).stronglyMeasurable hind
  have hXint : Integrable (fun ω : ℕ → Bool => mk ω (r + 1) - q) μ :=
    (integrable_mk h0 h1 (r + 1)).sub (integrable_const q)
  have hXYint : Integrable (fun ω : ℕ → Bool =>
      (mk ω (r + 1) - q) * hof p ω r) μ := by
    have h := integrable_dfun (q := q) hp1 hp2 h0 h1 hu6i r
    refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [dfun]
  have hpull : μ[(fun ω : ℕ → Bool => (mk ω (r + 1) - q) * hof p ω r) | Gfilt r]
      =ᵐ[μ] μ[(fun ω : ℕ → Bool => mk ω (r + 1) - q) | Gfilt r] * fun ω => hof p ω r :=
    condExp_mul_of_stronglyMeasurable_right hYsm hXYint hXint
  have e : dfun q p r = fun ω : ℕ → Bool => (mk ω (r + 1) - q) * hof p ω r := rfl
  rw [e]
  filter_upwards [hpull, hce] with ω h1ω h2ω
  simp only [Pi.mul_apply] at h1ω
  rw [h1ω, h2ω, hmeanX, zero_mul]
  rfl

/-! ### 3. The martingale instance and the strong law -/

/-- `M_r` is adapted to the natural finite-mark filtration. -/
theorem stronglyAdapted_Msum {q : ℝ} {p : ℝ} (hp0 : p ≠ 0) :
    StronglyAdapted Gfiltration (fun r (ω : ℕ → Bool) => Msum q p r ω) := by
  intro r
  exact dependsOn_stronglyMeasurable (dependsOn_Msum r) (measurable_Msum hp0 r)

/-- The fluctuation is integrable at every time. -/
theorem integrable_Msum {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hu6i : ∀ n, Integrable (fun ω => (hof p ω n) ^ 6) (markMeasure (boolMeasure q)))
    (r : ℕ) : Integrable (fun ω => Msum q p r ω) (markMeasure (boolMeasure q)) := by
  induction r with
  | zero => simpa [Msum] using integrable_zero (α := ℕ → Bool) (μ := markMeasure (boolMeasure q)) 0
  | succ r ih =>
      have h := ih.add (integrable_dfun hp1 hp2 h0 h1 hu6i r)
      refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
      simp only [Pi.add_apply]
      rw [Msum_succ]

/-- The conditional expectation of one step vanishes. -/
theorem condExp_Msum_sub {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hu6i : ∀ n, Integrable (fun ω => (hof p ω n) ^ 6) (markMeasure (boolMeasure q)))
    (r : ℕ) :
    condExp (Gfilt r) (markMeasure (boolMeasure q))
        (fun ω : ℕ → Bool => Msum q p (r + 1) ω - Msum q p r ω)
      =ᵐ[markMeasure (boolMeasure q)] 0 := by
  have hfuneq : (fun ω : ℕ → Bool => Msum q p (r + 1) ω - Msum q p r ω) = dfun q p r := by
    funext ω
    rw [Msum_succ]
    ring
  rw [hfuneq]
  exact condExp_dfun_eq_zero h0 h1 hp1 hp2 hu6i r

/-- **The martingale instance for the actual `Msum`.** -/
theorem martingale_Msum {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hu6i : ∀ n, Integrable (fun ω => (hof p ω n) ^ 6) (markMeasure (boolMeasure q))) :
    Martingale (fun r (ω : ℕ → Bool) => Msum q p r ω) Gfiltration
      (markMeasure (boolMeasure q)) := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure h0 h1
  refine martingale_of_condExp_sub_eq_zero_nat
    (stronglyAdapted_Msum (q := q) (by linarith : p ≠ 0))
    (fun r => integrable_Msum h0 h1 hp1 hp2 hu6i r) (fun r => ?_)
  exact condExp_Msum_sub h0 h1 hp1 hp2 hu6i r

/-- The increment of `Msum`. -/
lemma inc_Msum (r : ℕ) (ω : ℕ → Bool) :
    MartingaleLimit.inc (fun r (ω : ℕ → Bool) => Msum q p r ω) r ω = dfun q p r ω := by
  simp only [MartingaleLimit.inc_apply]
  rw [Msum_succ]
  ring

/-- The second moment of one increment is bounded by `q(1-q) C6`. -/
theorem integral_inc_sq_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hu6i : ∀ n, Integrable (fun ω => (hof p ω n) ^ 6) (markMeasure (boolMeasure q)))
    (hu6b : ∀ n, ∫ ω, (hof p ω n) ^ 6 ∂(markMeasure (boolMeasure q)) ≤ C6)
    (r : ℕ) :
    ∫ ω, (MartingaleLimit.inc (fun r (ω : ℕ → Bool) => Msum q p r ω) r ω) ^ 2
        ∂(markMeasure (boolMeasure q)) ≤ q * (1 - q) * C6 := by
  have hcongr : (fun ω : ℕ → Bool =>
      (MartingaleLimit.inc (fun r (ω : ℕ → Bool) => Msum q p r ω) r ω) ^ 2)
      = fun ω => (dfun q p r ω) ^ 2 := by
    funext ω
    rw [inc_Msum]
  rw [hcongr, integral_dfun_sq h0 h1 hp1 hp2 hu6i r]
  refine mul_le_mul_of_nonneg_left
    (integral_hof_pow_le_six hp1 hp2 hu6i hu6b (by norm_num) r) ?_
  nlinarith

/-- The weighted variance series is summable. -/
theorem summable_weighted_variance {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hu6i : ∀ n, Integrable (fun ω => (hof p ω n) ^ 6) (markMeasure (boolMeasure q)))
    (hu6b : ∀ n, ∫ ω, (hof p ω n) ^ 6 ∂(markMeasure (boolMeasure q)) ≤ C6) :
    Summable fun k : ℕ =>
      ((k : ℝ) + 1)⁻¹ ^ 2 *
        ∫ ω, (MartingaleLimit.inc (fun r (ω : ℕ → Bool) => Msum q p r ω) k ω) ^ 2
          ∂(markMeasure (boolMeasure q)) := by
  have hbase : Summable fun k : ℕ => ((k : ℝ) + 1)⁻¹ ^ 2 := by
    have h1' : Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2 :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have h2' : Summable fun n : ℕ => (1 : ℝ) / (((n : ℕ) : ℝ) + 1) ^ 2 := by
      simpa using (summable_nat_add_iff 1).mpr h1'
    refine h2'.congr fun k => ?_
    rw [one_div, inv_pow]
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (hbase.mul_left (q * (1 - q) * C6))
  have h2 : (0 : ℝ) ≤ ((k : ℝ) + 1)⁻¹ ^ 2 := by positivity
  calc ((k : ℝ) + 1)⁻¹ ^ 2 *
        ∫ ω, (MartingaleLimit.inc (fun r (ω : ℕ → Bool) => Msum q p r ω) k ω) ^ 2
          ∂(markMeasure (boolMeasure q))
      ≤ ((k : ℝ) + 1)⁻¹ ^ 2 * (q * (1 - q) * C6) :=
        mul_le_mul_of_nonneg_left (integral_inc_sq_le h0 h1 hp1 hp2 hu6i hu6b k) h2
    _ = (q * (1 - q) * C6) * ((k : ℝ) + 1)⁻¹ ^ 2 := by ring

/-- **The second-moment martingale strong law for `Msum`.** -/
theorem tendsto_Msum_div {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hu6i : ∀ n, Integrable (fun ω => (hof p ω n) ^ 6) (markMeasure (boolMeasure q)))
    (hu6b : ∀ n, ∫ ω, (hof p ω n) ^ 6 ∂(markMeasure (boolMeasure q)) ≤ C6) :
    ∀ᵐ ω ∂(markMeasure (boolMeasure q)),
      Tendsto (fun r : ℕ => ((r : ℝ))⁻¹ * Msum q p r ω) atTop (nhds 0) := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure h0 h1
  have hint : ∀ k : ℕ, Integrable (fun ω : ℕ → Bool =>
      (MartingaleLimit.inc (fun r (ω : ℕ → Bool) => Msum q p r ω) k ω) ^ 2)
      (markMeasure (boolMeasure q)) := by
    intro k
    have h := integrable_dfun_pow hp1 hp2 h0 h1 hu6i (k := 2) (by norm_num) k
    have e : (fun ω : ℕ → Bool =>
        (MartingaleLimit.inc (fun r (ω : ℕ → Bool) => Msum q p r ω) k ω) ^ 2)
        = fun ω => (dfun q p k ω) ^ 2 := by
      funext ω
      rw [inc_Msum]
    rw [e]
    exact h
  have hsl := MartingaleLimit.martingale_strong_law
    (μ := markMeasure (boolMeasure q)) (ℱ := Gfiltration)
    (Q := fun r (ω : ℕ → Bool) => Msum q p r ω)
    (martingale_Msum h0 h1 hp1 hp2 hu6i) hint
    (summable_weighted_variance h0 h1 hp1 hp2 hu6i hu6b)
  filter_upwards [hsl] with ω hω
  have e : (fun n : ℕ => (Msum q p n ω - Msum q p 0 ω) / (n : ℝ))
      = fun n : ℕ => (n : ℝ)⁻¹ * Msum q p n ω := by
    funext n
    have h0' : Msum q p 0 ω = 0 := by simp [Msum]
    rw [h0', sub_zero]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have hn' : (n : ℝ) ≠ 0 := by
        have : (0 : ℝ) < n := by exact_mod_cast hn
        positivity
      field_simp
  rw [e] at hω
  exact hω

/-! ### 4. `FluctuationVanishes` for the paper's parameters -/

/-- **The fluctuation lemma.**  For `1/2 < p < 1` and `m ≥ 2`, the centred-mark fluctuation
`M_r = Σ_{n<r} (mk(n+1) - q) h(n)` with `q = (1-p)^{m-1}` is `o(r)` almost surely:
this is `S8.FluctuationVanishes p m`, with no remaining hypothesis. -/
theorem fluctuationVanishes {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) : FluctuationVanishes p m := by
  obtain ⟨C6, hC6, hu6⟩ := exists_hof_pow_bound hp1 hp2 hm 6 (by norm_num)
  have hq0 : (0 : ℝ) ≤ (1 - p) ^ (m - 1) := (qpos hp2).le
  have hq1 : (1 - p) ^ (m - 1) ≤ 1 := qle_one hp1 hp2 (by omega)
  exact tendsto_Msum_div (q := (1 - p) ^ (m - 1)) (C6 := C6) hq0 hq1 hp1 hp2
    (fun n => (hu6 n).1) (fun n => (hu6 n).2)

/-- **(spav), first display, unconditional.**  For the actual i.i.d. Bernoulli site marks with
`q = (1-p)^{m-1}`, the spatial average of the paper's `h_j` converges almost surely to
`(1+a)/(1-a)`, `a = 1 - (2p-1)q/p`. -/
theorem spav_unconditional {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) :
    ∀ᵐ ω ∂(markMeasure (boolMeasure ((1 - p) ^ (m - 1)))),
      Filter.Tendsto (fun r : ℕ => (r : ℝ)⁻¹ * ∑ k ∈ Finset.range r, hof p ω k)
        Filter.atTop (nhds (targetParam p m)) :=
  spav hp1 hp2 hm (fluctuationVanishes hp1 hp2 hm)

end
end SwarmSpatial

/-! ### Audit -/


