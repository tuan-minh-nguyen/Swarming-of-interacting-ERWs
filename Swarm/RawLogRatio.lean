/-
  **The log-ratio strong law and product decay on the actual uniform array.**

  `LogRatioSLLN` and `ProdDecayBridge` work on the canonical Boolean mark space.
  `MarkFidelity.uniformArray_map_marks` identifies the law of its simplified one-row
  block space.  This file supplies the remaining transport to the strong interacting
  model `Swarming.Uniform.arrayMeasure N`, whose coordinates are indexed by
  `Fin N × ℤ × ℕ`.

  * `siteBlocks` selects the departure coordinates `k = 1, ..., m-1` at nonnegative
    sites of one walker.  Its product law follows from injective coordinate selection
    and product currying; no adaptive-independence argument is used.
  * `siteMarks` is the Boolean version of `Swarming.Trajectory.SiteMark` on nonnegative
    sites.  `measurePreserving_siteMarks` identifies one row's law with the canonical
    i.i.d. Bernoulli family of `MarkProcess`; `measurePreserving_siteMarksN` identifies
    the joint law of every actual row with `markMeasureN`.
  * `rho_omegaAt` proves pointwise that the ratio formed from the actual `omegaAt`
    is `SwarmSpatial.rhoOf` of this Boolean mark.
  * The remaining theorems pull back the strong law, eventual product decay and
    weighted summability to the actual array.  Finite intersections give one common
    full-measure event for every walker.

  Only nonnegative sites enter the one-sided crossing estimates.  These declarations
  do not assert the conditional stopped-crossing bound: that remains a separate input
  to the transience argument.
-/
import Swarm.Reveal
import Swarm.MarkFidelity
import Swarm.BCSummable

set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal

namespace SwarmLogRatio

noncomputable section

attribute [local instance] Classical.propDecidable

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory

/-- The finite block of departure coordinates used by the site mark at a nonnegative site. -/
def siteBlocks {N : ℕ} (m : ℕ) (U : Array N) (j : Fin N) :
    ℕ → Fin (m - 1) → ℝ :=
  fun x k => U (j, (x : ℤ), k.1 + 1)

/-- The actual site-mark sequence on nonnegative sites. -/
def siteMarks {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) : ℕ → Bool :=
  fun x => decide (SiteMark p m U j (x : ℤ))

lemma siteMark_iff_blocks {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N)
    (x : ℕ) :
    SiteMark p m U j (x : ℤ) ↔ ∀ k : Fin (m - 1), p < siteBlocks m U j x k := by
  constructor
  · intro h k
    exact h (k.1 + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  · intro h k hk
    have hk' := Finset.mem_Icc.mp hk
    let l : Fin (m - 1) := ⟨k - 1, by omega⟩
    have hl := h l
    have hkl : l.1 + 1 = k := by dsimp [l]; omega
    simpa only [siteBlocks, hkl] using hl

@[simp] lemma siteMarks_eq_markB {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N)
    (j : Fin N) (x : ℕ) :
    siteMarks p m U j x = SwarmMarks.markB (m - 1) p (siteBlocks m U j x) := by
  simp only [siteMarks, SwarmMarks.markB, siteMark_iff_blocks]

lemma measurable_siteBlocks {N : ℕ} (m : ℕ) (j : Fin N) :
    Measurable (fun U : Array N => siteBlocks m U j) := by
  apply measurable_pi_lambda
  intro x
  apply measurable_pi_lambda
  intro k
  exact measurable_pi_apply _

lemma measurePreserving_siteBlocks {N : ℕ} (m : ℕ) (j : Fin N) :
    MeasurePreserving (fun U : Array N => siteBlocks m U j) (arrayMeasure N)
      (Measure.infinitePi fun _ : ℕ => SwarmMarks.blockMeasure (m - 1)) := by
  let f : (Σ _ : ℕ, Fin (m - 1)) → Fin N × ℤ × ℕ :=
    fun c => (j, (c.1 : ℤ), c.2.1 + 1)
  have hf : Function.Injective f := by
    rintro ⟨x, k⟩ ⟨y, l⟩ h
    simp_all [f, Prod.ext_iff, Fin.ext_iff]
  have hflat := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Fin N × ℤ × ℕ => uniform01) hf
  have hcurry := Measure.infinitePi_map_piCurry
    (fun (_ : ℕ) (_ : Fin (m - 1)) => uniform01)
  simp only [Measure.infinitePi_eq_pi] at hcurry
  have hflatm : Measurable (fun (U : Array N) (c : Σ _ : ℕ, Fin (m - 1)) => U (f c)) :=
    measurable_pi_lambda _ fun c => measurable_pi_apply (f c)
  refine ⟨measurable_siteBlocks m j, ?_⟩
  calc
    Measure.map (fun U : Array N => siteBlocks m U j) (arrayMeasure N) =
        Measure.map (MeasurableEquiv.piCurry (fun (_ : ℕ) (_ : Fin (m - 1)) => ℝ))
          (Measure.map (fun (U : Array N) (c : Σ _ : ℕ, Fin (m - 1)) => U (f c))
            (arrayMeasure N)) := by
      rw [Measure.map_map (MeasurableEquiv.piCurry _).measurable hflatm]
      rfl
    _ = Measure.map (MeasurableEquiv.piCurry (fun (_ : ℕ) (_ : Fin (m - 1)) => ℝ))
          (Measure.infinitePi fun _ : (Σ _ : ℕ, Fin (m - 1)) => uniform01) :=
      congrArg _ hflat
    _ = _ := hcurry


lemma measurePreserving_markTransform {m : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    MeasurePreserving
      (fun (ω : ℕ → Fin (m - 1) → ℝ) (x : ℕ) => SwarmMarks.markB (m - 1) p (ω x))
      (Measure.infinitePi fun _ : ℕ => SwarmMarks.blockMeasure (m - 1))
      (SwarmMarks.markMeasure
        (SwarmMarks.boolMeasure ((1 - p) ^ (m - 1)))) where
  measurable := measurable_pi_lambda _ fun _ =>
    (SwarmMarks.measurable_markB _ _).comp (measurable_pi_apply _)
  map_eq := SwarmMarks.uniformArray_map_marks hp0 hp1

/-- The actual nonnegative site-mark row has exactly the canonical i.i.d. Bernoulli law. -/
theorem measurePreserving_siteMarks {N : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (m : ℕ) (j : Fin N) :
    MeasurePreserving (fun U : Array N => siteMarks p m U j) (arrayMeasure N)
      (SwarmMarks.markMeasure
        (SwarmMarks.boolMeasure ((1 - p) ^ (m - 1)))) := by
  have h := (measurePreserving_markTransform (m := m) hp0 hp1).comp
    (measurePreserving_siteBlocks m j)
  have heq : (fun U : Array N => siteMarks p m U j) =
      (fun U : Array N => (fun (ω : ℕ → Fin (m - 1) → ℝ) (x : ℕ) =>
        SwarmMarks.markB (m - 1) p (ω x)) (siteBlocks m U j)) := by
    funext U x
    exact siteMarks_eq_markB p m U j x
  rw [heq]
  exact h

/-- The log ratio of the actual weight is the Boolean site ratio, pointwise. -/
@[simp] theorem rho_omegaAt {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N)
    (x : ℕ) :
    (1 - omegaAt p m U j (x : ℤ)) / omegaAt p m U j (x : ℤ) =
      SwarmSpatial.rhoOf p (siteMarks p m U j x) := by
  by_cases h : SiteMark p m U j (x : ℤ)
  · simp [omegaAt, siteMarks, h, SwarmSpatial.rhoOf]
  · simp [omegaAt, siteMarks, h, SwarmSpatial.rhoOf]

/-- All walkers' finite departure blocks, still given by selection from the real array. -/
def siteBlocksN {N : ℕ} (m : ℕ) (U : Array N) : Fin N → ℕ → Fin (m - 1) → ℝ :=
  fun j => siteBlocks m U j

/-- All walkers' actual site-mark rows. -/
def siteMarksN {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) : Fin N → ℕ → Bool :=
  fun j => siteMarks p m U j

lemma measurePreserving_siteBlocksN {N : ℕ} (m : ℕ) :
    MeasurePreserving (fun U : Array N => siteBlocksN m U) (arrayMeasure N)
      (Measure.infinitePi fun _ : Fin N =>
        Measure.infinitePi fun _ : ℕ => SwarmMarks.blockMeasure (m - 1)) := by
  haveI := SwarmMarks.isProbabilityMeasure_blockMeasure (m - 1)
  let f : (Σ jx : (Σ _ : Fin N, ℕ), Fin (m - 1)) → Fin N × ℤ × ℕ :=
    fun c => (c.1.1, (c.1.2 : ℤ), c.2.1 + 1)
  have hf : Function.Injective f := by
    rintro ⟨⟨j, x⟩, k⟩ ⟨⟨j', y⟩, l⟩ h
    simp_all [f, Prod.ext_iff, Fin.ext_iff]
  have hflat := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Fin N × ℤ × ℕ => uniform01) hf
  have hcurry1 := Measure.infinitePi_map_piCurry
    (fun (_ : (Σ _ : Fin N, ℕ)) (_ : Fin (m - 1)) => uniform01)
  simp only [Measure.infinitePi_eq_pi] at hcurry1
  have hcurry2 := Measure.infinitePi_map_piCurry
    (fun (_ : Fin N) (_ : ℕ) => SwarmMarks.blockMeasure (m - 1))
  have hflatm : Measurable
      (fun (U : Array N) (c : Σ jx : (Σ _ : Fin N, ℕ), Fin (m - 1)) => U (f c)) :=
    measurable_pi_lambda _ fun c => measurable_pi_apply (f c)
  refine ⟨measurable_pi_lambda _ fun j => measurable_siteBlocks m j, ?_⟩
  calc
    Measure.map (fun U : Array N => siteBlocksN m U) (arrayMeasure N) =
        Measure.map (MeasurableEquiv.piCurry (fun (_ : Fin N) (_ : ℕ) => Fin (m - 1) → ℝ))
          (Measure.map
            (MeasurableEquiv.piCurry
              (fun (_ : (Σ _ : Fin N, ℕ)) (_ : Fin (m - 1)) => ℝ))
            (Measure.map
              (fun (U : Array N) (c : Σ jx : (Σ _ : Fin N, ℕ), Fin (m - 1)) => U (f c))
              (arrayMeasure N))) := by
      rw [Measure.map_map
        (MeasurableEquiv.piCurry
          (fun (_ : (Σ _ : Fin N, ℕ)) (_ : Fin (m - 1)) => ℝ)).measurable hflatm]
      rw [Measure.map_map
        (MeasurableEquiv.piCurry (fun (_ : Fin N) (_ : ℕ) => Fin (m - 1) → ℝ)).measurable
        ((MeasurableEquiv.piCurry
          (fun (_ : (Σ _ : Fin N, ℕ)) (_ : Fin (m - 1)) => ℝ)).measurable.comp hflatm)]
      rfl
    _ = Measure.map (MeasurableEquiv.piCurry (fun (_ : Fin N) (_ : ℕ) => Fin (m - 1) → ℝ))
          (Measure.map
            (MeasurableEquiv.piCurry
              (fun (_ : (Σ _ : Fin N, ℕ)) (_ : Fin (m - 1)) => ℝ))
            (Measure.infinitePi
              fun _ : (Σ jx : (Σ _ : Fin N, ℕ), Fin (m - 1)) => uniform01)) :=
      congrArg _ (congrArg _ hflat)
    _ = Measure.map (MeasurableEquiv.piCurry (fun (_ : Fin N) (_ : ℕ) => Fin (m - 1) → ℝ))
          (Measure.infinitePi
            fun _ : (Σ _ : Fin N, ℕ) => SwarmMarks.blockMeasure (m - 1)) :=
      congrArg _ hcurry1
    _ = _ := hcurry2

lemma measurePreserving_markTransformN {N : ℕ} {m : ℕ} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    MeasurePreserving
      (fun (ω : Fin N → ℕ → Fin (m - 1) → ℝ) (j : Fin N) (x : ℕ) =>
        SwarmMarks.markB (m - 1) p (ω j x))
      (Measure.infinitePi fun _ : Fin N =>
        Measure.infinitePi fun _ : ℕ => SwarmMarks.blockMeasure (m - 1))
      (SwarmMarks.markMeasureN N
        (SwarmMarks.boolMeasure ((1 - p) ^ (m - 1)))) := by
  haveI := SwarmMarks.isProbabilityMeasure_blockMeasure (m - 1)
  have hq0 : 0 ≤ (1 - p) ^ (m - 1) := by positivity
  have hq1 : (1 - p) ^ (m - 1) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  letI : IsProbabilityMeasure (SwarmMarks.boolMeasure ((1 - p) ^ (m - 1))) :=
    SwarmMarks.isProbabilityMeasure_boolMeasure hq0 hq1
  refine ⟨measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun x =>
    (SwarmMarks.measurable_markB _ _).comp (measurable_pi_apply x |>.comp
      (measurable_pi_apply j)), ?_⟩
  rw [SwarmMarks.markMeasureN]
  have h := Measure.infinitePi_map_pi
    (μ := fun _ : Fin N =>
      Measure.infinitePi fun _ : ℕ => SwarmMarks.blockMeasure (m - 1))
    (f := fun _j (ω : ℕ → Fin (m - 1) → ℝ) (x : ℕ) =>
      SwarmMarks.markB (m - 1) p (ω x))
    (fun _j => (measurePreserving_markTransform (m := m) hp0 hp1).measurable)
  rw [h]
  simp only [SwarmMarks.uniformArray_map_marks hp0 hp1]
  exact Measure.infinitePi_eq_pi _

/-- The full family of actual interacting site marks has the canonical independent joint law. -/
theorem measurePreserving_siteMarksN {N : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (m : ℕ) :
    MeasurePreserving (fun U : Array N => siteMarksN p m U) (arrayMeasure N)
      (SwarmMarks.markMeasureN N
        (SwarmMarks.boolMeasure ((1 - p) ^ (m - 1)))) := by
  have h := (measurePreserving_markTransformN (N := N) (m := m) hp0 hp1).comp
    (measurePreserving_siteBlocksN m)
  have heq : (fun U : Array N => siteMarksN p m U) =
      (fun U : Array N =>
        (fun (ω : Fin N → ℕ → Fin (m - 1) → ℝ) (j : Fin N) (x : ℕ) =>
          SwarmMarks.markB (m - 1) p (ω j x)) (siteBlocksN m U)) := by
    funext U j x
    exact siteMarks_eq_markB p m U j x
  rw [heq]
  exact h


/-- The paper's log-ratio strong law for an actual interacting-walker environment row. -/
theorem ae_tendsto_logRho_array {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p)
    (hp2 : p < 1) (m : ℕ) (j : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N),
      Tendsto
        (fun r : ℕ =>
          (∑ x ∈ Finset.range r,
            Real.log ((1 - omegaAt p m U j (x : ℤ)) / omegaAt p m U j (x : ℤ))) / r)
        atTop
        (𝓝 (((1 - p) ^ (m - 1)) * Real.log ((1 - p) / p))) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 ≤ (1 - p) ^ (m - 1) := by positivity
  have hq1 : (1 - p) ^ (m - 1) ≤ 1 :=
    pow_le_one₀ (by linarith) (by linarith)
  have h := (measurePreserving_siteMarks (N := N) hp0 hp2 m j).quasiMeasurePreserving.ae
    (tendsto_avg_logRho (q := (1 - p) ^ (m - 1)) hq0 hq1 p)
  filter_upwards [h] with U hU
  simpa only [rho_omegaAt] using hU

/-- The strong law in the exact `SwarmSpeed.psum` shape consumed by the transience layer. -/
theorem ae_tendsto_psum_omegaAt_array {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p)
    (hp2 : p < 1) (m : ℕ) (j : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N),
      Tendsto
        (fun r : ℕ => SwarmSpeed.psum
          (fun x => Real.log ((1 - omegaAt p m U j (x : ℤ)) /
            omegaAt p m U j (x : ℤ))) r / r)
        atTop
        (𝓝 (((1 - p) ^ (m - 1)) * Real.log ((1 - p) / p))) := by
  filter_upwards [ae_tendsto_logRho_array hp1 hp2 m j] with U hU
  simpa only [SwarmSpeed.psum] using hU

/-- The `psum` strong law simultaneously on every actual environment row. -/
theorem ae_tendsto_psum_omegaAt_array_all {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p)
    (hp2 : p < 1) (m : ℕ) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ j : Fin N,
      Tendsto
        (fun r : ℕ => SwarmSpeed.psum
          (fun x => Real.log ((1 - omegaAt p m U j (x : ℤ)) /
            omegaAt p m U j (x : ℤ))) r / r)
        atTop
        (𝓝 (((1 - p) ^ (m - 1)) * Real.log ((1 - p) / p))) :=
  (ae_all_iff (μ := arrayMeasure N) (ι := Fin N)).mpr
    (fun j => ae_tendsto_psum_omegaAt_array hp1 hp2 m j)

/-- The actual weight products over the paper's blocks decay eventually, almost surely. -/
theorem ae_prod_decay_array {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p)
    (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m) (j : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N),
      ∀ᶠ k : ℕ in atTop,
        ∏ x ∈ Finset.Ioc (SwarmSpeed.lvlA k) (SwarmSpeed.lvlB k),
            ((1 - omegaAt p m U j (x : ℤ)) / omegaAt p m U j (x : ℤ)) ≤
          Real.exp (-(paperC p ((1 - p) ^ (m - 1))) * (SwarmSpeed.lvlB k : ℝ)) := by
  have hp0 : 0 < p := by linarith
  have h := (measurePreserving_siteMarks (N := N) hp0 hp2 m j).quasiMeasurePreserving.ae
    (ae_prod_decay_paper hp1 hp2 hm)
  filter_upwards [h] with U hU
  simpa only [rho_omegaAt] using hU

/-- The weighted products of the actual environment are almost surely summable. -/
theorem ae_summable_prod_decay_array {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p)
    (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m) (j : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N),
      Summable (fun k : ℕ => ((k : ℝ) + 1) ^ 4 *
        ∏ x ∈ Finset.Ioc (SwarmSpeed.lvlA k) (SwarmSpeed.lvlB k),
          ((1 - omegaAt p m U j (x : ℤ)) / omegaAt p m U j (x : ℤ))) := by
  have hp0 : 0 < p := by linarith
  have h := (measurePreserving_siteMarks (N := N) hp0 hp2 m j).quasiMeasurePreserving.ae
    (ae_summable_prod_decay_paper hp1 hp2 hm)
  filter_upwards [h] with U hU
  simpa only [rho_omegaAt] using hU

/-- One common full-measure event gives the exact strong law for every walker's actual row. -/
theorem ae_tendsto_logRho_array_all {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p)
    (hp2 : p < 1) (m : ℕ) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ j : Fin N,
      Tendsto
        (fun r : ℕ =>
          (∑ x ∈ Finset.range r,
            Real.log ((1 - omegaAt p m U j (x : ℤ)) / omegaAt p m U j (x : ℤ))) / r)
        atTop
        (𝓝 (((1 - p) ^ (m - 1)) * Real.log ((1 - p) / p))) :=
  (ae_all_iff (μ := arrayMeasure N) (ι := Fin N)).mpr
    (fun j => ae_tendsto_logRho_array hp1 hp2 m j)

/-- One common full-measure event gives eventual product decay for every actual row. -/
theorem ae_prod_decay_array_all {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p)
    (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ j : Fin N, ∀ᶠ k : ℕ in atTop,
      ∏ x ∈ Finset.Ioc (SwarmSpeed.lvlA k) (SwarmSpeed.lvlB k),
          ((1 - omegaAt p m U j (x : ℤ)) / omegaAt p m U j (x : ℤ)) ≤
        Real.exp (-(paperC p ((1 - p) ^ (m - 1))) * (SwarmSpeed.lvlB k : ℝ)) :=
  (ae_all_iff (μ := arrayMeasure N) (ι := Fin N)).mpr
    (fun j => ae_prod_decay_array hp1 hp2 hm j)

/-- One common full-measure event gives weighted summability for every actual row. -/
theorem ae_summable_prod_decay_array_all {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p)
    (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ j : Fin N,
      Summable (fun k : ℕ => ((k : ℝ) + 1) ^ 4 *
        ∏ x ∈ Finset.Ioc (SwarmSpeed.lvlA k) (SwarmSpeed.lvlB k),
          ((1 - omegaAt p m U j (x : ℤ)) / omegaAt p m U j (x : ℤ))) :=
  (ae_all_iff (μ := arrayMeasure N) (ι := Fin N)).mpr
    (fun j => ae_summable_prod_decay_array hp1 hp2 hm j)

end
end SwarmLogRatio
