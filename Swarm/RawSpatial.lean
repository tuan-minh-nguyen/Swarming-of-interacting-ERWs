/-
  **The full `h + G` spatial-moment bounds on the actual uniform array.**

  `SpatialG` proves (expmom), (Kmom) and (maxmom) on the abstract product space
  `markMeasureN`. `RawLogRatio.measurePreserving_siteMarksN` identifies that space
  with the actual site marks of `Swarming.Uniform.arrayMeasure N`. This file pulls
  those three estimates back to the strong interacting model. The actual-array
  potential is exactly `hof`/`Gsup` evaluated at `siteMarksN`; no alternate potential
  or walker family is introduced.
-/
import Swarm.RawLogRatio
import Swarm.SpatialG

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal

namespace SwarmLogRatio

noncomputable section

open Swarming Swarming.Uniform

/-- The full-potential exponential moment under the actual array measure. -/
theorem expmom_G_array {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ (j : Fin N) (x : ℕ),
      ∫⁻ U, ENNReal.ofReal (Real.exp
        (c * (SwarmMarks.hof p (siteMarksN p m U j) x +
          SwarmMarks.Gsup p (siteMarksN p m U j) x))) ∂(arrayMeasure N)
        ≤ ENNReal.ofReal C := by
  obtain ⟨c, hc, C, hC, hbound⟩ := SwarmMarks.expmom_G hp1 hp2 hm N
  have hp0 : 0 < p := by linarith
  have hmap := measurePreserving_siteMarksN (N := N) hp0 hp2 m
  refine ⟨c, hc, C, hC, fun j x => ?_⟩
  have hmeas : Measurable (fun ω : Fin N → ℕ → Bool =>
      ENNReal.ofReal (Real.exp
        (c * (SwarmMarks.hof p (ω j) x + SwarmMarks.Gsup p (ω j) x)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul
      (((SwarmMarks.measurable_hof (by linarith : p ≠ 0) x).comp
          (measurable_pi_apply j)).add
        ((SwarmMarks.measurable_Gsup p x).comp (measurable_pi_apply j)))))
  rw [hmap.lintegral_comp hmeas]
  exact hbound j x

/-- The full-potential almost-sure logarithmic bound under the actual array measure. -/
theorem kmom_G_array {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) :
    ∃ c : ℝ, 0 < c ∧ ∀ᵐ U ∂(arrayMeasure N),
      ∀ᶠ n : ℕ in atTop, ∀ j : Fin N, ∀ x ≤ n + 1,
        SwarmMarks.hof p (siteMarksN p m U j) x +
          SwarmMarks.Gsup p (siteMarksN p m U j) x ≤
        (3 / c) * Real.log ((n : ℝ) + 2) := by
  obtain ⟨c, hc, hbound⟩ := SwarmMarks.kmom_G hp1 hp2 hm N
  have hp0 : 0 < p := by linarith
  exact ⟨c, hc, (measurePreserving_siteMarksN (N := N) hp0 hp2 m).quasiMeasurePreserving.ae
    hbound⟩

lemma measurable_YfunGN (p : ℝ) (hp0 : p ≠ 0) (N n : ℕ) (hN : 0 < N) :
    Measurable (fun ω : Fin N → ℕ → Bool => SwarmMarks.YfunGN p N n hN ω) := by
  have hY : (fun ω : Fin N → ℕ → Bool => SwarmMarks.YfunGN p N n hN ω) =
      (Finset.univ : Finset (Fin N)).sup' ⟨⟨0, hN⟩, Finset.mem_univ _⟩
        (fun j (ω : Fin N → ℕ → Bool) => SwarmMarks.YfunG p n (ω j)) := by
    funext ω
    exact (Finset.sup'_apply (s := (Finset.univ : Finset (Fin N)))
      ⟨⟨0, hN⟩, Finset.mem_univ _⟩
      (fun j (ω : Fin N → ℕ → Bool) => SwarmMarks.YfunG p n (ω j)) ω).symm
  rw [hY]
  exact Finset.measurable_sup' _ (fun j _ =>
    (SwarmMarks.measurable_YfunG p hp0 n).comp (measurable_pi_apply j))

/-- The full-potential polynomial running-maximum moment under the actual array measure. -/
theorem maxmom_G_array {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 0 < N) (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ∫⁻ U, ENNReal.ofReal ((1 + SwarmMarks.YfunGN p N n hN (siteMarksN p m U)) ^ s)
          ∂(arrayMeasure N)
        ≤ ENNReal.ofReal (C * (Real.log ((n : ℝ) + 2)) ^ s) := by
  obtain ⟨C, hC, hbound⟩ := SwarmMarks.maxmom_G hp1 hp2 hm N hN s hs
  have hp0 : 0 < p := by linarith
  have hmap := measurePreserving_siteMarksN (N := N) hp0 hp2 m
  refine ⟨C, hC, fun n => ?_⟩
  have hbase : Measurable (fun ω : Fin N → ℕ → Bool =>
      (1 + SwarmMarks.YfunGN p N n hN ω) ^ s) :=
    (Measurable.add measurable_const (measurable_YfunGN p (by linarith) N n hN)).pow_const s
  have hmeas : Measurable (fun ω : Fin N → ℕ → Bool =>
      ENNReal.ofReal ((1 + SwarmMarks.YfunGN p N n hN ω) ^ s)) :=
    ENNReal.measurable_ofReal.comp hbase
  rw [hmap.lintegral_comp hmeas]
  exact hbound n

/-- The actual-array form of both displays of Proposition `spatial`. -/
theorem spatial_G_array {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 0 < N) :
    (∃ c : ℝ, 0 < c ∧ ∀ᵐ U ∂(arrayMeasure N),
        ∀ᶠ n : ℕ in atTop, ∀ j : Fin N, ∀ x ≤ n + 1,
          SwarmMarks.hof p (siteMarksN p m U j) x +
            SwarmMarks.Gsup p (siteMarksN p m U j) x ≤
          (3 / c) * Real.log ((n : ℝ) + 2)) ∧
      (∀ s : ℕ, 1 ≤ s → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
        ∫⁻ U, ENNReal.ofReal ((1 + SwarmMarks.YfunGN p N n hN (siteMarksN p m U)) ^ s)
          ∂(arrayMeasure N) ≤ ENNReal.ofReal (C * (Real.log ((n : ℝ) + 2)) ^ s)) :=
  ⟨kmom_G_array hp1 hp2 hm, fun _ hs => maxmom_G_array hp1 hp2 hm hN _ hs⟩

end
end SwarmLogRatio
