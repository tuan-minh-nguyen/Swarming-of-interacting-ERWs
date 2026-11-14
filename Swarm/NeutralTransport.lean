/-
  Transport ballisticity through the initial-regeneration
  path-law identity, removing absolute continuity from the neutral-law assembly.

-/
import Swarm.StarRegen

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace M7Neutral

/-- A vanishing difference transfers a lower bound on `liminf`; unlike the
unit-bound version in `DensReduction`, this accepts any common absolute bound. -/
theorem le_liminf_of_tendsto_sub_zero {a b : ℕ → ℝ} {C κ : ℝ}
    (ha : ∀ n, |a n| ≤ C) (hb : ∀ n, |b n| ≤ C)
    (h : Tendsto (fun n => a n - b n) atTop (𝓝 0))
    (hκ : κ ≤ liminf b atTop) : κ ≤ liminf a atTop := by
  refine (le_liminf_iff (SwarmDens.isCoboundedUnder_ge_of_abs_le ha)
    (SwarmDens.isBoundedUnder_ge_of_abs_le ha)).mpr ?_
  intro y hy
  obtain ⟨y₂, hyy₂, hy₂κ⟩ := exists_between hy
  obtain ⟨y₃, hy₂y₃, hy₃l⟩ := exists_between (lt_of_lt_of_le hy₂κ hκ)
  have hδ : (0 : ℝ) < y₂ - y := by linarith
  have hev : ∀ᶠ n : ℕ in atTop, y₂ < b n :=
    (le_liminf_iff (SwarmDens.isCoboundedUnder_ge_of_abs_le hb)
      (SwarmDens.isBoundedUnder_ge_of_abs_le hb)).mp (le_of_lt hy₃l) y₂ hy₂y₃
  have hdiff : ∀ᶠ n : ℕ in atTop, |a n - b n| < y₂ - y :=
    SwarmDens.abs_sub_eventually_lt h hδ
  filter_upwards [hev, hdiff] with n hbn hdn
  have hsub : b n - a n ≤ |a n - b n| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  linarith

/-- Finite temporal and spatial translations preserve a lower bound on the
`liminf` of a bounded normalized path. -/
theorem le_liminf_translate {y : ℕ → ℝ} {c κ : ℝ} {S : ℕ}
    (hy : ∀ n, |y n / (n : ℝ)| ≤ 1)
    (hκ : κ ≤ liminf (fun n => y n / (n : ℝ)) atTop) :
    κ ≤ liminf (fun n => (y (n + S) - c) / (n : ℝ)) atTop := by
  let a : ℕ → ℝ := fun n => (y (n + S) - c) / (n : ℝ)
  let b : ℕ → ℝ := fun n => y (n + S) / ((n + S : ℕ) : ℝ)
  let C : ℝ := 1 + (S : ℝ) + |c|
  have hb_one : ∀ n, |b n| ≤ 1 := by
    intro n
    simpa [b, Nat.cast_add] using hy (n + S)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb : ∀ n, |b n| ≤ C := by
    intro n
    refine (hb_one n).trans ?_
    dsimp [C]
    have hS0 : (0 : ℝ) ≤ (S : ℝ) := Nat.cast_nonneg S
    have hc0 : 0 ≤ |c| := abs_nonneg c
    linarith
  have ha : ∀ n, |a n| ≤ C := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa [a] using hC
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hden : (0 : ℝ) < ((n + S : ℕ) : ℝ) := by positivity
    have hnorm : |y (n + S)| ≤ ((n + S : ℕ) : ℝ) := by
      have h := hb_one n
      change |y (n + S) / ((n + S : ℕ) : ℝ)| ≤ 1 at h
      rw [abs_div, abs_of_pos hden] at h
      exact (div_le_one hden).mp h
    rw [show a n = (y (n + S) - c) / (n : ℝ) from rfl, abs_div, abs_of_pos hnR]
    apply (div_le_iff₀ hnR).2
    calc
      |y (n + S) - c| ≤ |y (n + S)| + |c| := abs_sub _ _
      _ ≤ ((n + S : ℕ) : ℝ) + |c| := add_le_add hnorm le_rfl
      _ ≤ C * (n : ℝ) := by
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        dsimp [C]
        push_cast
        have hnon : 0 ≤ ((n : ℝ) - 1) * ((S : ℝ) + |c|) :=
          mul_nonneg (sub_nonneg.mpr hn1) (add_nonneg (Nat.cast_nonneg S) (abs_nonneg c))
        nlinarith
  have hS : Tendsto (fun n : ℕ => (S : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun n : ℕ => c / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hprod_norm : Tendsto (fun n : ℕ => ‖b n * ((S : ℝ) / (n : ℝ))‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => norm_nonneg _)
    · intro n
      calc
        ‖b n * ((S : ℝ) / (n : ℝ))‖ = |b n| * |(S : ℝ) / (n : ℝ)| := by
          simp only [norm_mul, Real.norm_eq_abs]
        _ ≤ 1 * |(S : ℝ) / (n : ℝ)| :=
          mul_le_mul_of_nonneg_right (hb_one n) (abs_nonneg _)
        _ = |(S : ℝ) / (n : ℝ)| := one_mul _
    · simpa only [Real.norm_eq_abs, norm_zero] using hS.norm
  have hprod : Tendsto (fun n : ℕ => b n * ((S : ℝ) / (n : ℝ))) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hprod_norm
  have hEq : (fun n => a n - b n) =ᶠ[atTop]
      (fun n => b n * ((S : ℝ) / (n : ℝ)) - c / (n : ℝ)) := by
    filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hns0 : ((n + S : ℕ) : ℝ) ≠ 0 := by positivity
    dsimp [a, b]
    field_simp
    push_cast
    ring
  have hzero : Tendsto (fun n => a n - b n) atTop (𝓝 0) := by
    have h := hprod.sub hc
    rw [sub_zero] at h
    exact h.congr' hEq.symm
  have hbκ : κ ≤ liminf b atTop := by
    have hshift := Filter.liminf_nat_add (fun n => y n / (n : ℝ)) S
    rw [show liminf b atTop = liminf (fun n => y n / (n : ℝ)) atTop by
      simpa [b, Nat.cast_add] using hshift]
    exact hκ
  exact le_liminf_of_tendsto_sub_zero ha hb hzero hbκ

/-- The common ballistic event is measurable on real-valued path space. -/
theorem measurableSet_all_le_liminf {N : ℕ} (κ : ℝ) :
    MeasurableSet {x : ℕ → Fin N → ℝ | ∀ i : Fin N,
      κ ≤ liminf (fun n : ℕ => x n i / (n : ℝ)) atTop} := by
  rw [Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => measurableSet_le measurable_const <|
    Measurable.liminf fun n => by
      have hn : Measurable (fun x : ℕ → Fin N → ℝ => x n) := measurable_pi_apply n
      have hi : Measurable (fun g : Fin N → ℝ => g i) := measurable_pi_apply i
      exact (hi.comp hn).div_const (n : ℝ)

/-- Transport any measurable path event across an equality of path laws. -/
theorem ae_transfer_of_map_eq {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    {μ ν : Measure Ω} {Ψ Φ : Ω → (ℕ → Fin N → ℝ)} {s : Set (ℕ → Fin N → ℝ)}
    (hΨ : Measurable Ψ) (hΦ : Measurable Φ)
    (hmap : μ.map Φ = ν.map Ψ) (hs : MeasurableSet s)
    (hμ : ∀ᵐ U ∂μ, Φ U ∈ s) : ∀ᵐ U ∂ν, Ψ U ∈ s := by
  have h1 : ∀ᵐ x ∂(μ.map Φ), x ∈ s := (ae_map_iff hΦ.aemeasurable hs).2 hμ
  rw [hmap] at h1
  exact (ae_map_iff hΨ.aemeasurable hs).1 h1

open Swarming.Uniform

variable {N m : ℕ} {p : ℝ}

/-- Actual-array common speed from a neutral regeneration law and the literal
initial-regeneration path-law identity.  No absolute continuity of the neutral
measure is needed: the identity transports the finite-shift ballistic event.
The neutral duration integral is derived by `actual_common_speed_of_neutral_ED`,
and the uniform ballistic constant is retained in the conclusion. -/
theorem actual_common_speed_of_neutral_map
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N)
    (ν : Measure (Array N)) [IsProbabilityMeasure ν]
    (D T : ℕ → Array N → ℕ)
    (hreg : Swarm.RegenLawWeak ν D T)
    (hsand : Swarm.Sandwich ν (Swarm.actualX (N := N) p m) D T)
    (S : Array N → ℕ) (c : Array N → ℝ) (hS : Measurable S) (hc : Measurable c)
    (hmap : Measure.map (fun U : Array N => fun (n : ℕ) (i : Fin N) =>
        Swarm.pos (Swarm.actualX (N := N) p m) (n + S U) i U - c U) (arrayMeasure N)
      = Measure.map (M6Star.actPath (N := N) p m) ν) :
    ∃ κ : ℝ, 0 < κ ∧
      κ ≤ (∫ U, (D 0 U : ℝ) ∂ν) / (∫ U, (T 0 U : ℝ) ∂ν) ∧
      (∫ U, (D 0 U : ℝ) ∂ν) / (∫ U, (T 0 U : ℝ) ∂ν) ≤ 2 * p - 1 ∧
      ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
        Tendsto (fun n : ℕ => Swarm.pos (Swarm.actualX (N := N) p m) n i U / (n : ℝ)) atTop
          (𝓝 ((∫ U, (D 0 U : ℝ) ∂ν) / (∫ U, (T 0 U : ℝ) ∂ν))) := by
  classical
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  obtain ⟨κ, hκpos, hκlim⟩ := Swarm.actualProjectedBallistic hp0 hp1 hm
  obtain ⟨𝓕, hlaw⟩ : ∃ 𝓕 : Filtration ℕ (inferInstanceAs (MeasurableSpace (Array N))),
      Swarm.IsInteractingLaw 𝓕 (arrayMeasure N) (Swarm.actualX (N := N) p m) m p :=
    ⟨_, SwarmCross.Actual.actual_isInteractingLaw (N := N) hp0 hp1 m⟩
  let Φ : Array N → (ℕ → Fin N → ℝ) := fun U n i =>
    Swarm.pos (Swarm.actualX (N := N) p m) (n + S U) i U - c U
  let Ψ : Array N → (ℕ → Fin N → ℝ) := M6Star.actPath (N := N) p m
  have hΦ : Measurable Φ := by
    simpa [Φ] using M6Star.measurable_shiftPath (N := N) p m S c hS hc
  have hΨ : Measurable Ψ := by
    simpa [Ψ] using M6Star.measurable_actPath (N := N) p m
  have hmap' : (arrayMeasure N).map Φ = ν.map Ψ := by
    simpa [Φ, Ψ] using hmap
  have hnorm : ∀ (U : Array N) (i : Fin N) (n : ℕ),
      |Swarm.pos (Swarm.actualX (N := N) p m) n i U / (n : ℝ)| ≤ 1 :=
    fun U i n => SwarmDens.abs_pos_div_le_one hlaw n U i
  have hshift : ∀ᵐ U ∂(arrayMeasure N), Φ U ∈ {x : ℕ → Fin N → ℝ | ∀ i : Fin N,
      κ ≤ liminf (fun n : ℕ => x n i / (n : ℝ)) atTop} := by
    filter_upwards [hκlim N hN] with U hU
    intro i
    change κ ≤ liminf (fun n : ℕ =>
      (Swarm.pos (Swarm.actualX (N := N) p m) (n + S U) i U - c U) / (n : ℝ)) atTop
    exact le_liminf_translate (y := fun n => Swarm.pos (Swarm.actualX (N := N) p m) n i U)
      (fun n => hnorm U i n) (by simpa using hU i)
  have hballν : ∀ᵐ U ∂ν, ∀ i : Fin N,
      κ ≤ liminf (fun n : ℕ => Swarm.pos (Swarm.actualX (N := N) p m) n i U / (n : ℝ)) atTop := by
    have h := ae_transfer_of_map_eq hΨ hΦ hmap' (measurableSet_all_le_liminf κ) hshift
    simpa [Ψ, M6Star.actPath] using h
  have hbdν : ∀ᵐ U ∂ν, ∀ (i : Fin N) (n : ℕ),
      -(1 : ℝ) ≤ Swarm.pos (Swarm.actualX (N := N) p m) n i U / (n : ℝ) := by
    exact Eventually.of_forall fun U i n => (abs_le.mp (hnorm U i n)).1
  obtain ⟨_hvpos, hvup, hlim⟩ := M6Star.actual_common_speed_of_neutral_ED
    (N := N) hp0 hp1 hm hN ν D T hκpos hreg hsand hballν hbdν S c hS hc hmap
  refine ⟨κ, hκpos, ?_, hvup, hlim⟩
  by_cases hcase : κ ≤ (∫ U, (D 0 U : ℝ) ∂ν) / (∫ U, (T 0 U : ℝ) ∂ν)
  · exact hcase
  · exfalso
    have hall : ∀ᵐ U ∂(arrayMeasure N),
        κ ≤ (∫ U, (D 0 U : ℝ) ∂ν) / (∫ U, (T 0 U : ℝ) ∂ν) := by
      have i₀ : Fin N := ⟨0, by omega⟩
      filter_upwards [hκlim N hN, hlim] with U hb hcl
      exact Swarm.le_of_le_liminf_of_tendsto (hcl i₀) (by simpa using hb i₀)
    exact absurd (MeasureTheory.ae_iff.1 hall) (by simp [hcase])

end M7Neutral
