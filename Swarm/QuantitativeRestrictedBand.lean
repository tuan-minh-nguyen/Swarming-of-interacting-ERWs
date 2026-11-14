/-
# Quantitative restricted-`GoodTime` bounds and the exact far-tail identity

`RestrictedGoodTimeBand` proves that the restricted no-`GoodTime` mass on the
bounded-ratio band `C₀*L ≤ r ≤ K*L` tends to zero, and that the full restricted
event splits into that band plus an uncontrolled far tail `K*L < r`.  Its band
bound carries no rate: it is obtained from almost-sure convergence of the
normalized defect and a finite-measure limit.

This file supplies three things that the existing interface does not have.

1. **The band bound is an absolute-scale statement.**  The pathwise engine
   `quarterGood_of_abs_defect` produces `QuarterGood` (hence a genuine
   `GoodTime`) from an *absolute* defect bound `d_s < L/8` on the window
   `[S, (K+B)*L]`, with no normalized-defect limit and no restriction on the
   lower band edge beyond `S ≤ r`.  The only genuinely global input is the
   one-walker speed lower bound from a fixed threshold `N₀ ≤ L`.

2. **An explicit rate for the band mass.**  The band mass is bounded, for every
   `L` above one fixed threshold, by `δ + (defect-window mass)`, where `δ` is
   *independent of* `L`, `C₀` and `K` and can be made arbitrarily small by
   raising `N₀`.  All remaining `L`-dependence sits in one absolute-scale defect
   window.  `bandQuarterBad_cubic_of_defectWindow_cubic` records that a
   cubically dominated window gives a cubically dominated band term, and
   `measure_restrictedNoGood_le_add_window_far` keeps the far tail visible.

3. **The far tail is exactly the supremum of the band masses over `K`.**
   `restrictedNoGood_eq_iUnion_band` is an exact set identity, and
   `measure_restrictedNoGood_eq_iSup_band` its exact measure form; consequently
   `exists_band_mass_close` shows that at every level `L ≥ 1` some *single*
   finite `K` already carries essentially the whole restricted mass.  Hence no
   family of bounds at fixed `K` can bound `restrictedNoGood`, and the far tail
   `r > K*L` cannot be removed by enlarging `K`.  This is a scope statement
   about the existing route, not a weakening of `GoodTime`.

Nothing here asserts the missing stochastic estimate, an invariant law, onset,
`MainClaim`, or a vanishing full restricted profile.
-/
import Swarm.RestrictedGoodTimeBand
import Swarm.BaseCarrierObstruction

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped ENNReal BigOperators

open RecordDefect RecordoSupply HblkTwo HblkFinal FluidBlock
open Swarming Swarming.Uniform SwarmRecordMeas SwarmRecordMeas.Actual

namespace QuantitativeRestrictedBand

/-! ## 1. The pathwise band engine from an absolute-scale defect bound -/

section Pathwise

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {X : ι → ℕ → ℤ} {τ : ℕ → ℕ}

/-- **`QuarterGood` on a band from an absolute defect bound.**

If one walker's lower speed bound `(κ/2) n ≤ X i n` holds for all `n ≥ N₀`, and
the defect satisfies `d_s < L/8` on the whole window `[S, (K+B)*L]`, then every
level `r` with `S ≤ r ≤ K*L` satisfies `QuarterGood` at the explicit record-time
allowance `bandTime κ B K`.  Unlike `eventually_quarterGood_band` there is no
normalized-defect limit and no constraint `S ≤ L`: the whole content is the
absolute bound at the two endpoints `r` and `r + B*L`. -/
theorem quarterGood_of_abs_defect (hτ : IsRecord X τ)
    {i : ι} {κ : ℝ} (hκ : 0 < κ) {N₀ B K L S : ℕ}
    (hspd : ∀ n : ℕ, N₀ ≤ n → (κ / 2) * (n : ℝ) ≤ (X i n : ℝ))
    (hB : 1 ≤ B) (hN₀L : N₀ ≤ L)
    (hdef : ∀ s : ℕ, S ≤ s → s ≤ (K + B) * L → (defect X τ s : ℝ) < (L : ℝ) / 8) :
    ∀ r : ℕ, S ≤ r → r ≤ K * L →
      LagForce.QuarterGood X τ B (RestrictedGoodTimeBand.bandTime κ B K) r L := by
  intro r hSr hrK
  let T : ℕ := RestrictedGoodTimeBand.bandTime κ B K
  let γ : ℝ := 2 * ((K : ℝ) + (B : ℝ)) / κ
  have hKBnat : 0 < K + B := by omega
  have hKB : (0 : ℝ) < (K : ℝ) + (B : ℝ) := by exact_mod_cast hKBnat
  have hγT : γ + 1 ≤ (T : ℝ) := by
    have hceil : γ ≤ ((⌈γ⌉₊ : ℕ) : ℝ) := Nat.le_ceil γ
    dsimp [T, γ, RestrictedGoodTimeBand.bandTime]
    push_cast
    linarith
  have hrK' : r ≤ (K + B) * L := by
    rw [Nat.add_mul]
    exact hrK.trans (Nat.le_add_right (K * L) (B * L))
  have hrB : r + B * L ≤ (K + B) * L := by
    rw [Nat.add_mul]
    exact Nat.add_le_add_right hrK (B * L)
  have hSrB : S ≤ r + B * L := hSr.trans (Nat.le_add_right r (B * L))
  have hbaseR : (defect X τ r : ℝ) < (L : ℝ) / 8 := hdef r hSr hrK'
  have hendR : (defect X τ (r + B * L) : ℝ) < (L : ℝ) / 8 := hdef (r + B * L) hSrB hrB
  have hbase : defect X τ r ≤ (L : ℤ) := by
    have h : (defect X τ r : ℝ) ≤ (L : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) L]
    exact_mod_cast h
  have hend : 4 * defect X τ (r + B * L) ≤ (L : ℤ) := by
    have h : (4 : ℝ) * (defect X τ (r + B * L) : ℝ) ≤ (L : ℝ) := by
      linarith [Nat.cast_nonneg (α := ℝ) L]
    exact_mod_cast h
  have hmono : τ r ≤ τ (r + B * L) := tau_mono hτ (Nat.le_add_right r (B * L))
  have htau := SwarmM4C.FixedConst.tau_le_threshold hτ hκ hspd (r + B * L)
  have hrKL : (r : ℝ) ≤ (K : ℝ) * (L : ℝ) := by exact_mod_cast hrK
  have hN₀R : (N₀ : ℝ) ≤ (L : ℝ) := by exact_mod_cast hN₀L
  have hcastBL : (((r + B * L : ℕ)) : ℝ) = (r : ℝ) + (B : ℝ) * (L : ℝ) := by push_cast; ring
  have htauUpper : (τ (r + B * L) : ℝ) ≤ (N₀ : ℝ) + γ * (L : ℝ) := by
    calc (τ (r + B * L) : ℝ) ≤ (N₀ : ℝ) + (2 / κ) * (((r + B * L : ℕ)) : ℝ) := htau
      _ ≤ (N₀ : ℝ) + (2 / κ) * (((K : ℝ) + (B : ℝ)) * (L : ℝ)) := by
            refine add_le_add (le_refl _) ?_
            refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0 : ℝ) ≤ 2 / κ)
            rw [hcastBL]
            nlinarith [Nat.cast_nonneg (α := ℝ) B, Nat.cast_nonneg (α := ℝ) L, hrKL]
      _ = (N₀ : ℝ) + γ * (L : ℝ) := by dsimp [γ]; ring
  have htime : τ (r + B * L) - τ r ≤ T * L := by
    have htimeR : ((τ (r + B * L) - τ r : ℕ) : ℝ) ≤ ((T * L : ℕ) : ℝ) := by
      rw [show ((τ (r + B * L) - τ r : ℕ) : ℝ) =
          (τ (r + B * L) : ℝ) - (τ r : ℝ) by push_cast [hmono]; ring]
      rw [show ((T * L : ℕ) : ℝ) = (T : ℝ) * (L : ℝ) by push_cast; ring]
      have hmul := mul_le_mul_of_nonneg_right hγT (Nat.cast_nonneg (α := ℝ) L)
      calc (τ (r + B * L) : ℝ) - (τ r : ℝ) ≤ (τ (r + B * L) : ℝ) := by
            linarith [Nat.cast_nonneg (α := ℝ) (τ r)]
        _ ≤ (N₀ : ℝ) + γ * (L : ℝ) := htauUpper
        _ ≤ (L : ℝ) + γ * (L : ℝ) := add_le_add hN₀R (le_refl _)
        _ = (γ + 1) * (L : ℝ) := by ring
        _ ≤ (T : ℝ) * (L : ℝ) := hmul
    exact_mod_cast htimeR
  exact ⟨hbase, htime, hend⟩

/-- **Sharp two-endpoint bridge.**  The `QuarterGood` block condition follows from
the *absolute* bounds `d_r < L/8`, `d_{r+BL} < L/8` together with the record
advance `τ (r+BL) - τ r ≤ T*L`.  This is the sharp-constant form of the paper's
block implication: `L/8` at both endpoints, not `L` at the start and `L/4` at the
end.  It is what makes the mass of the block-failure event bounded by three
*small* single-level tails rather than by the two carrier tails. -/
theorem quarterGood_of_half_defect (hτ : IsRecord X τ) {B T r L : ℕ}
    (hbase : (defect X τ r : ℝ) < (L : ℝ) / 8)
    (hend : (defect X τ (r + B * L) : ℝ) < (L : ℝ) / 8)
    (htime : τ (r + B * L) - τ r ≤ T * L) :
    LagForce.QuarterGood X τ B T r L := by
  refine ⟨?_, htime, ?_⟩
  · have h : (defect X τ r : ℝ) ≤ (L : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) L]
    exact_mod_cast h
  · have h : (4 : ℝ) * (defect X τ (r + B * L) : ℝ) ≤ (L : ℝ) := by
      linarith [Nat.cast_nonneg (α := ℝ) L]
    exact_mod_cast h

end Pathwise

/-! ## 1b. Exact pointwise decomposition: no band, no normalized defect -/

section Decomposition

variable {N : ℕ} [Nonempty (Fin N)]

/-- The absolute upper tail of the defect at the *single* level `s`, at threshold
`L/8`. -/
def defectHigh (p : ℝ) (m s L : ℕ) : Set (Array N) :=
  {U | (L : ℝ) / 8 ≤ (defect (actX p m U) (recTimeA p m U) s : ℝ)}

/-- The record-advance exception at the single starting level `r`, in the literal
form `τ (r+B*L) > τ r + T*L`. -/
def timeLag (p : ℝ) (m B T r L : ℕ) : Set (Array N) :=
  {U | recTimeA p m U r + T * L < recTimeA p m U (r + B * L)}

/-- **Pointwise three-term reduction of the carrier-restricted profile.**  For
*every* starting level `r` and scale `L` (no band, no `r ≥ C₀*L`, no normalized
defect), the carrier-restricted no-`GoodTime` event is almost surely contained in
three single-level exceptions: the defect at `r`, the defect at `r + B*L`, and the
record advance.  The threshold is `L/8` at both endpoints. -/
theorem restrictedAe_subset_three (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m B T r L : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) :
    ∀ᵐ U ∂(arrayMeasure N),
      U ∈ {U : Array N | defect (actX p m U) (recTimeA p m U) r ≤ (L : ℤ) ∧
            ¬ ∃ n : ℕ, GoodTime (actX p m U) (recTimeA p m U) B T r L n} →
        U ∈ defectHigh (N := N) p m r L ∪ defectHigh (N := N) p m (r + B * L) L ∪
          timeLag (N := N) p m B T r L := by
  filter_upwards [ae_isRecord_recTimeA (N := N) hp0 hp1 hm hN] with U hτ hU
  obtain ⟨_hcarrier, hno⟩ := hU
  by_contra hcon
  rw [Set.mem_union, Set.mem_union, not_or, not_or] at hcon
  obtain ⟨⟨hhigh1, hhigh2⟩, hlag⟩ := hcon
  have hbase : (defect (actX p m U) (recTimeA p m U) r : ℝ) < (L : ℝ) / 8 := by
    by_contra hge
    exact hhigh1 (not_lt.mp hge)
  have hend : (defect (actX p m U) (recTimeA p m U) (r + B * L) : ℝ) < (L : ℝ) / 8 := by
    by_contra hge
    exact hhigh2 (not_lt.mp hge)
  have htime : recTimeA p m U (r + B * L) - recTimeA p m U r ≤ T * L := by
    have hle : recTimeA p m U (r + B * L) ≤ recTimeA p m U r + T * L := Nat.le_of_not_gt hlag
    omega
  exact hno (LagForce.goodTime_of_quarterGood hτ
    (quarterGood_of_half_defect hτ hbase hend htime))

/-- **Pointwise three-term measure bound:** an exact decomposition with no band
restriction and no normalized-defect input. -/
theorem measure_restricted_pointwise_le_three (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m B T r L : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) :
    (arrayMeasure N) {U : Array N |
        defect (actX p m U) (recTimeA p m U) r ≤ (L : ℤ) ∧
          ¬ ∃ n : ℕ, GoodTime (actX p m U) (recTimeA p m U) B T r L n} ≤
      (arrayMeasure N) (defectHigh (N := N) p m r L) +
        (arrayMeasure N) (defectHigh (N := N) p m (r + B * L) L) +
          (arrayMeasure N) (timeLag (N := N) p m B T r L) := by
  calc (arrayMeasure N) {U : Array N |
        defect (actX p m U) (recTimeA p m U) r ≤ (L : ℤ) ∧
          ¬ ∃ n : ℕ, GoodTime (actX p m U) (recTimeA p m U) B T r L n}
      ≤ (arrayMeasure N) (defectHigh (N := N) p m r L ∪
          defectHigh (N := N) p m (r + B * L) L ∪ timeLag (N := N) p m B T r L) :=
        measure_mono_ae (restrictedAe_subset_three (N := N) hp0 hp1 hm hN)
    _ ≤ (arrayMeasure N) (defectHigh (N := N) p m r L) +
          (arrayMeasure N) (defectHigh (N := N) p m (r + B * L) L) +
            (arrayMeasure N) (timeLag (N := N) p m B T r L) := by
        refine (measure_union_le _ _).trans ?_
        exact add_le_add (measure_union_le _ _) (le_refl _)

/-- The same bound stated at the level of the full restricted profile: for every
`r ≥ C₀*L` the carrier-restricted mass is controlled by the three single-level
tails at that `r`.  In particular the profile requires a *uniform-in-`r`* bound
on those three tails; the band argument of `RestrictedGoodTimeBand` supplies them
only while `r ≲ L`. -/
theorem measure_profile_le_three (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m B T C₀ r L : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) (hC₀ : C₀ * L ≤ r) :
    (arrayMeasure N) {U : Array N |
        defect (actX p m U) (recTimeA p m U) r ≤ (L : ℤ) ∧
          ¬ ∃ n : ℕ, GoodTime (actX p m U) (recTimeA p m U) B T r L n} ≤
      (arrayMeasure N) (defectHigh (N := N) p m r L) +
        (arrayMeasure N) (defectHigh (N := N) p m (r + B * L) L) +
          (arrayMeasure N) (timeLag (N := N) p m B T r L) :=
  measure_restricted_pointwise_le_three (N := N) hp0 hp1 hm hN

end Decomposition

/-! ## 2. The far tail is exactly the supremum of the band masses over `K` -/

section Actual

variable {N : ℕ} [Nonempty (Fin N)]

/-- The band events at scale `L` are monotone in the band ratio `K`. -/
theorem restrictedBandNoGood_mono {p : ℝ} {m B T C₀ L K K' : ℕ} (h : K ≤ K') :
    RestrictedGoodTimeBand.restrictedBandNoGood (N := N) p m B T C₀ K L ⊆
      RestrictedGoodTimeBand.restrictedBandNoGood (N := N) p m B T C₀ K' L := by
  intro U hU
  obtain ⟨r, hrC, hrK, hbase, hno⟩ := hU
  exact ⟨r, hrC, hrK.trans (Nat.mul_le_mul_right L h), hbase, hno⟩

/-- **Exact far-tail identity.**  For `L ≥ 1` the full restricted no-`GoodTime`
event is the union over all band ratios `K` of the band events.  Hence the far
tail `K*L < r` is not an additional event that some further argument removes: it
is exactly the part of the full event not covered by any fixed band. -/
theorem restrictedNoGood_eq_iUnion_band {p : ℝ} (m B T C₀ L : ℕ) (hL : 1 ≤ L) :
    RestrictedGoodTimeBand.restrictedNoGood (N := N) p m B T C₀ L =
      ⋃ K : ℕ, RestrictedGoodTimeBand.restrictedBandNoGood (N := N) p m B T C₀ K L := by
  ext U
  constructor
  · rintro ⟨r, hrC, hbase, hno⟩
    refine Set.mem_iUnion.2 ⟨r + C₀, ?_⟩
    refine ⟨r, hrC, ?_, hbase, hno⟩
    calc r ≤ r + C₀ := Nat.le_add_right r C₀
      _ ≤ (r + C₀) * L := Nat.le_mul_of_pos_right (r + C₀) (by omega)
  · intro h
    obtain ⟨K, hK⟩ := Set.mem_iUnion.1 h
    obtain ⟨r, hrC, _hrK, hbase, hno⟩ := hK
    exact ⟨r, hrC, hbase, hno⟩

/-- **Exact measure form.**  The restricted mass is the supremum, over the band
ratio, of the band masses.  In particular a bound on the band mass at each *fixed*
`K` cannot bound the restricted mass: by `exists_band_mass_close` one single `K`
already carries essentially the whole mass. -/
theorem measure_restrictedNoGood_eq_iSup_band {p : ℝ} (m B T C₀ L : ℕ) (hL : 1 ≤ L) :
    (arrayMeasure N) (RestrictedGoodTimeBand.restrictedNoGood (N := N) p m B T C₀ L) =
      ⨆ K : ℕ, (arrayMeasure N)
        (RestrictedGoodTimeBand.restrictedBandNoGood (N := N) p m B T C₀ K L) := by
  rw [restrictedNoGood_eq_iUnion_band (N := N) (p := p) m B T C₀ L hL]
  exact Monotone.measure_iUnion
    (fun K K' hKK' => restrictedBandNoGood_mono (N := N) (p := p) (m := m) (B := B)
      (T := T) (C₀ := C₀) (L := L) hKK')

/-- For every threshold strictly below the restricted mass there is a *single*
finite band ratio whose band mass already exceeds it. -/
theorem exists_band_mass_close {p : ℝ} (m B T C₀ L : ℕ) (hL : 1 ≤ L)
    {a : ℝ≥0∞}
    (ha : a < (arrayMeasure N) (RestrictedGoodTimeBand.restrictedNoGood (N := N) p m B T C₀ L)) :
    ∃ K : ℕ, a < (arrayMeasure N)
      (RestrictedGoodTimeBand.restrictedBandNoGood (N := N) p m B T C₀ K L) := by
  rw [measure_restrictedNoGood_eq_iSup_band (N := N) (p := p) m B T C₀ L hL] at ha
  exact lt_iSup_iff.1 ha

end Actual

/-! ## 3. Explicit-rate band bound at fixed constants -/

section Rate

variable {N : ℕ} [Nonempty (Fin N)]

/-- The explicit exceptional set for the one-walker speed lower bound from
threshold `N₀`: some walker is strictly below `(κ/2) n` at some `n ≥ N₀`. -/
def speedBad (p : ℝ) (m : ℕ) (κ : ℝ) (N₀ : ℕ) : Set (Array N) :=
  {U | ∃ n : ℕ, N₀ ≤ n ∧ ∃ i : Fin N, (actX p m U i n : ℝ) < (κ / 2) * (n : ℝ)}

/-- The explicit absolute-scale defect window on which the band engine can fail:
some `s` in the band window `[C₀*L, (K+B)*L]` has defect at least `L/8`. -/
def defectWindow (p : ℝ) (m C₀ B K L : ℕ) : Set (Array N) :=
  {U | ∃ s : ℕ, C₀ * L ≤ s ∧ s ≤ (K + B) * L ∧
    (L : ℝ) / 8 ≤ (defect (actX p m U) (recTimeA p m U) s : ℝ)}

theorem measurableSet_speedBad (p : ℝ) (m : ℕ) (κ : ℝ) (N₀ : ℕ) :
    MeasurableSet (speedBad (N := N) p m κ N₀) := by
  have hset : speedBad (N := N) p m κ N₀ =
      ⋃ n ∈ Set.Ici N₀, ⋃ i : Fin N,
        {U : Array N | (actX p m U i n : ℝ) < (κ / 2) * (n : ℝ)} := by
    ext U
    simp only [speedBad, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_Ici, exists_prop]
  rw [hset]
  refine MeasurableSet.biUnion (Set.to_countable _) (fun n _ => ?_)
  exact MeasurableSet.iUnion (fun i => measurableSet_lt
    (Measurable.comp (by measurability : Measurable fun z : ℤ => (z : ℝ))
      (measurable_actX p m i n)) measurable_const)

/-- The restricted band event is almost surely contained in the explicit
exceptional sets: the speed set plus the absolute defect window.  No
normalized-defect convergence is used anywhere. -/
theorem bandQuarterBad_ae_subset (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) {κ : ℝ} (hκ : 0 < κ)
    {B C₀ K N₀ L : ℕ} (hB : 1 ≤ B) (hN₀L : N₀ ≤ L) :
    ∀ᵐ U ∂(arrayMeasure N),
      U ∈ RestrictedGoodTimeBand.bandQuarterBad (N := N) p m B
          (RestrictedGoodTimeBand.bandTime κ B K) C₀ K L →
        U ∈ speedBad (N := N) p m κ N₀ ∪ defectWindow (N := N) p m C₀ B K L := by
  filter_upwards [ae_isRecord_recTimeA (N := N) hp0 hp1 hm hN] with U hτ hband
  obtain ⟨r, hrC, hrK, hbad⟩ := hband
  by_contra hcon
  rw [Set.mem_union, not_or] at hcon
  obtain ⟨hspeed, hwin⟩ := hcon
  have hspd : ∀ n : ℕ, N₀ ≤ n → (κ / 2) * (n : ℝ) ≤ (actX p m U (Classical.arbitrary (Fin N)) n : ℝ) := by
    intro n hn
    by_contra hlt
    exact hspeed ⟨n, hn, Classical.arbitrary (Fin N), not_le.mp hlt⟩
  have hdef : ∀ s : ℕ, C₀ * L ≤ s → s ≤ (K + B) * L →
      (defect (actX p m U) (recTimeA p m U) s : ℝ) < (L : ℝ) / 8 := by
    intro s hs1 hs2
    by_contra hge
    exact hwin ⟨s, hs1, hs2, not_lt.mp hge⟩
  exact hbad (quarterGood_of_abs_defect hτ hκ hspd hB hN₀L hdef r hrC hrK)

/-- **Explicit-rate band bound.**  The restricted band mass is at most the mass
of the speed exception plus the mass of the absolute-scale defect window.  The
first term does not depend on `L`, `C₀` or `K`. -/
theorem measure_bandQuarterBad_le (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) {κ : ℝ} (hκ : 0 < κ)
    {B C₀ K N₀ L : ℕ} (hB : 1 ≤ B) (hN₀L : N₀ ≤ L) :
    (arrayMeasure N) (RestrictedGoodTimeBand.bandQuarterBad (N := N) p m B
        (RestrictedGoodTimeBand.bandTime κ B K) C₀ K L) ≤
      (arrayMeasure N) (speedBad (N := N) p m κ N₀) +
        (arrayMeasure N) (defectWindow (N := N) p m C₀ B K L) := by
  calc (arrayMeasure N) (RestrictedGoodTimeBand.bandQuarterBad (N := N) p m B
        (RestrictedGoodTimeBand.bandTime κ B K) C₀ K L)
      ≤ (arrayMeasure N) (speedBad (N := N) p m κ N₀ ∪
          defectWindow (N := N) p m C₀ B K L) :=
        measure_mono_ae (bandQuarterBad_ae_subset (N := N) hp0 hp1 hm hN hκ hB hN₀L)
    _ ≤ (arrayMeasure N) (speedBad (N := N) p m κ N₀) +
          (arrayMeasure N) (defectWindow (N := N) p m C₀ B K L) := measure_union_le _ _

/-- The speed exception mass tends to zero in its threshold. -/
theorem tendsto_measure_speedBad {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) {κ : ℝ} (hκ : 0 < κ)
    (hspeedAll : ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N, ∀ᶠ n : ℕ in atTop,
      (κ / 2) * (n : ℝ) ≤ (actX p m U i n : ℝ)) :
    Tendsto (fun N₀ : ℕ => (arrayMeasure N) (speedBad (N := N) p m κ N₀))
      atTop (𝓝 0) := by
  letI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hlim : ∀ᵐ U ∂(arrayMeasure N), ∀ᶠ N₀ : ℕ in atTop,
      (U ∈ speedBad (N := N) p m κ N₀ ↔ U ∈ (∅ : Set (Array N))) := by
    filter_upwards [hspeedAll] with U hU
    choose N₁ hN₁ using fun i : Fin N => eventually_atTop.1 (hU i)
    filter_upwards [eventually_ge_atTop (Finset.univ.sup N₁)] with N₀ hN₀
    refine ⟨fun h => ?_, fun h => absurd h (Set.notMem_empty U)⟩
    obtain ⟨n, hn, i, hlt⟩ := h
    exact absurd (hN₁ i n ((Finset.le_sup (Finset.mem_univ i)).trans (hN₀.trans hn)))
      (not_le.2 hlt)
  simpa only [measure_empty] using
    (tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
      (μ := arrayMeasure N) atTop MeasurableSet.empty
      (fun N₀ => measurableSet_speedBad p m κ N₀) hlim)

/-- **Uniform split of the band mass.**  For every `δ > 0` there is a single
threshold `N₀` such that for every band ratio, lower band edge and level
`L ≥ N₀` the band mass is at most `δ` plus one absolute-scale defect-window
mass.  This is the explicit-rate replacement for the unquantified `Tendsto`
statement of `RestrictedGoodTimeBand`. -/
theorem exists_uniform_band_split (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) {κ : ℝ} (hκ : 0 < κ)
    (hspeedAll : ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N, ∀ᶠ n : ℕ in atTop,
      (κ / 2) * (n : ℝ) ≤ (actX p m U i n : ℝ))
    {B : ℕ} (hB : 1 ≤ B) :
    ∀ δ : ℝ≥0∞, 0 < δ → ∃ N₀ : ℕ, ∀ (C₀ K L : ℕ), N₀ ≤ L →
      (arrayMeasure N) (RestrictedGoodTimeBand.bandQuarterBad (N := N) p m B
          (RestrictedGoodTimeBand.bandTime κ B K) C₀ K L) ≤
        δ + (arrayMeasure N) (defectWindow (N := N) p m C₀ B K L) := by
  intro δ hδ
  obtain ⟨N₀, hN₀⟩ := ENNReal.tendsto_atTop_zero.1
    (tendsto_measure_speedBad (N := N) hp0 hp1 hm hN hκ hspeedAll) δ hδ
  refine ⟨N₀, fun C₀ K L hNL => ?_⟩
  have hbound := measure_bandQuarterBad_le (N := N) hp0 hp1 hm hN hκ
    (B := B) (C₀ := C₀) (K := K) (N₀ := N₀) (L := L) hB hNL
  have hspeedle : (arrayMeasure N) (speedBad (N := N) p m κ N₀) ≤ δ := hN₀ N₀ le_rfl
  calc (arrayMeasure N) (RestrictedGoodTimeBand.bandQuarterBad (N := N) p m B
        (RestrictedGoodTimeBand.bandTime κ B K) C₀ K L)
      ≤ (arrayMeasure N) (speedBad (N := N) p m κ N₀) +
          (arrayMeasure N) (defectWindow (N := N) p m C₀ B K L) := hbound
    _ ≤ δ + (arrayMeasure N) (defectWindow (N := N) p m C₀ B K L) :=
        add_le_add hspeedle le_rfl

/-- **Cubic band term from a cubic defect window.**  If the speed bound holds
from `N₀` on almost surely and the absolute defect window is cubically dominated
in `L`, then the restricted band mass is cubically dominated — the exact rate
shape required by the `SourceTightAvail` clauses.  The far tail is *not* included. -/
theorem bandQuarterBad_cubic_of_defectWindow_cubic (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) {κ : ℝ} (hκ : 0 < κ)
    {B C₀ K N₀ : ℕ} (hB : 1 ≤ B)
    (hspeed : ∀ᵐ U ∂(arrayMeasure N), ∀ n : ℕ, N₀ ≤ n → ∀ i : Fin N,
      (κ / 2) * (n : ℝ) ≤ (actX p m U i n : ℝ))
    {K₁ : ℝ} (hK₁ : 0 ≤ K₁)
    (hwin : ∀ L : ℕ, N₀ ≤ L →
      (arrayMeasure N) (defectWindow (N := N) p m C₀ B K L) ≤
        ENNReal.ofReal (K₁ * (((L : ℝ) + 1))⁻¹ ^ 3)) :
    ∀ L : ℕ, N₀ ≤ L →
      (arrayMeasure N) (RestrictedGoodTimeBand.bandQuarterBad (N := N) p m B
          (RestrictedGoodTimeBand.bandTime κ B K) C₀ K L) ≤
        ENNReal.ofReal (K₁ * (((L : ℝ) + 1))⁻¹ ^ 3) := by
  intro L hNL
  have hsub : speedBad (N := N) p m κ N₀ ⊆
      {U : Array N | ¬ ∀ n : ℕ, N₀ ≤ n → ∀ i : Fin N,
        (κ / 2) * (n : ℝ) ≤ (actX p m U i n : ℝ)} := by
    intro U hU h
    obtain ⟨n, hn, i, hlt⟩ := hU
    exact absurd (h n hn i) (not_le.2 hlt)
  have hnull : (arrayMeasure N) (speedBad (N := N) p m κ N₀) = 0 :=
    measure_mono_null hsub (by rwa [ae_iff] at hspeed)
  calc (arrayMeasure N) (RestrictedGoodTimeBand.bandQuarterBad (N := N) p m B
        (RestrictedGoodTimeBand.bandTime κ B K) C₀ K L)
      ≤ (arrayMeasure N) (speedBad (N := N) p m κ N₀) +
          (arrayMeasure N) (defectWindow (N := N) p m C₀ B K L) :=
        measure_bandQuarterBad_le (N := N) hp0 hp1 hm hN hκ hB hNL
    _ = (arrayMeasure N) (defectWindow (N := N) p m C₀ B K L) := by rw [hnull, zero_add]
    _ ≤ ENNReal.ofReal (K₁ * (((L : ℝ) + 1))⁻¹ ^ 3) := hwin L hNL

/-- The band events are almost surely contained in the `QuarterGood` failure
event: `QuarterGood` produces a genuine `GoodTime` by
`LagForce.goodTime_of_quarterGood`. -/
theorem restrictedBandNoGood_le_bandQuarterBad (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m B T C₀ K L : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) :
    (arrayMeasure N) (RestrictedGoodTimeBand.restrictedBandNoGood (N := N) p m B T C₀ K L) ≤
      (arrayMeasure N) (RestrictedGoodTimeBand.bandQuarterBad (N := N) p m B T C₀ K L) := by
  refine measure_mono_ae ?_
  filter_upwards [ae_isRecord_recTimeA (N := N) hp0 hp1 hm hN] with U hτ h
  obtain ⟨r, hrC, hrK, _hbase, hno⟩ := h
  exact ⟨r, hrC, hrK, fun hq => hno (LagForce.goodTime_of_quarterGood hτ hq)⟩

/-- **Quantitative restricted ledger.**  The complete restricted no-`GoodTime`
mass at level `L` is bounded by a uniform speed exception, one absolute-scale
defect window, and the literal far-tail mass.  Both the speed exception and the
window are explicit; the far tail is kept visible and is not absorbed. -/
theorem measure_restrictedNoGood_le_add_window_far (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) {κ : ℝ} (hκ : 0 < κ)
    {B C₀ K N₀ L : ℕ} (hB : 1 ≤ B) (hN₀L : N₀ ≤ L) (hCK : C₀ ≤ K) :
    (arrayMeasure N) (RestrictedGoodTimeBand.restrictedNoGood (N := N) p m B
        (RestrictedGoodTimeBand.bandTime κ B K) C₀ L) ≤
      (arrayMeasure N) (speedBad (N := N) p m κ N₀) +
        (arrayMeasure N) (defectWindow (N := N) p m C₀ B K L) +
          (arrayMeasure N) (RestrictedGoodTimeBand.restrictedFarNoGood (N := N) p m B
            (RestrictedGoodTimeBand.bandTime κ B K) C₀ K L) := by
  have hsplit := RestrictedGoodTimeBand.measure_restrictedNoGood_le_band_add_far
    (N := N) p m B (RestrictedGoodTimeBand.bandTime κ B K) C₀ K L hCK
  have hband := restrictedBandNoGood_le_bandQuarterBad (N := N) hp0 hp1 (m := m) (B := B)
    (T := RestrictedGoodTimeBand.bandTime κ B K) (C₀ := C₀) (K := K) (L := L) hm hN
  have hrate := measure_bandQuarterBad_le (N := N) hp0 hp1 hm hN hκ
    (B := B) (C₀ := C₀) (K := K) (N₀ := N₀) (L := L) hB hN₀L
  have hrate' : (arrayMeasure N) (RestrictedGoodTimeBand.restrictedBandNoGood (N := N) p m B
        (RestrictedGoodTimeBand.bandTime κ B K) C₀ K L) ≤
      (arrayMeasure N) (speedBad (N := N) p m κ N₀) +
        (arrayMeasure N) (defectWindow (N := N) p m C₀ B K L) := hband.trans hrate
  calc (arrayMeasure N) (RestrictedGoodTimeBand.restrictedNoGood (N := N) p m B
        (RestrictedGoodTimeBand.bandTime κ B K) C₀ L)
      ≤ (arrayMeasure N) (RestrictedGoodTimeBand.restrictedBandNoGood (N := N) p m B
            (RestrictedGoodTimeBand.bandTime κ B K) C₀ K L) +
          (arrayMeasure N) (RestrictedGoodTimeBand.restrictedFarNoGood (N := N) p m B
            (RestrictedGoodTimeBand.bandTime κ B K) C₀ K L) := hsplit
    _ ≤ ((arrayMeasure N) (speedBad (N := N) p m κ N₀) +
          (arrayMeasure N) (defectWindow (N := N) p m C₀ B K L)) +
          (arrayMeasure N) (RestrictedGoodTimeBand.restrictedFarNoGood (N := N) p m B
            (RestrictedGoodTimeBand.bandTime κ B K) C₀ K L) :=
        add_le_add hrate' (le_refl _)

end Rate

/-! ## 4. Rotation to the literal `SourceTightAvail` clauses -/

section SourceClauses

variable {N : ℕ} [Nonempty (Fin N)]

/-- **The source advance clause from three single-level tail profiles.**  This is
the exact rotation of the frontier: no band, no normalized defect, no speed
bound, and no carrier-restricted `GoodTime` profile is assumed.  The three
inputs are the defect tails at the two block endpoints (threshold `ℓ/8`) and the
record-advance tail, each *uniform in the starting level* `r ≥ C₀*ℓ`. -/
theorem advanceClauseAt_of_three_tails (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) (B T C₀ : ℕ) (hC₀ : B + T + 1 ≤ C₀)
    (q₁ q₂ q₃ : ℕ → ℝ≥0∞)
    (h₁ : ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ r : ℕ, C₀ * ℓ ≤ r →
      (arrayMeasure N) (defectHigh (N := N) p m r ℓ) ≤ q₁ ℓ)
    (h₂ : ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ r : ℕ, C₀ * ℓ ≤ r →
      (arrayMeasure N) (defectHigh (N := N) p m (r + B * ℓ) ℓ) ≤ q₂ ℓ)
    (h₃ : ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ r : ℕ, C₀ * ℓ ≤ r →
      (arrayMeasure N) (timeLag (N := N) p m B T r ℓ) ≤ q₃ ℓ) :
    SourceTightAvail.AdvanceClauseAt (N := N) p m B T C₀ (q₁ + q₂ + q₃) := by
  refine BaseCarrier.advanceClauseAt_of_restricted_goodTime_profile (N := N) hp0 hp1 hm hN
    B T C₀ hC₀ (q₁ + q₂ + q₃) ?_
  intro ℓ hℓ r hr
  have hthree := measure_restricted_pointwise_le_three (N := N) hp0 hp1
    (m := m) (B := B) (T := T) (r := r) (L := ℓ) hm hN
  have hsum : (arrayMeasure N) (defectHigh (N := N) p m r ℓ) +
        (arrayMeasure N) (defectHigh (N := N) p m (r + B * ℓ) ℓ) +
          (arrayMeasure N) (timeLag (N := N) p m B T r ℓ) ≤
      q₁ ℓ + q₂ ℓ + q₃ ℓ :=
    add_le_add (add_le_add (h₁ ℓ hℓ r hr) (h₂ ℓ hℓ r hr)) (h₃ ℓ hℓ r hr)
  exact hthree.trans (by simpa only [Pi.add_apply] using hsum)

/-- **The source halving clause from the same three single-level tails.** -/
theorem halfClauseAt_of_three_tails (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) (B T C₀ : ℕ) (hC₀ : B + T + 1 ≤ C₀)
    (q₁ q₂ q₃ : ℕ → ℝ≥0∞)
    (h₁ : ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ r : ℕ, C₀ * ℓ ≤ r →
      (arrayMeasure N) (defectHigh (N := N) p m r ℓ) ≤ q₁ ℓ)
    (h₂ : ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ r : ℕ, C₀ * ℓ ≤ r →
      (arrayMeasure N) (defectHigh (N := N) p m (r + B * ℓ) ℓ) ≤ q₂ ℓ)
    (h₃ : ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ r : ℕ, C₀ * ℓ ≤ r →
      (arrayMeasure N) (timeLag (N := N) p m B T r ℓ) ≤ q₃ ℓ) :
    SourceTightAvail.HalfClauseAt (N := N) p m B C₀ (q₁ + q₂ + q₃) := by
  refine BaseCarrier.halfClauseAt_of_restricted_goodTime_profile (N := N) hp0 hp1 hm hN
    B T C₀ hC₀ (q₁ + q₂ + q₃) ?_
  intro ℓ hℓ r hr
  have hthree := measure_restricted_pointwise_le_three (N := N) hp0 hp1
    (m := m) (B := B) (T := T) (r := r) (L := ℓ) hm hN
  have hsum : (arrayMeasure N) (defectHigh (N := N) p m r ℓ) +
        (arrayMeasure N) (defectHigh (N := N) p m (r + B * ℓ) ℓ) +
          (arrayMeasure N) (timeLag (N := N) p m B T r ℓ) ≤
      q₁ ℓ + q₂ ℓ + q₃ ℓ :=
    add_le_add (add_le_add (h₁ ℓ hℓ r hr) (h₂ ℓ hℓ r hr)) (h₃ ℓ hℓ r hr)
  exact hthree.trans (by simpa only [Pi.add_apply] using hsum)

/-- The sum of three cubically dominated profiles is cubically dominated, with
the summed constant.  This is the exact majorant shape consumed by
`SourceTightAvail.record_tightness_of_block_clauses_at`. -/
theorem cubic_add_three {q₁ q₂ q₃ : ℕ → ℝ≥0∞} {K₁ K₂ K₃ : ℝ}
    (h₁ : 0 ≤ K₁) (h₂ : 0 ≤ K₂) (h₃ : 0 ≤ K₃)
    (hq₁ : ∀ ℓ : ℕ, q₁ ℓ ≤ ENNReal.ofReal (K₁ * (((ℓ : ℝ) + 1))⁻¹ ^ 3))
    (hq₂ : ∀ ℓ : ℕ, q₂ ℓ ≤ ENNReal.ofReal (K₂ * (((ℓ : ℝ) + 1))⁻¹ ^ 3))
    (hq₃ : ∀ ℓ : ℕ, q₃ ℓ ≤ ENNReal.ofReal (K₃ * (((ℓ : ℝ) + 1))⁻¹ ^ 3)) :
    ∀ ℓ : ℕ, (q₁ + q₂ + q₃) ℓ ≤
      ENNReal.ofReal ((K₁ + K₂ + K₃) * (((ℓ : ℝ) + 1))⁻¹ ^ 3) := by
  intro ℓ
  have hsum : ENNReal.ofReal (K₁ * (((ℓ : ℝ) + 1))⁻¹ ^ 3) +
        ENNReal.ofReal (K₂ * (((ℓ : ℝ) + 1))⁻¹ ^ 3) +
          ENNReal.ofReal (K₃ * (((ℓ : ℝ) + 1))⁻¹ ^ 3) =
      ENNReal.ofReal ((K₁ + K₂ + K₃) * (((ℓ : ℝ) + 1))⁻¹ ^ 3) := by
    have h₁' : (0 : ℝ) ≤ K₁ * (((ℓ : ℝ) + 1))⁻¹ ^ 3 :=
      mul_nonneg h₁ (by positivity)
    have h₂' : (0 : ℝ) ≤ K₂ * (((ℓ : ℝ) + 1))⁻¹ ^ 3 :=
      mul_nonneg h₂ (by positivity)
    have h₃' : (0 : ℝ) ≤ K₃ * (((ℓ : ℝ) + 1))⁻¹ ^ 3 :=
      mul_nonneg h₃ (by positivity)
    rw [← ENNReal.ofReal_add h₁' h₂', ← ENNReal.ofReal_add (by linarith) h₃']
    congr 1
    ring
  calc (q₁ + q₂ + q₃) ℓ = q₁ ℓ + q₂ ℓ + q₃ ℓ := rfl
    _ ≤ ENNReal.ofReal (K₁ * (((ℓ : ℝ) + 1))⁻¹ ^ 3) +
          ENNReal.ofReal (K₂ * (((ℓ : ℝ) + 1))⁻¹ ^ 3) +
            ENNReal.ofReal (K₃ * (((ℓ : ℝ) + 1))⁻¹ ^ 3) :=
        add_le_add (add_le_add (hq₁ ℓ) (hq₂ ℓ)) (hq₃ ℓ)
    _ = ENNReal.ofReal ((K₁ + K₂ + K₃) * (((ℓ : ℝ) + 1))⁻¹ ^ 3) := hsum

end SourceClauses

end QuantitativeRestrictedBand
