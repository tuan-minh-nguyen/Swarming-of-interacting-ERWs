/-
# Actual restricted `GoodTime` decay on bounded-ratio bands

The actual speed and normalized-defect limits give `QuarterGood` simultaneously
at every `C₀*L ≤ r ≤ K*L`, once `L` is large, for an explicit fixed record-time
allowance `bandTime κ B K`.  Consequently the actual-array restricted
no-`GoodTime` event on that band has measure tending to zero.

This is deliberately not the `SourceTightAvail` profile: that interface also
quantifies over the far tail `K*L < r`, uniformly in `K`, and requires a
quantitative summable rate.  The final set identity isolates exactly that
unresolved tail.  No auxiliary `BadTime` estimate, occupation onset, invariant
measure, or source theorem is assumed.
-/
import Swarm.FixedBlocks
import Mathlib.MeasureTheory.Integral.Indicator
import Swarm.LagForce

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped ENNReal BigOperators

open RecordDefect RecordoSupply HblkTwo HblkFinal FluidBlock
open Swarming Swarming.Uniform SwarmRecordMeas SwarmRecordMeas.Actual

namespace RestrictedGoodTimeBand

/-- A fixed record-time allowance for all levels in the ratio band `r ≤ K*L`.
The additive `2` absorbs the one-walker speed threshold for large `L`. -/
noncomputable def bandTime (κ : ℝ) (B K : ℕ) : ℕ :=
  ⌈2 * ((K : ℝ) + (B : ℝ)) / κ⌉₊ + 2

section Pathwise

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {X : ι → ℕ → ℤ} {τ : ℕ → ℕ}

/-- On one genuine record path, speed and `d_s/s → 0` give quarter-good blocks
simultaneously throughout every fixed bounded-ratio band.  The eventual lower
bound on `L` may depend on the path, so this is not a uniform rate. -/
theorem eventually_quarterGood_band (hτ : IsRecord X τ)
    {i : ι} {κ : ℝ} (hκ : 0 < κ) {N₀ : ℕ}
    (hspd : ∀ n : ℕ, N₀ ≤ n → (κ / 2) * (n : ℝ) ≤ (X i n : ℝ))
    (hdlim : Tendsto (fun s : ℕ => (defect X τ s : ℝ) / (s : ℝ)) atTop (𝓝 0))
    {B C₀ K : ℕ} (hB : 1 ≤ B) (hC₀ : 1 ≤ C₀) (hCK : C₀ ≤ K) :
    ∀ᶠ L : ℕ in atTop, ∀ r : ℕ, C₀ * L ≤ r → r ≤ K * L →
      LagForce.QuarterGood X τ B (bandTime κ B K) r L := by
  let T : ℕ := bandTime κ B K
  let γ : ℝ := 2 * ((K : ℝ) + (B : ℝ)) / κ
  let ε : ℝ := 1 / (8 * ((K : ℝ) + (B : ℝ)))
  have hKBnat : 0 < K + B := by omega
  have hKB : (0 : ℝ) < (K : ℝ) + (B : ℝ) := by exact_mod_cast hKBnat
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hγT : γ + 1 ≤ (T : ℝ) := by
    have hceil : γ ≤ ((⌈γ⌉₊ : ℕ) : ℝ) := Nat.le_ceil γ
    dsimp [T, bandTime, γ]
    push_cast
    linarith
  have hεKB : ε * ((K : ℝ) + (B : ℝ)) = 1 / 8 := by
    dsimp [ε]
    field_simp [ne_of_gt hKB]
  have hdefEv : ∀ᶠ s : ℕ in atTop, (defect X τ s : ℝ) / (s : ℝ) < ε :=
    (tendsto_order.1 hdlim).2 ε hε
  obtain ⟨S, hS⟩ := eventually_atTop.1 hdefEv
  filter_upwards [eventually_ge_atTop (max N₀ (max S 1))] with L hL
  have hLN₀ : N₀ ≤ L := (le_max_left N₀ (max S 1)).trans hL
  have hLS : S ≤ L := (le_max_left S 1).trans ((le_max_right N₀ (max S 1)).trans hL)
  have hL1 : 1 ≤ L := (le_max_right S 1).trans ((le_max_right N₀ (max S 1)).trans hL)
  have hLC : L ≤ C₀ * L := by
    calc
      L = 1 * L := (one_mul L).symm
      _ ≤ C₀ * L := Nat.mul_le_mul_right L hC₀
  intro r hrC hrK
  have hr1 : 1 ≤ r := hL1.trans (hLC.trans hrC)
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
  have hrS : S ≤ r := hLS.trans (hLC.trans hrC)
  have heS : S ≤ r + B * L := hrS.trans (Nat.le_add_right r (B * L))
  have hepos : (0 : ℝ) < ((r + B * L : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ r + B * L)
  have hrUpper : (r : ℝ) ≤ (K : ℝ) * (L : ℝ) := by exact_mod_cast hrK
  have hrUpperWide : (r : ℝ) ≤ ((K : ℝ) + (B : ℝ)) * (L : ℝ) := by
    calc
      (r : ℝ) ≤ (K : ℝ) * (L : ℝ) := hrUpper
      _ ≤ ((K : ℝ) + (B : ℝ)) * (L : ℝ) := by
        have hK : (K : ℝ) ≤ (K : ℝ) + (B : ℝ) := by
          linarith [Nat.cast_nonneg (α := ℝ) B]
        exact mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg (α := ℝ) L)
  have heUpper : ((r + B * L : ℕ) : ℝ) ≤ ((K : ℝ) + (B : ℝ)) * (L : ℝ) := by
    calc
      ((r + B * L : ℕ) : ℝ) = (r : ℝ) + (B : ℝ) * (L : ℝ) := by push_cast; ring
      _ ≤ (K : ℝ) * (L : ℝ) + (B : ℝ) * (L : ℝ) := add_le_add hrUpper (le_refl _)
      _ = ((K : ℝ) + (B : ℝ)) * (L : ℝ) := by ring
  have hbound : ∀ s : ℕ, S ≤ s → 0 < (s : ℝ) →
      (s : ℝ) ≤ ((K : ℝ) + (B : ℝ)) * (L : ℝ) →
      (defect X τ s : ℝ) < (L : ℝ) / 8 := by
    intro s hSs hspos hsUpper
    have hs := hS s hSs
    rw [div_lt_iff₀ hspos] at hs
    calc
      (defect X τ s : ℝ) < ε * (s : ℝ) := hs
      _ ≤ ε * (((K : ℝ) + (B : ℝ)) * (L : ℝ)) :=
        mul_le_mul_of_nonneg_left hsUpper hε.le
      _ = (L : ℝ) / 8 := by rw [← mul_assoc, hεKB]; ring
  have hbaseR : (defect X τ r : ℝ) < (L : ℝ) / 8 := hbound r hrS hrpos hrUpperWide
  have hendR : (defect X τ (r + B * L) : ℝ) < (L : ℝ) / 8 :=
    hbound (r + B * L) heS hepos heUpper
  have hbase : defect X τ r ≤ (L : ℤ) := by
    have h : (defect X τ r : ℝ) ≤ (L : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) L]
    exact_mod_cast h
  have hend : 4 * defect X τ (r + B * L) ≤ (L : ℤ) := by
    have h : (4 : ℝ) * (defect X τ (r + B * L) : ℝ) ≤ (L : ℝ) := by
      linarith [Nat.cast_nonneg (α := ℝ) L]
    exact_mod_cast h
  have hmono : τ r ≤ τ (r + B * L) := tau_mono hτ (Nat.le_add_right r (B * L))
  have htau := SwarmM4C.FixedConst.tau_le_threshold hτ hκ hspd (r + B * L)
  have htauUpper : (τ (r + B * L) : ℝ) ≤ (N₀ : ℝ) + γ * (L : ℝ) := by
    calc
      (τ (r + B * L) : ℝ) ≤ (N₀ : ℝ) + (2 / κ) * ((r + B * L : ℕ) : ℝ) := htau
      _ ≤ (N₀ : ℝ) + (2 / κ) * (((K : ℝ) + (B : ℝ)) * (L : ℝ)) := by
        exact add_le_add (le_refl ((N₀ : ℝ)))
          (mul_le_mul_of_nonneg_left heUpper (show (0 : ℝ) ≤ 2 / κ by positivity))
      _ = (N₀ : ℝ) + γ * (L : ℝ) := by dsimp [γ]; ring
  have htime : τ (r + B * L) - τ r ≤ T * L := by
    have htimeR : ((τ (r + B * L) - τ r : ℕ) : ℝ) ≤ ((T * L : ℕ) : ℝ) := by
      rw [show ((τ (r + B * L) - τ r : ℕ) : ℝ) =
          (τ (r + B * L) : ℝ) - (τ r : ℝ) by push_cast [hmono]; ring]
      rw [show ((T * L : ℕ) : ℝ) = (T : ℝ) * (L : ℝ) by push_cast; ring]
      have hN₀R : (N₀ : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLN₀
      have hmul := mul_le_mul_of_nonneg_right hγT (Nat.cast_nonneg (α := ℝ) L)
      calc
        (τ (r + B * L) : ℝ) - (τ r : ℝ) ≤ (τ (r + B * L) : ℝ) := by
          linarith [Nat.cast_nonneg (α := ℝ) (τ r)]
        _ ≤ (N₀ : ℝ) + γ * (L : ℝ) := htauUpper
        _ ≤ (L : ℝ) + γ * (L : ℝ) := add_le_add hN₀R (le_refl _)
        _ = (γ + 1) * (L : ℝ) := by ring
        _ ≤ (T : ℝ) * (L : ℝ) := hmul
    exact_mod_cast htimeR
  exact ⟨hbase, htime, hend⟩

end Pathwise

section Actual

variable {N : ℕ} [Nonempty (Fin N)]

/-- The measurable band on which at least one `QuarterGood` clause fails. -/
def bandQuarterBad (p : ℝ) (m B T C₀ K L : ℕ) : Set (Array N) :=
  {U | ∃ r : ℕ, C₀ * L ≤ r ∧ r ≤ K * L ∧
    ¬ LagForce.QuarterGood (actX p m U) (recTimeA p m U) B T r L}

/-- Restricted no-good-time event on the same bounded-ratio band. -/
def restrictedBandNoGood (p : ℝ) (m B T C₀ K L : ℕ) : Set (Array N) :=
  {U | ∃ r : ℕ, C₀ * L ≤ r ∧ r ≤ K * L ∧
    defect (actX p m U) (recTimeA p m U) r ≤ (L : ℤ) ∧
    ¬ ∃ n : ℕ, GoodTime (actX p m U) (recTimeA p m U) B T r L n}

/-- The complete restricted source-domain no-good-time event. -/
def restrictedNoGood (p : ℝ) (m B T C₀ L : ℕ) : Set (Array N) :=
  {U | ∃ r : ℕ, C₀ * L ≤ r ∧
    defect (actX p m U) (recTimeA p m U) r ≤ (L : ℤ) ∧
    ¬ ∃ n : ℕ, GoodTime (actX p m U) (recTimeA p m U) B T r L n}

/-- The part of the complete source-domain event beyond the proved band. -/
def restrictedFarNoGood (p : ℝ) (m B T C₀ K L : ℕ) : Set (Array N) :=
  {U | ∃ r : ℕ, K * L < r ∧
    defect (actX p m U) (recTimeA p m U) r ≤ (L : ℤ) ∧
    ¬ ∃ n : ℕ, GoodTime (actX p m U) (recTimeA p m U) B T r L n}

/-- Fixed-index `QuarterGood` is measurable with the canonical total record
clock, including its non-chain fallback. -/
theorem measurableSet_quarterGood (p : ℝ) (m B T r L : ℕ) :
    MeasurableSet {U : Array N |
      LagForce.QuarterGood (actX p m U) (recTimeA p m U) B T r L} := by
  have hset : {U : Array N |
      LagForce.QuarterGood (actX p m U) (recTimeA p m U) B T r L} =
      ({U : Array N | defect (actX p m U) (recTimeA p m U) r ≤ (L : ℤ)} ∩
        {U : Array N | recTimeA p m U (r + B * L) ≤ recTimeA p m U r + T * L}) ∩
      {U : Array N | 4 * defect (actX p m U) (recTimeA p m U) (r + B * L) ≤ (L : ℤ)} := by
    ext U
    simp only [LagForce.QuarterGood, Set.mem_ofPred_eq, Set.mem_inter_iff]
    rw [Nat.sub_le_iff_le_add]
    omega
  rw [hset]
  exact ((measurableSet_le (measurable_defectA p m r) measurable_const).inter
    (measurableSet_le (measurable_recTimeA p m (r + B * L))
      ((measurable_recTimeA p m r).add_const (T * L)))).inter
    (measurableSet_le ((measurable_defectA p m (r + B * L)).const_mul 4) measurable_const)

/-- The countable union of band failures is measurable. -/
theorem measurableSet_bandQuarterBad (p : ℝ) (m B T C₀ K L : ℕ) :
    MeasurableSet (bandQuarterBad (N := N) p m B T C₀ K L) := by
  have hset : bandQuarterBad (N := N) p m B T C₀ K L = ⋃ r : ℕ,
      {U : Array N | C₀ * L ≤ r ∧ r ≤ K * L ∧
        ¬ LagForce.QuarterGood (actX p m U) (recTimeA p m U) B T r L} := by
    ext U
    simp only [bandQuarterBad, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [hset]
  apply MeasurableSet.iUnion
  intro r
  by_cases hrC : C₀ * L ≤ r
  · by_cases hrK : r ≤ K * L
    · simp only [hrC, hrK, true_and]
      exact (measurableSet_quarterGood (N := N) p m B T r L).compl
    · simp [hrK]
  · simp [hrC]

/-- The actual array's quarter-good failure mass vanishes on every fixed band.
No assertion is made about its rate or about the far tail. -/
theorem exists_tendsto_bandQuarterBad {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N)
    {B C₀ K : ℕ} (hB : 1 ≤ B) (hC₀ : 1 ≤ C₀) (hCK : C₀ ≤ K) :
    ∃ κ : ℝ, 0 < κ ∧ Tendsto (fun L : ℕ => (arrayMeasure N)
      (bandQuarterBad (N := N) p m B (bandTime κ B K) C₀ K L)) atTop (𝓝 0) := by
  letI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  obtain ⟨κ, hκ, hspeedAll⟩ := RecordoSupply.speed_actual hp0 hp1 hm
  refine ⟨κ, hκ, ?_⟩
  have hrec := ae_isRecord_recTimeA (N := N) hp0 hp1 hm hN
  have hdiam := M7Block.diam_actual_recordo (N := N) hp0 hp1 hm hN
  have hband : ∀ᵐ U ∂(arrayMeasure N), ∀ᶠ L : ℕ in atTop,
      ∀ r : ℕ, C₀ * L ≤ r → r ≤ K * L →
        LagForce.QuarterGood (actX p m U) (recTimeA p m U) B (bandTime κ B K) r L := by
    filter_upwards [hspeedAll N hN, hrec, hdiam] with U hspd hτ hd
    let i : Fin N := Classical.arbitrary (Fin N)
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hspd i)
    exact eventually_quarterGood_band hτ hκ hN₀
      (RecordoSupply.defect_div_tendsto_zero_of_speed hτ (actX_step p m U)
        (actX_zero p m U) hκ (hspd i) hd) hB hC₀ hCK
  have hlim : ∀ᵐ U ∂(arrayMeasure N), ∀ᶠ L : ℕ in atTop,
      U ∈ bandQuarterBad (N := N) p m B (bandTime κ B K) C₀ K L ↔
        U ∈ (∅ : Set (Array N)) := by
    filter_upwards [hband] with U hU
    filter_upwards [hU] with L hL
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨r, hrC, hrK, hbad⟩
    exact hbad (hL r hrC hrK)
  simpa only [measure_empty] using
    (tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
      (μ := arrayMeasure N) atTop MeasurableSet.empty
      (fun L => measurableSet_bandQuarterBad (N := N) p m B (bandTime κ B K) C₀ K L) hlim)

/-- Consequently the literal restricted no-`GoodTime` mass also vanishes on
each fixed band.  This uses only `QuarterGood → ∃ GoodTime` on canonical
record paths; off that a.e. set the total fallback needs no separate estimate. -/
theorem exists_tendsto_restrictedBandNoGood {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N)
    {B C₀ K : ℕ} (hB : 1 ≤ B) (hC₀ : 1 ≤ C₀) (hCK : C₀ ≤ K) :
    ∃ κ : ℝ, 0 < κ ∧ Tendsto (fun L : ℕ => (arrayMeasure N)
      (restrictedBandNoGood (N := N) p m B (bandTime κ B K) C₀ K L)) atTop (𝓝 0) := by
  obtain ⟨κ, hκ, hzero⟩ := exists_tendsto_bandQuarterBad (N := N)
    hp0 hp1 hm hN hB hC₀ hCK
  refine ⟨κ, hκ, ?_⟩
  have hrec := ae_isRecord_recTimeA (N := N) hp0 hp1 hm hN
  have hle : ∀ L : ℕ, (arrayMeasure N)
      (restrictedBandNoGood (N := N) p m B (bandTime κ B K) C₀ K L) ≤
      (arrayMeasure N) (bandQuarterBad (N := N) p m B (bandTime κ B K) C₀ K L) := by
    intro L
    apply measure_mono_ae
    filter_upwards [hrec] with U hτ
    rintro ⟨r, hrC, hrK, _hbase, hno⟩
    refine ⟨r, hrC, hrK, ?_⟩
    intro hq
    exact hno (LagForce.goodTime_of_quarterGood hτ hq)
  rw [ENNReal.tendsto_atTop_zero] at hzero ⊢
  intro ε hε
  obtain ⟨R, hR⟩ := hzero ε hε
  exact ⟨R, fun L hL => (hle L).trans (hR L hL)⟩

/-- Splitting at `r = K*L` leaves precisely the far tail.  This identity uses
no probability or record hypothesis and makes explicit why band decay alone
does not discharge `BaseCarrier`'s full restricted-profile premise. -/
theorem restrictedNoGood_eq_band_union_far (p : ℝ) (m B T C₀ K L : ℕ)
    (hCK : C₀ ≤ K) :
    restrictedNoGood (N := N) p m B T C₀ L =
      restrictedBandNoGood (N := N) p m B T C₀ K L ∪
        restrictedFarNoGood (N := N) p m B T C₀ K L := by
  ext U
  constructor
  · rintro ⟨r, hrC, hbase, hno⟩
    by_cases hKr : K * L < r
    · exact Or.inr ⟨r, hKr, hbase, hno⟩
    · have hrK : r ≤ K * L := Nat.le_of_not_gt hKr
      exact Or.inl ⟨r, hrC, hrK, hbase, hno⟩
  · rintro (⟨r, hrC, hrK, hbase, hno⟩ | ⟨r, hKr, hbase, hno⟩)
    · exact ⟨r, hrC, hbase, hno⟩
    · have hrC : C₀ * L ≤ r :=
        (Nat.mul_le_mul_right L hCK).trans (Nat.le_of_lt hKr)
      exact ⟨r, hrC, hbase, hno⟩

/-- The corresponding quantitative ledger: after the proved band term, only
the far-tail mass remains.  Neither summability nor decay of that second term
is asserted. -/
theorem measure_restrictedNoGood_le_band_add_far (p : ℝ) (m B T C₀ K L : ℕ)
    (hCK : C₀ ≤ K) :
    (arrayMeasure N) (restrictedNoGood (N := N) p m B T C₀ L) ≤
      (arrayMeasure N) (restrictedBandNoGood (N := N) p m B T C₀ K L) +
        (arrayMeasure N) (restrictedFarNoGood (N := N) p m B T C₀ K L) := by
  rw [restrictedNoGood_eq_band_union_far (N := N) p m B T C₀ K L hCK]
  exact measure_union_le _ _

end Actual

end RestrictedGoodTimeBand
