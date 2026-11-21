import Swarm.BlkMeasure
import Swarm.NeutralTwoInputCapstone
import Swarm.RawInitialPathLaw

open MeasureTheory Set
open Swarming.Uniform SwarmRestart SwarmFresh
open RawInitialPathLaw RawStrictTransport SwarmRawTimeStrictSum
open scoped ENNReal

set_option autoImplicit false

namespace Swarming.Diameter

variable {p : ℝ} {m N : ℕ}

theorem ae_first_regeneration_finite [Nonempty (Fin N)]
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N) :
    ∀ᵐ U ∂arrayMeasure N, RegenPath.D (posPath p m U) ≠ ⊤ := by
  have htight := M4Blk.dT_tight p m hp₀ hp₁ hm N hN
  filter_upwards [SwarmDTR.ae_exists_strictAttempt_of_dT_tight hp₀ hp₁ hm hN htight] with U hU
  obtain ⟨r, hr⟩ := hU
  exact (SwarmActualHfull.raw_D_ne_top_iff_exists_isRegen (posPath p m U)
    (SwarmFresh.posPath_zero p m U) (SwarmFresh.posPath_step p m U)).mpr
    ⟨_, (r + 1 : ℕ), by exact_mod_cast Nat.succ_pos r, (M1Bridge.isRegen_posPath_iff _ _ _ _ _).mpr hr⟩

/-- The path translated at the first regeneration has the law of the original
path conditioned on strict positivity. -/
theorem map_firstFutureZ_eq [Nonempty (Fin N)]
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N) :
    (arrayMeasure N).map (firstFutureZ p m) =
      (SwarmFB.seedCond (p := p) (m := m) (N := N)).map (posPath p m) := by
  let C := ⋃ q : LevelTime, rawFirstCell (N := N) p m q Set.univ
  have hC : ∀ᵐ U ∂arrayMeasure N, U ∈ C := by
    simpa only [C, iUnion_rawFirstCell_univ p m (by omega : 0 < N), Set.mem_ofPred_eq] using
      ae_first_regeneration_finite (N := N) hp₀ hp₁ hm hN
  have hCmeas : MeasurableSet C :=
    MeasurableSet.iUnion fun q => measurableSet_rawFirstCell p m q MeasurableSet.univ
  have hCmass : arrayMeasure N C = 1 := (mem_ae_iff_prob_eq_one hCmeas).mp hC
  have hV := SwarmSeed.strictPos_measure_ne_zero hp₀ hp₁ hm hN
  have h := restrict_rawCompleted_map_firstFutureZ p m N (by omega) hV (measure_ne_top _ _)
  change ((arrayMeasure N).restrict C).map (firstFutureZ p m) =
    (arrayMeasure N) C • normalizedStrictLaw p m N at h
  rwa [Measure.restrict_eq_self_of_ae_mem hC, hCmass, one_smul,
    normalizedStrictLaw_eq_seedCond_map] at h

/-- At the first regeneration, sum the path factorization over all cells with
the prescribed level or time. The index `j` selects that coordinate. -/
theorem real_prob_first_regeneration_factor {μ : Measure (Array N)} [IsProbabilityMeasure μ]
    (hN : 0 < N) (hD : ∀ᵐ U ∂μ, RegenPath.D (posPath p m U) ≠ ⊤)
    (j : LevelTime → ℕ) (S : Array N → ℕ)
    (hS : ∀ q U, U ∈ rawFirstCell p m q Set.univ → S U = j q)
    (A : ℕ → Set (RegenPath.Path N))
    (hA : ∀ u, MeasurableSet (A u))
    (hrel : ∀ q U, U ∈ rawFirstCell p m q Set.univ → ∀ u,
      relFuture p m U q.1.2 (q.1.1 : ℤ) ∈ A u ↔ posPath p m U ∈ A (j q + u))
    (t u : ℕ) (c : ℝ≥0∞)
    (hcell : ∀ q : LevelTime, μ (rawFirstCell p m q (A u)) =
      μ (rawFirstCell p m q Set.univ) * c) :
    μ.real {U | S U = t ∧ posPath p m U ∈ A (t + u)} =
      μ.real {U | S U = t} * c.toReal := by
  let I := {q : LevelTime // j q = t}
  let B (q : I) := rawFirstCell (N := N) p m q.1 Set.univ
  let C (q : I) := rawFirstCell p m q.1 (A u)
  have hB : {U | S U = t} =ᵐ[μ] ⋃ q, B q := by
    filter_upwards [hD] with U hU
    apply propext
    change S U = t ↔ U ∈ ⋃ q, B q
    constructor
    · intro ht
      obtain ⟨d, v, hd, hD', hv⟩ := (D_ne_top_iff_exists_firstBlock _).mp hU
      let q : LevelTime := ⟨(d, v), hd⟩
      have hq := (rawFirstCell_univ_iff_D_tau p m q hN U).mpr ⟨hD', hv⟩
      exact Set.mem_iUnion.mpr ⟨⟨q, (hS q U hq).symm.trans ht⟩, hq⟩
    · intro ht
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp ht
      exact (hS q.1 U hq).trans q.2
  have hC : {U | S U = t ∧ posPath p m U ∈ A (t + u)} =ᵐ[μ] ⋃ q, C q := by
    filter_upwards [hB] with U hU
    apply propext
    change (S U = t ∧ posPath p m U ∈ A (t + u)) ↔ U ∈ ⋃ q, C q
    constructor
    · rintro ⟨ht, hu⟩
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp ((Iff.of_eq hU).mp ht)
      have hq' := (mem_rawFirstCell p m q.1 Set.univ U).mp hq
      have h := (hrel q.1 U hq u).mpr (by rwa [q.2])
      exact Set.mem_iUnion.mpr ⟨q, (mem_rawFirstCell p m q.1 (A u) U).mpr ⟨hq'.1, hq'.2.1, h⟩⟩
    · intro hh
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hh
      have hq' := (mem_rawFirstCell p m q.1 (A u) U).mp hq
      have hqu := (mem_rawFirstCell p m q.1 Set.univ U).mpr ⟨hq'.1, hq'.2.1, Set.mem_univ _⟩
      exact ⟨(hS q.1 U hqu).trans q.2, by simpa only [q.2] using (hrel q.1 U hqu u).mp hq'.2.2⟩
  have hdB : Pairwise fun x y => Disjoint (B x) (B y) := fun _ _ hne =>
    pairwise_disjoint_rawFirstCell p m Set.univ hN (fun he => hne (Subtype.ext he))
  have hdC : Pairwise fun x y => Disjoint (C x) (C y) := fun _ _ hne =>
    pairwise_disjoint_rawFirstCell p m (A u) hN (fun he => hne (Subtype.ext he))
  rw [measureReal_congr hB, measureReal_congr hC, measureReal_def, measureReal_def,
    measure_iUnion hdB (fun q => measurableSet_rawFirstCell p m q.1 MeasurableSet.univ),
    measure_iUnion hdC (fun q => measurableSet_rawFirstCell p m q.1 (hA u))]
  have hf (q : I) : μ (C q) = μ (B q) * c := hcell q.1
  simp only [hf, ENNReal.tsum_mul_right, ENNReal.toReal_mul]

private theorem rawFirstCell_inter_seed (q : LevelTime) (hN : 0 < N)
    (B : Set (ℕ → Fin N → ℤ)) :
    SwarmFB.seedSet (p := p) (m := m) (N := N) ∩ rawFirstCell p m q B =
      FirstBlockFuture p m q B := by
  ext U
  have h : U ∈ rawFirstCell (N := N) p m q B ↔
      U ∈ rawFirstCell p m q Set.univ ∧ relFuture p m U q.1.2 (q.1.1 : ℤ) ∈ B := by
    rw [mem_rawFirstCell p m q B U, mem_rawFirstCell p m q Set.univ U]
    simp only [Set.mem_univ, and_true, and_assoc]
  rw [Set.mem_inter_iff, h, rawFirstCell_univ_iff_D_tau p m q hN U,
    FirstBlockFuture, Set.mem_ofPred_eq, SwarmFB.seedSet, Set.mem_ofPred_eq]
  exact and_congr_right (fun _ => and_assoc)

theorem seedCond_firstCell_factor (hN : 0 < N)
    (hV : arrayMeasure N (SwarmFB.seedSet (p := p) (m := m) (N := N)) ≠ 0)
    (q : LevelTime) {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    SwarmFB.seedCond (p := p) (m := m) (N := N) (rawFirstCell p m q B) =
      SwarmFB.seedCond (p := p) (m := m) (N := N) (rawFirstCell p m q Set.univ) *
        normalizedStrictLaw p m N B := by
  let ν := SwarmFB.seedCond (p := p) (m := m) (N := N)
  let _ : IsProbabilityMeasure ν := SwarmFB.seedCond_isProbabilityMeasure hV
  have hf (A : Set (ℕ → Fin N → ℤ)) (hA : MeasurableSet A) :
      ν (rawFirstCell p m q A) =
        firstBlockLowMass (N := N) p m q * normalizedStrictLaw p m N A := by
    change SwarmFB.seedCond (p := p) (m := m) (N := N) (rawFirstCell p m q A) = _
    rw [SwarmFB.seedCond_apply SwarmFB.measurableSet_seedSet, rawFirstCell_inter_seed q hN,
      FirstBlockFuture, SwarmRawTimeStrict.array_firstBlock_future_mass p m q.1.1 q.1.2 q.2 hA,
      normalizedStrictLaw_apply p m N hA]
    exact mul_left_comm _ _ _
  have hu := hf Set.univ MeasurableSet.univ
  rw [normalizedStrictLaw_eq_seedCond_map, Measure.map_apply (measurable_posPath p m N)
    MeasurableSet.univ, Set.preimage_univ, measure_univ, mul_one] at hu
  change ν (rawFirstCell p m q B) = ν (rawFirstCell p m q Set.univ) * _
  rw [hf B hB, hu]

theorem firstRegeneration_eq_selected_zero (hN : 0 < N) {U : Array N}
    (hU : U ∈ SwarmSelInd.Achain p m N 1 Set.univ) :
    firstLevel p m U = NeutralRegen.selectedD p m N 0 U ∧
      firstTime p m U = NeutralRegen.selectedT p m N 0 U := by
  let _ : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  have hU' : U ∈ ⋃ L : Fin 1 → ℕ × ℕ, SwarmFB.Atom (p := p) (m := m) (N := N) L := by
    rwa [SwarmFB.iUnion_atom_eq]
  obtain ⟨L, hL⟩ := Set.mem_iUnion.mp hU'
  have hZ : SwarmFB.Z (p := p) (m := m) (N := N) 0 U = L 0 := by
    simpa using SwarmFB.Z_eq_of_mem_atom (p := p) (m := m) (N := N) hN L hL 0
  have hlist : SwarmFB.idxList L = [((L 0).1, SwarmFB.blkLevel (L 0))] := by
    simp [SwarmFB.idxList, List.ofFn_succ]
  rw [SwarmFB.Atom, hlist, SwarmSelInd.AchainIdx] at hL
  have hfr := (SwarmSelInd.mem_Hidx_cons.mp hL).2.1
  have hfr' : posPath p m U ∈ SwarmSel.firstRegen (L 0).1 (((L 0).2 + 1 : ℕ) : ℤ) := by
    simpa [SwarmFB.blkLevel, Nat.cast_add, Nat.cast_one] using hfr
  have hlevel := BlockLevelKac.firstRegenLevel_eq_of_firstRegen (posPath p m U)
    (SwarmFresh.posPath_zero p m U) (SwarmFresh.posPath_step p m U)
    (t := (L 0).1) (d := (L 0).2 + 1) (by omega) hfr'
  have hrec := (SwarmSel.mem_firstRegen_iff.mp hfr').2.1
  have htau : RegenPath.tau (posPath p m U) (((L 0).2 + 1 : ℕ) : ℤ) =
      ((L 0).1 : ℕ∞) := RegenPath.tau_eq_iff.mpr
    ⟨⟨⟨0, hN⟩, hrec.2 _⟩, fun n hn i => ne_of_lt (hrec.1 n hn i)⟩
  constructor
  · unfold firstLevel NeutralRegen.selectedD
    rw [hlevel, hZ]
  · rw [NeutralRegen.selectedT_eq_raw hN p m 0 hU, hZ]
    unfold firstTime firstTau firstLevel
    rw [hlevel, htau]
    simp

theorem seedCond_first_regeneration_one_pos (hN : 0 < N)
    (hV : arrayMeasure N (SwarmFB.seedSet (p := p) (m := m) (N := N)) ≠ 0) :
    0 < (SwarmFB.seedCond (p := p) (m := m) (N := N)).real {U | firstLevel p m U = 1 ∧ firstTime p m U = 1} := by
  let ν := SwarmFB.seedCond (p := p) (m := m) (N := N)
  let _ : IsProbabilityMeasure ν := SwarmFB.seedCond_isProbabilityMeasure hV
  let q : LevelTime := ⟨(1, 1), by omega⟩
  have hC : SwarmFB.seedSet (p := p) (m := m) (N := N) ⊆
      {U | RegenPath.Cdt (posPath p m U) 1 1} := by
    intro U hU
    have hpos : posPath p m U ∈ strictPos := hU
    have hone (i : Fin N) : posPath p m U 1 i = 1 := by
      have hs := SwarmFresh.posPath_step p m U 0 i
      rw [SwarmFresh.posPath_zero p m U i, sub_zero] at hs
      rwa [abs_of_pos (hpos.2 0 i)] at hs
    refine ⟨RegenPath.tau_eq_iff.mpr ⟨⟨⟨0, hN⟩, hone _⟩, ?_⟩, hone, ?_, ?_⟩
    · intro n hn i
      have hn' : n = 0 := by omega
      simp [hn', SwarmFresh.posPath_zero p m U i]
    · intro n hn ht i
      have hn' : n = 1 := by omega
      rw [hn', hone]
      decide
    · intro e he he'
      omega
  have hlow : 0 < firstBlockLowMass (N := N) p m q :=
    (pos_iff_ne_zero.mpr hV).trans_le (measure_mono hC)
  have hcell : ν (rawFirstCell p m q Set.univ) = firstBlockLowMass (N := N) p m q := by
    change SwarmFB.seedCond (p := p) (m := m) (N := N) (rawFirstCell p m q Set.univ) = _
    rw [SwarmFB.seedCond_apply SwarmFB.measurableSet_seedSet, rawFirstCell_inter_seed q hN,
      FirstBlockFuture, SwarmRawTimeStrict.array_firstBlock_future_mass p m q.1.1 q.1.2 q.2
        MeasurableSet.univ]
    simp only [Set.inter_univ]
    change _⁻¹ * (firstBlockLowMass (N := N) p m q *
      arrayMeasure N (SwarmFB.seedSet (p := p) (m := m) (N := N))) = _
    rw [mul_left_comm, ENNReal.inv_mul_cancel hV (measure_ne_top _ _), mul_one]
  have hsub : rawFirstCell (N := N) p m q Set.univ ⊆ {U | firstLevel p m U = 1 ∧ firstTime p m U = 1} :=
    fun _ hU => ⟨firstLevel_eq_of_rawFirstCell p m q hN hU,
      firstTime_eq_of_rawFirstCell p m q hN hU⟩
  have hp : 0 < ν {U | firstLevel p m U = 1 ∧ firstTime p m U = 1} :=
    (hcell.symm ▸ hlow).trans_le (measure_mono hsub)
  exact ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)

end Swarming.Diameter
