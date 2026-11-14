/-
Strictly-positive path mass from diagonal finite windows.

Only the diagonal identity at strictness and pattern horizon `K` is used.  For a
fixed width-`n` cylinder, the limit is taken along horizons `n + j`; hence no
unrestricted mixed-horizon identity is asserted.
-/
import Swarm.GeneralRawWindow
import Swarm.HorizonWindow

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace SwarmPositiveHorizon

open SwarmFinHorizon SwarmPrefix SwarmFresh

variable {N : ℕ}

/-- Diagonal finite-window identities determine the mass of every measurable
set inside `strictPos`.  On finite cylinders one uses the cofinal sequence of
horizons `n + j`, where `n` is the cylinder width, and then the generating
`pathCyl` π-system.  The scalar hypotheses are exactly those needed to commute
multiplication with the decreasing limit. -/
theorem strictPos_inter_eq_of_diagonal
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Φ : Ω → (ℕ → Fin N → ℤ)) (hΦ : Measurable Φ)
    (ν : Measure (ℕ → Fin N → ℤ)) [IsProbabilityMeasure ν]
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (h : ∀ (K : ℕ) (C : Set (Fin (K + 1) → Fin N → ℤ)), MeasurableSet C →
      μ (Φ ⁻¹' (finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C)) =
        c * ν (finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C)) :
    ∀ B : Set (ℕ → Fin N → ℤ), MeasurableSet B →
      μ (Φ ⁻¹' (strictPos (N := N) ∩ B)) = c * ν (strictPos (N := N) ∩ B) := by
  have hcyl : ∀ (n : ℕ) (C : Set (Fin (n + 1) → Fin N → ℤ)), MeasurableSet C →
      μ (Φ ⁻¹' (strictPos (N := N) ∩ pathPat (N := N) n ⁻¹' C)) =
        c * ν (strictPos (N := N) ∩ pathPat (N := N) n ⁻¹' C) := by
    intro n C hC
    have hB : MeasurableSet (pathPat (N := N) n ⁻¹' C) :=
      hC.preimage (measurable_pathPat n)
    have hstep : ∀ j : ℕ,
        μ (Φ ⁻¹' (finStrict (N := N) (j + n) ∩ pathPat (N := N) n ⁻¹' C)) =
          c * ν (finStrict (N := N) (j + n) ∩ pathPat (N := N) n ⁻¹' C) := by
      intro j
      have hn : n ≤ j + n := by omega
      have hCn : MeasurableSet (restrictPat (N := N) hn ⁻¹' C) :=
        measurableSet_restrictPat_preimage hn hC
      have hh := h (j + n) (restrictPat (N := N) hn ⁻¹' C) hCn
      have heq : finStrict (N := N) (j + n) ∩
          pathPat (N := N) (j + n) ⁻¹' (restrictPat (N := N) hn ⁻¹' C) =
          finStrict (N := N) (j + n) ∩ pathPat (N := N) n ⁻¹' C :=
        inter_pathPat_prefix hn (finStrict (N := N) (j + n)) C
      rw [heq] at hh
      exact hh
    have hInter : (⋂ j : ℕ, (finStrict (N := N) (j + n) ∩
        pathPat (N := N) n ⁻¹' C)) = strictPos (N := N) ∩ pathPat (N := N) n ⁻¹' C := by
      rw [← Set.iInter_inter]
      congr 1
      ext X
      constructor
      · intro hX
        rw [Set.mem_iInter] at hX
        rw [mem_strictPos]
        refine ⟨(mem_finStrict.mp (hX 0)).1, ?_⟩
        intro t ht i
        exact (mem_finStrict.mp (hX t)).2 t ht (by omega) i
      · intro hX
        apply Set.mem_iInter.mpr
        intro j
        exact strictPos_subset_finStrict _ hX
    have hanti : Antitone (fun j : ℕ => finStrict (N := N) (j + n) ∩
        pathPat (N := N) n ⁻¹' C) := fun j k hjk =>
      Set.inter_subset_inter_left _ (finStrict_antitone (Nat.add_le_add_right hjk n))
    have hmeas : ∀ j : ℕ, MeasurableSet (finStrict (N := N) (j + n) ∩
        pathPat (N := N) n ⁻¹' C) := fun j => (measurableSet_finStrict _).inter hB
    have h1 : μ (Φ ⁻¹' (⋂ j : ℕ, (finStrict (N := N) (j + n) ∩
        pathPat (N := N) n ⁻¹' C))) = ⨅ j : ℕ,
          μ (Φ ⁻¹' (finStrict (N := N) (j + n) ∩ pathPat (N := N) n ⁻¹' C)) := by
      rw [Set.preimage_iInter]
      exact Antitone.measure_iInter
        (fun _ _ hjk => Set.preimage_mono (hanti hjk))
        (fun j => (hΦ (hmeas j)).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩
    have h2 : ν (⋂ j : ℕ, (finStrict (N := N) (j + n) ∩
        pathPat (N := N) n ⁻¹' C)) = ⨅ j : ℕ,
          ν (finStrict (N := N) (j + n) ∩ pathPat (N := N) n ⁻¹' C) :=
      Antitone.measure_iInter hanti (fun j => (hmeas j).nullMeasurableSet)
        ⟨0, measure_ne_top _ _⟩
    have h4 : c * (⨅ j : ℕ,
        ν (finStrict (N := N) (j + n) ∩ pathPat (N := N) n ⁻¹' C)) =
        ⨅ j : ℕ, c * ν (finStrict (N := N) (j + n) ∩ pathPat (N := N) n ⁻¹' C) :=
      ENNReal.mul_iInf_of_ne hc0 hct
    calc
      μ (Φ ⁻¹' (strictPos (N := N) ∩ pathPat (N := N) n ⁻¹' C)) =
          μ (Φ ⁻¹' (⋂ j : ℕ, (finStrict (N := N) (j + n) ∩
            pathPat (N := N) n ⁻¹' C))) := by rw [hInter]
      _ = ⨅ j : ℕ, μ (Φ ⁻¹' (finStrict (N := N) (j + n) ∩
            pathPat (N := N) n ⁻¹' C)) := h1
      _ = ⨅ j : ℕ, c * ν (finStrict (N := N) (j + n) ∩
            pathPat (N := N) n ⁻¹' C) := iInf_congr hstep
      _ = c * (⨅ j : ℕ, ν (finStrict (N := N) (j + n) ∩
            pathPat (N := N) n ⁻¹' C)) := h4.symm
      _ = c * ν (⋂ j : ℕ, (finStrict (N := N) (j + n) ∩
            pathPat (N := N) n ⁻¹' C)) := by rw [h2]
      _ = c * ν (strictPos (N := N) ∩ pathPat (N := N) n ⁻¹' C) := by rw [hInter]
  have hmeasures : (μ.map Φ).restrict (strictPos (N := N)) =
      (c • ν).restrict (strictPos (N := N)) := by
    refine ext_of_generate_finite (pathCyl N) generateFrom_pathCyl.symm
      isPiSystem_pathCyl ?_ ?_
    · intro s hs
      obtain ⟨n, C, hC, rfl⟩ := hs
      have hm : MeasurableSet (pathPat (N := N) n ⁻¹' C) :=
        hC.preimage (measurable_pathPat n)
      rw [Measure.restrict_apply hm, Measure.restrict_apply hm, Measure.smul_apply,
        Set.inter_comm (pathPat (N := N) n ⁻¹' C) (strictPos (N := N)),
        Measure.map_apply hΦ (measurableSet_strictPos.inter hm)]
      exact hcyl n C hC
    · rw [Measure.restrict_apply MeasurableSet.univ, Measure.restrict_apply MeasurableSet.univ,
        Measure.smul_apply, Set.univ_inter, Measure.map_apply hΦ measurableSet_strictPos]
      simpa using hcyl 0 Set.univ MeasurableSet.univ
  intro B hB
  have hh : ((μ.map Φ).restrict (strictPos (N := N))) B =
      ((c • ν).restrict (strictPos (N := N))) B := by rw [hmeasures]
  rw [Measure.restrict_apply hB, Measure.restrict_apply hB, Measure.smul_apply,
    Set.inter_comm B (strictPos (N := N)),
    Measure.map_apply hΦ (measurableSet_strictPos.inter hB)] at hh
  exact hh

/-- The actual arbitrary-initial-law chain satisfies the full `strictPos`
path-mass identity.  Only the proved diagonal raw-window theorem is consumed.
When `π(srSet) = 0`, the same diagonal at horizon zero makes both sides zero;
otherwise `strictPos_inter_eq_of_diagonal` applies. -/
theorem chainLaw_strictPos_inter_eq {m : ℕ}
    (p : ℝ) (hm : 1 ≤ m) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π] :
    ∀ B : Set (ℕ → Fin N → ℤ), MeasurableSet B →
      SwarmChainAssemble.chainLaw
          (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp0.le hp1.le π)
          (SwarmFinFuture.chainPath ⁻¹' (strictPos (N := N) ∩ B)) =
        π (SwarmRec.srSet N m) * (Swarming.Uniform.arrayMeasure N) {U : Swarming.Uniform.Array N |
          SwarmRestart.posPath p m U ∈ strictPos (N := N) ∩ B} := by
  letI : IsProbabilityMeasure (Swarming.Uniform.arrayMeasure N) :=
    Swarming.Uniform.arrayMeasure_isProbabilityMeasure N
  letI : IsProbabilityMeasure
      (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp0.le hp1.le π) :=
    SwarmInfSeg.isProbabilityMeasure_infLaw p hm hp0.le hp1.le π
  letI : IsProbabilityMeasure
      ((Swarming.Uniform.arrayMeasure N).map (SwarmRestart.posPath p m)) :=
    Measure.isProbabilityMeasure_map (SwarmRestart.measurable_posPath p m N).aemeasurable
  by_cases hπ0 : π (SwarmRec.srSet N m) = 0
  · intro B hB
    have hbase := SwarmGeneralRawWindow.chainLaw_diagonal_window_eq_pi_srSet
      p hm hp0 hp1 π 0 Set.univ MeasurableSet.univ
    have hzero : SwarmChainAssemble.chainLaw
        (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp0.le hp1.le π)
        (SwarmFinFuture.chainPath ⁻¹' finStrict (N := N) 0) = 0 := by
      simpa [SwarmFinFuture.chainWindow, hπ0] using hbase
    rw [hπ0, zero_mul]
    apply le_antisymm ?_ (zero_le)
    calc
      _ ≤ SwarmChainAssemble.chainLaw
          (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp0.le hp1.le π)
          (SwarmFinFuture.chainPath ⁻¹' finStrict (N := N) 0) :=
        measure_mono (Set.preimage_mono (fun _ hX => strictPos_subset_finStrict 0 hX.1))
      _ = 0 := hzero
  · have hdiag : ∀ (K : ℕ) (C : Set (Fin (K + 1) → Fin N → ℤ)), MeasurableSet C →
        SwarmChainAssemble.chainLaw
            (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp0.le hp1.le π)
            (SwarmFinFuture.chainPath ⁻¹'
              (finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C)) =
          π (SwarmRec.srSet N m) *
            ((Swarming.Uniform.arrayMeasure N).map (SwarmRestart.posPath p m))
              (finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C) := by
      intro K C hC
      rw [Measure.map_apply (SwarmRestart.measurable_posPath p m N)
        ((measurableSet_finStrict K).inter (hC.preimage (measurable_pathPat K)))]
      exact SwarmGeneralRawWindow.chainLaw_diagonal_window_eq_pi_srSet
        p hm hp0 hp1 π K C hC
    have hh := strictPos_inter_eq_of_diagonal
      (μ := SwarmChainAssemble.chainLaw
        (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp0.le hp1.le π))
      (SwarmFinFuture.chainPath (N := N)) SwarmFinFuture.measurable_chainPath
      ((Swarming.Uniform.arrayMeasure N).map (SwarmRestart.posPath p m))
      (π (SwarmRec.srSet N m)) hπ0 (measure_ne_top _ _) hdiag
    intro B hB
    have h := hh B hB
    rw [Measure.map_apply (SwarmRestart.measurable_posPath p m N)
      (measurableSet_strictPos.inter hB)] at h
    exact h

/-- The genuine `hstruct` mass form for the actual enriched chain and an
arbitrary initial record probability.  This uses `chain_hstruct_iff` only to
rewrite `Chain.A` as the path's `strictPos` event; no finite-horizon family is
assumed. -/
theorem chainLaw_hstruct {m : ℕ}
    (p : ℝ) (hm : 1 ≤ m) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π] :
    ∀ B : Set (ℕ → Fin N → ℤ), MeasurableSet B →
      SwarmChainAssemble.chainLaw
          (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp0.le hp1.le π)
          (SwarmConcat.Chain.A ∩ SwarmFinFuture.chainPath ⁻¹' B) =
        π (SwarmRec.srSet N m) * (Swarming.Uniform.arrayMeasure N)
          {U : Swarming.Uniform.Array N |
            SwarmRestart.posPath p m U ∈ strictPos (N := N) ∩ B} := by
  refine (SwarmDHStruct.chain_hstruct_iff (N := N) (m := m) p π
    (SwarmChainAssemble.chainLaw
      (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp0.le hp1.le π))).2 ?_
  intro B hB
  change SwarmChainAssemble.chainLaw
      (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp0.le hp1.le π)
      (SwarmFinFuture.chainPath ⁻¹' (strictPos (N := N) ∩ B)) = _
  exact chainLaw_strictPos_inter_eq p hm hp0 hp1 π B hB

end SwarmPositiveHorizon
