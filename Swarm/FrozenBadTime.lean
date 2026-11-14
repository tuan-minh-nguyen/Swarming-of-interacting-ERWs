/-
  **The actual `BadTime`/`ActualExtra` crossing estimate.**

  This file preserves both parts of `BadTime`: its `enlFilt s`-measurable site event and its
  forward `hitBefore` event.  On any measurable `A` contained in the site event, the modified
  frozen walk of `FrozenSubset.lean` supplies the crossing estimate.  Here the raw and revealed
  window products are identified, `actualSite ∩ ActualExtra` is proved `enlFilt s`-measurable,
  and the actual forward crossing is included in the frozen `hitsBefore` event.
-/
import Swarm.FrozenSubset
import Swarm.BadBridge
import Swarm.EnlReveal
import Swarm.EnlFilt

open MeasureTheory Filter
open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Enl
open scoped ENNReal BigOperators Topology

namespace SwarmBad

noncomputable section

open SwarmSpeed SwarmDischarge SwarmSpeed.Frozen

variable {N : ℕ}

/-- On `badPos`, the raw and revealed environment potentials agree at natural levels. -/
theorem windowPotential_eq_revealed_nat {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ)
    {U : Array N} {i j : Fin N} (s b0 b1 : ℕ)
    (hbad : badPos p m U i j (b1 : ℤ) s) :
    R (windowWeight p m j U) b0 b1 = R (revealedWF p m j s U) b0 b1 := by
  unfold R
  apply Finset.prod_congr rfl
  intro x hx
  have hxb : (x : ℤ) ≤ (b1 : ℤ) := by
    exact_mod_cast (Finset.mem_Icc.mp hx).2
  simp only [rat, windowWeight, revealedWF]
  rw [revealedWeight_eq_omegaAt_of_badPos hp m hbad (Int.natCast_nonneg x) hxb]

/-- On the bad-site event, the raw `ActualExtra` event is enlarged-filtration measurable. -/
theorem measurableSet_actualSite_inter_actualExtra (p : ℝ) (m : ℕ) (hp : 1 / 2 ≤ p)
    (i j : Fin N) (c : ℝ) (k s : ℕ) :
    MeasurableSet[enlFilt (N := N) p m s]
      (actualSite p m i j k s ∩ ActualExtra p m j c k) := by
  have hsite : MeasurableSet[enlFilt (N := N) p m s] (actualSite p m i j k s) :=
    measurableSet_actualSite p m i j k s
  have hrev : Measurable[enlFilt (N := N) p m s]
      (fun U : Array N => R (revealedWF p m j s U) (lvlA k) (lvlB k)) :=
    measurable_R_diag (fun x => measurable_revealedWeight_enlFilt p m s j (x : ℤ))
      (lvlA k) (lvlB k)
  have hset : actualSite p m i j k s ∩ ActualExtra p m j c k =
      actualSite p m i j k s ∩
        {U : Array N | R (revealedWF p m j s U) (lvlA k) (lvlB k) ≤
          Real.exp (-(c * (lvlB k : ℝ)))} := by
    ext U
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, actualExtra_iff_R]
    constructor
    · rintro ⟨hs, hE⟩
      exact ⟨hs, by
        rw [← windowPotential_eq_revealed_nat hp m s (lvlA k) (lvlB k) hs]
        exact hE⟩
    · rintro ⟨hs, hE⟩
      exact ⟨hs, by
        rw [windowPotential_eq_revealed_nat hp m s (lvlA k) (lvlB k) hs]
        exact hE⟩
  rw [hset]
  exact hsite.inter (measurableSet_le hrev measurable_const)

/-- The actual forward bad crossing is contained in the frozen `hitsBefore` event on every
subset of the corresponding bad-position event.  The `hitBefore` witness is used, not discarded. -/
theorem badCross_inter_subset_frozen_hitsBefore (p : ℝ) (m : ℕ) (i j : Fin N)
    {k s : ℕ} {A : Set (Array N)}
    (hsub : A ⊆ {U : Array N | badPos p m U i j (lvlB k : ℤ) s}) (hk : 81 ≤ k) :
    badCross p m i k s ∩ A ⊆
      hitsBefore (shiftX (Xtil p m i (lvlA k) (lvlB k) s A) s)
        (lvlA k) (lvlB k + 1) ∩ A := by
  have hb : lvlA k < lvlB k := by
    have ha := lvlA_ge_one hk
    have hab := lvlA_le_lvlB k
    unfold lvlA at ha ⊢
    omega
  rintro U ⟨hCross, hA⟩
  have hbad : badPos p m U i j (lvlB k : ℤ) s := hsub hA
  rw [badCross_eq_hitsBefore i (lvlA_ge_one hk)] at hCross
  rcases hCross with ⟨n, hn, hprev⟩
  change ((trajectory p m U (s + n)).pos i).toNat = lvlA k at hn
  change ∀ k' < n, ((trajectory p m U (s + k')).pos i).toNat ≠ lvlB k + 1 at hprev
  by_cases hstop : exitAfterStart p m i (lvlA k) (lvlB k) s U ≤
      ((s + n : ℕ) : WithTop ℕ)
  · have hne : exitAfterStart p m i (lvlA k) (lvlB k) s U ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top hstop
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
    have hr' : exitAfterStart p m i (lvlA k) (lvlB k) s U = (r : WithTop ℕ) := hr.symm
    rw [hr'] at hstop
    have hsr : s ≤ r := by
      have h := exitAfterStart_le p m i (lvlA k) (lvlB k) s U
      rw [hr'] at h
      exact_mod_cast h
    have hrn : r ≤ s + n := by exact_mod_cast hstop
    have castTop : (((lvlB k : ℤ) + 1).toNat) = lvlB k + 1 := by
      rw [show (lvlB k : ℤ) + 1 = ((lvlB k + 1 : ℕ) : ℤ) by push_cast; ring]
      simp
    have hneTop : (trajectory p m U r).pos i ≠ (lvlB k : ℤ) + 1 := by
      by_cases hr_eq : r = s + n
      · subst r
        intro ht
        have hn' := hn
        rw [ht, castTop] at hn'
        have hab := lvlA_le_lvlB k
        omega
      · have hrlt : r < s + n := lt_of_le_of_ne hrn hr_eq
        intro ht
        have hprev' := hprev (r - s) (by omega)
        rw [Nat.add_sub_of_le hsr] at hprev'
        apply hprev'
        rw [ht, castTop]
    have hpos : (trajectory p m U r).pos i = (lvlA k : ℤ) := by
      rcases exit_eq_boundary p m i hb hbad.1 hr' with hbottom | htop
      · exact hbottom
      · exact False.elim (hneTop htop)
    refine ⟨⟨r - s, ?_, ?_⟩, hA⟩
    · change Xtil p m i (lvlA k) (lvlB k) s A (s + (r - s)) U = lvlA k
      rw [Nat.add_sub_of_le hsr, Xtil_of_mem hsr hA]
      have hz : zWalk p m i (lvlA k) (lvlB k) s r U = (trajectory p m U r).pos i := by
        calc
          zWalk p m i (lvlA k) (lvlB k) s r U =
              (trajectory p m U (exitAfterStart p m i (lvlA k) (lvlB k) s U).untopA).pos i :=
            stoppedProcess_eq_of_ge (by rw [hr']; exact le_rfl)
          _ = (trajectory p m U r).pos i :=
            congrArg (fun t : WithTop ℕ => (trajectory p m U t.untopA).pos i) hr'
      change (zWalk p m i (lvlA k) (lvlB k) s r U).toNat = lvlA k
      rw [hz, hpos]
      simp
    · intro k' hk'
      change Xtil p m i (lvlA k) (lvlB k) s A (s + k') U ≠ lvlB k + 1
      have hkr : s + k' < r := by omega
      have hkn : k' < n := by omega
      have hlt : ((s + k' : ℕ) : WithTop ℕ) <
          exitAfterStart p m i (lvlA k) (lvlB k) s U := by
        rw [hr']
        exact_mod_cast hkr
      have hcur := nWalk_current_of_not_stopped p m i
        (b0 := lvlA k) (b1 := lvlB k) (s := s) (n := s + k') (U := U) (by omega) hlt
      have heq : Xtil p m i (lvlA k) (lvlB k) s A (s + k') U =
          ((trajectory p m U (s + k')).pos i).toNat := by
        rw [Xtil_of_mem (A := A) (by omega) hA]
        simpa only [Int.toNat_natCast] using congrArg Int.toNat hcur
      rw [heq]
      exact hprev k' hkn
  · have heq {k' : ℕ} (hk' : k' ≤ n) :
        Xtil p m i (lvlA k) (lvlB k) s A (s + k') U =
          ((trajectory p m U (s + k')).pos i).toNat := by
      have hlt : ((s + k' : ℕ) : WithTop ℕ) <
          exitAfterStart p m i (lvlA k) (lvlB k) s U := by
        apply lt_of_not_ge
        intro hle
        exact hstop (hle.trans (by exact_mod_cast Nat.add_le_add_left hk' s))
      have hcur := nWalk_current_of_not_stopped p m i
        (b0 := lvlA k) (b1 := lvlB k) (s := s) (n := s + k') (U := U) (by omega) hlt
      rw [Xtil_of_mem (A := A) (by omega) hA]
      simpa only [Int.toNat_natCast] using congrArg Int.toNat hcur
    refine ⟨⟨n, ?_, ?_⟩, hA⟩
    · change Xtil p m i (lvlA k) (lvlB k) s A (s + n) U = lvlA k
      rw [heq (k' := n) le_rfl]
      exact hn
    · intro k' hk'
      change Xtil p m i (lvlA k) (lvlB k) s A (s + k') U ≠ lvlB k + 1
      rw [heq (k' := k') (by omega)]
      exact hprev k' hk'

/-- **The exact exponential bound on `BadTime ∩ ActualExtra`, without a crossing hypothesis.**
The threshold `81` ensures `1 ≤ lvlA k`; it is harmless for the eventual Borel--Cantelli
argument. -/
theorem badTime_actualExtra_crossing_bound {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    {m : ℕ} (i j : Fin N) (hij : i ≠ j) (c : ℝ) :
    ∀ k ≥ 81, ∀ s : ℕ,
      (arrayMeasure N) ({U : Array N | BadTime p m U i j k s} ∩ ActualExtra p m j c k) ≤
        ENNReal.ofReal (Real.exp (-(c * (lvlB k : ℝ)))) := by
  intro k hk s
  haveI hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hb : lvlA k < lvlB k := by
    have ha := lvlA_ge_one hk
    have hab := lvlA_le_lvlB k
    unfold lvlA at ha ⊢
    omega
  let A : Set (Array N) := actualSite p m i j k s ∩ ActualExtra p m j c k
  have hA : MeasurableSet[enlFilt (N := N) p m s] A :=
    measurableSet_actualSite_inter_actualExtra p m hp0.le i j c k s
  have hA0 : MeasurableSet A := (enlFilt (N := N) p m).le s _ hA
  have hsub : A ⊆ {U : Array N | badPos p m U i j (lvlB k : ℤ) s} := by
    intro U hU
    exact hU.1
  have hfrozen := subset_frozen_cross_prob_hitsBefore_le_R p m hp0 hp1 i j
    (A := A) hA hsub hb hij
  have hsubset := badCross_inter_subset_frozen_hitsBefore p m i j (A := A) hsub hk
  have hset : {U : Array N | BadTime p m U i j k s} ∩ ActualExtra p m j c k =
      badCross p m i k s ∩ A := by
    rw [badTime_eq i j k s]
    ext U
    simp only [Set.mem_inter_iff, A]
    tauto
  have hmono : (arrayMeasure N).real
      ({U : Array N | BadTime p m U i j k s} ∩ ActualExtra p m j c k) ≤
      (arrayMeasure N).real
        (hitsBefore (shiftX (Xtil p m i (lvlA k) (lvlB k) s A) s)
          (lvlA k) (lvlB k + 1) ∩ A) := by
    rw [hset]
    exact measureReal_mono hsubset
  have hrawint : IntegrableOn
      (fun U => R (windowWeight p m j U) (lvlA k) (lvlB k)) A (arrayMeasure N) := by
    refine Integrable.integrableOn (Integrable.of_bound
      (measurable_windowPotential p m j (lvlA k) (lvlB k)).aestronglyMeasurable 1 ?_)
    filter_upwards with U
    rw [Real.norm_eq_abs,
      abs_of_nonneg (windowPotential_bounds hp0.le hp1 j (lvlA k) (lvlB k) U).1]
    exact (windowPotential_bounds hp0.le hp1 j (lvlA k) (lvlB k) U).2
  have hrawpoint : ∀ᵐ U ∂(arrayMeasure N), U ∈ A →
      R (windowWeight p m j U) (lvlA k) (lvlB k) ≤ Real.exp (-(c * (lvlB k : ℝ))) := by
    refine Filter.Eventually.of_forall (fun U hU => ?_)
    have hE := hU.2
    rw [actualExtra_iff_R] at hE
    exact hE
  have hint : ∫ U in A, R (windowWeight p m j U) (lvlA k) (lvlB k) ∂(arrayMeasure N) ≤
      Real.exp (-(c * (lvlB k : ℝ))) * (arrayMeasure N).real A :=
    setIntegral_le_mul_real_of_le_on hA0 (Real.exp_pos _).le hrawint hrawpoint
  have hEq : ∫ U in A, R (revealedWF p m j s U) (lvlA k) (lvlB k) ∂(arrayMeasure N) =
      ∫ U in A, R (windowWeight p m j U) (lvlA k) (lvlB k) ∂(arrayMeasure N) := by
    refine setIntegral_congr_fun hA0 (fun U hU => ?_)
    exact (windowPotential_eq_revealed_nat hp0.le m s (lvlA k) (lvlB k) (hsub hU)).symm
  have hAone : (arrayMeasure N).real A ≤ 1 := by
    calc (arrayMeasure N).real A ≤ (arrayMeasure N).real Set.univ := measureReal_mono (Set.subset_univ _)
      _ = 1 := by rw [measureReal_def, measure_univ]; norm_num
  apply measure_le_ofReal_of_real_le
  calc
    (arrayMeasure N).real ({U : Array N | BadTime p m U i j k s} ∩ ActualExtra p m j c k) ≤
        (arrayMeasure N).real
          (hitsBefore (shiftX (Xtil p m i (lvlA k) (lvlB k) s A) s)
            (lvlA k) (lvlB k + 1) ∩ A) := hmono
    _ ≤ ∫ U in A, R (revealedWF p m j s U) (lvlA k) (lvlB k) ∂(arrayMeasure N) := hfrozen
    _ = ∫ U in A, R (windowWeight p m j U) (lvlA k) (lvlB k) ∂(arrayMeasure N) := hEq
    _ ≤ Real.exp (-(c * (lvlB k : ℝ))) * (arrayMeasure N).real A := hint
    _ ≤ Real.exp (-(c * (lvlB k : ℝ))) * 1 :=
      mul_le_mul_of_nonneg_left hAone (Real.exp_pos _).le
    _ = Real.exp (-(c * (lvlB k : ℝ))) := mul_one _

/-- **Transience of every actual walker distinct from the environment walker.**
The crossing premise of `ae_transience_of_actual_crossing_bound` is now discharged by
`badTime_actualExtra_crossing_bound`; the raw-array log-ratio strong law is supplied by that
consumer as before. -/
theorem ae_transience_actual {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (i j : Fin N) (hij : i ≠ j) :
    ∀ᵐ U ∂(arrayMeasure N), Tendsto (fun n => (trajectory p m U n).pos i) atTop atTop := by
  refine SwarmDischarge.ae_transience_of_actual_crossing_bound (N := N) (K := 81)
    hp0 hp1 hm i j ?_
  intro k hk s
  exact badTime_actualExtra_crossing_bound hp0 hp1 i j hij
    (SwarmLogRatio.paperC p ((1 - p) ^ (m - 1))) k hk s

end

end SwarmBad


