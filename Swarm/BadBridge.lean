/-
  **Bridge from the paper's `BadTime` to the crossing layer's own vocabulary.**

  * `hitsBeforeZ_eq_hitsBefore_toNat` -- `badCross` *is* the `SwarmSpeed.hitsBefore` event of
    `Swarm/Cross.lean` (which is `NN`-valued) evaluated on the natural-valued
    positions.  The only side condition is `1 <= a_k`, which holds for all `k >= 81`;
  * `lvlA_ge_one` -- that side condition, proved;
  * `setIntegral_le_of_condExp_le` / `condExp_le_of_forall_setIntegral_le` -- the exact
    equivalence between the "for every `F_s`-measurable test set" set-integral form and the
    a.e. `condExp` form.  The latter is literally the conclusion of
    `SwarmSpeed.condExp_cross_prob_shift_le_R`, so the crossing estimate can be supplied in
    whichever form an instantiation produces;
  * `ae_transience_of_hitsBefore_crossing` -- transience of the actual interacting trajectory
    from the crossing estimate written *entirely* in the crossing layer's notation
    (`hitsBefore` of the shifted walk, against `F_s`-measurable test sets).

  Nothing here asserts the crossing estimate itself.
-/
import Swarm.Imports
import Swarm.BadAssembly

open MeasureTheory Filter
open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Enl
open scoped ENNReal BigOperators Topology

namespace SwarmBad

noncomputable section

open SwarmSpeed SwarmDischarge

variable {N : ℕ}

/-! ### 1. `Z`-valued versus `NN`-valued "visits `z` before `w`" -/

/-- Taking `Int.toNat` of a `Z`-valued path is injective on the nonnegative levels `>= 1`,
which is all the paper's window uses. -/
theorem eq_of_toNat_eq {a : ℤ} {n : ℕ} (h : a.toNat = n) (hn : 1 ≤ n) : a = (n : ℤ) := by
  have h0 : 0 ≤ a := by
    by_contra hc
    push Not at hc
    have hz : a.toNat = 0 := Int.toNat_of_nonpos hc.le
    omega
  have h2 : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg h0
  rw [h] at h2
  exact h2.symm

/-- **`badCross` in the crossing layer's notation.**  For levels `z, w >= 1` the `Z`-valued
"visits `z` before `w`" event is the `NN`-valued `SwarmSpeed.hitsBefore` event of the
natural-valued path. -/
theorem hitsBeforeZ_eq_hitsBefore_toNat {Ω : Type*} {u : ℕ → Ω → ℤ} {z w : ℕ}
    (hz : 1 ≤ z) (hw : 1 ≤ w) :
    hitsBeforeZ u (z : ℤ) (w : ℤ)
      = hitsBefore (fun n ω => (u n ω).toNat) z w := by
  ext ω
  simp only [hitsBeforeZ, hitsBefore, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨n, hn, hk⟩
    refine ⟨n, by rw [hn]; simp, fun k hk' hcontra => ?_⟩
    exact hk k hk' (eq_of_toNat_eq hcontra hw)
  · rintro ⟨n, hn, hk⟩
    refine ⟨n, eq_of_toNat_eq hn hz, fun k hk' hcontra => ?_⟩
    exact hk k hk' (by rw [hcontra]; simp)

/-- The lower level `a_k` is at least `1` from `k = 81` on. -/
theorem lvlA_ge_one {k : ℕ} (hk : 81 ≤ k) : 1 ≤ lvlA k := by
  have h1 : 9 ≤ Nat.sqrt k := by
    rw [Nat.le_sqrt]
    omega
  have h2 : 3 ≤ Nat.sqrt (Nat.sqrt k) := by
    rw [Nat.le_sqrt]
    omega
  unfold lvlA lvlB
  omega

/-- `badCross` *is* the crossing layer's `hitsBefore` event of the shifted walk. -/
theorem badCross_eq_hitsBefore {p : ℝ} {m : ℕ} (i : Fin N) {k s : ℕ} (hz : 1 ≤ lvlA k) :
    badCross p m i k s
      = hitsBefore (fun n U => ((trajectory p m U (s + n)).pos i).toNat) (lvlA k) (lvlB k + 1) := by
  have hcast : ((lvlB k + 1 : ℕ) : ℤ) = (lvlB k : ℤ) + 1 := by push_cast; ring
  rw [badCross, hcast.symm,
    hitsBeforeZ_eq_hitsBefore_toNat (u := shiftPos (N := N) p m i s) hz (by omega)]
  rfl

/-! ### 2. The set-integral and the a.e. `condExp` forms are equivalent -/

/-- The set integral of `F`'s indicator over an `F_s`-measurable set is the measure of the
trace. -/
theorem setIntegral_indicator_one {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {F A : Set Ω} (hF : MeasurableSet F) :
    ∫ x in A, F.indicator (1 : Ω → ℝ) x ∂μ = μ.real (F ∩ A) := by
  have h := integral_indicator_one (μ := μ.restrict A) (s := F) hF
  have h2 : (μ.restrict A).real F = μ.real (F ∩ A) := by
    show ((μ.restrict A) F).toReal = (μ (F ∩ A)).toReal
    rw [Measure.restrict_apply hF]
  rw [h2] at h
  simpa using h

/-- **From an a.e. `condExp` bound to the test-set form.**  This is the direction in which
`SwarmSpeed.condExp_cross_prob_shift_le_R` is stated. -/
theorem setIntegral_le_of_condExp_le {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0} {s : ℕ} {F : Set Ω} {g : Ω → ℝ}
    (hF : MeasurableSet F) (hFint : Integrable (F.indicator (1 : Ω → ℝ)) μ)
    (_hg : Measurable[ℱ s] g) (hgint : Integrable g μ)
    (h : μ[F.indicator (1 : Ω → ℝ) | ℱ s] ≤ᵐ[μ] g) :
    ∀ A : Set Ω, MeasurableSet[ℱ s] A → μ.real (F ∩ A) ≤ ∫ x in A, g x ∂μ := by
  intro A hA
  rw [← setIntegral_indicator_one (μ := μ) (A := A) hF]
  rw [← setIntegral_condExp (μ := μ) (m := ℱ s) (ℱ.le s) hFint hA]
  exact setIntegral_mono_ae (μ := μ) (s := A) (f := μ[F.indicator (1 : Ω → ℝ) | ℱ s])
    (g := g) integrable_condExp.integrableOn hgint.integrableOn h

/-- **From the test-set form to an a.e. `condExp` bound.** -/
theorem condExp_ae_le_of_forall_setIntegral_le {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0} {s : ℕ}
    {F : Set Ω} {g : Ω → ℝ}
    (hF : MeasurableSet F) (hFint : Integrable (F.indicator (1 : Ω → ℝ)) μ)
    (hg : Measurable[ℱ s] g) (hgint : Integrable g μ)
    (h : ∀ A : Set Ω, MeasurableSet[ℱ s] A → μ.real (F ∩ A) ≤ ∫ x in A, g x ∂μ) :
    μ[F.indicator (1 : Ω → ℝ) | ℱ s] ≤ᵐ[μ] g := by
  refine SwarmSpeed.condExp_le_of_forall_setIntegral_le (μ := μ) (m := ℱ s) (ℱ.le s) hFint hgint
    hg ?_
  intro A hA
  rw [setIntegral_indicator_one (μ := μ) (A := A) hF]
  exact h A hA

/-! ### 3. Transience from the crossing estimate in the crossing layer's notation -/

/-- **Transience of the actual interacting trajectory** from the paper's eq. (cross) written
entirely in the vocabulary of `Swarm/Cross.lean`: the `hitsBefore` event of the
shifted actual walk, tested against every `F_s`-measurable event inside the site event, and
bounded by the revealed window potential `R (omega_j) a_k b_k`. -/
theorem ae_transience_of_hitsBefore_crossing {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (a b : Fin N) {K : ℕ}
    (hcx : ∀ k ≥ K, ∀ s : ℕ, ∀ A : Set (Array N),
      MeasurableSet[enlFilt (N := N) p m s] A → A ⊆ actualSite p m a b k s →
      (arrayMeasure N).real
          (hitsBefore (fun n U => ((trajectory p m U (s + n)).pos a).toNat)
            (lvlA k) (lvlB k + 1) ∩ A)
        ≤ ∫ U in A, R (windowWeight p m b U) (lvlA k) (lvlB k) ∂(arrayMeasure N))
    (hE : ∀ k ≥ K, ∀ s : ℕ,
      MeasurableSet[enlFilt (N := N) p m s]
        (actualSite p m a b k s
          ∩ ActualExtra p m b (SwarmLogRatio.paperC p ((1 - p) ^ (m - 1))) k)) :
    ∀ᵐ U ∂(arrayMeasure N),
      Tendsto (fun n => (trajectory p m U n).pos a) atTop atTop := by
  refine ae_transience_of_revealed_crossing hp1 hp2 hm a b (K := max K 81) ?_ (fun k hk s => ?_)
  · intro k hk s A hA hAsub
    rw [badCross_eq_hitsBefore a (lvlA_ge_one (le_trans (le_max_right _ _) hk))]
    exact hcx k (le_trans (le_max_left _ _) hk) s A hA hAsub
  · exact hE k (le_trans (le_max_left _ _) hk) s

end

end SwarmBad


