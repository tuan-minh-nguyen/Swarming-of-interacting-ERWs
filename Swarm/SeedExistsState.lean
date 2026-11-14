/-
# A finite prefix and state with a positive-probability nonnegative future

The paper proves `P(V) > 0` by first extracting, from transience, a finite time `t` and a finite
path `γ` such that the event "the path up to `t` is `γ` and the path is nonnegative from `t` on"
has positive probability.  This file supplies exactly that statement for the actual array law
(`exists_prefix_state`), together with the realising array.

The decomposition is over the countable set of finite nearest-neighbour prefixes
`Fin (t+1) → Fin N → ℤ`, and uses the transience theorem `SwarmBad.ae_transience_actual` of the
transience area (no re-derivation).
-/
import Swarm.SeedFutureDet
import Swarm.FrozenBadTime

open MeasureTheory Set ProbabilityTheory Filter
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmRestart

namespace SwarmSeed

variable {N : ℕ}

/-- The canonical extension of a finite prefix to an infinite path (zero after `t`). -/
def extendPath {t : ℕ} (γ : Fin (t + 1) → Fin N → ℤ) : ℕ → Fin N → ℤ :=
  fun n i => if h : n ≤ t then γ ⟨n, Nat.lt_succ_of_le h⟩ i else 0

/-- The state reached at time `t` by a finite prefix `γ` of length `t+1`. -/
noncomputable def pathState {t : ℕ} (γ : Fin (t + 1) → Fin N → ℤ) : WalkState N :=
  ⟨fun i => extendPath γ t i, dt (extendPath γ) t⟩

theorem pathState_pos {t : ℕ} (γ : Fin (t + 1) → Fin N → ℤ) (i : Fin N) :
    (pathState γ).pos i = γ ⟨t, Nat.lt_succ_self t⟩ i := by
  simp [pathState, extendPath]

/-- The event that the actual trajectory follows the finite prefix `γ` up to time `t`. -/
def Pref (p : ℝ) (m : ℕ) {t : ℕ} (γ : Fin (t + 1) → Fin N → ℤ) : Set (Array N) :=
  {U | ∀ k : Fin (t + 1), ∀ i : Fin N, (trajectory p m U k.val).pos i = γ k i}

theorem measurableSet_Pref (p : ℝ) (m : ℕ) {t : ℕ} (γ : Fin (t + 1) → Fin N → ℤ) :
    MeasurableSet (Pref (N := N) p m γ) := by
  have h : Pref (N := N) p m γ = ⋂ k : Fin (t + 1), ⋂ i : Fin N,
      {U : Array N | (trajectory p m U k.val).pos i = γ k i} := by
    ext U
    simp only [Pref, mem_ofPred_eq, mem_iInter]
  rw [h]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun i =>
    ((Swarming.Fair.measurable_trajectory (N := N) p m k.val).1 i) (measurableSet_singleton _)

/-- On its own prefix event, the state at time `t` is `pathState γ`. -/
theorem trajectory_eq_pathState {p : ℝ} {m : ℕ} {t : ℕ} {γ : Fin (t + 1) → Fin N → ℤ}
    {U : Array N} (hU : U ∈ Pref (N := N) p m γ) : trajectory p m U t = pathState γ := by
  have hpos : ∀ k, k ≤ t → ∀ i, (trajectory p m U k).pos i = extendPath γ k i := by
    intro k hk i
    rw [show (trajectory p m U k).pos i = γ ⟨k, Nat.lt_succ_of_le hk⟩ i from
      hU ⟨k, Nat.lt_succ_of_le hk⟩ i]
    simp only [extendPath, dif_pos hk]
  refine walkState_ext ?_ ?_
  · funext i
    rw [pathState]
    exact hpos t le_rfl i
  · funext i x
    rw [pathState]
    exact ell_eq_dt hpos i x

/-- **A positive-probability finite prefix whose future stays nonnegative.** -/
theorem exists_prefix_state {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (hN : 2 ≤ N) :
    ∃ (t : ℕ) (γ : Fin (t + 1) → Fin N → ℤ),
      (arrayMeasure N) (Pref (N := N) p m γ ∩ FutureGe p m (pathState γ) 0) ≠ 0 := by
  have htrans : ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
      Tendsto (fun n => (trajectory p m U n).pos i) atTop atTop := by
    refine Filter.eventually_all.mpr (fun i => ?_)
    obtain ⟨j, hji⟩ : ∃ j : Fin N, i ≠ j := by
      refine ⟨if h : i = ⟨0, by omega⟩ then ⟨1, by omega⟩ else ⟨0, by omega⟩, ?_⟩
      split_ifs with h
      · rw [h]
        intro hc
        exact absurd (congrArg Fin.val hc) (by norm_num)
      · intro hc
        exact h hc
    exact SwarmBad.ae_transience_actual hp0 hp1 hm i j hji
  have hfull : ∀ᵐ U ∂(arrayMeasure N),
      ∃ t, ∀ n, t ≤ n → ∀ i, 0 ≤ (trajectory p m U n).pos i := by
    filter_upwards [htrans] with U hU
    have hone : ∀ i : Fin N, ∃ N₀, ∀ n, N₀ ≤ n → 0 ≤ (trajectory p m U n).pos i := by
      intro i
      exact eventually_atTop.mp ((hU i).eventually (eventually_ge_atTop (0 : ℤ)))
    choose N₀ hN₀ using hone
    refine ⟨Finset.univ.sup N₀, fun n hn i => ?_⟩
    exact hN₀ i n (le_trans (Finset.le_sup (Finset.mem_univ i)) hn)
  set A : ℕ → Set (Array N) :=
    fun t => {U | ∀ n, t ≤ n → ∀ i, 0 ≤ (trajectory p m U n).pos i} with hA
  have hmeasA : ∀ t, MeasurableSet (A t) := by
    intro t
    have h : A t = ⋂ n, ⋂ (_ : t ≤ n), ⋂ i : Fin N,
        {U : Array N | 0 ≤ (trajectory p m U n).pos i} := by
      ext U
      simp only [hA, mem_ofPred_eq, mem_iInter]
    rw [h]
    exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun i =>
        ((Swarming.Fair.measurable_trajectory (N := N) p m n).1 i) measurableSet_Ici
  have hnull : (arrayMeasure N) ((⋃ t, A t)ᶜ) = 0 := by
    refine measure_mono_null ?_ (ae_iff.mp hfull)
    intro U hU
    simp only [mem_compl_iff, mem_iUnion, not_exists] at hU
    simp only [hA, mem_ofPred_eq]
    intro hex
    obtain ⟨t', ht'⟩ := hex
    exact hU t' ht'
  have h1 : (arrayMeasure N) (⋃ t, A t) = 1 := by
    have hcompl := measure_add_measure_compl (μ := arrayMeasure N) (s := ⋃ t, A t)
      (MeasurableSet.iUnion hmeasA)
    rw [hnull, add_zero] at hcompl
    rw [hcompl]
    simp
  obtain ⟨t, ht⟩ : ∃ t, (arrayMeasure N) (A t) ≠ 0 := by
    by_contra h
    push_neg at h
    have h0 : (arrayMeasure N) (⋃ t, A t) = 0 := measure_iUnion_null h
    rw [h1] at h0
    exact one_ne_zero h0
  have hpos : 0 < (arrayMeasure N) (A t) := pos_iff_ne_zero.mpr ht
  -- decompose by the finite prefix
  have hdec : A t ⊆ ⋃ (γ : Fin (t + 1) → Fin N → ℤ),
      (Pref (N := N) p m γ ∩ FutureGe p m (pathState γ) 0) := by
    intro U hU
    refine mem_iUnion.mpr ⟨(fun k i => (trajectory p m U k.val).pos i), ?_, ?_⟩
    · intro k i
      rfl
    · have hstate : pathState (fun k i => (trajectory p m U k.val).pos i) = trajectory p m U t :=
        (trajectory_eq_pathState (p := p) (m := m)
          (γ := fun k i => (trajectory p m U k.val).pos i) (fun k i => rfl)).symm
      rw [hstate]
      intro n i
      rw [← trajectory_add]
      exact hU (t + n) (Nat.le_add_right t n) i
  have hle : (arrayMeasure N) (A t) ≤
      ∑' γ : Fin (t + 1) → Fin N → ℤ,
        (arrayMeasure N) (Pref (N := N) p m γ ∩ FutureGe p m (pathState γ) 0) :=
    (measure_mono hdec).trans (measure_iUnion_le _)
  obtain ⟨γ, hγ⟩ : ∃ γ : Fin (t + 1) → Fin N → ℤ,
      (arrayMeasure N) (Pref (N := N) p m γ ∩ FutureGe p m (pathState γ) 0) ≠ 0 := by
    by_contra h
    push_neg at h
    have h0 : (∑' γ : Fin (t + 1) → Fin N → ℤ,
        (arrayMeasure N) (Pref (N := N) p m γ ∩ FutureGe p m (pathState γ) 0)) = 0 := by
      simp [h]
    rw [h0] at hle
    exact absurd hle (not_le.mpr hpos)
  exact ⟨t, γ, hγ⟩

end SwarmSeed
