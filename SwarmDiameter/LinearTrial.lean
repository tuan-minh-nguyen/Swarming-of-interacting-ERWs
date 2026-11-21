import Swarm.SyncAttemptForce
import SwarmDiameter.PathDiameter

open MeasureTheory Set
open Swarming.Enl Swarming.Uniform SwarmRestart
open scoped ENNReal

namespace Swarming.Diameter

variable {N m : ℕ} {p : ℝ} [Nonempty (Fin N)]

/-- From a common position, two walks moving in opposite directions for `L`
steps have diameter at least `2 * L`. The bound is integrated over a past event. -/
theorem linear_trial_mass_ge (hp₀ : (1 : ℝ) / 2 ≤ p) (hp₁ : p < 1) (hN : 2 ≤ N)
    (n L : ℕ) {G : Set (Array N)} (hG : MeasurableSet[enlMeas p m n] G)
    (hpos : ∀ U ∈ G, ∀ i j, posPath p m U n i = posPath p m U n j) :
    ENNReal.ofReal (1 - p) ^ (L * 2) * arrayMeasure N G ≤
      arrayMeasure N (G ∩ {U | 2 * (L : ℝ) ≤ pathDiameter (n + L) (posPath p m U)}) := by
  let i : Fin N := ⟨0, by omega⟩
  let j : Fin N := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    simpa [i, j] using congrArg Fin.val h
  let A : Finset (Fin N) := {i, j}
  have hA : A.card = 2 := by simp [A, hij]
  have hi : i ∈ A := by simp [A]
  have hj : j ∈ A := by simp [A]
  let ε : ℕ → Fin N → ℤ := fun _ k => if k = i then 1 else -1
  have hε (u : ℕ) (k : Fin N) : ε u k = 1 ∨ ε u k = -1 := by
    by_cases h : k = i <;> simp [ε, h]
  have hmass := evWord_mass_ge p hp₀ hp₁ m n A ε hε hG L
  rw [hA] at hmass
  apply hmass.trans (measure_mono ?_)
  rintro U ⟨hU, hw⟩
  refine ⟨hU, ?_⟩
  have hdiff (v : ℕ) (hv : v ≤ L) :
      posPath p m U (n + v) i - posPath p m U (n + v) j = 2 * (v : ℤ) := by
    induction v with
    | zero => simp [hpos U hU i j]
    | succ v ih =>
      have hs₁ := SyncAttemptForce.evWord_step_of_mem hw (by omega : v < L) hi
      have hs₂ := SyncAttemptForce.evWord_step_of_mem hw (by omega : v < L) hj
      change posPath p m U (n + v + 1) i = posPath p m U (n + v) i + ε v i at hs₁
      change posPath p m U (n + v + 1) j = posPath p m U (n + v) j + ε v j at hs₂
      simp only [ε, if_pos rfl] at hs₁
      simp only [ε, if_neg hij.symm] at hs₂
      rw [Nat.add_succ, hs₁, hs₂]
      have h := ih (by omega)
      push_cast
      omega
  have h := sub_le_pathDiameter (n + L) (posPath p m U) i j
  rw [hdiff L le_rfl] at h
  exact_mod_cast h

/-- The linear trial bound at an integer-valued stopping time, in integrated
form on each event in the stopped filtration. -/
theorem linear_trial_at_stopping_time_mass_ge (hp₀ : (1 : ℝ) / 2 ≤ p) (hp₁ : p < 1)
    (hN : 2 ≤ N) (S : Array N → ℕ) (L : ℕ) {G : Set (Array N)}
    (hG : ∀ n, MeasurableSet[enlMeas p m n] (G ∩ {U | S U = n}))
    (hpos : ∀ U ∈ G, ∀ i j, posPath p m U (S U) i = posPath p m U (S U) j) :
    ENNReal.ofReal (1 - p) ^ (L * 2) * arrayMeasure N G ≤
      arrayMeasure N (G ∩ {U | 2 * (L : ℝ) ≤ pathDiameter (S U + L) (posPath p m U)}) := by
  let A (n : ℕ) := G ∩ {U | S U = n}
  let B (n : ℕ) := {U : Array N | 2 * (L : ℝ) ≤ pathDiameter (n + L) (posPath p m U)}
  have hA : (⋃ n, A n) = G := by
    ext U
    simp [A, ← Set.inter_iUnion]
  have hAB : (⋃ n, A n ∩ B n) =
      G ∩ {U | 2 * (L : ℝ) ≤ pathDiameter (S U + L) (posPath p m U)} := by
    ext U
    constructor
    · intro h
      obtain ⟨n, ⟨⟨hU, hn⟩, hb⟩⟩ := Set.mem_iUnion.mp h
      refine ⟨hU, ?_⟩
      change S U = n at hn
      change 2 * (L : ℝ) ≤ pathDiameter (n + L) (posPath p m U) at hb
      change 2 * (L : ℝ) ≤ pathDiameter (S U + L) (posPath p m U)
      simpa only [hn] using hb
    · rintro ⟨hU, hb⟩
      exact Set.mem_iUnion.mpr ⟨S U, ⟨⟨hU, rfl⟩, hb⟩⟩
  have hd : Pairwise (fun n k => Disjoint (A n) (A k)) := by
    intro n k hne
    exact Set.disjoint_left.mpr fun _ h₁ h₂ => hne (h₁.2.symm.trans h₂.2)
  have hd' : Pairwise (fun n k => Disjoint (A n ∩ B n) (A k ∩ B k)) :=
    fun _ _ hne => (hd hne).mono Set.inter_subset_left Set.inter_subset_left
  have hm : ∀ n, MeasurableSet (A n) := fun n => enlMeas_le p m n _ (hG n)
  have hm' : ∀ n, MeasurableSet (A n ∩ B n) :=
    fun n => (hm n).inter ((measurable_pathDiameter _).comp (measurable_posPath p m N) measurableSet_Ici)
  rw [← hAB, ← hA, measure_iUnion hd hm, measure_iUnion hd' hm', ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro n
  apply linear_trial_mass_ge hp₀ hp₁ hN n L (hG n)
  intro U hU i j
  have hu := hpos U hU.1 i j
  have hn : S U = n := hU.2
  rwa [hn] at hu

end Swarming.Diameter
