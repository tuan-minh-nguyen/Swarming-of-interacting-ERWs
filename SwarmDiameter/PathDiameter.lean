import Swarm.LeaderDescent

open MeasureTheory

namespace Swarming.Diameter

variable {N : ℕ} [Nonempty (Fin N)]

/-- The diameter of the configuration at time `n`. -/
noncomputable def pathDiameter (n : ℕ) (X : ℕ → Fin N → ℤ) : ℝ :=
  (LeaderDescent.spreadZ (fun i t => X t i) n : ℝ)

theorem pathDiameter_nonneg (n : ℕ) (X : ℕ → Fin N → ℤ) :
    0 ≤ pathDiameter n X := by
  unfold pathDiameter
  exact_mod_cast LeaderDescent.spreadZ_nonneg (fun i t => X t i) n

theorem measurable_pathDiameter (n : ℕ) :
    Measurable (pathDiameter (N := N) n) := by
  exact (measurable_of_countable (fun f : Fin N → ℤ => pathDiameter 0 (fun _ => f))).comp
    (measurable_pi_apply n)

theorem pathDiameter_shift (X : ℕ → Fin N → ℤ) (t k : ℕ) (d : ℤ) :
    pathDiameter k (fun n i => X (t + n) i - d) = pathDiameter (t + k) X := by
  let f : Fin N → ℤ := X (t + k)
  let s : Finset (Fin N) := Finset.univ
  have hs : s.Nonempty := Finset.univ_nonempty
  have hmax : s.sup' hs (fun i => f i - d) = s.sup' hs f - d := by
    apply le_antisymm
    · apply Finset.sup'_le _ _
      intro i hi
      exact sub_le_sub_right (Finset.le_sup' f hi) d
    · obtain ⟨i, hi, hfi⟩ := Finset.exists_mem_eq_sup' hs f
      rw [hfi]
      exact Finset.le_sup' (fun j => f j - d) hi
  have hmin : s.inf' hs (fun i => f i - d) = s.inf' hs f - d := by
    apply le_antisymm
    · obtain ⟨i, hi, hfi⟩ := Finset.exists_mem_eq_inf' hs f
      rw [hfi]
      exact Finset.inf'_le (fun j => f j - d) hi
    · apply Finset.le_inf' _ _
      intro i hi
      exact sub_le_sub_right (Finset.inf'_le f hi) d
  change ((s.sup' hs (fun i => f i - d) - s.inf' hs (fun i => f i - d) : ℤ) : ℝ) =
    ((s.sup' hs f - s.inf' hs f : ℤ) : ℝ)
  rw [hmax, hmin]
  exact congrArg (fun z : ℤ => (z : ℝ)) (by omega)

end Swarming.Diameter
