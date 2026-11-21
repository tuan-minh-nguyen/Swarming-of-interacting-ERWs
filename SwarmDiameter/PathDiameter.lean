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

theorem sub_le_pathDiameter (n : ℕ) (X : ℕ → Fin N → ℤ) (i j : Fin N) :
    ((X n i - X n j : ℤ) : ℝ) ≤ pathDiameter n X := by
  unfold pathDiameter LeaderDescent.spreadZ
  exact_mod_cast sub_le_sub
    (Finset.le_sup' (X n) (Finset.mem_univ i))
    (Finset.inf'_le (X n) (Finset.mem_univ j))

theorem measurable_pathDiameter (n : ℕ) :
    Measurable (pathDiameter (N := N) n) := by
  exact (measurable_of_countable (fun f : Fin N → ℤ => pathDiameter 0 (fun _ => f))).comp
    (measurable_pi_apply n)

/-- The maximum diameter from time zero through time `n`. -/
noncomputable def runningDiameter (n : ℕ) (X : ℕ → Fin N → ℤ) : ℝ :=
  (Finset.range (n + 1)).sup' (by simp) (fun t => pathDiameter t X)

theorem runningDiameter_mono {n m : ℕ} (h : n ≤ m) (X : ℕ → Fin N → ℤ) :
    runningDiameter n X ≤ runningDiameter m X :=
  Finset.sup'_mono (fun t => pathDiameter t X)
    (Finset.range_subset_range.mpr (Nat.succ_le_succ h)) (by simp)

theorem pathDiameter_le_runningDiameter {t n : ℕ} (h : t ≤ n) (X : ℕ → Fin N → ℤ) :
    pathDiameter t X ≤ runningDiameter n X :=
  Finset.le_sup' (fun s => pathDiameter s X) (Finset.mem_range.mpr (Nat.lt_succ_of_le h))

theorem le_runningDiameter_iff {a : ℝ} (n : ℕ) (X : ℕ → Fin N → ℤ) :
    a ≤ runningDiameter n X ↔ ∃ t ≤ n, a ≤ pathDiameter t X := by
  constructor
  · intro ha
    obtain ⟨t, ht, he⟩ := Finset.exists_mem_eq_sup' (s := Finset.range (n + 1)) (by simp)
      (fun s => pathDiameter s X)
    exact ⟨t, Nat.le_of_lt_succ (Finset.mem_range.mp ht), ha.trans_eq he⟩
  · rintro ⟨t, ht, h⟩
    exact h.trans (pathDiameter_le_runningDiameter ht X)

theorem measurable_runningDiameter (n : ℕ) : Measurable (runningDiameter (N := N) n) := by
  apply measurable_of_Ici
  intro a
  have he : runningDiameter (N := N) n ⁻¹' Set.Ici a =
      ⋃ t : ℕ, ⋃ _ : t ≤ n, pathDiameter t ⁻¹' Set.Ici a := by
    ext X
    simp only [Set.mem_preimage, Set.mem_Ici, le_runningDiameter_iff, Set.mem_iUnion, exists_prop]
  rw [he]
  exact MeasurableSet.iUnion fun t => MeasurableSet.iUnion fun _ => measurable_pathDiameter t measurableSet_Ici

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
