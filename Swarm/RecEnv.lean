/-
  **The record-enlarged environment of the interacting array.**

  `Swarm/EnlFilt.lean` builds the enlarged filtration `enlFilt p m n`
  from the read set `prefRead n γ`: the coordinates the path `γ` has *departed* through strictly
  before time `n`.  That is one row short at the running record `M_n^j = runMax p m U j n`: the
  walker may be *sitting* on its record site at time `n` without ever having departed from it, so
  some coordinates `(j, M_n^j, k)` can lie outside `prefRead n γ`.  Hence `h_j(M_n^j)` is **not**
  known to be `enlFilt`-measurable, and the projected recursion `e_{g+1} = 1 + a (1 + e_g)`
  cannot be pulled out of a conditional expectation under `enlFilt`.

  This file does not assume the missing measurability: it *adds the record site's row to the base
  information*, as an explicit enlargement of the read set.

  * `pieceMeas` — the γ-piecewise σ-algebra of an arbitrary γ-dependent finite read set `S γ`
    (the construction of `enlMeas` with `prefRead n γ` replaced by `S γ`);
  * `enlMeas_le_pieceMeas` — `enlFilt n ≤ pieceMeas S` whenever `prefRead n γ ⊆ S γ`;
  * `recVal`, `recRow`, `recRead` — the record value of a prefix, the row of `m - 1` marks at a
    site, and `prefRead ∪ recRow (recVal)`;
  * `enlRecMeas` — the record-enlarged σ-algebra `pieceMeas (recRead)`;
  * `measurableSet_recVal_eq`, `measurableSet_recRow` — **the record edge**: the value of the
    running record and every mark coordinate *at* the record site are measurable for
    `enlRecMeas`.  Nothing like this is claimed for `enlFilt`.
  * `recInfo`, `infoPiece` — the same enlargement with the rows of the next `g` sites above the
    record adjoined (the increasing environment enlargement), with the monotonicity facts and the
    "every row is below `recVal + g`" fact used to keep the next strict-above-record site fresh.

  Everything here is deterministic: no probability enters.
-/
import Swarm.EnlFuture
import Swarm.RecursionCore
import Swarm.EnvCore

set_option linter.unusedVariables false
set_option warn.classDefReducibility false
set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory

variable {N : ℕ}

/-! ### The γ-piecewise cylinder σ-algebra over an arbitrary read set -/

/-- **Piecewise cylinder σ-algebra.**  `G` is measurable when, on every piece `{path = γ}`, it
agrees with a set determined by the finitely many coordinates in `S γ`.  With
`S = fun γ => prefRead n γ` this is `enlMeas p m n`; the point of the definition is that the read
set may be enlarged by further coordinates (the record row, the rows above it). -/
noncomputable def pieceMeas (p : ℝ) (m : ℕ) (n : ℕ)
    (S : Pref N n → Finset (Fin N × ℤ × ℕ)) : MeasurableSpace (Array N) where
  MeasurableSet' G := ∀ γ : Pref N n, ∃ B : Set (Array N),
    MeasurableSet[cylAt (N := N) (S γ)] B ∧ prefAgree p m γ ∩ G = prefAgree p m γ ∩ B
  measurableSet_empty := by
    intro γ
    exact ⟨∅, (cylAt (S γ)).measurableSet_empty, by simp⟩
  measurableSet_compl := by
    intro G hG γ
    obtain ⟨B, hB, hEq⟩ := hG γ
    refine ⟨Bᶜ, (cylAt (S γ)).measurableSet_compl _ hB, ?_⟩
    have hstep : prefAgree p m γ ∩ Gᶜ = prefAgree p m γ ∩ (prefAgree p m γ ∩ G)ᶜ := by
      ext U
      simp only [Set.mem_inter_iff, Set.mem_compl_iff]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun hc => h2 hc.2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun hg => h2 ⟨h1, hg⟩⟩
    have hgoal : prefAgree p m γ ∩ (prefAgree p m γ ∩ B)ᶜ = prefAgree p m γ ∩ Bᶜ := by
      ext U
      simp only [Set.mem_inter_iff, Set.mem_compl_iff]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun hb => h2 ⟨h1, hb⟩⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun hc => h2 hc.2⟩
    rw [hstep, hEq, hgoal]
  measurableSet_iUnion := by
    intro G hG γ
    choose B hB hEq using fun i => hG i γ
    exact ⟨⋃ i, B i, (cylAt (S γ)).measurableSet_iUnion B hB, by
      rw [Set.inter_iUnion, Set.inter_iUnion]
      congr 1
      funext i
      exact hEq i⟩

lemma pieceMeas_iff {p : ℝ} {m n : ℕ} {S : Pref N n → Finset (Fin N × ℤ × ℕ)}
    {G : Set (Array N)} :
    MeasurableSet[pieceMeas p m n S] G ↔ ∀ γ : Pref N n, ∃ B : Set (Array N),
      MeasurableSet[cylAt (N := N) (S γ)] B ∧ prefAgree p m γ ∩ G = prefAgree p m γ ∩ B :=
  Iff.rfl

/-- A fixed finite set of coordinates is measurable for the ambient product σ-algebra. -/
lemma cylAt_le_ambient (S : Finset (Fin N × ℤ × ℕ)) :
    cylAt (N := N) S ≤ (inferInstance : MeasurableSpace (Array N)) := by
  intro A hA
  obtain ⟨C, hC, hEq⟩ := MeasurableSpace.measurableSet_comap.1 hA
  rw [← hEq]
  have hproj : Measurable fun (g : Array N) (c : S) => g c :=
    measurable_pi_iff.2 fun c => measurable_pi_apply (X := fun _ => ℝ) ((c : ↥S) : Fin N × ℤ × ℕ)
  exact hC.preimage hproj

/-- `pieceMeas S` sits inside the ambient product σ-algebra. -/
lemma pieceMeas_le (p : ℝ) (m n : ℕ) (S : Pref N n → Finset (Fin N × ℤ × ℕ)) :
    pieceMeas (N := N) p m n S ≤ (inferInstance : MeasurableSpace (Array N)) := by
  intro G hG
  choose B hB hEq using hG
  have hpiece : ∀ γ : Pref N n, MeasurableSet (prefAgree p m γ ∩ B γ) := fun γ =>
    (measurableSet_prefAgree_ambient p m γ).inter (cylAt_le_ambient (S γ) (B γ) (hB γ))
  have hunion : G = ⋃ γ : Pref N n, (prefAgree p m γ ∩ B γ) := by
    ext U
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      refine ⟨prefOf p m n U, prefAgree_prefOf U, ?_⟩
      have h3 : U ∈ prefAgree p m (prefOf p m n U) ∩ G := ⟨prefAgree_prefOf U, h⟩
      rw [hEq (prefOf p m n U)] at h3
      exact h3.2
    · rintro ⟨γ, h1, h2⟩
      have h3 : U ∈ prefAgree p m γ ∩ G := by rw [hEq γ]; exact ⟨h1, h2⟩
      exact h3.2
  rw [hunion]
  exact MeasurableSet.iUnion hpiece

/-- Enlarging the read set can only enlarge the σ-algebra. -/
lemma pieceMeas_mono {p : ℝ} {m n : ℕ} {S S' : Pref N n → Finset (Fin N × ℤ × ℕ)}
    (h : ∀ γ, S γ ⊆ S' γ) : pieceMeas (N := N) p m n S ≤ pieceMeas p m n S' := by
  intro G hG γ
  obtain ⟨B, hB, hEq⟩ := hG γ
  exact ⟨B, cylAt_mono (h γ) B hB, hEq⟩

/-- The enlarged filtration is contained in the σ-algebra of any read set containing
`prefRead`. -/
lemma enlMeas_le_pieceMeas (p : ℝ) (m n : ℕ) (S : Pref N n → Finset (Fin N × ℤ × ℕ))
    (hS : ∀ γ, prefRead n γ ⊆ S γ) :
    enlMeas p m n ≤ pieceMeas (N := N) p m n S :=
  pieceMeas_mono hS

/-- **Measurability transfer.**  A function which on each piece agrees with a `cylAt (S γ)`-
measurable function is measurable for `pieceMeas S`. -/
lemma measurable_pieceMeas {p : ℝ} {m n : ℕ} {S : Pref N n → Finset (Fin N × ℤ × ℕ)}
    {f : Array N → ℝ} {f' : Pref N n → Array N → ℝ}
    (hf' : ∀ γ, Measurable[cylAt (N := N) (S γ)] (f' γ))
    (hagree : ∀ γ, ∀ U ∈ prefAgree p m γ, f U = f' γ U) :
    Measurable[pieceMeas p m n S] f := by
  intro T hT γ
  refine ⟨(f' γ) ⁻¹' T, hf' γ hT, ?_⟩
  ext U
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [hagree γ U h1] at h2; exact h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [hagree γ U h1]; exact h2⟩

/-- A set which on each piece is either empty or the whole piece is measurable.  This is how the
*path-determined* events (prefixes, the record value) enter `pieceMeas`. -/
lemma measurableSet_pieceMeas_of_piecewise {p : ℝ} {m n : ℕ}
    {S : Pref N n → Finset (Fin N × ℤ × ℕ)} {G : Set (Array N)}
    (h : ∀ γ : Pref N n, prefAgree p m γ ∩ G = ∅ ∨ prefAgree p m γ ∩ G = prefAgree p m γ) :
    MeasurableSet[pieceMeas p m n S] G := by
  intro γ
  rcases h γ with h | h
  · exact ⟨∅, (cylAt (S γ)).measurableSet_empty, by rw [h, Set.inter_empty]⟩
  · exact ⟨Set.univ, MeasurableSet.univ, by rw [h, Set.inter_univ]⟩

/-! ### The record value of a prefix, and the row at a site -/

/-- The running record `M_n^j` read off a position prefix. -/
noncomputable def recVal (j : Fin N) {n : ℕ} (γ : Pref N n) : ℤ :=
  (Finset.range (n + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩ (fun t => ext γ t j)

/-- The `m - 1` mark coordinates of walker `j` at the site `y`. -/
noncomputable def recRow (m : ℕ) (j : Fin N) (y : ℤ) : Finset (Fin N × ℤ × ℕ) :=
  (Finset.Icc 1 (m - 1)).image (fun k => (j, y, k))

lemma mem_recRow {m : ℕ} {j : Fin N} {y : ℤ} {c : Fin N × ℤ × ℕ} :
    c ∈ recRow m j y ↔ ∃ k ∈ Finset.Icc 1 (m - 1), c = (j, y, k) := by
  simp only [recRow, Finset.mem_image]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, rfl⟩

/-- The read set of the enlarged filtration together with the whole row at the record site.
This is the base information of the record edge. -/
noncomputable def recRead (m : ℕ) (j : Fin N) {n : ℕ} (γ : Pref N n) :
    Finset (Fin N × ℤ × ℕ) :=
  prefRead n γ ∪ recRow m j (recVal j γ)

lemma prefRead_subset_recRead {m n : ℕ} (j : Fin N) (γ : Pref N n) :
    prefRead n γ ⊆ recRead m j γ := by
  intro c hc
  exact Finset.mem_union_left _ hc

/-- **The record-enlarged σ-algebra**: the enlarged filtration plus the whole row of marks at
the running record site. -/
noncomputable def enlRecMeas (p : ℝ) (m : ℕ) (n : ℕ) (j : Fin N) : MeasurableSpace (Array N) :=
  pieceMeas p m n (recRead (N := N) m j)

lemma enlMeas_le_enlRecMeas (p : ℝ) (m n : ℕ) (j : Fin N) :
    enlMeas p m n ≤ enlRecMeas (N := N) p m n j :=
  enlMeas_le_pieceMeas p m n _ (fun γ => prefRead_subset_recRead j γ)

lemma enlRecMeas_le (p : ℝ) (m n : ℕ) (j : Fin N) :
    enlRecMeas (N := N) p m n j ≤ (inferInstance : MeasurableSpace (Array N)) :=
  pieceMeas_le p m n _

lemma enlFilt_le_enlRecMeas (p : ℝ) (m n : ℕ) (j : Fin N) :
    enlFilt (N := N) p m n ≤ enlRecMeas (N := N) p m n j :=
  enlMeas_le_enlRecMeas p m n j

/-! ### The record edge: the record value and its row are measurable -/

lemma recVal_prefOf_of_mem {p : ℝ} {m n : ℕ} {γ : Pref N n} {U : Array N}
    (hU : U ∈ prefAgree p m γ) (j : Fin N) :
    recVal j (prefOf p m n U) = recVal j γ := by
  unfold recVal
  refine Finset.sup'_congr _ rfl ?_
  intro t ht
  have ht' : t < n + 1 := Finset.mem_range.mp ht
  rw [ext_prefOf U (Nat.lt_succ_iff.mp ht') j, ext_of_lt γ ht' j]
  exact congrFun (hU ⟨t, ht'⟩) j

/-- The prefix record is the actual running record of the trajectory. -/
theorem runMax_eq_recVal (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (n : ℕ) :
    runMax p m U j n = recVal j (prefOf p m n U) := by
  unfold runMax recVal
  refine Finset.sup'_congr _ rfl ?_
  intro t ht
  have ht' : t < n + 1 := Finset.mem_range.mp ht
  exact (ext_prefOf U (Nat.lt_succ_iff.mp ht') j).symm

lemma zero_le_runMax (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (n : ℕ) :
    0 ≤ runMax p m U j n := by
  have h := Finset.le_sup' (fun t => (trajectory p m U t).pos j)
    (Finset.mem_range.mpr (Nat.succ_pos n) : 0 ∈ Finset.range (n + 1))
  have h0 : (trajectory p m U 0).pos j = 0 := rfl
  rw [h0] at h
  exact h

/-- The running record is nonnegative, so it may be read as a natural number.  This is the
`0 ≤ M_n^j` restriction, which holds identically here and is *not* dropped later. -/
lemma zero_le_recVal_prefOf (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (n : ℕ) :
    0 ≤ recVal j (prefOf p m n U) := by
  rw [← runMax_eq_recVal]
  exact zero_le_runMax p m U j n

/-- A prefix position never exceeds the record. -/
lemma le_recVal (p : ℝ) (m : ℕ) {n : ℕ} {γ : Pref N n} {U : Array N}
    (hU : U ∈ prefAgree p m γ) (j : Fin N) {t : ℕ} (ht : t ≤ n) :
    (trajectory p m U t).pos j ≤ recVal j γ := by
  have ht' : t < n + 1 := by omega
  rw [← ext_prefOf_of_mem hU ht j]
  exact Finset.le_sup' (fun s => ext γ s j) (Finset.mem_range.mpr ht')

/-- The value of the running record is measurable for the record-enlarged σ-algebra. -/
theorem measurableSet_recVal_eq (p : ℝ) (m n : ℕ) (j : Fin N) (y : ℤ) :
    MeasurableSet[enlRecMeas p m n j] {U : Array N | recVal j (prefOf p m n U) = y} := by
  refine measurableSet_pieceMeas_of_piecewise (fun γ => ?_)
  by_cases h : recVal j γ = y
  · right
    refine Set.Subset.antisymm Set.inter_subset_left ?_
    rintro U hU
    refine ⟨hU, ?_⟩
    simp only [Set.mem_ofPred_eq]
    rw [recVal_prefOf_of_mem hU j, h]
  · left
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro U ⟨hU, hy⟩
    simp only [Set.mem_ofPred_eq] at hy
    exact h (by rw [← recVal_prefOf_of_mem hU j]; exact hy)

/-- **The record edge.**  Every mark coordinate *at* the running record site is measurable for
the record-enlarged σ-algebra, although it need not have been read before time `n`. -/
theorem measurableSet_recRow (p : ℝ) (m n : ℕ) (j : Fin N) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 (m - 1)) {I : Set ℝ} (hI : MeasurableSet I) :
    MeasurableSet[enlRecMeas p m n j]
      {U : Array N | U (j, recVal j (prefOf p m n U), k) ∈ I} := by
  intro γ
  have hmem : (j, recVal j γ, k) ∈ recRead (N := N) m j γ :=
    Finset.mem_union_right _ (mem_recRow.mpr ⟨k, hk, rfl⟩)
  refine ⟨{U : Array N | U (j, recVal j γ, k) ∈ I}, ?_, ?_⟩
  · exact measurableSet_cylAt_of_mem hmem hI
  · ext U
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [recVal_prefOf_of_mem h1 j] at h2; exact h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [recVal_prefOf_of_mem h1 j]; exact h2⟩

/-! ### The increasing environment enlargement above the record -/

/-- The read set with the rows of the next `g` sites above the record adjoined. -/
noncomputable def recInfo (m : ℕ) (j : Fin N) (g : ℕ) {n : ℕ} (γ : Pref N n) :
    Finset (Fin N × ℤ × ℕ) :=
  recRead m j γ ∪ (Finset.Icc 1 g).biUnion (fun k => recRow m j (recVal j γ + (k : ℤ)))

/-- The `g`-th enlargement of the record information. -/
noncomputable def infoPiece (p : ℝ) (m : ℕ) (n : ℕ) (j : Fin N) (g : ℕ) :
    MeasurableSpace (Array N) :=
  pieceMeas p m n (recInfo (N := N) m j g)

lemma recRead_subset_recInfo {m : ℕ} (j : Fin N) (g : ℕ) {n : ℕ} (γ : Pref N n) :
    recRead m j γ ⊆ recInfo m j g γ := Finset.subset_union_left

lemma prefRead_subset_recInfo {m : ℕ} (j : Fin N) (g : ℕ) {n : ℕ} (γ : Pref N n) :
    prefRead n γ ⊆ recInfo m j g γ :=
  (prefRead_subset_recRead j γ).trans (recRead_subset_recInfo j g γ)

lemma recInfo_mono {m : ℕ} (j : Fin N) {g g' : ℕ} (hgg : g ≤ g') {n : ℕ} (γ : Pref N n) :
    recInfo m j g γ ⊆ recInfo m j g' γ := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact Finset.mem_union_left _ hx
  · refine Finset.mem_union_right _ ?_
    rw [Finset.mem_biUnion] at hx ⊢
    obtain ⟨h, hh, hxh⟩ := hx
    exact ⟨h, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hh).1, le_trans (Finset.mem_Icc.mp hh).2 hgg⟩, hxh⟩

lemma enlRecMeas_le_infoPiece (p : ℝ) (m n : ℕ) (j : Fin N) (g : ℕ) :
    enlRecMeas (N := N) p m n j ≤ infoPiece (N := N) p m n j g :=
  pieceMeas_mono (fun γ => recRead_subset_recInfo j g γ)

lemma enlMeas_le_infoPiece (p : ℝ) (m n : ℕ) (j : Fin N) (g : ℕ) :
    enlMeas p m n ≤ infoPiece (N := N) p m n j g :=
  (enlMeas_le_enlRecMeas p m n j).trans (enlRecMeas_le_infoPiece p m n j g)

lemma infoPiece_mono (p : ℝ) (m n : ℕ) (j : Fin N) {g g' : ℕ} (hgg : g ≤ g') :
    infoPiece (N := N) p m n j g ≤ infoPiece (N := N) p m n j g' :=
  pieceMeas_mono (fun γ => recInfo_mono j hgg γ)

lemma infoPiece_le (p : ℝ) (m n : ℕ) (j : Fin N) (g : ℕ) :
    infoPiece (N := N) p m n j g ≤ (inferInstance : MeasurableSpace (Array N)) :=
  pieceMeas_le p m n _

/-- Every coordinate of walker `j` in the `g`-th enlargement sits at a site `≤ recVal + g`. -/
lemma recInfo_site_le {m : ℕ} (j : Fin N) (g : ℕ) {n : ℕ} (γ : Pref N n)
    {c : Fin N × ℤ × ℕ} (hc : c ∈ recInfo (N := N) m j g γ) (hj : c.1 = j) :
    c.2.1 ≤ recVal j γ + (g : ℤ) := by
  rcases Finset.mem_union.mp hc with hc | hc
  · rcases Finset.mem_union.mp hc with hc | hc
    · rw [mem_prefRead] at hc
      obtain ⟨t, ht, hx, -⟩ := hc
      rw [hj] at hx
      rw [← hx]
      have hle : ext γ t j ≤ recVal j γ :=
        Finset.le_sup' (fun s => ext γ s j) (Finset.mem_range.mpr (by omega))
      have hg0 : (0 : ℤ) ≤ (g : ℤ) := by exact_mod_cast Nat.zero_le g
      linarith
    · obtain ⟨k, hk, rfl⟩ := mem_recRow.mp hc
      simp only
      have hg0 : (0 : ℤ) ≤ (g : ℤ) := by exact_mod_cast Nat.zero_le g
      linarith
  · rw [Finset.mem_biUnion] at hc
    obtain ⟨h, hh, hc⟩ := hc
    obtain ⟨k, hk, rfl⟩ := mem_recRow.mp hc
    simp only
    have hlt : (h : ℤ) ≤ (g : ℤ) := by
      have hgg : (h : ℤ) ≤ (g : ℤ) := by exact_mod_cast (Finset.mem_Icc.mp hh).2
      linarith
    linarith

end Swarming.Enl
