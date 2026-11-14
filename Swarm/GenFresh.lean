/-
  **Generalized fresh-block cylinder law over an arbitrary finite environment.**

  `EnlFuture.enl_fresh_future_piece` gives the fresh-coordinate law on a piece
  `{path = γ}` with base information exactly the revealed set `prefRead n γ`.  That is not
  enough above a running record: at time `n` a walker may be sitting *at* the record site
  `M_n^j = x` with local time `≤ m-1`, in which case the mark coordinates `(j, x, k)`,
  `k ∈ {1,…,m-1}`, have **not** been read (`prefRead` only contains departures at times
  `< n`) but they are needed as part of the environment.  So the base information has to be
  enlarged by the record site's mark, and the independence statement must be available for
  an arbitrary finite environment `S ⊇ prefRead n γ`, not just for `prefRead n γ` itself.

  This file provides exactly that, with no conditional-expectation machinery:

  * `prefCyl` — the determining set in the finite product over `S`;
  * `measurableSet_prefCyl` — it is measurable;
  * `prefAgree_eq_prefCyl` — **the piece `{path = γ}` is a cylinder over `S`** whenever
    `prefRead n γ ⊆ S`.  This is the whole content of "coordinates outside the revealed set
    are not needed to decide the prefix";
  * `measurableSet_prefAgree_of_subset` — the piece is measurable for `cylAt S`;
  * `fresh_piece_of_subset` — **the generalized fresh-block law**
    `μ (piece ∩ B ∩ {U (α i) ∈ I i}) = (∏ i, |I i|) * μ (piece ∩ B)` for
    `B` measurable in `cylAt S`, an injective family `α` avoiding `S`, and arbitrary
    measurable boxes `I i`.  `enl_fresh_future_piece` is the special case `S = prefRead`;
  * `runMaxPref`, `runMax_eq_runMaxPref` — the running record of a prefix, and its
    identification with `runMax` of the trajectory on the piece;
  * `recEnv` — the **record environment** `prefRead n γ ∪ {(j, M_n^j, k) : 1 ≤ k ≤ m-1}`;
  * `measurableSet_recordMark` — the record site's mark belongs to `cylAt (recEnv …)`;
  * `notMem_recEnv_of_lt` — a site strictly above the record is fresh for the record
    environment (not just for `prefRead`);
  * `recEnv_fresh_siteMark_piece` / `recEnv_fresh_siteMark_real` — the site-mark law above
    the record **with the record mark included in the base information** (exact measure
    form and real form);
  * `recEnv_two_fresh_sites` — two successive above-record blocks: the first is absorbed
    into the environment, the second keeps the same multiplier (the induction step for an
    increasing environment enlargement);
  * `markCoords`, `measurableSet_siteMarks_cylAt`, `fresh_siteMarks_multi` — **finitely many
    fresh sites above the record at once**: for a finite set `F` of sites all strictly above
    the record, `μ (path = γ, B_j(x) for all x ∈ F) = ((1-p)^(m-1))^(#F) * μ (path = γ)`.
    This is the environment enlargement iterated, proved by induction over `F` using
    `fresh_piece_of_subset` with the environment `prefRead ∪ markCoords of the sites already
    added`;
  * `PiecewiseRecCyl`, `PiecewiseRecCyl.inter`, `piecewiseRecCyl_of_runMax` — sets determined
    piecewise by the record environment; **every event `{P (M_n^j)}` of the record alone is
    such a set** (so `{0 ≤ M_n^j}` can be kept as an explicit intersection);
  * `recMeas` — **the record-enlarged σ-algebra** at time `n` (piecewise `cylAt (recEnv …)`),
    with `recMeas_le` (inside the ambient σ-algebra), `enlMeas_le_recMeas` /
    `enlFilt_le_recMeas` (it contains the enlarged filtration), and
    `measurableSet_recordMark_recMeas` / `measurableSet_runMax_recMeas` (the record's mark and
    every record event are in it);
  * `recEnv_setIntegral_siteMark_enn` / `recEnv_setIntegral_siteMark` and their `recMeas`
    restatements — the conditional mass of a fresh mark at a site above the record, with the
    record mark allowed in the base information;
  * `recMeas_setIntegral_siteMark_succ_enn` / `recMeas_setIntegral_siteMark_succ` — **the same
    law at the random site `M_n^j + 1`**, which is strictly above the record on every path;
  * `siteMark_not_cylAt_prefRead_zero` — the record mark is *not* measurable for the old
    base at time `0`, so the enlargement is genuinely needed.

  No proof hole and no custom axiom.  Everything is stated on the actual trajectory
  `Swarming.Trajectory.trajectory` and the actual product measure `arrayMeasure N`.

  What this file does **not** do (see `REPORT.md`): it does not assemble a conditional
  expectation, does not prove the projected recursion `e_{g+1} = 1 + a (1 + e_g)`, and does not
  claim `Ballistic` or the occupation bound.
-/
import Swarm.EnlFuture
import Swarm.EnlLaw
import Swarm.UniformArray
import Swarm.Reveal

set_option linter.unusedVariables false
set_option warn.classDefReducibility false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory

variable {N : ℕ}

/-! ### Ambient measurability of a cylinder over an arbitrary finite set -/

/-- A set measurable in the coordinates of a finite set `S` is ambient measurable. -/
lemma measurableSet_of_cylAt {S : Finset (Fin N × ℤ × ℕ)} {B : Set (Array N)}
    (hB : MeasurableSet[cylAt (N := N) S] B) : MeasurableSet B := by
  obtain ⟨Bs, hBs, hBeq⟩ := MeasurableSpace.measurableSet_comap.1 hB
  rw [← hBeq]
  exact hBs.preimage (measurable_pi_lambda _ fun c =>
    measurable_pi_apply (X := fun _ : Fin N × ℤ × ℕ => ℝ) (a := (c : Fin N × ℤ × ℕ)))

/-! ### The piece is a cylinder over any environment containing the revealed set -/

/-- The set of value vectors on `S` that produce the prefix `γ` (with the coordinates
outside `S` filled by `0`). -/
noncomputable def prefCyl (p : ℝ) (m : ℕ) {n : ℕ} (γ : Pref N n)
    (S : Finset (Fin N × ℤ × ℕ)) : Set (S → ℝ) :=
  {g : S → ℝ | ∀ t : Fin (n + 1), (trajectory p m (extendArr (S := S) g) t.1).pos = γ t}

lemma measurableSet_prefCyl (p : ℝ) (m : ℕ) {n : ℕ} (γ : Pref N n)
    (S : Finset (Fin N × ℤ × ℕ)) : MeasurableSet (prefCyl (N := N) p m γ S) := by
  have hsingle : ∀ (t : Fin (n + 1)) (i : Fin N), Measurable fun g : S → ℝ =>
      (trajectory p m (extendArr (S := S) g) t.1).pos i := by
    intro t i
    have h1 : Measurable fun g : S → ℝ => extendArr (S := S) g :=
      measurable_pi_iff.2 fun c => measurable_extendArr (S := S) c
    exact ((Swarming.Fair.measurable_trajectory p m t.1).1 i).comp h1
  have hset : prefCyl (N := N) p m γ S = ⋂ t : Fin (n + 1), {g : S → ℝ |
      (trajectory p m (extendArr (S := S) g) t.1).pos = γ t} := by
    ext g
    simp only [prefCyl, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [hset]
  exact MeasurableSet.iInter fun t =>
    (measurable_pi_iff.2 (hsingle t)) (measurableSet_singleton _)

/-- **The prefix piece is a cylinder over `S`** as soon as `S` contains the revealed set:
the trajectory up to time `n` is a function of the revealed coordinates only. -/
lemma prefAgree_eq_prefCyl (p : ℝ) (m : ℕ) {n : ℕ} (γ : Pref N n)
    {S : Finset (Fin N × ℤ × ℕ)} (hS : prefRead n γ ⊆ S) :
    prefAgree p m γ = (fun U (c : S) => U c) ⁻¹' prefCyl (N := N) p m γ S := by
  ext U
  simp only [Set.mem_preimage, prefCyl, Set.mem_ofPred_eq, prefAgree]
  constructor
  · intro hU t
    have hagree : ∀ c : Fin N × ℤ × ℕ, c ∈ prefRead n γ →
        U c = extendArr (S := S) (fun c' : S => U c') c := by
      intro c hc
      rw [extendArr_of_mem (hS hc)]
    have hdep := traj_depends_on_prefRead p m γ U (extendArr (S := S) fun c' : S => U c')
      hU hagree
    rw [← hU t]
    exact congrArg (fun s : WalkState N => s.pos) (hdep t.1 (by omega)).symm
  · intro hg t
    have hdep := traj_depends_on_prefRead p m γ (extendArr (S := S) fun c' : S => U c') U
      (fun t => hg t)
      (fun c hc => (extendArr_of_mem (S := S) (g := fun c' : S => U c') (hS hc)).trans (by simp))
    rw [← hg t]
    exact congrArg (fun s : WalkState N => s.pos) (hdep t.1 (by omega)).symm

/-- The piece `{path = γ}` is measurable for the σ-algebra generated by any environment
`S` containing the revealed set. -/
lemma measurableSet_prefAgree_of_subset (p : ℝ) (m : ℕ) {n : ℕ} (γ : Pref N n)
    {S : Finset (Fin N × ℤ × ℕ)} (hS : prefRead n γ ⊆ S) :
    MeasurableSet[cylAt (N := N) S] (prefAgree p m γ) := by
  rw [prefAgree_eq_prefCyl p m γ hS]
  exact MeasurableSpace.measurableSet_comap.2
    ⟨prefCyl (N := N) p m γ S, measurableSet_prefCyl p m γ S, rfl⟩

/-! ### The generalized fresh-block law -/

/-- **Fresh block over an arbitrary finite environment.**  On the piece `{path = γ}`, an
event `B` determined by the coordinates in a finite set `S ⊇ prefRead n γ` is independent of
every injective finite family of coordinates avoiding `S`, and those coordinates have the
product uniform law.  No independence of the future array from the past is assumed: only the
finite family matters. -/
theorem fresh_piece_of_subset (p : ℝ) (m : ℕ) (n : ℕ) (γ : Pref N n)
    (S : Finset (Fin N × ℤ × ℕ)) (hS : prefRead n γ ⊆ S)
    {B : Set (Array N)} (hB : MeasurableSet[cylAt (N := N) S] B)
    {ι : Type*} [Fintype ι] (α : ι → Fin N × ℤ × ℕ) (hαinj : Function.Injective α)
    (hfresh : ∀ i, α i ∉ S) (I : ι → Set ℝ) (hI : ∀ i, MeasurableSet (I i)) :
    arrayMeasure N (prefAgree p m γ ∩ B ∩ ⋂ i, {U : Array N | U (α i) ∈ I i}) =
      (∏ i, uniform01 (I i)) * arrayMeasure N (prefAgree p m γ ∩ B) := by
  classical
  obtain ⟨Bs, hBs, hBeq⟩ := MeasurableSpace.measurableSet_comap.1 hB
  set A : Set (S → ℝ) := prefCyl (N := N) p m γ S ∩ Bs with hA
  have hAmeas : MeasurableSet A := (measurableSet_prefCyl p m γ S).inter hBs
  have hbase : prefAgree p m γ ∩ B = (fun U (c : S) => U c) ⁻¹' A := by
    rw [← hBeq, prefAgree_eq_prefCyl p m γ hS]
    ext U
    simp only [Set.mem_inter_iff, Set.mem_preimage, hA]
  have hfull : prefAgree p m γ ∩ B ∩ ⋂ i, {U : Array N | U (α i) ∈ I i} =
      (fun U (c : S) => U c) ⁻¹' A ∩ ⋂ i, (fun U : Array N => U (α i)) ⁻¹' I i := by
    rw [hbase]
    ext U
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_preimage]
  have hind := SwarmIID.indep_fresh_finset (μ := arrayMeasure N) (array_independent N)
    (fun c => measurable_pi_apply c) hαinj hfresh A hAmeas I hI
  have hprod : ∀ i, arrayMeasure N ((fun U : Array N => U (α i)) ⁻¹' I i) = uniform01 (I i) :=
    fun i => arrayMeasure_preimage_set N (α i) (I i) (hI i)
  rw [hfull, hind, hbase]
  simp only [hprod]
  rw [mul_comm]

/-- Site-mark event as a box condition on the site's first `m-1` coordinates. -/
lemma siteMark_eq_box (p : ℝ) (m : ℕ) (j : Fin N) (x : ℤ) :
    {U : Array N | SiteMark p m U j x} = ⋂ k ∈ Finset.Icc 1 (m - 1),
      {U : Array N | U (j, x, k) ∈ Set.Ioi p} := by
  ext U
  simp only [SiteMark, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_Ioi]

lemma siteMark_box_inter (p : ℝ) (m : ℕ) (j : Fin N) (x : ℤ) (B : Set (Array N)) :
    B ∩ {U : Array N | SiteMark p m U j x} =
      B ∩ ⋂ i : ↥(Finset.Icc 1 (m - 1)),
        {U : Array N | U (j, x, i.1) ∈ Set.Ioi p} := by
  ext U
  simp only [SiteMark, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_Ioi]
  constructor
  · rintro ⟨hB, hmark⟩
    exact ⟨hB, fun c => hmark c.1 c.2⟩
  · rintro ⟨hB, hmark⟩
    exact ⟨hB, fun k hk => hmark ⟨k, hk⟩⟩

/-- A product of `m-1` copies of the site-mark box mass. -/
lemma prod_uniform01_Ioi (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (m : ℕ) :
    (∏ _i : ↥(Finset.Icc 1 (m - 1)), uniform01 (Set.Ioi p)) =
      (ENNReal.ofReal (1 - p)) ^ (m - 1) := by
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe, uniform01_Ioi hp0 hp1]
  simp

/-- The site mark at `x` is measurable in any environment containing the site's first
`m-1` coordinates. -/
lemma measurableSet_siteMark_cylAt (p : ℝ) (m : ℕ) {S : Finset (Fin N × ℤ × ℕ)}
    (j : Fin N) (x : ℤ) (hS : ∀ k ∈ Finset.Icc 1 (m - 1), (j, x, k) ∈ S) :
    MeasurableSet[cylAt (N := N) S] {U : Array N | SiteMark p m U j x} := by
  rw [siteMark_eq_box]
  exact Finset.measurableSet_biInter _ fun k hk =>
    measurableSet_cylAt_of_mem (hS k hk) measurableSet_Ioi

/-! ### The running record of a prefix -/

/-- The running maximum `M_n^j = max_{0 ≤ t ≤ n} X_t^j` of a position prefix. -/
noncomputable def runMaxPref {n : ℕ} (γ : Pref N n) (j : Fin N) : ℤ :=
  (Finset.range (n + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩
    (fun t => ext γ t j)

lemma ext_le_runMaxPref {n : ℕ} (γ : Pref N n) (j : Fin N) {t : ℕ} (ht : t < n + 1) :
    ext γ t j ≤ runMaxPref (N := N) γ j :=
  Finset.le_sup' (fun s => ext γ s j) (Finset.mem_range.mpr ht)

/-- On the piece `{path = γ}` the running record is the prefix's running record. -/
lemma runMax_eq_runMaxPref (p : ℝ) (m : ℕ) {n : ℕ} {γ : Pref N n} {U : Array N}
    (hU : U ∈ prefAgree p m γ) (j : Fin N) :
    runMax p m U j n = runMaxPref (N := N) γ j := by
  have hH : (Finset.range (n + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩
  have hcongr : ∀ t ∈ Finset.range (n + 1), (trajectory p m U t).pos j = ext γ t j := by
    intro t ht
    exact (ext_prefOf_of_mem hU (by have := Finset.mem_range.mp ht; omega) j).symm
  unfold runMax runMaxPref
  exact Finset.sup'_congr hH rfl hcongr

/-! ### The record environment -/

/-- **The record environment of a prefix**: the coordinates revealed before time `n`
together with the mark coordinates of the record site `M_n^j`.  This is the base
information that (unlike `prefRead n γ` alone) contains the record's mark. -/
noncomputable def recEnv (m : ℕ) {n : ℕ} (γ : Pref N n) (j : Fin N) :
    Finset (Fin N × ℤ × ℕ) :=
  prefRead n γ ∪ (Finset.Icc 1 (m - 1)).image (fun k => (j, runMaxPref (N := N) γ j, k))

lemma prefRead_subset_recEnv (m : ℕ) {n : ℕ} (γ : Pref N n) (j : Fin N) :
    prefRead n γ ⊆ recEnv (N := N) m γ j :=
  Finset.subset_union_left

lemma record_coord_mem_recEnv (m : ℕ) {n : ℕ} (γ : Pref N n) (j : Fin N) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 (m - 1)) :
    (j, runMaxPref (N := N) γ j, k) ∈ recEnv (N := N) m γ j :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k, hk, rfl⟩)

/-- The piece is measurable for the record environment. -/
lemma measurableSet_prefAgree_recEnv (p : ℝ) (m : ℕ) {n : ℕ} (γ : Pref N n) (j : Fin N) :
    MeasurableSet[cylAt (N := N) (recEnv (N := N) m γ j)] (prefAgree p m γ) :=
  measurableSet_prefAgree_of_subset p m γ (prefRead_subset_recEnv m γ j)

/-- **The record site's mark belongs to the record environment.** -/
lemma measurableSet_recordMark (p : ℝ) (m : ℕ) {n : ℕ} (γ : Pref N n) (j : Fin N) :
    MeasurableSet[cylAt (N := N) (recEnv (N := N) m γ j)]
      {U : Array N | SiteMark p m U j (runMaxPref (N := N) γ j)} :=
  measurableSet_siteMark_cylAt p m j _ (fun k hk => record_coord_mem_recEnv m γ j hk)

/-- A site **strictly above the record** is unread *and* its coordinates are not the record
site's, so it is fresh for the whole record environment. -/
lemma notMem_recEnv_of_lt (m : ℕ) {n : ℕ} (γ : Pref N n) (j : Fin N) {x : ℤ}
    (hx : runMaxPref (N := N) γ j < x) (k : ℕ) :
    (j, x, k) ∉ recEnv (N := N) m γ j := by
  intro hmem
  rw [recEnv, Finset.mem_union] at hmem
  rcases hmem with h | h
  · refine notMem_prefRead_of_le (x := x) γ j (runMaxPref (N := N) γ j) ?_ hx k h
    intro t
    have h1 : ext γ (t : ℕ) j = γ t j := ext_of_lt γ (by omega) j
    rw [← h1]
    exact ext_le_runMaxPref γ j (by omega)
  · obtain ⟨k', -, hk'⟩ := Finset.mem_image.mp h
    have h2 : runMaxPref (N := N) γ j = x := by
      have := congrArg (fun c : Fin N × ℤ × ℕ => c.2.1) hk'
      simpa using this
    omega

/-! ### The fresh site-mark law above the record, with the record mark known -/

/-- **Site-mark law at a fresh site above the record, conditional on base information that
may contain the record mark.**  `B` is any event of the record environment `recEnv`;
`x` is strictly above the record, so its coordinates are fresh. -/
theorem recEnv_fresh_siteMark_piece (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (m : ℕ) {n : ℕ}
    (γ : Pref N n) (j : Fin N) {x : ℤ} (hx : runMaxPref (N := N) γ j < x)
    {B : Set (Array N)} (hB : MeasurableSet[cylAt (N := N) (recEnv (N := N) m γ j)] B) :
    arrayMeasure N (prefAgree p m γ ∩ B ∩ {U : Array N | SiteMark p m U j x}) =
      (ENNReal.ofReal (1 - p)) ^ (m - 1) * arrayMeasure N (prefAgree p m γ ∩ B) := by
  have hbase := fresh_piece_of_subset p m n γ (recEnv (N := N) m γ j)
    (prefRead_subset_recEnv m γ j) hB
    (α := fun k : ↥(Finset.Icc 1 (m - 1)) => (j, x, k.1))
    (by
      intro a b hab
      have hv := congrArg (fun c : Fin N × ℤ × ℕ => c.2.2) hab
      exact Subtype.ext hv)
    (fun k => notMem_recEnv_of_lt m γ j hx k.1)
    (fun _ => Set.Ioi p) (fun _ => measurableSet_Ioi)
  rw [siteMark_box_inter p m j x (prefAgree p m γ ∩ B), ← prod_uniform01_Ioi p hp0 hp1 m]
  exact hbase

/-- Real-measure form of the same law, ready for a conditional-expectation assembly. -/
theorem recEnv_fresh_siteMark_real (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (m : ℕ) {n : ℕ}
    (γ : Pref N n) (j : Fin N) {x : ℤ} (hx : runMaxPref (N := N) γ j < x)
    {B : Set (Array N)} (hB : MeasurableSet[cylAt (N := N) (recEnv (N := N) m γ j)] B) :
    (arrayMeasure N).real (prefAgree p m γ ∩ B ∩ {U : Array N | SiteMark p m U j x}) =
      (1 - p) ^ (m - 1) * (arrayMeasure N).real (prefAgree p m γ ∩ B) := by
  have h := recEnv_fresh_siteMark_piece p hp0 hp1 m γ j hx hB
  have hnonneg : (0 : ℝ) ≤ 1 - p := by linarith
  calc
    (arrayMeasure N).real (prefAgree p m γ ∩ B ∩ {U : Array N | SiteMark p m U j x}) =
        (arrayMeasure N (prefAgree p m γ ∩ B ∩ {U : Array N | SiteMark p m U j x})).toReal :=
      rfl
    _ = ((ENNReal.ofReal (1 - p)) ^ (m - 1) * arrayMeasure N (prefAgree p m γ ∩ B)).toReal :=
      congrArg ENNReal.toReal h
    _ = (1 - p) ^ (m - 1) * (arrayMeasure N).real (prefAgree p m γ ∩ B) := by
      rw [ENNReal.toReal_mul, ← ENNReal.ofReal_pow hnonneg,
        ENNReal.toReal_ofReal (pow_nonneg hnonneg _)]
      rfl

/-- **The record mark as base information**: knowing the record site's mark does not change
the multiplier at a fresh site above the record. -/
theorem recordMark_and_fresh_above (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (m : ℕ) {n : ℕ}
    (γ : Pref N n) (j : Fin N) {x : ℤ} (hx : runMaxPref (N := N) γ j < x) :
    arrayMeasure N (prefAgree p m γ
        ∩ {U : Array N | SiteMark p m U j (runMaxPref (N := N) γ j)}
        ∩ {U : Array N | SiteMark p m U j x}) =
      (ENNReal.ofReal (1 - p)) ^ (m - 1) *
        arrayMeasure N (prefAgree p m γ
          ∩ {U : Array N | SiteMark p m U j (runMaxPref (N := N) γ j)}) :=
  recEnv_fresh_siteMark_piece p hp0 hp1 m γ j hx (measurableSet_recordMark p m γ j)

/-! ### Successive fresh sites: the environment enlargement step -/

lemma notMem_recEnv_succ_of_lt (m : ℕ) {n : ℕ} (γ : Pref N n) (j : Fin N) {x₁ x₂ : ℤ}
    (hx₂ : runMaxPref (N := N) γ j < x₂) (hne : x₁ ≠ x₂) (k : ℕ) :
    (j, x₂, k) ∉ recEnv (N := N) m γ j ∪
      (Finset.Icc 1 (m - 1)).image (fun k' => (j, x₁, k')) := by
  intro hmem
  rw [Finset.mem_union] at hmem
  rcases hmem with h | h
  · exact notMem_recEnv_of_lt m γ j hx₂ k h
  · obtain ⟨k', -, hk'⟩ := Finset.mem_image.mp h
    have h2 : x₁ = x₂ := by
      have := congrArg (fun c : Fin N × ℤ × ℕ => c.2.1) hk'
      simpa using this
    exact hne h2

/-- **Two successive above-record blocks.**  After absorbing the first site's mark into the
environment, the second site is still fresh and keeps the same multiplier
`(1-p)^(m-1)`.  This is the induction step of the increasing environment enlargement. -/
theorem recEnv_two_fresh_sites (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (m : ℕ) {n : ℕ}
    (γ : Pref N n) (j : Fin N) {x₁ x₂ : ℤ}
    (hx₁ : runMaxPref (N := N) γ j < x₁) (hx₂ : runMaxPref (N := N) γ j < x₂)
    (hne : x₁ ≠ x₂) :
    arrayMeasure N (prefAgree p m γ ∩ {U : Array N | SiteMark p m U j x₁}
        ∩ {U : Array N | SiteMark p m U j x₂}) =
      ((ENNReal.ofReal (1 - p)) ^ (m - 1)) ^ 2 * arrayMeasure N (prefAgree p m γ) := by
  have hS : prefRead n γ ⊆ recEnv (N := N) m γ j ∪
      (Finset.Icc 1 (m - 1)).image (fun k' => (j, x₁, k')) :=
    (prefRead_subset_recEnv m γ j).trans (Finset.subset_union_left)
  have hb₁ : MeasurableSet[cylAt (N := N) (recEnv (N := N) m γ j ∪
      (Finset.Icc 1 (m - 1)).image (fun k' => (j, x₁, k')))]
      {U : Array N | SiteMark p m U j x₁} :=
    measurableSet_siteMark_cylAt p m j x₁
      (fun k hk => Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨k, hk, rfl⟩))
  have hstep := fresh_piece_of_subset p m n γ
    (recEnv (N := N) m γ j ∪ (Finset.Icc 1 (m - 1)).image (fun k' => (j, x₁, k')))
    hS hb₁
    (α := fun k : ↥(Finset.Icc 1 (m - 1)) => (j, x₂, k.1))
    (by
      intro a b hab
      have hv := congrArg (fun c : Fin N × ℤ × ℕ => c.2.2) hab
      exact Subtype.ext hv)
    (fun k => notMem_recEnv_succ_of_lt m γ j hx₂ hne k.1)
    (fun _ => Set.Ioi p) (fun _ => measurableSet_Ioi)
  have hone := recEnv_fresh_siteMark_piece p hp0 hp1 m γ j hx₁
    (B := Set.univ) MeasurableSet.univ
  simp only [Set.inter_univ] at hone
  rw [siteMark_box_inter p m j x₂ (prefAgree p m γ ∩ {U : Array N | SiteMark p m U j x₁})]
  rw [hstep, hone, prod_uniform01_Ioi p hp0 hp1 m, pow_two, mul_assoc]


/-! ### Finitely many fresh sites above the record at once -/

/-- The site mark at `x` as the intersection of the coordinate boxes (subtype-indexed form
used by the fresh-block law). -/
lemma siteMark_eq_iInter_subtype (p : ℝ) (m : ℕ) (j : Fin N) (x : ℤ) :
    {U : Array N | SiteMark p m U j x} =
      ⋂ i : ↥(Finset.Icc 1 (m - 1)), {U : Array N | U (j, x, i.1) ∈ Set.Ioi p} := by
  ext U
  simp only [SiteMark, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_Ioi]
  constructor
  · intro h i
    exact h i.1 i.2
  · intro h k hk
    exact h ⟨k, hk⟩

/-- The mark coordinates of a finite set of sites. -/
noncomputable def markCoords (m : ℕ) (j : Fin N) (F : Finset ℤ) :
    Finset (Fin N × ℤ × ℕ) :=
  F.biUnion fun x => (Finset.Icc 1 (m - 1)).image (fun k => (j, x, k))

lemma mem_markCoords {m : ℕ} {j : Fin N} {F : Finset ℤ} {x : ℤ} {k : ℕ}
    (hx : x ∈ F) (hk : k ∈ Finset.Icc 1 (m - 1)) :
    (j, x, k) ∈ markCoords (N := N) m j F :=
  Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image.mpr ⟨k, hk, rfl⟩⟩

/-- The conjunction of the site marks of a finite set of sites is measurable in any
environment containing their mark coordinates. -/
lemma measurableSet_siteMarks_cylAt (p : ℝ) (m : ℕ) {S : Finset (Fin N × ℤ × ℕ)}
    (j : Fin N) (F : Finset ℤ) (hS : ∀ x ∈ F, ∀ k ∈ Finset.Icc 1 (m - 1), (j, x, k) ∈ S) :
    MeasurableSet[cylAt (N := N) S] (⋂ x ∈ F, {U : Array N | SiteMark p m U j x}) := by
  have hset : (⋂ x ∈ F, {U : Array N | SiteMark p m U j x}) =
      ⋂ x ∈ F, ⋂ k ∈ Finset.Icc 1 (m - 1), {U : Array N | U (j, x, k) ∈ Set.Ioi p} := by
    simp only [siteMark_eq_box]
  rw [hset]
  exact Finset.measurableSet_biInter _ fun x hx =>
    Finset.measurableSet_biInter _ fun k hk =>
      measurableSet_cylAt_of_mem (hS x hx k hk) measurableSet_Ioi

/-- **Finitely many fresh marks above the record.**  For a finite set `F` of sites, all
strictly above the record, the marks at all of them are jointly independent of the record
environment with the constant multiplier `(1-p)^(m-1)` per site:

  `μ (path = γ, B_j(x) for all x ∈ F) = ((1-p)^(m-1))^(#F) * μ (path = γ)`.

This is the general form of the increasing environment enlargement: each site is added to the
base environment after the previous one, using `fresh_piece_of_subset` with environment
`prefRead n γ ∪ (mark coordinates of the sites already added)`. -/
theorem fresh_siteMarks_multi (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (m : ℕ) {n : ℕ}
    (γ : Pref N n) (j : Fin N) (F : Finset ℤ)
    (hF : ∀ x ∈ F, runMaxPref (N := N) γ j < x) :
    arrayMeasure N (prefAgree p m γ ∩ ⋂ x ∈ F, {U : Array N | SiteMark p m U j x}) =
      ((ENNReal.ofReal (1 - p)) ^ (m - 1)) ^ F.card * arrayMeasure N (prefAgree p m γ) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert x F' hx ih =>
    have hxr : runMaxPref (N := N) γ j < x :=
      hF x (Finset.mem_insert_self x F')
    have hF' : ∀ y ∈ F', runMaxPref (N := N) γ j < y :=
      fun y hy => hF y (Finset.mem_insert_of_mem hy)
    have hIH := ih hF'
    set B : Set (Array N) := ⋂ y ∈ F', {U : Array N | SiteMark p m U j y} with hBdef
    set S : Finset (Fin N × ℤ × ℕ) := prefRead n γ ∪ markCoords (N := N) m j F' with hSdef
    have hSsub : prefRead n γ ⊆ S := Finset.subset_union_left
    have hB : MeasurableSet[cylAt (N := N) S] B :=
      measurableSet_siteMarks_cylAt p m j F'
        (fun y hy k hk => Finset.mem_union_right _ (mem_markCoords hy hk))
    have hfresh : ∀ i : ↥(Finset.Icc 1 (m - 1)), (j, x, i.1) ∉ S := by
      intro i hmem
      rw [hSdef, Finset.mem_union] at hmem
      rcases hmem with h | h
      · refine notMem_prefRead_of_le (x := x) γ j (runMaxPref (N := N) γ j) (fun t => ?_) hxr i.1 h
        have h1 : ext γ (t : ℕ) j = γ t j := ext_of_lt γ (by omega) j
        rw [← h1]
        exact ext_le_runMaxPref γ j (by omega)
      · obtain ⟨y, hy, hmem⟩ := Finset.mem_biUnion.mp h
        obtain ⟨k'', -, hk''⟩ := Finset.mem_image.mp hmem
        have hxy : y = x := by
          have := congrArg (fun c : Fin N × ℤ × ℕ => c.2.1) hk''
          simpa using this
        exact hx (hxy ▸ hy)
    have hmain := fresh_piece_of_subset p m n γ S hSsub hB
      (α := fun i : ↥(Finset.Icc 1 (m - 1)) => (j, x, i.1))
      (by
        intro a b hab
        have hv := congrArg (fun c : Fin N × ℤ × ℕ => c.2.2) hab
        exact Subtype.ext hv)
      hfresh (fun _ => Set.Ioi p) (fun _ => measurableSet_Ioi)
    have hstep : prefAgree p m γ ∩ B ∩
        (⋂ i : ↥(Finset.Icc 1 (m - 1)),
          {U : Array N | U (j, x, i.1) ∈ Set.Ioi p}) =
        prefAgree p m γ ∩ ⋂ y ∈ insert x F', {U : Array N | SiteMark p m U j y} := by
      rw [← siteMark_eq_iInter_subtype p m j x, Finset.set_biInter_insert]
      rw [Set.inter_assoc, Set.inter_comm B]
    rw [hstep, prod_uniform01_Ioi p hp0 hp1 m] at hmain
    rw [hmain, hIH, Finset.card_insert_of_notMem hx, pow_succ]
    ring_nf

/-! ### Sets determined piecewise by the record environment -/

/-- **A set determined piecewise by the record environment**: on each piece `{path = γ}` it
agrees with an event of `cylAt (recEnv m γ j)`, i.e. of the revealed coordinates together
with the record site's mark.  This is the hypothesis a conditional-expectation assembly needs;
it does not presuppose any σ-algebra instance. -/
def PiecewiseRecCyl (p : ℝ) (m : ℕ) (n : ℕ) (j : Fin N) (A : Set (Array N)) : Prop :=
  ∀ γ : Pref N n, ∃ B : Set (Array N),
    MeasurableSet[cylAt (N := N) (recEnv (N := N) m γ j)] B ∧
      prefAgree p m γ ∩ A = prefAgree p m γ ∩ B

lemma PiecewiseRecCyl.univ (p : ℝ) (m n : ℕ) (j : Fin N) :
    PiecewiseRecCyl (N := N) p m n j Set.univ := by
  intro γ
  have hU : MeasurableSet[cylAt (N := N) (recEnv (N := N) m γ j)] (Set.univ : Set (Array N)) :=
    MeasurableSet.univ
  exact ⟨Set.univ, hU, rfl⟩

lemma PiecewiseRecCyl.inter {p : ℝ} {m n : ℕ} {j : Fin N} {A C : Set (Array N)}
    (hA : PiecewiseRecCyl (N := N) p m n j A)
    (hC : PiecewiseRecCyl (N := N) p m n j C) :
    PiecewiseRecCyl (N := N) p m n j (A ∩ C) := by
  intro γ
  obtain ⟨B, hB, hEq⟩ := hA γ
  obtain ⟨D, hD, hEqD⟩ := hC γ
  refine ⟨B ∩ D, hB.inter hD, ?_⟩
  ext U
  constructor
  · rintro ⟨hp, hAU, hCU⟩
    exact ⟨hp, (hEq ▸ show U ∈ prefAgree p m γ ∩ A from ⟨hp, hAU⟩).2,
      (hEqD ▸ show U ∈ prefAgree p m γ ∩ C from ⟨hp, hCU⟩).2⟩
  · rintro ⟨hp, hb, hd⟩
    exact ⟨hp, (hEq ▸ show U ∈ prefAgree p m γ ∩ B from ⟨hp, hb⟩).2,
      (hEqD ▸ show U ∈ prefAgree p m γ ∩ D from ⟨hp, hd⟩).2⟩

/-- Any event that, on a piece, is a condition on the running record alone is determined
piecewise by the record environment: on `{path = γ}` the record is the prefix record
`runMaxPref γ j`, so the event is either the whole piece or empty.  This covers in particular
the eventual-nonnegativity event `0 ≤ M_n^j` used to turn record indices into naturals. -/
lemma piecewiseRecCyl_of_runMax (p : ℝ) (m n : ℕ) (j : Fin N) (P : ℤ → Prop) :
    PiecewiseRecCyl (N := N) p m n j {U : Array N | P (runMax p m U j n)} := by
  classical
  intro γ
  by_cases h : P (runMaxPref (N := N) γ j)
  · have hU : MeasurableSet[cylAt (N := N) (recEnv (N := N) m γ j)]
        (Set.univ : Set (Array N)) := MeasurableSet.univ
    refine ⟨Set.univ, hU, ?_⟩
    rw [Set.inter_univ]
    ext U
    constructor
    · rintro ⟨hp, -⟩
      exact hp
    · intro hp
      refine ⟨hp, ?_⟩
      show P (runMax p m U j n)
      rw [runMax_eq_runMaxPref p m hp j]
      exact h
  · refine ⟨(∅ : Set (Array N)),
      (cylAt (N := N) (recEnv (N := N) m γ j)).measurableSet_empty, ?_⟩
    rw [Set.inter_empty, Set.eq_empty_iff_forall_notMem]
    rintro U ⟨hp, hP⟩
    have hP' : P (runMax p m U j n) := hP
    rw [runMax_eq_runMaxPref p m hp j] at hP'
    exact h hP'

/-- The record is a function of the record environment on each piece, so the
eventual-nonnegativity event `0 ≤ M_n^j` is determined piecewise by it. -/
lemma piecewiseRecCyl_nonneg_runMax (p : ℝ) (m n : ℕ) (j : Fin N) :
    PiecewiseRecCyl (N := N) p m n j {U : Array N | 0 ≤ runMax p m U j n} :=
  piecewiseRecCyl_of_runMax p m n j (fun x => 0 ≤ x)

/-- **Conditional site-mark mass over the record-enlarged environment.**  For a set `A`
determined piecewise by the record environment and contained in the strict above-record event
`{M_n^j < x}`, the fresh site rescales by `(1-p)^(m-1)`:

  `μ.real (A ∩ {B_j(x)}) = (1-p)^(m-1) * μ.real A`.

Unlike `enl_setIntegral_siteMark_above_runMax`, the base information here may contain the
record site's own mark, which is exactly what the record edge requires.  The above-record
restriction `A ⊆ {M_n^j < x}` is preserved, not dropped. -/
theorem recEnv_setIntegral_siteMark_enn (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (m : ℕ) (n : ℕ) (j : Fin N) (x : ℤ) {A : Set (Array N)}
    (hA : PiecewiseRecCyl (N := N) p m n j A)
    (hAx : A ⊆ {U : Array N | runMax p m U j n < x}) :
    arrayMeasure N (A ∩ {U : Array N | SiteMark p m U j x}) =
      (ENNReal.ofReal (1 - p)) ^ (m - 1) * arrayMeasure N A := by
  classical
  choose B hB hEq using fun γ => hA γ
  have hbase : ∀ γ : Pref N n, MeasurableSet (prefAgree p m γ ∩ B γ) :=
    fun γ => (measurableSet_prefAgree_ambient p m γ).inter (measurableSet_of_cylAt (hB γ))
  have hGunion : A = ⋃ γ : Pref N n, prefAgree p m γ ∩ B γ := by
    ext U
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      refine ⟨prefOf p m n U, prefAgree_prefOf U, ?_⟩
      have hh : U ∈ prefAgree p m (prefOf p m n U) ∩ A := ⟨prefAgree_prefOf U, h⟩
      rw [hEq (prefOf p m n U)] at hh
      exact hh.2
    · rintro ⟨γ, h1, h2⟩
      have hh : U ∈ prefAgree p m γ ∩ A := by rw [hEq γ]; exact ⟨h1, h2⟩
      exact hh.2
  have hdisj : Pairwise (fun γ γ' : Pref N n =>
      Disjoint (prefAgree p m γ ∩ B γ) (prefAgree p m γ' ∩ B γ')) := by
    intro γ γ' hne
    rw [Set.disjoint_left]
    rintro U ⟨h1, -⟩ ⟨h2, -⟩
    exact hne (by funext t; rw [← h1 t, ← h2 t])
  have hdisjMark : Pairwise (fun γ γ' : Pref N n =>
      Disjoint ((prefAgree p m γ ∩ B γ) ∩ {U : Array N | SiteMark p m U j x})
        ((prefAgree p m γ' ∩ B γ') ∩ {U : Array N | SiteMark p m U j x})) := by
    intro γ γ' hne
    exact (hdisj hne).mono Set.inter_subset_left Set.inter_subset_left
  have hmark : ∀ γ : Pref N n,
      arrayMeasure N ((prefAgree p m γ ∩ B γ) ∩ {U : Array N | SiteMark p m U j x}) =
        (ENNReal.ofReal (1 - p)) ^ (m - 1) * arrayMeasure N (prefAgree p m γ ∩ B γ) := by
    intro γ
    by_cases hpref : prefAgree p m γ ∩ B γ = ∅
    · simp [hpref]
    · obtain ⟨V, hV⟩ := Set.nonempty_iff_ne_empty.mpr hpref
      have hVA : V ∈ A := by
        have hh : V ∈ prefAgree p m γ ∩ A := by rw [hEq γ]; exact hV
        exact hh.2
      have hxV : runMax p m V j n < x := hAx hVA
      have hx' : runMaxPref (N := N) γ j < x := by
        rw [← runMax_eq_runMaxPref p m hV.1 j]
        exact hxV
      have hpiece := recEnv_fresh_siteMark_piece (N := N) p hp0 hp1 m γ j hx' (hB γ)
      simpa only [Set.inter_assoc] using hpiece
  have hlhs : arrayMeasure N (A ∩ {U : Array N | SiteMark p m U j x}) =
      ∑' γ : Pref N n, (ENNReal.ofReal (1 - p)) ^ (m - 1) *
        arrayMeasure N (prefAgree p m γ ∩ B γ) := by
    have hunion : A ∩ {U : Array N | SiteMark p m U j x} = ⋃ γ : Pref N n,
        (prefAgree p m γ ∩ B γ) ∩ {U : Array N | SiteMark p m U j x} := by
      conv_lhs => rw [hGunion]
      rw [Set.iUnion_inter]
    rw [hunion, measure_iUnion hdisjMark (fun γ =>
      (hbase γ).inter (measurableSet_siteMark_array p m j x))]
    exact tsum_congr hmark
  rw [hlhs, ENNReal.tsum_mul_left]
  rw [← measure_iUnion hdisj hbase, hGunion]

/-- Real-measure form of `recEnv_setIntegral_siteMark_enn`. -/
theorem recEnv_setIntegral_siteMark (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (m : ℕ) (n : ℕ) (j : Fin N) (x : ℤ) {A : Set (Array N)}
    (hA : PiecewiseRecCyl (N := N) p m n j A)
    (hAx : A ⊆ {U : Array N | runMax p m U j n < x}) :
    (arrayMeasure N).real (A ∩ {U : Array N | SiteMark p m U j x}) =
      (1 - p) ^ (m - 1) * (arrayMeasure N).real A := by
  have hreal := recEnv_setIntegral_siteMark_enn p hp0 hp1 m n j x hA hAx
  have hreal' : ENNReal.toReal (arrayMeasure N (A ∩ {U : Array N | SiteMark p m U j x})) =
      ENNReal.toReal ((ENNReal.ofReal (1 - p)) ^ (m - 1) * arrayMeasure N A) :=
    congrArg ENNReal.toReal hreal
  calc
    (arrayMeasure N).real (A ∩ {U : Array N | SiteMark p m U j x}) =
        ENNReal.toReal (arrayMeasure N (A ∩ {U : Array N | SiteMark p m U j x})) := rfl
    _ = ((ENNReal.ofReal (1 - p)) ^ (m - 1) * arrayMeasure N A).toReal := hreal'
    _ = (1 - p) ^ (m - 1) * (arrayMeasure N).real A := by
      have hnonneg : 0 ≤ 1 - p := by linarith
      rw [ENNReal.toReal_mul, ← ENNReal.ofReal_pow hnonneg,
        ENNReal.toReal_ofReal (pow_nonneg hnonneg _)]
      rfl


/-! ### The record-enlarged σ-algebra -/

/-- **The record-enlarged σ-algebra at time `n`**: on each piece `{path = γ}` it is the
σ-algebra generated by the revealed coordinates *and* the record site's mark coordinates.
It contains the enlarged filtration `enlFilt p m n` (see `enlMeas_le_recMeas`) and makes the
record's mark measurable, which `enlFilt` does not (see `siteMark_not_cylAt_prefRead_zero`). -/
noncomputable def recMeas (p : ℝ) (m n : ℕ) (j : Fin N) : MeasurableSpace (Array N) where
  MeasurableSet' G := PiecewiseRecCyl p m n j G
  measurableSet_empty := fun γ =>
    ⟨∅, (cylAt (N := N) (recEnv (N := N) m γ j)).measurableSet_empty, by simp⟩
  measurableSet_compl := by
    intro G hG γ
    obtain ⟨B, hB, hEq⟩ := hG γ
    refine ⟨Bᶜ, (cylAt (N := N) (recEnv (N := N) m γ j)).measurableSet_compl _ hB, ?_⟩
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
    exact ⟨⋃ i, B i, (cylAt (N := N) (recEnv (N := N) m γ j)).measurableSet_iUnion B hB, by
      rw [Set.inter_iUnion, Set.inter_iUnion]
      congr 1
      funext i
      exact hEq i⟩

lemma measurableSet_recMeas_iff {A : Set (Array N)} {p : ℝ} {m n : ℕ} {j : Fin N} :
    MeasurableSet[recMeas p m n j] A ↔ PiecewiseRecCyl (N := N) p m n j A := Iff.rfl

/-- The record-enlarged σ-algebra is inside the ambient σ-algebra of the array. -/
lemma recMeas_le (p : ℝ) (m n : ℕ) (j : Fin N) :
    recMeas p m n j ≤ (inferInstance : MeasurableSpace (Array N)) := by
  intro G hG
  choose B hB hEq using fun γ => hG γ
  have hpiece : ∀ γ : Pref N n, MeasurableSet (prefAgree p m γ ∩ B γ) :=
    fun γ => (measurableSet_prefAgree_ambient p m γ).inter (measurableSet_of_cylAt (hB γ))
  have hunion : G = ⋃ γ : Pref N n, (prefAgree p m γ ∩ B γ) := by
    ext U
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      refine ⟨prefOf p m n U, prefAgree_prefOf U, ?_⟩
      have hh : U ∈ prefAgree p m (prefOf p m n U) ∩ G := ⟨prefAgree_prefOf U, h⟩
      rw [hEq (prefOf p m n U)] at hh
      exact hh.2
    · rintro ⟨γ, h1, h2⟩
      have hh : U ∈ prefAgree p m γ ∩ G := by rw [hEq γ]; exact ⟨h1, h2⟩
      exact hh.2
  rw [hunion]
  exact MeasurableSet.iUnion hpiece

/-- **The enlarged filtration is contained in the record-enlarged σ-algebra**: everything
known before time `n` (revealed coordinates) is base information for the record environment. -/
lemma enlMeas_le_recMeas (p : ℝ) (m n : ℕ) (j : Fin N) :
    enlMeas p m n ≤ recMeas p m n j := by
  intro G hG γ
  obtain ⟨B, hB, hEq⟩ := hG γ
  exact ⟨B, cylAt_mono (prefRead_subset_recEnv m γ j) B hB, hEq⟩

lemma enlFilt_le_recMeas (p : ℝ) (m n : ℕ) (j : Fin N) :
    enlFilt p m n ≤ recMeas p m n j := fun A hA => enlMeas_le_recMeas p m n j A hA

/-- Record events are measurable in the record-enlarged σ-algebra. -/
lemma measurableSet_runMax_recMeas (p : ℝ) (m n : ℕ) (j : Fin N) (P : ℤ → Prop) :
    MeasurableSet[recMeas p m n j] {U : Array N | P (runMax p m U j n)} :=
  piecewiseRecCyl_of_runMax p m n j P

/-- **The record site's mark is measurable in the record-enlarged σ-algebra.** -/
lemma measurableSet_recordMark_recMeas (p : ℝ) (m n : ℕ) (j : Fin N) :
    MeasurableSet[recMeas p m n j]
      {U : Array N | SiteMark p m U j (runMax p m U j n)} := by
  intro γ
  refine ⟨{U : Array N | SiteMark p m U j (runMaxPref (N := N) γ j)},
    measurableSet_recordMark p m γ j, ?_⟩
  ext U
  constructor
  · rintro ⟨hp, hmark⟩
    refine ⟨hp, ?_⟩
    have h1 : runMax p m U j n = runMaxPref (N := N) γ j := runMax_eq_runMaxPref p m hp j
    rw [← h1]
    exact hmark
  · rintro ⟨hp, hmark⟩
    refine ⟨hp, ?_⟩
    have h1 : runMax p m U j n = runMaxPref (N := N) γ j := runMax_eq_runMaxPref p m hp j
    show SiteMark p m U j (runMax p m U j n)
    rw [h1]
    exact hmark

/-- **Conditional site-mark mass over the record-enlarged σ-algebra** (restated form of
`recEnv_setIntegral_siteMark`).  `A` is any event of the record-enlarged σ-algebra contained
in the strict above-record event `{M_n^j < x}`. -/
theorem recMeas_setIntegral_siteMark (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (m : ℕ) (n : ℕ) (j : Fin N) (x : ℤ) {A : Set (Array N)}
    (hA : MeasurableSet[recMeas p m n j] A)
    (hAx : A ⊆ {U : Array N | runMax p m U j n < x}) :
    (arrayMeasure N).real (A ∩ {U : Array N | SiteMark p m U j x}) =
      (1 - p) ^ (m - 1) * (arrayMeasure N).real A :=
  recEnv_setIntegral_siteMark p hp0 hp1 m n j x hA hAx

/-- ENNReal form of `recMeas_setIntegral_siteMark`. -/
theorem recMeas_setIntegral_siteMark_enn (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (m : ℕ) (n : ℕ) (j : Fin N) (x : ℤ) {A : Set (Array N)}
    (hA : MeasurableSet[recMeas p m n j] A)
    (hAx : A ⊆ {U : Array N | runMax p m U j n < x}) :
    arrayMeasure N (A ∩ {U : Array N | SiteMark p m U j x}) =
      (ENNReal.ofReal (1 - p)) ^ (m - 1) * arrayMeasure N A :=
  recEnv_setIntegral_siteMark_enn p hp0 hp1 m n j x hA hAx

/-! ### The first strictly-above-record site `M_n^j + 1` -/

/-- **The fresh mark at the next above-record site.**  The site `M_n^j + 1` is above the
record on *every* path, so no above-record hypothesis is needed: for every event `A` of the
record-enlarged σ-algebra,

  `μ (A ∩ {B_j(M_n^j + 1)}) = (1-p)^(m-1) * μ A`.

This is the site that the recursion actually uses.  The nonnegativity event
`{0 ≤ M_n^j}` is itself recMeas-measurable (`measurableSet_runMax_recMeas`), so it can be
kept as an explicit intersection with `A` rather than dropped. -/
theorem recMeas_setIntegral_siteMark_succ_enn (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (m : ℕ) (n : ℕ) (j : Fin N) {A : Set (Array N)}
    (hA : MeasurableSet[recMeas p m n j] A) :
    arrayMeasure N (A ∩ {U : Array N | SiteMark p m U j (runMax p m U j n + 1)}) =
      (ENNReal.ofReal (1 - p)) ^ (m - 1) * arrayMeasure N A := by
  classical
  have hAx : ∀ x : ℤ, MeasurableSet[recMeas p m n j]
      (A ∩ {U : Array N | runMax p m U j n = x}) :=
    fun x => hA.inter (measurableSet_runMax_recMeas p m n j (· = x))
  have hPieceMeas : ∀ x : ℤ, MeasurableSet
      ((A ∩ {U : Array N | runMax p m U j n = x}) ∩
        {U : Array N | SiteMark p m U j (x + 1)}) :=
    fun x => ((recMeas_le p m n j) _ (hAx x)).inter
      (measurableSet_siteMark_array p m j (x + 1))
  have hunion : A ∩ {U : Array N | SiteMark p m U j (runMax p m U j n + 1)} =
      ⋃ x : ℤ, (A ∩ {U : Array N | runMax p m U j n = x}) ∩
        {U : Array N | SiteMark p m U j (x + 1)} := by
    ext U
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hAU, hmark⟩
      exact ⟨runMax p m U j n, ⟨hAU, rfl⟩, hmark⟩
    · rintro ⟨x, ⟨hAU, hx⟩, hmark⟩
      refine ⟨hAU, ?_⟩
      rw [hx]
      exact hmark
  have hdisj : Pairwise (fun x y : ℤ => Disjoint
      ((A ∩ {U : Array N | runMax p m U j n = x}) ∩
        {U : Array N | SiteMark p m U j (x + 1)})
      ((A ∩ {U : Array N | runMax p m U j n = y}) ∩
        {U : Array N | SiteMark p m U j (y + 1)})) := by
    intro x y hxy
    rw [Set.disjoint_left]
    rintro U ⟨⟨-, hx⟩, -⟩ ⟨⟨-, hy⟩, -⟩
    simp only [Set.mem_ofPred_eq] at hx hy
    exact hxy (hx.symm.trans hy)
  have hpiece : ∀ x : ℤ,
      arrayMeasure N ((A ∩ {U : Array N | runMax p m U j n = x}) ∩
          {U : Array N | SiteMark p m U j (x + 1)}) =
        (ENNReal.ofReal (1 - p)) ^ (m - 1) *
          arrayMeasure N (A ∩ {U : Array N | runMax p m U j n = x}) := by
    intro x
    refine recMeas_setIntegral_siteMark_enn p hp0 hp1 m n j (x + 1) (hAx x) ?_
    intro U hU
    have h1 : runMax p m U j n = x := by simpa using hU.2
    show runMax p m U j n < x + 1
    omega
  have hAdisj : Pairwise (fun x y : ℤ => Disjoint
      (A ∩ {U : Array N | runMax p m U j n = x})
      (A ∩ {U : Array N | runMax p m U j n = y})) := by
    intro x y hxy
    rw [Set.disjoint_left]
    rintro U ⟨-, hx⟩ ⟨-, hy⟩
    simp only [Set.mem_ofPred_eq] at hx hy
    exact hxy (hx.symm.trans hy)
  have htsumA : (∑' x : ℤ, arrayMeasure N (A ∩ {U : Array N | runMax p m U j n = x})) =
      arrayMeasure N A := by
    rw [← measure_iUnion hAdisj (fun x => (recMeas_le p m n j) _ (hAx x))]
    congr 1
    ext U
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, h, -⟩
      exact h
    · intro h
      exact ⟨runMax p m U j n, h, rfl⟩
  have hstep1 : arrayMeasure N
      (A ∩ {U : Array N | SiteMark p m U j (runMax p m U j n + 1)}) =
      ∑' x : ℤ, arrayMeasure N ((A ∩ {U : Array N | runMax p m U j n = x}) ∩
        {U : Array N | SiteMark p m U j (x + 1)}) := by
    rw [hunion, measure_iUnion hdisj hPieceMeas]
  rw [hstep1, tsum_congr hpiece, ENNReal.tsum_mul_left, htsumA]

/-- Real-measure form of `recMeas_setIntegral_siteMark_succ_enn`: the form a conditional
expectation assembly consumes. -/
theorem recMeas_setIntegral_siteMark_succ (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (m : ℕ) (n : ℕ) (j : Fin N) {A : Set (Array N)}
    (hA : MeasurableSet[recMeas p m n j] A) :
    (arrayMeasure N).real (A ∩ {U : Array N | SiteMark p m U j (runMax p m U j n + 1)}) =
      (1 - p) ^ (m - 1) * (arrayMeasure N).real A := by
  have h := recMeas_setIntegral_siteMark_succ_enn p hp0 hp1 m n j hA
  have h' : ENNReal.toReal (arrayMeasure N (A ∩
        {U : Array N | SiteMark p m U j (runMax p m U j n + 1)})) =
      ENNReal.toReal ((ENNReal.ofReal (1 - p)) ^ (m - 1) * arrayMeasure N A) :=
    congrArg ENNReal.toReal h
  calc
    (arrayMeasure N).real (A ∩ {U : Array N | SiteMark p m U j (runMax p m U j n + 1)}) =
        ENNReal.toReal (arrayMeasure N (A ∩
          {U : Array N | SiteMark p m U j (runMax p m U j n + 1)})) := rfl
    _ = ((ENNReal.ofReal (1 - p)) ^ (m - 1) * arrayMeasure N A).toReal := h'
    _ = (1 - p) ^ (m - 1) * (arrayMeasure N).real A := by
      have hnonneg : 0 ≤ 1 - p := by linarith
      rw [ENNReal.toReal_mul, ← ENNReal.ofReal_pow hnonneg,
        ENNReal.toReal_ofReal (pow_nonneg hnonneg _)]
      rfl

/-- **The record site's own coordinates are measurable in the record-enlarged σ-algebra.**
For the mark coordinates `k ∈ {1,…,m-1}` (exactly the ones `SiteMark` uses), the value
`U (j, M_n^j, k)` is a record-environment coordinate on each piece.  Note the boundary: the
`k = 0` coordinate of the record site is **not** in `recEnv`, so it is not covered here. -/
lemma measurableSet_recordCoord_recMeas (p : ℝ) (m n : ℕ) (j : Fin N) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 (m - 1)) {I : Set ℝ} (hI : MeasurableSet I) :
    MeasurableSet[recMeas p m n j] {U : Array N | U (j, runMax p m U j n, k) ∈ I} := by
  intro γ
  refine ⟨{U : Array N | U (j, runMaxPref (N := N) γ j, k) ∈ I},
    measurableSet_cylAt_of_mem (record_coord_mem_recEnv m γ j hk) hI, ?_⟩
  ext U
  constructor
  · rintro ⟨hp, hU⟩
    refine ⟨hp, ?_⟩
    rw [← runMax_eq_runMaxPref p m hp j]
    exact hU
  · rintro ⟨hp, hU⟩
    refine ⟨hp, ?_⟩
    show U (j, runMax p m U j n, k) ∈ I
    rw [runMax_eq_runMaxPref p m hp j]
    exact hU

/-! ### The record edge is real: at time `0` the record mark is not in the old base -/

lemma prefRead_zero_gen (γ : Pref N 0) : prefRead 0 γ = ∅ := by
  simp [prefRead]

/-- Every set measurable in *no* coordinates is trivial. -/
lemma measurableSet_cylAt_empty {B : Set (Array N)}
    (hB : MeasurableSet[cylAt (N := N) (∅ : Finset (Fin N × ℤ × ℕ))] B) :
    B = ∅ ∨ B = Set.univ := by
  obtain ⟨Bs, hBs, hBeq⟩ := MeasurableSpace.measurableSet_comap.1 hB
  have hEmpty : IsEmpty ↥(∅ : Finset (Fin N × ℤ × ℕ)) :=
    ⟨fun c => absurd c.2 (Finset.notMem_empty c.1)⟩
  have htriv : Bs = ∅ ∨ Bs = Set.univ := by
    rcases Bs.eq_empty_or_nonempty with h | ⟨g, hg⟩
    · exact Or.inl h
    · refine Or.inr ?_
      rw [Set.eq_univ_iff_forall]
      intro g'
      have hgg : g' = g := funext fun c => hEmpty.elim c
      rw [hgg]
      exact hg
  rw [← hBeq]
  rcases htriv with h | h
  · left
    rw [h]
    exact Set.preimage_empty
  · right
    rw [h]
    exact Set.preimage_univ

/-- The site-mark event above `0` is nonempty. -/
lemma siteMark_nonempty (p : ℝ) (hp1 : p < 1) (m : ℕ) (j : Fin N) (x : ℤ) :
    {U : Array N | SiteMark p m U j x}.Nonempty := by
  exact ⟨fun _ => 1, fun k _ => hp1⟩

/-- The site-mark event above `0` is not everything, as soon as there is at least one mark
coordinate (`2 ≤ m`). -/
lemma siteMark_ne_univ (p : ℝ) (hp0 : 0 < p) (m : ℕ) (hm : 2 ≤ m) (j : Fin N) (x : ℤ) :
    {U : Array N | SiteMark p m U j x} ≠ Set.univ := by
  intro hU
  have hmem : (1 : ℕ) ∈ Finset.Icc 1 (m - 1) := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hmemU : (fun c : Fin N × ℤ × ℕ => if c = (j, x, 1) then (0 : ℝ) else 1) ∈
      {U : Array N | SiteMark p m U j x} := by
    rw [hU]
    exact Set.mem_univ _
  have h1 := hmemU 1 hmem
  simp at h1
  linarith

/-- **The record mark is not measurable for the old base.**  At time `0` the revealed set is
empty and the record is the initial site, so the record's mark is *not* a function of the
revealed coordinates: `cylAt (prefRead 0 γ)` is trivial there while the mark is not.  This is
the precise sense in which one cannot pull the record mark out of a `condExp` under the plain
enlarged filtration. -/
theorem siteMark_not_cylAt_prefRead_zero (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (m : ℕ)
    (hm : 2 ≤ m) (γ : Pref N 0) (j : Fin N) :
    ¬ MeasurableSet[cylAt (N := N) (prefRead 0 γ)]
      {U : Array N | SiteMark p m U j (runMaxPref (N := N) γ j)} := by
  intro hB
  rw [prefRead_zero_gen] at hB
  rcases measurableSet_cylAt_empty hB with h | h
  · exact (siteMark_nonempty p hp1 m j _).ne_empty h
  · exact siteMark_ne_univ p hp0 m hm j _ h

end Swarming.Enl


