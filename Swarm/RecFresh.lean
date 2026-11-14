/-
  **Freshness of the sites strictly above the record, for the record-enlarged base.**

  `EnlFuture.lean` proves that, on the piece `{path = γ}`, an injective finite family of
  coordinates avoiding `prefRead n γ` has the product uniform law and is independent of every
  `cylAt (prefRead n γ)`-measurable event.  Here the base is enlarged to an arbitrary
  γ-dependent finite set `S γ ⊇ prefRead n γ` — in the application
  `S γ = recRead m j γ = prefRead n γ ∪ {marks at the record}` together with the rows of the
  already-adjoined sites above the record.

  * `prefAgree_eq_preimage_gen` — `{path = γ}` is the preimage, over the coordinates of `S γ`,
    of a measurable set of the finite product (the identification that lets the piece be
    analysed inside the product);
  * `fresh_block_gen` — the product law and independence over an enlarged base;
  * `fresh_siteMark_gen` — at a site `x` whose whole row is outside `S γ`, the site mark has
    exactly the Bernoulli mass `(1-p)^(m-1)`, multiplied by the base mass;
  * `setIntegral_siteMark_gen` — the same as a measure-level conditional statement for an
    arbitrary `pieceMeas S`-measurable event, subject only to "the record is below `x`" and
    "no coordinate of the row at `x` lies in `S γ`".  This is the fresh multiplier needed for
    the projected recursion, with the record row kept in the base instead of being assumed
    `enlFilt`-measurable.
-/
import Swarm.RecEnv

set_option linter.unusedVariables false
set_option warn.classDefReducibility false
set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory

variable {N : ℕ}

/-! ### The piece as a cylinder over an enlarged read set -/

/-- **The piece `{path = γ}` is a cylinder over any read set containing `prefRead n γ`.**  This is
`prefAgree_preimage` with `prefRead n γ` replaced by `S`. -/
theorem prefAgree_eq_preimage_gen (p : ℝ) (m : ℕ) {n : ℕ} (γ : Pref N n)
    (S : Finset (Fin N × ℤ × ℕ)) (hS : prefRead n γ ⊆ S) :
    prefAgree p m γ =
      (fun U (c : S) => U c) ⁻¹'
        {g : S → ℝ | ∀ t : Fin (n + 1),
          (trajectory p m (extendArr g) t.1).pos = γ t} := by
  ext U
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, prefAgree]
  have hagree : ∀ c : Fin N × ℤ × ℕ, c ∈ prefRead n γ →
      U c = extendArr (S := S) (fun c' => U c') c := by
    intro c hc
    rw [extendArr_of_mem (hS hc)]
  constructor
  · intro hU
    have hdep := traj_depends_on_prefRead p m γ U (extendArr (S := S) fun c' => U c') hU
      (fun c hc => hagree c hc)
    intro t
    rw [← hU t]
    exact congrArg (fun s : WalkState N => s.pos) (hdep t.1 (by omega)).symm
  · intro hg
    have hdep := traj_depends_on_prefRead p m γ (extendArr (S := S) fun c' => U c') U
      (fun t => hg t) (fun c hc => (hagree c hc).symm)
    intro t
    rw [← hg t]
    exact congrArg (fun s : WalkState N => s.pos) (hdep t.1 (by omega)).symm

/-- The determining set in the finite product over `S` is measurable. -/
lemma measurableSet_prod_prefAgree (p : ℝ) (m : ℕ) {n : ℕ} (γ : Pref N n)
    (S : Finset (Fin N × ℤ × ℕ)) :
    MeasurableSet {g : S → ℝ | ∀ t : Fin (n + 1),
      (trajectory p m (extendArr g) t.1).pos = γ t} := by
  have hsingle : ∀ (t : Fin (n + 1)) (i : Fin N), Measurable fun g : S → ℝ =>
      (trajectory p m (extendArr g) t.1).pos i := by
    intro t i
    have h1 : Measurable fun g : S → ℝ => extendArr g :=
      measurable_pi_iff.2 fun c => measurable_extendArr (S := S) (c : Fin N × ℤ × ℕ)
    exact ((Swarming.Fair.measurable_trajectory p m t.1).1 i).comp h1
  have h : ∀ t : Fin (n + 1), Measurable fun g : S → ℝ =>
      (trajectory p m (extendArr g) t.1).pos := fun t => measurable_pi_iff.2 (hsingle t)
  have hset : {g : S → ℝ | ∀ t : Fin (n + 1),
      (trajectory p m (extendArr g) t.1).pos = γ t} =
      ⋂ t : Fin (n + 1), {g : S → ℝ |
        (trajectory p m (extendArr g) t.1).pos = γ t} := by
    ext g
    simp
  rw [hset]
  exact MeasurableSet.iInter fun t => (h t) (measurableSet_singleton _)

/-! ### The finite fresh-block law over an enlarged base -/

/-- **Fresh-block law over an enlarged base.**  On the piece `{path = γ}`, an injective finite
family of coordinates avoiding `S γ` has the product uniform law and is independent of every
event measurable in the coordinates of `S γ`. -/
theorem fresh_block_gen (p : ℝ) (m : ℕ) (n : ℕ) (γ : Pref N n)
    (S : Finset (Fin N × ℤ × ℕ)) (hS : prefRead n γ ⊆ S)
    {B : Set (Array N)} (hB : MeasurableSet[cylAt (N := N) S] B)
    {ι : Type*} [Fintype ι] (α : ι → Fin N × ℤ × ℕ) (hαinj : Function.Injective α)
    (hfresh : ∀ i, α i ∉ S) (I : ι → Set ℝ) (hI : ∀ i, MeasurableSet (I i)) :
    arrayMeasure N (prefAgree p m γ ∩ B ∩ ⋂ i, {U : Array N | U (α i) ∈ I i}) =
      (∏ i, uniform01 (I i)) * arrayMeasure N (prefAgree p m γ ∩ B) := by
  classical
  obtain ⟨Bs, hBs, hBeq⟩ := MeasurableSpace.measurableSet_comap.1 hB
  set A : Set (S → ℝ) :=
    {g : S → ℝ | ∀ t : Fin (n + 1),
        (trajectory p m (extendArr g) t.1).pos = γ t} ∩ Bs with hA
  have hAmeas : MeasurableSet A :=
    (measurableSet_prod_prefAgree p m γ S).inter hBs
  have hbase : prefAgree p m γ ∩ B = (fun U (c : S) => U c) ⁻¹' A := by
    rw [← hBeq, prefAgree_eq_preimage_gen p m γ S hS]
    rfl
  have hfull : prefAgree p m γ ∩ B ∩ ⋂ i, {U : Array N | U (α i) ∈ I i} =
      (fun U (c : S) => U c) ⁻¹' A ∩ ⋂ i, (fun U : Array N => U (α i)) ⁻¹' I i := by
    rw [hbase]
    ext U
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_preimage]
  have hind := SwarmIID.indep_fresh_finset (μ := arrayMeasure N) (array_independent N)
    (fun c => measurable_pi_apply c) hαinj hfresh A hAmeas I hI
  have hprod : ∀ i, arrayMeasure N ((fun U : Array N => U (α i)) ⁻¹' I i) =
      uniform01 (I i) := fun i => arrayMeasure_preimage_set N (α i) (I i) (hI i)
  rw [hfull, hind, hbase]
  simp only [hprod]
  rw [mul_comm]

/-- **The record-row-honest site-mark law on one piece.**  If the whole row at the site `x` is
outside the enlarged read set `S γ`, then the site mark there has mass `(1-p)^(m-1)` relative to
the base mass. -/
theorem fresh_siteMark_gen (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (m : ℕ) {n : ℕ}
    (γ : Pref N n) (S : Finset (Fin N × ℤ × ℕ)) (hS : prefRead n γ ⊆ S)
    {B : Set (Array N)} (hB : MeasurableSet[cylAt (N := N) S] B)
    (j : Fin N) (x : ℤ) (hfresh : ∀ k ∈ Finset.Icc 1 (m - 1), (j, x, k) ∉ S) :
    arrayMeasure N (prefAgree p m γ ∩ B ∩ {V : Array N | SiteMark p m V j x}) =
      (ENNReal.ofReal (1 - p)) ^ (m - 1) * arrayMeasure N (prefAgree p m γ ∩ B) := by
  have hbase := fresh_block_gen p m n γ S hS hB
    (α := fun k : ↥(Finset.Icc 1 (m - 1)) => (j, x, k.1))
    (by
      intro a b hab
      have hv := congrArg (fun c : Fin N × ℤ × ℕ => c.2.2) hab
      exact Subtype.ext hv)
    (fun c => hfresh c.1 c.2)
    (fun _ => Set.Ioi p) (fun _ => measurableSet_Ioi)
  have hset : prefAgree p m γ ∩ B ∩ {V : Array N | SiteMark p m V j x} =
      prefAgree p m γ ∩ B ∩ ⋂ k : ↥(Finset.Icc 1 (m - 1)),
        {V : Array N | V (j, x, k.1) ∈ Set.Ioi p} := by
    ext V
    simp only [Set.mem_inter_iff, SiteMark, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_Ioi]
    constructor
    · rintro ⟨⟨hγ, hBmem⟩, hmark⟩
      exact ⟨⟨hγ, hBmem⟩, fun c => hmark c.1 c.2⟩
    · rintro ⟨⟨hγ, hBmem⟩, hmark⟩
      exact ⟨⟨hγ, hBmem⟩, fun k hk => hmark ⟨k, hk⟩⟩
  rw [hset, hbase]
  simp [uniform01_Ioi hp0 hp1]

/-! ### The set-integral form over an enlarged base -/

/-- **Fresh site mark at a prefix-determined site, as a measure-level conditional statement.**
For an arbitrary `pieceMeas S`-measurable event `A`, if on every piece `γ` the row at the site
`siteF γ` of walker `j` avoids the enlarged read set `S γ`, then the site mark there has mass
`(1-p)^(m-1)` relative to `A`.  In the application `siteF γ = recVal j γ + e` and
`S γ = recInfo m j g γ`, so `hfresh` is supplied by `recInfo_site_le`. -/
theorem setIntegral_siteMark_gen (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (m : ℕ) {n : ℕ}
    (S : Pref N n → Finset (Fin N × ℤ × ℕ)) (hS : ∀ γ, prefRead n γ ⊆ S γ)
    (j : Fin N) (siteF : Pref N n → ℤ)
    (hsite : ∀ (γ : Pref N n) (U : Array N), U ∈ prefAgree p m γ →
      siteF (prefOf p m n U) = siteF γ)
    (hfresh : ∀ γ k, k ∈ Finset.Icc 1 (m - 1) → (j, siteF γ, k) ∉ S γ)
    {A : Set (Array N)} (hA : MeasurableSet[pieceMeas p m n S] A) :
    (arrayMeasure N).real
        (A ∩ {U : Array N | SiteMark p m U j (siteF (prefOf p m n U))}) =
      (1 - p) ^ (m - 1) * (arrayMeasure N).real A := by
  classical
  have hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  choose B hB hEq using hA
  have hbase : ∀ γ : Pref N n, MeasurableSet (prefAgree p m γ ∩ B γ) := fun γ =>
    (measurableSet_prefAgree_ambient p m γ).inter (cylAt_le_ambient (S γ) (B γ) (hB γ))
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
      Disjoint ((prefAgree p m γ ∩ B γ) ∩
          {U : Array N | SiteMark p m U j (siteF (prefOf p m n U))})
        ((prefAgree p m γ' ∩ B γ') ∩
          {U : Array N | SiteMark p m U j (siteF (prefOf p m n U))})) := by
    intro γ γ' hne
    exact (hdisj hne).mono Set.inter_subset_left Set.inter_subset_left
  have hmark : ∀ γ : Pref N n,
      arrayMeasure N ((prefAgree p m γ ∩ B γ) ∩
          {U : Array N | SiteMark p m U j (siteF γ)}) =
        (ENNReal.ofReal (1 - p)) ^ (m - 1) * arrayMeasure N (prefAgree p m γ ∩ B γ) :=
    fun γ => fresh_siteMark_gen (N := N) p hp0 hp1 m γ (S γ) (hS γ) (hB γ) j (siteF γ)
      (fun k hk => hfresh γ k hk)
  have hpiece : ∀ γ : Pref N n,
      (prefAgree p m γ ∩ B γ) ∩ {U : Array N | SiteMark p m U j (siteF (prefOf p m n U))} =
        (prefAgree p m γ ∩ B γ) ∩ {U : Array N | SiteMark p m U j (siteF γ)} := by
    intro γ
    ext U
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h2⟩, by rw [hsite γ U h1] at h3; exact h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h2⟩, by rw [hsite γ U h1]; exact h3⟩
  have hlhs : arrayMeasure N
      (A ∩ {U : Array N | SiteMark p m U j (siteF (prefOf p m n U))}) =
      ∑' γ : Pref N n,
        (ENNReal.ofReal (1 - p)) ^ (m - 1) * arrayMeasure N (prefAgree p m γ ∩ B γ) := by
    have hunion : A ∩ {U : Array N | SiteMark p m U j (siteF (prefOf p m n U))} =
        ⋃ γ : Pref N n, (prefAgree p m γ ∩ B γ) ∩
          {U : Array N | SiteMark p m U j (siteF (prefOf p m n U))} := by
      conv_lhs => rw [hGunion]
      rw [Set.iUnion_inter]
    rw [hunion, measure_iUnion hdisjMark (fun γ => (hpiece γ) ▸
      (hbase γ).inter (measurableSet_siteMark_array p m j (siteF γ)))]
    exact tsum_congr (fun γ => (hpiece γ) ▸ hmark γ)
  have hreal : arrayMeasure N
      (A ∩ {U : Array N | SiteMark p m U j (siteF (prefOf p m n U))}) =
      (ENNReal.ofReal (1 - p)) ^ (m - 1) * arrayMeasure N A := by
    rw [hlhs, ENNReal.tsum_mul_left]
    rw [← measure_iUnion hdisj hbase, hGunion]
  have hreal' : ENNReal.toReal (arrayMeasure N
      (A ∩ {U : Array N | SiteMark p m U j (siteF (prefOf p m n U))})) =
      ENNReal.toReal ((ENNReal.ofReal (1 - p)) ^ (m - 1) * arrayMeasure N A) :=
    congrArg ENNReal.toReal hreal
  calc
    (arrayMeasure N).real
        (A ∩ {U : Array N | SiteMark p m U j (siteF (prefOf p m n U))}) =
        ENNReal.toReal (arrayMeasure N
          (A ∩ {U : Array N | SiteMark p m U j (siteF (prefOf p m n U))})) := rfl
    _ = ((ENNReal.ofReal (1 - p)) ^ (m - 1) * arrayMeasure N A).toReal := hreal'
    _ = (1 - p) ^ (m - 1) * (arrayMeasure N).real A := by
      have hnonneg : 0 ≤ 1 - p := by linarith
      rw [ENNReal.toReal_mul, ← ENNReal.ofReal_pow hnonneg,
        ENNReal.toReal_ofReal (pow_nonneg hnonneg _)]
      rfl

end Swarming.Enl
