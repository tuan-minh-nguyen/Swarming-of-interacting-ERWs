/-
# Fresh coordinates above the random record: the finite block law

`areas/spatialavg/S14.lean` names its one missing ingredient explicitly:

> given `F_n`, the marks of walker `j` at the sites `> M^j_n` are i.i.d. Bernoulli(q)
> and independent of `F_n`  (walker `j` never reads a coordinate above its running maximum)

and records that `Swarm/FreshIndependence.lean` only handles a *fixed* finite fresh set, so that the
passage to the random set `prefRead n γ` needs the piece-by-piece cylinder decomposition of
`enlMeas`.  `Swarm/EnlFuture.lean` supplies the one-site case at the random record
(`enl_setIntegral_siteMark_above_runMax`, `condExp_siteMark_above_runMax`) on top of that
decomposition.

This file proves the *finite block* version, which is what the paper's projected recursion
needs (`h_j(r_n + g)` involves only the `g` sites above the record):

* `AboveRec p m j n r` : walker `j`'s running maximum at time `n` is still `< r`
  (an `enlFilt p m n`-event; the strict containment is essential, no product law is asserted
  once the record has reached `r`).
* `FreshAbove j r α` : the finite coordinate family `α` lies in walker `j`'s row at sites `>= r`.
* `enl_setIntegral_fresh_above_runMax` : for an `enlFilt p m n`-event `A ⊆ AboveRec` and any
  injective finite family `α` of walker-`j` coordinates at sites `>= r`,
  `μ.real (A ∩ ⋂ i, {U | U (α i) ∈ I i}) = μ.real A * ∏ i, uniform01 (I i)`:
  the unread coordinates are i.i.d. `uniform01` and independent of the past.
* `enl_setIntegral_markBlock_above_runMax` : the corresponding site-mark block law,
  `μ.real (A ∩ MarksBox S) = q ^ |S| * μ.real A`, `q = (1-p) ^ (m-1)`.
* `condExp_markBlock_above_runMax` : the conditional-expectation form
  `E[1{AboveRec ∩ MarksBox} | F_n] = 1{AboveRec} · q ^ |S|`.

Everything is derived from `enl_fresh_future_piece` (the finite fresh-coordinate product law on
each piece `prefAgree γ`) plus the union/`tsum` decomposition of `enlMeas`; no new independence
assumption, no null-history conditioning, and no countable product extension is used.
-/
import Swarm.Imports
import Swarm.EnlFuture

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
open Swarming.Model Swarming.Uniform Swarming.Trajectory

namespace Swarming.Enl

variable {N : ℕ}

/-! ### The record event and the fresh family -/

/-- Walker `j`'s running maximum at time `n` is still strictly below the level `r`. -/
def AboveRec (p : ℝ) (m : ℕ) (j : Fin N) (n : ℕ) (r : ℤ) : Set (Array N) :=
  {U | runMax p m U j n < r}

lemma measurableSet_aboveRec_enl (p : ℝ) (m : ℕ) (j : Fin N) (n : ℕ) (r : ℤ) :
    MeasurableSet[enlFilt p m n] (AboveRec (N := N) p m j n r) :=
  measurableSet_runMax_lt_enl p m j n r

/-- The finite family of fresh coordinates lies in walker `j`'s row above the level `r`. -/
def FreshAbove (j : Fin N) (r : ℤ) {ι : Type*} (α : ι → Fin N × ℤ × ℕ) : Prop :=
  (∀ i, (α i).1 = j) ∧ (∀ i, r ≤ (α i).2.1)

/-- Every site of `S` carries the Bernoulli site mark. -/
def MarksBox (p : ℝ) (m : ℕ) (j : Fin N) (S : Finset ℤ) : Set (Array N) :=
  {U | ∀ x ∈ S, SiteMark p m U j x}

lemma measurableSet_marksBox_array (p : ℝ) (m : ℕ) (j : Fin N) (S : Finset ℤ) :
    MeasurableSet (MarksBox (N := N) p m j S) := by
  have hset : MarksBox (N := N) p m j S = ⋂ x ∈ S, {U : Array N | SiteMark p m U j x} := by
    ext U
    simp [MarksBox]
  rw [hset]
  exact Finset.measurableSet_biInter _ (fun x _ => measurableSet_siteMark_array p m j x)

/-! ### The general finite fresh-coordinate law above the random record -/

/-- **Finite fresh-coordinate law above the random record.**  On an `enlFilt p m n`-event `A`
on which walker `j`'s running maximum is still below `r`, every injective finite family of
walker-`j` coordinates at sites `>= r` has the product `uniform01` law and is independent of
`A`.  This is the "unread coordinates retain their law" statement for the *actual* array at a
random record. -/
theorem enl_setIntegral_fresh_above_runMax (p : ℝ) (m : ℕ) {n : ℕ} {A : Set (Array N)}
    (hA : MeasurableSet[enlFilt p m n] A) (j : Fin N) (r : ℤ)
    (hAsub : A ⊆ AboveRec (N := N) p m j n r)
    {ι : Type*} [Fintype ι] (α : ι → Fin N × ℤ × ℕ) (hαinj : Function.Injective α)
    (hα : FreshAbove (N := N) j r α)
    (I : ι → Set ℝ) (hI : ∀ i, MeasurableSet (I i)) :
    (arrayMeasure N).real (A ∩ ⋂ i, {U : Array N | U (α i) ∈ I i}) =
      (arrayMeasure N).real A * (∏ i, uniform01 (I i)).toReal := by
  classical
  have hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hAn : MeasurableSet[enlMeas p m n] A := hA
  choose B hB hEq using hAn
  have hbase : ∀ γ : Pref N n, MeasurableSet (prefAgree p m γ ∩ B γ) := by
    intro γ
    exact (measurableSet_prefAgree_ambient p m γ).inter (measurableSet_of_cyl (hB γ))
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
  set F : Set (Array N) := ⋂ i, {U : Array N | U (α i) ∈ I i} with hF
  have hdisjF : Pairwise (fun γ γ' : Pref N n =>
      Disjoint ((prefAgree p m γ ∩ B γ) ∩ F) ((prefAgree p m γ' ∩ B γ') ∩ F)) := by
    intro γ γ' hne
    exact (hdisj hne).mono Set.inter_subset_left Set.inter_subset_left
  have hFmeas : MeasurableSet F := by
    refine MeasurableSet.iInter fun i => ?_
    exact (hI i).preimage (measurable_pi_apply (α i))
  have hpiece : ∀ γ : Pref N n,
      arrayMeasure N ((prefAgree p m γ ∩ B γ) ∩ F) =
        (∏ i, uniform01 (I i)) * arrayMeasure N (prefAgree p m γ ∩ B γ) := by
    intro γ
    by_cases hpref : prefAgree p m γ ∩ B γ = ∅
    · simp [hpref]
    · obtain ⟨V, hV⟩ := Set.nonempty_iff_ne_empty.mpr hpref
      have hVA : V ∈ A := by
        have hh : V ∈ prefAgree p m γ ∩ A := by rw [hEq γ]; exact hV
        exact hh.2
      have hVlt : runMax p m V j n < r := hAsub hVA
      have hfresh : ∀ i, α i ∉ prefRead n γ := by
        intro i
        have hlt : runMax p m V (α i).1 n < (α i).2.1 := by
          rw [hα.1 i]
          exact lt_of_lt_of_le hVlt (hα.2 i)
        exact notMem_prefRead_above_runMax p m hV.1 (α i).1 hlt (α i).2.2
      exact enl_fresh_future_piece p m n γ (hB γ) α hαinj hfresh I hI
  have hunion : A ∩ F = ⋃ γ : Pref N n, (prefAgree p m γ ∩ B γ) ∩ F := by
    conv_lhs => rw [hGunion]
    rw [Set.iUnion_inter]
  have hlhs : arrayMeasure N (A ∩ F) =
      ∑' γ : Pref N n, (∏ i, uniform01 (I i)) * arrayMeasure N (prefAgree p m γ ∩ B γ) := by
    rw [hunion, measure_iUnion hdisjF (fun γ => (hbase γ).inter hFmeas)]
    exact tsum_congr hpiece
  have hreal : arrayMeasure N (A ∩ F) = (∏ i, uniform01 (I i)) * arrayMeasure N A := by
    rw [hlhs, ENNReal.tsum_mul_left, ← measure_iUnion hdisj hbase, hGunion]
  have hreal' : ENNReal.toReal (arrayMeasure N (A ∩ F)) =
      ENNReal.toReal ((∏ i, uniform01 (I i)) * arrayMeasure N A) := congrArg ENNReal.toReal hreal
  calc
    (arrayMeasure N).real (A ∩ ⋂ i, {U : Array N | U (α i) ∈ I i}) =
        ENNReal.toReal (arrayMeasure N (A ∩ F)) := rfl
    _ = ENNReal.toReal ((∏ i, uniform01 (I i)) * arrayMeasure N A) := hreal'
    _ = (arrayMeasure N).real A * (∏ i, uniform01 (I i)).toReal := by
      rw [ENNReal.toReal_mul, mul_comm]
      rfl

/-! ### The site-mark block law above the record -/

/-- Coordinates of all sites of `S` at departure numbers `1, …, m-1` in walker `j`'s row. -/
def freshFamily (j : Fin N) (S : Finset ℤ) (m : ℕ) :
    ↥(S.product (Finset.Icc 1 (m - 1))) → Fin N × ℤ × ℕ :=
  fun c => (j, c.1.1, c.1.2)

lemma freshFamily_injective (j : Fin N) (S : Finset ℤ) (m : ℕ) :
    Function.Injective (freshFamily (N := N) j S m) := by
  intro a b hab
  have h1 : (a.1.1 : ℤ) = b.1.1 := congrArg (fun c : Fin N × ℤ × ℕ => c.2.1) hab
  have h2 : (a.1.2 : ℕ) = b.1.2 := congrArg (fun c : Fin N × ℤ × ℕ => c.2.2) hab
  exact Subtype.ext (Prod.ext h1 h2)

lemma marksBox_eq_box (p : ℝ) (m : ℕ) (j : Fin N) (S : Finset ℤ) :
    MarksBox (N := N) p m j S =
      ⋂ c : ↥(S.product (Finset.Icc 1 (m - 1))),
        {U : Array N | U (j, c.1.1, c.1.2) ∈ Set.Ioi p} := by
  ext U
  simp only [MarksBox, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_Ioi, SiteMark]
  constructor
  · intro h c
    exact h c.1.1 (Finset.mem_product.mp c.2).1 c.1.2 (Finset.mem_product.mp c.2).2
  · intro h x hx k hk
    exact h ⟨⟨x, k⟩, Finset.mem_product.mpr ⟨hx, hk⟩⟩

/-- **Finite fresh site-mark block law above the random record.**  On an `enlFilt p m n`-event
`A` on which every site of `S` is still strictly above walker `j`'s running maximum, the marks
of all sites of `S` occur jointly with probability `((1-p)^{m-1})^{|S|}`, independently of `A`. -/
theorem enl_setIntegral_markBlock_above_runMax (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (m : ℕ) {n : ℕ} {A : Set (Array N)} (hA : MeasurableSet[enlFilt p m n] A)
    (j : Fin N) (S : Finset ℤ) (r : ℤ)
    (hAsub : A ⊆ AboveRec (N := N) p m j n r)
    (hSr : ∀ x ∈ S, r ≤ x) :
    (arrayMeasure N).real (A ∩ MarksBox (N := N) p m j S) =
      ((1 - p) ^ (m - 1)) ^ S.card * (arrayMeasure N).real A := by
  classical
  set qE : ℝ≥0∞ := (ENNReal.ofReal (1 - p)) ^ (m - 1) with hqE
  have hcardT : (Finset.Icc 1 (m - 1)).card = m - 1 := by
    rw [Nat.card_Icc]; omega
  have hcardProd : (S.product (Finset.Icc 1 (m - 1))).card = S.card * (m - 1) := by
    have h := Finset.card_product S (Finset.Icc 1 (m - 1))
    rw [hcardT] at h
    exact h
  have hprod : (∏ c : ↥(S.product (Finset.Icc 1 (m - 1))),
        uniform01 (Set.Ioi p)) = qE ^ S.card := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe, hcardProd,
      uniform01_Ioi hp0 hp1, Nat.mul_comm, pow_mul, ← hqE]
  have hα : FreshAbove (N := N) j r (freshFamily (N := N) j S m) :=
    ⟨fun _ => rfl, fun c => hSr c.1.1 (Finset.mem_product.mp c.2).1⟩
  have hmain := enl_setIntegral_fresh_above_runMax p m hA j r hAsub
    (freshFamily (N := N) j S m) (freshFamily_injective j S m) hα
    (fun _ => Set.Ioi p) (fun _ => measurableSet_Ioi)
  simp only [freshFamily] at hmain
  have hqReal : (qE ^ S.card).toReal = ((1 - p) ^ (m - 1)) ^ S.card := by
    rw [ENNReal.toReal_pow, hqE, ENNReal.toReal_pow]
    rw [ENNReal.toReal_ofReal (by linarith)]
  rw [marksBox_eq_box, hmain, hprod, hqReal]
  ring

/-! ### The conditional-expectation form -/

/-- **Fresh block law above the random record, conditional-expectation form.**
`E[1{AboveRec ∩ MarksBox} | F_n] = 1{AboveRec} · ((1-p)^{m-1})^{|S|}`. -/
theorem condExp_markBlock_above_runMax (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (m : ℕ) (n : ℕ) (j : Fin N) (S : Finset ℤ) (r : ℤ) (hSr : ∀ x ∈ S, r ≤ x) :
    (arrayMeasure N)[(AboveRec (N := N) p m j n r).indicator
        ((MarksBox (N := N) p m j S).indicator fun _ => (1 : ℝ)) | enlFilt p m n]
      =ᵐ[arrayMeasure N]
        (AboveRec (N := N) p m j n r).indicator (fun _ => ((1 - p) ^ (m - 1)) ^ S.card) := by
  classical
  let μ := arrayMeasure N
  let R : Set (Array N) := AboveRec (N := N) p m j n r
  let T : Set (Array N) := MarksBox (N := N) p m j S
  have hprob : IsProbabilityMeasure μ := arrayMeasure_isProbabilityMeasure N
  have hle : enlFilt p m n ≤ (inferInstance : MeasurableSpace (Array N)) := (enlFilt p m).le n
  have hsig : SigmaFinite (μ.trim hle) := inferInstance
  have hR : MeasurableSet[enlFilt p m n] R := measurableSet_aboveRec_enl p m j n r
  have hR0 : MeasurableSet R := hle R hR
  have hS0 : MeasurableSet T := measurableSet_marksBox_array p m j S
  have hq0 : 0 ≤ (1 - p) ^ (m - 1) := pow_nonneg (by linarith) _
  have hq1 : (1 - p) ^ (m - 1) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hq0' : 0 ≤ ((1 - p) ^ (m - 1)) ^ S.card := pow_nonneg hq0 _
  have hq1' : ((1 - p) ^ (m - 1)) ^ S.card ≤ 1 := pow_le_one₀ hq0 hq1
  have hind_int : Integrable (R.indicator (T.indicator fun _ => (1 : ℝ))) μ := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (((measurable_const.indicator hS0).indicator hR0).aestronglyMeasurable) ?_
    filter_upwards with U
    by_cases hU : U ∈ R
    · by_cases hmark : U ∈ T
      · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hmark, Real.norm_eq_abs, abs_one]
      · rw [Set.indicator_of_mem hU, Set.indicator_of_notMem hmark]
        simp
    · rw [Set.indicator_of_notMem hU]
      simp
  refine (ae_eq_condExp_of_forall_setIntegral_eq hle hind_int ?_ ?_
    ((measurable_const.indicator hR).aestronglyMeasurable)).symm
  · intro s hs hfin
    exact ((integrable_const (1 : ℝ)).mono'
      (measurable_const.indicator hR0).aestronglyMeasurable
      (Filter.Eventually.of_forall fun U => by
        by_cases hU : U ∈ R
        · rw [Set.indicator_of_mem hU, Real.norm_eq_abs, abs_of_nonneg hq0']
          exact hq1'
        · rw [Set.indicator_of_notMem hU]
          simp)).integrableOn
  · intro s hs hfin
    have hs0 : MeasurableSet s := hle s hs
    have hsr : MeasurableSet (s ∩ R) := hs0.inter hR0
    have hleft : ∫ U in s, R.indicator (T.indicator fun _ => (1 : ℝ)) U ∂μ =
        μ.real ((s ∩ R) ∩ T) := by
      rw [← integral_indicator (μ := μ) hs0]
      have hcongr : ∫ U, s.indicator (R.indicator (T.indicator fun _ => (1 : ℝ))) U ∂μ =
          ∫ U, ((s ∩ R) ∩ T).indicator (fun _ => (1 : ℝ)) U ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
        by_cases hU : U ∈ s
        · by_cases hr : U ∈ R
          · by_cases hm : U ∈ T
            · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hr, Set.indicator_of_mem hm,
                Set.indicator_of_mem (Set.mem_inter (Set.mem_inter hU hr) hm)]
            · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hr, Set.indicator_of_notMem hm,
                Set.indicator_of_notMem (fun h => hm h.2)]
          · rw [Set.indicator_of_mem hU, Set.indicator_of_notMem hr,
              Set.indicator_of_notMem (fun h => hr h.1.2)]
        · rw [Set.indicator_of_notMem hU,
            Set.indicator_of_notMem (fun h => hU h.1.1)]
      rw [hcongr]
      exact integral_indicator_one (μ := μ) (hsr.inter hS0)
    have hright : ∫ U in s, R.indicator (fun _ => ((1 - p) ^ (m - 1)) ^ S.card) U ∂μ =
        ((1 - p) ^ (m - 1)) ^ S.card * μ.real (s ∩ R) := by
      rw [← integral_indicator (μ := μ) hs0]
      have hcongr : ∫ U, s.indicator (R.indicator (fun _ => ((1 - p) ^ (m - 1)) ^ S.card)) U ∂μ =
          ∫ U, (s ∩ R).indicator (fun _ => ((1 - p) ^ (m - 1)) ^ S.card) U ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
        by_cases hU : U ∈ s
        · by_cases hr : U ∈ R
          · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hr,
              Set.indicator_of_mem (Set.mem_inter hU hr)]
          · rw [Set.indicator_of_mem hU, Set.indicator_of_notMem hr,
              Set.indicator_of_notMem (fun h => hr h.2)]
        · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem (fun h => hU h.1)]
      rw [hcongr, integral_indicator hsr, setIntegral_const, smul_eq_mul, mul_comm]
    have hA' : MeasurableSet[enlFilt p m n] (s ∩ R) := hs.inter hR
    have hsub : (s ∩ R) ⊆ AboveRec (N := N) p m j n r := fun U hU => hU.2
    rw [hright, hleft]
    exact (enl_setIntegral_markBlock_above_runMax p hp0 hp1 m hA' j S r hsub hSr).symm

/-! ### The paper's form: on `{M^j_n = r}` the sites `r+1, …, ` carry fresh marks -/

/-- **Fresh marks above a known record.**  On an `enlFilt p m n`-event `A` on which walker
`j`'s running maximum equals the fixed level `r`, every finite set `S` of sites strictly above
`r` carries joint mark probability `((1-p)^{m-1})^{|S|}`, independently of `A`.  This is the
paper's step "the sites above the record are i.i.d. Bernoulli(q) and independent of `F_n`",
at a fixed value of the record. -/
theorem enl_setIntegral_markBlock_above_record (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (m : ℕ) {n : ℕ} {A : Set (Array N)} (hA : MeasurableSet[enlFilt p m n] A)
    (j : Fin N) (S : Finset ℤ) (r : ℤ)
    (hArec : A ⊆ {U : Array N | runMax p m U j n = r})
    (hSr : ∀ x ∈ S, r < x) :
    (arrayMeasure N).real (A ∩ MarksBox (N := N) p m j S) =
      ((1 - p) ^ (m - 1)) ^ S.card * (arrayMeasure N).real A :=
  enl_setIntegral_markBlock_above_runMax p hp0 hp1 m hA j S (r + 1)
    (fun U hU => by
      have h : runMax p m U j n = r := hArec hU
      show runMax p m U j n < r + 1
      omega)
    (fun x hx => Int.add_one_le_iff.mpr (hSr x hx))

/-- **Conditional independence of the marks at two disjoint site blocks above the record.**
For disjoint finite `S`, `S'` above the record the joint mark probability factorises into the
two block probabilities, i.e. the site marks above the record are conditionally independent
given `F_n`. -/
theorem enl_setIntegral_markBlock_pair (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (m : ℕ) {n : ℕ} {A : Set (Array N)} (hA : MeasurableSet[enlFilt p m n] A)
    (j : Fin N) (S S' : Finset ℤ) (r : ℤ) (hdisj : Disjoint S S')
    (hAsub : A ⊆ AboveRec (N := N) p m j n r)
    (hSr : ∀ x ∈ S ∪ S', r ≤ x) :
    (arrayMeasure N).real (A ∩ MarksBox (N := N) p m j S ∩ MarksBox (N := N) p m j S') =
      ((1 - p) ^ (m - 1)) ^ (S.card + S'.card) * (arrayMeasure N).real A := by
  have hunion : MarksBox (N := N) p m j S ∩ MarksBox (N := N) p m j S'
      = MarksBox (N := N) p m j (S ∪ S') := by
    ext U
    simp only [MarksBox, Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.mem_union]
    exact ⟨fun h x hx => hx.elim (h.1 x) (h.2 x), fun h => ⟨fun x hx => h x (Or.inl hx),
      fun x hx => h x (Or.inr hx)⟩⟩
  have hcard : (S ∪ S').card = S.card + S'.card := Finset.card_union_of_disjoint hdisj
  have hSunion : ∀ x ∈ S ∪ S', r ≤ x := hSr
  rw [Set.inter_assoc, hunion,
    enl_setIntegral_markBlock_above_runMax p hp0 hp1 m hA j (S ∪ S') r hAsub hSunion, hcard]

end Swarming.Enl


