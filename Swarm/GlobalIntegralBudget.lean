/-
  **DIRECTION G (m7) — `GlobalIntegralBudget.lean`: the real-integral form of the global
  one-step `Hpot` lower bound over the finite offset partition.**

  This file is the integral (unconditional-expectation) companion of Direction F's pointwise
  `enlFilt` assembly.  Nothing here is a new probability estimate: it is one-step bookkeeping,
  namely

  * the finite partition of the array space into the strictly-below-record region `B` and the
    above-record offsets `A_g = {X_n^i = M_n^j + g}`, `g ∈ range (n+1)`, with pairwise
    disjointness and the pointwise indicator identity
    `1_B + Σ_{g<n+1} 1_{A_g} = 1`;
  * the piecewise **global weight** `budgetWeight` / `campaignWeight` (below: `-b_n`,
    at record: `1 - b_n`, above at offset `g ≥ 1`: `-b_n a^g`) in the exact shapes the ledger
    uses, and its exact decomposition into the below/record/above set intersections;
  * a generic "integrate a piecewise restricted `condExp` bound" lemma: from
    `1_A w ≤ᵐ E[1_A f | F]` for each piece and the partition identity, conclude
    `Σ ∫_A w ≤ ∫ f`, using `integral_condExp` and `integral_indicator` only;
  * the **campaign budget theorem**: given the below-region restricted bound (the audited
    below-record candidate, as an explicit hypothesis), the *integrated* record bound
    (`RecordTower.indicator_le_condExp_indicator_HpotInc_zero`, no hypothesis) and the
    above-record restricted bound for `g ≥ 1` (Direction A, as an explicit hypothesis),
    the real integral of the actual increment dominates the piecewise weight, with the sum
    kept in the separated form `g = 0` and `g ≥ 1`;
  * the **exact weight comparison with the paper's `(Zloss)`**: the paper's weight
    (`SwarmOcc.Zloss`'s left-hand side at `r = M_n^j`, `x = X_n^i`, `b = b_n`, `a = aRec p m`)
    differs from the campaign weight by exactly
    `1_B · (1{0 ≤ x} + b_n)`, which is pointwise nonnegative; hence the campaign budget is the
    paper budget minus that explicit (nonnegative) remainder, and the *sharpened* below-record
    bound yields the paper's weight exactly.  No constant is changed silently.

  Quarantined: no `Q`, no occupation/regeneration statement, no Ballistic conclusion, no main
  theorem.  The two external inputs (below-region bound, above-record `g ≥ 1` bound) are carried
  as explicit hypotheses and are identified as such.

  No `sorry`, no `admit`, no custom axioms, no `native_decide`; the axiom audit is in
  `Audit.lean` (same directory).
-/
import Swarm.InteriorBound
import Swarm.AboveActualDrift
import Swarm.RecordTower

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl
namespace Budget

open Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross

variable {N : ℕ}

/-! ### The increment, in the common normalisation

`RecordTower.HpotInc` is the common actual increment.  `AboveActualDrift` states its
integrability and its above-record conditional law with `siteH`, which is `envH`
definitionally, so the two spellings coincide. -/

/-- The common increment is the `siteH`-spelled increment of `AboveActualDrift`. -/
theorem HpotInc_eq_siteH (p : ℝ) (m n : ℕ) (i j : Fin N) :
    HpotInc p m n i j = fun U : Array N =>
      SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U (n + 1)).pos i)
        - SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U n).pos i) := rfl

/-- **The actual one-step increment is integrable** (from `AboveActualDrift`). -/
theorem integrable_HpotInc {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hpne : p ≠ 0)
    (m n : ℕ) (i j : Fin N) :
    Integrable (HpotInc p m n i j) (arrayMeasure N) :=
  integrable_Hpot_traj_step hp0 hp1 hpne m n i j

/-- Every restriction of the increment to an ambient measurable set is integrable. -/
theorem integrable_indicator_HpotInc {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hpne : p ≠ 0) (m n : ℕ) (i j : Fin N) {A : Set (Array N)} (hA : MeasurableSet A) :
    Integrable (A.indicator (HpotInc p m n i j)) (arrayMeasure N) :=
  (integrable_HpotInc hp0 hp1 hpne m n i j).indicator hA

/-! ### The strictly-below-record region, and the finite partition -/

/-- The below-record region, *defined* as the complement of the finitely many above-record
offsets.  With this definition the finite partition is a tautology; the equality with the
trajectory form `{X_n^i < M_n^j}` is `belowSet_eq_lt_runMax` below. -/
noncomputable def belowSet (p : ℝ) (m n : ℕ) (i j : Fin N) : Set (Array N) :=
  (⋃ g ∈ Finset.range (n + 1), abovePosSet p m n i j g)ᶜ

theorem mem_belowSet_iff {p : ℝ} {m n : ℕ} {i j : Fin N} {U : Array N} :
    U ∈ belowSet p m n i j
      ↔ ∀ g : ℕ, g < n + 1 → U ∉ abovePosSet p m n i j g := by
  simp only [belowSet, Set.mem_compl_iff, Set.mem_iUnion, Finset.mem_range, exists_prop,
    not_exists, not_and]

/-- The below-record region in the trajectory language. -/
theorem belowSet_eq_lt_recVal (p : ℝ) (m n : ℕ) (i j : Fin N) :
    belowSet p m n i j
      = {U : Array N | (trajectory p m U n).pos i < recVal j (prefOf p m n U)} := by
  ext U
  rw [mem_belowSet_iff]
  simp only [abovePosSet, Set.mem_ofPred_eq]
  have hpos : ext (prefOf p m n U) n i = (trajectory p m U n).pos i := ext_prefOf U le_rfl i
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have hd : (0 : ℤ) ≤ (trajectory p m U n).pos i - recVal j (prefOf p m n U) := by linarith
    have hle : (trajectory p m U n).pos i - recVal j (prefOf p m n U) ≤ (n : ℤ) := by
      have h1 := (pos_bounds (p := p) (m := m) U n i).2
      have h2 := zero_le_recVal_prefOf p m U j n
      linarith
    have hg : ((trajectory p m U n).pos i - recVal j (prefOf p m n U)).toNat < n + 1 := by
      have hcast : (((trajectory p m U n).pos i
          - recVal j (prefOf p m n U)).toNat : ℤ) = (trajectory p m U n).pos i
            - recVal j (prefOf p m n U) := Int.toNat_of_nonneg hd
      have hZ : (((trajectory p m U n).pos i
          - recVal j (prefOf p m n U)).toNat : ℤ) ≤ (n : ℤ) := by
        rw [hcast]; linarith
      exact Nat.lt_succ_of_le (by exact_mod_cast hZ)
    refine h _ hg ?_
    rw [hpos]
    have hcast : (((trajectory p m U n).pos i
        - recVal j (prefOf p m n U)).toNat : ℤ) = (trajectory p m U n).pos i
          - recVal j (prefOf p m n U) := Int.toNat_of_nonneg hd
    rw [hcast]
    ring
  · rintro h g hg heq
    have hnn : (0 : ℤ) ≤ (g : ℤ) := by exact_mod_cast Nat.zero_le g
    have hle : recVal j (prefOf p m n U) ≤ ext (prefOf p m n U) n i := by linarith
    have hpos' : (trajectory p m U n).pos i = ext (prefOf p m n U) n i := hpos.symm
    linarith

/-- The below-record region in the trajectory/running-maximum language. -/
theorem belowSet_eq_lt_runMax (p : ℝ) (m n : ℕ) (i j : Fin N) :
    belowSet p m n i j
      = {U : Array N | (trajectory p m U n).pos i < runMax p m U j n} := by
  rw [belowSet_eq_lt_recVal]
  ext U
  simp only [Set.mem_ofPred_eq, runMax_eq_recVal]

/-- The below-record region is ambient measurable. -/
theorem measurableSet_belowSet (p : ℝ) (m n : ℕ) (i j : Fin N) :
    MeasurableSet (belowSet p m n i j) := by
  refine MeasurableSet.compl ?_
  refine Finset.measurableSet_biUnion _ fun g _ => ?_
  exact infoPiece_le p m n j g _ (measurableSet_abovePosSet p m n i j g g)

/-- The below-record region is disjoint from every above-record offset in the finite cover. -/
theorem disjoint_belowSet_abovePosSet (p : ℝ) (m n : ℕ) (i j : Fin N) {g : ℕ}
    (hg : g ∈ Finset.range (n + 1)) :
    Disjoint (belowSet p m n i j) (abovePosSet p m n i j g) := by
  rw [Set.disjoint_left]
  intro U h1 h2
  rw [mem_belowSet_iff] at h1
  exact h1 g (Finset.mem_range.mp hg) h2

/-- Distinct above-record offsets are disjoint. -/
theorem disjoint_abovePosSet (p : ℝ) (m n : ℕ) (i j : Fin N) {g g' : ℕ} (h : g ≠ g') :
    Disjoint (abovePosSet p m n i j g) (abovePosSet p m n i j g') := by
  rw [Set.disjoint_left]
  intro U h1 h2
  rw [abovePosSet_traj_iff] at h1 h2
  have : (g : ℤ) = (g' : ℤ) := by linarith
  exact h (by exact_mod_cast this)

/-- **The partition, as a pointwise indicator identity.** -/
theorem indicator_belowSet_add_sum_abovePosSet (p : ℝ) (m n : ℕ) (i j : Fin N)
    (U : Array N) :
    (belowSet p m n i j).indicator (fun _ => (1 : ℝ)) U
        + ∑ g ∈ Finset.range (n + 1),
            (abovePosSet p m n i j g).indicator (fun _ => (1 : ℝ)) U = 1 := by
  classical
  by_cases hU : U ∈ belowSet p m n i j
  · rw [Set.indicator_of_mem hU]
    have hzero : ∀ g ∈ Finset.range (n + 1),
        (abovePosSet p m n i j g).indicator (fun _ => (1 : ℝ)) U = 0 := by
      intro g hg
      exact Set.indicator_of_notMem (f := fun _ => (1 : ℝ)) (fun h =>
        (Set.disjoint_left.mp (disjoint_belowSet_abovePosSet p m n i j hg)) hU h)
    rw [Finset.sum_eq_zero hzero]
    ring
  · rw [Set.indicator_of_notMem hU]
    have hex : ∃ g : ℕ, g < n + 1 ∧ U ∈ abovePosSet p m n i j g := by
      by_contra hcon
      exact hU (by
        rw [mem_belowSet_iff]
        intro g hg hmem
        exact hcon ⟨g, hg, hmem⟩)
    obtain ⟨g₀, hg₀, hmem₀⟩ := hex
    rw [Finset.sum_eq_single g₀]
    · rw [Set.indicator_of_mem hmem₀]; ring
    · intro b _ hne
      exact Set.indicator_of_notMem (f := fun _ => (1 : ℝ)) (fun h =>
        (Set.disjoint_left.mp (disjoint_abovePosSet p m n i j hne)) h hmem₀)
    · intro hcon
      exact absurd (Finset.mem_range.mpr hg₀) hcon


/-! ### The piecewise global weight of the campaign

Below the record the campaign uses the worst-case `-b_n`; at the record `1 - b_n`; at offset
`g ≥ 1` the projected loss `-b_n a^g`.  `campaignWeight` writes the whole ledger as a single
function of the position relative to the record, which is what the unconditional budget
integrates; `campaignWeight_eq_pieces` identifies it with the below/record/above set pieces. -/

/-- The at-record weight `1 - b_n`. -/
noncomputable def recordWeight (p : ℝ) (m n : ℕ) (j : Fin N) : Array N → ℝ :=
  fun U => 1 - bRec p m n j U

/-- The above-record weight `-b_n a^g` at offset `g`. -/
noncomputable def aboveWeight (p : ℝ) (m n : ℕ) (j : Fin N) (g : ℕ) : Array N → ℝ :=
  fun U => -(bRec p m n j U * aRec p m ^ g)

/-- The offset weight of the finite above-record chain: `1 - b_n` at offset `0`, `-b_n a^g` at
offset `g ≥ 1`. -/
noncomputable def offsetWeight (p : ℝ) (m n : ℕ) (j : Fin N) : ℕ → Array N → ℝ
  | 0 => recordWeight p m n j
  | (g + 1) => aboveWeight p m n j (g + 1)

/-- **The piecewise global one-step weight of the drift campaign**, as a function of the position
`X_n^i` relative to the running record `M_n^j`: `-b_n` strictly below the record, `1 - b_n` at the
record, `-b_n a^g` at offset `g ≥ 1`. -/
noncomputable def campaignWeight (p : ℝ) (m n : ℕ) (i j : Fin N) (U : Array N) : ℝ :=
  if (trajectory p m U n).pos i < runMax p m U j n then -(bRec p m n j U)
  else if (trajectory p m U n).pos i = runMax p m U j n then recordWeight p m n j U
  else aboveWeight p m n j ((trajectory p m U n).pos i - runMax p m U j n).toNat U

/-- Membership characterisation of the below-record region (avoiding rewrites under hypotheses). -/
theorem mem_belowSet_iff_lt (p : ℝ) (m n : ℕ) (i j : Fin N) (U : Array N) :
    U ∈ belowSet p m n i j ↔ (trajectory p m U n).pos i < runMax p m U j n := by
  rw [belowSet_eq_lt_runMax]
  exact Iff.rfl

/-- The finite cover, in the direction the weight decomposition needs. -/
theorem exists_abovePosSet_of_notMem_belowSet (p : ℝ) (m n : ℕ) (i j : Fin N) {U : Array N}
    (hU : U ∉ belowSet p m n i j) :
    ∃ g : ℕ, g < n + 1 ∧ U ∈ abovePosSet p m n i j g := by
  by_contra hcon
  exact hU ((mem_belowSet_iff (p := p) (m := m) (n := n) (i := i) (j := j) (U := U)).mpr
    (fun g hg hmem => hcon ⟨g, hg, hmem⟩))

/-- **The global weight, decomposed onto the finite partition.** -/
theorem campaignWeight_eq_pieces (p : ℝ) (m n : ℕ) (i j : Fin N) (U : Array N) :
    campaignWeight p m n i j U
      = (belowSet p m n i j).indicator (fun U => -(bRec p m n j U)) U
        + ∑ g ∈ Finset.range (n + 1),
            (abovePosSet p m n i j g).indicator (offsetWeight p m n j g) U := by
  classical
  by_cases hU : U ∈ belowSet p m n i j
  · have hlt : (trajectory p m U n).pos i < runMax p m U j n :=
      (mem_belowSet_iff_lt p m n i j U).mp hU
    rw [campaignWeight, if_pos hlt, Set.indicator_of_mem hU]
    have hzero : ∀ g ∈ Finset.range (n + 1),
        (abovePosSet p m n i j g).indicator (offsetWeight p m n j g) U = 0 := by
      intro g hg
      exact Set.indicator_of_notMem (f := offsetWeight p m n j g) (fun h =>
        (Set.disjoint_left.mp (disjoint_belowSet_abovePosSet p m n i j hg)) hU h)
    rw [Finset.sum_eq_zero hzero]
    ring
  · obtain ⟨g₀, hg₀, hmem₀⟩ := exists_abovePosSet_of_notMem_belowSet p m n i j hU
    have hposEq : (trajectory p m U n).pos i = runMax p m U j n + (g₀ : ℤ) :=
      (abovePosSet_traj_iff p m n i j g₀ U).mp hmem₀
    have hge : runMax p m U j n ≤ (trajectory p m U n).pos i := by
      have hnn : (0 : ℤ) ≤ (g₀ : ℤ) := by exact_mod_cast Nat.zero_le g₀
      linarith
    have hbelowInd : (belowSet p m n i j).indicator (fun U => -(bRec p m n j U)) U = 0 :=
      Set.indicator_of_notMem (f := fun U => -(bRec p m n j U)) hU
    rw [campaignWeight, if_neg (not_lt.mpr hge), hbelowInd]
    have hsingle : ∑ g ∈ Finset.range (n + 1),
        (abovePosSet p m n i j g).indicator (offsetWeight p m n j g) U
        = (abovePosSet p m n i j g₀).indicator (offsetWeight p m n j g₀) U := by
      refine Finset.sum_eq_single (s := Finset.range (n + 1))
        (f := fun g => (abovePosSet p m n i j g).indicator (offsetWeight p m n j g) U) g₀ ?_ ?_
      · intro b _ hne
        exact Set.indicator_of_notMem (f := offsetWeight p m n j b) (fun h =>
          (Set.disjoint_left.mp (disjoint_abovePosSet p m n i j hne)) h hmem₀)
      · intro hcon
        exact absurd (Finset.mem_range.mpr hg₀) hcon
    rw [hsingle, Set.indicator_of_mem hmem₀]
    match g₀ with
    | 0 =>
        have hEq : (trajectory p m U n).pos i = runMax p m U j n := by simpa using hposEq
        rw [if_pos hEq]
        simp [offsetWeight]
    | (k + 1) =>
        have hne : (trajectory p m U n).pos i ≠ runMax p m U j n := by
          intro hcontra
          have hk : (0 : ℤ) < ((k + 1 : ℕ) : ℤ) := by positivity
          rw [hposEq] at hcontra
          linarith
        rw [if_neg hne]
        have hexp : ((trajectory p m U n).pos i - runMax p m U j n).toNat = k + 1 := by
          have : (trajectory p m U n).pos i - runMax p m U j n = ((k : ℤ) + 1) := by
            rw [hposEq]
            push_cast
            ring
          rw [this]
          simp
        rw [hexp]
        simp [offsetWeight, aboveWeight]

/-! ### Integrability of the weight components -/

theorem integrable_HprevAt_w {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m n : ℕ)
    (j : Fin N) : Integrable (HprevAt p m n j) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  refine Integrable.mono' (integrable_const (2 * (n : ℝ) + 3))
    (measurable_HprevAt p m n j).aestronglyMeasurable (Filter.Eventually.of_forall fun U => ?_)
  rw [Real.norm_eq_abs]
  exact abs_HprevAt_le hp1 hp2 m n j U

theorem integrable_bRec_w {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m n : ℕ)
    (j : Fin N) : Integrable (bRec p m n j) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have h := (integrable_HprevAt_w hp1 hp2 m n j).add (integrable_const (2 : ℝ))
  refine h.congr (Filter.Eventually.of_forall fun U => ?_)
  simp only [Pi.add_apply]
  rw [bRec]

theorem integrable_recordWeight_w {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m n : ℕ)
    (j : Fin N) : Integrable (recordWeight p m n j) (arrayMeasure N) :=
  (integrable_const (1 : ℝ)).sub (integrable_bRec_w hp1 hp2 m n j)

theorem integrable_aboveWeight_w {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m n : ℕ)
    (j : Fin N) (g : ℕ) : Integrable (aboveWeight p m n j g) (arrayMeasure N) := by
  have h := (integrable_bRec_w hp1 hp2 m n j).mul_const (aRec p m ^ g)
  exact h.neg.congr (Filter.Eventually.of_forall fun U => rfl)

theorem integrable_offsetWeight_w {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m n : ℕ)
    (j : Fin N) (g : ℕ) : Integrable (offsetWeight p m n j g) (arrayMeasure N) := by
  match g with
  | 0 => exact integrable_recordWeight_w hp1 hp2 m n j
  | (k + 1) => exact integrable_aboveWeight_w hp1 hp2 m n j (k + 1)

/-! ### Integrating a piecewise restricted `condExp` bound -/

/-- **Set-integral monotonicity from a restricted `condExp` bound.**  If `1_A w` is dominated
a.e. by the `enlFilt n`-conditional mean of `1_A f`, then `∫_A w ≤ ∫_A f`.  Only the two
identities `integral_condExp` and `integral_indicator` are used. -/
theorem setIntegral_le_setIntegral_of_condExp {p : ℝ} {m n : ℕ} {A : Set (Array N)}
    {w f : Array N → ℝ} (hA : MeasurableSet A) (hf : Integrable f (arrayMeasure N))
    (hw : Integrable w (arrayMeasure N))
    (h : (fun U => A.indicator w U) ≤ᵐ[arrayMeasure N]
      condExp (enlFilt p m n) (arrayMeasure N) (A.indicator f)) :
    ∫ U in A, w U ∂(arrayMeasure N) ≤ ∫ U in A, f U ∂(arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hle : enlFilt p m n ≤ (inferInstance : MeasurableSpace (Array N)) := (enlFilt p m).le n
  haveI : SigmaFinite ((arrayMeasure N).trim hle) := inferInstance
  calc ∫ U in A, w U ∂(arrayMeasure N)
      = ∫ U, A.indicator w U ∂(arrayMeasure N) := (integral_indicator hA).symm
    _ ≤ ∫ U, condExp (enlFilt p m n) (arrayMeasure N) (A.indicator f) U
          ∂(arrayMeasure N) := integral_mono_ae (hw.indicator hA) integrable_condExp h
    _ = ∫ U, A.indicator f U ∂(arrayMeasure N) := integral_condExp hle
    _ = ∫ U in A, f U ∂(arrayMeasure N) := integral_indicator hA

/-- **The finite piecewise integral bound.**  From the partition identity
`1_B + Σ_{i ∈ s} 1_{A_i} = 1` and a restricted `condExp` bound on each piece, the sum of the
piecewise set integrals is dominated by the integral of `f`. -/
theorem integral_piecewise_bound {ι : Type*} (s : Finset ι) {p : ℝ} {m n : ℕ}
    {B : Set (Array N)} {wB : Array N → ℝ} {A : ι → Set (Array N)} {w : ι → Array N → ℝ}
    {f : Array N → ℝ}
    (hpart : ∀ U : Array N, B.indicator (fun _ => (1 : ℝ)) U
      + ∑ i ∈ s, (A i).indicator (fun _ => (1 : ℝ)) U = 1)
    (hBm : MeasurableSet B) (hAm : ∀ i ∈ s, MeasurableSet (A i))
    (hf : Integrable f (arrayMeasure N))
    (hwB : Integrable wB (arrayMeasure N)) (hw : ∀ i ∈ s, Integrable (w i) (arrayMeasure N))
    (hB : (fun U => B.indicator wB U) ≤ᵐ[arrayMeasure N]
      condExp (enlFilt p m n) (arrayMeasure N) (B.indicator f))
    (hA : ∀ i ∈ s, (fun U => (A i).indicator (w i) U) ≤ᵐ[arrayMeasure N]
      condExp (enlFilt p m n) (arrayMeasure N) ((A i).indicator f)) :
    (∫ U in B, wB U ∂(arrayMeasure N))
        + ∑ i ∈ s, ∫ U in A i, w i U ∂(arrayMeasure N)
      ≤ ∫ U, f U ∂(arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hBf : Integrable (B.indicator f) (arrayMeasure N) := hf.indicator hBm
  have hAf : ∀ i ∈ s, Integrable ((A i).indicator f) (arrayMeasure N) :=
    fun i hi => hf.indicator (hAm i hi)
  have hsumf : Integrable (fun U => ∑ i ∈ s, (A i).indicator f U) (arrayMeasure N) :=
    integrable_finsetSum s hAf
  have hpt : ∀ U : Array N, f U = B.indicator f U + ∑ i ∈ s, (A i).indicator f U := by
    intro U
    calc f U = (B.indicator (fun _ => (1 : ℝ)) U
          + ∑ i ∈ s, (A i).indicator (fun _ => (1 : ℝ)) U) * f U := by
          rw [hpart U, one_mul]
      _ = B.indicator (fun _ => (1 : ℝ)) U * f U
            + (∑ i ∈ s, (A i).indicator (fun _ => (1 : ℝ)) U) * f U := by rw [add_mul]
      _ = B.indicator f U + ∑ i ∈ s, (A i).indicator f U := by
          rw [Finset.sum_mul]
          congr 1
          · by_cases hU : U ∈ B
            · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU]; ring
            · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]; ring
          · refine Finset.sum_congr rfl fun i _ => ?_
            by_cases hU : U ∈ A i
            · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU]; ring
            · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]; ring
  have hIf : ∫ U, f U ∂(arrayMeasure N)
      = ∫ U in B, f U ∂(arrayMeasure N)
        + ∑ i ∈ s, ∫ U in A i, f U ∂(arrayMeasure N) := by
    calc ∫ U, f U ∂(arrayMeasure N)
        = ∫ U, (B.indicator f U + ∑ i ∈ s, (A i).indicator f U) ∂(arrayMeasure N) :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = ∫ U, B.indicator f U ∂(arrayMeasure N)
            + ∫ U, ∑ i ∈ s, (A i).indicator f U ∂(arrayMeasure N) := integral_add hBf hsumf
      _ = ∫ U in B, f U ∂(arrayMeasure N)
            + ∑ i ∈ s, ∫ U in A i, f U ∂(arrayMeasure N) := by
          rw [integral_finsetSum s hAf, integral_indicator hBm]
          exact congrArg₂ (fun a b => a + b) rfl
            (Finset.sum_congr rfl fun i hi => integral_indicator (hAm i hi))
  have h1 : ∫ U in B, wB U ∂(arrayMeasure N) ≤ ∫ U in B, f U ∂(arrayMeasure N) :=
    setIntegral_le_setIntegral_of_condExp hBm hf hwB hB
  have h2 : ∀ i ∈ s, ∫ U in A i, w i U ∂(arrayMeasure N) ≤ ∫ U in A i, f U ∂(arrayMeasure N) :=
    fun i hi => setIntegral_le_setIntegral_of_condExp (hAm i hi) hf (hw i hi) (hA i hi)
  calc (∫ U in B, wB U ∂(arrayMeasure N))
        + ∑ i ∈ s, ∫ U in A i, w i U ∂(arrayMeasure N)
      ≤ ∫ U in B, f U ∂(arrayMeasure N)
        + ∑ i ∈ s, ∫ U in A i, f U ∂(arrayMeasure N) := add_le_add h1 (Finset.sum_le_sum h2)
    _ = ∫ U, f U ∂(arrayMeasure N) := hIf.symm


/-! ### Measurability of the above-record pieces -/

theorem measurableSet_abovePosSet_w (p : ℝ) (m n : ℕ) (i j : Fin N) (g : ℕ) :
    MeasurableSet (abovePosSet p m n i j g) :=
  infoPiece_le p m n j g _ (measurableSet_abovePosSet p m n i j g g)

/-- Integrability of the global weight, from its decomposition onto the finite partition. -/
theorem integrable_campaignWeight_w {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n : ℕ) (i j : Fin N) :
    Integrable (campaignWeight p m n i j) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hBm : MeasurableSet (belowSet p m n i j) := measurableSet_belowSet p m n i j
  have hpiece : Integrable (fun U => (belowSet p m n i j).indicator
      (fun U => -(bRec p m n j U)) U
        + ∑ g ∈ Finset.range (n + 1),
            (abovePosSet p m n i j g).indicator (offsetWeight p m n j g) U)
      (arrayMeasure N) :=
    ((integrable_bRec_w hp1 hp2 m n j).neg.indicator hBm).add
      (integrable_finsetSum _ (fun g _ =>
        (integrable_offsetWeight_w hp1 hp2 m n j g).indicator
          (measurableSet_abovePosSet_w p m n i j g)))
  exact hpiece.congr (Filter.Eventually.of_forall fun U =>
    (campaignWeight_eq_pieces p m n i j U).symm)

/-! ### The campaign budget: the real integral of the actual increment -/

/-- **The exact piecewise expansion of the global campaign weight's integral**, with the record
row `g = 0` separated from the above-record rows `g ≥ 1` (`Finset.range n` shifted by one). -/
theorem integral_campaignWeight_eq {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n : ℕ) (i j : Fin N) :
    ∫ U, campaignWeight p m n i j U ∂(arrayMeasure N)
      = (∫ U in belowSet p m n i j, (-(bRec p m n j U)) ∂(arrayMeasure N))
        + (∫ U in abovePosSet p m n i j 0, (1 - bRec p m n j U) ∂(arrayMeasure N))
        + ∑ g ∈ Finset.range n, ∫ U in abovePosSet p m n i j (g + 1),
            (-(bRec p m n j U * aRec p m ^ (g + 1))) ∂(arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hBm : MeasurableSet (belowSet p m n i j) := measurableSet_belowSet p m n i j
  have hmeas : ∀ g : ℕ, MeasurableSet (abovePosSet p m n i j g) :=
    fun g => measurableSet_abovePosSet_w p m n i j g
  have hBint : Integrable (fun U => (belowSet p m n i j).indicator
      (fun U => -(bRec p m n j U)) U) (arrayMeasure N) :=
    (integrable_bRec_w hp1 hp2 m n j).neg.indicator hBm
  have hAint : ∀ g ∈ Finset.range (n + 1), Integrable (fun U =>
      (abovePosSet p m n i j g).indicator (offsetWeight p m n j g) U) (arrayMeasure N) :=
    fun g _ => (integrable_offsetWeight_w hp1 hp2 m n j g).indicator (hmeas g)
  have hsumint : Integrable (fun U => ∑ g ∈ Finset.range (n + 1),
      (abovePosSet p m n i j g).indicator (offsetWeight p m n j g) U) (arrayMeasure N) :=
    integrable_finsetSum _ hAint
  calc ∫ U, campaignWeight p m n i j U ∂(arrayMeasure N)
      = ∫ U, ((belowSet p m n i j).indicator (fun U => -(bRec p m n j U)) U
          + ∑ g ∈ Finset.range (n + 1),
              (abovePosSet p m n i j g).indicator (offsetWeight p m n j g) U)
          ∂(arrayMeasure N) :=
        integral_congr_ae (Filter.Eventually.of_forall fun U =>
          campaignWeight_eq_pieces p m n i j U)
    _ = (∫ U, (belowSet p m n i j).indicator (fun U => -(bRec p m n j U)) U
          ∂(arrayMeasure N))
        + (∫ U, ∑ g ∈ Finset.range (n + 1),
            (abovePosSet p m n i j g).indicator (offsetWeight p m n j g) U
          ∂(arrayMeasure N)) := integral_add hBint hsumint
    _ = (∫ U in belowSet p m n i j, (-(bRec p m n j U)) ∂(arrayMeasure N))
        + ∑ g ∈ Finset.range (n + 1),
            ∫ U in abovePosSet p m n i j g, offsetWeight p m n j g U ∂(arrayMeasure N) := by
        rw [integral_finsetSum _ hAint, integral_indicator hBm]
        congr 1
        exact Finset.sum_congr rfl fun g _ => integral_indicator (hmeas g)
    _ = (∫ U in belowSet p m n i j, (-(bRec p m n j U)) ∂(arrayMeasure N))
        + ((∫ U in abovePosSet p m n i j 0, (1 - bRec p m n j U) ∂(arrayMeasure N))
          + ∑ g ∈ Finset.range n, ∫ U in abovePosSet p m n i j (g + 1),
              (-(bRec p m n j U * aRec p m ^ (g + 1))) ∂(arrayMeasure N)) := by
        rw [Finset.sum_range_succ']
        have h0 : (∫ U in abovePosSet p m n i j 0, offsetWeight p m n j 0 U
            ∂(arrayMeasure N))
            = ∫ U in abovePosSet p m n i j 0, (1 - bRec p m n j U) ∂(arrayMeasure N) := rfl
        rw [h0]
        have hsucc : ∀ g : ℕ, (∫ U in abovePosSet p m n i j (g + 1),
            offsetWeight p m n j (g + 1) U ∂(arrayMeasure N))
            = ∫ U in abovePosSet p m n i j (g + 1),
                (-(bRec p m n j U * aRec p m ^ (g + 1))) ∂(arrayMeasure N) := fun g => rfl
        simp only [hsucc]
        ring
    _ = (∫ U in belowSet p m n i j, (-(bRec p m n j U)) ∂(arrayMeasure N))
        + (∫ U in abovePosSet p m n i j 0, (1 - bRec p m n j U) ∂(arrayMeasure N))
        + ∑ g ∈ Finset.range n, ∫ U in abovePosSet p m n i j (g + 1),
            (-(bRec p m n j U * aRec p m ^ (g + 1))) ∂(arrayMeasure N) := by ring

/-- **The campaign budget, in piecewise set-integral form.**

Inputs (explicit hypotheses, identified in the README):

* `hBelow` : the below-record restricted `enlFilt` bound `1_B·(-b_n) ≤ᵐ E[1_B inc | F_n]`
  (the audited below-record candidate, Direction C/D);
* `hAbove` : the above-record restricted `enlFilt` bound `1_{A_g}·(-b_n a^g) ≤ᵐ E[1_{A_g} inc]`
  for `1 ≤ g ≤ n` (Direction A — the random-`alpha` tower step).

The record row `g = 0` is *not* a hypothesis: it is the integrated
`RecordTower.indicator_le_condExp_indicator_HpotInc_zero`. -/
theorem integral_HpotInc_ge_budget {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m n : ℕ} {i j : Fin N} (hij : i ≠ j)
    (hBelow : (fun U => (belowSet p m n i j).indicator (fun U => -(bRec p m n j U)) U)
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        ((belowSet p m n i j).indicator (HpotInc p m n i j)))
    (hAbove : ∀ g : ℕ, 1 ≤ g → g ≤ n →
      (fun U => (abovePosSet p m n i j g).indicator
          (fun U => -(bRec p m n j U * aRec p m ^ g)) U)
        ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
          ((abovePosSet p m n i j g).indicator (HpotInc p m n i j))) :
    (∫ U in belowSet p m n i j, (-(bRec p m n j U)) ∂(arrayMeasure N))
      + (∫ U in abovePosSet p m n i j 0, (1 - bRec p m n j U) ∂(arrayMeasure N))
      + ∑ g ∈ Finset.range n, ∫ U in abovePosSet p m n i j (g + 1),
          (-(bRec p m n j U * aRec p m ^ (g + 1))) ∂(arrayMeasure N)
    ≤ ∫ U, HpotInc p m n i j U ∂(arrayMeasure N) := by
  have hpne : p ≠ 0 := by linarith
  have hf : Integrable (HpotInc p m n i j) (arrayMeasure N) :=
    integrable_HpotInc hp1 hp2 hpne m n i j
  have hpiece : ∀ g ∈ Finset.range (n + 1),
      (fun U => (abovePosSet p m n i j g).indicator (offsetWeight p m n j g) U)
        ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
          ((abovePosSet p m n i j g).indicator (HpotInc p m n i j)) := by
    intro g hg
    match g with
    | 0 =>
        have hw : offsetWeight p m n j 0 = (fun U => 1 - bRec p m n j U) := rfl
        rw [hw]
        exact indicator_le_condExp_indicator_HpotInc_zero (N := N) p hp1 hp2 m n hij
    | (k + 1) =>
        have hk : k + 1 ≤ n := by
          have := Finset.mem_range.mp hg
          omega
        have hw : offsetWeight p m n j (k + 1)
            = (fun U => -(bRec p m n j U * aRec p m ^ (k + 1))) := rfl
        rw [hw]
        exact hAbove (k + 1) (by omega) hk
  have hmain := integral_piecewise_bound (s := Finset.range (n + 1)) (p := p) (m := m) (n := n)
    (B := belowSet p m n i j) (wB := fun U => -(bRec p m n j U))
    (A := fun g => abovePosSet p m n i j g) (w := fun g => offsetWeight p m n j g)
    (f := HpotInc p m n i j)
    (indicator_belowSet_add_sum_abovePosSet p m n i j)
    (measurableSet_belowSet p m n i j)
    (fun g _ => measurableSet_abovePosSet_w p m n i j g)
    hf
    ((integrable_bRec_w hp1 hp2 m n j).neg)
    (fun g _ => integrable_offsetWeight_w hp1 hp2 m n j g)
    hBelow hpiece
  have hsplit : ∑ g ∈ Finset.range (n + 1),
      ∫ U in abovePosSet p m n i j g, offsetWeight p m n j g U ∂(arrayMeasure N)
      = (∫ U in abovePosSet p m n i j 0, (1 - bRec p m n j U) ∂(arrayMeasure N))
        + ∑ g ∈ Finset.range n, ∫ U in abovePosSet p m n i j (g + 1),
            (-(bRec p m n j U * aRec p m ^ (g + 1))) ∂(arrayMeasure N) := by
    rw [Finset.sum_range_succ']
    have h0 : (∫ U in abovePosSet p m n i j 0, offsetWeight p m n j 0 U
        ∂(arrayMeasure N))
        = ∫ U in abovePosSet p m n i j 0, (1 - bRec p m n j U) ∂(arrayMeasure N) := rfl
    rw [h0]
    have hsucc : ∀ g : ℕ, (∫ U in abovePosSet p m n i j (g + 1),
        offsetWeight p m n j (g + 1) U ∂(arrayMeasure N))
        = ∫ U in abovePosSet p m n i j (g + 1),
            (-(bRec p m n j U * aRec p m ^ (g + 1))) ∂(arrayMeasure N) := fun g => rfl
    simp only [hsucc]
    ring
  linarith [hmain, hsplit]

/-- **The headline integral budget.**  Under the two explicit regional hypotheses, the
unconditional expectation of the actual one-step `Hpot` increment dominates the integral of the
piecewise global campaign weight. -/
theorem integral_HpotInc_ge_campaignWeight {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m n : ℕ} {i j : Fin N} (hij : i ≠ j)
    (hBelow : (fun U => (belowSet p m n i j).indicator (fun U => -(bRec p m n j U)) U)
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        ((belowSet p m n i j).indicator (HpotInc p m n i j)))
    (hAbove : ∀ g : ℕ, 1 ≤ g → g ≤ n →
      (fun U => (abovePosSet p m n i j g).indicator
          (fun U => -(bRec p m n j U * aRec p m ^ g)) U)
        ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
          ((abovePosSet p m n i j g).indicator (HpotInc p m n i j))) :
    ∫ U, campaignWeight p m n i j U ∂(arrayMeasure N)
      ≤ ∫ U, HpotInc p m n i j U ∂(arrayMeasure N) := by
  have h1 := integral_HpotInc_ge_budget (N := N) (p := p) hp1 hp2 hij hBelow hAbove
  have h2 := integral_campaignWeight_eq (N := N) (p := p) hp1 hp2 m n i j
  linarith [h1, h2]


/-! ### The paper's `(Zloss)` weight, and the exact remainder

The paper's one-step weight (`SwarmOcc.Zloss`'s left-hand side, at the actual record `r = M_n^j`,
`x = X_n^i`, `b = b_n`, `a = aRec p m`) is

  `1{0 ≤ x ≤ r} - b_n a^{(x-r)} 1{r ≤ x}`.

It is *not* the campaign weight: below the record the paper pays `1` on the interior `0 ≤ x < r`
and `0` below zero, while the campaign only carries the worst case `-b_n`.  The difference is
computed exactly below; nothing is silently absorbed. -/

/-- The paper's `(Zloss)` weight at the actual record. -/
noncomputable def paperWeight (p : ℝ) (m n : ℕ) (i j : Fin N) (U : Array N) : ℝ :=
  (if 0 ≤ (trajectory p m U n).pos i ∧ (trajectory p m U n).pos i ≤ runMax p m U j n
      then (1 : ℝ) else 0)
    - bRec p m n j U * (if runMax p m U j n ≤ (trajectory p m U n).pos i then
        aRec p m ^ ((trajectory p m U n).pos i - runMax p m U j n).toNat else 0)

/-- The gain indicator `1{0 ≤ X_n^i}`. -/
noncomputable def posWeight (p : ℝ) (m n : ℕ) (i : Fin N) (U : Array N) : ℝ :=
  if 0 ≤ (trajectory p m U n).pos i then 1 else 0

/-- **The exact weight comparison.**  The paper's weight is the campaign weight plus the
below-region remainder `1_B · (1{0 ≤ X_n^i} + b_n)`; at and above the record the two weights
coincide row by row (`1 - b_n` at offset `0`, `-b_n a^g` at offset `g ≥ 1`). -/
theorem paperWeight_eq_campaignWeight_add_below (p : ℝ) (m n : ℕ) (i j : Fin N) (U : Array N) :
    paperWeight p m n i j U
      = campaignWeight p m n i j U
        + (belowSet p m n i j).indicator
            (fun U => posWeight p m n i U + bRec p m n j U) U := by
  by_cases hU : U ∈ belowSet p m n i j
  · have hlt : (trajectory p m U n).pos i < runMax p m U j n :=
      (mem_belowSet_iff_lt p m n i j U).mp hU
    have hnot : ¬ runMax p m U j n ≤ (trajectory p m U n).pos i := not_le.mpr hlt
    have hle : (trajectory p m U n).pos i ≤ runMax p m U j n := le_of_lt hlt
    rw [paperWeight, campaignWeight, if_pos hlt, if_neg hnot, Set.indicator_of_mem hU, posWeight]
    by_cases h0 : 0 ≤ (trajectory p m U n).pos i
    · rw [if_pos ⟨h0, hle⟩, if_pos h0]
      ring
    · rw [if_neg (fun h => h0 h.1), if_neg h0]
      ring
  · have hge : runMax p m U j n ≤ (trajectory p m U n).pos i :=
      not_lt.mp (fun h => hU ((mem_belowSet_iff_lt p m n i j U).mpr h))
    have hind : (belowSet p m n i j).indicator
        (fun U => posWeight p m n i U + bRec p m n j U) U = 0 :=
      Set.indicator_of_notMem (f := fun U => posWeight p m n i U + bRec p m n j U) hU
    rw [hind, add_zero, paperWeight, campaignWeight, if_neg (not_lt.mpr hge)]
    by_cases hEq : (trajectory p m U n).pos i = runMax p m U j n
    · rw [if_pos hEq]
      have h0le : 0 ≤ (trajectory p m U n).pos i := by
        rw [hEq]
        exact zero_le_runMax p m U j n
      rw [if_pos ⟨h0le, le_of_eq hEq⟩, if_pos (le_of_eq hEq.symm)]
      have hzero : ((trajectory p m U n).pos i - runMax p m U j n).toNat = 0 := by
        rw [hEq]
        simp
      rw [hzero, pow_zero, mul_one]
      change 1 - bRec p m n j U = recordWeight p m n j U
      rfl
    · rw [if_neg hEq]
      have hgt : runMax p m U j n < (trajectory p m U n).pos i :=
        lt_of_le_of_ne hge (Ne.symm hEq)
      rw [if_neg (fun h : 0 ≤ (trajectory p m U n).pos i
        ∧ (trajectory p m U n).pos i ≤ runMax p m U j n => absurd h.2 (not_le.mpr hgt)),
        if_pos hge]
      change 0 - bRec p m n j U
          * aRec p m ^ ((trajectory p m U n).pos i - runMax p m U j n).toNat
        = aboveWeight p m n j ((trajectory p m U n).pos i - runMax p m U j n).toNat U
      change 0 - bRec p m n j U
          * aRec p m ^ ((trajectory p m U n).pos i - runMax p m U j n).toNat
        = -(bRec p m n j U
          * aRec p m ^ ((trajectory p m U n).pos i - runMax p m U j n).toNat)
      ring

/-! ### Integrability of the paper weight and of the gain indicator -/

theorem measurable_posWeight (p : ℝ) (m n : ℕ) (i : Fin N) : Measurable (posWeight p m n i) := by
  have hmeas : Measurable fun U : Array N => (trajectory p m U n).pos i :=
    (Swarming.Fair.measurable_trajectory (N := N) p m n).1 i
  exact Measurable.ite (measurableSet_le measurable_const hmeas) measurable_const measurable_const

theorem integrable_posWeight_w (p : ℝ) (m n : ℕ) (i : Fin N) :
    Integrable (posWeight p m n i) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  refine Integrable.mono' (integrable_const (1 : ℝ)) (measurable_posWeight p m n i).aestronglyMeasurable
    (Filter.Eventually.of_forall fun U => ?_)
  rw [Real.norm_eq_abs, posWeight]
  split_ifs <;> simp

/-- Integrability of the paper weight, from the exact comparison and the piecewise expansion. -/
theorem integrable_paperWeight_w {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n : ℕ) (i j : Fin N) : Integrable (paperWeight p m n i j) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hBm : MeasurableSet (belowSet p m n i j) := measurableSet_belowSet p m n i j
  have hrem : Integrable (fun U => (belowSet p m n i j).indicator
      (fun U => posWeight p m n i U + bRec p m n j U) U) (arrayMeasure N) :=
    ((integrable_posWeight_w p m n i).add (integrable_bRec_w hp1 hp2 m n j)).indicator hBm
  have hsum := (integrable_campaignWeight_w (N := N) (p := p) hp1 hp2 m n i j).add hrem
  exact hsum.congr (Filter.Eventually.of_forall fun U =>
    (paperWeight_eq_campaignWeight_add_below p m n i j U).symm)

/-! ### The paper's budget -/

/-- **The below-region cancellation.**  The campaign's below row `-b_n` plus the remainder
`1{0 ≤ x} + b_n` is exactly the paper's below row `1{0 ≤ x}`. -/
theorem below_cancellation {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m n : ℕ) (i j : Fin N) :
    (∫ U in belowSet p m n i j, (-(bRec p m n j U)) ∂(arrayMeasure N))
      + (∫ U in belowSet p m n i j,
          (posWeight p m n i U + bRec p m n j U) ∂(arrayMeasure N))
      = ∫ U in belowSet p m n i j, posWeight p m n i U ∂(arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hBm : MeasurableSet (belowSet p m n i j) := measurableSet_belowSet p m n i j
  have hi1 : Integrable (fun U => (belowSet p m n i j).indicator
      (fun U => -(bRec p m n j U)) U) (arrayMeasure N) :=
    (integrable_bRec_w hp1 hp2 m n j).neg.indicator hBm
  have hi2 : Integrable (fun U => (belowSet p m n i j).indicator
      (fun U => posWeight p m n i U + bRec p m n j U) U) (arrayMeasure N) :=
    ((integrable_posWeight_w p m n i).add (integrable_bRec_w hp1 hp2 m n j)).indicator hBm
  have h1 : (∫ U in belowSet p m n i j, (-(bRec p m n j U)) ∂(arrayMeasure N))
      = ∫ U, (belowSet p m n i j).indicator (fun U => -(bRec p m n j U)) U
          ∂(arrayMeasure N) := (integral_indicator hBm).symm
  have h2 : (∫ U in belowSet p m n i j, (posWeight p m n i U + bRec p m n j U)
        ∂(arrayMeasure N))
      = ∫ U, (belowSet p m n i j).indicator
          (fun U => posWeight p m n i U + bRec p m n j U) U ∂(arrayMeasure N) :=
    (integral_indicator hBm).symm
  have h3 : (∫ U in belowSet p m n i j, posWeight p m n i U ∂(arrayMeasure N))
      = ∫ U, (belowSet p m n i j).indicator (fun U => posWeight p m n i U) U
          ∂(arrayMeasure N) := (integral_indicator hBm).symm
  rw [h1, h2, h3, ← integral_add hi1 hi2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  show (belowSet p m n i j).indicator (fun U => -(bRec p m n j U)) U
      + (belowSet p m n i j).indicator (fun U => posWeight p m n i U + bRec p m n j U) U
      = (belowSet p m n i j).indicator (fun U => posWeight p m n i U) U
  by_cases hU : U ∈ belowSet p m n i j
  · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU, Set.indicator_of_mem hU]; ring
  · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]; ring

/-- **The integral of the global campaign weight, written through the paper weight.** -/
theorem integral_paperWeight_eq {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n : ℕ) (i j : Fin N) :
    ∫ U, paperWeight p m n i j U ∂(arrayMeasure N)
      = (∫ U in belowSet p m n i j, posWeight p m n i U ∂(arrayMeasure N))
        + (∫ U in abovePosSet p m n i j 0, (1 - bRec p m n j U) ∂(arrayMeasure N))
        + ∑ g ∈ Finset.range n, ∫ U in abovePosSet p m n i j (g + 1),
            (-(bRec p m n j U * aRec p m ^ (g + 1))) ∂(arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hBm : MeasurableSet (belowSet p m n i j) := measurableSet_belowSet p m n i j
  have hrem : Integrable (fun U => (belowSet p m n i j).indicator
      (fun U => posWeight p m n i U + bRec p m n j U) U) (arrayMeasure N) :=
    ((integrable_posWeight_w p m n i).add (integrable_bRec_w hp1 hp2 m n j)).indicator hBm
  have hcamp := integral_campaignWeight_eq (N := N) (p := p) hp1 hp2 m n i j
  have hadd : ∫ U, paperWeight p m n i j U ∂(arrayMeasure N)
      = ∫ U, campaignWeight p m n i j U ∂(arrayMeasure N)
        + ∫ U in belowSet p m n i j,
            (posWeight p m n i U + bRec p m n j U) ∂(arrayMeasure N) := by
    calc ∫ U, paperWeight p m n i j U ∂(arrayMeasure N)
        = ∫ U, (campaignWeight p m n i j U + (belowSet p m n i j).indicator
            (fun U => posWeight p m n i U + bRec p m n j U) U) ∂(arrayMeasure N) :=
          integral_congr_ae (Filter.Eventually.of_forall fun U =>
            paperWeight_eq_campaignWeight_add_below p m n i j U)
      _ = ∫ U, campaignWeight p m n i j U ∂(arrayMeasure N)
            + ∫ U, (belowSet p m n i j).indicator
                (fun U => posWeight p m n i U + bRec p m n j U) U ∂(arrayMeasure N) :=
          integral_add (integrable_campaignWeight_w hp1 hp2 m n i j) hrem
      _ = ∫ U, campaignWeight p m n i j U ∂(arrayMeasure N)
            + ∫ U in belowSet p m n i j,
                (posWeight p m n i U + bRec p m n j U) ∂(arrayMeasure N) := by
          rw [integral_indicator hBm]
  linarith [hadd, hcamp, below_cancellation (p := p) hp1 hp2 m n i j]


/-! ### The offset sum split (`g = 0` versus `g ≥ 1`), factored out -/

/-- The finite offset sum split at `g = 0`. -/
theorem sum_setIntegral_offsetWeight_eq (p : ℝ) (m n : ℕ) (i j : Fin N) :
    ∑ g ∈ Finset.range (n + 1),
        ∫ U in abovePosSet p m n i j g, offsetWeight p m n j g U ∂(arrayMeasure N)
      = (∫ U in abovePosSet p m n i j 0, (1 - bRec p m n j U) ∂(arrayMeasure N))
        + ∑ g ∈ Finset.range n, ∫ U in abovePosSet p m n i j (g + 1),
            (-(bRec p m n j U * aRec p m ^ (g + 1))) ∂(arrayMeasure N) := by
  rw [Finset.sum_range_succ']
  have h0 : (∫ U in abovePosSet p m n i j 0, offsetWeight p m n j 0 U
      ∂(arrayMeasure N))
      = ∫ U in abovePosSet p m n i j 0, (1 - bRec p m n j U) ∂(arrayMeasure N) := rfl
  rw [h0]
  have hsucc : ∀ g : ℕ, (∫ U in abovePosSet p m n i j (g + 1),
      offsetWeight p m n j (g + 1) U ∂(arrayMeasure N))
      = ∫ U in abovePosSet p m n i j (g + 1),
          (-(bRec p m n j U * aRec p m ^ (g + 1))) ∂(arrayMeasure N) := fun g => rfl
  simp only [hsucc]
  ring

/-! ### The paper-level budget

With the *sharpened* below-record bound (the paper's interior gain `1` on `0 ≤ x < r` and `0`
below zero, which the below-record candidate proves pointwise), the same assembly yields the
paper's weight exactly. -/

/-- **The paper-level budget.**  With the sharpened below-region bound, the real integral of the
actual one-step increment dominates the paper's one-step weight `paperWeight` (the left-hand side
of `SwarmOcc.Zloss`). -/
theorem integral_HpotInc_ge_paper_pieces {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m n : ℕ} {i j : Fin N} (hij : i ≠ j)
    (hBelowSharp : (fun U => (belowSet p m n i j).indicator
        (fun U => posWeight p m n i U) U)
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        ((belowSet p m n i j).indicator (HpotInc p m n i j)))
    (hAbove : ∀ g : ℕ, 1 ≤ g → g ≤ n →
      (fun U => (abovePosSet p m n i j g).indicator
          (fun U => -(bRec p m n j U * aRec p m ^ g)) U)
        ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
          ((abovePosSet p m n i j g).indicator (HpotInc p m n i j))) :
    (∫ U in belowSet p m n i j, posWeight p m n i U ∂(arrayMeasure N))
      + (∫ U in abovePosSet p m n i j 0, (1 - bRec p m n j U) ∂(arrayMeasure N))
      + ∑ g ∈ Finset.range n, ∫ U in abovePosSet p m n i j (g + 1),
          (-(bRec p m n j U * aRec p m ^ (g + 1))) ∂(arrayMeasure N)
    ≤ ∫ U, HpotInc p m n i j U ∂(arrayMeasure N) := by
  have hpne : p ≠ 0 := by linarith
  have hf : Integrable (HpotInc p m n i j) (arrayMeasure N) :=
    integrable_HpotInc hp1 hp2 hpne m n i j
  have hpiece : ∀ g ∈ Finset.range (n + 1),
      (fun U => (abovePosSet p m n i j g).indicator (offsetWeight p m n j g) U)
        ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
          ((abovePosSet p m n i j g).indicator (HpotInc p m n i j)) := by
    intro g hg
    match g with
    | 0 =>
        have hw : offsetWeight p m n j 0 = (fun U => 1 - bRec p m n j U) := rfl
        rw [hw]
        exact indicator_le_condExp_indicator_HpotInc_zero (N := N) p hp1 hp2 m n hij
    | (k + 1) =>
        have hk : k + 1 ≤ n := by
          have := Finset.mem_range.mp hg
          omega
        have hw : offsetWeight p m n j (k + 1)
            = (fun U => -(bRec p m n j U * aRec p m ^ (k + 1))) := rfl
        rw [hw]
        exact hAbove (k + 1) (by omega) hk
  have hmain := integral_piecewise_bound (s := Finset.range (n + 1)) (p := p) (m := m) (n := n)
    (B := belowSet p m n i j) (wB := posWeight p m n i)
    (A := fun g => abovePosSet p m n i j g) (w := fun g => offsetWeight p m n j g)
    (f := HpotInc p m n i j)
    (indicator_belowSet_add_sum_abovePosSet p m n i j)
    (measurableSet_belowSet p m n i j)
    (fun g _ => measurableSet_abovePosSet_w p m n i j g)
    hf
    (integrable_posWeight_w p m n i)
    (fun g _ => integrable_offsetWeight_w hp1 hp2 m n j g)
    hBelowSharp hpiece
  linarith [hmain, sum_setIntegral_offsetWeight_eq (p := p) m n i j]

/-- **The paper weight is the campaign budget's exact sharpening.**  With the sharpened
below-region bound the integral of the paper's `(Zloss)` weight is dominated by the increment. -/
theorem integral_HpotInc_ge_paperWeight {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m n : ℕ} {i j : Fin N} (hij : i ≠ j)
    (hBelowSharp : (fun U => (belowSet p m n i j).indicator
        (fun U => posWeight p m n i U) U)
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        ((belowSet p m n i j).indicator (HpotInc p m n i j)))
    (hAbove : ∀ g : ℕ, 1 ≤ g → g ≤ n →
      (fun U => (abovePosSet p m n i j g).indicator
          (fun U => -(bRec p m n j U * aRec p m ^ g)) U)
        ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
          ((abovePosSet p m n i j g).indicator (HpotInc p m n i j))) :
    ∫ U, paperWeight p m n i j U ∂(arrayMeasure N)
      ≤ ∫ U, HpotInc p m n i j U ∂(arrayMeasure N) := by
  have h1 := integral_HpotInc_ge_paper_pieces (N := N) (p := p) hp1 hp2 hij hBelowSharp hAbove
  have h2 := integral_paperWeight_eq (N := N) (p := p) hp1 hp2 m n i j
  linarith [h1, h2]

/-- **The exact integral-level remainder.**  The paper weight's integral exceeds the campaign
weight's integral by exactly the below-region remainder `∫_B (1{0 ≤ X_n^i} + b_n)`. -/
theorem integral_paperWeight_sub_campaignWeight {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n : ℕ) (i j : Fin N) :
    (∫ U, paperWeight p m n i j U ∂(arrayMeasure N))
        - ∫ U, campaignWeight p m n i j U ∂(arrayMeasure N)
      = ∫ U in belowSet p m n i j, (posWeight p m n i U + bRec p m n j U)
          ∂(arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hBm : MeasurableSet (belowSet p m n i j) := measurableSet_belowSet p m n i j
  have hrem : Integrable (fun U => (belowSet p m n i j).indicator
      (fun U => posWeight p m n i U + bRec p m n j U) U) (arrayMeasure N) :=
    ((integrable_posWeight_w p m n i).add (integrable_bRec_w hp1 hp2 m n j)).indicator hBm
  have hdiff : (∫ U, paperWeight p m n i j U ∂(arrayMeasure N))
      - ∫ U, campaignWeight p m n i j U ∂(arrayMeasure N)
      = ∫ U, (belowSet p m n i j).indicator
          (fun U => posWeight p m n i U + bRec p m n j U) U ∂(arrayMeasure N) := by
    rw [← integral_sub (integrable_paperWeight_w hp1 hp2 m n i j)
      (integrable_campaignWeight_w hp1 hp2 m n i j)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    show paperWeight p m n i j U - campaignWeight p m n i j U
      = (belowSet p m n i j).indicator (fun U => posWeight p m n i U + bRec p m n j U) U
    rw [paperWeight_eq_campaignWeight_add_below p m n i j U]
    ring
  rw [hdiff, integral_indicator hBm]

/-- **The campaign bound as "paper weight minus the explicit remainder".**  This is the exact
statement of what the campaign weights give up relative to the paper's `(Zloss)`: nothing else. -/
theorem integral_HpotInc_ge_paperWeight_sub_remainder {p : ℝ} (hp1 : (1 : ℝ) / 2 < p)
    (hp2 : p < 1) {m n : ℕ} {i j : Fin N} (hij : i ≠ j)
    (hBelow : (fun U => (belowSet p m n i j).indicator (fun U => -(bRec p m n j U)) U)
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        ((belowSet p m n i j).indicator (HpotInc p m n i j)))
    (hAbove : ∀ g : ℕ, 1 ≤ g → g ≤ n →
      (fun U => (abovePosSet p m n i j g).indicator
          (fun U => -(bRec p m n j U * aRec p m ^ g)) U)
        ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
          ((abovePosSet p m n i j g).indicator (HpotInc p m n i j))) :
    (∫ U, paperWeight p m n i j U ∂(arrayMeasure N))
        - ∫ U in belowSet p m n i j, (posWeight p m n i U + bRec p m n j U)
            ∂(arrayMeasure N)
      ≤ ∫ U, HpotInc p m n i j U ∂(arrayMeasure N) := by
  have h1 := integral_HpotInc_ge_campaignWeight (N := N) (p := p) hp1 hp2 hij hBelow hAbove
  have h2 := integral_paperWeight_sub_campaignWeight (N := N) (p := p) hp1 hp2 m n i j
  linarith [h1, h2]

/-! ### Bridges to the external regional inputs

These restate the two explicit hypotheses in the exact shapes the other directions produce, so
that the assembly can be fed without re-deriving anything. -/

/-- The below-region hypothesis, read from the trajectory form
`B = {X_n^i < M_n^j}` (the shape of the audited below-record candidate). -/
theorem below_hypothesis_of_lt_runMax {p : ℝ} {m n : ℕ} {i j : Fin N}
    (h : (fun U => ({U : Array N | (trajectory p m U n).pos i < runMax p m U j n}).indicator
        (fun U => -(bRec p m n j U)) U)
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        (({U : Array N | (trajectory p m U n).pos i < runMax p m U j n}).indicator
          (HpotInc p m n i j))) :
    (fun U => (belowSet p m n i j).indicator (fun U => -(bRec p m n j U)) U)
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        ((belowSet p m n i j).indicator (HpotInc p m n i j)) := by
  rwa [belowSet_eq_lt_runMax]

/-- The sharpened (paper) below-region hypothesis, read from the trajectory form. -/
theorem belowSharp_hypothesis_of_lt_runMax {p : ℝ} {m n : ℕ} {i j : Fin N}
    (h : (fun U => ({U : Array N | (trajectory p m U n).pos i < runMax p m U j n}).indicator
        (fun U => posWeight p m n i U) U)
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        (({U : Array N | (trajectory p m U n).pos i < runMax p m U j n}).indicator
          (HpotInc p m n i j))) :
    (fun U => (belowSet p m n i j).indicator (fun U => posWeight p m n i U) U)
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        ((belowSet p m n i j).indicator (HpotInc p m n i j)) := by
  rwa [belowSet_eq_lt_runMax]

/-- The above-record hypothesis for all `g ≥ 1` (the natural shape of Direction A's result),
restricted to the finitely many offsets `g ≤ n` that the partition carries. -/
theorem above_hypothesis_of_all {p : ℝ} {m n : ℕ} {i j : Fin N}
    (h : ∀ g : ℕ, 1 ≤ g →
      (fun U => (abovePosSet p m n i j g).indicator
          (fun U => -(bRec p m n j U * aRec p m ^ g)) U)
        ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
          ((abovePosSet p m n i j g).indicator (HpotInc p m n i j))) :
    ∀ g : ℕ, 1 ≤ g → g ≤ n →
      (fun U => (abovePosSet p m n i j g).indicator
          (fun U => -(bRec p m n j U * aRec p m ^ g)) U)
        ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
          ((abovePosSet p m n i j g).indicator (HpotInc p m n i j)) :=
  fun g h1 _ => h g h1


/-! ### Connection to the integrated `(Zloss)`/`(Vdrift)` interface

`SwarmOcc.Vdrift_combine` (integrated in `Swarm/Vdrift.lean`) consumes the paper's
`(Zloss)` weight in the form

  `Dh ≥ 1{0 ≤ x ≤ r} - b a^{(x-r)} 1{r ≤ x}`,

at `r = r_n`, `x = X_n^i`, `b = b_n`, `a = a^n`.  `paperWeight` is *literally* that expression at
the actual model, so the budget of this file is the input that interface expects — no rescaling,
no changed constant. -/

/-- `paperWeight` is, definitionally, the left-hand side of the `hDh` hypothesis of
`SwarmOcc.Vdrift_combine`. -/
theorem paperWeight_eq_Vdrift_lhs (p : ℝ) (m n : ℕ) (i j : Fin N) (U : Array N) :
    paperWeight p m n i j U
      = (if 0 ≤ (trajectory p m U n).pos i ∧ (trajectory p m U n).pos i ≤ runMax p m U j n
          then (1 : ℝ) else 0)
        - bRec p m n j U * (if runMax p m U j n ≤ (trajectory p m U n).pos i then
            aRec p m ^ ((trajectory p m U n).pos i - runMax p m U j n).toNat else 0) := rfl

/-- The `(Zloss)`-input of `SwarmOcc.Vdrift_combine` is exactly a pointwise lower bound of
`paperWeight`. -/
theorem Vdrift_input_of_paperWeight {p : ℝ} {m n : ℕ} {i j : Fin N} {U : Array N} {Dh : ℝ}
    (h : paperWeight p m n i j U ≤ Dh) :
    (if 0 ≤ (trajectory p m U n).pos i ∧ (trajectory p m U n).pos i ≤ runMax p m U j n
        then (1 : ℝ) else 0)
      - bRec p m n j U * (if runMax p m U j n ≤ (trajectory p m U n).pos i then
          aRec p m ^ ((trajectory p m U n).pos i - runMax p m U j n).toNat else 0) ≤ Dh := h

/-- The gain indicator is nonnegative. -/
theorem posWeight_nonneg (p : ℝ) (m n : ℕ) (i : Fin N) (U : Array N) :
    0 ≤ posWeight p m n i U := by
  rw [posWeight]
  split_ifs <;> norm_num

/-- **The remainder is nonnegative.**  So the campaign budget (`∫ campaignWeight ≤ ∫ inc`) is the
paper budget (`∫ paperWeight ≤ ∫ inc`) minus an explicitly nonnegative amount — the campaign
weights give up exactly `1{0 ≤ X_n^i} + b_n` on the below-record region, and nothing else. -/
theorem integral_remainder_nonneg {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n : ℕ) (i j : Fin N) :
    0 ≤ ∫ U in belowSet p m n i j, (posWeight p m n i U + bRec p m n j U)
        ∂(arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hBm : MeasurableSet (belowSet p m n i j) := measurableSet_belowSet p m n i j
  refine integral_nonneg_of_ae ?_
  refine Filter.Eventually.of_forall fun U => ?_
  exact add_nonneg (posWeight_nonneg p m n i U) (by
    have h3 := three_le_bRec hp1 hp2 m n j U
    linarith)

/-! ### A concrete instantiation check

All constants instantiate: `N = 2`, `p = 3/4`, `m = 2`, `n = 1`, `i ≠ j`.  At `n = 1` the ledger
has the below row, the record row `A_0`, and the single above row `g = 1` (so `range 1` has the
one element `0`, at offset `g = 0 + 1 = 1`). -/

example (i j : Fin 2) (hij : i ≠ j)
    (hBelow : (fun U => (belowSet (3 / 4) 2 1 i j).indicator
        (fun U => -(bRec (3 / 4) 2 1 j U)) U)
      ≤ᵐ[arrayMeasure 2] condExp (enlFilt (3 / 4) 2 1) (arrayMeasure 2)
        ((belowSet (3 / 4) 2 1 i j).indicator (HpotInc (3 / 4) 2 1 i j)))
    (hAbove : ∀ g : ℕ, 1 ≤ g → g ≤ 1 →
      (fun U => (abovePosSet (3 / 4) 2 1 i j g).indicator
          (fun U => -(bRec (3 / 4) 2 1 j U * aRec (3 / 4) 2 ^ g)) U)
        ≤ᵐ[arrayMeasure 2] condExp (enlFilt (3 / 4) 2 1) (arrayMeasure 2)
          ((abovePosSet (3 / 4) 2 1 i j g).indicator (HpotInc (3 / 4) 2 1 i j))) :
    (∫ U in belowSet (3 / 4) 2 1 i j, (-(bRec (3 / 4) 2 1 j U)) ∂(arrayMeasure 2))
      + (∫ U in abovePosSet (3 / 4) 2 1 i j 0,
          (1 - bRec (3 / 4) 2 1 j U) ∂(arrayMeasure 2))
      + ∑ g ∈ Finset.range 1, ∫ U in abovePosSet (3 / 4) 2 1 i j (g + 1),
          (-(bRec (3 / 4) 2 1 j U * aRec (3 / 4) 2 ^ (g + 1))) ∂(arrayMeasure 2)
    ≤ ∫ U, HpotInc (3 / 4) 2 1 i j U ∂(arrayMeasure 2) :=
  integral_HpotInc_ge_budget (p := 3 / 4) (by norm_num) (by norm_num) hij hBelow hAbove


/-- The below-region hypothesis in the *unfolded* increment spelling (the spelling of the
below-record candidate): `HpotInc` is definitionally that expression. -/
theorem below_hypothesis_of_HpotInc_expansion {p : ℝ} {m n : ℕ} {i j : Fin N}
    (h : (fun U => (belowSet p m n i j).indicator (fun U => -(bRec p m n j U)) U)
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        ((belowSet p m n i j).indicator (fun U => SwarmOcc.Hpot (envH p m j U)
          ((trajectory p m U (n + 1)).pos i)
            - SwarmOcc.Hpot (envH p m j U) ((trajectory p m U n).pos i)))) :
    (fun U => (belowSet p m n i j).indicator (fun U => -(bRec p m n j U)) U)
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        ((belowSet p m n i j).indicator (HpotInc p m n i j)) := h

/-- The same below-region hypothesis read with the **record value** `recVal j (prefOf p m n ·)`
instead of the running maximum; the two are equal on the actual trajectory. -/
theorem below_hypothesis_of_lt_recVal {p : ℝ} {m n : ℕ} {i j : Fin N}
    (h : (fun U => ({U : Array N | (trajectory p m U n).pos i < recVal j (prefOf p m n U)}).indicator
        (fun U => -(bRec p m n j U)) U)
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        (({U : Array N | (trajectory p m U n).pos i < recVal j (prefOf p m n U)}).indicator
          (HpotInc p m n i j))) :
    (fun U => (belowSet p m n i j).indicator (fun U => -(bRec p m n j U)) U)
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        ((belowSet p m n i j).indicator (HpotInc p m n i j)) := by
  rwa [belowSet_eq_lt_recVal]


/-! ### Integrating Direction F's pointwise `enlFilt` bound directly

Direction F's assembly states the a.e. pointwise inequality
`globalWeight ≤ᵐ E[HpotInc | enlFilt n]`.  Integrating such a statement is the other half of the
bookkeeping, and it is independent of how the pointwise inequality was obtained (piecewise rows
or otherwise). -/

/-- **Integration of a pointwise `enlFilt` lower bound**: if a weight `w` is dominated a.e. by the
`enlFilt n`-conditional mean of the increment, its integral is dominated by the integral of the
increment. -/
theorem integral_le_of_condExp_ge {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m n : ℕ} {i j : Fin N} {w : Array N → ℝ}
    (hw : Integrable w (arrayMeasure N))
    (h : w ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j)) :
    ∫ U, w U ∂(arrayMeasure N) ≤ ∫ U, HpotInc p m n i j U ∂(arrayMeasure N) := by
  have hpne : p ≠ 0 := by linarith
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hle : enlFilt p m n ≤ (inferInstance : MeasurableSpace (Array N)) := (enlFilt p m).le n
  haveI : SigmaFinite ((arrayMeasure N).trim hle) := inferInstance
  have hmono := integral_mono_ae hw integrable_condExp h
  rwa [integral_condExp hle] at hmono

/-- The same statement for the campaign weight itself: a pointwise `enlFilt` bound of Direction F
yields the campaign integral budget directly, without the two regional hypotheses. -/
theorem integral_campaignWeight_le_of_condExp {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m n : ℕ} {i j : Fin N}
    (h : campaignWeight p m n i j
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j)) :
    ∫ U, campaignWeight p m n i j U ∂(arrayMeasure N)
      ≤ ∫ U, HpotInc p m n i j U ∂(arrayMeasure N) :=
  integral_le_of_condExp_ge (N := N) (p := p) hp1 hp2
    (integrable_campaignWeight_w hp1 hp2 m n i j) h


/-- **The below-region hypothesis, accepted verbatim from the below-record candidate.**

The (unaccepted, audited by Direction C) below-record module states

  `1_{B} · (-b_n) ≤ᵐ E[ 1_{B} · (Hpot h_j(X_{n+1}^i) - Hpot h_j(X_n^i)) | enlFilt n ]`,
  `B = {U | (trajectory p m U n).pos i < runMax p m U j n}`.

This lemma converts exactly that statement into the hypothesis this file consumes: the region is
the same (`belowSet_eq_lt_runMax`), and the increment spelling is the common `HpotInc`
(definitionally the same expression). -/
theorem below_hypothesis_of_belowRec {p : ℝ} {m n : ℕ} {i j : Fin N}
    (h : (fun U => ({U : Array N | (trajectory p m U n).pos i < runMax p m U j n}).indicator
        (fun U => -(bRec p m n j U)) U)
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        (({U : Array N | (trajectory p m U n).pos i < runMax p m U j n}).indicator
          (fun U => SwarmOcc.Hpot (envH p m j U) ((trajectory p m U (n + 1)).pos i)
            - SwarmOcc.Hpot (envH p m j U) ((trajectory p m U n).pos i)))) :
    (fun U => (belowSet p m n i j).indicator (fun U => -(bRec p m n j U)) U)
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        ((belowSet p m n i j).indicator (HpotInc p m n i j)) := by
  have hset : ({U : Array N | (trajectory p m U n).pos i < runMax p m U j n})
      = belowSet p m n i j := (belowSet_eq_lt_runMax p m n i j).symm
  have hinc : (fun U => SwarmOcc.Hpot (envH p m j U) ((trajectory p m U (n + 1)).pos i)
      - SwarmOcc.Hpot (envH p m j U) ((trajectory p m U n).pos i))
      = HpotInc p m n i j := rfl
  rw [hset, hinc] at h
  exact h

end Budget
end Swarming.Enl
