/-
# Tower exhaustion: from a per-level *conditional* force to `μ {D = ⊤} = 0`

## What this file does

The campaign's raw-nullity files
(`SyncAttemptForce`, `StrictEpochTower`, `DefectBandEpoch`, `DefectSlack`,
`RawNullityMass`, `RawAttemptBridge`, `HpathFromDtopNull`) reduce the last
input of the paper's Theorem 1.1 to

  `(arrayMeasure N) {U | RegenPath.D (posPath p m U) = ⊤} = 0`,

and `HpathFromDtopNull.hpath_of_D_top_null` turns that nullity into the
literal neutral `hpath`.  What those files have is an **additive** inequality
(`DefectSlack`):

  `μ {D = ⊤} + c * ∑_K β^K * μ {d_r = K} ≤ 1`,

whose own docstring records the exact obstruction: *"the inequality is additive
in mass, not multiplicative, so it cannot be iterated over levels"*.  Its
constant is `c = (1-p)^{2N} P(V) < 1` and the weighted defect mass is at most
`1`, so the additive route can never reach `μ {D = ⊤} = 0`; it caps at `1 - c`.

This file supplies the missing **multiplicative** step.  The genuine stochastic
input is isolated as a single, purely qualitative, level-uniform statement: the
*conditional* (pathwise-past) form of the existing one-attempt synchronisation
force,

  `(F)  ∃ q > 0, ∀ r,  q * μ (no success among the first r attempts)
                        ≤ μ (the r-th attempt is the first success)`.

`(F)` is strictly weaker than nullity of `{D = ⊤}` and has no rate, no profile
and no defect profile in it.  From `(F)` this file proves

  `μ.real (no success among the first R attempts) ≤ (1 - q)^R`,
  `μ (InfiniteFailure) = 0`, and hence `μ {D = ⊤} = 0`.

Together with the public `HpathFromDtopNull.hpath_of_D_top_null` (module
`TowerExhaustHpath.lean`) this removes `hpath` from the neutral final capstone.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `opaque`, no `unsafe`.
-/
import Swarm.RawStrictAttemptTower
import Swarm.StrictEpochTower
import Swarm.RegenPath

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open MeasureTheory Set ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace SwarmTowerExhaust

open Swarming.Uniform Swarming.Trajectory SwarmRestart
open RecordoSupply SwarmRecordMeas SwarmRecordMeas.Actual
open SwarmFresh SwarmSeed
open RawStrictAttemptTower

variable {N : ℕ} [Nonempty (Fin N)] {p : ℝ} {m : ℕ}

/-! ### 1. The decreasing all-fail events -/

/-- `NoSucc r`: no strict record attempt with index `< r` has succeeded.  This is the
path event "the tower has failed at every one of the first `r` stages". -/
def NoSucc (p : ℝ) (m : ℕ) (r : ℕ) : Set (Array N) :=
  {U | ∀ k, k < r → U ∉ FirstSuccessCell p m k}

theorem NoSucc_zero : NoSucc (N := N) p m 0 = univ := by
  ext U
  simp [NoSucc]

theorem NoSucc_eq_compl (r : ℕ) :
    NoSucc (N := N) p m r
      = (⋃ k ∈ Finset.range r, FirstSuccessCell (N := N) p m k)ᶜ := by
  ext U
  simp [NoSucc, Finset.mem_range]

theorem NoSucc_eq_iInter (r : ℕ) :
    NoSucc (N := N) p m r = ⋂ k ∈ Finset.range r, (FirstSuccessCell p m k)ᶜ := by
  ext U
  simp [NoSucc, Finset.mem_range]

theorem measurableSet_NoSucc (r : ℕ) : MeasurableSet (NoSucc (N := N) p m r) := by
  rw [NoSucc_eq_iInter]
  exact Finset.measurableSet_biInter _
    fun k _ => (measurableSet_firstSuccessCell (N := N) p m k).compl

theorem NoSucc_succ (r : ℕ) :
    NoSucc (N := N) p m (r + 1)
      = NoSucc (N := N) p m r ∩ (FirstSuccessCell p m r)ᶜ := by
  ext U
  simp only [NoSucc, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff]
  constructor
  · intro h
    exact ⟨fun k hk => h k (by omega), h r (by omega)⟩
  · rintro ⟨h1, h2⟩ k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
    · exact h1 k h
    · subst h; exact h2

theorem NoSucc_antitone : Antitone (NoSucc (N := N) p m) := by
  intro a b hab U hU
  exact fun k hk => hU k (lt_of_lt_of_le hk hab)

/-- The `r`-th first-success cell already lies in the event that stages `< r` failed. -/
theorem firstSuccessCell_subset_NoSucc (r : ℕ) :
    FirstSuccessCell (N := N) p m r ⊆ NoSucc (N := N) p m r := by
  intro U hU k hk
  have hd : Disjoint (FirstSuccessCell (N := N) p m r) (FirstSuccessCell (N := N) p m k) :=
    pairwise_disjoint_firstSuccessCell (N := N) p m (by omega)
  exact (Set.disjoint_left.mp hd) hU

theorem NoSucc_eq_union (r : ℕ) :
    NoSucc (N := N) p m r
      = NoSucc (N := N) p m (r + 1) ∪ FirstSuccessCell (N := N) p m r := by
  rw [NoSucc_succ]
  ext U
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
  constructor
  · intro h
    by_cases hrs : U ∈ FirstSuccessCell (N := N) p m r
    · exact Or.inr hrs
    · exact Or.inl ⟨h, hrs⟩
  · rintro (⟨h1, -⟩ | h)
    · exact h1
    · exact firstSuccessCell_subset_NoSucc r h

theorem disjoint_NoSucc_firstSuccessCell (r : ℕ) :
    Disjoint (NoSucc (N := N) p m (r + 1)) (FirstSuccessCell (N := N) p m r) := by
  rw [NoSucc_succ, Set.disjoint_left]
  rintro U ⟨-, hc⟩ hr
  exact hc hr

/-- **Exact mass bookkeeping.**  The mass lost when the tower is run one more stage is
*exactly* the mass of the `r`-th first-success cell. -/
theorem real_NoSucc_eq (r : ℕ) :
    (arrayMeasure N).real (NoSucc (N := N) p m r)
      = (arrayMeasure N).real (NoSucc (N := N) p m (r + 1))
        + (arrayMeasure N).real (FirstSuccessCell (N := N) p m r) := by
  have hmeas : MeasurableSet (FirstSuccessCell (N := N) p m r) :=
    measurableSet_firstSuccessCell (N := N) p m r
  rw [NoSucc_eq_union, measureReal_union (disjoint_NoSucc_firstSuccessCell r) hmeas]

/-! ### 2. The intersection is the all-fail event -/

theorem iInter_NoSucc :
    (⋂ r, NoSucc (N := N) p m r) = InfiniteFailure (N := N) p m := by
  have hU : (⋃ r, ⋃ k ∈ Finset.range r, FirstSuccessCell (N := N) p m k)
      = (⋃ k, FirstSuccessCell (N := N) p m k) := by
    ext U
    simp only [Set.mem_iUnion, Finset.mem_range]
    constructor
    · rintro ⟨_, k, _, h⟩
      exact ⟨k, h⟩
    · rintro ⟨k, h⟩
      exact ⟨k + 1, k, by omega, h⟩
  have hstep : (⋂ r, NoSucc (N := N) p m r)
      = (⋃ r, ⋃ k ∈ Finset.range r, FirstSuccessCell (N := N) p m k)ᶜ := by
    simp only [NoSucc_eq_compl]
    rw [← Set.compl_iUnion]
  rw [hstep, hU, iUnion_firstSuccessCell]
  rfl

theorem infiniteFailure_subset_NoSucc (r : ℕ) :
    InfiniteFailure (N := N) p m ⊆ NoSucc (N := N) p m r := by
  rw [← iInter_NoSucc]
  exact Set.iInter_subset _ r

/-! ### 3. The multiplicative decay -/

/-- **Geometric failure decay.**  If at every stage the *conditional* probability of a
first success given that the tower has failed so far is at least `q`, then the failure
probability after `R` stages is at most `(1 - q)^R`.

This is the step the campaign's additive `DefectSlack` inequality cannot make. -/
theorem real_NoSucc_le_geom {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hforce : ∀ r : ℕ,
      q * (arrayMeasure N).real (NoSucc (N := N) p m r)
        ≤ (arrayMeasure N).real (FirstSuccessCell (N := N) p m r))
    (R : ℕ) :
    (arrayMeasure N).real (NoSucc (N := N) p m R) ≤ (1 - q) ^ R := by
  induction R with
  | zero => simp [NoSucc_zero]
  | succ R ih =>
    have hsplit := real_NoSucc_eq (N := N) (p := p) (m := m) R
    have hf := hforce R
    have hnn : 0 ≤ (arrayMeasure N).real (NoSucc (N := N) p m R) := measureReal_nonneg
    have hstep : (arrayMeasure N).real (NoSucc (N := N) p m (R + 1))
        ≤ (1 - q) * (arrayMeasure N).real (NoSucc (N := N) p m R) := by
      nlinarith [hsplit, hf, hnn]
    calc (arrayMeasure N).real (NoSucc (N := N) p m (R + 1))
        ≤ (1 - q) * (arrayMeasure N).real (NoSucc (N := N) p m R) := hstep
      _ ≤ (1 - q) * (1 - q) ^ R := by
          exact mul_le_mul_of_nonneg_left ih (by linarith)
      _ = (1 - q) ^ (R + 1) := by ring

/-- The failure probability tends to zero geometrically. -/
theorem tendsto_real_NoSucc_zero {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hforce : ∀ r : ℕ,
      q * (arrayMeasure N).real (NoSucc (N := N) p m r)
        ≤ (arrayMeasure N).real (FirstSuccessCell (N := N) p m r)) :
    Tendsto (fun R => (arrayMeasure N).real (NoSucc (N := N) p m R)) atTop (𝓝 0) := by
  refine squeeze_zero (fun R => measureReal_nonneg)
    (fun R => real_NoSucc_le_geom hq0.le hq1 hforce R)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : (0:ℝ) ≤ 1 - q) (by linarith))

/-- **The conditional force kills the all-fail event.** -/
theorem infiniteFailure_real_eq_zero {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hforce : ∀ r : ℕ,
      q * (arrayMeasure N).real (NoSucc (N := N) p m r)
        ≤ (arrayMeasure N).real (FirstSuccessCell (N := N) p m r)) :
    (arrayMeasure N).real (InfiniteFailure (N := N) p m) = 0 := by
  have hlim := tendsto_real_NoSucc_zero (N := N) (p := p) (m := m) hq0 hq1 hforce
  have hbdd : (arrayMeasure N).real (InfiniteFailure (N := N) p m) ≤ 0 := by
    refine le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall ?_)
    intro R
    exact measureReal_mono (infiniteFailure_subset_NoSucc R)
  have hnn : 0 ≤ (arrayMeasure N).real (InfiniteFailure (N := N) p m) := measureReal_nonneg
  linarith

theorem infiniteFailure_eq_zero {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hforce : ∀ r : ℕ,
      q * (arrayMeasure N).real (NoSucc (N := N) p m r)
        ≤ (arrayMeasure N).real (FirstSuccessCell (N := N) p m r)) :
    (arrayMeasure N) (InfiniteFailure (N := N) p m) = 0 := by
  have h := infiniteFailure_real_eq_zero (N := N) (p := p) (m := m) hq0 hq1 hforce
  rw [← measureReal_eq_zero_iff (by finiteness :
    (arrayMeasure N) (InfiniteFailure (N := N) p m) ≠ ∞)]
  exact h

/-- Almost-sure success of the strict-attempt tower, in the exact form the chain
consumes. -/
theorem ae_exists_strictAttempt {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hforce : ∀ r : ℕ,
      q * (arrayMeasure N).real (NoSucc (N := N) p m r)
        ≤ (arrayMeasure N).real (FirstSuccessCell (N := N) p m r)) :
    ∀ᵐ U ∂(arrayMeasure N), ∃ r, StrictAttempt p m U r :=
  ae_exists_strictAttempt_of_infiniteFailure_null
    (infiniteFailure_eq_zero (N := N) (p := p) (m := m) hq0 hq1 hforce)

/-! ### 4. Transfer to the raw first-regeneration level `D` -/

/-- A successful canonical strict attempt is a genuine regeneration at its own level,
so `D = ⊤` forces every attempt to fail. -/
theorem D_top_subset_infiniteFailure {U : Array N}
    (h : RegenPath.D (posPath p m U) = ⊤) :
    U ∈ InfiniteFailure (N := N) p m := by
  classical
  rw [InfiniteFailure, Set.mem_ofPred_eq, not_exists]
  intro k hk
  have hpartial : RegenAtStrict p m U (recTimeA p m U (k + 1)) (((k + 1 : ℕ)) : ℤ) := by
    simpa [StrictAttempt, attemptTime, attemptLevel] using hk
  obtain ⟨hrec, hstrict⟩ := hpartial
  obtain ⟨hbelow, hat⟩ := hrec
  have htau : RegenPath.tau (posPath p m U) (((k + 1 : ℕ)) : ℤ) =
      (recTimeA p m U (k + 1) : ℕ∞) := by
    rw [RegenPath.tau_eq_iff]
    refine ⟨⟨Classical.arbitrary (Fin N), ?_⟩, fun n hn i => ?_⟩
    · show (trajectory p m U (recTimeA p m U (k + 1))).pos _ = _
      exact hat _
    · show (trajectory p m U n).pos i ≠ (((k + 1 : ℕ)) : ℤ)
      have := hbelow n hn i
      omega
  have hReg : RegenPath.Reg (posPath p m U) (((k + 1 : ℕ)) : ℤ) := by
    refine ⟨recTimeA p m U (k + 1), htau, fun i => ?_, fun n hn i => ?_⟩
    · show (trajectory p m U (recTimeA p m U (k + 1))).pos i = _
      exact hat i
    · have h2 := hstrict (n - recTimeA p m U (k + 1)) (by omega) i
      have heq : recTimeA p m U (k + 1) + (n - recTimeA p m U (k + 1)) = n := by omega
      rw [heq] at h2
      exact h2
  have hex : ∃ r : ℕ, 1 ≤ r ∧ RegenPath.Reg (posPath p m U) (((r : ℕ)) : ℤ) :=
    ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k), hReg⟩
  have hD : RegenPath.D (posPath p m U) = (Nat.find hex : ℕ∞) := by
    rw [RegenPath.D, dif_pos hex]
  rw [hD] at h
  exact WithTop.coe_ne_top h

/-- **Raw nullity of the first positive regeneration level.** -/
theorem D_top_eq_zero {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hforce : ∀ r : ℕ,
      q * (arrayMeasure N).real (NoSucc (N := N) p m r)
        ≤ (arrayMeasure N).real (FirstSuccessCell (N := N) p m r)) :
    (arrayMeasure N) {U : Array N | RegenPath.D (posPath p m U) = ⊤} = 0 := by
  refine measure_mono_null (fun U hU => D_top_subset_infiniteFailure hU) ?_
  exact infiniteFailure_eq_zero (N := N) (p := p) (m := m) hq0 hq1 hforce

/-! ### 4b. Level-varying force constants

The tower's own unconditional one-attempt constants decay with the level, so the
constant-`q` form above is too rigid to be usable.  The same argument with
`∑_r q_r = ∞` still gives nullity; only the divergence of the conditional force
matters, never its size. -/

theorem real_NoSucc_le_prod {q : ℕ → ℝ} (hq0 : ∀ r, 0 ≤ q r) (hq1 : ∀ r, q r ≤ 1)
    (hforce : ∀ r : ℕ,
      q r * (arrayMeasure N).real (NoSucc (N := N) p m r)
        ≤ (arrayMeasure N).real (FirstSuccessCell (N := N) p m r))
    (R : ℕ) :
    (arrayMeasure N).real (NoSucc (N := N) p m R)
      ≤ ∏ r ∈ Finset.range R, (1 - q r) := by
  induction R with
  | zero => simp [NoSucc_zero]
  | succ R ih =>
    rw [Finset.prod_range_succ]
    have hsplit := real_NoSucc_eq (N := N) (p := p) (m := m) R
    have hf := hforce R
    have hnn : 0 ≤ (arrayMeasure N).real (NoSucc (N := N) p m R) := measureReal_nonneg
    have hnonneg : 0 ≤ ∏ r ∈ Finset.range R, (1 - q r) :=
      Finset.prod_nonneg fun r _ => by linarith [hq1 r]
    have hstep : (arrayMeasure N).real (NoSucc (N := N) p m (R + 1))
        ≤ (1 - q R) * (arrayMeasure N).real (NoSucc (N := N) p m R) := by
      nlinarith [hsplit, hf, hnn]
    calc (arrayMeasure N).real (NoSucc (N := N) p m (R + 1))
        ≤ (1 - q R) * (arrayMeasure N).real (NoSucc (N := N) p m R) := hstep
      _ ≤ (1 - q R) * ∏ r ∈ Finset.range R, (1 - q r) :=
          mul_le_mul_of_nonneg_left ih (by linarith [hq1 R])
      _ = (∏ r ∈ Finset.range R, (1 - q r)) * (1 - q R) := by rw [mul_comm]

theorem prod_one_sub_tendsto_zero {q : ℕ → ℝ} (hq0 : ∀ r, 0 ≤ q r) (hq1 : ∀ r, q r ≤ 1)
    (hdiv : Tendsto (fun R : ℕ => ∑ r ∈ Finset.range R, q r) atTop atTop) :
    Tendsto (fun R : ℕ => ∏ r ∈ Finset.range R, (1 - q r)) atTop (𝓝 0) := by
  have hexp : Tendsto (fun R : ℕ => Real.exp (-(∑ r ∈ Finset.range R, q r))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℕ => Real.exp (∑ r ∈ Finset.range R, q r)) atTop atTop :=
      Real.tendsto_exp_atTop.comp hdiv
    have h2 : Tendsto (fun R : ℕ => (Real.exp (∑ r ∈ Finset.range R, q r))⁻¹) atTop (𝓝 0) :=
      h1.inv_tendsto_atTop
    have h3 : (fun R : ℕ => Real.exp (-(∑ r ∈ Finset.range R, q r)))
        = fun R : ℕ => (Real.exp (∑ r ∈ Finset.range R, q r))⁻¹ := by
      funext R
      exact Real.exp_neg _
    rw [h3]
    exact h2
  refine squeeze_zero (fun R => Finset.prod_nonneg fun r _ => by linarith [hq1 r])
    (fun R => ?_) hexp
  have hneg : -(∑ r ∈ Finset.range R, q r) = ∑ r ∈ Finset.range R, (-(q r)) := by
    rw [Finset.sum_neg_distrib]
  have hrhs : Real.exp (-(∑ r ∈ Finset.range R, q r))
      = ∏ r ∈ Finset.range R, Real.exp (-(q r)) := by
    rw [hneg, Real.exp_sum]
  rw [hrhs]
  exact Finset.prod_le_prod (fun r _ => by linarith [hq1 r])
    (fun r _ => Real.one_sub_le_exp_neg (q r))

/-- **Divergent conditional force kills the all-fail event.**  Only
`∑_r q_r = ∞` is required; the individual constants may decay. -/
theorem infiniteFailure_eq_zero_of_tendsto_sum {q : ℕ → ℝ}
    (hq0 : ∀ r, 0 ≤ q r) (hq1 : ∀ r, q r ≤ 1)
    (hdiv : Tendsto (fun R : ℕ => ∑ r ∈ Finset.range R, q r) atTop atTop)
    (hforce : ∀ r : ℕ,
      q r * (arrayMeasure N).real (NoSucc (N := N) p m r)
        ≤ (arrayMeasure N).real (FirstSuccessCell (N := N) p m r)) :
    (arrayMeasure N) (InfiniteFailure (N := N) p m) = 0 := by
  have hprod := prod_one_sub_tendsto_zero hq0 hq1 hdiv
  have hreal : (arrayMeasure N).real (InfiniteFailure (N := N) p m) = 0 := by
    have hbdd : (arrayMeasure N).real (InfiniteFailure (N := N) p m) ≤ 0 := by
      refine le_of_tendsto_of_tendsto tendsto_const_nhds hprod (Eventually.of_forall ?_)
      intro R
      exact le_trans (measureReal_mono (infiniteFailure_subset_NoSucc R))
        (real_NoSucc_le_prod hq0 hq1 hforce R)
    have hnn : 0 ≤ (arrayMeasure N).real (InfiniteFailure (N := N) p m) := measureReal_nonneg
    linarith
  rw [← measureReal_eq_zero_iff (by finiteness :
    (arrayMeasure N) (InfiniteFailure (N := N) p m) ≠ ∞)]
  exact hreal

/-- **Raw nullity of `{D = ⊤}` from a divergent per-level conditional force.** -/
theorem D_top_eq_zero_of_tendsto_sum {q : ℕ → ℝ}
    (hq0 : ∀ r, 0 ≤ q r) (hq1 : ∀ r, q r ≤ 1)
    (hdiv : Tendsto (fun R : ℕ => ∑ r ∈ Finset.range R, q r) atTop atTop)
    (hforce : ∀ r : ℕ,
      q r * (arrayMeasure N).real (NoSucc (N := N) p m r)
        ≤ (arrayMeasure N).real (FirstSuccessCell (N := N) p m r)) :
    (arrayMeasure N) {U : Array N | RegenPath.D (posPath p m U) = ⊤} = 0 :=
  measure_mono_null (fun U hU => D_top_subset_infiniteFailure hU)
    (infiniteFailure_eq_zero_of_tendsto_sum hq0 hq1 hdiv hforce)

/-! ### 5. Exhaustiveness of the disjoint first-success cells

This is the "raw exhaustiveness of the completed future law" the campaign records as
the residual; here it is an identity, and the tower condition is exactly what makes the
total mass one.  The two consequences in this section are **unconditional**. -/

theorem measure_iUnion_firstSuccessCell :
    (arrayMeasure N) (⋃ k, FirstSuccessCell (N := N) p m k)
      = ∑' k, (arrayMeasure N) (FirstSuccessCell (N := N) p m k) :=
  measure_iUnion (fun a b hab =>
    pairwise_disjoint_firstSuccessCell (N := N) p m hab)
    (fun k => measurableSet_firstSuccessCell (N := N) p m k)

/-- **Unconditional exhaustiveness identity.**  The all-fail mass plus the *total* mass
of the disjoint first-success cells is exactly one. -/
theorem infiniteFailure_add_tsum_firstSuccessCell :
    (arrayMeasure N) (InfiniteFailure (N := N) p m)
      + (∑' k, (arrayMeasure N) (FirstSuccessCell (N := N) p m k)) = 1 := by
  have : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hcompl : (⋃ k, FirstSuccessCell (N := N) p m k)ᶜ = InfiniteFailure (N := N) p m := by
    rw [iUnion_firstSuccessCell]
    rfl
  have hmeas : MeasurableSet (⋃ k, FirstSuccessCell (N := N) p m k) :=
    MeasurableSet.iUnion fun k => measurableSet_firstSuccessCell (N := N) p m k
  have h := measure_add_measure_compl hmeas (μ := arrayMeasure N)
  rw [hcompl, measure_iUnion_firstSuccessCell, measure_univ, add_comm] at h
  exact h

/-- **Unconditional sharpened exclusion of raw failure.**  The whole sum of the exact
disjoint first-success masses, not merely its first term, is excluded from `{D = ⊤}`:

  `μ {D = ⊤} + ∑_k μ (first success at stage k) ≤ 1`.

The campaign's `RawNullityMass` bound `μ {D = ⊤} + 2^{-N} P(V) ≤ 1` and the
defect-weighted `DefectSlack` bound are the `k = 0` and single-defect-class truncations
of this identity; neither can reach nullity because both are additive. -/
theorem D_top_add_tsum_firstSuccessCell_le_one :
    (arrayMeasure N) {U : Array N | RegenPath.D (posPath p m U) = ⊤}
      + (∑' k, (arrayMeasure N) (FirstSuccessCell (N := N) p m k)) ≤ 1 := by
  have hmono : (arrayMeasure N) {U : Array N | RegenPath.D (posPath p m U) = ⊤}
      ≤ (arrayMeasure N) (InfiniteFailure (N := N) p m) :=
    measure_mono (fun U hU => D_top_subset_infiniteFailure hU)
  calc (arrayMeasure N) {U : Array N | RegenPath.D (posPath p m U) = ⊤}
        + (∑' k, (arrayMeasure N) (FirstSuccessCell (N := N) p m k))
      ≤ (arrayMeasure N) (InfiniteFailure (N := N) p m)
        + (∑' k, (arrayMeasure N) (FirstSuccessCell (N := N) p m k)) :=
        add_le_add hmono le_rfl
    _ = 1 := infiniteFailure_add_tsum_firstSuccessCell

theorem tsum_firstSuccessCell_le_one :
    (∑' k, (arrayMeasure N) (FirstSuccessCell (N := N) p m k)) ≤ 1 := by
  have h := D_top_add_tsum_firstSuccessCell_le_one (N := N) (p := p) (m := m)
  exact le_trans (le_add_left le_rfl) h

/-- **Failure probability after `R` stages is the unspent first-success mass.**  For the
real-valued probabilities this is the exact identity
`μ (no success among the first R) = 1 - ∑_{k<R} μ (first success at stage k)`,
so the tower condition is literally "the first-success masses exhaust the space". -/
theorem real_NoSucc_eq_one_sub_sum (R : ℕ) :
    (arrayMeasure N).real (NoSucc (N := N) p m R)
      = 1 - ∑ k ∈ Finset.range R,
          (arrayMeasure N).real (FirstSuccessCell (N := N) p m k) := by
  have : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  induction R with
  | zero => simp [NoSucc_zero]
  | succ R ih =>
    rw [Finset.sum_range_succ]
    have hsplit := real_NoSucc_eq (N := N) (p := p) (m := m) R
    have hstep : (arrayMeasure N).real (NoSucc (N := N) p m (R + 1))
        = (arrayMeasure N).real (NoSucc (N := N) p m R)
          - (arrayMeasure N).real (FirstSuccessCell (N := N) p m R) := by
      linarith
    rw [hstep, ih]
    ring

theorem measure_firstSuccessCell_tsum_eq_one {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hforce : ∀ r : ℕ,
      q * (arrayMeasure N).real (NoSucc (N := N) p m r)
        ≤ (arrayMeasure N).real (FirstSuccessCell (N := N) p m r)) :
    ∑' k, (arrayMeasure N) (FirstSuccessCell (N := N) p m k) = 1 := by
  have : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hnull := infiniteFailure_eq_zero (N := N) (p := p) (m := m) hq0 hq1 hforce
  have h := infiniteFailure_add_tsum_firstSuccessCell (N := N) (p := p) (m := m)
  rw [hnull, zero_add] at h
  exact h

end SwarmTowerExhaust
