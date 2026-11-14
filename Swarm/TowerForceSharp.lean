/-
# The past-relative tower force is *exactly* nullity of the all-fail event

## What this file establishes

The public capstone `main_claim_actual_of_invariant_and_conditional_force` consumes a single
hypothesis beyond the invariant stopped-record law `hπ`: the per-level *conditional force*

  `(F)  ∃ q : ℕ → ℝ, (∀ r, 0 ≤ q r) ∧ (∀ r, q r ≤ 1) ∧ ∑_r q r = ∞ ∧
        ∀ r, q r * μ (no success among the first r attempts) ≤ μ (first success at stage r)`.

`TowerExhaust` shows `(F) ⟹ μ (InfiniteFailure) = 0`.  This file proves the **converse**, so

  `(F) ⟺ μ (InfiniteFailure) = 0`,

and `TowerForceBridge.lean` adds `μ (InfiniteFailure) = μ {D = ⊤}`, which is *literally* the
hypothesis of `HpathFromDtopNull.hpath_of_D_top_null`.

So the force is not a weaker input, nor a "synchronisation/freshness" input that can be
discharged by a defect or freshness estimate on the prefix all-fail events: it is
*equivalent* to almost-sure success of the strict-record tower.  Any proof of `(F)` is a proof
of `μ {D = ⊤} = 0` and conversely; the two statements carry the same mathematical content.
The corollary `no_divergent_force_of_pos_infiniteFailure` makes the falsification criterion
explicit: a model with positive all-fail mass refutes `(F)` outright.

The constructive half is sharp structure, not a restatement: the *optimal* choice is the
per-level "conditional freshness" `q r = 1 - a (r+1) / a r`, where `a r` is the mass of the
all-fail event; the real content of `(F)` is that these conditional probabilities have
divergent sum.  The construction used in `exists_divergent_force_of_pos` avoids any
product/logarithm estimate: it takes `q` constant `1/2` on the levels `g j` at which the
all-fail mass halves, and each block between consecutive halving levels contributes sum
`≥ 1/2` by the elementary product inequality `1 - ∑ δ_i ≤ ∏ (1 - δ_i)`.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `opaque`, no `unsafe`.
-/
import Swarm.TowerExhaust

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open MeasureTheory Set ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace TowerForceSharp

open Swarming.Uniform SwarmTowerExhaust RawStrictAttemptTower

/-! ### 1. An elementary product inequality

For `δ_i ∈ [0,1]`, `1 - ∑ δ_i ≤ ∏ (1 - δ_i)`.  This replaces the exponential/logarithm
estimate that a "summable force" argument would otherwise need. -/

theorem one_sub_sum_le_prod_one_sub (s : Finset ℕ) (d : ℕ → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ d i) (h1 : ∀ i ∈ s, d i ≤ 1) :
    1 - ∑ i ∈ s, d i ≤ ∏ i ∈ s, (1 - d i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have h0' : ∀ i ∈ s, 0 ≤ d i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
      have h1' : ∀ i ∈ s, d i ≤ 1 := fun i hi => h1 i (Finset.mem_insert_of_mem hi)
      have ih' := ih h0' h1'
      have hda0 : 0 ≤ d a := h0 a (Finset.mem_insert_self a s)
      have hda1 : d a ≤ 1 := h1 a (Finset.mem_insert_self a s)
      have hS0 : 0 ≤ ∑ i ∈ s, d i := Finset.sum_nonneg h0'
      nlinarith [mul_nonneg hS0 hda0]

/-! ### 2. Divergent forces from vanishing mass (abstract form)

The tower's own mass bookkeeping makes the force `q r * a r ≤ a r - a (r+1)` an upper bound on
`q` in terms of the *conditional* freshness profile `1 - a (r+1)/a r`.  The lemmas below show
that a divergent force exists exactly when the mass vanishes, with an explicit construction. -/

/-- **Divergent force for a strictly positive vanishing mass sequence.** -/
theorem exists_divergent_force_of_pos {a : ℕ → ℝ}
    (ha : ∀ r, 0 < a r) (hanti : Antitone a) (htend : Tendsto a atTop (𝓝 0)) :
    ∃ q : ℕ → ℝ, (∀ r, 0 ≤ q r) ∧ (∀ r, q r ≤ 1) ∧
      Tendsto (fun R : ℕ => ∑ r ∈ Finset.range R, q r) atTop atTop ∧
      ∀ r, q r * a r ≤ a r - a (r + 1) := by
  classical
  -- halving levels
  have hex : ∀ r : ℕ, ∃ s : ℕ, r < s ∧ a s ≤ a r / 2 := by
    intro r
    have hev : ∀ᶠ s in atTop, a s < a r / 2 :=
      htend.eventually (Iio_mem_nhds (by have := ha r; linarith))
    obtain ⟨s, hs, hsr⟩ := (hev.and (Ioi_mem_atTop r)).exists
    exact ⟨s, hsr, le_of_lt hs⟩
  let gstep : ℕ → ℕ := fun r => Nat.find (hex r)
  have hgstep : ∀ r, r < gstep r ∧ a (gstep r) ≤ a r / 2 := fun r => Nat.find_spec (hex r)
  let g : ℕ → ℕ := fun n => Nat.rec 0 (fun _ gk => gstep gk) n
  have g_zero : g 0 = 0 := rfl
  have g_succ : ∀ n, g (n + 1) = gstep (g n) := fun n => rfl
  have g_lt : ∀ n, g n < g (n + 1) := fun n => (hgstep (g n)).1
  have g_halve : ∀ n, a (g (n + 1)) ≤ a (g n) / 2 := fun n => (hgstep (g n)).2
  have hratio0 : ∀ r, 0 ≤ a (r + 1) / a r := fun r =>
    div_nonneg (le_of_lt (ha (r + 1))) (le_of_lt (ha r))
  have hratio1 : ∀ r, a (r + 1) / a r ≤ 1 := fun r =>
    (div_le_one (ha r)).mpr (hanti (Nat.le_succ r))
  refine ⟨fun r => 1 - a (r + 1) / a r, fun r => by linarith [hratio1 r],
    fun r => by linarith [hratio0 r], ?_, fun r => ?_⟩
  · -- telescoping of the conditional freshness over a block
    have htel : ∀ k n : ℕ,
        (∏ r ∈ Finset.Ico k (k + n), (a (r + 1) / a r)) * a k = a (k + n) := by
      intro k n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [show k + (n + 1) = (k + n) + 1 by ring,
            Finset.prod_Ico_succ_top (by omega)]
          calc ((∏ r ∈ Finset.Ico k (k + n), a (r + 1) / a r) * (a (k + n + 1) / a (k + n)))
                * a k
              = ((∏ r ∈ Finset.Ico k (k + n), a (r + 1) / a r) * a k)
                  * (a (k + n + 1) / a (k + n)) := by ring
            _ = a (k + n) * (a (k + n + 1) / a (k + n)) := by rw [ih]
            _ = a (k + n) * a (k + n + 1) / a (k + n) := by rw [mul_div_assoc]
            _ = a (k + n + 1) :=
                mul_div_cancel_left₀ (a (k + n + 1)) (ne_of_gt (ha (k + n)))
    have hblock : ∀ j : ℕ,
        (1 / 2 : ℝ) ≤ ∑ r ∈ Finset.Ico (g j) (g (j + 1)), (1 - a (r + 1) / a r) := by
      intro j
      have htel' := htel (g j) (g (j + 1) - g j)
      have hgap : g j + (g (j + 1) - g j) = g (j + 1) := Nat.add_sub_cancel' (le_of_lt (g_lt j))
      rw [hgap] at htel'
      have hprod : ∏ r ∈ Finset.Ico (g j) (g (j + 1)), (a (r + 1) / a r)
          = a (g (j + 1)) / a (g j) := by
        rw [eq_div_iff (ne_of_gt (ha (g j)))]
        exact htel'
      have hbern : 1 - ∑ r ∈ Finset.Ico (g j) (g (j + 1)), (1 - a (r + 1) / a r)
          ≤ ∏ r ∈ Finset.Ico (g j) (g (j + 1)), (1 - (1 - a (r + 1) / a r)) :=
        one_sub_sum_le_prod_one_sub _ _
          (fun i _ => by linarith [hratio1 i]) (fun i _ => by linarith [hratio0 i])
      have hcongr : (∏ r ∈ Finset.Ico (g j) (g (j + 1)),
            (1 - (1 - a (r + 1) / a r))) = a (g (j + 1)) / a (g j) := by
        calc (∏ r ∈ Finset.Ico (g j) (g (j + 1)), (1 - (1 - a (r + 1) / a r)))
            = ∏ r ∈ Finset.Ico (g j) (g (j + 1)), (a (r + 1) / a r) :=
              Finset.prod_congr rfl fun r _ => by ring
          _ = a (g (j + 1)) / a (g j) := hprod
      rw [hcongr] at hbern
      have hle : a (g (j + 1)) / a (g j) ≤ 1 / 2 := by
        rw [div_le_iff₀ (ha (g j))]
        linarith [g_halve j]
      linarith
    -- the partial sums are the block sums
    have hpart : ∀ n : ℕ,
        ∑ r ∈ Finset.range (g n), (1 - a (r + 1) / a r)
          = ∑ j ∈ Finset.range n,
              ∑ r ∈ Finset.Ico (g j) (g (j + 1)), (1 - a (r + 1) / a r) := by
      intro n
      induction n with
      | zero => simp [g_zero]
      | succ n ih =>
          have hsplit : Finset.range (g (n + 1))
              = Finset.range (g n) ∪ Finset.Ico (g n) (g (n + 1)) := by
            rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
            exact (Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) (le_of_lt (g_lt n))).symm
          have hdisj : Disjoint (Finset.range (g n)) (Finset.Ico (g n) (g (n + 1))) := by
            rw [Finset.range_eq_Ico]
            exact Finset.Ico_disjoint_Ico_consecutive _ _ _
          rw [hsplit, Finset.sum_union hdisj, ih, Finset.sum_range_succ]
    have hlow : ∀ n : ℕ,
        (n : ℝ) / 2 ≤ ∑ r ∈ Finset.range (g n), (1 - a (r + 1) / a r) := by
      intro n
      rw [hpart n]
      have hconst : ∑ _j ∈ Finset.range n, (1 / 2 : ℝ) = (n : ℝ) / 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
      rw [← hconst]
      exact Finset.sum_le_sum fun j _ => hblock j
    have hmono : Monotone (fun R : ℕ => ∑ r ∈ Finset.range R, (1 - a (r + 1) / a r)) :=
      monotone_nat_of_le_succ fun R => by
        rw [Finset.sum_range_succ]
        linarith [hratio1 R]
    refine tendsto_atTop_atTop_of_monotone hmono fun b => ?_
    obtain ⟨n, hn⟩ := exists_nat_ge (2 * b)
    refine ⟨g n, ?_⟩
    have h1 := hlow n
    have h2 : b ≤ (n : ℝ) / 2 := by linarith
    linarith
  · -- the force holds with equality
    have hEq : (1 - a (r + 1) / a r) * a r = a r - a (r + 1) := by
      have hr : a r ≠ 0 := ne_of_gt (ha r)
      field_simp
    rw [hEq]

/-- **Divergent force for a vanishing nonnegative antitone mass sequence.** -/
theorem exists_divergent_force {a : ℕ → ℝ}
    (hnn : ∀ r, 0 ≤ a r) (hanti : Antitone a) (htend : Tendsto a atTop (𝓝 0)) :
    ∃ q : ℕ → ℝ, (∀ r, 0 ≤ q r) ∧ (∀ r, q r ≤ 1) ∧
      Tendsto (fun R : ℕ => ∑ r ∈ Finset.range R, q r) atTop atTop ∧
      ∀ r, q r * a r ≤ a r - a (r + 1) := by
  classical
  by_cases hpos : ∀ r, 0 < a r
  · exact exists_divergent_force_of_pos hpos hanti htend
  · push Not at hpos
    obtain ⟨r₀, hr₀⟩ := hpos
    have hr₀0 : a r₀ = 0 := le_antisymm hr₀ (hnn r₀)
    -- the first zero of the sequence
    have hex0 : ∃ r, a r = 0 := ⟨r₀, hr₀0⟩
    have hexR : ∃ R : ℕ, a R = 0 ∧ ∀ r, r < R → a r ≠ 0 :=
      ⟨Nat.find hex0, Nat.find_spec hex0, fun r hr => Nat.find_min hex0 hr⟩
    obtain ⟨R, hR0, hRmin⟩ := hexR
    have hRpos : ∀ r, r < R → 0 < a r := fun r hr =>
      lt_of_le_of_ne (hnn r) (Ne.symm (hRmin r hr))
    have hzero : ∀ r, R ≤ r → a r = 0 := fun r hr =>
      le_antisymm (le_trans (hanti hr) (le_of_eq hR0)) (hnn r)
    have hratio0 : ∀ r, r < R → 0 ≤ a (r + 1) / a r := fun r hr =>
      div_nonneg (hnn _) (le_of_lt (hRpos r hr))
    have hratio1 : ∀ r, r < R → a (r + 1) / a r ≤ 1 := fun r hr =>
      (div_le_one (hRpos r hr)).mpr (hanti (Nat.le_succ r))
    have hq0 : ∀ r, 0 ≤ (if r < R then 1 - a (r + 1) / a r else 1) := by
      intro r
      by_cases h : r < R
      · simp only [h, if_true]; exact sub_nonneg.mpr (hratio1 r h)
      · simp only [h, if_false]; norm_num
    have hq1 : ∀ r, (if r < R then 1 - a (r + 1) / a r else 1) ≤ 1 := by
      intro r
      by_cases h : r < R
      · simp only [h, if_true]; exact sub_le_self 1 (hratio0 r h)
      · simp only [h, if_false]; norm_num
    refine ⟨fun r => if r < R then 1 - a (r + 1) / a r else 1, hq0, hq1, ?_, ?_⟩
    · -- divergence: the tail is constantly one
      have hnn' := hq0
      have hmono : Monotone (fun N : ℕ => ∑ r ∈ Finset.range N,
          if r < R then 1 - a (r + 1) / a r else 1) :=
        monotone_nat_of_le_succ fun N => by
          rw [Finset.sum_range_succ]
          linarith [hnn' N]
      refine tendsto_atTop_atTop_of_monotone hmono fun b => ?_
      have htail : ∀ n : ℕ, (n : ℝ) ≤ ∑ r ∈ Finset.range (R + n),
          (if r < R then 1 - a (r + 1) / a r else 1) := by
        intro n
        induction n with
        | zero =>
            push_cast
            exact Finset.sum_nonneg fun r _ => hnn' r
        | succ k ih =>
            rw [show R + (k + 1) = (R + k) + 1 by ring, Finset.sum_range_succ]
            have hqk : (if R + k < R then 1 - a (R + k + 1) / a (R + k) else 1) = 1 :=
              if_neg (by omega)
            rw [hqk]
            push_cast
            linarith
      obtain ⟨n, hn⟩ := exists_nat_ge b
      exact ⟨R + n, le_trans hn (htail n)⟩
    · -- the force
      intro r
      by_cases h : r < R
      · have hEq : (1 - a (r + 1) / a r) * a r = a r - a (r + 1) := by
          have hr : a r ≠ 0 := ne_of_gt (hRpos r h)
          field_simp
        simp only [h, if_true]
        rw [hEq]
      · have hz : a r = 0 := hzero r (by omega)
        have hz1 : a (r + 1) = 0 := hzero (r + 1) (by omega)
        simp only [h, if_false, hz, hz1]
        norm_num

/-! ### 3. The force on the actual array -/

section Actual

variable {N : ℕ} [Nonempty (Fin N)] {p : ℝ} {m : ℕ}

/-- The all-fail masses of the actual strict-attempt tower on the raw array. -/
noncomputable def noSuccMass (p : ℝ) (m : ℕ) (N : ℕ) [Nonempty (Fin N)] (r : ℕ) : ℝ :=
  (arrayMeasure N).real (NoSucc (N := N) p m r)

theorem noSuccMass_nonneg (r : ℕ) : 0 ≤ noSuccMass p m N r := measureReal_nonneg

theorem noSuccMass_antitone : Antitone (noSuccMass (N := N) p m) := fun i j hij =>
  measureReal_mono (NoSucc_antitone (N := N) (p := p) (m := m) hij)

theorem noSuccMass_sub (r : ℕ) :
    noSuccMass (N := N) p m r - noSuccMass (N := N) p m (r + 1)
      = (arrayMeasure N).real (FirstSuccessCell (N := N) p m r) := by
  have h := real_NoSucc_eq (N := N) (p := p) (m := m) r
  simp only [noSuccMass]
  linarith

/-- **Existence of a divergent per-level force from vanishing all-fail mass.**  This is the
converse of `TowerExhaust.infiniteFailure_eq_zero_of_tendsto_sum`. -/
theorem exists_divergent_force_of_tendsto_zero
    (h : Tendsto (fun r => noSuccMass p m N r) atTop (𝓝 0)) :
    ∃ q : ℕ → ℝ, (∀ r, 0 ≤ q r) ∧ (∀ r, q r ≤ 1) ∧
      Tendsto (fun R : ℕ => ∑ r ∈ Finset.range R, q r) atTop atTop ∧
      ∀ r, q r * (arrayMeasure N).real (NoSucc (N := N) p m r)
        ≤ (arrayMeasure N).real (FirstSuccessCell (N := N) p m r) := by
  obtain ⟨q, h0, h1, hdiv, hforce⟩ :=
    exists_divergent_force (a := noSuccMass (N := N) p m)
      (fun r => noSuccMass_nonneg (N := N) (p := p) (m := m) r)
      (noSuccMass_antitone (N := N) (p := p) (m := m)) h
  refine ⟨q, h0, h1, hdiv, fun r => ?_⟩
  have hsplit := noSuccMass_sub (N := N) (p := p) (m := m) r
  simp only [noSuccMass] at hsplit
  have hf := hforce r
  simp only [noSuccMass] at hf
  linarith

/-- **A divergent force forces the all-fail masses to vanish** (the geometric bookkeeping of
`TowerExhaust`, restated for the named mass sequence). -/
theorem tendsto_noSuccMass_zero_of_force {q : ℕ → ℝ}
    (hq0 : ∀ r, 0 ≤ q r) (hq1 : ∀ r, q r ≤ 1)
    (hdiv : Tendsto (fun R : ℕ => ∑ r ∈ Finset.range R, q r) atTop atTop)
    (hforce : ∀ r, q r * (arrayMeasure N).real (NoSucc (N := N) p m r)
      ≤ (arrayMeasure N).real (FirstSuccessCell (N := N) p m r)) :
    Tendsto (fun r => noSuccMass p m N r) atTop (𝓝 0) := by
  have hle : ∀ r, noSuccMass p m N r ≤ ∏ r' ∈ Finset.range r, (1 - q r') := by
    intro r
    have h := real_NoSucc_le_prod hq0 hq1 hforce r
    simpa only [noSuccMass] using h
  exact squeeze_zero (fun r => noSuccMass_nonneg (N := N) (p := p) (m := m) r) hle
    (prod_one_sub_tendsto_zero hq0 hq1 hdiv)

/-- **The all-fail mass vanishes exactly when the all-fail event is null** (continuity of the
array measure from above on the decreasing family `NoSucc r`). -/
theorem tendsto_noSuccMass_zero_iff_infiniteFailure_eq_zero :
    Tendsto (fun r => noSuccMass p m N r) atTop (𝓝 0)
      ↔ (arrayMeasure N) (InfiniteFailure (N := N) p m) = 0 := by
  constructor
  · intro htend
    obtain ⟨q, h0, h1, hdiv, hforce⟩ := exists_divergent_force_of_tendsto_zero htend
    exact infiniteFailure_eq_zero_of_tendsto_sum h0 h1 hdiv hforce
  · intro hnull
    have htend := tendsto_measure_iInter_atTop
      (μ := arrayMeasure N) (s := fun r => NoSucc (N := N) p m r)
      (fun r => (measurableSet_NoSucc (N := N) (p := p) (m := m) r).nullMeasurableSet)
      (NoSucc_antitone (N := N) (p := p) (m := m)) ⟨0, by simp [NoSucc_zero]⟩
    rw [iInter_NoSucc, hnull] at htend
    have hcont : ContinuousAt ENNReal.toReal (0 : ℝ≥0∞) := ENNReal.continuousAt_toReal (by simp)
    have hcomp : Tendsto (fun r => ((arrayMeasure N) (NoSucc (N := N) p m r)).toReal)
        atTop (𝓝 ((0 : ℝ≥0∞).toReal)) := hcont.tendsto.comp htend
    have hz : ((0 : ℝ≥0∞)).toReal = (0 : ℝ) := ENNReal.toReal_zero
    rw [hz] at hcomp
    simpa only [noSuccMass, measureReal_def] using hcomp

/-- **The per-level conditional force is equivalent to nullity of the all-fail event.** -/
theorem diverging_force_iff_infiniteFailure_eq_zero :
    (∃ q : ℕ → ℝ, (∀ r, 0 ≤ q r) ∧ (∀ r, q r ≤ 1) ∧
      Tendsto (fun R : ℕ => ∑ r ∈ Finset.range R, q r) atTop atTop ∧
      ∀ r, q r * (arrayMeasure N).real (NoSucc (N := N) p m r)
        ≤ (arrayMeasure N).real (FirstSuccessCell (N := N) p m r))
      ↔ (arrayMeasure N) (InfiniteFailure (N := N) p m) = 0 := by
  constructor
  · rintro ⟨q, h0, h1, hdiv, hforce⟩
    exact infiniteFailure_eq_zero_of_tendsto_sum h0 h1 hdiv hforce
  · intro hnull
    exact exists_divergent_force_of_tendsto_zero
      ((tendsto_noSuccMass_zero_iff_infiniteFailure_eq_zero).mpr hnull)

/-- **Falsification criterion.**  Positive all-fail mass refutes the force: on such a model no
divergent per-level force can exist.  This is the exact sense in which the force is not a
strictly weaker input than nullity. -/
theorem no_divergent_force_of_pos_infiniteFailure
    (hpos : 0 < (arrayMeasure N) (InfiniteFailure (N := N) p m)) :
    ¬ ∃ q : ℕ → ℝ, (∀ r, 0 ≤ q r) ∧ (∀ r, q r ≤ 1) ∧
      Tendsto (fun R : ℕ => ∑ r ∈ Finset.range R, q r) atTop atTop ∧
      ∀ r, q r * (arrayMeasure N).real (NoSucc (N := N) p m r)
        ≤ (arrayMeasure N).real (FirstSuccessCell (N := N) p m r) := by
  rintro ⟨q, h0, h1, hdiv, hforce⟩
  have hnull := infiniteFailure_eq_zero_of_tendsto_sum h0 h1 hdiv hforce
  rw [hnull] at hpos
  exact lt_irrefl _ hpos

end Actual

end TowerForceSharp
