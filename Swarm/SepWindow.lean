/-
# The separation remainder of `(locgroup)` from a deterministic base time

Generalisation of `SepResidual.lean` to a base time `a`: the window estimate
`measure_max_abs_Q_pair_le` charges separation failure over `j < a + n`, and the reduction below
reduces that remainder, *on the event that `(sep)` holds at the base time `a`*, to three
one-sided events over the window `[a, a+n)`, with the descent measured from the time-`a`
positions.  The time-`0` version (`SepResidual.lean`) is the special case `a = 0`.

`GroupQAzuma.measure_max_abs_Q_pair_le` bounds the maximal oscillation of the compensator
martingale `Q^{I,J}` except on two *residual* geometric events, the first of which is

  `⋃ j, {not Sep p m j I J}`   (separation fails somewhere in the window).

That is an honest remainder, but its probability is not bounded there.  This file records the
**exact deterministic content of the residual separation event** on the actual array model:

* `sepClause_iff_two_le_gapMin` — `(sep)`'s separation clause at time `k` is *equivalent* to
  `2 ≤ gapMin`, where `gapMin` is the worst-case gap
  `min_{i in I} X_k^i - max_{j in J} runMax_j(k)` (running maxima of the `J`-walkers);
* `gapMin_succ_ge` — one unit step moves the gap by at most `2` (an `I`-walker down by one, a
  `J`-running-maximum up by one);
* `descent_or_ascent` — **the exact residual reduction**.  If `(sep)` holds at time `0` and fails
  at time `k`, then either some walker is below `0` at time `k`, or some `I`-walker has descended
  from its own time-`0` position, or some `J`-walker's running maximum has risen above its
  time-`0` value, and the descent or the ascent is at least `(gapMin_0 - 1)/2`:
  `gapMin_0 - 1 ≤ 2 * (X_0^i - X_k^i)` resp. `gapMin_0 - 1 ≤ 2 * (runMax_j(k) - runMax_j(0))`.
  Both alternatives are *one-sided* events in the direction of the drift (an `I`-walker sinks,
  a `J`-walker climbs), i.e. exactly the shape for which the model's one-sided estimates apply;
* `gapMin_sub_one_le_two_mul_time` — the deterministic time obstruction: those alternatives
  cannot happen before time `(gapMin_0 - 1)/2`;
* `measureReal_sep_residual_le` — the corresponding bound of the *outer* measure of the residual
  separation event by the three one-sided probabilities, on the event that `(sep)` holds at
  the base time `a`.

No probability of a one-sided event is bounded here; those remain the named remaining inputs
(`(sep)`-survival, `h_1`/`h_2`-type one-sided walker estimates).  Nothing probabilistic is
assumed: everything above is a statement about the strong trajectory at every array `U`.
-/
import Swarm.SepGroup
import Swarm.UniformArray

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace LocSepWindow

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie

variable {N : ℕ}

/-! ## 1. The separation clause and the worst-case gap -/

/-- The separation clause of the paper's `(sep)`, without the nonnegativity clause: every walker
of `I` is at least two above every running maximum of a walker of `J`. -/
def SepClause (p : ℝ) (m k : ℕ) (I J : Finset (Fin N)) (U : Array N) : Prop :=
  ∀ i ∈ I, ∀ j ∈ J, runMax p m U j k + 2 ≤ X p m U k i

/-- `(sep)` is exactly nonnegativity plus the separation clause. -/
theorem sep_iff (p : ℝ) (m k : ℕ) (I J : Finset (Fin N)) (U : Array N) :
    Sep p m U k I J ↔ (∀ i, 0 ≤ X p m U k i) ∧ SepClause p m k I J U :=
  Iff.rfl

/-- The worst-case gap between the lowest `I`-position and the highest `J`-running-maximum. -/
noncomputable def gapMin (p : ℝ) (m k : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty)
    (hJ : J.Nonempty) (U : Array N) : ℤ :=
  I.inf' hI (fun i => X p m U k i) - J.sup' hJ (fun j => runMax p m U j k)

variable {p : ℝ} {m k : ℕ} {I J : Finset (Fin N)} {U : Array N}

/-- **The separation clause is the two-sided gap inequality.** -/
theorem sepClause_iff_two_le_gapMin (hI : I.Nonempty) (hJ : J.Nonempty) :
    SepClause p m k I J U ↔ 2 ≤ gapMin p m k I J hI hJ U := by
  constructor
  · intro h
    have hsup : J.sup' hJ (fun j => runMax p m U j k)
        ≤ I.inf' hI (fun i => X p m U k i) - 2 := by
      refine Finset.sup'_le hJ (f := fun j => runMax p m U j k) (fun j hj => ?_)
      have h2 : runMax p m U j k + 2 ≤ I.inf' hI (fun i => X p m U k i) :=
        Finset.le_inf' hI (f := fun i => X p m U k i) (fun i hi => h i hi j hj)
      linarith
    unfold gapMin
    linarith
  · intro h i hi j hj
    have h1 : I.inf' hI (fun i => X p m U k i) ≤ X p m U k i :=
      Finset.inf'_le (f := fun i => X p m U k i) hi
    have h2 : runMax p m U j k ≤ J.sup' hJ (fun j => runMax p m U j k) :=
      Finset.le_sup' (f := fun j => runMax p m U j k) hj
    unfold gapMin at h
    linarith

/-- The `I`-minimum can drop by at most one in a unit step. -/
theorem inf'_succ_ge (hI : I.Nonempty) (p : ℝ) (m : ℕ) (U : Array N) (k : ℕ) :
    I.inf' hI (fun i => X p m U k i) - 1 ≤ I.inf' hI (fun i => X p m U (k + 1) i) := by
  refine Finset.le_inf' hI (f := fun i => X p m U (k + 1) i) (fun i hi => ?_)
  have h1 : I.inf' hI (fun i => X p m U k i) ≤ X p m U k i :=
    Finset.inf'_le (f := fun i => X p m U k i) hi
  have h2 : X p m U k i - 1 ≤ X p m U (k + 1) i := pos_sub_one_le_succ p m U k i
  linarith

/-- A `J`-running maximum can rise by at most one in a unit step. -/
theorem runMax_succ_le (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (k : ℕ) :
    runMax p m U j (k + 1) ≤ runMax p m U j k + 1 := by
  have hstep : ∀ t ∈ Finset.range (k + 1 + 1),
      (trajectory p m U t).pos j ≤ runMax p m U j k + 1 := by
    intro t ht
    rw [Finset.mem_range] at ht
    rcases Nat.lt_or_ge t (k + 1) with hlt | hge
    · have h1 : (trajectory p m U t).pos j ≤ runMax p m U j k :=
        le_runMax_of_le p m U k j (Nat.lt_succ_iff.mp hlt)
      linarith
    · have ht' : t = k + 1 := by omega
      subst ht'
      have h1 : (trajectory p m U (k + 1)).pos j
          ≤ (trajectory p m U k).pos j + 1 := pos_succ_le p m U k j
      have h2 : (trajectory p m U k).pos j ≤ runMax p m U j k :=
        le_runMax_of_le p m U k j (le_refl k)
      linarith
  exact Finset.sup'_le _ (f := fun t => (trajectory p m U t).pos j) hstep

/-- **The gap loses at most two per unit step.** -/
theorem gapMin_succ_ge (hI : I.Nonempty) (hJ : J.Nonempty) (p : ℝ) (m : ℕ) (U : Array N)
    (k : ℕ) :
    gapMin p m k I J hI hJ U ≤ gapMin p m (k + 1) I J hI hJ U + 2 := by
  have h1 := inf'_succ_ge (p := p) (m := m) (U := U) hI k
  have hsup : J.sup' hJ (fun j => runMax p m U j (k + 1))
      ≤ J.sup' hJ (fun j => runMax p m U j k) + 1 := by
    refine Finset.sup'_le hJ (f := fun j => runMax p m U j (k + 1)) (fun j hj => ?_)
    have h2 : runMax p m U j k ≤ J.sup' hJ (fun j => runMax p m U j k) :=
      Finset.le_sup' (f := fun j => runMax p m U j k) hj
    have := runMax_succ_le p m U j k
    linarith
  unfold gapMin
  linarith

/-! ## 2. Exact one-step witnesses and net moves -/

/-- Failure of the separation clause at time `k` exhibits a pair `(i, j)` whose gap is at most
one. -/
theorem not_sepClause_witness (h : ¬ SepClause p m k I J U) :
    ∃ i ∈ I, ∃ j ∈ J, X p m U k i ≤ runMax p m U j k + 1 := by
  unfold SepClause at h
  push Not at h
  obtain ⟨i, hi, j, hj, hij⟩ := h
  exact ⟨i, hi, j, hj, by omega⟩

/-- A walker at time `k` is at most `k` below its time-`0` position. -/
theorem X_le_add_time (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) :
    ∀ k : ℕ, X p m U 0 i - (k : ℤ) ≤ X p m U k i := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have h1 : X p m U k i - 1 ≤ X p m U (k + 1) i := pos_sub_one_le_succ p m U k i
      push_cast
      linarith

/-- A running maximum at time `k` is at most `k` above its time-`0` value. -/
theorem runMax_le_add_time (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) :
    ∀ k : ℕ, runMax p m U j k ≤ runMax p m U j 0 + (k : ℤ) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have h1 := runMax_succ_le p m U j k
      push_cast
      linarith

/-! ## 3. The exact residual reduction -/

/-- **The residual separation event splits into one-sided descent/ascent events.**
If `(sep)` holds at time `0` and fails at time `k`, then either a walker is negative at time `k`,
or an `I`-walker has sunk by at least `(gapMin_0 - 1)/2` from its own time-`0` position, or a
`J`-walker's running maximum has climbed by at least `(gapMin_0 - 1)/2` above its time-`0` value. -/
theorem descent_or_ascent (hI : I.Nonempty) (hJ : J.Nonempty) {a k : ℕ}
    (h0 : Sep p m U a I J) (hk : ¬ Sep p m U k I J) :
    (∃ i : Fin N, X p m U k i < 0) ∨
      (∃ i ∈ I, gapMin p m a I J hI hJ U - 1 ≤ 2 * (X p m U a i - X p m U k i)) ∨
      (∃ j ∈ J, gapMin p m a I J hI hJ U - 1
        ≤ 2 * (runMax p m U j k - runMax p m U j a)) := by
  by_cases hneg : ∃ i : Fin N, X p m U k i < 0
  · exact Or.inl hneg
  · push Not at hneg
    have hnc : ¬ SepClause p m k I J U := by
      intro hc
      exact hk ((sep_iff p m k I J U).mpr ⟨hneg, hc⟩)
    obtain ⟨i, hi, j, hj, hij⟩ := not_sepClause_witness hnc
    have hgap : gapMin p m a I J hI hJ U ≤ X p m U a i - runMax p m U j a := by
      have h1 : I.inf' hI (fun i => X p m U a i) ≤ X p m U a i :=
        Finset.inf'_le (f := fun i => X p m U a i) hi
      have h2 : runMax p m U j a ≤ J.sup' hJ (fun j => runMax p m U j a) :=
        Finset.le_sup' (f := fun j => runMax p m U j a) hj
      unfold gapMin
      linarith
    have hda : gapMin p m a I J hI hJ U - 1
        ≤ (X p m U a i - X p m U k i) + (runMax p m U j k - runMax p m U j a) := by
      linarith
    by_cases hd : gapMin p m a I J hI hJ U - 1 ≤ 2 * (X p m U a i - X p m U k i)
    · exact Or.inr (Or.inl ⟨i, hi, hd⟩)
    · refine Or.inr (Or.inr ⟨j, hj, ?_⟩)
      have hd' : 2 * (X p m U a i - X p m U k i) ≤ gapMin p m a I J hI hJ U - 1 - 1 := by
        omega
      omega


/-! ## 4. The residual event over a window from the base time `a` -/

/-- On the event that `(sep)` holds at the base time `a`, failure of `(sep)` at some time
`k ∈ [a, a+n]` implies one of the three one-sided events, with the descent measured from the
time-`a` positions. -/
theorem exists_descent_or_ascent_of_not_sep (hI : I.Nonempty) (hJ : J.Nonempty) {a n : ℕ}
    {U : Array N} (h0 : Sep p m U a I J)
    (hk : ∃ k, a ≤ k ∧ k ≤ a + n ∧ ¬ Sep p m U k I J) :
    (∃ k, a ≤ k ∧ k ≤ a + n ∧ ∃ i : Fin N, X p m U k i < 0) ∨
      (∃ k, a ≤ k ∧ k ≤ a + n ∧ ∃ i ∈ I,
        gapMin p m a I J hI hJ U - 1 ≤ 2 * (X p m U a i - X p m U k i)) ∨
      (∃ k, a ≤ k ∧ k ≤ a + n ∧ ∃ j ∈ J,
        gapMin p m a I J hI hJ U - 1 ≤ 2 * (runMax p m U j k - runMax p m U j a)) := by
  obtain ⟨k, hak, hkn, hfail⟩ := hk
  rcases descent_or_ascent (p := p) (m := m) hI hJ h0 hfail with h | h | h
  · exact Or.inl ⟨k, hak, hkn, h⟩
  · exact Or.inr (Or.inl ⟨k, hak, hkn, h⟩)
  · exact Or.inr (Or.inr ⟨k, hak, hkn, h⟩)

/-- **The decomposition of the separation remainder.**  The separation failure over
`j < a + n` is contained in its part at times `j ≤ a` plus the three one-sided events over the
window `[a, a+n]`.  No probability is assumed. -/
theorem sep_remainder_subset (hI : I.Nonempty) (hJ : J.Nonempty) (p : ℝ) (m a n : ℕ) :
    (⋃ j ∈ Finset.range (a + n), {U : Array N | ¬ Sep p m U j I J})
      ⊆ (⋃ j ∈ Finset.range (a + 1), {U : Array N | ¬ Sep p m U j I J})
        ∪ ({U : Array N | ∃ k ∈ Finset.Ico a (a + n + 1), ∃ i : Fin N, X p m U k i < 0}
          ∪ {U : Array N | ∃ k ∈ Finset.Ico a (a + n + 1), ∃ i ∈ I,
              gapMin p m a I J hI hJ U - 1 ≤ 2 * (X p m U a i - X p m U k i)}
          ∪ {U : Array N | ∃ k ∈ Finset.Ico a (a + n + 1), ∃ j ∈ J,
              gapMin p m a I J hI hJ U - 1
                ≤ 2 * (runMax p m U j k - runMax p m U j a)}) := by
  intro U hU
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hU
  obtain ⟨hjr, hfail⟩ := Set.mem_iUnion.mp hj
  have hjn : j < a + n := Finset.mem_range.mp hjr
  by_cases hja : j ≤ a
  · have hjar : j ∈ Finset.range (a + 1) := Finset.mem_range.mpr (by omega)
    refine Or.inl ?_
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨j, hjar, hfail⟩
  · push Not at hja
    have hmem : j ∈ Finset.Ico a (a + n + 1) := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    by_cases hsep : Sep p m U a I J
    · rcases descent_or_ascent (p := p) (m := m) hI hJ hsep hfail with h | h | h
      · exact Or.inr (Or.inl (Or.inl ⟨j, hmem, h⟩))
      · exact Or.inr (Or.inl (Or.inr ⟨j, hmem, h⟩))
      · exact Or.inr (Or.inr ⟨j, hmem, h⟩)
    · refine Or.inl ?_
      simp only [Set.mem_iUnion, exists_prop]
      exact ⟨a, Finset.mem_range.mpr (by omega), hsep⟩

/-- **The outer measure of the separation remainder, decomposed.**  This is the honest form of
the geometric remainder of the window estimate: the part before the base time (which is the
initial separation failure at a record start), plus three one-sided events over `[a, a+n]`
(a walker below zero, an `I`-walker sinking by `(gapMin_a - 1)/2`, a `J`-running-maximum climbing
by `(gapMin_a - 1)/2`). -/
theorem measureReal_sep_remainder_decomposed (hI : I.Nonempty) (hJ : J.Nonempty) (p : ℝ) (m a n : ℕ) :
    (arrayMeasure N).real (⋃ j ∈ Finset.range (a + n), {U : Array N | ¬ Sep p m U j I J})
      ≤ (arrayMeasure N).real (⋃ j ∈ Finset.range (a + 1), {U : Array N | ¬ Sep p m U j I J})
        + (arrayMeasure N).real
            {U : Array N | ∃ k ∈ Finset.Ico a (a + n + 1), ∃ i : Fin N, X p m U k i < 0}
        + (arrayMeasure N).real {U : Array N | ∃ k ∈ Finset.Ico a (a + n + 1), ∃ i ∈ I,
            gapMin p m a I J hI hJ U - 1 ≤ 2 * (X p m U a i - X p m U k i)}
        + (arrayMeasure N).real {U : Array N | ∃ k ∈ Finset.Ico a (a + n + 1), ∃ j ∈ J,
            gapMin p m a I J hI hJ U - 1 ≤ 2 * (runMax p m U j k - runMax p m U j a)} := by
  set S := (⋃ j ∈ Finset.range (a + n), {U : Array N | ¬ Sep p m U j I J}) with hSdef
  set S1 := (⋃ j ∈ Finset.range (a + 1), {U : Array N | ¬ Sep p m U j I J}) with hS1def
  set A := {U : Array N | ∃ k ∈ Finset.Ico a (a + n + 1), ∃ i : Fin N, X p m U k i < 0}
    with hAdef
  set B := {U : Array N | ∃ k ∈ Finset.Ico a (a + n + 1), ∃ i ∈ I,
      gapMin p m a I J hI hJ U - 1 ≤ 2 * (X p m U a i - X p m U k i)} with hBdef
  set C := {U : Array N | ∃ k ∈ Finset.Ico a (a + n + 1), ∃ j ∈ J,
      gapMin p m a I J hI hJ U - 1 ≤ 2 * (runMax p m U j k - runMax p m U j a)} with hCdef
  have hsub : S ⊆ S1 ∪ (A ∪ B ∪ C) := by
    simpa only [hSdef, hS1def, hAdef, hBdef, hCdef] using
      (sep_remainder_subset (N := N) (p := p) (m := m) hI hJ a n)
  have hmono := measureReal_mono hsub (measure_ne_top (arrayMeasure N) _)
  have hu1 : (arrayMeasure N).real (S1 ∪ (A ∪ B ∪ C))
      ≤ (arrayMeasure N).real S1 + (arrayMeasure N).real (A ∪ B ∪ C) :=
    measureReal_union_le (μ := arrayMeasure N) (s₁ := S1) (s₂ := A ∪ B ∪ C)
  have hu2 : (arrayMeasure N).real (A ∪ B ∪ C)
      ≤ (arrayMeasure N).real (A ∪ B) + (arrayMeasure N).real C :=
    measureReal_union_le (μ := arrayMeasure N) (s₁ := A ∪ B) (s₂ := C)
  have hu3 : (arrayMeasure N).real (A ∪ B)
      ≤ (arrayMeasure N).real A + (arrayMeasure N).real B :=
    measureReal_union_le (μ := arrayMeasure N) (s₁ := A) (s₂ := B)
  have hchain : (arrayMeasure N).real S
      ≤ (arrayMeasure N).real S1 + (((arrayMeasure N).real A
        + (arrayMeasure N).real B) + (arrayMeasure N).real C) := by
    refine le_trans hmono (le_trans hu1 (add_le_add le_rfl ?_))
    exact le_trans hu2 (add_le_add hu3 le_rfl)
  linarith

end LocSepWindow
