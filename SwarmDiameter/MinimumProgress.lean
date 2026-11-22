import SwarmDiameter.RecordLocalClauses
import Swarm.DeepExc

open Filter Finset MeasureTheory Set
open Swarming.Uniform Swarming.Model Swarming.Trajectory SwarmRecordMeas.Actual
open PaperBlock

set_option autoImplicit false

namespace Swarming.Diameter

/-- If some minimizer is excited at each step, the minimum advances at least
the drift divided by the number of walkers, up to the compensated errors.
We sum the compensated paths truncated at a level determined by the final minimum. -/
theorem minimum_progress_of_compensated_error {ι : Type*} [Fintype ι] [Nonempty ι]
    (X : ι → ℕ → ℤ) (A : ι → ℕ → ℕ) {μ E : ℝ} (hμ : 0 ≤ μ) (hE : 0 ≤ E)
    {s t : ℕ} (hst : s ≤ t) (hA : ∀ i, Monotone (A i))
    (hM : ∀ i n, s ≤ n → n ≤ t →
      |((X i n : ℝ) - μ * (A i n : ℝ)) - ((X i s : ℝ) - μ * (A i s : ℝ))| ≤ E)
    (hmin : ∀ n, s ≤ n → n < t → ∃ i,
      X i n = RecordDefect.runMin X n ∧ A i (n + 1) = A i n + 1) :
    (RecordDefect.runMin X s : ℝ) + μ / (Fintype.card ι : ℝ) * ((t : ℝ) - s) -
        3 * E - μ ≤ (RecordDefect.runMin X t : ℝ) := by
  classical
  let Y (i : ι) (n : ℕ) : ℝ := (X i s : ℝ) + μ * ((A i n : ℝ) - A i s)
  have hYmono (i : ι) : Monotone (Y i) := by
    intro a b hab
    have h : (A i a : ℝ) ≤ A i b := by exact_mod_cast hA i hab
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (sub_le_sub_right h _) hμ)
  have hYs (i : ι) : Y i s = (X i s : ℝ) := by simp [Y]
  have hYclose (i : ι) (n : ℕ) (hs : s ≤ n) (ht : n ≤ t) :
      |(X i n : ℝ) - Y i n| ≤ E := by
    convert hM i n hs ht using 2
    dsimp only [Y]
    ring
  obtain ⟨j, -, hj⟩ :=
    Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun i => X i t)
  change RecordDefect.runMin X t = X j t at hj
  have hjt : Y j t ≤ (RecordDefect.runMin X t : ℝ) + E := by
    rw [hj]
    linarith only [(abs_le.mp (hYclose j t hst le_rfl)).1]
  let H := (RecordDefect.runMin X t : ℝ) + 3 * E + μ
  have hHs : (RecordDefect.runMin X s : ℝ) ≤ H := by
    have hxs : (RecordDefect.runMin X s : ℝ) ≤ X j s := by
      exact_mod_cast RecordDefect.runMin_le (X := X) s j
    have hy := hYmono j hst
    rw [hYs] at hy
    dsimp only [H]
    linarith
  let Z (n : ℕ) : ℝ := ∑ i, min (Y i n) H
  have hZstep (n : ℕ) (hs : s ≤ n) (ht : n < t) : μ ≤ Z (n + 1) - Z n := by
    obtain ⟨i, hi, hAi⟩ := hmin n hs ht
    have hpos : (X i n : ℝ) ≤ X j n := by
      exact_mod_cast (hi ▸ RecordDefect.runMin_le (X := X) n j)
    have hYi : Y i n ≤ (RecordDefect.runMin X t : ℝ) + 3 * E := by
      have hci := (abs_le.mp (hYclose i n hs ht.le)).1
      have hcj := (abs_le.mp (hYclose j n hs ht.le)).2
      have hyt := hYmono j ht.le
      linarith only [hci, hpos, hcj, hyt, hjt]
    have hinc : Y i (n + 1) = Y i n + μ := by
      dsimp only [Y]
      rw [hAi, Nat.cast_add, Nat.cast_one]
      ring
    have hbound : Y i (n + 1) ≤ H := by rw [hinc]; exact add_le_add hYi le_rfl
    have hbefore : Y i n ≤ H := (hYmono i (Nat.le_succ n)).trans hbound
    have hdiff : min (Y i (n + 1)) H - min (Y i n) H = μ := by
      rw [min_eq_left hbound, min_eq_left hbefore, hinc, add_sub_cancel_left]
    dsimp only [Z]
    rw [← Finset.sum_sub_distrib, ← hdiff]
    exact Finset.single_le_sum (fun k _ => sub_nonneg.mpr
      (min_le_min (hYmono k (Nat.le_succ n)) le_rfl)) (Finset.mem_univ i)
  have hZtotal (n : ℕ) (hs : s ≤ n) (ht : n ≤ t) :
      μ * ((n : ℝ) - s) ≤ Z n - Z s := by
    induction n, hs using Nat.le_induction with
    | base => simp
    | succ n hs ih =>
      have hnt : n < t := ht
      have hprev := ih hnt.le
      have hnext := hZstep n hs hnt
      push_cast
      linarith only [hprev, hnext]
  have hZs : (Fintype.card ι : ℝ) * (RecordDefect.runMin X s : ℝ) ≤ Z s := calc
    _ = ∑ _ : ι, (RecordDefect.runMin X s : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun i _ => by
      rw [hYs]
      exact le_min (by exact_mod_cast RecordDefect.runMin_le (X := X) s i) hHs
  have hZt : Z t ≤ (Fintype.card ι : ℝ) * H := calc
    _ ≤ ∑ _ : ι, H := Finset.sum_le_sum fun _ _ => min_le_right _ _
    _ = _ := by simp
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos (α := ι)
  have hrate : μ / (Fintype.card ι : ℝ) * ((t : ℝ) - s) ≤
      H - (RecordDefect.runMin X s : ℝ) := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hcard).2
    linarith only [hZtotal t hst le_rfl, hZs, hZt]
  dsimp only [H] at hrate
  linarith only [hrate]

/-- When `m < N`, the swarm minimum advances at speed at least
`(2 * p - 1) / N` up to the prescribed error on every subinterval of
the record-time window, with an exponentially small exceptional probability. -/
theorem record_minimum_progress_failure_le_exp
    {N : ℕ} [Nonempty (Fin N)] {p : ℝ} {m : ℕ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1)
    (hm : 2 ≤ m) (hmN : m < N) (T : ℕ) (hT : 1 ≤ T) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ L : ℕ in atTop, ∀ r : ℕ, (T + 3) * L ≤ r →
      (arrayMeasure N).real (RecClockLG.recordCarrier (N := N) p m r L ∩ {U |
        ∃ s t : ℕ, recTimeA p m U r ≤ s ∧ s ≤ t ∧ t ≤ recTimeA p m U r + T * L ∧
          (RecordDefect.runMin (Xa p m U) t : ℝ) <
            (RecordDefect.runMin (Xa p m U) s : ℝ) + (2 * p - 1) / (N : ℝ) * ((t : ℝ) - s) -
              ε * (L : ℝ)}) ≤ (N : ℝ) * Real.exp (-c * (L : ℝ)) := by
  classical
  let δ := ε / 6
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hN : 2 ≤ N := hm.trans hmN.le
  obtain ⟨c, hc, hprob⟩ := record_drift_martingale_failure_le_exp hp₀ hp₁ hm hN T hT hδ
  have htop : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  refine ⟨c, hc, ?_⟩
  filter_upwards [hprob, htop.eventually_ge_atTop (2 / ε)] with L hLp hL
  intro r hr
  have hLε : 2 ≤ ε * (L : ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ hε).mp hL
  have herror : 3 * (δ * (L : ℝ)) + (2 * p - 1) ≤ ε * (L : ℝ) := by
    dsimp only [δ]
    linarith only [hLε, hp₁]
  let B (i : Fin N) := RecordClock.stoppedWindowRec p m r (T * L) (δ * L) i
  have hsub : RecClockLG.recordCarrier (N := N) p m r L ∩ {U |
      ∃ s t : ℕ, recTimeA p m U r ≤ s ∧ s ≤ t ∧ t ≤ recTimeA p m U r + T * L ∧
        (RecordDefect.runMin (Xa p m U) t : ℝ) <
          (RecordDefect.runMin (Xa p m U) s : ℝ) + (2 * p - 1) / (N : ℝ) * ((t : ℝ) - s) -
            ε * (L : ℝ)} ⊆ ⋃ i, B i := by
    rintro U ⟨hU, s, t, hs, hst, ht, hbad⟩
    by_contra hnone
    have hM (i : Fin N) (n : ℕ) (hsn : s ≤ n) (hnt : n ≤ t) :
        |driftMartingale p m U n i - driftMartingale p m U s i| ≤ δ * L := by
      by_contra! h
      exact hnone (Set.mem_iUnion.mpr ⟨i, ClockLocMove.mem_stoppedWindow_of_pair
        (Q := fun n U => driftMartingale p m U n i) hs hsn (hnt.trans ht) h.le⟩)
    have hmin (n : ℕ) (hsn : s ≤ n) (hnt : n < t) :
        ∃ i : Fin N, Xa p m U i n = RecordDefect.runMin (Xa p m U) n ∧
          excitedSteps p m U (n + 1) i = excitedSteps p m U n i + 1 := by
      obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun i => Xa p m U i n)
      change RecordDefect.runMin (Xa p m U) n = Xa p m U i n at hi
      refine ⟨i, hi.symm, ?_⟩
      have hpos := nonneg_of_carrier p m r L T U hU hr (hs.trans hsn) (hnt.le.trans ht) i
      have hminpos (j : Fin N) : Xa p m U i n ≤ Xa p m U j n :=
        hi ▸ RecordDefect.runMin_le (X := Xa p m U) n j
      have he := excited_of_isMin p m U n i hpos rfl hminpos (show m ≤ N - 1 by omega)
      simp only [excitedSteps, Finset.sum_range_succ]
      congr 1
      exact if_pos he
    have hgood := minimum_progress_of_compensated_error (Xa p m U)
      (fun i n => excitedSteps p m U n i) (M1DMart.two_p_sub_one_pos hp₀).le
      (mul_nonneg hδ.le (Nat.cast_nonneg L)) hst (M1DMart.monotone_excitedSteps p m U)
      (fun i n hsn hnt => by
        simpa only [M1DMart.Xa_excitedSteps_martingaleEq] using hM i n hsn hnt) hmin
    rw [Fintype.card_fin] at hgood
    linarith only [hgood, herror, hbad]
  refine ((measureReal_mono hsub).trans (measureReal_iUnion_fintype_le B)).trans ?_
  simpa only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin] using
    (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N))) (fun i _ => hLp r i))

end Swarming.Diameter
