/-
# Finite enriched prefixes determine arbitrary raw-time windows

This file gives a measurable, self-contained index calculation on the first `n+1` enriched
atoms. `prefixCum` is the cumulative record time and `prefixBlk v t` is the least `k` with
`t < prefixCum v (k+1)`. Beyond the supplied prefix the cumulative function is extended by
unit durations, solely to make the least-number operator total; for `t ≤ n` none is read.
The finite calculation agrees with the actual `chainOf` path for a compatible trajectory.
The record-boundary formula selects the segment beginning at that time.
-/
import Swarm.ChainFiniteWindow

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal
open SimJump

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace SwarmFinFuture

attribute [local instance] Classical.propDecidable

variable {N m : ℕ}

/-- The record consisting of enriched atoms `0,…,n`. -/
abbrev Prefix (n : ℕ) := Π _i : Finset.Iic n, SwarmInfSeg.Pair N m

/-- Cumulative record times read from a finite record. The `else 1` branch is only a totalising
extension after the supplied atoms. -/
def prefixCum {n : ℕ} (v : Prefix (N := N) (m := m) n) : ℕ → ℕ
  | 0 => 0
  | k + 1 => prefixCum v k + if h : k ≤ n then
      (v ⟨k, Finset.mem_Iic.2 h⟩).1.dur else 1

@[simp] theorem prefixCum_zero {n : ℕ} (v : Prefix (N := N) (m := m) n) :
    prefixCum v 0 = 0 := rfl

theorem prefixCum_succ_of_le {n k : ℕ} (v : Prefix (N := N) (m := m) n) (h : k ≤ n) :
    prefixCum v (k + 1) = prefixCum v k + (v ⟨k, Finset.mem_Iic.2 h⟩).1.dur := by
  simp [prefixCum, h]

theorem prefixCum_succ_of_not_le {n k : ℕ} (v : Prefix (N := N) (m := m) n) (h : ¬ k ≤ n) :
    prefixCum v (k + 1) = prefixCum v k + 1 := by
  simp [prefixCum, h]

theorem prefixCum_lt_succ {n : ℕ} (v : Prefix (N := N) (m := m) n) (k : ℕ) :
    prefixCum v k < prefixCum v (k + 1) := by
  by_cases h : k ≤ n
  · rw [prefixCum_succ_of_le v h]
    have := (v ⟨k, Finset.mem_Iic.2 h⟩).1.dur_pos
    omega
  · rw [prefixCum_succ_of_not_le v h]
    omega

theorem prefixCum_strictMono {n : ℕ} (v : Prefix (N := N) (m := m) n) :
    StrictMono (prefixCum v) :=
  strictMono_nat_of_lt_succ (prefixCum_lt_succ v)

theorem le_prefixCum {n : ℕ} (v : Prefix (N := N) (m := m) n) (k : ℕ) :
    k ≤ prefixCum v k := by
  induction k with
  | zero => simp
  | succ k ih => have := prefixCum_lt_succ v k; omega

theorem exists_prefixCum_gt {n : ℕ} (v : Prefix (N := N) (m := m) n) (t : ℕ) :
    ∃ k, t < prefixCum v (k + 1) :=
  ⟨t, lt_of_lt_of_le (Nat.lt_succ_self t) (le_prefixCum v (t + 1))⟩

/-- The least segment whose half-open raw-time interval contains `t`. -/
noncomputable def prefixBlk {n : ℕ} (v : Prefix (N := N) (m := m) n) (t : ℕ) : ℕ :=
  Nat.find (exists_prefixCum_gt v t)

theorem prefixBlk_spec {n : ℕ} (v : Prefix (N := N) (m := m) n) (t : ℕ) :
    t < prefixCum v (prefixBlk v t + 1) :=
  Nat.find_spec (exists_prefixCum_gt v t)

theorem prefixBlk_le {n : ℕ} (v : Prefix (N := N) (m := m) n) {t k : ℕ}
    (h : t < prefixCum v (k + 1)) : prefixBlk v t ≤ k :=
  Nat.find_min' (exists_prefixCum_gt v t) h

theorem prefixBlk_le_time {n : ℕ} (v : Prefix (N := N) (m := m) n) (t : ℕ) :
    prefixBlk v t ≤ t :=
  prefixBlk_le v (lt_of_lt_of_le (Nat.lt_succ_self t) (le_prefixCum v (t + 1)))

theorem prefixCum_blk_le {n : ℕ} (v : Prefix (N := N) (m := m) n) (t : ℕ) :
    prefixCum v (prefixBlk v t) ≤ t := by
  rcases Nat.eq_zero_or_pos (prefixBlk v t) with h | h
  · rw [h]
    exact Nat.zero_le t
  · obtain ⟨k, hk⟩ : ∃ k, prefixBlk v t = k + 1 := ⟨prefixBlk v t - 1, by omega⟩
    by_contra hcon
    have hlt : t < prefixCum v (k + 1) := by rw [← hk]; omega
    have := prefixBlk_le v hlt
    omega

/-- At a record time the selected block is the segment beginning at that time. -/
theorem prefixBlk_record {n k : ℕ} (v : Prefix (N := N) (m := m) n) :
    prefixBlk v (prefixCum v k) = k := by
  refine le_antisymm (prefixBlk_le v (prefixCum_lt_succ v k)) ?_
  by_contra hcon
  push Not at hcon
  have hs := prefixBlk_spec v (prefixCum v k)
  have hle := le_prefixCum v (prefixBlk v (prefixCum v k) + 1)
  have hmono := (prefixCum_strictMono v).monotone
    (show prefixBlk v (prefixCum v k) + 1 ≤ k by omega)
  omega

/-- The raw position read from the finite prefix. The zero branch is unreachable for `t ≤ n`. -/
noncomputable def prefixX {n : ℕ} (v : Prefix (N := N) (m := m) n) (t : ℕ) (i : Fin N) : ℤ :=
  if h : prefixBlk v t ≤ n then
    (prefixBlk v t : ℤ) +
      (v ⟨prefixBlk v t, Finset.mem_Iic.2 h⟩).1.p (t - prefixCum v (prefixBlk v t)) i
  else 0

/-- Joint position evaluation is measurable despite its natural-time second argument. -/
theorem measurable_seg_p_dyn (i : Fin N) :
    Measurable (fun q : SwarmConcat.Seg N × ℕ => q.1.p q.2 i) :=
  measurable_from_prod_countable_left (fun r => SwarmConcat.measurable_seg_p r i)

theorem measurable_prefixCum {n : ℕ} (k : ℕ) :
    Measurable (fun v : Prefix (N := N) (m := m) n => prefixCum v k) := by
  induction k with
  | zero => simpa only [prefixCum_zero] using
      (measurable_const : Measurable (fun _ : Prefix (N := N) (m := m) n => (0 : ℕ)))
  | succ k ih =>
      by_cases h : k ≤ n
      · rw [show (fun v : Prefix (N := N) (m := m) n => prefixCum v (k + 1)) =
            fun v => prefixCum v k + (v ⟨k, Finset.mem_Iic.2 h⟩).1.dur from
          funext fun v => prefixCum_succ_of_le v h]
        exact ih.add (SwarmConcat.measurable_seg_dur.comp
          (measurable_fst.comp (measurable_pi_apply
            (⟨k, Finset.mem_Iic.2 h⟩ : ↥(Finset.Iic n)))))
      · rw [show (fun v : Prefix (N := N) (m := m) n => prefixCum v (k + 1)) =
            fun v => prefixCum v k + 1 from
          funext fun v => prefixCum_succ_of_not_le v h]
        exact ih.add measurable_const

theorem measurable_prefixBlk {n : ℕ} (t : ℕ) :
    Measurable (fun v : Prefix (N := N) (m := m) n => prefixBlk v t) := by
  unfold prefixBlk
  exact measurable_find (exists_prefixCum_gt · t) (fun k =>
    measurableSet_lt measurable_const (measurable_prefixCum (N := N) (m := m) (k + 1)))

theorem measurable_prefixX {n : ℕ} (t : ℕ) (i : Fin N) :
    Measurable (fun v : Prefix (N := N) (m := m) n => prefixX v t i) := by
  unfold prefixX prefixBlk
  refine Measurable.find (p := fun k v => t < prefixCum v (k + 1))
    (f := fun k v => if h : k ≤ n then
      (k : ℤ) + (v ⟨k, Finset.mem_Iic.2 h⟩).1.p (t - prefixCum v k) i else 0) ?_ ?_
    (fun v => exists_prefixCum_gt v t)
  · intro k
    by_cases h : k ≤ n
    · simp only [h, dif_pos]
      exact measurable_const.add ((measurable_seg_p_dyn i).comp
        ((measurable_fst.comp (measurable_pi_apply
          (⟨k, Finset.mem_Iic.2 h⟩ : ↥(Finset.Iic n)))).prodMk
          (measurable_const.sub (measurable_prefixCum k))))
    · simp only [h, dif_neg]
      exact measurable_const
  · intro k
    exact measurableSet_lt measurable_const (measurable_prefixCum (k + 1))

/-- The full finite-prefix path (dummy beyond the supplied horizon). -/
noncomputable def prefixPath {n : ℕ} (v : Prefix (N := N) (m := m) n) : ℕ → Fin N → ℤ :=
  fun t i => prefixX v t i

theorem measurable_prefixPath {n : ℕ} :
    Measurable (fun v : Prefix (N := N) (m := m) n => prefixPath v) := by
  exact measurable_pi_iff.mpr fun t => measurable_pi_iff.mpr fun i => measurable_prefixX t i

theorem measurable_prefixPat {n : ℕ} :
    Measurable (fun v : Prefix (N := N) (m := m) n =>
      SwarmFinHorizon.pathPat (N := N) n (prefixPath v)) := by
  exact (SwarmFinHorizon.measurable_pathPat n).comp measurable_prefixPath

/-- Exact interval criterion for the finite least block. -/
theorem prefixBlk_of_between {n : ℕ} (v : Prefix (N := N) (m := m) n) {t k : ℕ}
    (h1 : prefixCum v k ≤ t) (h2 : t < prefixCum v (k + 1)) :
    prefixBlk v t = k := by
  refine le_antisymm (prefixBlk_le v h2) ?_
  by_contra hcon
  push Not at hcon
  have hs := prefixBlk_spec v t
  have hmono := (prefixCum_strictMono v).monotone
    (show prefixBlk v t + 1 ≤ k by omega)
  omega

/-- **Interior and endpoint-explicit raw path formula.** The local time can be `dur atom k`
only at the upper endpoint, which instead belongs to atom `k+1`; the two formulas therefore
cover every duration split without overlap. -/
theorem prefixX_of_between {n k : ℕ} (v : Prefix (N := N) (m := m) n) {t : ℕ}
    (hk : k ≤ n) (h1 : prefixCum v k ≤ t) (h2 : t < prefixCum v (k + 1)) (i : Fin N) :
    prefixX v t i = (k : ℤ) + (v ⟨k, Finset.mem_Iic.2 hk⟩).1.p (t - prefixCum v k) i := by
  have hb := prefixBlk_of_between v h1 h2
  unfold prefixX
  simp only [hb, dif_pos hk]

/-- Record-boundary formula, including the case where the record is the last raw position. -/
theorem prefixX_record {n k : ℕ} (v : Prefix (N := N) (m := m) n) (h : k ≤ n) (i : Fin N) :
    prefixX v (prefixCum v k) i =
      (k : ℤ) + (v ⟨k, Finset.mem_Iic.2 h⟩).1.p 0 i := by
  unfold prefixX
  simp only [prefixBlk_record, dif_pos h, Nat.sub_self]

/-- Cumulative times computed from a compatible trajectory are the actual chain cumulative times. -/
theorem prefixCum_eq_chain_cum {n : ℕ} {A : ℕ → SwarmInfSeg.Pair N m}
    (hA : SwarmChainAssemble.TrajCompat A) {k : ℕ} (hk : k ≤ n + 1) :
    prefixCum (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) n A) k =
      (SwarmChainAssemble.chainOf A).cum k := by
  induction k with
  | zero => rw [prefixCum_zero, SwarmConcat.Chain.cum_zero]
  | succ k ih =>
      have hkn : k ≤ n := by omega
      rw [prefixCum_succ_of_le _ hkn, SwarmConcat.Chain.cum_succ, ih (by omega),
        SwarmChainAssemble.chainOf_seg_of_compat hA k]
      rfl

/-- For raw time at most `n`, the finite least block is the actual chain block. -/
theorem prefixBlk_eq_chain_blk {n : ℕ} {A : ℕ → SwarmInfSeg.Pair N m}
    (hA : SwarmChainAssemble.TrajCompat A) {t : ℕ} (ht : t ≤ n) :
    prefixBlk (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) n A) t =
      (SwarmChainAssemble.chainOf A).blk t := by
  let v : Prefix (N := N) (m := m) n :=
    Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) n A
  have hb : prefixBlk v t ≤ n := le_trans (prefixBlk_le_time v t) ht
  have hc : (SwarmChainAssemble.chainOf A).blk t ≤ n := by
    refine le_trans ((SwarmChainAssemble.chainOf A).blk_le ?_) ht
    exact lt_of_lt_of_le (Nat.lt_succ_self t) ((SwarmChainAssemble.chainOf A).le_cum (t + 1))
  apply le_antisymm
  · apply prefixBlk_le v
    rw [prefixCum_eq_chain_cum hA (by omega : (SwarmChainAssemble.chainOf A).blk t + 1 ≤ n + 1)]
    exact (SwarmChainAssemble.chainOf A).blk_spec t
  · apply (SwarmChainAssemble.chainOf A).blk_le
    rw [← prefixCum_eq_chain_cum hA (by omega : prefixBlk v t + 1 ≤ n + 1)]
    exact prefixBlk_spec v t

/-- **The finite-prefix path agrees with the actual assembled path at every raw time `t ≤ n`.** -/
theorem prefixX_eq_chain_X {n : ℕ} {A : ℕ → SwarmInfSeg.Pair N m}
    (hA : SwarmChainAssemble.TrajCompat A) {t : ℕ} (ht : t ≤ n) (i : Fin N) :
    prefixX (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) n A) t i =
      (SwarmChainAssemble.chainOf A).X t i := by
  let v : Prefix (N := N) (m := m) n :=
    Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) n A
  have hb : prefixBlk v t ≤ n := le_trans (prefixBlk_le_time v t) ht
  have hseg : (SwarmChainAssemble.chainOf A).seg (prefixBlk v t) =
      (v ⟨prefixBlk v t, Finset.mem_Iic.2 hb⟩).1 := by
    rw [SwarmChainAssemble.chainOf_seg_of_compat hA]
    rfl
  have hcum : prefixCum v (prefixBlk v t) =
      (SwarmChainAssemble.chainOf A).cum (prefixBlk v t) :=
    prefixCum_eq_chain_cum hA (by omega)
  have hcumNext : prefixCum v (prefixBlk v t + 1) =
      (SwarmChainAssemble.chainOf A).cum (prefixBlk v t + 1) :=
    prefixCum_eq_chain_cum hA (by omega)
  have h1 : (SwarmChainAssemble.chainOf A).cum (prefixBlk v t) ≤ t := by
    rw [← hcum]
    exact prefixCum_blk_le v t
  have h2 : t < (SwarmChainAssemble.chainOf A).cum (prefixBlk v t + 1) := by
    rw [← hcumNext]
    exact prefixBlk_spec v t
  change prefixX v t i = _
  rw [SwarmConcat.Chain.X_block _ h1 h2]
  unfold prefixX
  rw [dif_pos hb, ← hseg, hcum]

end SwarmFinFuture


