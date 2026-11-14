/-
Auxiliary symmetric walk: almost-sure divergence of the running maximum.

The integrated fixed-horizon non-hitting bound
`Swarming.SymmTransport.prob_nonhit_le_sqrt_actual`

  `P(∀ k ≤ n, S_k < b) ≤ (2b+1)√2/√(n+1)`

is upgraded here to a *pathwise* almost-sure statement.  Along the geometric
subsequence `n = 2^(4q)` with threshold `b = 2^q` the bound is summable in `q`,
so Borel--Cantelli gives that, almost surely, the running maximum up to time
`2^(4q)` eventually exceeds `2^q`.  Interpolating over `q = n.log2 / 4` yields

  `2 ^ (n.log2 / 4) ≤ S_k` for some `k ≤ n`, eventually in `n`,

and hence the running maximum of the actual auxiliary walk tends to `+∞`
almost surely.  Composing with the verified coupling
`Swarming.Trajectory.symmetricWalk_le_trajectory` transfers this to the running
maximum of the actual interacting trajectory.

This is the Borel--Cantelli step of the paper's Lemma `transience`; the
deterministic/martingale half of that lemma is *not* addressed here.
-/
import Swarm.Bound

open MeasureTheory ProbabilityTheory Set Filter
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory
open scoped ENNReal BigOperators Topology

namespace Swarming.SymmAeMax

variable {N : ℕ}

/-! ### The bad event at a geometric stage -/

/-- At stage `q`: up to time `2 ^ (4 * q)` the auxiliary walk stays strictly below
`2 ^ q`. -/
def badSet (p : ℝ) (m : ℕ) (i : Fin N) (q : ℕ) : Set (Array N) :=
  {U | ∀ k ≤ 2 ^ (4 * q), symmetricWalk p m U i k < ((2 ^ q : ℕ) : ℤ)}

/-- The bad event is literally the set appearing in the fixed-horizon non-hitting bound. -/
lemma badSet_eq (p : ℝ) (m : ℕ) (i : Fin N) (q : ℕ) :
    badSet p m i q =
      {U : Array N | ∀ k ≤ 2 ^ (4 * q), symmetricWalk p m U i k < ((2 ^ q : ℕ) : ℤ)} :=
  rfl

/-! ### Geometric summability of the bad events -/

/-- Explicit geometric decay of the bad events. -/
lemma measure_badSet_le (p : ℝ) (m : ℕ) (i : Fin N) (q : ℕ) :
    arrayMeasure N (badSet p m i q) ≤
      ENNReal.ofReal (3 * Real.sqrt 2 * (1 / 2 : ℝ) ^ q) := by
  have hb : 1 ≤ 2 ^ q := Nat.one_le_two_pow
  have h := Swarming.SymmTransport.prob_nonhit_le_sqrt_actual (N := N) (p := p) (m := m)
    (i := i) (n := 2 ^ (4 * q)) (b := 2 ^ q) hb
  have hreal : (arrayMeasure N).real (badSet p m i q) ≤
      3 * Real.sqrt 2 * (1 / 2 : ℝ) ^ q := by
    refine h.trans ?_
    push_cast
    set Q : ℝ := (2 : ℝ) ^ q with hQ
    have hhalf : (1 / 2 : ℝ) ^ q = Q⁻¹ := by
      simp only [one_div, inv_pow, hQ]
    have hcast : (2 : ℝ) ^ (4 * q) = Q ^ 4 := by
      rw [hQ, ← pow_mul]
      congr 1
      omega
    rw [hhalf, hcast]
    have hQ1 : (1 : ℝ) ≤ Q := one_le_pow₀ (by norm_num)
    have hQpos : (0 : ℝ) < Q := by linarith
    have hsqrt : Q ^ 2 ≤ Real.sqrt (Q ^ 4 + 1) := by
      have h1 : Real.sqrt ((Q ^ 2) ^ 2) = Q ^ 2 := Real.sqrt_sq (by positivity)
      rw [← h1]
      apply Real.sqrt_le_sqrt
      nlinarith [sq_nonneg Q, sq_nonneg (Q ^ 2)]
    have hpos : (0 : ℝ) < Real.sqrt (Q ^ 4 + 1) := by
      apply Real.sqrt_pos.2
      positivity
    rw [div_le_iff₀ hpos]
    have h1 : 3 * Real.sqrt 2 * Q⁻¹ * Q ^ 2 ≤
        3 * Real.sqrt 2 * Q⁻¹ * Real.sqrt (Q ^ 4 + 1) :=
      mul_le_mul_of_nonneg_left hsqrt (by positivity)
    have h2 : 3 * Real.sqrt 2 * Q⁻¹ * Q ^ 2 = 3 * Real.sqrt 2 * Q := by
      field_simp
    have h3 : (2 * Q + 1) * Real.sqrt 2 ≤ 3 * Real.sqrt 2 * Q := by
      have hle : 2 * Q + 1 ≤ 3 * Q := by linarith
      calc (2 * Q + 1) * Real.sqrt 2 ≤ (3 * Q) * Real.sqrt 2 :=
            mul_le_mul_of_nonneg_right hle (Real.sqrt_nonneg 2)
        _ = 3 * Real.sqrt 2 * Q := by ring
    linarith
  have hne : arrayMeasure N (badSet p m i q) ≠ ∞ := measure_ne_top _ _
  calc arrayMeasure N (badSet p m i q)
      = ENNReal.ofReal ((arrayMeasure N).real (badSet p m i q)) := by
        rw [measureReal_def, ENNReal.ofReal_toReal hne]
    _ ≤ ENNReal.ofReal (3 * Real.sqrt 2 * (1 / 2 : ℝ) ^ q) := ENNReal.ofReal_le_ofReal hreal

/-- The bad events have finite total mass. -/
lemma tsum_badSet_ne_top (p : ℝ) (m : ℕ) (i : Fin N) :
    (∑' q : ℕ, arrayMeasure N (badSet p m i q)) ≠ ∞ := by
  have hgeom : Summable (fun q : ℕ => (1 / 2 : ℝ) ^ q) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hsummable : Summable (fun q : ℕ => 3 * Real.sqrt 2 * (1 / 2 : ℝ) ^ q) :=
    hgeom.mul_left (3 * Real.sqrt 2)
  have hnn : ∀ q : ℕ, 0 ≤ 3 * Real.sqrt 2 * (1 / 2 : ℝ) ^ q := fun q => by positivity
  have hle : (∑' q : ℕ, arrayMeasure N (badSet p m i q)) ≤
      ENNReal.ofReal (∑' q : ℕ, 3 * Real.sqrt 2 * (1 / 2 : ℝ) ^ q) := by
    refine (ENNReal.tsum_le_tsum fun q => measure_badSet_le p m i q).trans_eq ?_
    exact (ENNReal.ofReal_tsum_of_nonneg hnn hsummable).symm
  exact ne_of_lt (lt_of_le_of_lt hle ENNReal.ofReal_lt_top)

/-! ### Borel--Cantelli on the geometric subsequence -/

/-- Almost surely, at the geometric stages `q`, the running maximum up to time `2^(4q)`
reaches `2^q`. -/
theorem ae_eventually_badSet_compl (p : ℝ) (m : ℕ) (i : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ᶠ q in atTop,
      ∃ k ≤ 2 ^ (4 * q), ((2 ^ q : ℕ) : ℤ) ≤ symmetricWalk p m U i k := by
  have hae := MeasureTheory.ae_eventually_notMem (tsum_badSet_ne_top (N := N) p m i)
  filter_upwards [hae] with U hU
  filter_upwards [hU] with q hq
  simp only [badSet, Set.mem_ofPred_eq] at hq
  push Not at hq
  exact hq

/-! ### Interpolation to every large time -/

/-- **Almost-sure growth of the running maximum of the actual auxiliary walk.**
For almost every array, eventually every time `n` has a `k ≤ n` at which the walk is at
least `2 ^ (n.log2 / 4)` (which is within a factor two of `n ^ (1/4)`). -/
theorem ae_eventually_exists_ge_log2 (p : ℝ) (m : ℕ) (i : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ᶠ n in atTop,
      ∃ k ≤ n, ((2 ^ (Nat.log2 n / 4) : ℕ) : ℤ) ≤ symmetricWalk p m U i k := by
  filter_upwards [MeasureTheory.ae_eventually_notMem (tsum_badSet_ne_top (N := N) p m i)]
    with U hU
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.1 hU
  filter_upwards [Filter.eventually_ge_atTop (2 ^ (4 * q₀))] with n hn
  have hn0 : n ≠ 0 := by
    have h1 : 1 ≤ 2 ^ (4 * q₀) := Nat.one_le_two_pow
    omega
  have hlog : 4 * q₀ ≤ Nat.log2 n := (Nat.le_log2 hn0).2 hn
  have hq_ge : q₀ ≤ Nat.log2 n / 4 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
  have hnot : U ∉ badSet p m i (Nat.log2 n / 4) := hq₀ _ hq_ge
  have h4q : 2 ^ (4 * (Nat.log2 n / 4)) ≤ n := by
    apply (Nat.le_log2 hn0).1
    have h := Nat.div_mul_le_self (Nat.log2 n) 4
    omega
  simp only [badSet, Set.mem_ofPred_eq] at hnot
  push Not at hnot
  obtain ⟨k, hk1, hk2⟩ := hnot
  exact ⟨k, hk1.trans h4q, hk2⟩

/-- **The running maximum of the actual auxiliary walk is unbounded above almost surely**,
at every level, for every walker and every pair of parameters. -/
theorem ae_eventually_exists_ge (p : ℝ) (m : ℕ) (i : Fin N) (b : ℕ) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ᶠ n in atTop,
      ∃ k ≤ n, (b : ℤ) ≤ symmetricWalk p m U i k := by
  filter_upwards [ae_eventually_exists_ge_log2 (N := N) p m i] with U hU
  filter_upwards [hU, Filter.eventually_ge_atTop (2 ^ (4 * b))] with n hU hn
  obtain ⟨k, hk, hbk⟩ := hU
  refine ⟨k, hk, ?_⟩
  have hn0 : n ≠ 0 := by
    have h1 : 1 ≤ 2 ^ (4 * b) := Nat.one_le_two_pow
    omega
  have hlog : 4 * b ≤ Nat.log2 n := (Nat.le_log2 hn0).2 hn
  have hb_le : b ≤ Nat.log2 n / 4 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
  have hmono : 2 ^ b ≤ 2 ^ (Nat.log2 n / 4) := Nat.pow_le_pow_right (by norm_num) hb_le
  have hbb : b ≤ 2 ^ b := le_of_lt Nat.lt_two_pow_self
  exact (Nat.cast_le.2 (le_trans hbb hmono)).trans hbk

/-! ### The running maximum as a function -/

/-- The running maximum of the auxiliary walk up to time `n`. -/
noncomputable def runMax (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (n : ℕ) : ℤ :=
  ((Finset.range (n + 1)).image (fun k => symmetricWalk p m U i k)).max'
    ⟨symmetricWalk p m U i 0,
      Finset.mem_image.2 ⟨0, Finset.mem_range.2 (Nat.succ_pos n), rfl⟩⟩

/-- The running maximum dominates every earlier value. -/
lemma le_runMax (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) {n k : ℕ} (hk : k ≤ n) :
    symmetricWalk p m U i k ≤ runMax p m U i n :=
  Finset.le_max' _ _ (Finset.mem_image.2 ⟨k, Finset.mem_range.2 (Nat.lt_succ_iff.2 hk), rfl⟩)

/-- Every level is almost surely eventually exceeded by the auxiliary walk. -/theorem ae_forall_eventually_exists_ge (p : ℝ) (m : ℕ) (i : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ b : ℕ, ∀ᶠ n in atTop,
      ∃ k ≤ n, (b : ℤ) ≤ symmetricWalk p m U i k :=
  eventually_countable_forall.2 fun b => ae_eventually_exists_ge p m i b

/-- **The running maximum of the actual auxiliary walk tends to `+∞` almost surely.** -/
theorem ae_tendsto_runMax (p : ℝ) (m : ℕ) (i : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N), Tendsto (fun n => runMax p m U i n) atTop atTop := by
  filter_upwards [ae_forall_eventually_exists_ge (N := N) p m i] with U hU
  rw [tendsto_atTop_atTop]
  intro a
  rcases le_or_gt (0 : ℤ) a with ha | ha
  · obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hU a.toNat)
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨k, hk, hbk⟩ := hN n hn
    have hcast : a ≤ ((a.toNat : ℕ) : ℤ) := by omega
    exact (hcast.trans hbk).trans (le_runMax p m U i hk)
  · obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hU 0)
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨k, hk, hbk⟩ := hN n hn
    exact (le_of_lt ha).trans (hbk.trans (le_runMax p m U i hk))

/-- **Transfer to the actual interacting trajectory.**  For `p ≥ 1/2` the interacting
position dominates the auxiliary walk, so its running maximum is almost surely
unbounded above at every level. -/
theorem ae_eventually_trajectory_exists_ge {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ) (i : Fin N)
    (b : ℕ) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ᶠ n in atTop,
      ∃ k ≤ n, (b : ℤ) ≤ (trajectory p m U k).pos i := by
  filter_upwards [ae_eventually_exists_ge (N := N) p m i b] with U hU
  filter_upwards [hU] with n hn
  obtain ⟨k, hk, hbk⟩ := hn
  exact ⟨k, hk, hbk.trans (symmetricWalk_le_trajectory hp m U i k)⟩

/-- Every level is almost surely eventually exceeded by the interacting trajectory. -/
theorem ae_trajectory_forall_eventually_exists_ge {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ) (i : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ b : ℕ, ∀ᶠ n in atTop,
      ∃ k ≤ n, (b : ℤ) ≤ (trajectory p m U k).pos i :=
  eventually_countable_forall.2 fun b => ae_eventually_trajectory_exists_ge hp m i b

/-- **All walkers simultaneously**: almost every array has, for every walker `i` and every
level `b`, some time `k ≤ n` with `b ≤ S_k^i`, eventually in `n`. -/
theorem ae_forall_walkers_eventually_exists_ge (p : ℝ) (m : ℕ) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N, ∀ b : ℕ, ∀ᶠ n in atTop,
      ∃ k ≤ n, (b : ℤ) ≤ symmetricWalk p m U i k :=
  eventually_all.2 fun i => ae_forall_eventually_exists_ge p m i

/-- **All walkers simultaneously**: the running maxima of all walkers diverge. -/
theorem ae_forall_walkers_tendsto_runMax (p : ℝ) (m : ℕ) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
      Tendsto (fun n => runMax p m U i n) atTop atTop :=
  eventually_all.2 fun i => ae_tendsto_runMax p m i

/-- **All walkers simultaneously, for the interacting trajectory** (`p ≥ 1/2`): almost
every array has every trajectory's running maximum exceeding every level. -/
theorem ae_forall_walkers_trajectory_exists_ge {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N, ∀ b : ℕ, ∀ᶠ n in atTop,
      ∃ k ≤ n, (b : ℤ) ≤ (trajectory p m U k).pos i :=
  eventually_all.2 fun i => ae_trajectory_forall_eventually_exists_ge hp m i

end Swarming.SymmAeMax


