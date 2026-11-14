/-
# the `topDefect` residual of the integrated `QplWindow` bound

The integrated source `QplWindow.qpl_measure_max_abs_le_of_top_scale` proves

  `μ.real {∃ k ≤ T*L, L^{3/4} ≤ |Qpl_k|}`
  `  ≤ 2 (T L + 1) exp (-V^8/(4 T (KepW (V+2))^2))`
  `    + μ.real (topDefect p m i j M (T*L)) + exp (-c V)`,   `V = xOf L = L^{1/16}`,

and leaves the geometric residual `topDefect` uncharged:

  `topDefect p m i j M K`
  `  = {∃ k < K, 1 + M ≤ (M_k^j).toNat} ∪ {∃ k < K, 1 + M < (X_k^i).toNat + 2}`,

i.e. the running record of walker `j` reaches the top `1+M` of the origin-anchored window, or
walker `i` reaches level `M`, within `K` steps.

This file charges it with two *actual* estimates, and states exactly where each applies:

* **Spatial (deterministic).**  A walker that started at the origin and makes nearest-neighbour
  steps is at site `≤ k` at time `k`, and the record `M_k^j = sup_{t≤k} X_t^j` likewise.  Hence
  for `M ≥ K` both branches of `topDefect` are impossible: `topDefect p m i j M K = ∅` and its
  measure is *exactly* `0` (`topDefect_eq_empty_of_le`, `measure_topDefect_eq_zero`).  At the
  paper window `M = T*L` this removes the residual from
  `qpl_measure_max_abs_le_of_top_scale` entirely (`qpl_measure_max_abs_le_of_top_scale_killed`).

* **Running-maximum / hitting (probabilistic).**  For `M > (2p-1) K` the same event is an
  upcrossing of level `M` by the running maximum of a nearest-neighbour walk with conditional
  increment in `[-(1-2p), 1]`; the drift martingale `M^i_n = X^i_n - (2p-1) #{t < n : excited}`
  of the model converts it into a deviation of a martingale with increments bounded by `2`, and
  the maximal Azuma–Hoeffding estimate gives

    `μ.real (topDefect p m i j M K) ≤ 4 (K+1) exp (-(M - (2p-1)K)^2 / (16 K))`

  (`measure_topDefect_le`).  The exponent is *quadratic in the excess over the drift level*;
  with `M = c L`, `K = T L` it equals `L (c - (2p-1)T)^2 / (16 T)`, i.e. it is **exponential in
  `L`**, with only a polynomial prefactor `4 (T L + 1)` from the union bound over the horizon.

* **The threshold is real.**  For `M = 1` the event already has probability `≥ 1/2`
  (`half_le_measure_topDefect_one`), so no bound uniform in `M` can hold; the exponential regime
  `M > (2p-1)K` above is the correct one.

* **The rate is exponential in both directions.**  The residual contains the event that walker `i`
  steps right at every one of its first `M` steps, whose probability is at least `2^{-M}`
  (`pow_half_le_measure_topDefect`), so `2^{-M} ≤ μ.real (topDefect p m i j M K)` and the decay in
  `M` is exponential, never faster (`measure_topDefect_sandwich`).  At the paper scale
  `M = c L`, `K = T L` the probability is `e^{-Θ(L)}`.

Everything here is about the *integrated* `QplWindow` objects; no `sorry`, no custom axiom, no
`native_decide`, and no use of `(locgroup)`, `(locmove)`, tightness or `MainClaim`.
-/
import Swarm.QplWindow
import Swarm.LocMartConcrete

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

namespace QplWindow

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl SwarmMarks SwarmLogRatio LocSumAct QplPredEnv

variable {N : ℕ}

/-! ### 1. Spatial bounds: a walker is at site at most its own time -/

/-- A nearest-neighbour walk started at the origin is at site at most `t` at time `t`, so its
nonnegative part is at most `t`. -/
theorem toNat_pos_le_time (p : ℝ) (m : ℕ) (U : Array N) (k : ℕ) (i : Fin N) :
    ((trajectory p m U k).pos i).toNat ≤ k := by
  have h := pos_le_time p m U k i
  have h' := Int.toNat_le_toNat h
  simpa using h'

/-- The running record read from the prefix is at most its time: `M_k^j ≤ k`. -/
theorem toNat_recVal_le_time (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (k : ℕ) :
    (recVal j (prefOf p m k U)).toNat ≤ k :=
  toNat_recVal_prefOf_le p m U j k

/-- **Reaching the top of the window is reaching a site.**  If the record at time `k` is at least
`1 + M`, then some position of walker `j` at a time `t ≤ k` is at least `1 + M`: the record is a
running maximum, not a new variable. -/
theorem exists_pos_ge_of_recVal_toNat_ge {p : ℝ} {m : ℕ} {U : Array N} {j : Fin N} {k M : ℕ}
    (h : 1 + M ≤ (recVal j (prefOf p m k U)).toNat) :
    ∃ t ≤ k, (M : ℤ) + 1 ≤ (trajectory p m U t).pos j := by
  have hz : 0 ≤ recVal j (prefOf p m k U) := zero_le_recVal_prefOf p m U j k
  have hge : ((1 + M : ℕ) : ℤ) ≤ recVal j (prefOf p m k U) := (Int.le_toNat hz).mp h
  obtain ⟨t, ht, heq⟩ := Swarming.Trajectory.exists_eq_runMax p m U j k
  rw [runMax_eq_recVal] at heq
  refine ⟨t, ht, ?_⟩
  rw [heq]
  push_cast at hge
  linarith

/-- Hitting level `M` as a natural number means being at site `≥ M`: the position is
nonnegative there because `1 ≤ M`. -/
theorem pos_ge_of_toNat_ge {a : ℤ} {M : ℕ} (hM : 1 ≤ M) (h : M ≤ a.toNat) : (M : ℤ) ≤ a := by
  have h0 : 0 ≤ a := by
    by_contra hneg
    rw [Int.toNat_of_nonpos (by omega : a ≤ 0)] at h
    omega
  exact (Int.le_toNat h0).mp h

/-! ### 2. The spatial case: above the time horizon `topDefect` is empty -/

/-- **Spatial emptiness.**  If the window top `1 + M` is above `K + 1`, then within `K` steps no
nearest-neighbour walk from the origin can reach it and the record cannot either: `topDefect` is
the empty set.  No probability is used. -/
theorem topDefect_eq_empty_of_le {p : ℝ} {m : ℕ} {i j : Fin N} {M K : ℕ} (hK : K ≤ M) :
    topDefect p m i j M K = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  intro U hU
  simp only [topDefect, Set.mem_ofPred_eq] at hU
  rcases hU with ⟨k, hkK, hle⟩ | ⟨k, hkK, hlt⟩
  · have h1 : (recVal j (prefOf p m k U)).toNat ≤ k := toNat_recVal_le_time p m U j k
    omega
  · have h1 : ((trajectory p m U k).pos i).toNat ≤ k := toNat_pos_le_time p m U k i
    omega

/-- The spatial bound in measure form: the residual `topDefect` is *exactly* negligible above the
horizon. -/
theorem measure_topDefect_eq_zero {p : ℝ} {m : ℕ} {i j : Fin N} {M K : ℕ} (hK : K ≤ M) :
    (arrayMeasure N).real (topDefect p m i j M K) = 0 := by
  rw [topDefect_eq_empty_of_le hK, Measure.real_def, measure_empty, ENNReal.toReal_zero]


/-! ### 3. The hitting case: reduction to the drift martingale `M^i_n = X^i_n - (2p-1) #excited` -/

section General

variable {Ω : Type*} [m0 : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration ℕ m0} {X : ℕ → Ω → Fin N → ℤ} {m : ℕ} {p : ℝ}

/-- **The maximal Azuma–Hoeffding bound for the drift martingale at an arbitrary level and
horizon.**  For `p ∈ [1/2,1]` the drift martingale of the model has increments bounded by `2`,
so the maximal two-sided deviation over any horizon `n ≥ 1` is at most
`2 (n+1) exp (-ε^2 / (16 n))`.  This is `LocMart.measure_max_abs_psum_ge_le` (the union bound
over the horizon) applied to the verified martingale `SwarmHosc.mart_martingale`; only the level
`ε` and the horizon `n` are generalised compared with `LocMart.measure_max_abs_mart_of_interactingLaw`. -/
theorem measure_max_abs_mart_le (hlaw : Swarm.IsInteractingLaw ℱ μ X m p)
    (hp0 : 1 / 2 ≤ p) (hp1 : p ≤ 1) (i : Fin N) {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ∃ k ≤ n, ε ≤ |Swarm.mart p X m k ω i|}
      ≤ 2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (16 * (n : ℝ))) := by
  have hQ : Martingale (fun k ω => Swarm.mart p X m k ω i) ℱ μ :=
    SwarmHosc.mart_martingale hlaw i
  have hbdd : ∀ k ω, |MartingaleLimit.inc (fun k ω => Swarm.mart p X m k ω i) k ω| ≤ 2 :=
    fun k ω => SwarmHosc.abs_mart_inc_le hlaw hp0 hp1 k i ω
  have hmeas : ∀ k, StronglyMeasurable[ℱ (k + 1)]
      (MartingaleLimit.inc (fun k ω => Swarm.mart p X m k ω i) k) := by
    intro k
    exact (hQ.stronglyAdapted (k + 1)).sub
      ((hQ.stronglyAdapted k).mono (ℱ.mono (Nat.le_succ k)))
  have hmean : ∀ k, μ[MartingaleLimit.inc (fun k ω => Swarm.mart p X m k ω i) k | ℱ k]
      =ᵐ[μ] 0 := fun k => MartingaleLimit.condExp_inc_eq_zero hQ k
  have hmain := LocMart.measure_max_abs_psum_ge_le (μ := μ) (ℱ := ℱ)
    (ξ := MartingaleLimit.inc (fun k ω => Swarm.mart p X m k ω i)) (C := 2) (n := n) (ε := ε)
    hmeas (by norm_num) hbdd hmean hn hε
  have heq : {ω | ∃ k ≤ n, ε ≤ |LocMart.psum
        (MartingaleLimit.inc (fun k ω => Swarm.mart p X m k ω i)) k ω|}
      = {ω | ∃ k ≤ n, ε ≤ |Swarm.mart p X m k ω i|} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    congr! 3 with k hk
    rw [show LocMart.psum (MartingaleLimit.inc (fun k ω => Swarm.mart p X m k ω i)) k ω
        = Swarm.mart p X m k ω i - Swarm.mart p X m 0 ω i from
        MartingaleLimit.sum_inc (fun k ω => Swarm.mart p X m k ω i) k ω,
      SwarmHosc.mart_zero hlaw i ω, sub_zero]
  rw [heq] at hmain
  have hden : (4 : ℝ) * (n : ℝ) * 2 ^ 2 = 16 * (n : ℝ) := by ring
  rw [hden] at hmain
  exact hmain

end General

/-! ### 4. The concrete model: the drift martingale of the array measure -/

/-- The maximal deviation bound for the drift martingale of the actual uniform-array
trajectory, at an arbitrary level and horizon. -/
theorem trajectory_measure_max_abs_mart_le {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (i : Fin N) {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    (arrayMeasure N).real {U | ∃ k ≤ n, ε ≤
      |Swarm.mart p (fun t (U : Array N) => (trajectory p m U t).pos) m k U i|}
      ≤ 2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (16 * (n : ℝ))) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  exact measure_max_abs_mart_le (SwarmCross.Actual.actual_isInteractingLaw hp0 hp1 m)
    hp0.le hp1.le i hn hε

/-- **From a site to the drift martingale.**  If walker `i` is at a site `≥ A` at time `k`, then
its drift martingale at time `k` is at least `A - (2p-1) k`: the excitation counter is at most
the number of elapsed steps and the drift `2p-1` is at most one. -/
theorem mart_ge_of_pos_ge {p : ℝ} (hp : 1 / 2 ≤ p) {m : ℕ} {U : Array N} {i : Fin N}
    {k A : ℕ} (h : (A : ℤ) ≤ (trajectory p m U k).pos i) :
    (A : ℝ) - (2 * p - 1) * (k : ℝ) ≤
      Swarm.mart p (fun t (U : Array N) => (trajectory p m U t).pos) m k U i := by
  have hexc : (Swarm.excCount (fun t (U : Array N) => (trajectory p m U t).pos) m k U i : ℝ)
      ≤ (k : ℝ) := by
    have h := SwarmHosc.excCount_le
      (X := fun t (U : Array N) => (trajectory p m U t).pos) (m := m) k U i
    exact_mod_cast h
  have hpos : (A : ℝ) ≤ ((trajectory p m U k).pos i : ℝ) := by exact_mod_cast h
  have hmu : (0 : ℝ) ≤ 2 * p - 1 := by linarith
  have hmul : (2 * p - 1) * (Swarm.excCount
      (fun t (U : Array N) => (trajectory p m U t).pos) m k U i : ℝ)
      ≤ (2 * p - 1) * (k : ℝ) := by
    exact mul_le_mul_of_nonneg_left hexc hmu
  simp only [Swarm.mart, Swarm.pos]
  linarith

/-- **The residual is covered by two running-maximum events.**  Both branches of `topDefect` are
upcrossings of a level by the running maximum of a single nearest-neighbour walk; here they are
reduced to deviations `≥ M - (2p-1)K` of the two drift martingales.  Nothing about the
environment enters: this is the spatial/running-maximum content. -/
theorem topDefect_subset_mart {p : ℝ} (hp : 1 / 2 ≤ p) {m : ℕ} {i j : Fin N} {M K : ℕ}
    (hM : 1 ≤ M) :
    topDefect p m i j M K ⊆
      ({U | ∃ k ≤ K, (M : ℝ) - (2 * p - 1) * (K : ℝ) ≤
        |Swarm.mart p (fun t (U : Array N) => (trajectory p m U t).pos) m k U i|}) ∪
      ({U | ∃ k ≤ K, (M : ℝ) - (2 * p - 1) * (K : ℝ) ≤
        |Swarm.mart p (fun t (U : Array N) => (trajectory p m U t).pos) m k U j|}) := by
  intro U hU
  simp only [topDefect, Set.mem_ofPred_eq, Set.mem_union] at hU ⊢
  have hmu : (0 : ℝ) ≤ 2 * p - 1 := by linarith
  rcases hU with ⟨k, hk, hle⟩ | ⟨k, hk, hlt⟩
  · -- walker `j`'s record reaches `1+M`, hence so does a position at some time `t ≤ k`
    obtain ⟨t, htk, hpos⟩ := exists_pos_ge_of_recVal_toNat_ge hle
    right
    refine ⟨t, le_trans htk (le_of_lt hk), ?_⟩
    have hm := mart_ge_of_pos_ge hp (k := t) (A := M + 1) hpos
    have htK : (t : ℝ) ≤ (K : ℝ) := by exact_mod_cast le_trans htk (le_of_lt hk)
    have hlow : (M : ℝ) - (2 * p - 1) * (K : ℝ) ≤
        Swarm.mart p (fun t (U : Array N) => (trajectory p m U t).pos) m t U j := by
      have hMK : (2 * p - 1) * (t : ℝ) ≤ (2 * p - 1) * (K : ℝ) :=
        mul_le_mul_of_nonneg_left htK hmu
      have : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
      linarith
    have habs : Swarm.mart p (fun t (U : Array N) => (trajectory p m U t).pos) m t U j
        ≤ |Swarm.mart p (fun t (U : Array N) => (trajectory p m U t).pos) m t U j| :=
      le_abs_self _
    linarith
  · -- walker `i`'s position reaches `M`
    left
    have hMt : M ≤ ((trajectory p m U k).pos i).toNat := by omega
    have hpos : (M : ℤ) ≤ (trajectory p m U k).pos i := pos_ge_of_toNat_ge hM hMt
    refine ⟨k, le_of_lt hk, ?_⟩
    have hm := mart_ge_of_pos_ge hp (k := k) (A := M) hpos
    have hkK : (k : ℝ) ≤ (K : ℝ) := by exact_mod_cast le_of_lt hk
    have hlow : (M : ℝ) - (2 * p - 1) * (K : ℝ) ≤
        Swarm.mart p (fun t (U : Array N) => (trajectory p m U t).pos) m k U i := by
      have hMK : (2 * p - 1) * (k : ℝ) ≤ (2 * p - 1) * (K : ℝ) :=
        mul_le_mul_of_nonneg_left hkK hmu
      linarith
    have habs : Swarm.mart p (fun t (U : Array N) => (trajectory p m U t).pos) m k U i
        ≤ |Swarm.mart p (fun t (U : Array N) => (trajectory p m U t).pos) m k U i| :=
      le_abs_self _
    linarith


/-! ### 5. The hitting bound for the residual `topDefect` -/

/-- **The residual is at most `4 (K+1) exp (-(M - (2p-1)K)^2 / (16 K))`.**  Both branches of
`topDefect` are running-maximum upcrossings; `topDefect_subset_mart` turns each into a deviation
of the drift martingale, and the maximal Azuma–Hoeffding bound `trajectory_measure_max_abs_mart_le`
charges them at the level `ε = M - (2p-1)K > 0`.

This is the non-vacuous probabilistic bound: the exponent is the squared *excess of the window top
over the maximal ballistic level*, divided by `16 K`.  Only the polynomial prefactor `4 (K+1)` is
lost, to the union bound over the horizon. -/
theorem measure_topDefect_le {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) (i j : Fin N)
    {M K : ℕ} (hM : 1 ≤ M) (hK : 1 ≤ K) (hbig : (2 * p - 1) * (K : ℝ) < (M : ℝ)) :
    (arrayMeasure N).real (topDefect p m i j M K) ≤
      4 * ((K : ℝ) + 1) *
        Real.exp (-(((M : ℝ) - (2 * p - 1) * (K : ℝ)) ^ 2) / (16 * (K : ℝ))) := by
  have hε : 0 < (M : ℝ) - (2 * p - 1) * (K : ℝ) := by linarith
  have hsub := topDefect_subset_mart (N := N) (m := m) (i := i) (j := j) (M := M) (K := K)
    hp0.le hM
  have hmono : (arrayMeasure N).real (topDefect p m i j M K)
      ≤ (arrayMeasure N).real
          ({U | ∃ k ≤ K, (M : ℝ) - (2 * p - 1) * (K : ℝ) ≤
            |Swarm.mart p (fun t (U : Array N) => (trajectory p m U t).pos) m k U i|} ∪
           {U | ∃ k ≤ K, (M : ℝ) - (2 * p - 1) * (K : ℝ) ≤
            |Swarm.mart p (fun t (U : Array N) => (trajectory p m U t).pos) m k U j|}) :=
    measureReal_mono hsub (measure_ne_top _ _)
  refine le_trans hmono (le_trans (measureReal_union_le _ _) ?_)
  have h1 := trajectory_measure_max_abs_mart_le (N := N) hp0 hp1 m i (n := K)
    (ε := (M : ℝ) - (2 * p - 1) * (K : ℝ)) hK hε
  have h2 := trajectory_measure_max_abs_mart_le (N := N) hp0 hp1 m j (n := K)
    (ε := (M : ℝ) - (2 * p - 1) * (K : ℝ)) hK hε
  linarith [h1, h2]

/-- **Rate form with the excess `Δ` explicit.**  Writing the window top as
`M = (2p-1)K + Δ` (i.e. `Δ` above the maximal ballistic level) the residual satisfies

  `μ.real (topDefect p m i j M K) ≤ 4 (K+1) exp (-Δ^2/(16 K))`.

So the bound is exponential in `K` exactly while `Δ^2/K → ∞`: with `M = c L`, `K = T L` it is
`4 (T L + 1) exp (-L (c - (2p-1)T)^2 / (16 T))`, i.e. exponential in `L` with an explicit
constant.  Only the prefactor `4 (T L + 1)` is polynomial. -/
theorem measure_topDefect_le_delta {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ)
    (i j : Fin N) {M K : ℕ} (hM : 1 ≤ M) (hK : 1 ≤ K) {Δ : ℝ} (hΔ : 0 < Δ)
    (hsplit : (M : ℝ) = (2 * p - 1) * (K : ℝ) + Δ) :
    (arrayMeasure N).real (topDefect p m i j M K) ≤
      4 * ((K : ℝ) + 1) * Real.exp (-(Δ ^ 2) / (16 * (K : ℝ))) := by
  have hbig : (2 * p - 1) * (K : ℝ) < (M : ℝ) := by rw [hsplit]; linarith
  have h := measure_topDefect_le (N := N) hp0 hp1 m i j hM hK hbig
  have hsub : (M : ℝ) - (2 * p - 1) * (K : ℝ) = Δ := by rw [hsplit]; ring
  rwa [hsub] at h

/-- Absorption of a polynomial prefactor into an exponential rate: if
`log a + c ≤ γ` then `a * exp (-γ) ≤ exp (-c)`. -/
theorem mul_exp_neg_le_exp_neg {a γ c : ℝ} (ha : 0 < a) (h : Real.log a + c ≤ γ) :
    a * Real.exp (-γ) ≤ Real.exp (-c) := by
  have hpos : (0 : ℝ) < a * Real.exp (-γ) := mul_pos ha (Real.exp_pos _)
  rw [← Real.log_le_iff_le_exp hpos]
  rw [Real.log_mul (ne_of_gt ha) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
  linarith

/-- **Absorbing the polynomial prefactor.**  If the exponent dominates `log (4 (K+1)) + c`, the
residual is at most `exp (-c)`: the polynomial prefactor costs nothing but a logarithmic shift of
the rate. -/
theorem measure_topDefect_le_exp {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) (i j : Fin N)
    {M K : ℕ} (hM : 1 ≤ M) (hK : 1 ≤ K) (hbig : (2 * p - 1) * (K : ℝ) < (M : ℝ)) {c : ℝ}
    (hlog : Real.log (4 * ((K : ℝ) + 1)) + c
      ≤ ((M : ℝ) - (2 * p - 1) * (K : ℝ)) ^ 2 / (16 * (K : ℝ))) :
    (arrayMeasure N).real (topDefect p m i j M K) ≤ Real.exp (-c) := by
  have ha : (0 : ℝ) < 4 * ((K : ℝ) + 1) := by positivity
  have hgoal : 4 * ((K : ℝ) + 1) *
      Real.exp (-(((M : ℝ) - (2 * p - 1) * (K : ℝ)) ^ 2) / (16 * (K : ℝ))) ≤ Real.exp (-c) := by
    convert mul_exp_neg_le_exp_neg ha hlog using 2
    rw [neg_div]
  exact le_trans (measure_topDefect_le (N := N) hp0 hp1 m i j hM hK hbig) hgoal

/-! ### 6. The threshold is real: at `M = 1` the residual is not small

The exponential bound needs `M > (2p-1)K`.  That restriction is not an artefact: at `M = 1` the
event already contains the first rightward step of walker `i`, which has probability `≥ 1/2`. -/

/-- **`topDefect` at `M = 1` has probability at least `1/2`.**  For `K ≥ 2` the event contains
the set `{X_1^i = 1}`, and the model's jump rule gives that set probability
`1/2 + (p-1/2) μ.real{excited} ≥ 1/2`.  Hence no bound uniform in `M` can hold, and the
exponential regime `M > (2p-1)K` of `measure_topDefect_le` is the right one. -/
theorem half_le_measure_topDefect_one {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ}
    (i j : Fin N) {K : ℕ} (hK : 2 ≤ K) :
    (1 / 2 : ℝ) ≤ (arrayMeasure N).real (topDefect p m i j 1 K) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hsub : Swarm.upSet (fun t (U : Array N) => (trajectory p m U t).pos) 0 i
      ⊆ topDefect p m i j 1 K := by
    intro U hU
    have h0 : (trajectory p m U 0).pos i = 0 := pos_zero p m U i
    have h1 : (trajectory p m U 1).pos i = 1 := by
      have := hU
      simp only [Swarm.upSet, Set.mem_ofPred_eq] at this
      rw [h0] at this
      simpa using this
    right
    refine ⟨1, by omega, ?_⟩
    rw [h1]
    norm_num
  have hmono := measureReal_mono hsub (measure_ne_top (arrayMeasure N) (topDefect p m i j 1 K))
  have hrule := SwarmCross.Actual.measureReal_inter_upSet (N := N) hp0 hp1 m 0 i
    (A := Set.univ) MeasurableSet.univ
  simp only [Set.univ_inter] at hrule
  have hμ : (arrayMeasure N).real (Set.univ : Set (Array N)) = 1 := by
    rw [Measure.real_def, measure_univ]; simp
  rw [hμ] at hrule
  have hnonneg : 0 ≤ (p - 1 / 2) * (arrayMeasure N).real
      (Swarm.excitedSet (fun t (U : Array N) => (trajectory p m U t).pos) m 0 i) := by
    have h1 : (0 : ℝ) ≤ p - 1 / 2 := by linarith
    have h2 : (0 : ℝ) ≤ (arrayMeasure N).real
        (Swarm.excitedSet (fun t (U : Array N) => (trajectory p m U t).pos) m 0 i) :=
      measureReal_nonneg
    exact mul_nonneg h1 h2
  have hup : (1 / 2 : ℝ) ≤ (arrayMeasure N).real
      (Swarm.upSet (fun t (U : Array N) => (trajectory p m U t).pos) 0 i) := by
    rw [hrule]
    linarith [hnonneg]
  linarith [hup, hmono]


/-! ### 7. Composition with the integrated source -/

/-- **The paper-scale `Qpl` maximal bound with the geometric residual removed.**  The integrated
`QplWindow.qpl_measure_max_abs_le_of_top_scale` charges everything except
`μ.real (topDefect p m i j M (T*L))`, with `M` free in `1 ≤ M`, `1 + M ≤ 2 (T+3) L`.  Choosing
the window top at the *time horizon*, `M = T*L`, the spatial bound
`measure_topDefect_eq_zero` makes that term `0`, so the maximal bound holds with only the two
explicit exponential terms:

  `μ.real {∃ k ≤ T*L, L^{3/4} ≤ |Qpl_k|}`
  `  ≤ 2 (T L + 1) exp (-V^8/(4 T (KepW (V+2))^2)) + exp (-c V)`,   `V = xOf L = L^{1/16}`.

No residual, no `(locgroup)`, `(locmove)`, tightness or `MainClaim`. -/
theorem qpl_measure_max_abs_le_of_top_scale_killed {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) {i j : Fin N} (hij : i ≠ j) {eps : ℝ} (hε : 0 < eps)
    {T : ℕ} (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀,
      (arrayMeasure N).real
          {U | ∃ k ≤ T * L, (L : ℝ) ^ (3 / 4 : ℝ) ≤ |ProjLedger.Qpl p m eps i j k U|}
        ≤ 2 * (((T * L : ℕ) : ℝ) + 1)
              * Real.exp (-((LocSumAct.xOf L) ^ 8 /
                  (4 * (T : ℝ) * (KepW p m * (LocSumAct.xOf L + 2)) ^ 2)))
          + Real.exp (-c * LocSumAct.xOf L) := by
  obtain ⟨c, hc, L₀, hL0⟩ := qpl_measure_max_abs_le_of_top_scale (N := N) hp0 hp1 hm hij hε hT
  refine ⟨c, hc, max L₀ 1, ?_⟩
  intro L hL
  have hL0' : L₀ ≤ L := le_trans (le_max_left _ _) hL
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  have hM1 : 1 ≤ T * L := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hMup : 1 + T * L ≤ 2 * (T + 3) * L := by
    have h2 : 2 * (T + 3) * L = 2 * (T * L) + 6 * L := by ring
    rw [h2]
    omega
  have hb := hL0 L hL0' (T * L) hM1 hMup
  have hzero : (arrayMeasure N).real (topDefect p m i j (T * L) (T * L)) = 0 :=
    measure_topDefect_eq_zero (p := p) (m := m) (i := i) (j := j) (M := T * L) (K := T * L)
      le_rfl
  linarith [hb, hzero]

/-- **The paper-scale `Qpl` maximal bound with the residual charged explicitly.**  For any window
top `M` above the maximal ballistic level `(2p-1) T L`, the residual is at most
`4 (T L + 1) exp (-(M - (2p-1)TL)^2/(16 T L))`.  Together with the deterministic case `M ≥ T L`
this covers the whole range of `M` that the source allows and the whole range in which the
residual can be non-empty. -/
theorem qpl_measure_max_abs_le_of_top_scale_hit {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) {i j : Fin N} (hij : i ≠ j) {eps : ℝ} (hε : 0 < eps)
    {T : ℕ} (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ M : ℕ, 1 ≤ M → 1 + M ≤ 2 * (T + 3) * L →
      (2 * p - 1) * ((T * L : ℕ) : ℝ) < (M : ℝ) →
      (arrayMeasure N).real
          {U | ∃ k ≤ T * L, (L : ℝ) ^ (3 / 4 : ℝ) ≤ |ProjLedger.Qpl p m eps i j k U|}
        ≤ 2 * (((T * L : ℕ) : ℝ) + 1)
              * Real.exp (-((LocSumAct.xOf L) ^ 8 /
                  (4 * (T : ℝ) * (KepW p m * (LocSumAct.xOf L + 2)) ^ 2)))
          + 4 * (((T * L : ℕ) : ℝ) + 1)
              * Real.exp (-(((M : ℝ) - (2 * p - 1) * ((T * L : ℕ) : ℝ)) ^ 2)
                  / (16 * ((T * L : ℕ) : ℝ)))
          + Real.exp (-c * LocSumAct.xOf L) := by
  obtain ⟨c, hc, L₀, hL0⟩ := qpl_measure_max_abs_le_of_top_scale (N := N) hp0 hp1 hm hij hε hT
  refine ⟨c, hc, max L₀ 1, ?_⟩
  intro L hL M hM hMup hbig
  have hL0' : L₀ ≤ L := le_trans (le_max_left _ _) hL
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  have hTL : 1 ≤ T * L := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hb := hL0 L hL0' M hM hMup
  have hhit := measure_topDefect_le (N := N) hp0 hp1 m i j (K := T * L) hM hTL hbig
  linarith [hb, hhit]

/-! ### 8. Rate accounting: the exponent is linear in the horizon -/

/-- **Rate with an explicit relative excess.**  If the window top exceeds the maximal ballistic
level `(2p-1)K` by a fraction `δ` of the horizon, the residual is at most
`4 (K+1) exp (-δ^2 K / 16)`.  At the paper scale `K = T L` this is
`4 (T L + 1) exp (-δ^2 T L / 16)`: **exponential in `L`**, with rate `δ^2 T/16` and only a
polynomial prefactor. -/
theorem measure_topDefect_le_rate {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ)
    (i j : Fin N) {M K : ℕ} (hM : 1 ≤ M) (hK : 1 ≤ K) {δ : ℝ} (hδ : 0 < δ)
    (hbig : (2 * p - 1) * (K : ℝ) + δ * (K : ℝ) ≤ (M : ℝ)) :
    (arrayMeasure N).real (topDefect p m i j M K) ≤
      4 * ((K : ℝ) + 1) * Real.exp (-(δ ^ 2 * (K : ℝ) / 16)) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hδK : (0 : ℝ) < δ * (K : ℝ) := mul_pos hδ hK0
  have hstrict : (2 * p - 1) * (K : ℝ) < (M : ℝ) := by linarith
  have h := measure_topDefect_le (N := N) hp0 hp1 m i j hM hK hstrict
  refine le_trans h ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Real.exp_le_exp.mpr ?_
  have hexc : δ * (K : ℝ) ≤ (M : ℝ) - (2 * p - 1) * (K : ℝ) := by linarith
  have hexc0 : 0 ≤ δ * (K : ℝ) := le_of_lt (mul_pos hδ hK0)
  have hsq : (δ * (K : ℝ)) ^ 2 ≤ ((M : ℝ) - (2 * p - 1) * (K : ℝ)) ^ 2 := by
    refine pow_le_pow_left₀ hexc0 hexc 2
  have hpos : δ ^ 2 * (K : ℝ) / 16
      ≤ ((M : ℝ) - (2 * p - 1) * (K : ℝ)) ^ 2 / (16 * (K : ℝ)) := by
    have hsplit : δ ^ 2 * (K : ℝ) / 16 = (δ * (K : ℝ)) ^ 2 / (16 * (K : ℝ)) := by
      field_simp
    rw [hsplit]
    exact div_le_div_of_nonneg_right hsq (by positivity)
  have hdiv : -(((M : ℝ) - (2 * p - 1) * (K : ℝ)) ^ 2) / (16 * (K : ℝ))
      ≤ -(δ ^ 2 * (K : ℝ) / 16) := by
    have h := neg_le_neg hpos
    rwa [← neg_div] at h
  exact hdiv

/-- **The paper-scale rate.**  With horizon `K = T L` and a window top of at least
`((2p-1) + δ) T L` — i.e. a relative excess `δ` above the maximal ballistic level — the residual
satisfies

  `μ.real (topDefect p m i j M (T L)) ≤ 4 (T L + 1) exp (-δ^2 T L / 16)`.

Since `δ^2 T L/16` is linear in `L`, this is an exponential-in-`L` bound with explicit constant
`δ^2 T/16`; the only non-exponential factor is `4 (T L + 1)`, which the union bound over the
horizon costs.  For `M ≥ T L` the same term is exactly `0` (`measure_topDefect_eq_zero`), so the
whole residual is removed at the window the source actually needs. -/
theorem measure_topDefect_paper_scale {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ)
    (i j : Fin N) {T L M : ℕ} (hT : 1 ≤ T) (hL : 1 ≤ L) (hM : 1 ≤ M) {δ : ℝ} (hδ : 0 < δ)
    (hsplit : ((2 * p - 1) + δ) * ((T : ℝ) * (L : ℝ)) ≤ (M : ℝ)) :
    (arrayMeasure N).real (topDefect p m i j M (T * L)) ≤
      4 * (((T * L : ℕ) : ℝ) + 1) * Real.exp (-(δ ^ 2 * ((T * L : ℕ) : ℝ) / 16)) := by
  have hTL : 1 ≤ T * L := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hcast : ((T * L : ℕ) : ℝ) = (T : ℝ) * (L : ℝ) := by push_cast; ring
  refine measure_topDefect_le_rate (N := N) hp0 hp1 m i j hM hTL hδ ?_
  have h2 : (2 * p - 1) * ((T * L : ℕ) : ℝ) + δ * ((T * L : ℕ) : ℝ)
      = ((2 * p - 1) + δ) * ((T : ℝ) * (L : ℝ)) := by
    rw [hcast]; ring
  linarith [hsplit, h2]


/-! ### 9. A matching lower bound: the residual decays at most like `2^{-M}`

The upper bounds above are all of exponential type; this section shows that the residual really is
of that type, in the only direction that the model can certify unconditionally: the event contains
the probability that walker `i` steps right at every one of its first `M` steps.  Each such step
has conditional probability `1/2 + (p - 1/2) 1{excited} ≥ 1/2`, so the event has probability at
least `2^{-M}`.  Hence the true rate is exponential in `M` (at most `log 2` per site), never
faster, and the residual cannot be a `o(2^{-M})` quantity. -/

/-- The "all right" event: walker `i` steps right at every time `t < n`. -/
noncomputable def allRight (p : ℝ) (m : ℕ) (i : Fin N) (n : ℕ) : Set (Array N) :=
  ⋂ t ∈ Finset.range n,
    Swarm.upSet (fun s (U : Array N) => (trajectory p m U s).pos) t i

theorem allRight_zero (p : ℝ) (m : ℕ) (i : Fin N) : allRight p m i 0 = Set.univ := by
  simp [allRight]

theorem allRight_succ (p : ℝ) (m : ℕ) (i : Fin N) (n : ℕ) :
    allRight p m i (n + 1)
      = allRight p m i n ∩
        Swarm.upSet (fun s (U : Array N) => (trajectory p m U s).pos) n i := by
  ext U
  simp only [allRight, Set.mem_iInter, Finset.mem_range, Set.mem_inter_iff]
  constructor
  · intro h
    exact ⟨fun t ht => h t (by omega), h n (by omega)⟩
  · rintro ⟨h1, h2⟩ t ht
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with h | h
    · exact h1 t h
    · rw [h]; exact h2

theorem measurableSet_allRight (p : ℝ) (m : ℕ) (i : Fin N) (n : ℕ) :
    MeasurableSet[SwarmCross.pathMeas p m n] (allRight p m i n) := by
  refine Finset.measurableSet_biInter _ (fun t ht => ?_)
  have htn : t < n := Finset.mem_range.mp ht
  have hset : MeasurableSet[SwarmCross.pathMeas p m (t + 1)]
      (Swarm.upSet (fun s (U : Array N) => (trajectory p m U s).pos) t i) := by
    letI : MeasurableSpace (Array N) := SwarmCross.pathMeas p m (t + 1)
    have h1 : Measurable (fun U : Array N => (trajectory p m U (t + 1)).pos i) :=
      SwarmCross.pos_adapted p m i (t + 1)
    have h2 : Measurable (fun U : Array N => (trajectory p m U t).pos i) :=
      (SwarmCross.pos_adapted p m i t).mono
        (SwarmCross.pathMeas_mono (N := N) p m (Nat.le_succ t)) le_rfl
    exact measurableSet_eq_fun h1 (h2.add_const 1)
  exact (SwarmCross.pathMeas_mono (N := N) p m (by omega : t + 1 ≤ n)) _ hset

/-- **The all-right event has probability at least `2^{-n}`**: every step of the model is rightward
with conditional probability at least `1/2`, and the event is a chain of `n` such steps. -/
theorem pow_half_le_measure_allRight {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ)
    (i : Fin N) (n : ℕ) :
    (1 / 2 : ℝ) ^ n ≤ (arrayMeasure N).real (allRight p m i n) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  induction n with
  | zero =>
      rw [allRight_zero, Measure.real_def, measure_univ]
      simp
  | succ n ih =>
      rw [allRight_succ]
      have hlaw := SwarmCross.Actual.measureReal_inter_upSet (N := N) hp0 hp1 m n i
        (A := allRight p m i n) (measurableSet_allRight p m i n)
      have hnn : (0 : ℝ) ≤ (p - 1 / 2) * (arrayMeasure N).real
          (allRight p m i n ∩ Swarm.excitedSet
            (fun s (U : Array N) => (trajectory p m U s).pos) m n i) :=
        mul_nonneg (by linarith) measureReal_nonneg
      have hge : (1 / 2) * (arrayMeasure N).real (allRight p m i n)
          ≤ (arrayMeasure N).real (allRight p m i n ∩ Swarm.upSet
              (fun s (U : Array N) => (trajectory p m U s).pos) n i) := by
        rw [hlaw]; linarith
      have hpow : (1 / 2 : ℝ) ^ (n + 1) = (1 / 2) * (1 / 2) ^ n := by
        rw [pow_succ]; ring
      rw [hpow]
      exact le_trans (mul_le_mul_of_nonneg_left ih (by norm_num)) hge

/-- On the all-right event the walker sits at site `M` at time `M`, so the event is contained in
the branch of `topDefect` produced by walker `i`, as soon as `M < K`. -/
theorem allRight_subset_topDefect {p : ℝ} {m : ℕ} {i j : Fin N} {M K : ℕ} (hK : M + 1 ≤ K) :
    allRight p m i M ⊆ topDefect p m i j M K := by
  intro U hU
  have hall : ∀ t < M, (trajectory p m U (t + 1)).pos i
      = (trajectory p m U t).pos i + 1 := by
    intro t ht
    have hmem := Set.mem_iInter₂.mp hU t (Finset.mem_range.mpr ht)
    simpa only [Swarm.upSet, Set.mem_ofPred_eq] using hmem
  have hpos : ∀ n, n ≤ M → (trajectory p m U n).pos i = (n : ℤ) := by
    intro n
    induction n with
    | zero => intro _; exact pos_zero p m U i
    | succ k ih =>
        intro hk
        have hkM : k < M := by omega
        rw [hall k hkM, ih (by omega)]
        push_cast
        ring
  right
  refine ⟨M, by omega, ?_⟩
  rw [hpos M le_rfl, Int.toNat_natCast]
  omega

/-- **The matched lower bound: `μ.real (topDefect p m i j M K) ≥ 2^{-M}`.**  Together with
`measure_topDefect_le` this sandwiches the residual between two exponentials in `M`: it is never
smaller than `2^{-M}`, and it is at most `4 (K+1) exp (-(M - (2p-1)K)^2/(16 K))`.  In particular
the residual is *not* a `o(2^{-M})` quantity, and at the paper scale `M = c L`, `K = T L` its
decay in `L` is exponential (between `2^{-cL}` and `4(TL+1)e^{-L(c-(2p-1)T)^2/(16T)}`), never
polynomial and never super-exponential. -/
theorem pow_half_le_measure_topDefect {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ)
    (i j : Fin N) {M K : ℕ} (hK : M + 1 ≤ K) :
    (1 / 2 : ℝ) ^ M ≤ (arrayMeasure N).real (topDefect p m i j M K) := by
  refine le_trans (pow_half_le_measure_allRight hp0 hp1 m i M) ?_
  exact measureReal_mono (allRight_subset_topDefect (p := p) (m := m) (i := i) (j := j) hK)
    (measure_ne_top (arrayMeasure N) (topDefect p m i j M K))


/-- **The residual is exponential in `M` in both directions.**  For `M ≥ 1`, `1 ≤ K`, `M + 1 ≤ K`
and `M` above the maximal ballistic level `(2p-1)K`:

  `2^{-M} ≤ μ.real (topDefect p m i j M K) ≤ 4 (K+1) exp (-(M - (2p-1)K)^2/(16 K))`.

This is the exact rate assessment for the residual: it decays like an exponential in `M`, with the
upper exponent quadratic in the excess over the drift level and the lower bound `log 2` per site.
It is therefore neither polynomial nor super-exponential in `M`, and at the paper scale
`M = c L`, `K = T L` it is exponential in `L` in both directions. -/
theorem measure_topDefect_sandwich {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ)
    (i j : Fin N) {M K : ℕ} (hM : 1 ≤ M) (hK1 : 1 ≤ K) (hK : M + 1 ≤ K)
    (hbig : (2 * p - 1) * (K : ℝ) < (M : ℝ)) :
    ((1 / 2 : ℝ) ^ M ≤ (arrayMeasure N).real (topDefect p m i j M K)) ∧
      ((arrayMeasure N).real (topDefect p m i j M K) ≤
        4 * ((K : ℝ) + 1) *
          Real.exp (-(((M : ℝ) - (2 * p - 1) * (K : ℝ)) ^ 2) / (16 * (K : ℝ)))) :=
  ⟨pow_half_le_measure_topDefect hp0 hp1 m i j hK,
   measure_topDefect_le hp0 hp1 m i j hM hK1 hbig⟩

end QplWindow
