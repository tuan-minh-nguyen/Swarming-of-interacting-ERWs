/-
# `DiamAssembly.HdefA`: the actual array deficit is `o(t)` almost surely

This module closes the last stochastic residual of `DiamAssemblyMain.lean` that is *not*
`HcompA` and *not* the log-fourth variance estimate:

  `HdefA p m`  :  `∀ᵐ U, ∀ ε > 0, ∀ᶠ t, deficit (XA p m U) t ≤ ε t`
  where        `deficit X t = max_{j : Fin N} (M^j_t - X^j_t)`,
               `M^j_t = max_{0 ≤ s ≤ t} X^j_s`.

This is the paper's `(prelim)`, proved in the paper by two lines below `(mart)`:
`0 ≤ max_{t≤n}(M_t^i - X_t^i) ≤ 2 max_{t≤n}|𝓜_t^i| = o(n)`.  Both halves are already
available in the verified corpus:

* `SwarmHosc.trajectory_hosc` (area `martingale`, actual `arrayMeasure N`, unconditional for
  `1/2 < p < 1`) is exactly the single-walker statement `(M^i_n - X^i_n)/n → 0` a.s. for every
  `i` simultaneously; its proof goes through `SwarmHosc.hosc_of_law`, i.e. the paper's
  `(mart)` decomposition `X = 𝓜 + (2p-1)·(excitation count)` with the Hall–Heyde martingale
  strong law `MartingaleLimit.martingale_strong_law` and the running-maximum upgrade
  `MartingaleLimit.tendsto_running_max`;
* the array supremum in `deficit` is a supremum over the *fixed finite* index set `Fin N`, so it
  is a deterministic `Finset.sup'` transfer: the supremum of finitely many `o(t)` sequences is
  `o(t)`.  No union bound, no tail estimate, no Borel–Cantelli step, no probability input at all.

Contents:

* `walker_deficit_eventually_le` — deterministic single-coordinate bridge
  `(M_n - X_n)/n → 0 ⇒ eventually M_n - X_n ≤ ε n` (integer/real cast bookkeeping);
* `sup'_univ_cast_le` — the finite-sup transfer lemma;
* `hdefA_of_oscillation` — `HdefA` from the single-walker oscillation hypothesis (the exact
  shape of `trajectory_hosc`), with all other ingredients deterministic;
* `hdefA` — **`DiamAssembly.HdefA p m` unconditionally, for `1/2 < p < 1`, every `m`, every
  `N` with `Nonempty (Fin N)`**;
* `deficit_le_two_mart_max` and `hdefA_via_mart` — the paper's own `(mart)` route, an
  independent second proof that does not pass through `trajectory_hosc`: the pathwise inequality
  `max_{t≤n}(M_t - X_t) ≤ 2 max_{t≤n}|𝓜_t|` plus `SwarmHosc.ae_mart_max_div`.

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no Poissonisation.
-/
import Swarm.ActualHosc
import Swarm.DiamAssemblyMain

open Filter Finset MeasureTheory Topology
open scoped BigOperators

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup SepGroup.Model Cookie

namespace DiamAssemblyHdefA

variable {N : ℕ}

/-! ## 1. Deterministic bookkeeping: one coordinate

The oscillation hypothesis is about `(M_n - X_n)/n : ℝ`; `HdefA` needs the integer inequality
`M_n - X_n ≤ ε n`.  Since `M_n - X_n ≥ 0` and `n ≥ 1`, the two are equivalent. -/

/-- **Single-coordinate bridge.**  If the normalised oscillation of an integer sequence tends to
`0`, then eventually the (nonnegative) integer oscillation is at most `ε n`. -/
theorem walker_deficit_eventually_le {f : ℕ → ℤ}
    (h : Tendsto (fun n => ((SwarmSpeed.runMax f n : ℝ) - (f n : ℝ)) / (n : ℝ)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ((SwarmSpeed.runMax f n - f n : ℤ) : ℝ) ≤ ε * (n : ℝ) := by
  intro ε hε
  filter_upwards [h.eventually (Iio_mem_nhds hε), Filter.eventually_gt_atTop (0 : ℕ)]
    with n hn hn0
  have hn0' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hcast : ((SwarmSpeed.runMax f n - f n : ℤ) : ℝ)
      = (SwarmSpeed.runMax f n : ℝ) - (f n : ℝ) := by
    push_cast
    ring
  rw [hcast]
  have hkey : (SwarmSpeed.runMax f n : ℝ) - (f n : ℝ) < ε * (n : ℝ) := by
    have h' := (div_lt_iff₀ hn0').mp hn
    nlinarith [h', mul_comm (n : ℝ) ε]
  linarith

/-! ## 2. The finite-sup transfer

`deficit` is a `Finset.sup'` over `univ : Finset (Fin N)`, so a bound valid at every coordinate
transfers to the supremum by evaluating the supremum at its (attained) maximiser. -/

/-- **Finite-sup transfer.**  If every coordinate of `f : ι → ℤ` is at most the real constant `C`,
then so is the maximum of `f`. -/
theorem sup'_univ_cast_le {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℤ) {C : ℝ}
    (h : ∀ i, (f i : ℝ) ≤ C) :
    ((Finset.univ.sup' Finset.univ_nonempty f : ℤ) : ℝ) ≤ C := by
  obtain ⟨j, -, hj⟩ :=
    Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset ι)) Finset.univ_nonempty f
  rw [hj]
  exact h j

/-! ## 3. `HdefA` from the single-walker oscillation

The hypothesis `hosc` below is *literally* the conclusion of `SwarmHosc.trajectory_hosc`, but it
is stated separately so that the transfer is independent of how the oscillation was proved. -/

/-- **`HdefA` from the single-walker oscillation `(M^i_n - X^i_n)/n → 0` for all `i`.**

Everything except `hosc` here is deterministic. -/
theorem hdefA_of_oscillation {p : ℝ} {m : ℕ} [Nonempty (Fin N)]
    (hosc : ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N, Tendsto
      (fun n => ((SwarmSpeed.runMax
            (fun t => (Swarming.Trajectory.trajectory p m U t).pos i) n : ℝ)
          - (((Swarming.Trajectory.trajectory p m U n).pos i : ℤ) : ℝ)) / (n : ℝ))
      atTop (𝓝 0)) :
    @DiamAssembly.HdefA N p m _ := by
  filter_upwards [hosc] with U hU ε hε
  have hsingle : ∀ i : Fin N, ∀ᶠ t : ℕ in atTop,
      ((LeaderDescent.runMax (DiamAssembly.XA p m U) i t - DiamAssembly.XA p m U i t : ℤ) : ℝ) ≤ ε * (t : ℝ) := by
    intro i
    have h := walker_deficit_eventually_le
      (f := fun t => (Swarming.Trajectory.trajectory p m U t).pos i) (hU i) ε hε
    simpa only [DiamAssembly.XA_apply, LeaderDescent.runMax, SepGroup.Model.X, SwarmSpeed.runMax] using h
  filter_upwards [Filter.eventually_all.mpr hsingle] with t ht
  show ((Finset.univ.sup' Finset.univ_nonempty
      (fun j => LeaderDescent.runMax (DiamAssembly.XA p m U) j t - DiamAssembly.XA p m U j t) : ℤ) : ℝ) ≤ ε * (t : ℝ)
  exact sup'_univ_cast_le _ (fun j => ht j)

/-- **`DiamAssembly.HdefA` unconditionally** for `1/2 < p < 1`, every `m ≥ 0` and every `N` with
`Nonempty (Fin N)` (the paper's `(prelim)`, second half).

The only probabilistic input is the verified single-walker oscillation
`SwarmHosc.trajectory_hosc`, which is itself the Hall–Heyde martingale strong law applied to the
paper's `(mart)` martingale. -/
theorem hdefA {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) [Nonempty (Fin N)] :
    @DiamAssembly.HdefA N p m _ :=
  hdefA_of_oscillation (p := p) (m := m) (N := N)
    (SwarmHosc.trajectory_hosc hp0 hp1 m N)

end DiamAssemblyHdefA

/-!
## 4. Independent second proof: the paper's own `(mart)` route

The paper proves `(prelim)` as `0 ≤ max_{t≤n}(M_t^i - X_t^i) ≤ 2 max_{t≤n}|𝓜_t^i| = o(n)`,
where `𝓜^i_n = X^i_n - (2p-1) #{t < n : i excited at t}` is the drift martingale.  We prove the
pathwise inequality here (it uses only `2p-1 ≥ 0` and monotonicity of the excitation counter) and
combine it with `SwarmHosc.trajectory_mart_max_div`, which is `max_{t≤n}|𝓜_t^i| = o(n)` for the
actual array.  This route does not pass through `trajectory_hosc`, so the two proofs of `HdefA`
below are logically independent apart from the shared `(mart)` decomposition.
-/

namespace DiamAssemblyHdefA

variable {N : ℕ}

/-- **The paper's pathwise inequality.**  If the drift martingale of walker `i` is bounded by
`η n` in absolute value up to time `n`, then the `(prelim)` deficit of walker `i` at every time
`t ≤ n` is at most `2 η n`.

This is exactly `max_{t≤n}(M_t - X_t) ≤ 2 max_{t≤n}|𝓜_t|` at scale `η n`: for `s ≤ t ≤ n`,
`X_s - X_t = (𝓜_s - 𝓜_t) + (2p-1)(E_s - E_t) ≤ |𝓜_s| + |𝓜_t|` since `2p-1 ≥ 0` and the
excitation counter `E` is monotone. -/
theorem deficit_le_two_mart {p : ℝ} (hp : 1 / 2 ≤ p) {m : ℕ} (U : Array N) [Nonempty (Fin N)]
    (i : Fin N) {n : ℕ} {η : ℝ}
    (hA : ∀ u ≤ n,
      |Swarm.mart p (fun t (U : Array N) => (trajectory p m U t).pos) m u U i| ≤ η * (n : ℝ)) :
    ∀ t ≤ n,
      ((LeaderDescent.runMax (DiamAssembly.XA p m U) i t - DiamAssembly.XA p m U i t : ℤ) : ℝ)
        ≤ 2 * (η * (n : ℝ)) := by
  intro t ht
  have hc0 : 0 ≤ 2 * p - 1 := by linarith
  -- the maximiser of the running maximum up to time `t`
  obtain ⟨s, hs, hsup⟩ := Finset.exists_mem_eq_sup'
    (s := Finset.range (t + 1)) ⟨0, Finset.mem_range.mpr (Nat.succ_pos t)⟩
    (fun s => DiamAssembly.XA p m U i s)
  have hst : s ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  -- the decomposition `X = 𝓜 + (2p-1)·E`
  have hid : ∀ u : ℕ, ((DiamAssembly.XA p m U i u : ℤ) : ℝ)
      = Swarm.mart p (fun t (U : Array N) => (trajectory p m U t).pos) m u U i
        + (2 * p - 1)
            * (Swarm.excCount (fun t (U : Array N) => (trajectory p m U t).pos) m u U i : ℝ) := by
    intro u
    simp only [Swarm.mart, Swarm.pos, DiamAssembly.XA_apply, SepGroup.Model.X]
    ring
  have hcast : ((LeaderDescent.runMax (DiamAssembly.XA p m U) i t
        - DiamAssembly.XA p m U i t : ℤ) : ℝ)
      = ((DiamAssembly.XA p m U i s : ℤ) : ℝ) - ((DiamAssembly.XA p m U i t : ℤ) : ℝ) := by
    rw [LeaderDescent.runMax, hsup]
    push_cast
    ring
  rw [hcast, hid s, hid t]
  -- monotonicity of the excitation counter
  have hEs : (Swarm.excCount (fun t (U : Array N) => (trajectory p m U t).pos) m s U i : ℝ)
      ≤ (Swarm.excCount (fun t (U : Array N) => (trajectory p m U t).pos) m t U i : ℝ) := by
    exact_mod_cast SwarmHosc.excCount_mono (X := fun t (U : Array N) => (trajectory p m U t).pos)
      (m := m) s t hst U i
  have hcs : (2 * p - 1)
      * ((Swarm.excCount (fun t (U : Array N) => (trajectory p m U t).pos) m s U i : ℝ)
        - (Swarm.excCount (fun t (U : Array N) => (trajectory p m U t).pos) m t U i : ℝ)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hc0 (by linarith)
  have h1 := le_of_abs_le (hA s (le_trans hst ht))
  have h2 : -(η * (n : ℝ))
      ≤ Swarm.mart p (fun t (U : Array N) => (trajectory p m U t).pos) m t U i :=
    neg_le_of_abs_le (hA t ht)
  nlinarith [hcs, h1, h2]

/-- **`HdefA` by the paper's `(mart)` route**, from `max_{t≤n}|𝓜_t^i| = o(n)`.
No oscillation theorem is used: only `SwarmHosc.trajectory_mart_max_div` and the deterministic
inequality `deficit_le_two_mart`. -/
theorem hdefA_via_mart {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) [Nonempty (Fin N)] :
    @DiamAssembly.HdefA N p m _ := by
  have hmax := SwarmHosc.trajectory_mart_max_div (p := p) hp0 hp1 m N
  filter_upwards [hmax] with U hU ε hε
  have hsingle : ∀ i : Fin N, ∀ᶠ t : ℕ in atTop,
      ((LeaderDescent.runMax (DiamAssembly.XA p m U) i t - DiamAssembly.XA p m U i t : ℤ) : ℝ)
        ≤ ε * (t : ℝ) := by
    intro i
    filter_upwards [hU i (ε / 2) (by linarith)] with n hn
    have h := deficit_le_two_mart (N := N) (le_of_lt hp0) (m := m) U i (n := n) (η := ε / 2)
      (fun u hu => hn u hu) n le_rfl
    linarith
  filter_upwards [Filter.eventually_all.mpr hsingle] with t ht
  show ((Finset.univ.sup' Finset.univ_nonempty
      (fun j => LeaderDescent.runMax (DiamAssembly.XA p m U) j t - DiamAssembly.XA p m U j t)
        : ℤ) : ℝ) ≤ ε * (t : ℝ)
  exact sup'_univ_cast_le _ (fun j => ht j)

end DiamAssemblyHdefA

/-!
## 5. Interface consequences

Two consequences that make the result directly usable downstream:

* `deficit_div_tendsto` — the paper's literal phrasing `(M_t - X_t)/t → 0` a.s.;
* `ae_spread_div_tendsto_zero_of_transience'` — `(diam)` from `DiamAssemblyMain.lean` with the
  `HdefA` premise *discharged*: the remaining premises are exactly `LogVarBound` (the paper's
  log-fourth `Q` variance estimate), `HcompA` (the positional comparison) and the a.e. transience
  of the individual walkers.
-/

namespace DiamAssemblyHdefA

variable {N : ℕ}

/-- **The paper's phrasing of `(prelim)`**: the normalised deficit converges to `0` a.s. -/
theorem deficit_div_tendsto {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) [Nonempty (Fin N)] :
    ∀ᵐ U ∂(arrayMeasure N), Tendsto
      (fun t : ℕ => ((NestedLeader.deficit (DiamAssembly.XA p m U) t : ℤ) : ℝ) / (t : ℝ))
      atTop (𝓝 0) := by
  have hdef : @DiamAssembly.HdefA N p m _ := hdefA (N := N) hp0 hp1 m
  filter_upwards [hdef] with U hU
  refine tendsto_order.2 ⟨?_, ?_⟩
  · -- lower bound: the deficit is nonnegative
    intro a ha
    filter_upwards with t
    have hnn : (0 : ℝ) ≤ ((NestedLeader.deficit (DiamAssembly.XA p m U) t : ℤ) : ℝ) := by
      exact_mod_cast NestedLeader.deficit_nonneg (X := DiamAssembly.XA p m U) t
    have : (0 : ℝ) ≤ ((NestedLeader.deficit (DiamAssembly.XA p m U) t : ℤ) : ℝ) / (t : ℝ) :=
      div_nonneg hnn (Nat.cast_nonneg t)
    linarith
  · -- upper bound: `HdefA` at `ε / 2`
    intro a ha
    have ha2 : 0 < a / 2 := by linarith
    filter_upwards [hU (a / 2) ha2, Filter.eventually_gt_atTop (0 : ℕ)] with t ht ht0
    have ht0' : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht0
    have hle : ((NestedLeader.deficit (DiamAssembly.XA p m U) t : ℤ) : ℝ) ≤ (a / 2) * (t : ℝ) := ht
    rw [div_lt_iff₀ ht0']
    nlinarith [hle]

/-- **`(diam)` with the `HdefA` premise discharged.**

This is `DiamAssembly.ae_spread_div_tendsto_zero_of_transience` with `hdef` supplied by
`hdefA`.  The remaining premises are the paper's log-fourth `Q` variance estimate
(`LogVarBound`), the positional comparison `HcompA`, and a.e. transience of each walker. -/
theorem ae_spread_div_tendsto_zero_of_transience' {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) [Nonempty (Fin N)] {C K : ℝ} (hK : 0 ≤ K)
    (hC : @DiamAssembly.LogVarBound N p m C) (hcomp : @DiamAssembly.HcompA N p m _ K)
    (htr : ∀ i : Fin N, ∀ᵐ U ∂(arrayMeasure N),
      Tendsto (fun n => (trajectory p m U n).pos i) atTop atTop) :
    ∀ᵐ U ∂(arrayMeasure N),
      Tendsto (fun n => ((LeaderDescent.spreadZ (DiamAssembly.XA p m U) n : ℤ) : ℝ) / (n : ℝ))
        atTop (𝓝 0) :=
  DiamAssembly.ae_spread_div_tendsto_zero_of_transience (N := N) hp0 hp1 m hK hC hcomp
    (hdefA (N := N) hp0 hp1 m) htr

end DiamAssemblyHdefA

/-!
## 6. Abstract form: the transfer is structural, not array-specific

The same finite-sup transfer from `SwarmHosc.hosc_of_law` gives the deficit estimate for *any*
system satisfying the paper's interacting law (and hence, by `actual_isInteractingLaw`, for the
actual array again).  This records that `HdefA` needs nothing beyond `(mart)`.
-/

namespace DiamAssemblyHdefA

variable {N : ℕ}

/-- **Deficit estimate for any interacting law.**  For every system satisfying the paper's
one-step law, almost surely every walker's running maximum minus its position is `o(t)`, so the
array supremum is `o(t)`. -/
theorem hdef_of_law {Ω : Type*} [m0 : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Fin N → ℤ} {𝓕 : Filtration ℕ m0} {m : ℕ} {p : ℝ}
    (hp0 : 1 / 2 < p) (hp1 : p < 1) (hlaw : Swarm.IsInteractingLaw 𝓕 μ X m p)
    [Nonempty (Fin N)] :
    ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℕ in atTop,
      ((NestedLeader.deficit (fun i s => X s ω i) t : ℤ) : ℝ) ≤ ε * (t : ℝ) := by
  filter_upwards [SwarmHosc.hosc_of_law hlaw (le_of_lt hp0) (le_of_lt hp1)] with ω hω ε hε
  have hsingle : ∀ i : Fin N, ∀ᶠ t : ℕ in atTop,
      ((LeaderDescent.runMax (fun i s => X s ω i) i t - (fun i s => X s ω i) i t : ℤ) : ℝ)
        ≤ ε * (t : ℝ) := by
    intro i
    have h := walker_deficit_eventually_le (f := fun s => X s ω i) (hω i) ε hε
    simpa only [LeaderDescent.runMax, SwarmSpeed.runMax] using h
  filter_upwards [Filter.eventually_all.mpr hsingle] with t ht
  exact sup'_univ_cast_le _ (fun j => ht j)

/-- **`DiamAssembly.HdefA` once more, now as a corollary of the abstract `hdef_of_law`.** -/
theorem hdefA' {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) [Nonempty (Fin N)] :
    @DiamAssembly.HdefA N p m _ := by
  have h := hdef_of_law (N := N) (μ := arrayMeasure N)
    (X := fun t (U : Array N) => (trajectory p m U t).pos)
    (𝓕 := SwarmCross.pathFilt p m) (m := m) hp0 hp1
    (SwarmCross.Actual.actual_isInteractingLaw hp0 hp1 m)
  filter_upwards [h] with U hU
  have hfun : (fun i s => (trajectory p m U s).pos i) = DiamAssembly.XA p m U := by
    funext i s
    simp only [DiamAssembly.XA_apply, SepGroup.Model.X]
  rwa [hfun] at hU

end DiamAssemblyHdefA
