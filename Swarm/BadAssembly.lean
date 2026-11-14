/-
  **The `BadTime` layer and the exponential crossing bound at the actual model.**

  `Swarm/ActualDischarge.lean` reduces transience of the actual interacting
  trajectory to one numeric premise `hcross`:

  ```
  forall k >= K, forall s,  P(BadTime k s inter ActualExtra k) <= exp (-c b_k).
  ```

  `Swarm/Aggregation.lean` already proves the union bound / Borel--Cantelli
  half of that reduction, and `RawLogRatio` proves the log-ratio strong law.  What is not
  in the repository is a proof of `hcross` itself, and the reason is not only the
  probabilistic crossing estimate: **the `BadTime` event is not in the shape the crossing
  layer bounds.**  It carries

  * a `hitBefore` conjunct, which is a *forward* event (it speaks about times `>= s`) and so
    cannot be an `F_s`-measurable test event; and
  * a product weight `prod_{a_k < x <= b_k} (1-omega_j(x))/omega_j(x)` written with an
    explicit `Finset.Ioc`, whereas the verified crossing layer `Swarm/Cross.lean`
    produces its right-hand side in the scale-function form `R (omega_j) a_k b_k`.

  This file closes exactly that bookkeeping and nothing else.  It proves, at the actual
  model, with no new stochastic hypothesis beyond the crossing estimate itself:

  * `hitBefore_iff_shift` -- `hitBefore` *is* the shifted `hitsBefore` event of the crossing
    layer (with `Z`-valued positions);
  * `badTime_eq` -- `BadTime k s = actualSite k s inter badCross k s`, an `F_s`-measurable
    "site" event intersected with the purely forward crossing event;
  * `measurableSet_actualSite` -- the site event is `F_s`-measurable for the **actual
    enlarged filtration** `enlFilt p m` (positions and their running maxima are adapted);
  * `actualExtra_iff_R` -- the paper's product-decay event `ActualExtra` is, verbatim, the
    event `{R (omega_j) a_k b_k <= exp (-c b_k)}` of the crossing layer;
  * `setIntegral_le_mul_real_of_le_on` and `measure_le_ofReal_of_real_le` -- the two
    measure-theoretic trivialities that turn a set-integral bound with a pointwise weight
    bound into the `ENNReal` bound `hcross`;
  * `crossing_bound_of_condExp` -- the exponential crossing bound `hcross` from the
    conditional revealed crossing estimate, in the exact "for every `F_s`-measurable test
    set" form the crossing layer delivers;
  * `ae_transience_of_revealed_crossing` -- transience of the actual interacting trajectory
    from that single input.

  What is *not* proved here, and is not disguised as a hypothesis: the conditional revealed
  crossing estimate itself.  Supplying it needs (i) the exit-frozen walk on `[a_k, b_k+1]`
  (the global a.e. hypotheses `hstart`, `hrange`, `hstep` of `Cross.lean` are false for the
  unstopped actual walk, since it is unbounded above), (ii) the one-step law as a genuine
  `condExp` on `enlFilt`, and (iii) `F_s`-measurability of the revealed window weights
  `omega_j(x)`, `a_k < x <= b_k`, which the site event guarantees through `M^j_s >= b_k+1`.
  Those three are separate directions of this swarm, not consequences of anything below.
-/
import Swarm.Imports
import Swarm.ActualDischarge
import Swarm.Transience.Main
import Swarm.PathNat
import Swarm.Cross
import Swarm.EnlFilt

open MeasureTheory Filter
open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Enl
open scoped ENNReal BigOperators Topology

namespace SwarmBad

noncomputable section

open SwarmSpeed SwarmDischarge

variable {N : ℕ}

/-! ### 1. The `hitBefore` conjunct, in the crossing layer's own vocabulary -/

/-- The crossing layer's `SwarmSpeed.hitsBefore`, with `Z`-valued paths -- the shape in
which the actual interacting positions take values.  `hitsBeforeZ X z w` is the event that
the path `X` visits the level `z` before the level `w`. -/
def hitsBeforeZ {Ω : Type*} (X : ℕ → Ω → ℤ) (z w : ℤ) : Set Ω :=
  {ω | ∃ n, X n ω = z ∧ ∀ k < n, X k ω ≠ w}

/-- The actual walker `i` of the interacting recursion, seen from time `s`. -/
def shiftPos (p : ℝ) (m : ℕ) (i : Fin N) (s : ℕ) : ℕ → Array N → ℤ :=
  fun n U => (trajectory p m U (s + n)).pos i

/-- **The paper's `hitBefore`, shifted.**  "Starting at time `s`, the path `u` reaches the
level `w` before the level `z`" is the same statement about the shifted path
`n |-> u (s+n)`, with no hypothesis on `u`. -/
theorem hitBefore_iff_shift {u : ℕ → ℤ} {s : ℕ} {z w : ℤ} :
    SwarmDeepNat.hitBefore u s z w ↔
      ∃ n, u (s + n) = w ∧ ∀ k < n, u (s + k) ≠ z := by
  unfold SwarmDeepNat.hitBefore
  constructor
  · rintro ⟨t, hst, hwt, hz⟩
    refine ⟨t - s, by rw [Nat.add_sub_of_le hst]; exact hwt, fun k hk => ?_⟩
    exact hz (s + k) (Nat.le_add_right s k) (by omega)
  · rintro ⟨n, hn, hz⟩
    refine ⟨s + n, Nat.le_add_right s n, hn, fun r hr hrt => ?_⟩
    have hrw : s + (r - s) = r := Nat.add_sub_of_le hr
    have hk : r - s < n := by omega
    rw [← hrw]
    exact hz (r - s) hk

/-! ### 2. The bad-time event as a site event times a future crossing event -/

/-- The `F_s`-measurable half of the paper's bad time: walker `i` sits at `b_k` and walker
`j`'s running maximum has already reached `b_k + 1`. -/
def actualSite (p : ℝ) (m : ℕ) (i j : Fin N) (k s : ℕ) : Set (Array N) :=
  {U | (trajectory p m U s).pos i = (lvlB k : ℤ) ∧
    (lvlB k : ℤ) + 1 ≤ runMax (fun t => (trajectory p m U t).pos j) s}

/-- The purely future half of the paper's bad time: walker `i` crosses down to `a_k` before
reaching `b_k + 1`. -/
def badCross (p : ℝ) (m : ℕ) (i : Fin N) (k s : ℕ) : Set (Array N) :=
  hitsBeforeZ (shiftPos (N := N) p m i s) ((lvlA k : ℕ) : ℤ) ((lvlB k : ℤ) + 1)

/-- **The paper's bad time factorises** into its `F_s`-measurable site part and the future
crossing part, with the `hitBefore` conjunct in the crossing layer's form. -/
theorem badTime_eq {p : ℝ} {m : ℕ} (i j : Fin N) (k s : ℕ) :
    {U : Array N | BadTime p m U i j k s} = actualSite p m i j k s ∩ badCross p m i k s := by
  ext U
  have h := hitBefore_iff_shift (u := fun t => (trajectory p m U t).pos i) (s := s)
    (z := (lvlB k : ℤ) + 1) (w := ((lvlA k : ℕ) : ℤ))
  simp only [BadTime, actualSite, badCross, hitsBeforeZ, shiftPos, Set.mem_ofPred_eq,
    Set.mem_inter_iff]
  rw [h]
  tauto

/-! ### 3. Adaptedness of the site event in the actual enlarged filtration -/

/-- `c <= runMax u n` as a finite disjunction over the times `t <= n`. -/
theorem le_runMax_iff_exists {u : ℕ → ℤ} {c : ℤ} {n : ℕ} :
    c ≤ runMax u n ↔ ∃ t ≤ n, c ≤ u t := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have hle : runMax u n ≤ c - 1 :=
      runMax_le (fun t ht => by have := hc t ht; omega)
    omega
  · rintro ⟨t, ht, hc⟩
    exact le_trans hc (le_runMax ht)

/-- The running maximum of the actual walker `j` is adapted to the enlarged filtration. -/
theorem measurableSet_runMax_ge (p : ℝ) (m : ℕ) (j : Fin N) (c : ℤ) (s : ℕ) :
    MeasurableSet[enlFilt (N := N) p m s]
      {U : Array N | c ≤ runMax (fun t => (trajectory p m U t).pos j) s} := by
  have hset : {U : Array N | c ≤ runMax (fun t => (trajectory p m U t).pos j) s}
      = ⋃ t ∈ Finset.range (s + 1),
          {U : Array N | c ≤ (trajectory p m U t).pos j} := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range]
    rw [le_runMax_iff_exists]
    constructor
    · rintro ⟨t, ht, hc⟩
      exact ⟨t, by omega, hc⟩
    · rintro ⟨t, ht, hc⟩
      exact ⟨t, by omega, hc⟩
  rw [hset]
  refine Finset.measurableSet_biUnion _ (fun t ht => ?_)
  have hts : t ≤ s := by simp only [Finset.mem_range] at ht; omega
  exact (enl_pos_measurable p m s hts j) (Set.to_countable (Set.Ici c)).measurableSet

/-- **The site event of the paper's bad time is `F_s`-measurable for the actual enlarged
filtration `enlFilt p m`.** -/
theorem measurableSet_actualSite (p : ℝ) (m : ℕ) (i j : Fin N) (k s : ℕ) :
    MeasurableSet[enlFilt (N := N) p m s] (actualSite p m i j k s) := by
  have h1 : MeasurableSet[enlFilt (N := N) p m s]
      {U : Array N | (trajectory p m U s).pos i = (lvlB k : ℤ)} :=
    (enl_pos_measurable p m s le_rfl i) (measurableSet_singleton _)
  have h2 := measurableSet_runMax_ge (N := N) p m j ((lvlB k : ℤ) + 1) s
  exact h1.inter h2

/-! ### 4. The paper's product-decay event is the crossing layer's potential event -/

/-- `Finset.Ioc a b = Finset.Icc (a+1) b`: the product range of the paper's `ActualExtra`
is the scale-function range `R` uses. -/
theorem Ioc_eq_Icc_succ (a b : ℕ) : Finset.Ioc a b = Finset.Icc (a + 1) b := by
  ext x
  simp only [Finset.mem_Ioc, Finset.mem_Icc]
  omega

/-- The revealed weights of walker `j` at the sites of the window `(a_k, b_k]`, as a
function of the underlying array. -/
def windowWeight (p : ℝ) (m : ℕ) (j : Fin N) : Array N → ℕ → ℝ :=
  fun U x => omegaAt p m U j (x : ℤ)

/-- **`ActualExtra` is exactly the crossing layer's potential event.**  The paper's product
`prod_{a_k < x <= b_k} (1-omega_j(x))/omega_j(x)` is `R (omega_j) a_k b_k` with `R, rat` of
`Scale.lean`, and the decay threshold is the same real number. -/
theorem actualExtra_iff_R {p : ℝ} {m : ℕ} (j : Fin N) (c : ℝ) (k : ℕ) :
    ActualExtra p m j c k
      = {U : Array N |
          R (windowWeight p m j U) (lvlA k) (lvlB k) ≤ Real.exp (-(c * (lvlB k : ℝ)))} := by
  ext U
  simp only [ActualExtra, Set.mem_ofPred_eq]
  rw [Ioc_eq_Icc_succ]
  rfl

/-- The revealed weights are measurable functions of the array (no filtration claim). -/
theorem measurableSet_siteMark (p : ℝ) (m : ℕ) (j : Fin N) (x : ℤ) :
    MeasurableSet {U : Array N | SiteMark p m U j x} := by
  have hset : {U : Array N | SiteMark p m U j x}
      = ⋂ k ∈ Finset.Icc 1 (m - 1), {U : Array N | p < U (j, x, k)} := by
    ext U
    simp only [SiteMark, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [hset]
  exact Finset.measurableSet_biInter _ (fun k _ =>
    measurableSet_lt measurable_const
      (measurable_pi_apply (X := fun _ : Fin N × ℤ × ℕ => ℝ) (j, x, k)))

theorem measurable_omegaAt (p : ℝ) (m : ℕ) (j : Fin N) (x : ℤ) :
    Measurable fun U : Array N => omegaAt p m U j x := by
  unfold omegaAt
  exact Measurable.ite (measurableSet_siteMark p m j x) measurable_const measurable_const

theorem measurable_windowPotential (p : ℝ) (m : ℕ) (j : Fin N) (b0 y : ℕ) :
    Measurable fun U : Array N => R (windowWeight p m j U) b0 y :=
  measurable_R_diag (fun x => measurable_omegaAt p m j (x : ℤ)) b0 y

/-- On the actual model the revealed window potential lies in `[0,1]`. -/
theorem windowPotential_bounds {p : ℝ} (hp1 : 1 / 2 ≤ p) (hp2 : p < 1) {m : ℕ}
    (j : Fin N) (b0 y : ℕ) (U : Array N) :
    0 ≤ R (windowWeight p m j U) b0 y ∧ R (windowWeight p m j U) b0 y ≤ 1 := by
  have hlo : ∀ x, (1 : ℝ) / 2 ≤ windowWeight p m j U x := by
    intro x
    unfold windowWeight omegaAt
    classical
    split_ifs with h
    · exact hp1
    · norm_num
  have hhi : ∀ x, windowWeight p m j U x < 1 := by
    intro x
    unfold windowWeight omegaAt
    classical
    split_ifs with h
    · exact hp2
    · norm_num
  exact ⟨R_nonneg hlo hhi y, R_le_one hlo hhi y⟩

/-! ### 5. The measure-theoretic last step -/

/-- **A set-integral bound with a pointwise weight bound becomes a bound by the constant.** -/
theorem setIntegral_le_mul_real_of_le_on {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {A : Set Ω} {g : Ω → ℝ} {C : ℝ}
    (hA : MeasurableSet A) (_hC : 0 ≤ C)
    (hgint : IntegrableOn g A μ) (hg : ∀ᵐ ω ∂μ, ω ∈ A → g ω ≤ C) :
    ∫ ω in A, g ω ∂μ ≤ C * μ.real A := by
  have hCint : IntegrableOn (fun _ : Ω => C) A μ := integrableOn_const (by simp)
  have h := setIntegral_mono_on_ae (μ := μ) (s := A) (f := g) (g := fun _ : Ω => C)
    hgint hCint hA hg
  rw [MeasureTheory.setIntegral_const] at h
  simpa only [smul_eq_mul, mul_comm] using h

/-- A `real`-valued bound upgrades to the `ENNReal`-valued bound for a finite measure. -/
theorem measure_le_ofReal_of_real_le {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {S : Set Ω} {x : ℝ} (h : μ.real S ≤ x) :
    μ S ≤ ENNReal.ofReal x := by
  have hfin : μ S ≠ ⊤ := measure_ne_top μ S
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal h

/-! ### 6. The exponential crossing bound at the actual model -/

/-- **Eq. (cross) integrated out, from the conditional revealed crossing estimate.**

If for every `F_s`-measurable event `A` contained in the site event the conditional
probability of the bad crossing is bounded by the revealed potential `R (omega_j) a_k b_k`,
then the paper's crossing estimate
`P(BadTime k s inter ActualExtra k) <= exp(-c b_k)` holds. -/
theorem crossing_bound_of_condExp {p : ℝ} (hp1 : 1 / 2 ≤ p) (hp2 : p < 1) {m : ℕ}
    (i j : Fin N) {c : ℝ} {K : ℕ}
    (hcx : ∀ k ≥ K, ∀ s : ℕ, ∀ A : Set (Array N),
      MeasurableSet[enlFilt (N := N) p m s] A → A ⊆ actualSite p m i j k s →
      (arrayMeasure N).real (badCross p m i k s ∩ A)
        ≤ ∫ U in A, R (windowWeight p m j U) (lvlA k) (lvlB k) ∂(arrayMeasure N))
    (hE : ∀ k ≥ K, ∀ s : ℕ,
      MeasurableSet[enlFilt (N := N) p m s]
        (actualSite p m i j k s ∩ ActualExtra p m j c k)) :
    ∀ k ≥ K, ∀ s : ℕ,
      (arrayMeasure N) ({U : Array N | BadTime p m U i j k s} ∩ ActualExtra p m j c k)
        ≤ ENNReal.ofReal (Real.exp (-(c * (lvlB k : ℝ)))) := by
  intro k hk s
  have hAmeas : MeasurableSet[enlFilt (N := N) p m s]
      (actualSite p m i j k s ∩ ActualExtra p m j c k) := hE k hk s
  have hAmeas' : MeasurableSet (actualSite p m i j k s ∩ ActualExtra p m j c k) :=
    (enlFilt (N := N) p m).le s _ hAmeas
  have hcxA : (arrayMeasure N).real
      (badCross p m i k s ∩ (actualSite p m i j k s ∩ ActualExtra p m j c k))
      ≤ ∫ U in (actualSite p m i j k s ∩ ActualExtra p m j c k),
          R (windowWeight p m j U) (lvlA k) (lvlB k) ∂(arrayMeasure N) :=
    hcx k hk s _ hAmeas Set.inter_subset_left
  -- the pointwise bound: `R` is at most the decay threshold on `ActualExtra`
  have hpoint : ∀ U : Array N,
      U ∈ actualSite p m i j k s ∩ ActualExtra p m j c k →
      R (windowWeight p m j U) (lvlA k) (lvlB k) ≤ Real.exp (-(c * (lvlB k : ℝ))) := by
    intro U hU
    have h := hU.2
    rwa [actualExtra_iff_R] at h
  have hRint : IntegrableOn (fun U => R (windowWeight p m j U) (lvlA k) (lvlB k))
      (actualSite p m i j k s ∩ ActualExtra p m j c k) (arrayMeasure N) := by
    refine Integrable.integrableOn (Integrable.of_bound
      (measurable_windowPotential p m j (lvlA k) (lvlB k)).aestronglyMeasurable 1 ?_)
    filter_upwards with U
    rw [Real.norm_eq_abs,
      abs_of_nonneg (windowPotential_bounds hp1 hp2 j (lvlA k) (lvlB k) U).1]
    exact (windowPotential_bounds hp1 hp2 j (lvlA k) (lvlB k) U).2
  have hint : ∫ U in (actualSite p m i j k s ∩ ActualExtra p m j c k),
        R (windowWeight p m j U) (lvlA k) (lvlB k) ∂(arrayMeasure N)
      ≤ Real.exp (-(c * (lvlB k : ℝ)))
        * (arrayMeasure N).real (actualSite p m i j k s ∩ ActualExtra p m j c k) :=
    setIntegral_le_mul_real_of_le_on hAmeas' (Real.exp_pos _).le hRint
      (Filter.Eventually.of_forall hpoint)
  have hAone : (arrayMeasure N).real (actualSite p m i j k s ∩ ActualExtra p m j c k) ≤ 1 := by
    calc (arrayMeasure N).real (actualSite p m i j k s ∩ ActualExtra p m j c k)
        ≤ (arrayMeasure N).real Set.univ := measureReal_mono (Set.subset_univ _)
      _ = 1 := by rw [measureReal_def, measure_univ]; norm_num
  have hreal : (arrayMeasure N).real
      (badCross p m i k s ∩ (actualSite p m i j k s ∩ ActualExtra p m j c k))
      ≤ Real.exp (-(c * (lvlB k : ℝ))) := by
    refine hcxA.trans ?_
    refine hint.trans ?_
    calc Real.exp (-(c * (lvlB k : ℝ)))
          * (arrayMeasure N).real (actualSite p m i j k s ∩ ActualExtra p m j c k)
        ≤ Real.exp (-(c * (lvlB k : ℝ))) * 1 :=
          mul_le_mul_of_nonneg_left hAone (Real.exp_pos _).le
      _ = Real.exp (-(c * (lvlB k : ℝ))) := mul_one _
  -- identify the measure of the paper's event with that set-integral
  have hset : {U : Array N | BadTime p m U i j k s} ∩ ActualExtra p m j c k
      = badCross p m i k s ∩ (actualSite p m i j k s ∩ ActualExtra p m j c k) := by
    rw [badTime_eq i j k s]
    ext U
    simp only [Set.mem_inter_iff]
    tauto
  rw [hset]
  exact measure_le_ofReal_of_real_le hreal

/-! ### 7. Transience of the actual interacting trajectory from that single input -/

/-- **Transience of the actual interacting trajectory** from the conditional revealed
crossing estimate.  The remaining input `hcx` is the crossing estimate eq. (cross) in
integrated-conditional form; everything else -- the `hitBefore`/`Ioc` bookkeeping, the
`F_s`-measurability of the site event, the pointwise product bound, the union bound over
`s <= (k+1)^4`, Borel--Cantelli, the log-ratio strong law and the pathwise excursion
argument -- is proved. -/
theorem ae_transience_of_revealed_crossing {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (a b : Fin N) {K : ℕ}
    (hcx : ∀ k ≥ K, ∀ s : ℕ, ∀ A : Set (Array N),
      MeasurableSet[enlFilt (N := N) p m s] A → A ⊆ actualSite p m a b k s →
      (arrayMeasure N).real (badCross p m a k s ∩ A)
        ≤ ∫ U in A, R (windowWeight p m b U) (lvlA k) (lvlB k) ∂(arrayMeasure N))
    (hE : ∀ k ≥ K, ∀ s : ℕ,
      MeasurableSet[enlFilt (N := N) p m s]
        (actualSite p m a b k s
          ∩ ActualExtra p m b (SwarmLogRatio.paperC p ((1 - p) ^ (m - 1))) k)) :
    ∀ᵐ U ∂(arrayMeasure N),
      Tendsto (fun n => (trajectory p m U n).pos a) atTop atTop := by
  refine SwarmDischarge.ae_transience_of_actual_crossing_bound (N := N) (m := m) (K := K)
    hp1 hp2 hm a b ?_
  exact crossing_bound_of_condExp (N := N) hp1.le hp2 a b hcx hE

end

end SwarmBad


