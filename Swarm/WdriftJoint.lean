/-
  ** joint the joint `(Wdrift)` / `(Wstrict)` conditional
  expectation on the actual interacting array.**
-/
import Swarm.DiamWdrift
import Swarm.MartingaleLimit

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace SwarmJointDrift

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie

variable {N : ℕ}

/-! ### 0. The objects of the drift estimate -/

/-- The separation event `(sep)` at time `n`, as a set. -/
def SepSet (p : ℝ) (m : ℕ) (n : ℕ) (I J : Finset (Fin N)) (U : Array N) : Prop :=
  Sep p m U n I J

theorem measurableSet_sepSet (p : ℝ) (m : ℕ) (n : ℕ) (I J : Finset (Fin N)) :
    MeasurableSet[posFilt N p m n] {U : Array N | SepSet p m n I J U} :=
  SwarmM3.measurableSet_Sep_posFilt p m n I J

/-- `|I|^{-1} sum_{i in I} H_n^{J^c}(X_{n+1}^i)`: the average at the *new* positions with the
*old* weights. -/
noncomputable def Anext (p : ℝ) (m : ℕ) (n : ℕ) (I J : Finset (Fin N)) (U : Array N) : ℝ :=
  Swarming.Group.average I (fun i => HA p m U n Jᶜ (X p m U (n + 1) i))

/-- `max_{j in J} H_n^{J^c}(X_{n+1}^j)` at the new positions with the old weights. -/
noncomputable def Mnext (p : ℝ) (m : ℕ) (n : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty)
    (U : Array N) : ℝ :=
  Swarming.Group.maximumOn J hJ (fun j => HA p m U n Jᶜ (X p m U (n + 1) j))

/-- `|I|^{-1} sum_{i in I} H_n^{J^c}(X_n^i)`. -/
noncomputable def Anow (p : ℝ) (m : ℕ) (n : ℕ) (I J : Finset (Fin N)) (U : Array N) : ℝ :=
  Swarming.Group.average I (fun i => HA p m U n Jᶜ (X p m U n i))

/-- `max_{j in J} H_n^{J^c}(X_n^j)`. -/
noncomputable def Mnow (p : ℝ) (m : ℕ) (n : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty)
    (U : Array N) : ℝ :=
  Swarming.Group.maximumOn J hJ (fun j => HA p m U n Jᶜ (X p m U n j))

/-- The paper's correction average `|I|^{-1} sum_{i in I} (alpha_n^i - w_n^{J^c}(X_n^i))
(h + h^-)`; it is `-` the `(Wstrict)` right-hand side. -/
noncomputable def Cavg (p : ℝ) (m : ℕ) (n : ℕ) (I J : Finset (Fin N)) (U : Array N) : ℝ :=
  Swarming.Group.average I (fun i => corr p m U n Jᶜ i)

/-- `max_{j in J} (1 + corr_n^j + H_n^{J^c}(X_n^j))`, the lower bound for the conditional mean
of the maximum. -/
noncomputable def Cmax (p : ℝ) (m : ℕ) (n : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty)
    (U : Array N) : ℝ :=
  Swarming.Group.maximumOn J hJ (fun j => 1 + corr p m U n Jᶜ j + HA p m U n Jᶜ (X p m U n j))

theorem WA_eq (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (I J : Finset (Fin N))
    (hI : I.Nonempty) (hJ : J.Nonempty) :
    WA p m U n I J hI hJ = Anow p m n I J U - Mnow p m n J hJ U := rfl

/-! ### 1. The stored right probability and the drift correction -/

theorem alphaFun_eq_rightProb (p : ℝ) (m n : ℕ) (i : Fin N) (U : Array N) :
    SwarmCross.alphaFun p m n i U
      = rightProbability p m (trajectory p m U n).ell i (X p m U n i) := rfl

/-- The paper's `(unit)` identity in the form of the correction term `corr`. -/
theorem condExp_HA_drift_corr {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m n : ℕ)
    (A : Finset (Fin N)) (i : Fin N) {A₀ : Set (Array N)}
    (hA₀ : MeasurableSet[posFilt N p m n] A₀) (hsub : A₀ ⊆ {U | 0 ≤ X p m U n i}) :
    condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => A₀.indicator
        (fun U => HA p m U n A (X p m U (n + 1) i) - HA p m U n A (X p m U n i)) U)
    =ᵐ[arrayMeasure N]
      fun U => A₀.indicator (fun U => 1 + corr p m U n A i) U := by
  refine (SwarmM3.condExp_HA_drift_of_subset hp0 hp1 m n A i hA₀ hsub).trans ?_
  refine Filter.EventuallyEq.of_eq ?_
  funext U
  by_cases hU : U ∈ A₀
  · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU]
    simp only [corr, alphaFun_eq_rightProb]
  · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]

/-! ### 2. Measurability and integrability of the potential at a random site -/

theorem measurable_wA_ambient (p : ℝ) (m n : ℕ) (A : Finset (Fin N)) (x : ℕ) :
    Measurable (fun U : Array N => wA p m U n A x) :=
  (SwarmM3.measurable_wA_posFilt p m n A x).mono ((posFilt N p m).le n) le_rfl

theorem measurable_hfix_wA_ambient (p : ℝ) (m n : ℕ) (A : Finset (Fin N)) (u : ℕ) :
    Measurable (fun U : Array N => hfix (wA p m U n A) u) :=
  (SwarmM3.measurable_hfix_wA_posFilt p m n A u).mono ((posFilt N p m).le n) le_rfl

theorem measurable_X_ambient (p : ℝ) (m : ℕ) (k : ℕ) (i : Fin N) :
    Measurable (fun U : Array N => X p m U k i) :=
  (measurable_pos_posFilt p m i (le_refl k)).mono ((posFilt N p m).le k) le_rfl

/-- `H^w` evaluated at a random site: explicit `if`/finite-sum form. -/
theorem HA_random_site_eq (p : ℝ) (m n : ℕ) (A : Finset (Fin N)) (Y : Array N → ℤ)
    {M : ℕ} (hYb : ∀ U, |Y U| ≤ (M : ℤ)) :
    (fun U : Array N => HA p m U n A (Y U))
      = fun U => if Y U < 0 then ((Y U : ℤ) : ℝ) else
          ∑ u ∈ Finset.range (M + 1), (if (u : ℤ) < Y U then hfix (wA p m U n A) u else 0) := by
  funext U
  rcases lt_or_ge (Y U) 0 with hneg | hpos
  · rw [if_pos hneg]
    show SepGroup.HZ (wA p m U n A) (Y U) = ((Y U : ℤ) : ℝ)
    rw [SepGroup.HZ_neg hneg]
  · rw [if_neg (by omega)]
    show SepGroup.HZ (wA p m U n A) (Y U)
      = ∑ u ∈ Finset.range (M + 1), (if (u : ℤ) < Y U then hfix (wA p m U n A) u else 0)
    rw [SepGroup.HZ_nonneg hpos, Cookie.Hfix]
    have hsub : Finset.range (Y U).toNat ⊆ Finset.range (M + 1) := by
      refine Finset.range_subset_range.mpr ?_
      have := (abs_le.mp (hYb U)).2
      omega
    have hleft : (∑ u ∈ Finset.range (Y U).toNat, hfix (wA p m U n A) u)
        = ∑ u ∈ Finset.range (Y U).toNat,
            (if (u : ℤ) < Y U then hfix (wA p m U n A) u else 0) := by
      refine Finset.sum_congr rfl fun u hu => ?_
      have hu' : u < (Y U).toNat := Finset.mem_range.mp hu
      have hlt : (u : ℤ) < Y U := by
        have h1 : (u : ℤ) + 1 = ((u + 1 : ℕ) : ℤ) := by push_cast; ring
        have h2 : ((u + 1 : ℕ) : ℤ) ≤ ((Y U).toNat : ℤ) := by
          exact_mod_cast Nat.succ_le_of_lt hu'
        have h3 : ((Y U).toNat : ℤ) = Y U := Int.toNat_of_nonneg hpos
        omega
      rw [if_pos hlt]
    rw [hleft]
    refine Finset.sum_subset hsub fun u _ hnu => ?_
    rw [if_neg]
    intro hlt
    apply hnu
    rw [Finset.mem_range]
    have h1 : (u : ℤ) ≤ Y U := le_of_lt hlt
    have h2 : ((Y U).toNat : ℤ) = Y U := Int.toNat_of_nonneg hpos
    omega

theorem measurable_HA_random_site (p : ℝ) (m n : ℕ) (A : Finset (Fin N)) (Y : Array N → ℤ)
    (hY : Measurable Y) (M : ℕ) (hYb : ∀ U, |Y U| ≤ (M : ℤ)) :
    Measurable (fun U : Array N => HA p m U n A (Y U)) := by
  rw [HA_random_site_eq p m n A Y hYb]
  refine Measurable.ite (hY measurableSet_Iio) ?_ ?_
  · have hcast : Measurable (fun z : ℤ => (z : ℝ)) :=
      measurable_of_countable (fun z : ℤ => (z : ℝ))
    exact hcast.comp hY
  · exact Finset.measurable_sum _ fun u _ =>
      Measurable.ite (measurableSet_lt measurable_const hY) (measurable_hfix_wA_ambient p m n A u)
        measurable_const

/-- Explicit bound for `H_n^A` at a site of modulus at most `M`. -/
theorem abs_HA_le {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ) (U : Array N)
    (A : Finset (Fin N)) {y : ℤ} {M : ℕ} (hy : |y| ≤ (M : ℤ)) :
    |HA p m U n A y| ≤ (M : ℝ) * (2 * (M : ℝ) + 3) + 3 :=
  SwarmM3.abs_HZ_le (w := wA p m U n A) (fun k => one_half_le_wA p m U hp n A k)
    (fun k => wA_le_one p m U hp1 n A k) hy

/-- Integrability of `H_n^A` evaluated at the actual position of walker `i` at time `k`. -/
theorem integrable_HA_X {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n k : ℕ)
    (A : Finset (Fin N)) (i : Fin N) :
    Integrable (fun U : Array N => HA p m U n A (X p m U k i)) (arrayMeasure N) := by
  have hprob := arrayMeasure_isProbabilityMeasure N
  haveI := hprob
  refine Integrable.of_bound (f := fun U : Array N => HA p m U n A (X p m U k i)) ?_
    ((k : ℝ) * (2 * (k : ℝ) + 3) + 3) (Filter.Eventually.of_forall fun U => ?_)
  · exact (measurable_HA_random_site p m n A (fun U => X p m U k i)
      (measurable_X_ambient p m k i) k (fun U => SwarmM3.abs_X_le p m U k i)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact abs_HA_le hp hp1 m n U A (SwarmM3.abs_X_le p m U k i)


/-! ### 3. A `posFilt` version of the random-site measurability, and integrability -/

theorem measurable_HA_random_site' {F : MeasurableSpace (Array N)} (p : ℝ) (m n : ℕ)
    (A : Finset (Fin N)) (Y : Array N → ℤ) (hY : Measurable[F] Y)
    (hfixM : ∀ u, Measurable[F] (fun U => hfix (wA p m U n A) u)) (M : ℕ)
    (hYb : ∀ U, |Y U| ≤ (M : ℤ)) :
    Measurable[F] (fun U : Array N => HA p m U n A (Y U)) := by
  rw [HA_random_site_eq p m n A Y hYb]
  refine Measurable.ite (hY measurableSet_Iio) ?_ ?_
  · have hcast : Measurable (fun z : ℤ => (z : ℝ)) := measurable_of_countable _
    exact hcast.comp hY
  · exact Finset.measurable_sum _ fun u _ =>
      Measurable.ite (measurableSet_lt measurable_const hY) (hfixM u) measurable_const

/-- `posFilt`-measurability of `H_n^A` at the actual position of time `n`. -/
theorem measurable_HA_X_posFilt (p : ℝ) (m n : ℕ) (A : Finset (Fin N)) (i : Fin N) :
    Measurable[posFilt N p m n] (fun U : Array N => HA p m U n A (X p m U n i)) :=
  measurable_HA_random_site' p m n A (fun U => X p m U n i)
    (measurable_pos_posFilt p m i le_rfl) (fun u => SwarmM3.measurable_hfix_wA_posFilt p m n A u)
    n (fun U => SwarmM3.abs_X_le p m U n i)

theorem integrable_average {ι : Type*} (s : Finset ι) {f : ι → Array N → ℝ}
    (h : ∀ i ∈ s, Integrable (f i) (arrayMeasure N)) :
    Integrable (fun U => Swarming.Group.average s (fun i => f i U)) (arrayMeasure N) := by
  have hsum : Integrable (fun U => ∑ i ∈ s, f i U) (arrayMeasure N) :=
    integrable_finsetSum s h
  have heq : (fun U => Swarming.Group.average s (fun i => f i U))
      = fun U => (∑ i ∈ s, f i U) / ((s.card : ℕ) : ℝ) := rfl
  rw [heq]
  exact hsum.div_const _

theorem integrable_sup' {ι : Type*} (s : Finset ι) (hs : s.Nonempty) {f : ι → Array N → ℝ}
    (h : ∀ i ∈ s, Integrable (f i) (arrayMeasure N))
    (hmeas : ∀ i ∈ s, Measurable (f i)) :
    Integrable (s.sup' hs f) (arrayMeasure N) := by
  refine Integrable.mono' (g := fun U => ∑ i ∈ s, |f i U|)
    (integrable_finsetSum s (fun i hi => (h i hi).abs)) ?_ ?_
  · exact (Finset.measurable_sup' hs hmeas).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun U => ?_
    obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup' hs (fun i => f i U)
    rw [Real.norm_eq_abs, Finset.sup'_apply, hjeq]
    exact Finset.single_le_sum (f := fun i => |f i U|) (fun i _ => abs_nonneg _) hj

/-- The eta-expanded form of `integrable_sup'`, matching the `maximumOn` definition. -/
theorem integrable_sup'_fun {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    {f : ι → Array N → ℝ} (h : ∀ i ∈ s, Integrable (f i) (arrayMeasure N))
    (hmeas : ∀ i ∈ s, Measurable (f i)) :
    Integrable (fun U => s.sup' hs (fun i => f i U)) (arrayMeasure N) := by
  have heq : (fun U => s.sup' hs (fun i => f i U)) = s.sup' hs f := by
    funext U
    rw [Finset.sup'_apply]
  rw [heq]
  exact integrable_sup' s hs h hmeas

theorem integrable_Anext {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (I J : Finset (Fin N)) :
    Integrable (Anext p m n I J) (arrayMeasure N) :=
  integrable_average I (fun i _ => integrable_HA_X hp hp1 m n (n + 1) Jᶜ i)

theorem integrable_Anow {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (I J : Finset (Fin N)) :
    Integrable (Anow p m n I J) (arrayMeasure N) :=
  integrable_average I (fun i _ => integrable_HA_X hp hp1 m n n Jᶜ i)

theorem integrable_Mnext {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (J : Finset (Fin N)) (hJ : J.Nonempty) :
    Integrable (Mnext p m n J hJ) (arrayMeasure N) :=
  integrable_sup'_fun J hJ (fun j _ => integrable_HA_X hp hp1 m n (n + 1) Jᶜ j)
    (fun j _ => measurable_HA_random_site p m n Jᶜ (fun U => X p m U (n + 1) j)
      (measurable_X_ambient p m (n + 1) j) (n + 1) (fun U => SwarmM3.abs_X_le p m U (n + 1) j))

theorem integrable_Mnow {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (J : Finset (Fin N)) (hJ : J.Nonempty) :
    Integrable (Mnow p m n J hJ) (arrayMeasure N) :=
  integrable_sup'_fun J hJ (fun j _ => integrable_HA_X hp hp1 m n n Jᶜ j)
    (fun j _ => (measurable_HA_X_posFilt p m n Jᶜ j).mono ((posFilt N p m).le n) le_rfl)

/-! ### 4. The indicator commutes with the finite average -/

theorem indicator_average {ι : Type*} (s : Finset ι) (A₀ : Set (Array N))
    (f : ι → Array N → ℝ) :
    (fun U => A₀.indicator (fun U => Swarming.Group.average s (fun i => f i U)) U)
      = fun U => Swarming.Group.average s (fun i => A₀.indicator (fun U => f i U) U) := by
  funext U
  by_cases hU : U ∈ A₀
  · simp only [Set.indicator_of_mem hU, Swarming.Group.average, Finset.sum_apply]
  · simp only [Set.indicator_of_notMem hU, Swarming.Group.average, Finset.sum_apply,
      Pi.zero_apply, Finset.sum_const_zero, zero_div]

theorem indicator_sup' {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (A₀ : Set (Array N))
    (f : ι → Array N → ℝ) :
    (fun U => A₀.indicator (fun U => s.sup' hs (fun i => f i U)) U)
      = fun U => s.sup' hs (fun i => A₀.indicator (fun U => f i U) U) := by
  funext U
  by_cases hU : U ∈ A₀
  · simp only [Set.indicator_of_mem hU, Finset.sup'_apply]
  · simp only [Set.indicator_of_notMem hU, Finset.sup'_apply, Pi.zero_apply,
      Finset.sup'_const]

/-! ### 5. Almost-everywhere congruence for averages and suprema -/

theorem ae_average_congr {ι : Type*} (s : Finset ι) {f g : ι → Array N → ℝ}
    (h : ∀ i ∈ s, f i =ᵐ[arrayMeasure N] g i) :
    (fun U => Swarming.Group.average s (fun i => f i U))
      =ᵐ[arrayMeasure N] (fun U => Swarming.Group.average s (fun i => g i U)) := by
  have hall : ∀ᵐ U ∂(arrayMeasure N), ∀ i ∈ s, f i U = g i U :=
    (Finset.eventually_all (I := s)).mpr h
  filter_upwards [hall] with U hU
  simp only [Swarming.Group.average]
  exact congrArg (fun x => x / ((s.card : ℕ) : ℝ)) (Finset.sum_congr rfl fun i hi => hU i hi)

theorem ae_sup'_congr {ι : Type*} (s : Finset ι) (hs : s.Nonempty) {f g : ι → Array N → ℝ}
    (h : ∀ i ∈ s, f i =ᵐ[arrayMeasure N] g i) :
    (fun U => s.sup' hs (fun i => f i U)) =ᵐ[arrayMeasure N]
      (fun U => s.sup' hs (fun i => g i U)) := by
  have hall : ∀ᵐ U ∂(arrayMeasure N), ∀ i ∈ s, f i U = g i U :=
    (Finset.eventually_all (I := s)).mpr h
  filter_upwards [hall] with U hU
  exact Finset.sup'_congr hs rfl (fun i hi => hU i hi)

/-! ### 6. The single-walker conditional mean in "average at the new site" form -/

theorem condExp_indicator_HA_next {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m n : ℕ)
    (A : Finset (Fin N)) (i : Fin N) {A₀ : Set (Array N)}
    (hA₀ : MeasurableSet[posFilt N p m n] A₀) (hsub : A₀ ⊆ {U | 0 ≤ X p m U n i}) :
    condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => A₀.indicator (fun U => HA p m U n A (X p m U (n + 1) i)) U)
    =ᵐ[arrayMeasure N]
      fun U => A₀.indicator
        (fun U => 1 + corr p m U n A i + HA p m U n A (X p m U n i)) U := by
  classical
  have hprob := arrayMeasure_isProbabilityMeasure N
  haveI := hprob
  have hp : 1 / 2 ≤ p := le_of_lt hp0
  have hp1' : p ≤ 1 := le_of_lt hp1
  have hnext : Integrable (fun U : Array N => HA p m U n A (X p m U (n + 1) i))
      (arrayMeasure N) := integrable_HA_X hp hp1' m n (n + 1) A i
  have hnow : Integrable (fun U : Array N => HA p m U n A (X p m U n i))
      (arrayMeasure N) := integrable_HA_X hp hp1' m n n A i
  have hS : Integrable (fun U : Array N => A₀.indicator
      (fun U => HA p m U n A (X p m U (n + 1) i) - HA p m U n A (X p m U n i)) U)
      (arrayMeasure N) := (hnext.sub hnow).indicator (((posFilt N p m).le n) A₀ hA₀)
  have hN : Integrable (fun U : Array N => A₀.indicator
      (fun U => HA p m U n A (X p m U n i)) U) (arrayMeasure N) := hnow.indicator (((posFilt N p m).le n) A₀ hA₀)
  have hsplit : (fun U => A₀.indicator (fun U => HA p m U n A (X p m U (n + 1) i)) U)
      = fun U => A₀.indicator
          (fun U => HA p m U n A (X p m U (n + 1) i) - HA p m U n A (X p m U n i)) U
        + A₀.indicator (fun U => HA p m U n A (X p m U n i)) U := by
    funext U
    by_cases hU : U ∈ A₀
    · simp only [Set.indicator_of_mem hU, Pi.add_apply]
      ring
    · simp only [Set.indicator_of_notMem hU, Pi.add_apply, add_zero]
  have hstrong : StronglyMeasurable[posFilt N p m n]
      (fun U : Array N => A₀.indicator (fun U => HA p m U n A (X p m U n i)) U) :=
    ((measurable_HA_X_posFilt p m n A i).indicator hA₀).stronglyMeasurable
  have hpull : condExp (posFilt N p m n) (arrayMeasure N)
      (fun U : Array N => A₀.indicator (fun U => HA p m U n A (X p m U n i)) U)
      =ᵐ[arrayMeasure N] fun U => A₀.indicator (fun U => HA p m U n A (X p m U n i)) U :=
    Filter.EventuallyEq.of_eq
      (condExp_of_stronglyMeasurable ((posFilt N p m).le n) hstrong hN)
  have hdrift := condExp_HA_drift_corr hp0 hp1 m n A i hA₀ hsub
  have hlast : (fun U : Array N => A₀.indicator (fun U => 1 + corr p m U n A i) U
        + A₀.indicator (fun U => HA p m U n A (X p m U n i)) U)
      = fun U => A₀.indicator
          (fun U => 1 + corr p m U n A i + HA p m U n A (X p m U n i)) U := by
    funext U
    by_cases hU : U ∈ A₀
    · simp only [Set.indicator_of_mem hU, Pi.add_apply]
    · simp only [Set.indicator_of_notMem hU, Pi.add_apply, add_zero]
  calc condExp (posFilt N p m n) (arrayMeasure N)
        (fun U => A₀.indicator (fun U => HA p m U n A (X p m U (n + 1) i)) U)
      =ᵐ[arrayMeasure N] condExp (posFilt N p m n) (arrayMeasure N)
          (fun U => A₀.indicator
              (fun U => HA p m U n A (X p m U (n + 1) i) - HA p m U n A (X p m U n i)) U
            + A₀.indicator (fun U => HA p m U n A (X p m U n i)) U) :=
        condExp_congr_ae (Filter.EventuallyEq.of_eq hsplit)
    _ =ᵐ[arrayMeasure N] condExp (posFilt N p m n) (arrayMeasure N)
          (fun U => A₀.indicator
              (fun U => HA p m U n A (X p m U (n + 1) i) - HA p m U n A (X p m U n i)) U)
        + condExp (posFilt N p m n) (arrayMeasure N)
          (fun U => A₀.indicator (fun U => HA p m U n A (X p m U n i)) U) :=
        condExp_add hS hN _
    _ =ᵐ[arrayMeasure N] (fun U => A₀.indicator (fun U => 1 + corr p m U n A i) U)
        + (fun U => A₀.indicator (fun U => HA p m U n A (X p m U n i)) U) :=
        hdrift.add hpull
    _ =ᵐ[arrayMeasure N] fun U => A₀.indicator
          (fun U => 1 + corr p m U n A i + HA p m U n A (X p m U n i)) U :=
        Filter.EventuallyEq.of_eq hlast

/-! ### 7. The average: conditional mean of the new-site average -/

theorem indicator_average_add_eq (p : ℝ) (m n : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty)
    (A₀ : Set (Array N)) :
    (fun U => Swarming.Group.average I
        (fun i => A₀.indicator
          (fun U => 1 + corr p m U n Jᶜ i + HA p m U n Jᶜ (X p m U n i)) U))
      = fun U => A₀.indicator
          (fun U => 1 + Cavg p m n I J U + Anow p m n I J U) U := by
  funext U
  by_cases hU : U ∈ A₀
  · rw [Set.indicator_of_mem hU]
    have h1 : Swarming.Group.average I
        (fun i => 1 + corr p m U n Jᶜ i + HA p m U n Jᶜ (X p m U n i))
        = Swarming.Group.average I (fun i => (1 + corr p m U n Jᶜ i)) +
          Swarming.Group.average I (fun i => HA p m U n Jᶜ (X p m U n i)) :=
      SepGroup.Model.average_add _ _
    have h2 : Swarming.Group.average I (fun i => 1 + corr p m U n Jᶜ i)
        = 1 + Swarming.Group.average I (fun i => corr p m U n Jᶜ i) := by
      have h := SepGroup.average_add_const hI (fun i => corr p m U n Jᶜ i) 1
      calc Swarming.Group.average I (fun i => 1 + corr p m U n Jᶜ i)
          = Swarming.Group.average I (fun i => corr p m U n Jᶜ i + 1) :=
            SepGroup.Model.average_congr (fun i _ => by ring)
        _ = Swarming.Group.average I (fun i => corr p m U n Jᶜ i) + 1 := h
        _ = 1 + Swarming.Group.average I (fun i => corr p m U n Jᶜ i) := by ring
    rw [Cavg, Anow]
    simp only [Set.indicator_of_mem hU]
    linarith [h1, h2]
  · rw [Set.indicator_of_notMem hU]
    simp only [Set.indicator_of_notMem hU, Swarming.Group.average, Finset.sum_const_zero, zero_div]

theorem condExp_indicator_Anext {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m n : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) {A₀ : Set (Array N)}
    (hA₀ : MeasurableSet[posFilt N p m n] A₀) (hsub : A₀ ⊆ {U | SepSet p m n I J U}) :
    condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => A₀.indicator (Anext p m n I J) U)
    =ᵐ[arrayMeasure N]
      fun U => A₀.indicator (fun U => 1 + Cavg p m n I J U + Anow p m n I J U) U := by
  classical
  have hprob := arrayMeasure_isProbabilityMeasure N
  haveI := hprob
  have hp : 1 / 2 ≤ p := le_of_lt hp0
  have hp1' : p ≤ 1 := le_of_lt hp1
  have hsubi : ∀ i ∈ I, A₀ ⊆ {U | 0 ≤ X p m U n i} :=
    fun i _ U hU => (hsub hU).1 i
  have hper : ∀ i ∈ I, condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => A₀.indicator (fun U => HA p m U n Jᶜ (X p m U (n + 1) i)) U)
      =ᵐ[arrayMeasure N] fun U => A₀.indicator
        (fun U => 1 + corr p m U n Jᶜ i + HA p m U n Jᶜ (X p m U n i)) U :=
    fun i hi => condExp_indicator_HA_next hp0 hp1 m n Jᶜ i hA₀ (hsubi i hi)
  have hint : ∀ i ∈ I, Integrable (fun U : Array N =>
      A₀.indicator (fun U => HA p m U n Jᶜ (X p m U (n + 1) i)) U) (arrayMeasure N) :=
    fun i _ => (integrable_HA_X hp hp1' m n (n + 1) Jᶜ i).indicator (((posFilt N p m).le n) A₀ hA₀)
  have havg := SwarmM3.condExp_average (N := N) p m n I hI (f := fun i U =>
    A₀.indicator (fun U => HA p m U n Jᶜ (X p m U (n + 1) i)) U) hint
  calc condExp (posFilt N p m n) (arrayMeasure N)
        (fun U => A₀.indicator (Anext p m n I J) U)
      = condExp (posFilt N p m n) (arrayMeasure N)
          (fun U => Swarming.Group.average I
            (fun i => A₀.indicator (fun U => HA p m U n Jᶜ (X p m U (n + 1) i)) U)) :=
        congrArg _ (indicator_average I A₀ (fun i U => HA p m U n Jᶜ (X p m U (n + 1) i)))
    _ =ᵐ[arrayMeasure N] (fun U => Swarming.Group.average I
          (fun i => condExp (posFilt N p m n) (arrayMeasure N)
            (fun U => A₀.indicator (fun U => HA p m U n Jᶜ (X p m U (n + 1) i)) U) U)) := havg
    _ =ᵐ[arrayMeasure N] (fun U => Swarming.Group.average I
          (fun i => A₀.indicator
            (fun U => 1 + corr p m U n Jᶜ i + HA p m U n Jᶜ (X p m U n i)) U)) :=
        ae_average_congr I hper
    _ =ᵐ[arrayMeasure N] fun U => A₀.indicator
          (fun U => 1 + Cavg p m n I J U + Anow p m n I J U) U :=
        Filter.EventuallyEq.of_eq (indicator_average_add_eq p m n I J hI A₀)

/-! ### 8. Measurability of the time-`n` observables -/

theorem measurable_Anow_posFilt (p : ℝ) (m n : ℕ) (I J : Finset (Fin N)) :
    Measurable[posFilt N p m n] (Anow p m n I J) := by
  have hsum : Measurable[posFilt N p m n]
      (fun U => ∑ i ∈ I, HA p m U n Jᶜ (X p m U n i)) :=
    Finset.measurable_sum I (fun i _ => measurable_HA_X_posFilt p m n Jᶜ i)
  have heq : Anow p m n I J
      = fun U => (∑ i ∈ I, HA p m U n Jᶜ (X p m U n i)) / ((I.card : ℕ) : ℝ) := rfl
  rw [heq]
  exact hsum.div_const _

theorem measurable_Mnow_posFilt (p : ℝ) (m n : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty) :
    Measurable[posFilt N p m n] (Mnow p m n J hJ) := by
  letI : MeasurableSpace (Array N) := posFilt N p m n
  have hfun : Mnow p m n J hJ
      = fun U : Array N => J.sup' hJ (fun j => HA p m U n Jᶜ (X p m U n j)) := rfl
  rw [hfun]
  have heta : (fun U : Array N => J.sup' hJ (fun j => HA p m U n Jᶜ (X p m U n j)))
      = J.sup' hJ (fun j U => HA p m U n Jᶜ (X p m U n j)) := by
    funext U
    rw [Finset.sup'_apply]
  rw [heta]
  exact Finset.measurable_sup' hJ (fun j _ => measurable_HA_X_posFilt p m n Jᶜ j)

theorem measurable_WA_posFilt (p : ℝ) (m n : ℕ) (I J : Finset (Fin N))
    (hI : I.Nonempty) (hJ : J.Nonempty) :
    Measurable[posFilt N p m n] (fun U => WA p m U n I J hI hJ) := by
  have heq : (fun U => WA p m U n I J hI hJ)
      = fun U => Anow p m n I J U - Mnow p m n J hJ U := by
    funext U
    exact WA_eq p m U n I J hI hJ
  rw [heq]
  exact (measurable_Anow_posFilt p m n I J).sub (measurable_Mnow_posFilt p m n J hJ)

/-! ### 9. The maximum term: conditional mean dominates the maximum of the means -/

theorem condExp_indicator_Mnext_ge {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m n : ℕ)
    (I J : Finset (Fin N)) (hJ : J.Nonempty) {A₀ : Set (Array N)}
    (hA₀ : MeasurableSet[posFilt N p m n] A₀) (hsub : A₀ ⊆ {U | SepSet p m n I J U}) :
    (fun U => A₀.indicator (Cmax p m n J hJ) U)
      ≤ᵐ[arrayMeasure N] condExp (posFilt N p m n) (arrayMeasure N)
        (fun U => A₀.indicator (Mnext p m n J hJ) U) := by
  classical
  have hprob := arrayMeasure_isProbabilityMeasure N
  haveI := hprob
  have hp : 1 / 2 ≤ p := le_of_lt hp0
  have hp1' : p ≤ 1 := le_of_lt hp1
  have hsubj : ∀ j ∈ J, A₀ ⊆ {U | 0 ≤ X p m U n j} := fun j _ U hU => (hsub hU).1 j
  have hper : ∀ j ∈ J, condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => A₀.indicator (fun U => HA p m U n Jᶜ (X p m U (n + 1) j)) U)
      =ᵐ[arrayMeasure N] fun U => A₀.indicator
        (fun U => 1 + corr p m U n Jᶜ j + HA p m U n Jᶜ (X p m U n j)) U :=
    fun j hj => condExp_indicator_HA_next hp0 hp1 m n Jᶜ j hA₀ (hsubj j hj)
  have hint : ∀ j ∈ J, Integrable (fun U : Array N =>
      A₀.indicator (fun U => HA p m U n Jᶜ (X p m U (n + 1) j)) U) (arrayMeasure N) :=
    fun j _ => (integrable_HA_X hp hp1' m n (n + 1) Jᶜ j).indicator
      (((posFilt N p m).le n) A₀ hA₀)
  have hmeas : ∀ j ∈ J, Measurable (fun U : Array N =>
      A₀.indicator (fun U => HA p m U n Jᶜ (X p m U (n + 1) j)) U) :=
    fun j _ => (measurable_HA_random_site p m n Jᶜ (fun U => X p m U (n + 1) j)
      (measurable_X_ambient p m (n + 1) j) (n + 1)
      (fun U => SwarmM3.abs_X_le p m U (n + 1) j)).indicator
      (((posFilt N p m).le n) A₀ hA₀)
  have hintsup : Integrable (fun U : Array N =>
      J.sup' hJ (fun j => A₀.indicator (fun U => HA p m U n Jᶜ (X p m U (n + 1) j)) U))
      (arrayMeasure N) :=
    integrable_sup'_fun J hJ hint hmeas
  have hsup := SwarmM3.condExp_sup'_le (N := N) p m n J hJ hint hintsup
  have hLHS : (fun U => A₀.indicator (Cmax p m n J hJ) U)
      =ᵐ[arrayMeasure N] (fun U => J.sup' hJ (fun j =>
        condExp (posFilt N p m n) (arrayMeasure N)
          (fun U => A₀.indicator (fun U => HA p m U n Jᶜ (X p m U (n + 1) j)) U) U)) := by
    have h1 : (fun U => J.sup' hJ (fun j =>
        condExp (posFilt N p m n) (arrayMeasure N)
          (fun U => A₀.indicator (fun U => HA p m U n Jᶜ (X p m U (n + 1) j)) U) U))
        =ᵐ[arrayMeasure N] (fun U => J.sup' hJ (fun j => A₀.indicator
          (fun U => 1 + corr p m U n Jᶜ j + HA p m U n Jᶜ (X p m U n j)) U)) :=
      ae_sup'_congr J hJ hper
    have h2 : (fun U => J.sup' hJ (fun j => A₀.indicator
          (fun U => 1 + corr p m U n Jᶜ j + HA p m U n Jᶜ (X p m U n j)) U))
        = fun U => A₀.indicator (Cmax p m n J hJ) U :=
      (indicator_sup' J hJ A₀
        (fun j U => 1 + corr p m U n Jᶜ j + HA p m U n Jᶜ (X p m U n j))).symm
    exact (Filter.EventuallyEq.of_eq h2).symm.trans h1.symm
  have hRHS : condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => J.sup' hJ (fun j =>
        A₀.indicator (fun U => HA p m U n Jᶜ (X p m U (n + 1) j)) U))
      =ᵐ[arrayMeasure N] condExp (posFilt N p m n) (arrayMeasure N)
        (fun U => A₀.indicator (Mnext p m n J hJ) U) := by
    refine condExp_congr_ae (Filter.EventuallyEq.of_eq ?_)
    exact (indicator_sup' J hJ A₀ (fun j U => HA p m U n Jᶜ (X p m U (n + 1) j))).symm
  refine hLHS.le.trans ?_
  refine hsup.trans_eq ?_
  exact hRHS

/-! ### 10. The pointwise algebraic core of `(Wdrift)` on `(sep)` -/

theorem mnow_add_one_le_cmax {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ) (U : Array N)
    (J : Finset (Fin N)) (hJ : J.Nonempty) (h0 : ∀ j, 0 ≤ X p m U n j) :
    Mnow p m n J hJ U + 1 ≤ Cmax p m n J hJ U := by
  have hpos := wA_pos p m U hp n Jᶜ
  have hone := wA_le_one p m U hp1 n Jᶜ
  have hterm : ∀ j : Fin N, 0 < hfix (wA p m U n Jᶜ) (X p m U n j).toNat
      + hprev (wA p m U n Jᶜ) (X p m U n j).toNat := by
    intro j
    have h1 := one_le_hfix (wA p m U n Jᶜ) hpos hone (X p m U n j).toNat
    have h2 := one_le_hprev hpos hone (X p m U n j).toNat
    linarith
  have hcorr : ∀ j ∈ J, 0 ≤ corr p m U n Jᶜ j := by
    intro j hj
    have hα := wA_le_rightProbability_of_J p m U hp (J := J) hj (h0 j)
    have ht := hterm j
    simp only [corr]
    exact mul_nonneg (by linarith) (le_of_lt ht)
  have hstep : J.sup' hJ (fun j => HA p m U n Jᶜ (X p m U n j) + 1) ≤ Cmax p m n J hJ U := by
    refine Finset.sup'_le hJ _ fun j hj => ?_
    have h1 : HA p m U n Jᶜ (X p m U n j) + 1 ≤ 1 + corr p m U n Jᶜ j
        + HA p m U n Jᶜ (X p m U n j) := by linarith [hcorr j hj]
    exact le_trans h1 (Finset.le_sup' (fun j => 1 + corr p m U n Jᶜ j
      + HA p m U n Jᶜ (X p m U n j)) hj)
  have hadd := SepGroup.maximumOn_add_const hJ (fun j => HA p m U n Jᶜ (X p m U n j)) 1
  have hM : Mnow p m n J hJ U + 1
      = J.sup' hJ (fun j => HA p m U n Jᶜ (X p m U n j) + 1) := by
    rw [Mnow]
    exact hadd.symm
  rw [hM]
  exact hstep

theorem pointwise_key {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ) (U : Array N)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hsep : Sep p m U n I J) :
    1 + Cavg p m n I J U + Anow p m n I J U - Cmax p m n J hJ U
        - WA p m U n I J hI hJ ≤ Cavg p m n I J U := by
  have h := mnow_add_one_le_cmax (p := p) hp hp1 m n U J hJ (fun j => hsep.1 j)
  have hWA := WA_eq p m U n I J hI hJ
  linarith

/-! ### 11. Two general purpose helpers for the a.e. algebra -/

theorem condExp_sub_sub {F : MeasurableSpace (Array N)} {f g h : Array N → ℝ}
    (hf : Integrable f (arrayMeasure N)) (hg : Integrable g (arrayMeasure N))
    (hh : Integrable h (arrayMeasure N)) :
    condExp F (arrayMeasure N) (f - g - h)
      =ᵐ[arrayMeasure N] (condExp F (arrayMeasure N) f - condExp F (arrayMeasure N) g)
        - condExp F (arrayMeasure N) h := by
  have h1 : condExp F (arrayMeasure N) (f - g - h)
      =ᵐ[arrayMeasure N] condExp F (arrayMeasure N) (f - g) - condExp F (arrayMeasure N) h :=
    condExp_sub (hf.sub hg) hh F
  have h2 : condExp F (arrayMeasure N) (f - g)
      =ᵐ[arrayMeasure N] condExp F (arrayMeasure N) f - condExp F (arrayMeasure N) g :=
    condExp_sub hf hg F
  refine h1.trans ?_
  have hrefl : condExp F (arrayMeasure N) h =ᵐ[arrayMeasure N] condExp F (arrayMeasure N) h :=
    Filter.EventuallyEq.rfl
  exact h2.sub hrefl

theorem le_of_ae_decomp {f A B Z E1 E2 E3 g : Array N → ℝ}
    (h1 : f =ᵐ[arrayMeasure N] E1 - E2 - E3)
    (h2 : E1 =ᵐ[arrayMeasure N] A) (h3 : B ≤ᵐ[arrayMeasure N] E2)
    (h4 : E3 =ᵐ[arrayMeasure N] Z) (h5 : (fun U => A U - B U - Z U) ≤ᵐ[arrayMeasure N] g) :
    f ≤ᵐ[arrayMeasure N] g := by
  have hle : (fun U => E1 U - E2 U - E3 U) ≤ᵐ[arrayMeasure N] fun U => A U - B U - Z U := by
    filter_upwards [h2, h3, h4] with U hU2 hU3 hU4
    rw [hU2, hU4]
    linarith
  exact h1.trans_le hle |>.trans h5

/-! ### 12. `(Wdrift)` at `condExp` level with the explicit correction -/

theorem indicator_triple_eq (p : ℝ) (m n : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty)
    (hJ : J.Nonempty) (A₀ : Set (Array N)) :
    (fun U => A₀.indicator (fun U => Anext p m n I J U - Mnext p m n J hJ U
        - WA p m U n I J hI hJ) U)
      = (fun U => A₀.indicator (Anext p m n I J) U - A₀.indicator (Mnext p m n J hJ) U
          - A₀.indicator (fun U => WA p m U n I J hI hJ) U) := by
  funext U
  by_cases hU : U ∈ A₀
  · simp only [Set.indicator_of_mem hU, Pi.sub_apply]
  · simp only [Set.indicator_of_notMem hU, Pi.sub_apply, sub_zero]

theorem condExp_indicator_drift_le_cavg {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m n : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty)
    {A₀ : Set (Array N)} (hA₀ : MeasurableSet[posFilt N p m n] A₀)
    (hsub : A₀ ⊆ {U | SepSet p m n I J U}) :
    condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => A₀.indicator (fun U => Anext p m n I J U - Mnext p m n J hJ U
        - WA p m U n I J hI hJ) U)
    ≤ᵐ[arrayMeasure N] fun U => A₀.indicator (fun U => Cavg p m n I J U) U := by
  classical
  have hprob := arrayMeasure_isProbabilityMeasure N
  haveI := hprob
  have hp : 1 / 2 ≤ p := le_of_lt hp0
  have hp1' : p ≤ 1 := le_of_lt hp1
  have hAn : Integrable (Anext p m n I J) (arrayMeasure N) := integrable_Anext hp hp1' m n I J
  have hMn : Integrable (Mnext p m n J hJ) (arrayMeasure N) := integrable_Mnext hp hp1' m n J hJ
  have hWA : Integrable (fun U => WA p m U n I J hI hJ) (arrayMeasure N) := by
    have h := (integrable_Anow hp hp1' m n I J).sub (integrable_Mnow hp hp1' m n J hJ)
    have heq : (fun U => WA p m U n I J hI hJ)
        = fun U => Anow p m n I J U - Mnow p m n J hJ U := funext fun U => WA_eq p m U n I J hI hJ
    rw [heq]
    exact h
  have hx : Integrable (fun U => A₀.indicator (Anext p m n I J) U) (arrayMeasure N) :=
    hAn.indicator (((posFilt N p m).le n) A₀ hA₀)
  have hy : Integrable (fun U => A₀.indicator (Mnext p m n J hJ) U) (arrayMeasure N) :=
    hMn.indicator (((posFilt N p m).le n) A₀ hA₀)
  have hz : Integrable (fun U => A₀.indicator (fun U => WA p m U n I J hI hJ) U) (arrayMeasure N) :=
    hWA.indicator (((posFilt N p m).le n) A₀ hA₀)
  -- the a.e. decomposition
  have h1 : condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => A₀.indicator (fun U => Anext p m n I J U - Mnext p m n J hJ U
        - WA p m U n I J hI hJ) U)
      =ᵐ[arrayMeasure N] (condExp (posFilt N p m n) (arrayMeasure N)
          (fun U => A₀.indicator (Anext p m n I J) U))
        - (condExp (posFilt N p m n) (arrayMeasure N)
          (fun U => A₀.indicator (Mnext p m n J hJ) U))
        - (condExp (posFilt N p m n) (arrayMeasure N)
          (fun U => A₀.indicator (fun U => WA p m U n I J hI hJ) U)) := by
    refine (condExp_congr_ae (Filter.EventuallyEq.of_eq
      (indicator_triple_eq p m n I J hI hJ A₀))).trans ?_
    exact condExp_sub_sub (F := posFilt N p m n) hx hy hz
  have h2 := condExp_indicator_Anext hp0 hp1 m n I J hI hA₀ hsub
  have h3 := condExp_indicator_Mnext_ge hp0 hp1 m n I J hJ hA₀ hsub
  have h4 : condExp (posFilt N p m n) (arrayMeasure N)
        (fun U => A₀.indicator (fun U => WA p m U n I J hI hJ) U)
      =ᵐ[arrayMeasure N] fun U => A₀.indicator (fun U => WA p m U n I J hI hJ) U :=
    Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable ((posFilt N p m).le n)
      (((measurable_WA_posFilt p m n I J hI hJ).indicator hA₀)).stronglyMeasurable hz)
  have h5 : (fun U => A₀.indicator (fun U => 1 + Cavg p m n I J U + Anow p m n I J U) U
        - A₀.indicator (Cmax p m n J hJ) U
        - A₀.indicator (fun U => WA p m U n I J hI hJ) U)
      ≤ᵐ[arrayMeasure N] fun U => A₀.indicator (fun U => Cavg p m n I J U) U := by
    refine Filter.Eventually.of_forall fun U => ?_
    by_cases hU : U ∈ A₀
    · simp only [Set.indicator_of_mem hU]
      exact pointwise_key hp hp1' m n U I J hI hJ (hsub hU)
    · simp only [Set.indicator_of_notMem hU]
      norm_num
  exact le_of_ae_decomp h1 h2 h3 h4 h5

/-! ### 13. Sign of the correction, and `(Wdrift)` at `condExp` level -/

theorem one_lt_hterm (p : ℝ) (m n : ℕ) (U : Array N) (A : Finset (Fin N)) (k : Fin N)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) :
    0 < hfix (wA p m U n A) (X p m U n k).toNat + hprev (wA p m U n A) (X p m U n k).toNat := by
  have h1 := one_le_hfix (wA p m U n A) (wA_pos p m U hp n A) (wA_le_one p m U hp1 n A)
    (X p m U n k).toNat
  have h2 := one_le_hprev (wA_pos p m U hp n A) (wA_le_one p m U hp1 n A) (X p m U n k).toNat
  linarith

theorem corr_nonpos_of_sep {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ} {U : Array N}
    {I J : Finset (Fin N)} (hid : Disjoint I J) (hsep : Sep p m U n I J) {i : Fin N}
    (hi : i ∈ I) :
    corr p m U n Jᶜ i ≤ 0 := by
  have hα := rightProbability_le_wA_of_sep p m U hp hid hsep hi
  have ht := one_lt_hterm p m n U Jᶜ i hp hp1
  simp only [corr]
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt ht)

theorem cavg_nonpos {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ) (U : Array N)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hid : Disjoint I J) (hsep : Sep p m U n I J) :
    Cavg p m n I J U ≤ 0 := by
  have hsum : (∑ i ∈ I, corr p m U n Jᶜ i) ≤ 0 :=
    Finset.sum_nonpos fun i hi => corr_nonpos_of_sep hp hp1 hid hsep hi
  have hcard : (0 : ℝ) ≤ (I.card : ℝ) := Nat.cast_nonneg _
  have h := div_nonpos_of_nonpos_of_nonneg hsum hcard
  simpa only [Cavg, Swarming.Group.average] using h

theorem condExp_indicator_drift_le_zero {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m n : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {A₀ : Set (Array N)} (hA₀ : MeasurableSet[posFilt N p m n] A₀)
    (hsub : A₀ ⊆ {U | SepSet p m n I J U}) :
    condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => A₀.indicator (fun U => Anext p m n I J U - Mnext p m n J hJ U
        - WA p m U n I J hI hJ) U)
    ≤ᵐ[arrayMeasure N] 0 := by
  refine (condExp_indicator_drift_le_cavg hp0 hp1 m n I J hI hJ hA₀ hsub).trans ?_
  refine Filter.Eventually.of_forall fun U => ?_
  change A₀.indicator (fun U => Cavg p m n I J U) U ≤ (0 : ℝ)
  by_cases hU : U ∈ A₀
  · rw [Set.indicator_of_mem hU]
    exact cavg_nonpos (le_of_lt hp0) (le_of_lt hp1) m n U I J hI hid (hsub hU)
  · rw [Set.indicator_of_notMem hU]

/-! ### 14. The actual `W_{n+1}`: `WA_step` inside the conditional expectation -/

theorem integrable_WA {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m k : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) :
    Integrable (fun U => WA p m U k I J hI hJ) (arrayMeasure N) := by
  have h := (integrable_Anow hp hp1 m k I J).sub (integrable_Mnow hp hp1 m k J hJ)
  have heq : (fun U => WA p m U k I J hI hJ)
      = fun U => Anow p m k I J U - Mnow p m k J hJ U := funext fun U => WA_eq p m U k I J hI hJ
  rw [heq]
  exact h

theorem indicator_WA_step_le {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) {A₀ : Set (Array N)}
    (hsub : A₀ ⊆ {U | SepSet p m n I J U}) :
    (fun U => A₀.indicator (fun U => WA p m U (n + 1) I J hI hJ
        - WA p m U n I J hI hJ) U)
      ≤ᵐ[arrayMeasure N] (fun U => A₀.indicator (fun U => Anext p m n I J U
        - Mnext p m n J hJ U - WA p m U n I J hI hJ) U) := by
  refine Filter.Eventually.of_forall fun U => ?_
  change A₀.indicator (fun U => WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ) U
    ≤ A₀.indicator (fun U => Anext p m n I J U - Mnext p m n J hJ U
      - WA p m U n I J hI hJ) U
  by_cases hU : U ∈ A₀
  · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU]
    have hstep : WA p m U (n + 1) I J hI hJ
        ≤ Anext p m n I J U - Mnext p m n J hJ U :=
      WA_step p m U hp hp1 (n := n) hI hJ (hsub hU)
    linarith
  · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]

theorem condExp_indicator_WA_drift_le_cavg {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m n : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty)
    {A₀ : Set (Array N)} (hA₀ : MeasurableSet[posFilt N p m n] A₀)
    (hsub : A₀ ⊆ {U | SepSet p m n I J U}) :
    condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => A₀.indicator (fun U => WA p m U (n + 1) I J hI hJ
        - WA p m U n I J hI hJ) U)
    ≤ᵐ[arrayMeasure N] fun U => A₀.indicator (fun U => Cavg p m n I J U) U := by
  classical
  have hprob := arrayMeasure_isProbabilityMeasure N
  haveI := hprob
  have hp : 1 / 2 ≤ p := le_of_lt hp0
  have hp1' : p ≤ 1 := le_of_lt hp1
  have hsplit := integrable_WA hp hp1' m (n + 1) I J hI hJ
  have hWa : Integrable (fun U => WA p m U n I J hI hJ) (arrayMeasure N) :=
    integrable_WA hp hp1' m n I J hI hJ
  have hAn : Integrable (Anext p m n I J) (arrayMeasure N) := integrable_Anext hp hp1' m n I J
  have hMn : Integrable (Mnext p m n J hJ) (arrayMeasure N) := integrable_Mnext hp hp1' m n J hJ
  have hint1 : Integrable (fun U => A₀.indicator (fun U => WA p m U (n + 1) I J hI hJ
      - WA p m U n I J hI hJ) U) (arrayMeasure N) :=
    (hsplit.sub hWa).indicator (((posFilt N p m).le n) A₀ hA₀)
  have hint2 : Integrable (fun U => A₀.indicator (fun U => Anext p m n I J U
      - Mnext p m n J hJ U - WA p m U n I J hI hJ) U) (arrayMeasure N) :=
    ((hAn.sub hMn).sub hWa).indicator (((posFilt N p m).le n) A₀ hA₀)
  exact (condExp_mono hint1 hint2 (indicator_WA_step_le hp hp1' m n I J hI hJ hsub)).trans
    (condExp_indicator_drift_le_cavg hp0 hp1 m n I J hI hJ hA₀ hsub)

theorem condExp_indicator_WA_drift_le_zero {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m n : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {A₀ : Set (Array N)} (hA₀ : MeasurableSet[posFilt N p m n] A₀)
    (hsub : A₀ ⊆ {U | SepSet p m n I J U}) :
    condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => A₀.indicator (fun U => WA p m U (n + 1) I J hI hJ
        - WA p m U n I J hI hJ) U)
    ≤ᵐ[arrayMeasure N] 0 := by
  refine (condExp_indicator_WA_drift_le_cavg hp0 hp1 m n I J hI hJ hA₀ hsub).trans ?_
  refine Filter.Eventually.of_forall fun U => ?_
  change A₀.indicator (fun U => Cavg p m n I J U) U ≤ (0 : ℝ)
  by_cases hU : U ∈ A₀
  · rw [Set.indicator_of_mem hU]
    exact cavg_nonpos (le_of_lt hp0) (le_of_lt hp1) m n U I J hI hid (hsub hU)
  · rw [Set.indicator_of_notMem hU]

/-! ### 15. The paper's statements: `A₀` is the separation event -/

/-- **(Wstrict) as a conditional-expectation inequality on the separation event.** -/
theorem Wstrict_sep {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m n : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) :
    condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => ({U | SepSet p m n I J U}).indicator
        (fun U => WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ) U)
    ≤ᵐ[arrayMeasure N] fun U => ({U | SepSet p m n I J U}).indicator
        (fun U => Cavg p m n I J U) U :=
  condExp_indicator_WA_drift_le_cavg hp0 hp1 m n I J hI hJ
    (measurableSet_sepSet p m n I J) (fun _ h => h)

/-- **(Wdrift): the conditional mean of `W_{n+1}^{I,J} - W_n^{I,J}` is nonpositive on (sep).** -/
theorem Wdrift_sep {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m n : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J) :
    condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => ({U | SepSet p m n I J U}).indicator
        (fun U => WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ) U)
    ≤ᵐ[arrayMeasure N] 0 :=
  condExp_indicator_WA_drift_le_zero hp0 hp1 m n I J hI hJ hid
    (measurableSet_sepSet p m n I J) (fun _ h => h)

/-- **Integrated form of `(Wdrift)`:** `E[1_{(sep)} (W_{n+1}^{I,J} - W_n^{I,J})] <= 0`. -/
theorem integral_Wdrift_sep_le_zero {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m n : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J) :
    ∫ U, ({U | SepSet p m n I J U}).indicator
        (fun U => WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ) U
        ∂(arrayMeasure N) ≤ 0 := by
  have hprob := arrayMeasure_isProbabilityMeasure N
  haveI := hprob
  have hp : 1 / 2 ≤ p := le_of_lt hp0
  have hp1' : p ≤ 1 := le_of_lt hp1
  have hint : Integrable (fun U => ({U | SepSet p m n I J U}).indicator
      (fun U => WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ) U)
      (arrayMeasure N) :=
    ((integrable_WA hp hp1' m (n + 1) I J hI hJ).sub (integrable_WA hp hp1' m n I J hI hJ)).indicator
      (((posFilt N p m).le n) {U | SepSet p m n I J U} (measurableSet_sepSet p m n I J))
  have hce : ∫ U, condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => ({U | SepSet p m n I J U}).indicator
        (fun U => WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ) U) U
      ∂(arrayMeasure N)
      = ∫ U, ({U | SepSet p m n I J U}).indicator
        (fun U => WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ) U ∂(arrayMeasure N) :=
    integral_condExp ((posFilt N p m).le n)
  have hcondint : Integrable (fun U => condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => ({U | SepSet p m n I J U}).indicator
        (fun U => WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ) U) U)
      (arrayMeasure N) := by
    haveI := hint
    exact integrable_condExp
  have hmono : ∫ U, condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => ({U | SepSet p m n I J U}).indicator
        (fun U => WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ) U) U ∂(arrayMeasure N)
      ≤ ∫ U, (0 : ℝ) ∂(arrayMeasure N) :=
    integral_mono_ae hcondint (integrable_const 0) (Wdrift_sep hp0 hp1 m n I J hI hJ hid)
  rw [← hce]
  simpa using hmono

/-! ### 16. The paper's `Q^{I,J}` martingale correction -/

/-- `StronglyMeasurable` passes to finer σ-algebras (the direction needed for filtrations). -/
theorem stronglyMeasurable_mono_filt {F F' : MeasurableSpace (Array N)} {f : Array N → ℝ}
    (h : StronglyMeasurable[F] f) (hle : F ≤ F') : StronglyMeasurable[F'] f :=
  (h.measurable.mono hle le_rfl).stronglyMeasurable

/-- The raw increment `1_{(sep)}(W_{n+1}^{I,J} - W_n^{I,J})` of the paper's `Q^{I,J}`. -/
noncomputable def Qraw (p : ℝ) (m : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty)
    (hJ : J.Nonempty) (n : ℕ) (U : Array N) : ℝ :=
  ({U | SepSet p m n I J U}).indicator
    (fun U => WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ) U

/-- The paper's `Q^{I,J}` increment: raw `(sep)`-increment minus its conditional mean. -/
noncomputable def dQ (p : ℝ) (m : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty)
    (hJ : J.Nonempty) (n : ℕ) (U : Array N) : ℝ :=
  Qraw p m I J hI hJ n U
    - condExp (posFilt N p m n) (arrayMeasure N) (Qraw p m I J hI hJ n) U

/-- The paper's cumulative correction `Q^{I,J}_n = sum_{k<n} dQ_k`. -/
noncomputable def Q (p : ℝ) (m : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty)
    (hJ : J.Nonempty) (n : ℕ) (U : Array N) : ℝ :=
  ∑ k ∈ Finset.range n, dQ p m I J hI hJ k U

theorem Q_zero (p : ℝ) (m : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty)
    (U : Array N) : Q p m I J hI hJ 0 U = 0 := by
  simp [Q]

theorem Q_succ (p : ℝ) (m : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty)
    (n : ℕ) (U : Array N) :
    Q p m I J hI hJ (n + 1) U = Q p m I J hI hJ n U + dQ p m I J hI hJ n U := by
  simp only [Q, Finset.sum_range_succ]

theorem measurable_Qraw_succ (p : ℝ) (m n : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty)
    (hJ : J.Nonempty) :
    Measurable[posFilt N p m (n + 1)] (Qraw p m I J hI hJ n) := by
  have h1 : Measurable[posFilt N p m (n + 1)] (fun U => WA p m U (n + 1) I J hI hJ) :=
    measurable_WA_posFilt p m (n + 1) I J hI hJ
  have h2 : Measurable[posFilt N p m (n + 1)] (fun U => WA p m U n I J hI hJ) :=
    (measurable_WA_posFilt p m n I J hI hJ).mono ((posFilt N p m).mono (Nat.le_succ n)) le_rfl
  have h3 : MeasurableSet[posFilt N p m (n + 1)] {U : Array N | SepSet p m n I J U} :=
    ((posFilt N p m).mono (Nat.le_succ n)) {U : Array N | SepSet p m n I J U}
      (measurableSet_sepSet p m n I J)
  exact (h1.sub h2).indicator h3

theorem integrable_Qraw {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ) (I J : Finset (Fin N))
    (hI : I.Nonempty) (hJ : J.Nonempty) :
    Integrable (Qraw p m I J hI hJ n) (arrayMeasure N) :=
  ((integrable_WA hp hp1 m (n + 1) I J hI hJ).sub (integrable_WA hp hp1 m n I J hI hJ)).indicator
    (((posFilt N p m).le n) {U : Array N | SepSet p m n I J U} (measurableSet_sepSet p m n I J))

theorem integrable_condExp_Qraw {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) :
    Integrable (fun U => condExp (posFilt N p m n) (arrayMeasure N) (Qraw p m I J hI hJ n) U)
      (arrayMeasure N) := by
  haveI := integrable_Qraw hp hp1 m n I J hI hJ
  exact integrable_condExp

theorem integrable_dQ {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ) (I J : Finset (Fin N))
    (hI : I.Nonempty) (hJ : J.Nonempty) :
    Integrable (dQ p m I J hI hJ n) (arrayMeasure N) :=
  (integrable_Qraw hp hp1 m n I J hI hJ).sub (integrable_condExp_Qraw hp hp1 m n I J hI hJ)

theorem stronglyMeasurable_dQ (p : ℝ) (m n : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty)
    (hJ : J.Nonempty) :
    StronglyMeasurable[posFilt N p m (n + 1)] (dQ p m I J hI hJ n) := by
  have hraw : StronglyMeasurable[posFilt N p m (n + 1)] (Qraw p m I J hI hJ n) :=
    (measurable_Qraw_succ p m n I J hI hJ).stronglyMeasurable
  have hce : StronglyMeasurable[posFilt N p m (n + 1)]
      (fun U => condExp (posFilt N p m n) (arrayMeasure N) (Qraw p m I J hI hJ n) U) :=
    stronglyMeasurable_mono_filt (stronglyMeasurable_condExp : StronglyMeasurable[posFilt N p m n]
      (fun U => condExp (posFilt N p m n) (arrayMeasure N) (Qraw p m I J hI hJ n) U))
      ((posFilt N p m).mono (Nat.le_succ n))
  exact hraw.sub hce

/-- **`dQ_n` is a martingale difference**: its conditional mean given `F_n` vanishes. -/
theorem condExp_dQ {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ) (I J : Finset (Fin N))
    (hI : I.Nonempty) (hJ : J.Nonempty) :
    condExp (posFilt N p m n) (arrayMeasure N) (dQ p m I J hI hJ n)
      =ᵐ[arrayMeasure N] 0 := by
  have hX := integrable_Qraw hp hp1 m n I J hI hJ
  have hY := integrable_condExp_Qraw hp hp1 m n I J hI hJ
  have hsub : condExp (posFilt N p m n) (arrayMeasure N) (dQ p m I J hI hJ n)
      =ᵐ[arrayMeasure N] condExp (posFilt N p m n) (arrayMeasure N) (Qraw p m I J hI hJ n)
        - condExp (posFilt N p m n) (arrayMeasure N)
            (fun U => condExp (posFilt N p m n) (arrayMeasure N) (Qraw p m I J hI hJ n) U) :=
    condExp_sub hX hY _
  have hpull : condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => condExp (posFilt N p m n) (arrayMeasure N) (Qraw p m I J hI hJ n) U)
      = fun U => condExp (posFilt N p m n) (arrayMeasure N) (Qraw p m I J hI hJ n) U :=
    condExp_of_stronglyMeasurable ((posFilt N p m).le n) stronglyMeasurable_condExp hY
  refine hsub.trans ?_
  rw [hpull]
  filter_upwards with U
  simp

theorem stronglyAdapted_Q (p : ℝ) (m : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty)
    (hJ : J.Nonempty) : StronglyAdapted (posFilt N p m) (Q p m I J hI hJ) := by
  intro n
  show StronglyMeasurable[posFilt N p m n]
    (fun U => ∑ k ∈ Finset.range n, dQ p m I J hI hJ k U)
  have hsum : (fun U : Array N => ∑ k ∈ Finset.range n, dQ p m I J hI hJ k U)
      = ∑ k ∈ Finset.range n, fun U => dQ p m I J hI hJ k U := by
    funext U
    rw [Finset.sum_apply]
  rw [hsum]
  refine Finset.stronglyMeasurable_sum _ fun k hk => ?_
  have hk' : k < n := Finset.mem_range.mp hk
  exact stronglyMeasurable_mono_filt (stronglyMeasurable_dQ p m k I J hI hJ)
    ((posFilt N p m).mono (Nat.succ_le_of_lt hk'))

theorem integrable_Q {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ) (I J : Finset (Fin N))
    (hI : I.Nonempty) (hJ : J.Nonempty) :
    Integrable (Q p m I J hI hJ n) (arrayMeasure N) := by
  show Integrable (fun U => ∑ k ∈ Finset.range n, dQ p m I J hI hJ k U) (arrayMeasure N)
  exact integrable_finsetSum _ fun k _ => integrable_dQ hp hp1 m k I J hI hJ

theorem condExp_Q_succ {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ) (I J : Finset (Fin N))
    (hI : I.Nonempty) (hJ : J.Nonempty) :
    condExp (posFilt N p m n) (arrayMeasure N) (Q p m I J hI hJ (n + 1))
      =ᵐ[arrayMeasure N] Q p m I J hI hJ n := by
  have hprob := arrayMeasure_isProbabilityMeasure N
  haveI := hprob
  have heq : Q p m I J hI hJ (n + 1)
      = fun U => Q p m I J hI hJ n U + dQ p m I J hI hJ n U :=
    funext fun U => Q_succ p m I J hI hJ n U
  have hQ : condExp (posFilt N p m n) (arrayMeasure N) (Q p m I J hI hJ (n + 1))
      =ᵐ[arrayMeasure N] condExp (posFilt N p m n) (arrayMeasure N)
        (fun U => Q p m I J hI hJ n U + dQ p m I J hI hJ n U) :=
    condExp_congr_ae (Filter.EventuallyEq.of_eq heq)
  have h1 : condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => Q p m I J hI hJ n U + dQ p m I J hI hJ n U)
      =ᵐ[arrayMeasure N] condExp (posFilt N p m n) (arrayMeasure N) (Q p m I J hI hJ n)
        + condExp (posFilt N p m n) (arrayMeasure N) (dQ p m I J hI hJ n) :=
    condExp_add (integrable_Q hp hp1 m n I J hI hJ) (integrable_dQ hp hp1 m n I J hI hJ) _
  have h2 : condExp (posFilt N p m n) (arrayMeasure N) (Q p m I J hI hJ n)
      = Q p m I J hI hJ n :=
    condExp_of_stronglyMeasurable ((posFilt N p m).le n) ((stronglyAdapted_Q p m I J hI hJ) n)
      (integrable_Q hp hp1 m n I J hI hJ)
  have h3 := condExp_dQ hp hp1 m n I J hI hJ
  refine hQ.trans ?_
  refine h1.trans ?_
  rw [h2]
  filter_upwards [h3] with U hU
  simp only [Pi.add_apply, hU, Pi.zero_apply, add_zero]

/-- **The paper's `Q^{I,J}` is a martingale** for the actual position filtration. -/
theorem martingale_Q {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m : ℕ) (I J : Finset (Fin N))
    (hI : I.Nonempty) (hJ : J.Nonempty) :
    Martingale (Q p m I J hI hJ) (posFilt N p m) (arrayMeasure N) :=
  martingale_nat (stronglyAdapted_Q p m I J hI hJ) (fun n => integrable_Q hp hp1 m n I J hI hJ)
    (fun n => (condExp_Q_succ hp hp1 m n I J hI hJ).symm)

/-! ### 17. Paper `(Qslln)` from the log-fourth variance bound -/

/-- **The paper's `(Qslln)`.**  If the `Q^{I,J}` increments satisfy the paper's log-fourth
variance estimate `E[(dQ_k)^2] <= C log^4(k+2)`, then `Q_n = o(n)` almost surely.  This is
the paper's `(Qslln)`; the variance estimate itself is the (hcomp)/(maxmom) input that is
*not* proved here. -/
theorem Qslln_of_log_variance {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) {C : ℝ}
    (hint : ∀ k : ℕ, Integrable
      (fun U => (MartingaleLimit.inc (Q p m I J hI hJ) k U) ^ 2) (arrayMeasure N))
    (hvar : ∀ k : ℕ, ∫ U, (MartingaleLimit.inc (Q p m I J hI hJ) k U) ^ 2
      ∂(arrayMeasure N) ≤ C * (Real.log ((k : ℝ) + 2)) ^ 4) :
    ∀ᵐ U ∂(arrayMeasure N), Tendsto (fun n => Q p m I J hI hJ n U / n) atTop (𝓝 0) := by
  have hprob := arrayMeasure_isProbabilityMeasure N
  haveI := hprob
  have h := MartingaleLimit.martingale_strong_law_of_log_variance
    (martingale_Q hp hp1 m I J hI hJ) hint hvar
  filter_upwards [h] with U hU
  have h0 : Q p m I J hI hJ 0 U = 0 := Q_zero p m I J hI hJ U
  simpa [h0] using hU

/-- The running-maximum form of `(Qslln)`: `max_{t<=n} |Q_t| = o(n)` almost surely. -/
theorem Q_running_max_of_log_variance {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) {C : ℝ}
    (hint : ∀ k : ℕ, Integrable
      (fun U => (MartingaleLimit.inc (Q p m I J hI hJ) k U) ^ 2) (arrayMeasure N))
    (hvar : ∀ k : ℕ, ∫ U, (MartingaleLimit.inc (Q p m I J hI hJ) k U) ^ 2
      ∂(arrayMeasure N) ≤ C * (Real.log ((k : ℝ) + 2)) ^ 4) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ((Finset.range (n + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩
        fun t => |Q p m I J hI hJ t U|) ≤ ε * (n : ℝ) := by
  have hprob := arrayMeasure_isProbabilityMeasure N
  haveI := hprob
  exact MartingaleLimit.running_max_div (Qslln_of_log_variance hp hp1 m I J hI hJ hint hvar)

/-! ### 18. Deterministic telescoping on an interval on which `(sep)` holds -/

theorem telescope_aux {a c : ℕ → ℝ} {s : ℕ} :
    ∀ t, s ≤ t → (∀ k, s ≤ k → k < t → a (k + 1) - a k ≤ c k) →
      a t - a s ≤ ∑ k ∈ Finset.range t, c k - ∑ k ∈ Finset.range s, c k := by
  intro t hst
  induction t, hst using Nat.le_induction with
  | base =>
      intro _
      simp
  | succ n hn ih =>
      intro h
      have h1 : ∑ k ∈ Finset.range (n + 1), c k = ∑ k ∈ Finset.range n, c k + c n :=
        Finset.sum_range_succ c n
      have h2 := h n hn (Nat.lt_succ_self n)
      have h3 := ih (fun k hk hkn => h k hk (Nat.lt_succ_of_lt hkn))
      linarith

/-- **The paper's summation of `(Wdrift)`:** on any time interval on which `(sep)` holds, the
observable is bounded by its initial value plus the `Q^{I,J}` excursion. -/
theorem telescope_of_sep {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ s t : ℕ, s ≤ t →
      (∀ k, s ≤ k → k < t → SepSet p m k I J U) →
      WA p m U t I J hI hJ ≤ WA p m U s I J hI hJ
        + (Q p m I J hI hJ t U - Q p m I J hI hJ s U) := by
  have hprob := arrayMeasure_isProbabilityMeasure N
  haveI := hprob
  have hdrift : ∀ᵐ U ∂(arrayMeasure N), ∀ k : ℕ,
      condExp (posFilt N p m k) (arrayMeasure N) (Qraw p m I J hI hJ k) U ≤ 0 :=
    MeasureTheory.ae_all_iff.mpr
      (fun k => Wdrift_sep hp0 hp1 m k I J hI hJ hid)
  filter_upwards [hdrift] with U hU s t hst hsep
  have hpt : ∀ k, s ≤ k → k < t →
      WA p m U (k + 1) I J hI hJ - WA p m U k I J hI hJ ≤ dQ p m I J hI hJ k U := by
    intro k hk hkt
    have hSk : SepSet p m k I J U := hsep k hk hkt
    have hmem : U ∈ {U : Array N | SepSet p m k I J U} := hSk
    have hQraw : Qraw p m I J hI hJ k U
        = WA p m U (k + 1) I J hI hJ - WA p m U k I J hI hJ := by
      simp only [Qraw, Set.indicator_of_mem hmem]
    have hdQ : dQ p m I J hI hJ k U = Qraw p m I J hI hJ k U
        - condExp (posFilt N p m k) (arrayMeasure N) (Qraw p m I J hI hJ k) U := rfl
    have hle : condExp (posFilt N p m k) (arrayMeasure N) (Qraw p m I J hI hJ k) U ≤ 0 := hU k
    linarith
  have haux := telescope_aux (a := fun n => WA p m U n I J hI hJ)
    (c := fun n => dQ p m I J hI hJ n U) (s := s) t hst hpt
  simp only [Q] at haux ⊢
  linarith

/-! ### 19. Paper fidelity of the correction term and the crude increment bound -/

/-- The correction average is *minus* the paper's `(Wstrict)` right-hand side. -/
theorem Cavg_eq_neg {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ) (I J : Finset (Fin N))
    (hI : I.Nonempty) (U : Array N) :
    Cavg p m n I J U = - Swarming.Group.average I (fun i : Fin N =>
      (wA p m U n Jᶜ (X p m U n i).toNat
        - rightProbability p m (trajectory p m U n).ell i (X p m U n i))
      * (hfix (wA p m U n Jᶜ) (X p m U n i).toNat
        + hprev (wA p m U n Jᶜ) (X p m U n i).toNat)) := by
  rw [Cavg, Swarming.Group.average, Swarming.Group.average]
  have hsum : (∑ i ∈ I, corr p m U n Jᶜ i)
      = -∑ i ∈ I, (wA p m U n Jᶜ (X p m U n i).toNat
          - rightProbability p m (trajectory p m U n).ell i (X p m U n i))
        * (hfix (wA p m U n Jᶜ) (X p m U n i).toNat
          + hprev (wA p m U n Jᶜ) (X p m U n i).toNat) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [corr, alphaFun_eq_rightProb]
    ring
  rw [hsum, neg_div]

/-- Uniform bound for the observable: `|W_k^{I,J}| <= 2 k(2k+3) + 6`. -/
theorem abs_WA_le {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m k : ℕ) (U : Array N)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) :
    |WA p m U k I J hI hJ| ≤ 2 * ((k : ℝ) * (2 * (k : ℝ) + 3) + 3) := by
  set B : ℝ := (k : ℝ) * (2 * (k : ℝ) + 3) + 3 with hB
  have hpt : ∀ i : Fin N, |HA p m U k Jᶜ (X p m U k i)| ≤ B := fun i =>
    abs_HA_le hp hp1 m k U Jᶜ (SwarmM3.abs_X_le p m U k i)
  have hcard : (0 : ℝ) < (I.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hI
  have hsumabs : |∑ i ∈ I, HA p m U k Jᶜ (X p m U k i)| ≤ (I.card : ℝ) * B := by
    calc |∑ i ∈ I, HA p m U k Jᶜ (X p m U k i)|
        ≤ ∑ i ∈ I, |HA p m U k Jᶜ (X p m U k i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ I, B := Finset.sum_le_sum (fun i _ => hpt i)
      _ = (I.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
  have havg : |Swarming.Group.average I (fun i => HA p m U k Jᶜ (X p m U k i))| ≤ B := by
    rw [Swarming.Group.average, abs_div, abs_of_pos hcard, div_le_iff₀ hcard]
    calc |∑ i ∈ I, HA p m U k Jᶜ (X p m U k i)| ≤ (I.card : ℝ) * B := hsumabs
      _ = B * (I.card : ℝ) := by ring
  have hmax : |Swarming.Group.maximumOn J hJ (fun j => HA p m U k Jᶜ (X p m U k j))| ≤ B := by
    obtain ⟨j₀, hj₀, hjeq⟩ := Finset.exists_mem_eq_sup' hJ (fun j => HA p m U k Jᶜ (X p m U k j))
    rw [Swarming.Group.maximumOn, hjeq]
    exact hpt j₀
  have hWA : WA p m U k I J hI hJ
      = Swarming.Group.average I (fun i => HA p m U k Jᶜ (X p m U k i))
        - Swarming.Group.maximumOn J hJ (fun j => HA p m U k Jᶜ (X p m U k j)) := rfl
  rw [hWA]
  calc |Swarming.Group.average I (fun i => HA p m U k Jᶜ (X p m U k i))
        - Swarming.Group.maximumOn J hJ (fun j => HA p m U k Jᶜ (X p m U k j))|
      ≤ |Swarming.Group.average I (fun i => HA p m U k Jᶜ (X p m U k i))|
        + |Swarming.Group.maximumOn J hJ (fun j => HA p m U k Jᶜ (X p m U k j))| := abs_sub _ _
    _ ≤ B + B := add_le_add havg hmax
    _ = 2 * ((k : ℝ) * (2 * (k : ℝ) + 3) + 3) := by rw [hB]; ring

/-- **The crude one-step bound.**  On any path (in particular on `(sep)`),
`|W_{n+1}^{I,J} - W_n^{I,J}| <= 2 (n+1)(2n+5) + 2 n(2n+3) + 12 = O(n^2)`.  This is *not*
the paper's `(hcomp)` estimate `O((1 + max(h_j + G_j))^2)`, whose mean is `O(log^4 n)`; the
quadratic pointwise bound sums to `O(n^3)` and therefore cannot drive the martingale strong
law.  The gap between this bound and `(hcomp)` is the exact missing second-moment input. -/
theorem abs_WA_drift_le {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ) (U : Array N)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) :
    |WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ|
      ≤ 2 * (((n + 1 : ℕ) : ℝ) * (2 * ((n + 1 : ℕ) : ℝ) + 3) + 3)
        + 2 * ((n : ℝ) * (2 * (n : ℝ) + 3) + 3) := by
  have h1 := abs_WA_le hp hp1 m (n + 1) U I J hI hJ
  have h2 := abs_WA_le hp hp1 m n U I J hI hJ
  have := abs_sub (WA p m U (n + 1) I J hI hJ) (WA p m U n I J hI hJ)
  linarith

/-! ### 20. The paper's quantitative strict drift `-(2p-1)/|I|` -/

/-- At a site that is excited for the group (`w_n^{J^c}(x) = p`) but not for the walker
(`alpha_n^i = 1/2`), the correction term is at most `-(2p-1)`. -/
theorem corr_le_neg_of_excited {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ) (U : Array N)
    (J : Finset (Fin N)) {i : Fin N}
    (hα : rightProbability p m (trajectory p m U n).ell i (X p m U n i) = 1 / 2)
    (hw : wA p m U n Jᶜ (X p m U n i).toNat = p) :
    corr p m U n Jᶜ i ≤ -(2 * p - 1) := by
  have h1 := one_le_hfix (wA p m U n Jᶜ) (wA_pos p m U hp n Jᶜ) (wA_le_one p m U hp1 n Jᶜ)
    (X p m U n i).toNat
  have h2 := one_le_hprev (wA_pos p m U hp n Jᶜ) (wA_le_one p m U hp1 n Jᶜ) (X p m U n i).toNat
  simp only [corr, alphaFun_eq_rightProb, hα, hw]
  nlinarith

/-- **The paper's strict drift bound** (used at the times `Γ_y^A` in the proof of `(diam)`):
if, on (sep), the walker `i₀ ∈ I` sits at a site that is excited for the group but not for
itself, then the correction average is at most `-(2p-1)/|I|`. -/
theorem cavg_le_neg_card {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ) (U : Array N)
    (I J : Finset (Fin N)) (hI : I.Nonempty) {i₀ : Fin N} (hi₀ : i₀ ∈ I)
    (hα : rightProbability p m (trajectory p m U n).ell i₀ (X p m U n i₀) = 1 / 2)
    (hw : wA p m U n Jᶜ (X p m U n i₀).toNat = p)
    (hnonpos : ∀ i ∈ I, corr p m U n Jᶜ i ≤ 0) :
    Cavg p m n I J U ≤ -(2 * p - 1) / ((I.card : ℕ) : ℝ) := by
  have hcard : (0 : ℝ) < (I.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hI
  have hsum : (∑ i ∈ I, corr p m U n Jᶜ i) ≤ -(2 * p - 1) := by
    have hsingle : corr p m U n Jᶜ i₀ ≤ -(2 * p - 1) := corr_le_neg_of_excited hp hp1 m n U J hα hw
    have hsplit : (∑ i ∈ I, corr p m U n Jᶜ i)
        = corr p m U n Jᶜ i₀ + ∑ i ∈ I.erase i₀, corr p m U n Jᶜ i :=
      (Finset.add_sum_erase I (fun i => corr p m U n Jᶜ i) hi₀).symm
    have hrest : (∑ i ∈ I.erase i₀, corr p m U n Jᶜ i) ≤ 0 :=
      Finset.sum_nonpos fun i hi => hnonpos i (Finset.mem_of_mem_erase hi)
    linarith
  rw [Cavg, Swarming.Group.average]
  rw [div_le_iff₀ hcard]
  calc (∑ i ∈ I, corr p m U n Jᶜ i) ≤ -(2 * p - 1) := hsum
    _ = -(2 * p - 1) / (I.card : ℝ) * (I.card : ℝ) := by field_simp
