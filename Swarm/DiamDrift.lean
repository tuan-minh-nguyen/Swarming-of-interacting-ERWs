/-
  **`(diam)` input, part 2: the single-walker conditional drift of the group potential**
  (the paper's equation (unit) inside the proof of Proposition `group`).

  This is the honest `condExp` statement for the actual interacting model: for every walker
  `i` and every group `A`, on the event `{0 ≤ X_n^i}`,

      E[ H_n^A(X_{n+1}^i) - H_n^A(X_n^i) | F_n ]
        = 1 + (alpha_n^i - w_n^A(X_n^i)) (h_n^A(X_n^i) + h_n^A(X_n^i - 1)),

  where `F_n = posFilt N p m n` is the paper's natural filtration of the walks.  The
  right-hand side is exactly `stepMean - H_n^A(X_n^i)` from `SepGroup.Model.stepMean_HA_sub`,
  so this is the two-point mean identity lifted to a genuine conditional expectation.

  Strategy: `Swarming.Enl.condExp_drift_of_adapted` proves this for the *enlarged*
  filtration (states together with all revealed coordinates), given measurability of the two
  restricted potential steps.  Here the measurability is proved in the position filtration
  (`M3DiamMeas`), the enlarged statement is transferred by the tower property
  `posFilt ≤ enlFilt`, and the right-hand side is put in the paper's
  `1 + (alpha - w)(h + h^-)` form with `Cookie.drift_identity`.
-/
import Swarm.DiamMeas

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace SwarmM3

open Swarming Swarming.Uniform Swarming.Trajectory SepGroup.Model
open Swarming.Enl (hZpot stepDownInd hZpot_of_nonpos hZpot_of_nonneg)

variable {N : ℕ}

/-! ### Bridge: the group potential is `SwarmOcc.Hpot` of the step function `hfix wA` -/

theorem HZ_eq_Hpot (w : ℕ → ℝ) (x : ℤ) :
    SepGroup.HZ w x = SwarmOcc.Hpot (Cookie.hfix w) x := by
  rcases lt_or_ge x 0 with h | h
  · rw [SepGroup.HZ_neg h, SwarmOcc.Hpot_of_nonpos (by omega)]
  · rcases eq_or_lt_of_le h with h0 | h0
    · subst h0
      simp [SepGroup.HZ, SwarmOcc.Hpot, Cookie.Hfix]
    · have hx : ¬ x ≤ 0 := by omega
      rw [SepGroup.HZ_nonneg h, SwarmOcc.Hpot, if_neg hx]
      rfl

theorem HA_eq_Hpot (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (A : Finset (Fin N)) (x : ℤ) :
    HA p m U n A x = SwarmOcc.Hpot (hA p m U n A) x :=
  HZ_eq_Hpot (wA p m U n A) x

/-! ### Bounds for the two potential steps at the actual position -/

theorem abs_hZpot_le {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ) (U : Array N)
    (A : Finset (Fin N)) {y : ℤ} {M : ℕ} (hy : |y| ≤ (M : ℤ)) :
    |hZpot (hA p m U n A) y| ≤ 2 * (M : ℝ) + 5 := by
  have hw0 : ∀ k, 1 / 2 ≤ wA p m U n A k := fun k => one_half_le_wA p m U hp n A k
  have hw1 : ∀ k, wA p m U n A k ≤ 1 := fun k => wA_le_one p m U hp1 n A k
  by_cases h : y ≤ -1
  · rw [hZpot_of_nonpos h, abs_one]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  · have h0 : 0 ≤ y := by omega
    have hone := Cookie.one_le_hfix (wA p m U n A) (fun k => by linarith [hw0 k]) hw1 y.toNat
    rw [hZpot_of_nonneg h0]
    simp only [hA]
    rw [abs_of_nonneg (le_trans (by norm_num) hone)]
    have hb := hfix_le_lin (wA p m U n A) hw0 hw1 y.toNat
    have hy' : y.toNat ≤ M := by
      have := (abs_le.mp hy).2
      omega
    have hy'' : (y.toNat : ℝ) ≤ (M : ℝ) := by exact_mod_cast hy'
    linarith

/-! ### The right-hand side in the paper's form -/

/-- On `{0 ≤ X_n^i}` the two potential steps at the actual position are `hfix wA (X_n)` and
`hprev wA (X_n)`, so `Cookie.drift_identity` turns the conditional two-point mean into the
paper's `1 + (alpha - w)(h + h^-)`. -/
theorem hZpot_rhs_eq {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ) (U : Array N)
    (A : Finset (Fin N)) (i : Fin N) (hx : 0 ≤ X p m U n i) :
    SwarmCross.alphaFun p m n i U * hZpot (hA p m U n A) (X p m U n i)
        - (1 - SwarmCross.alphaFun p m n i U) * hZpot (hA p m U n A) (X p m U n i - 1)
      = 1 + (SwarmCross.alphaFun p m n i U - wA p m U n A (X p m U n i).toNat) *
          (Cookie.hfix (wA p m U n A) (X p m U n i).toNat
            + Cookie.hprev (wA p m U n A) (X p m U n i).toNat) := by
  have hup : hZpot (hA p m U n A) (X p m U n i)
      = Cookie.hfix (wA p m U n A) (X p m U n i).toNat := hZpot_of_nonneg hx
  have hdn : hZpot (hA p m U n A) (X p m U n i - 1)
      = Cookie.hprev (wA p m U n A) (X p m U n i).toNat := by
    rcases eq_or_lt_of_le hx with h0 | hpos
    · have hx0 : X p m U n i = 0 := by omega
      rw [hx0]
      rw [show ((0 : ℤ) - 1) = -1 by ring, hZpot_of_nonpos (by norm_num)]
      simp
    · have h1 : 0 ≤ X p m U n i - 1 := by omega
      have hnat : (X p m U n i - 1).toNat = (X p m U n i).toNat - 1 := by
        have h2 : ((X p m U n i).toNat : ℤ) = X p m U n i := Int.toNat_of_nonneg hx
        have h3 : ((X p m U n i).toNat - 1 : ℕ) = (X p m U n i).toNat - 1 := rfl
        omega
      have hne : (X p m U n i).toNat ≠ 0 := by omega
      rw [hZpot_of_nonneg h1]
      simp only [hA]
      rw [hnat, Cookie.hprev, if_neg hne]
  rw [hup, hdn]
  exact Cookie.drift_identity (wA p m U n A)
    (fun k => ne_of_gt (wA_pos p m U hp n A k)) (X p m U n i).toNat (SwarmCross.alphaFun p m n i U)

/-! ### Measurability of the two restricted potential steps -/

theorem measurable_indicator_hZpot_posFilt (p : ℝ) (m n : ℕ) (A : Finset (Fin N)) (i : Fin N)
    {A₀ : Set (Array N)} (hA₀ : MeasurableSet[posFilt N p m n] A₀) :
    Measurable[posFilt N p m n]
      (fun U : Array N => A₀.indicator (fun U => hZpot (hA p m U n A) (X p m U n i)) U) :=
  (measurable_hZpot_X_posFilt p m n A i).indicator hA₀

theorem measurable_indicator_hZpot_pred_posFilt (p : ℝ) (m n : ℕ) (A : Finset (Fin N))
    (i : Fin N) {A₀ : Set (Array N)} (hA₀ : MeasurableSet[posFilt N p m n] A₀) :
    Measurable[posFilt N p m n]
      (fun U : Array N => A₀.indicator (fun U => hZpot (hA p m U n A) (X p m U n i - 1)) U) :=
  (measurable_hZpot_Xsub1_posFilt p m n A i).indicator hA₀

/-- `alphaFun` is adapted to the position filtration. -/
theorem measurable_alphaFun_posFilt (p : ℝ) (m n : ℕ) (i : Fin N) :
    Measurable[posFilt N p m n] (SwarmCross.alphaFun p m n i) := by
  rw [← pathMeas_eq_posFilt]
  exact SwarmCross.measurable_alphaFun p m n i

/-! ### The single-walker conditional drift -/

/-- **The paper's `(unit)` identity at `condExp` level, in the position filtration.**
For every walker `i` and group `A`, on the event `{0 ≤ X_n^i}` the conditional mean of the
potential increment is the two-point mean, i.e.
`1 + (alpha_n^i - w_n^A(X_n^i))(h_n^A(X_n^i) + h_n^A(X_n^i-1))`. -/
theorem condExp_HA_drift_of_subset {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) (n : ℕ)
    (A : Finset (Fin N)) (i : Fin N) {A₀ : Set (Array N)}
    (hA₀ : MeasurableSet[posFilt N p m n] A₀)
    (hsub : A₀ ⊆ {U | 0 ≤ X p m U n i}) :
    condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => A₀.indicator
        (fun U => HA p m U n A (X p m U (n + 1) i) - HA p m U n A (X p m U n i)) U)
    =ᵐ[arrayMeasure N]
      fun U => A₀.indicator
        (fun U => 1 + (SwarmCross.alphaFun p m n i U - wA p m U n A (X p m U n i).toNat) *
          (Cookie.hfix (wA p m U n A) (X p m U n i).toNat
            + Cookie.hprev (wA p m U n A) (X p m U n i).toNat)) U := by
  classical
  haveI hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hp : 1 / 2 ≤ p := le_of_lt hp0
  have hp1' : p ≤ 1 := le_of_lt hp1
  -- adaptedness and bounds of the two restricted potential steps
  have hupM := measurable_indicator_hZpot_posFilt (N := N) p m n A i hA₀
  have hdnM := measurable_indicator_hZpot_pred_posFilt (N := N) p m n A i hA₀
  have hble : ∀ U : Array N, ‖A₀.indicator
      (fun U => hZpot (hA p m U n A) (X p m U n i)) U‖
        ≤ 2 * ((n + 1 : ℕ) : ℝ) + 5 := by
    intro U
    by_cases hU : U ∈ A₀
    · rw [Set.indicator_of_mem hU, Real.norm_eq_abs]
      have h1 := abs_hZpot_le (p := p) (m := m) (n := n) (U := U) (A := A) (M := n) hp hp1'
        (abs_X_le p m U n i)
      have h2 : (2 * (n : ℝ) + 5) ≤ 2 * ((n + 1 : ℕ) : ℝ) + 5 := by
        push_cast
        linarith
      linarith
    · rw [Set.indicator_of_notMem hU]
      simp only [norm_zero]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
  have hblp : ∀ U : Array N, ‖A₀.indicator
      (fun U => hZpot (hA p m U n A) (X p m U n i - 1)) U‖
        ≤ 2 * ((n + 1 : ℕ) : ℝ) + 5 := by
    intro U
    by_cases hU : U ∈ A₀
    · rw [Set.indicator_of_mem hU, Real.norm_eq_abs]
      refine abs_hZpot_le (p := p) (m := m) (n := n) (U := U) (A := A) (M := n + 1) hp hp1' ?_
      have h := abs_X_le p m U n i
      rw [abs_le] at h ⊢
      push_cast
      omega
    · rw [Set.indicator_of_notMem hU]
      simp only [norm_zero]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
  -- the enlarged-filtration drift of `Swarming.Enl`
  have hpf : posFilt N p m n ≤ Swarming.Enl.enlFilt p m n :=
    (Swarming.Enl.posFilt_le_enlFilt (N := N) p m) n
  have hA₀E : MeasurableSet[Swarming.Enl.enlFilt p m n] A₀ := hpf A₀ hA₀
  have hupE : Measurable[Swarming.Enl.enlFilt p m n]
      (fun U : Array N => A₀.indicator (fun U => hZpot (hA p m U n A) (X p m U n i)) U) :=
    Measurable.mono hupM hpf le_rfl
  have hdnE : Measurable[Swarming.Enl.enlFilt p m n]
      (fun U : Array N => A₀.indicator (fun U => hZpot (hA p m U n A) (X p m U n i - 1)) U) :=
    Measurable.mono hdnM hpf le_rfl
  have hE := Swarming.Enl.condExp_drift_of_adapted (N := N) hp0 hp1
    (m := m) (n := n) (fun U => hA p m U n A) i (A := A₀) hA₀E hupE hdnE
    (2 * ((n + 1 : ℕ) : ℝ) + 5) (by positivity)
    (fun U => hble U) (fun U => hblp U)
  -- translate `Hpot` into the group potential `HA`
  have htrans : (fun U : Array N => A₀.indicator
        (fun U => HA p m U n A (X p m U (n + 1) i) - HA p m U n A (X p m U n i)) U)
      =ᵐ[arrayMeasure N] (fun U : Array N => A₀.indicator
        (fun U => SwarmOcc.Hpot (hA p m U n A) (X p m U (n + 1) i)
          - SwarmOcc.Hpot (hA p m U n A) (X p m U n i)) U) := by
    refine Filter.EventuallyEq.of_eq ?_
    funext U
    simp only [HA_eq_Hpot]
  have hE' : condExp (Swarming.Enl.enlFilt p m n) (arrayMeasure N)
      (fun U : Array N => A₀.indicator
        (fun U => HA p m U n A (X p m U (n + 1) i) - HA p m U n A (X p m U n i)) U)
      =ᵐ[arrayMeasure N] fun U => A₀.indicator
        (fun U => SwarmCross.alphaFun p m n i U * hZpot (hA p m U n A) (X p m U n i)
          - (1 - SwarmCross.alphaFun p m n i U) * hZpot (hA p m U n A) (X p m U n i - 1)) U :=
    (condExp_congr_ae htrans).trans hE
  -- the target right-hand side is adapted
  have hRext : Measurable[posFilt N p m n]
      (fun U : Array N => A₀.indicator
        (fun U => SwarmCross.alphaFun p m n i U * hZpot (hA p m U n A) (X p m U n i)
          - (1 - SwarmCross.alphaFun p m n i U) * hZpot (hA p m U n A) (X p m U n i - 1)) U) := by
    refine Measurable.indicator ?_ hA₀
    refine Measurable.sub ?_ ?_
    · exact (measurable_alphaFun_posFilt p m n i).mul (measurable_hZpot_X_posFilt p m n A i)
    · exact ((measurable_const_posFilt p m n 1).sub
        (measurable_alphaFun_posFilt p m n i)).mul (measurable_hZpot_Xsub1_posFilt p m n A i)
  have hRint : Integrable (fun U : Array N => A₀.indicator
      (fun U => SwarmCross.alphaFun p m n i U * hZpot (hA p m U n A) (X p m U n i)
        - (1 - SwarmCross.alphaFun p m n i U) * hZpot (hA p m U n A) (X p m U n i - 1)) U)
      (arrayMeasure N) := by
    refine Integrable.mono' (integrable_const (4 * (n : ℝ) + 10)) ?_ ?_
    · exact (hRext.mono ((posFilt N p m).le n) le_rfl).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun U => ?_
      have hα := SwarmCross.alphaFun_mem_Icc hp0 hp1 m n i U
      obtain ⟨hα0, hα1⟩ := hα
      have hU : ∀ y : ℤ, |y| ≤ (n : ℤ) → |y - 1| ≤ ((n + 1 : ℕ) : ℤ) := by
        intro y hy
        rw [abs_le] at hy ⊢
        omega
      have b1 : |hZpot (hA p m U n A) (X p m U n i)| ≤ 2 * (n : ℝ) + 5 :=
        abs_hZpot_le (p := p) (m := m) (n := n) (U := U) (A := A) (M := n) hp hp1'
          (abs_X_le p m U n i)
      have b2 : |hZpot (hA p m U n A) (X p m U n i - 1)| ≤ 2 * ((n + 1 : ℕ) : ℝ) + 5 :=
        abs_hZpot_le (p := p) (m := m) (n := n) (U := U) (A := A) (M := n + 1) hp hp1'
          (hU (X p m U n i) (abs_X_le p m U n i))
      by_cases hmem : U ∈ A₀
      · rw [Set.indicator_of_mem hmem, Real.norm_eq_abs, abs_le]
        have h2 : |hZpot (hA p m U n A) (X p m U n i - 1)| ≤ 2 * ((n + 1 : ℕ) : ℝ) + 5 := b2
        push_cast at h2 ⊢
        constructor <;> nlinarith [abs_le.mp b1, abs_le.mp h2, hα0, hα1, b1]
      · rw [Set.indicator_of_notMem hmem]
        simp only [norm_zero]
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
  -- descend to the position filtration by the tower property
  have hle : posFilt N p m n ≤ Swarming.Enl.enlFilt p m n :=
    (Swarming.Enl.posFilt_le_enlFilt (N := N) p m) n
  haveI hsig : SigmaFinite ((arrayMeasure N).trim ((Swarming.Enl.enlFilt p m).le n)) := inferInstance
  haveI hsig2 : SigmaFinite ((arrayMeasure N).trim ((posFilt N p m).le n)) := inferInstance
  have htower := condExp_condExp_of_le (m₁ := posFilt N p m n)
    (m₂ := Swarming.Enl.enlFilt p m n) (μ := arrayMeasure N) hle ((Swarming.Enl.enlFilt p m).le n)
    (f := fun U : Array N => A₀.indicator
      (fun U => HA p m U n A (X p m U (n + 1) i) - HA p m U n A (X p m U n i)) U)
  calc condExp (posFilt N p m n) (arrayMeasure N)
        (fun U : Array N => A₀.indicator
          (fun U => HA p m U n A (X p m U (n + 1) i) - HA p m U n A (X p m U n i)) U)
      =ᵐ[arrayMeasure N] condExp (posFilt N p m n) (arrayMeasure N)
          (condExp (Swarming.Enl.enlFilt p m n) (arrayMeasure N)
            (fun U : Array N => A₀.indicator
              (fun U => HA p m U n A (X p m U (n + 1) i) - HA p m U n A (X p m U n i)) U)) :=
        htower.symm
    _ =ᵐ[arrayMeasure N] condExp (posFilt N p m n) (arrayMeasure N)
          (fun U => A₀.indicator
            (fun U => SwarmCross.alphaFun p m n i U * hZpot (hA p m U n A) (X p m U n i)
              - (1 - SwarmCross.alphaFun p m n i U) *
                  hZpot (hA p m U n A) (X p m U n i - 1)) U) :=
        condExp_congr_ae hE'
    _ =ᵐ[arrayMeasure N] (fun U => A₀.indicator
            (fun U => SwarmCross.alphaFun p m n i U * hZpot (hA p m U n A) (X p m U n i)
              - (1 - SwarmCross.alphaFun p m n i U) *
                  hZpot (hA p m U n A) (X p m U n i - 1)) U) :=
        Filter.EventuallyEq.of_eq
          (condExp_of_stronglyMeasurable ((posFilt N p m).le n) hRext.stronglyMeasurable hRint)
    _ =ᵐ[arrayMeasure N] (fun U => A₀.indicator
          (fun U => 1 + (SwarmCross.alphaFun p m n i U - wA p m U n A (X p m U n i).toNat) *
            (Cookie.hfix (wA p m U n A) (X p m U n i).toNat
              + Cookie.hprev (wA p m U n A) (X p m U n i).toNat)) U) := by
        refine Filter.EventuallyEq.of_eq ?_
        funext U
        by_cases hU : U ∈ A₀
        · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU]
          exact hZpot_rhs_eq hp hp1' m n U A i (hsub hU)
        · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]

/-- **The paper's `(unit)` identity at `condExp` level on `{0 ≤ X_n^i}`.** -/
theorem condExp_HA_drift_posFilt {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) (n : ℕ)
    (A : Finset (Fin N)) (i : Fin N) :
    condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => {U | 0 ≤ X p m U n i}.indicator
        (fun U => HA p m U n A (X p m U (n + 1) i) - HA p m U n A (X p m U n i)) U)
    =ᵐ[arrayMeasure N]
      fun U => {U | 0 ≤ X p m U n i}.indicator
        (fun U => 1 + (SwarmCross.alphaFun p m n i U - wA p m U n A (X p m U n i).toNat) *
          (Cookie.hfix (wA p m U n A) (X p m U n i).toNat
            + Cookie.hprev (wA p m U n A) (X p m U n i).toNat)) U :=
  condExp_HA_drift_of_subset hp0 hp1 m n A i
    (measurableSet_le (measurable_const_posFilt_int p m n 0) (measurable_pos_posFilt p m i le_rfl))
    (fun _ h => h)

end SwarmM3
