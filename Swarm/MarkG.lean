/-
  **The `G`-part of displays (Kmom) and (maxmom)** of Proposition "spatial"
  (*Swarming of interacting excited random walks*, `main_1d_revised.tex`).

  `MarkBoth.lean` proves the exponential moment of `h(x) + G(x)` (display (expmom)); what is still
  missing in the mark layer is the maximum over the sites:

      max_{0 <= x <= n+1} (h(x) + G(x)) = O (log (n+2))                       a.s.      (Kmom)
      E [(1 + max_{0 <= x <= n+1} (h(x) + G(x)))^s] <= C_s (log (n+2))^s,    s >= 1.   (maxmom)

  The one structural point not present in the earlier files is that `G(x)` is the *limit* of the
  truncations `G_N(x)`: the identity

      ⨆_N  ofReal (exp (θ (h(x) + G_N(x))))  =  ofReal (exp (θ (h(x) + G(x))))

  (a monotone continuous image of an indexed supremum, `iSup_ofReal_exp_hofGsup`) lets the
  `lintegral` bound `lintegral_exp_hG_sup_le` be read as a bound for `exp (θ (h(x) + G(x)))`
  itself.  `G` is finite a.s. (`Gsup_ne_top_ae`), i.e. the defining series converges a.s., which is
  exactly the `BddAbove` hypothesis of that identity.
-/
import Swarm.Imports
import Swarm.RecursionCore
import Swarm.MarkProcess
import Swarm.MarkMoments
import Swarm.MarkTails
import Swarm.MarkFuture
import Swarm.MarkBoth
import Swarm.MarkMaxmom

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open SwarmMarks

namespace SwarmMarks

noncomputable section

/-! ### The forward potential `G(x)` as a real-valued function -/

/-- The paper's forward potential `G(x) = 1 + sum_{l>=1} prod_{u=1}^{l} rho(x+u)`, written as the
supremum of its truncations.  On the almost-sure event where the defining series converges this is
the genuine supremum; every statement below is either an `lintegral` statement, an almost-sure
statement, or carries `BddAbove (range fun N => Gtrunc p ω N (x+1))` explicitly. -/
def Gsup (p : ℝ) (ω : ℕ → Bool) (x : ℕ) : ℝ := ⨆ N, Gtrunc p ω N (x + 1)

lemma measurable_Gsup (p : ℝ) (x : ℕ) :
    Measurable (fun ω : ℕ → Bool => Gsup p ω x) :=
  Measurable.iSup fun N => measurable_Gtrunc p N (x + 1)

/-- The truncations increase in `N`. -/
lemma monotone_Gtrunc {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (ω : ℕ → Bool) (x : ℕ) :
    Monotone fun N => Gtrunc p ω N (x + 1) :=
  monotone_nat_of_le_succ fun N => Gtrunc_mono hp1 hp2 ω N (x + 1)

/-- **The defining series of `G(x)` converges almost surely**, in the form needed for the
supremum identity: the truncations are bounded above.  Derived from the finiteness of the
exponential moment `⨆_N exp (θ G_N(x)) < ∞` (`Gsup_ne_top_ae`), using `G_N >= 1`. -/
theorem bddAbove_range_Gtrunc_ae {p q θ γ : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hθ : 0 < θ) (hγpos : 0 < γ) (hγ1 : γ < 1)
    (hγ : (1 - q) * Real.exp (2 * θ) + q * ((1 - p) / p) * Real.exp (θ / p) ≤ γ) :
    ∀ᵐ ω ∂(markMeasure (boolMeasure q)), ∀ x : ℕ,
      BddAbove (Set.range fun N => Gtrunc p ω N (x + 1)) := by
  have hfin := Gsup_ne_top_ae hp1 hp2 hq0 hq1 hθ hγpos hγ1 hγ
  filter_upwards [hfin] with ω hω x
  set c : ℝ≥0∞ := ⨆ N, ENNReal.ofReal (Real.exp (θ * Gtrunc p ω N (x + 1))) with hc
  have hcne : c ≠ ⊤ := hω x
  refine ⟨Real.log c.toReal / θ, ?_⟩
  rintro y ⟨N, rfl⟩
  have h1 : ENNReal.ofReal (Real.exp (θ * Gtrunc p ω N (x + 1))) ≤ c := by
    rw [hc]
    exact le_iSup (fun N => ENNReal.ofReal (Real.exp (θ * Gtrunc p ω N (x + 1)))) N
  have h2 : Real.exp (θ * Gtrunc p ω N (x + 1)) ≤ c.toReal := by
    have h := h1
    rw [← ENNReal.ofReal_toReal hcne] at h
    exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp h
  have h3 : θ * Gtrunc p ω N (x + 1) ≤ Real.log c.toReal := by
    calc θ * Gtrunc p ω N (x + 1)
        = Real.log (Real.exp (θ * Gtrunc p ω N (x + 1))) := (Real.log_exp _).symm
      _ ≤ Real.log c.toReal := Real.log_le_log (Real.exp_pos _) h2
  rw [le_div_iff₀ hθ]
  linarith

/-- `G(x)` dominates each truncation, wherever the series converges. -/
lemma Gtrunc_le_Gsup {p : ℝ} (ω : ℕ → Bool) (x N : ℕ)
    (hbdd : BddAbove (Set.range fun N => Gtrunc p ω N (x + 1))) :
    Gtrunc p ω N (x + 1) ≤ Gsup p ω x :=
  le_ciSup hbdd N

lemma one_le_Gsup {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (ω : ℕ → Bool) (x : ℕ)
    (hbdd : BddAbove (Set.range fun N => Gtrunc p ω N (x + 1))) :
    1 ≤ Gsup p ω x :=
  (one_le_Gtrunc hp1 hp2 ω 0 (x + 1)).trans (Gtrunc_le_Gsup ω x 0 hbdd)

/-- **The supremum identity**: on the convergence event, `exp (θ (h(x) + G_N(x)))` increases to
`exp (θ (h(x) + G(x)))`.  This is the only place where the definition of `G` as a limit enters. -/
lemma iSup_ofReal_exp_hofGsup {p θ : ℝ} (hθ : 0 < θ) (ω : ℕ → Bool) (x : ℕ)
    (hbdd : BddAbove (Set.range fun N => Gtrunc p ω N (x + 1))) :
    (⨆ N, ENNReal.ofReal (Real.exp (θ * (hof p ω x + Gtrunc p ω N (x + 1)))))
      = ENNReal.ofReal (Real.exp (θ * (hof p ω x + Gsup p ω x))) := by
  have hmono : Monotone fun y : ℝ =>
      ENNReal.ofReal (Real.exp (θ * (hof p ω x + y))) := by
    intro y y' hyy'
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have : θ * (hof p ω x + y) ≤ θ * (hof p ω x + y') := by nlinarith
    exact this
  have hcont : Continuous fun y : ℝ => ENNReal.ofReal (Real.exp (θ * (hof p ω x + y))) :=
    ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (by fun_prop))
  have key := Monotone.map_ciSup_of_continuousAt hcont.continuousAt hmono hbdd
  simp only [Gsup]
  exact key.symm

/-! ### The exponential moment of `h(x) + G(x)` for the untruncated `G` -/

/-- **Display (expmom) for the untruncated forward potential**: for every site `x`,
`E exp (θ (h(x) + G(x))) <= M²`, with the constants of `MarkBoth`. -/
theorem lintegral_exp_hofGsup_le {p q θ γ : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hθ : 0 < θ) (hγpos : 0 < γ) (hγ1 : γ < 1)
    (hγ : (1 - q) * Real.exp (2 * θ) + q * ((1 - p) / p) * Real.exp (θ / p) ≤ γ)
    (x : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * (hof p ω x + Gsup p ω x)))
        ∂(markMeasure (boolMeasure q))
      ≤ ENNReal.ofReal (momConst p q θ γ * momConst p q θ γ) := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure hq0 hq1
  have hbdd := bddAbove_range_Gtrunc_ae hp1 hp2 hq0 hq1 hθ hγpos hγ1 hγ
  have hcongr : ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * (hof p ω x + Gsup p ω x)))
        ∂(markMeasure (boolMeasure q))
      = ∫⁻ ω, (⨆ N, ENNReal.ofReal (Real.exp (θ * (hof p ω x + Gtrunc p ω N (x + 1)))))
        ∂(markMeasure (boolMeasure q)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hbdd] with ω hω
    exact (iSup_ofReal_exp_hofGsup hθ ω x (hω x)).symm
  rw [hcongr]
  exact lintegral_exp_hG_sup_le hp1 hp2 hq0 hq1 hθ hγpos hγ1 hγ x

/-! ### The tail of `h(x) + G(x)` -/

/-- **Exponential tail of `h(x) + G(x)`.** -/
theorem hofG_tail_bound {p q θ γ : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hθ : 0 < θ) (hγpos : 0 < γ) (hγ1 : γ < 1)
    (hγ : (1 - q) * Real.exp (2 * θ) + q * ((1 - p) / p) * Real.exp (θ / p) ≤ γ)
    (x : ℕ) (u : ℝ) :
    markMeasure (boolMeasure q) {ω : ℕ → Bool | u ≤ hof p ω x + Gsup p ω x}
      ≤ ENNReal.ofReal
          (momConst p q θ γ * momConst p q θ γ * Real.exp (-(θ * u))) := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure hq0 hq1
  have hp0 : p ≠ 0 := by linarith
  have hmeas : Measurable (fun ω : ℕ → Bool =>
      ENNReal.ofReal (Real.exp (θ * (hof p ω x + Gsup p ω x)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul ((measurable_hof hp0 x).add (measurable_Gsup p x))))
  have hM := lintegral_exp_hofGsup_le hp1 hp2 hq0 hq1 hθ hγpos hγ1 hγ x
  have hset : {ω : ℕ → Bool | u ≤ hof p ω x + Gsup p ω x}
      = {ω : ℕ → Bool | ENNReal.ofReal (Real.exp (θ * u))
          ≤ ENNReal.ofReal (Real.exp (θ * (hof p ω x + Gsup p ω x)))} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le, Real.exp_le_exp]
    constructor <;> intro h <;> nlinarith [hθ]
  rw [hset]
  have hmk := mul_measure_le_lintegral (μ := markMeasure (boolMeasure q)) hmeas
    (ENNReal.ofReal (Real.exp (θ * u)))
  have hchain := le_trans hmk hM
  rw [mul_comm] at hchain
  have hfin : ENNReal.ofReal (Real.exp (θ * u)) ≠ 0 := by simp [Real.exp_pos]
  have htop : ENNReal.ofReal (Real.exp (θ * u)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hdiv : (markMeasure (boolMeasure q))
      {ω : ℕ → Bool | ENNReal.ofReal (Real.exp (θ * u))
        ≤ ENNReal.ofReal (Real.exp (θ * (hof p ω x + Gsup p ω x)))}
      ≤ ENNReal.ofReal (momConst p q θ γ * momConst p q θ γ)
        / ENNReal.ofReal (Real.exp (θ * u)) := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hfin) (Or.inl htop)]
    exact hchain
  refine hdiv.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), Real.exp_neg, div_eq_mul_inv]

/-! ### Union bound over the sites `0, ..., n+1` -/

theorem hofG_max_tail_bound {p q θ γ : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hθ : 0 < θ) (hγpos : 0 < γ) (hγ1 : γ < 1)
    (hγ : (1 - q) * Real.exp (2 * θ) + q * ((1 - p) / p) * Real.exp (θ / p) ≤ γ)
    (n : ℕ) (u : ℝ) :
    markMeasure (boolMeasure q)
        {ω : ℕ → Bool | ∃ x ∈ Finset.range (n + 2), u ≤ hof p ω x + Gsup p ω x}
      ≤ (n + 2 : ℝ≥0∞) * ENNReal.ofReal
          (momConst p q θ γ * momConst p q θ γ * Real.exp (-(θ * u))) := by
  have hset : {ω : ℕ → Bool | ∃ x ∈ Finset.range (n + 2), u ≤ hof p ω x + Gsup p ω x}
      = ⋃ x ∈ Finset.range (n + 2), {ω : ℕ → Bool | u ≤ hof p ω x + Gsup p ω x} := by
    ext ω
    simp
  rw [hset]
  refine (measure_biUnion_finset_le _ _).trans ?_
  have hsingle : ∀ x ∈ Finset.range (n + 2),
      markMeasure (boolMeasure q) {ω : ℕ → Bool | u ≤ hof p ω x + Gsup p ω x}
        ≤ ENNReal.ofReal (momConst p q θ γ * momConst p q θ γ * Real.exp (-(θ * u))) :=
    fun x _ => hofG_tail_bound hp1 hp2 hq0 hq1 hθ hγpos hγ1 hγ x u
  refine (Finset.sum_le_sum hsingle).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- **Display (Kmom), `G`-part.**  Almost surely,
`max_{0 <= x <= n+1} (h(x) + G(x)) = O (log (n+2))`. -/
theorem hofG_eventually_log_bound {p q θ γ : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hθ : 0 < θ) (hγpos : 0 < γ) (hγ1 : γ < 1)
    (hγ : (1 - q) * Real.exp (2 * θ) + q * ((1 - p) / p) * Real.exp (θ / p) ≤ γ) :
    ∀ᵐ ω ∂(markMeasure (boolMeasure q)), ∀ᶠ n : ℕ in Filter.atTop,
      ∀ x ≤ n + 1, hof p ω x + Gsup p ω x ≤ (3 / θ) * Real.log ((n : ℝ) + 2) := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure hq0.le hq1
  have hsumR : Summable (fun n : ℕ => (((n : ℝ) + 2) ^ 2)⁻¹) := by
    have h0 : Summable (fun n : ℕ => 1 / ((n : ℝ)) ^ 2) :=
      (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    have h1 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ 2) := by
      have h2 := (summable_nat_add_iff (f := fun m : ℕ => 1 / ((m : ℝ)) ^ 2) 2).mpr h0
      simpa [Nat.cast_add, Nat.cast_ofNat] using h2
    refine h1.congr fun n => ?_
    simp [one_div]
  have hM1 : 0 ≤ momConst p q θ γ := momConst_nonneg hp1 hp2 hq0.le hγ1
  have hMnn : 0 ≤ momConst p q θ γ * momConst p q θ γ := mul_nonneg hM1 hM1
  have hterm : ∀ n : ℕ,
      markMeasure (boolMeasure q) {ω : ℕ → Bool | ∃ x ∈ Finset.range (n + 2),
        (3 / θ) * Real.log ((n : ℝ) + 2) ≤ hof p ω x + Gsup p ω x}
      ≤ ENNReal.ofReal (momConst p q θ γ * momConst p q θ γ)
          * ENNReal.ofReal ((((n : ℝ) + 2) ^ 2)⁻¹) := by
    intro n
    refine (hofG_max_tail_bound hp1 hp2 hq0.le hq1 hθ hγpos hγ1 hγ n
      ((3 / θ) * Real.log ((n : ℝ) + 2))).trans ?_
    have hcast : ((n : ℝ≥0∞) + 2) = ENNReal.ofReal ((n : ℝ) + 2) := by
      rw [← ENNReal.ofReal_natCast (n := n), ← ENNReal.ofReal_ofNat (n := 2),
        ← ENNReal.ofReal_add (by positivity : (0:ℝ) ≤ (n:ℝ)) (by norm_num : (0:ℝ) ≤ 2)]
    have hexp : Real.exp (-(θ * ((3 / θ) * Real.log ((n : ℝ) + 2))))
        = (((n : ℝ) + 2) ^ 3)⁻¹ := by
      have hn : (0:ℝ) < (n : ℝ) + 2 := by positivity
      have h1 : θ * ((3 / θ) * Real.log ((n : ℝ) + 2)) = 3 * Real.log ((n : ℝ) + 2) := by
        field_simp
      rw [h1, show (3:ℝ) * Real.log ((n : ℝ) + 2) = Real.log (((n : ℝ) + 2) ^ 3) by
        rw [Real.log_pow]; push_cast; ring]
      rw [Real.exp_neg, Real.exp_log (by positivity)]
    rw [show ((n : ℝ≥0∞) + 2) = ENNReal.ofReal ((n : ℝ) + 2) from hcast, hexp,
      ← ENNReal.ofReal_mul hMnn]
    refine le_of_eq ?_
    rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ ((n : ℝ) + 2))]
    congr 1
    field_simp
  have htsum : (∑' n : ℕ, ENNReal.ofReal (momConst p q θ γ * momConst p q θ γ)
      * ENNReal.ofReal ((((n : ℝ) + 2) ^ 2)⁻¹)) ≠ ⊤ := by
    calc (∑' n : ℕ, ENNReal.ofReal (momConst p q θ γ * momConst p q θ γ)
        * ENNReal.ofReal ((((n : ℝ) + 2) ^ 2)⁻¹))
        = ∑' n : ℕ, ENNReal.ofReal
            (momConst p q θ γ * momConst p q θ γ * (((n : ℝ) + 2) ^ 2)⁻¹) := by
          refine tsum_congr fun n => ?_
          rw [ENNReal.ofReal_mul hMnn]
      _ = ENNReal.ofReal
            (∑' n : ℕ, momConst p q θ γ * momConst p q θ γ * (((n : ℝ) + 2) ^ 2)⁻¹) := by
          rw [ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) (hsumR.mul_left _)]
      _ = ENNReal.ofReal
            (momConst p q θ γ * momConst p q θ γ * ∑' n : ℕ, (((n : ℝ) + 2) ^ 2)⁻¹) := by
          rw [tsum_mul_left]
      _ ≠ ⊤ := ENNReal.ofReal_ne_top
  have htsumA : (∑' n : ℕ, (markMeasure (boolMeasure q))
      {ω : ℕ → Bool | ∃ x ∈ Finset.range (n + 2),
        (3 / θ) * Real.log ((n : ℝ) + 2) ≤ hof p ω x + Gsup p ω x}) ≠ ⊤ :=
    ne_top_of_le_ne_top htsum (ENNReal.tsum_le_tsum hterm)
  have hbc := MeasureTheory.ae_eventually_notMem
    (μ := markMeasure (boolMeasure q))
    (s := fun n => {ω : ℕ → Bool | ∃ x ∈ Finset.range (n + 2),
      (3 / θ) * Real.log ((n : ℝ) + 2) ≤ hof p ω x + Gsup p ω x}) htsumA
  filter_upwards [hbc] with ω hω
  filter_upwards [hω] with n hn x hx
  by_contra hcon
  exact hn ⟨x, Finset.mem_range.mpr (by omega), le_of_lt (not_le.mp hcon)⟩

/-! ### Display (maxmom) for `h + G` -/

/-- `max_{0 <= x <= n+1} (h(x) + G(x))`. -/
def YfunG (p : ℝ) (n : ℕ) (ω : ℕ → Bool) : ℝ :=
  (Finset.range (n + 2)).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩
    (fun x => hof p ω x + Gsup p ω x)

lemma measurable_YfunG (p : ℝ) (hp0 : p ≠ 0) (n : ℕ) :
    Measurable (fun ω : ℕ → Bool => YfunG p n ω) := by
  have hY : (fun ω : ℕ → Bool => YfunG p n ω)
      = (Finset.range (n + 2)).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩
          (fun i (ω : ℕ → Bool) => hof p ω i + Gsup p ω i) := by
    funext ω
    exact (Finset.sup'_apply (s := Finset.range (n + 2))
      ⟨0, Finset.mem_range.mpr (by omega)⟩
      (fun i (ω : ℕ → Bool) => hof p ω i + Gsup p ω i) ω).symm
  rw [hY]
  exact Finset.measurable_sup' _ (fun i _ => (measurable_hof hp0 i).add (measurable_Gsup p i))

lemma le_YfunG (p : ℝ) (n x : ℕ) (ω : ℕ → Bool) (hx : x ∈ Finset.range (n + 2)) :
    hof p ω x + Gsup p ω x ≤ YfunG p n ω :=
  Finset.le_sup' (fun x => hof p ω x + Gsup p ω x) hx

lemma one_le_YfunG {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (n : ℕ) (ω : ℕ → Bool)
    (h0 : 1 ≤ hof p ω 0 + Gsup p ω 0) :
    1 ≤ YfunG p n ω :=
  h0.trans (le_YfunG p n 0 ω (Finset.mem_range.mpr (by omega)))

/-- The exponential of the maximum is dominated by the sum over the sites. -/
lemma ofReal_exp_YfunG_le_sum (p θ : ℝ) (n : ℕ) (ω : ℕ → Bool) :
    ENNReal.ofReal (Real.exp (θ * YfunG p n ω))
      ≤ ∑ x ∈ Finset.range (n + 2),
          ENNReal.ofReal (Real.exp (θ * (hof p ω x + Gsup p ω x))) := by
  obtain ⟨x, hx, hxeq⟩ := Finset.exists_mem_eq_sup'
    (s := Finset.range (n + 2)) ⟨0, Finset.mem_range.mpr (by omega)⟩
    (fun x => hof p ω x + Gsup p ω x)
  have hxeq' : YfunG p n ω = hof p ω x + Gsup p ω x := hxeq
  rw [hxeq']
  exact Finset.single_le_sum
    (f := fun x => ENNReal.ofReal (Real.exp (θ * (hof p ω x + Gsup p ω x))))
    (fun i _ => by simp) hx

/-- **Display (maxmom), `G`-part.**  For `m >= 2`, `p in (1/2,1)` and `s >= 1` there is
`C = C(s,m,p) < ∞` with

    E[(1 + max_{0<=x<=n+1} (h(x) + G(x)))^s] <= C (log (n+2))^s   for every n. -/
theorem maxmom_hG {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ∫⁻ ω, ENNReal.ofReal ((1 + YfunG p n ω) ^ s)
          ∂(markMeasure (boolMeasure ((1 - p) ^ (m - 1))))
        ≤ ENNReal.ofReal (C * (Real.log ((n : ℝ) + 2)) ^ s) := by
  set qm : ℝ := (1 - p) ^ (m - 1) with hqm
  have hqm0 : 0 < qm := by rw [hqm]; exact pow_pos (by linarith) _
  have hqm1 : qm ≤ 1 := by
    rw [hqm]; have := pow_one_sub_le_half hp1 hp2 hm; linarith
  obtain ⟨θ, hθpos, hθc⟩ := exists_theta hp1 hp2 hqm0 (by linarith)
  set γm : ℝ := (1 - qm) * Real.exp (2 * θ) + qm * ((1 - p) / p) * Real.exp (θ / p) with hγm
  have hγm1 : γm < 1 := hθc
  have hγmpos : 0 < γm := by
    have hqlt : qm < 1 := by
      rw [hqm]
      have h0 : (0:ℝ) ≤ 1 - p := by linarith
      have hlt : 1 - p < 1 := by linarith
      exact pow_lt_one₀ h0 hlt (by omega)
    have hr := rho_nonneg hp1 hp2
    have h1 : 0 < 1 - qm := by linarith
    have h2 : 0 ≤ qm * ((1 - p) / p) * Real.exp (θ / p) := by positivity
    rw [hγm]
    nlinarith [Real.exp_pos (2 * θ)]
  haveI : IsProbabilityMeasure (boolMeasure qm) := isProbabilityMeasure_boolMeasure hqm0.le hqm1
  have hp0 : p ≠ 0 := by linarith
  obtain ⟨Cc, hCcpos, hCc⟩ := poly_le_exp s hθpos
  set M : ℝ := momConst p qm θ γm with hM
  have hMnn : 0 ≤ M := momConst_nonneg (θ := θ) hp1 hp2 hqm0.le hγm1
  have hMMnn : 0 ≤ M * M := mul_nonneg hMnn hMnn
  have hbdd := bddAbove_range_Gtrunc_ae hp1 hp2 hqm0.le hqm1 hθpos hγmpos hγm1 hγm.symm.le
  have hz0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmom : ∀ x : ℕ, ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * (hof p ω x + Gsup p ω x)))
      ∂(markMeasure (boolMeasure qm)) ≤ ENNReal.ofReal (M * M) := fun x =>
    lintegral_exp_hofGsup_le hp1 hp2 hqm0.le hqm1 hθpos hγmpos hγm1 hγm.symm.le x
  have hexpY : ∀ n : ℕ, ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * YfunG p n ω))
      ∂(markMeasure (boolMeasure qm)) ≤ ENNReal.ofReal (((n : ℝ) + 2) * (M * M)) := by
    intro n
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * YfunG p n ω)) ∂(markMeasure (boolMeasure qm))
        ≤ ∫⁻ ω, ∑ x ∈ Finset.range (n + 2),
            ENNReal.ofReal (Real.exp (θ * (hof p ω x + Gsup p ω x)))
            ∂(markMeasure (boolMeasure qm)) := by
          apply lintegral_mono
          intro ω
          exact ofReal_exp_YfunG_le_sum p θ n ω
      _ = ∑ x ∈ Finset.range (n + 2), ∫⁻ ω,
            ENNReal.ofReal (Real.exp (θ * (hof p ω x + Gsup p ω x)))
            ∂(markMeasure (boolMeasure qm)) :=
          lintegral_finsetSum _ (fun x _ => ENNReal.measurable_ofReal.comp
            (Real.measurable_exp.comp (measurable_const.mul
              ((measurable_hof hp0 x).add (measurable_Gsup p x)))))
      _ ≤ ∑ x ∈ Finset.range (n + 2), ENNReal.ofReal (M * M) :=
          Finset.sum_le_sum (fun x _ => hmom x)
      _ = ENNReal.ofReal (((n : ℝ) + 2) * (M * M)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          push_cast
          ring
  refine ⟨(1 / Real.log 2 + 4 / θ) ^ s + Cc * (M * M) / (Real.log 2) ^ s, ?_, ?_⟩
  · have h1 : (0:ℝ) < (1 / Real.log 2 + 4 / θ) ^ s := by positivity
    have h2 : 0 ≤ Cc * (M * M) / (Real.log 2) ^ s := by positivity
    linarith
  · intro n
    set z : ℝ := Real.log ((n : ℝ) + 2) with hz
    set U : ℝ := (4 / θ) * z with hU
    have hzpos : 0 < z := Real.log_pos (by linarith)
    have hzge : Real.log 2 ≤ z := by
      rw [hz]
      apply Real.log_le_log (by norm_num)
      linarith
    -- pointwise inequality, almost surely (the `BddAbove` event)
    have hpoint : ∀ᵐ ω ∂(markMeasure (boolMeasure qm)),
        (1 + YfunG p n ω) ^ s
          ≤ (1 + U) ^ s + (Cc * Real.exp (-(θ * U / 2))) * Real.exp (θ * YfunG p n ω) := by
      filter_upwards [hbdd] with ω hb
      have hY0 : 0 ≤ YfunG p n ω := by
        have h1 : 1 ≤ hof p ω 0 + Gsup p ω 0 := by
          have h2 := one_le_hof hp1.le hp2 ω 0
          have h3 := one_le_Gsup hp1 hp2 ω 0 (hb 0)
          linarith
        linarith [one_le_YfunG hp1 hp2 n ω h1]
      have hb' := hCc (YfunG p n ω) hY0
      have hexpU : (0:ℝ) < Real.exp (-(θ * U / 2)) := Real.exp_pos _
      rcases le_or_gt (YfunG p n ω) U with hle | hgt
      · have h1 : (1 + YfunG p n ω) ^ s ≤ (1 + U) ^ s :=
          pow_le_pow_left₀ (by linarith) (by linarith) s
        have h2 : 0 ≤ (Cc * Real.exp (-(θ * U / 2))) * Real.exp (θ * YfunG p n ω) := by positivity
        linarith
      · have hstep : Real.exp (θ * YfunG p n ω / 2)
            ≤ Real.exp (θ * YfunG p n ω) * Real.exp (-(θ * U / 2)) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          nlinarith [hgt]
        have : (1 + YfunG p n ω) ^ s
            ≤ Cc * (Real.exp (θ * YfunG p n ω) * Real.exp (-(θ * U / 2))) :=
          le_trans hb' (mul_le_mul_of_nonneg_left hstep hCcpos.le)
        have h2 : 0 ≤ (1 + U) ^ s := by positivity
        nlinarith
    calc ∫⁻ ω, ENNReal.ofReal ((1 + YfunG p n ω) ^ s) ∂(markMeasure (boolMeasure qm))
        ≤ ∫⁻ ω, ENNReal.ofReal ((1 + U) ^ s
            + (Cc * Real.exp (-(θ * U / 2))) * Real.exp (θ * YfunG p n ω))
            ∂(markMeasure (boolMeasure qm)) := by
          apply lintegral_mono_ae
          filter_upwards [hpoint] with ω hω
          exact ENNReal.ofReal_le_ofReal hω
      _ = ENNReal.ofReal ((1 + U) ^ s)
            + ENNReal.ofReal (Cc * Real.exp (-(θ * U / 2)))
              * ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * YfunG p n ω))
                ∂(markMeasure (boolMeasure qm)) := by
          have hsplit : (fun ω : ℕ → Bool => ENNReal.ofReal ((1 + U) ^ s
              + (Cc * Real.exp (-(θ * U / 2))) * Real.exp (θ * YfunG p n ω)))
              = fun ω => ENNReal.ofReal ((1 + U) ^ s)
                + ENNReal.ofReal (Cc * Real.exp (-(θ * U / 2)))
                  * ENNReal.ofReal (Real.exp (θ * YfunG p n ω)) := by
            funext ω
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by positivity)]
          rw [hsplit]
          rw [lintegral_add_left (f := fun _ : ℕ → Bool => ENNReal.ofReal ((1 + U) ^ s))
            (g := fun ω : ℕ → Bool => ENNReal.ofReal (Cc * Real.exp (-(θ * U / 2)))
              * ENNReal.ofReal (Real.exp (θ * YfunG p n ω))) measurable_const,
            lintegral_const, measure_univ, mul_one,
            lintegral_const_mul (ENNReal.ofReal (Cc * Real.exp (-(θ * U / 2))))
              (f := fun ω : ℕ → Bool => ENNReal.ofReal (Real.exp (θ * YfunG p n ω)))
              (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
                (measurable_const.mul (measurable_YfunG p hp0 n))))]
      _ ≤ ENNReal.ofReal ((1 + U) ^ s)
            + ENNReal.ofReal (Cc * Real.exp (-(θ * U / 2)))
              * ENNReal.ofReal (((n : ℝ) + 2) * (M * M)) := by
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hexpY n) (by simp))
      _ = ENNReal.ofReal ((1 + U) ^ s
            + (Cc * Real.exp (-(θ * U / 2))) * (((n : ℝ) + 2) * (M * M))) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ ENNReal.ofReal ((1 + U) ^ s + Cc * (M * M)) := by
          apply ENNReal.ofReal_le_ofReal
          have hexpval : Real.exp (-(θ * U / 2)) = (((n : ℝ) + 2) ^ 2)⁻¹ := by
            have h1 : θ * U / 2 = 2 * z := by
              rw [hU]
              field_simp
              ring
            rw [h1, hz, Real.exp_neg,
              show (2:ℝ) * Real.log ((n : ℝ) + 2) = Real.log (((n : ℝ) + 2) ^ 2) by
                rw [Real.log_pow]; push_cast; ring,
              Real.exp_log (by positivity)]
          rw [hexpval]
          have hpos2 : (0:ℝ) < (n : ℝ) + 2 := by positivity
          have hkey : (((n : ℝ) + 2) ^ 2)⁻¹ * (((n : ℝ) + 2) * (M * M)) ≤ M * M := by
            have h1 : (((n : ℝ) + 2) ^ 2)⁻¹ * ((n : ℝ) + 2) = ((n : ℝ) + 2)⁻¹ := by
              field_simp
            calc (((n : ℝ) + 2) ^ 2)⁻¹ * (((n : ℝ) + 2) * (M * M))
                = ((((n : ℝ) + 2) ^ 2)⁻¹ * ((n : ℝ) + 2)) * (M * M) := by ring
              _ = ((n : ℝ) + 2)⁻¹ * (M * M) := by rw [h1]
              _ ≤ 1 * (M * M) := by
                  apply mul_le_mul_of_nonneg_right _ hMMnn
                  exact (inv_le_one₀ (by linarith : (0:ℝ) < (n:ℝ) + 2)).mpr (by linarith)
              _ = M * M := by ring
          nlinarith [hkey, hCcpos.le]
      _ ≤ ENNReal.ofReal
            (((1 / Real.log 2 + 4 / θ) ^ s + Cc * (M * M) / (Real.log 2) ^ s)
            * (Real.log ((n : ℝ) + 2)) ^ s) := by
          apply ENNReal.ofReal_le_ofReal
          have h1U : (1 + U) ^ s ≤ ((1 / Real.log 2 + 4 / θ) * z) ^ s := by
            have hb : (1 + U) = z * (1 / z + 4 / θ) := by
              rw [hU]
              field_simp
            rw [hb, mul_pow]
            have hcoef : 1 / z + 4 / θ ≤ 1 / Real.log 2 + 4 / θ := by
              have h1z : 1 / z ≤ 1 / Real.log 2 :=
                div_le_div_of_nonneg_left (by norm_num) hz0 hzge
              linarith
            calc z ^ s * (1 / z + 4 / θ) ^ s
                ≤ z ^ s * (1 / Real.log 2 + 4 / θ) ^ s := by
                  apply mul_le_mul_of_nonneg_left _ (by positivity)
                  exact pow_le_pow_left₀ (by positivity) hcoef s
              _ = ((1 / Real.log 2 + 4 / θ) * z) ^ s := by
                  rw [mul_pow]; ring
          have h2 : Cc * (M * M) ≤ Cc * (M * M) / (Real.log 2) ^ s * z ^ s := by
            have hzs : (Real.log 2) ^ s ≤ z ^ s := pow_le_pow_left₀ hz0.le hzge s
            have hz0s : (0:ℝ) < (Real.log 2) ^ s := by positivity
            have hCM : 0 ≤ Cc * (M * M) := mul_nonneg hCcpos.le hMMnn
            rw [div_mul_eq_mul_div, le_div_iff₀ hz0s]
            nlinarith [hzs]
          have h3 : ((1 / Real.log 2 + 4 / θ) * z) ^ s
              = (1 / Real.log 2 + 4 / θ) ^ s * z ^ s := mul_pow _ _ _
          have hfinal : (1 + U) ^ s + Cc * (M * M)
              ≤ ((1 / Real.log 2 + 4 / θ) ^ s + Cc * (M * M) / (Real.log 2) ^ s) * z ^ s := by
            rw [add_mul]
            linarith [h1U, h2, h3]
          exact hfinal

end

end SwarmMarks
