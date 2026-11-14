/-
  **The shifted-seed recursion: any `enlRecMeas`-measurable seed.**

  `RecCond.lean` proves the projected recursion for the seed `h(-1) = 1` at the record (the
  Markov restart `shiftH`).  The paper's `e_g = E[h_j(M_n^j + g) | F_n]` instead uses the seed
  `h_j(M_n^j)`, and the one-step relation `h(M+g+1) = 1 + rho(B(M+g+1)) (1 + h(M+g))` is the same
  for every seed.  Here the whole argument is redone for an *arbitrary* seed `h0` measurable for
  the record-enlarged σ-algebra `enlRecMeas p m n j`:

  * `shiftG` — the potential `Φ^g h0` driven by the marks `B(M+1), B(M+2), …` above the record;
  * `measurable_shiftG` — it is `infoPiece g`-measurable (the random shift is handled piecewise);
  * `integrable_shiftG` — integrability from a deterministic bound;
  * `condExp_shiftG` — **`E[Φ^g h0 | enlRecMeas] = Φ_det^g h0`**, hence for a seed satisfying the
    one-step recursion at the record the paper's `(projh)` follows with the seed as data;
  * `shiftH_eq_shiftG` — `shiftH` is the special case `h0 = hstep (B(M)) 1`.
-/
import Swarm.RecCond

set_option linter.unusedVariables false
set_option warn.classDefReducibility false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory

variable {N : ℕ}

/-- The potential driven by the marks above the record, started from an arbitrary seed. -/
noncomputable def shiftG (h0 : Array N → ℝ) (p : ℝ) (m n : ℕ) (j : Fin N) :
    ℕ → Array N → ℝ
  | 0 => h0
  | (g + 1) => fun U => 1 + rhoStep p m n j (g + 1) U * (1 + shiftG h0 p m n j g U)

lemma shiftG_zero (h0 : Array N → ℝ) (p : ℝ) (m n : ℕ) (j : Fin N) :
    shiftG h0 p m n j 0 = h0 := rfl

lemma shiftG_succ (h0 : Array N → ℝ) (p : ℝ) (m n : ℕ) (j : Fin N) (g : ℕ) :
    shiftG h0 p m n j (g + 1)
      = fun U => 1 + rhoStep p m n j (g + 1) U * (1 + shiftG h0 p m n j g U) := rfl

/-! ### Measurability -/

/-- The multiplier at a fixed site whose row lies in the read set is `cylAt`-measurable. -/
lemma measurable_rhoStepAt (p : ℝ) (m : ℕ) (j : Fin N) (y : ℤ)
    (S : Finset (Fin N × ℤ × ℕ))
    (hy : ∀ k' ∈ Finset.Icc 1 (m - 1), (j, y, k') ∈ S) :
    Measurable[cylAt (N := N) S] (fun U : Array N => SwarmMarks.rhoOf p (markB p m j y U)) := by
  have hmk : Measurable[cylAt (N := N) S] (fun U : Array N => markB p m j y U) := by
    letI : MeasurableSpace (Array N) := cylAt (N := N) S
    refine measurable_to_bool ?_
    have hset : {U : Array N | markB p m j y U = true} = {U : Array N | SiteMark p m U j y} := by
      ext U
      simp only [Set.mem_ofPred_eq]
      exact ⟨fun hh => by
        by_contra hc
        rw [markB_neg hc] at hh
        exact Bool.false_ne_true hh, fun hh => markB_pos hh⟩
    rw [hset]
    have hEq : {U : Array N | SiteMark p m U j y} =
        ⋂ k' ∈ Finset.Icc 1 (m - 1), {U : Array N | p < U (j, y, k')} := by
      ext U
      simp only [SiteMark, Set.mem_ofPred_eq, Set.mem_iInter]
    rw [hEq]
    exact Finset.measurableSet_biInter _ (fun k' hk' =>
      measurableSet_cylAt_of_mem (hy k' hk') measurableSet_Ioi)
  exact (SwarmMarks.measurable_rhoOf p).comp hmk

/-- The multiplier at the `(g+1)`-st site above the record is `infoPiece (g+1)`-measurable. -/
theorem measurable_rhoStep_infoPiece {p : ℝ} (m n : ℕ) (j : Fin N) (g : ℕ) :
    Measurable[infoPiece (N := N) p m n j (g + 1)] (rhoStep p m n j (g + 1)) := by
  refine measurable_pieceMeas (f' := fun γ U =>
    SwarmMarks.rhoOf p (markB p m j (recVal j γ + ((g + 1 : ℕ) : ℤ)) U)) (fun γ => ?_) ?_
  · exact measurable_rhoStepAt p m j (recVal j γ + ((g + 1 : ℕ) : ℤ)) (recInfo (N := N) m j (g + 1) γ)
      (fun k' hk' => recInfo_row_mem j (g + 1) γ le_rfl hk')
  · intro γ U hU
    show SwarmMarks.rhoOf p (markSeq p m n j U (g + 1)) = _
    have hseq : markSeq p m n j U (g + 1)
        = markB p m j (recVal j γ + ((g + 1 : ℕ) : ℤ)) U := by
      rw [show markSeq p m n j U (g + 1)
        = markB p m j (recVal j (prefOf p m n U) + ((g + 1 : ℕ) : ℤ)) U from rfl,
        recVal_prefOf_of_mem hU j]
    rw [hseq]

/-- **Measurability of the shifted-seed potential.** -/
theorem measurable_shiftG {p : ℝ} (m n : ℕ) (j : Fin N) {h0 : Array N → ℝ}
    (hh0 : Measurable[enlRecMeas (N := N) p m n j] h0) (g : ℕ) :
    Measurable[infoPiece (N := N) p m n j g] (shiftG h0 p m n j g) := by
  induction g with
  | zero =>
      rw [shiftG_zero]
      exact fun s hs => enlRecMeas_le_infoPiece p m n j 0 (h0 ⁻¹' s) (hh0 hs)
  | succ k ih =>
      rw [shiftG_succ]
      have hmono : infoPiece (N := N) p m n j k ≤ infoPiece (N := N) p m n j (k + 1) :=
        infoPiece_mono p m n j (Nat.le_succ k)
      have ih' : Measurable[infoPiece (N := N) p m n j (k + 1)] (shiftG h0 p m n j k) :=
        fun s hs => hmono (shiftG h0 p m n j k ⁻¹' s) (ih hs)
      exact measurable_const.add ((measurable_rhoStep_infoPiece m n j k).mul
        (measurable_const.add ih'))

/-! ### Deterministic bounds and integrability -/

lemma abs_shiftG_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {h0 : Array N → ℝ} {c : ℝ} (hc : ∀ U, |h0 U| ≤ c) (m n : ℕ) (j : Fin N) (g : ℕ)
    (U : Array N) : |shiftG h0 p m n j g U| ≤ c + 2 * (g : ℝ) + 2 := by
  induction g with
  | zero =>
      rw [shiftG_zero]
      have := hc U
      push_cast
      linarith
  | succ k ih =>
      rw [shiftG_succ]
      set X := rhoStep p m n j (k + 1) U with hX
      set Y := shiftG h0 p m n j k U with hY
      have hr : |X| ≤ 1 := abs_rhoStep_le hp1 hp2 m n j (k + 1) U
      have h1 : |1 + X * (1 + Y)| ≤ 1 + |1 + Y| := by
        have h := abs_add_le (1 : ℝ) (X * (1 + Y))
        rw [abs_one, abs_mul] at h
        have h2 : |X| * |1 + Y| ≤ 1 * |1 + Y| :=
          mul_le_mul_of_nonneg_right hr (abs_nonneg _)
        linarith
      have h2 : |1 + Y| ≤ 1 + |Y| := by
        have h := abs_add_le (1 : ℝ) Y
        rwa [abs_one] at h
      have hih : |Y| ≤ c + 2 * (k : ℝ) + 2 := ih
      push_cast
      linarith

lemma integrable_shiftG {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n : ℕ) (j : Fin N)
    {h0 : Array N → ℝ} {c : ℝ} (hc : ∀ U, |h0 U| ≤ c)
    (hh0 : Measurable[enlRecMeas (N := N) p m n j] h0) (g : ℕ) :
    Integrable (shiftG h0 p m n j g) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  refine Integrable.mono' (integrable_const (c + 2 * (g : ℝ) + 2)) ?_ ?_
  · have hmeas : Measurable (shiftG h0 p m n j g) :=
      fun s hs => infoPiece_le p m n j g (shiftG h0 p m n j g ⁻¹' s)
        ((measurable_shiftG (h0 := h0) m n j hh0 g) hs)
    exact hmeas.aestronglyMeasurable
  · filter_upwards with U
    calc ‖shiftG h0 p m n j g U‖ = |shiftG h0 p m n j g U| := Real.norm_eq_abs _
      _ ≤ c + 2 * (g : ℝ) + 2 := abs_shiftG_le hp1 hp2 hc m n j g U

lemma integrable_rhoStep_mul_shiftG {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n : ℕ) (j : Fin N)
    {h0 : Array N → ℝ} {c : ℝ} (hc : ∀ U, |h0 U| ≤ c)
    (hh0 : Measurable[enlRecMeas (N := N) p m n j] h0) (g : ℕ) :
    Integrable (fun U => rhoStep p m n j (g + 1) U * (1 + shiftG h0 p m n j g U))
      (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  refine Integrable.mono' (integrable_const (c + 2 * (g : ℝ) + 3)) ?_ ?_
  · have h1 : Measurable (rhoStep p m n j (g + 1)) := measurable_rhoStep p m n j (g + 1)
    have h2 : Measurable (shiftG h0 p m n j g) :=
      fun s hs => infoPiece_le p m n j g (shiftG h0 p m n j g ⁻¹' s)
        ((measurable_shiftG (h0 := h0) m n j hh0 g) hs)
    exact (h1.mul (measurable_const.add h2)).aestronglyMeasurable
  · filter_upwards with U
    have hr : |rhoStep p m n j (g + 1) U| ≤ 1 := abs_rhoStep_le hp1 hp2 m n j (g + 1) U
    have hb : |shiftG h0 p m n j g U| ≤ c + 2 * (g : ℝ) + 2 := abs_shiftG_le hp1 hp2 hc m n j g U
    have h1 : |1 + shiftG h0 p m n j g U| ≤ 1 + |shiftG h0 p m n j g U| := by
      have h := abs_add_le (1 : ℝ) (shiftG h0 p m n j g U)
      rwa [abs_one] at h
    calc ‖rhoStep p m n j (g + 1) U * (1 + shiftG h0 p m n j g U)‖
        = |rhoStep p m n j (g + 1) U| * |1 + shiftG h0 p m n j g U| := by
          rw [Real.norm_eq_abs, abs_mul]
      _ ≤ 1 * (1 + |shiftG h0 p m n j g U|) := mul_le_mul hr h1 (abs_nonneg _) zero_le_one
      _ ≤ c + 2 * (g : ℝ) + 3 := by linarith

/-! ### The conditional recursion -/

/-- **The one-step recursion for an arbitrary seed.** -/
theorem condExp_shiftG_succ {p : ℝ} (hp0 : p ≠ 0) (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m : ℕ) {n : ℕ} (j : Fin N)
    {h0 : Array N → ℝ} {c : ℝ} (hc : ∀ U, |h0 U| ≤ c)
    (hh0 : Measurable[enlRecMeas (N := N) p m n j] h0)
    (hint : Integrable h0 (arrayMeasure N)) (g : ℕ) :
    condExp (infoPiece (N := N) p m n j g) (arrayMeasure N) (shiftG h0 p m n j (g + 1))
      =ᵐ[arrayMeasure N] fun U => 1 + aRec p m * (1 + shiftG h0 p m n j g U) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  set μ := arrayMeasure N with hμ
  have hle : infoPiece (N := N) p m n j g ≤ (inferInstance : MeasurableSpace (Array N)) :=
    infoPiece_le p m n j g
  have hpt : shiftG h0 p m n j (g + 1)
      = fun U => 1 + rhoStep p m n j (g + 1) U * (1 + shiftG h0 p m n j g U) := shiftG_succ h0 p m n j g
  have hY : StronglyMeasurable[infoPiece (N := N) p m n j g]
      (fun U => 1 + shiftG h0 p m n j g U) :=
    (measurable_const.add (measurable_shiftG m n j hh0 g)).stronglyMeasurable
  have hXY : Integrable (fun U => rhoStep p m n j (g + 1) U * (1 + shiftG h0 p m n j g U)) μ :=
    integrable_rhoStep_mul_shiftG hp1 hp2 m n j hc hh0 g
  have hX : Integrable (rhoStep p m n j (g + 1)) μ := integrable_rhoStep hp1 hp2 m n j (g + 1)
  have e1 : condExp (infoPiece p m n j g) μ (fun U =>
        1 + rhoStep p m n j (g + 1) U * (1 + shiftG h0 p m n j g U))
      =ᵐ[μ] condExp (infoPiece p m n j g) μ (fun _ : Array N => (1 : ℝ)) +
        condExp (infoPiece p m n j g) μ
          (fun U => rhoStep p m n j (g + 1) U * (1 + shiftG h0 p m n j g U)) :=
    condExp_add (integrable_const 1) hXY _
  have e2 : condExp (infoPiece p m n j g) μ
        (fun U => rhoStep p m n j (g + 1) U * (1 + shiftG h0 p m n j g U))
      =ᵐ[μ] condExp (infoPiece p m n j g) μ (rhoStep p m n j (g + 1)) *
        (fun U => 1 + shiftG h0 p m n j g U) :=
    condExp_mul_of_stronglyMeasurable_right hY hXY hX
  have e3 : condExp (infoPiece p m n j g) μ (rhoStep p m n j (g + 1))
      =ᵐ[μ] fun _ : Array N => aRec p m := condExp_rhoStep hp0 hp1 hp2 m j g
  have e4 : condExp (infoPiece p m n j g) μ (fun _ : Array N => (1 : ℝ)) =ᵐ[μ] fun _ => 1 :=
    Filter.EventuallyEq.of_eq (condExp_const (μ := μ) (m := infoPiece p m n j g) hle (1 : ℝ))
  rw [hpt]
  filter_upwards [e1, e2, e3, e4] with U h1U h2U h3U h4U
  simp only [Pi.add_apply, Pi.mul_apply] at h1U h2U h3U h4U ⊢
  rw [h1U, h2U, h3U, h4U]

/-- **The projected recursion for an arbitrary seed:**
`E[Φ^g h0 | enlRecMeas] = Φ_det^g h0` almost surely. -/
theorem condExp_shiftG {p : ℝ} (hp0 : p ≠ 0) (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m : ℕ) {n : ℕ} (j : Fin N)
    {h0 : Array N → ℝ} {c : ℝ} (hc : ∀ U, |h0 U| ≤ c)
    (hh0 : Measurable[enlRecMeas (N := N) p m n j] h0)
    (hint : Integrable h0 (arrayMeasure N)) (g : ℕ) :
    condExp (enlRecMeas (N := N) p m n j) (arrayMeasure N) (shiftG h0 p m n j g)
      =ᵐ[arrayMeasure N] fun U => phiIter (aRec p m) g (h0 U) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  set μ := arrayMeasure N with hμ
  induction g with
  | zero =>
      rw [shiftG_zero]
      have hs : StronglyMeasurable[enlRecMeas (N := N) p m n j] h0 :=
        hh0.stronglyMeasurable
      exact Filter.EventuallyEq.of_eq
        (condExp_of_stronglyMeasurable (μ := μ) (enlRecMeas_le p m n j) hs hint)
  | succ k ih =>
      have hm₀ : enlRecMeas (N := N) p m n j ≤ (inferInstance : MeasurableSpace (Array N)) :=
        enlRecMeas_le p m n j
      have hmk : infoPiece (N := N) p m n j k ≤ (inferInstance : MeasurableSpace (Array N)) :=
        infoPiece_le p m n j k
      have hmono : enlRecMeas (N := N) p m n j ≤ infoPiece (N := N) p m n j k :=
        enlRecMeas_le_infoPiece p m n j k
      have htower : condExp (enlRecMeas p m n j) μ (shiftG h0 p m n j (k + 1))
          =ᵐ[μ] condExp (enlRecMeas p m n j) μ
            (condExp (infoPiece p m n j k) μ (shiftG h0 p m n j (k + 1))) :=
        (condExp_condExp_of_le (μ := μ) hmono hmk).symm
      have hinner : condExp (infoPiece p m n j k) μ (shiftG h0 p m n j (k + 1))
          =ᵐ[μ] fun U => 1 + aRec p m * (1 + shiftG h0 p m n j k U) :=
        condExp_shiftG_succ hp0 hp1 hp2 m j hc hh0 hint k
      have haff := condExp_affine_gen (m := enlRecMeas p m n j) (μ := μ) hm₀
        (shiftG h0 p m n j k) (integrable_shiftG hp1 hp2 m n j hc hh0 k) (aRec p m)
      calc condExp (enlRecMeas p m n j) μ (shiftG h0 p m n j (k + 1))
          =ᵐ[μ] condExp (enlRecMeas p m n j) μ
              (condExp (infoPiece p m n j k) μ (shiftG h0 p m n j (k + 1))) := htower
        _ =ᵐ[μ] condExp (enlRecMeas p m n j) μ
              (fun U => 1 + aRec p m * (1 + shiftG h0 p m n j k U)) :=
            condExp_congr_ae hinner
        _ =ᵐ[μ] fun U => 1 + aRec p m * (1 + condExp (enlRecMeas p m n j) μ
              (shiftG h0 p m n j k) U) := haff
        _ =ᵐ[μ] fun U => phiIter (aRec p m) (k + 1) (h0 U) := by
            filter_upwards [ih] with U hU
            rw [phiIter_succ, hU]

/-- `shiftH` is the special case of `shiftG` with the empty past at the record, `h(-1) = 1`. -/
theorem shiftH_eq_shiftG {p : ℝ} (hp0 : p ≠ 0) (m n : ℕ) (j : Fin N) (g : ℕ) :
    shiftH p m n j g
      = shiftG (fun U => SwarmMarks.hstep p (markSeq p m n j U 0) 1) p m n j g := by
  induction g with
  | zero => rfl
  | succ k ih =>
      funext U
      rw [shiftH_succ hp0, shiftG_succ,
        show shiftH p m n j k U
          = shiftG (fun U => SwarmMarks.hstep p (markSeq p m n j U 0) 1) p m n j k U
          from congrFun ih U]

end Swarming.Enl


