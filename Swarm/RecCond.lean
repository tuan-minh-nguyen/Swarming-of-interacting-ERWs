/-
  **The projected recursion `e_{g+1} = 1 + a (1 + e_g)` on the record-enlarged environment.**

  Contents:

  * `setIntegral_rhoStep` — the one-site multiplier at the `(g+1)`-st site above the record has
    set integral `aRec p m · μ.real A` over every `infoPiece g`-measurable `A`;
  * `condExp_rhoStep` — its conditional mean given `infoPiece g` is the constant `aRec p m`;
  * `condExp_shiftH_succ` — the one-step recursion
    `E[h(M+g+1) | infoPiece g] = 1 + a (1 + h(M+g))`;
  * `condExp_affine_gen` — the affine pull-out for an arbitrary σ-algebra below the ambient one;
  * `phiIter`, `condExp_shiftH` — the iteration `E[h(M+g) | enlRecMeas] = Φ^g (h(M))` with
    `Φ(h) = 1 + a (1 + h)`;
  * `eSeq`, `eSeq_succ`, `eSeq_eq_condExp` — `(projh)` as a statement about `arrayMeasure N`.

  The `0 ≤ M_n^j` restriction is *kept*: `recSet_eq_univ` shows that event is the whole space
  (`runMax` dominates the initial position `0`), and `condExp_shiftH_indicator` states the
  recursion with the indicator of that event on both sides.
-/
import Swarm.RecExp

set_option linter.unusedVariables false
set_option warn.classDefReducibility false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory

variable {N : ℕ}

/-! ### Preparations -/

/-- The zeroth record information is the record-enlarged σ-algebra. -/
lemma infoPiece_zero (p : ℝ) (m n : ℕ) (j : Fin N) :
    infoPiece (N := N) p m n j 0 = enlRecMeas (N := N) p m n j := by
  unfold infoPiece enlRecMeas
  congr 1
  funext γ
  simp [recInfo]

/-- The site mark at the random site `M_n^j + g + 1` is ambient measurable. -/
lemma measurableSet_randomSiteMark (p : ℝ) (m n : ℕ) (j : Fin N) (g : ℕ) :
    MeasurableSet {U : Array N |
      SiteMark p m U j (recVal j (prefOf p m n U) + ((g + 1 : ℕ) : ℤ))} := by
  have hfib : ∀ y : ℤ,
      MeasurableSet {U : Array N | recVal j (prefOf p m n U) + ((g + 1 : ℕ) : ℤ) = y} := by
    intro y
    have hset : {U : Array N | recVal j (prefOf p m n U) + ((g + 1 : ℕ) : ℤ) = y} =
        {U : Array N | recVal j (prefOf p m n U) = y - ((g + 1 : ℕ) : ℤ)} := by
      ext U
      simp only [Set.mem_ofPred_eq]
      constructor <;> intro h <;> omega
    rw [hset]
    exact measurableSet_recVal_eq_ambient p m n j (y - ((g + 1 : ℕ) : ℤ))
  have h : Measurable fun U : Array N =>
      markB p m j (recVal j (prefOf p m n U) + ((g + 1 : ℕ) : ℤ)) U :=
    SwarmIID.measurable_of_countable_pieces (Ω := Array N)
      (U := fun y : ℤ => fun U : Array N => markB p m j y U)
      (fun y => measurable_markB_fixed p m j y)
      (fun U : Array N => recVal j (prefOf p m n U) + ((g + 1 : ℕ) : ℤ)) hfib
  have hEq : ((fun U : Array N =>
      markB p m j (recVal j (prefOf p m n U) + ((g + 1 : ℕ) : ℤ)) U) ⁻¹' {true}) =
      {U : Array N | SiteMark p m U j (recVal j (prefOf p m n U) + ((g + 1 : ℕ) : ℤ))} := by
    ext U
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    exact ⟨fun hh => by
      by_contra hc
      rw [markB_neg hc] at hh
      exact Bool.false_ne_true hh, fun hh => markB_pos hh⟩
  rw [← hEq]
  exact h (measurableSet_singleton true)

/-- **The multiplier's set integral.**  Over any `infoPiece g`-measurable event, the one-site
multiplier at the site `M_n^j + g + 1` integrates to `aRec p m` times the mass. -/
theorem setIntegral_rhoStep {p : ℝ} (hp0 : p ≠ 0) (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m : ℕ) {n : ℕ} (j : Fin N) (g : ℕ) {A : Set (Array N)}
    (hA : MeasurableSet[infoPiece p m n j g] A) :
    ∫ U in A, rhoStep p m n j (g + 1) U ∂(arrayMeasure N) =
      aRec p m * (arrayMeasure N).real A := by
  classical
  set μ := arrayMeasure N with hμ
  haveI : IsProbabilityMeasure μ := arrayMeasure_isProbabilityMeasure N
  have hA0 : MeasurableSet A := infoPiece_le p m n j g A hA
  set SS : Set (Array N) :=
    {U : Array N | SiteMark p m U j (recVal j (prefOf p m n U) + ((g + 1 : ℕ) : ℤ))} with hSSdef
  have hSS0 : MeasurableSet SS := measurableSet_randomSiteMark p m n j g
  have hstep : ∀ U, rhoStep p m n j (g + 1) U =
      1 + (SwarmMarks.rhoOf p true - 1) * SS.indicator (fun _ => (1 : ℝ)) U := by
    intro U
    have hunf : rhoStep p m n j (g + 1) U = SwarmMarks.rhoOf p
        (markB p m j (recVal j (prefOf p m n U) + ((g + 1 : ℕ) : ℤ)) U) := rfl
    rw [hunf]
    by_cases h : SiteMark p m U j (recVal j (prefOf p m n U) + ((g + 1 : ℕ) : ℤ))
    · rw [rhoOf_markB_pos h]
      have hmem : U ∈ SS := by simpa [hSSdef] using h
      rw [Set.indicator_of_mem hmem]
      ring
    · rw [rhoOf_markB_neg h]
      have hnot : U ∉ SS := by simpa [hSSdef] using h
      rw [Set.indicator_of_notMem hnot]
      ring
  -- the integral of the mass at the fresh random site
  have hmass : μ.real (A ∩ SS) = (1 - p) ^ (m - 1) * μ.real A := by
    refine setIntegral_siteMark_gen (p := p) (hp0 := by linarith) (hp1 := hp2) (m := m)
      (S := recInfo (N := N) m j g) (hS := fun γ => prefRead_subset_recInfo j g γ)
      (j := j) (siteF := fun γ => recVal j γ + ((g + 1 : ℕ) : ℤ))
      (hsite := fun γ U hU => by rw [recVal_prefOf_of_mem hU j]) (hfresh := ?_) (hA := hA)
    intro γ k _ hmem
    have hle := recInfo_site_le (m := m) j g γ hmem rfl
    have hlt : ((g : ℕ) : ℤ) < ((g + 1 : ℕ) : ℤ) := by exact_mod_cast Nat.lt_succ_self g
    linarith
  have h1 : Integrable (fun U => A.indicator (fun _ => (1 : ℝ)) U) μ := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (Measurable.indicator measurable_const hA0).aestronglyMeasurable
      (Filter.Eventually.of_forall fun U => ?_)
    rw [Real.norm_eq_abs]
    by_cases hU : U ∈ A <;> simp [hU]
  have h2 : Integrable (fun U => (A ∩ SS).indicator (fun _ => (SwarmMarks.rhoOf p true - 1)) U) μ := by
    refine Integrable.mono' (integrable_const |SwarmMarks.rhoOf p true - 1|)
      (Measurable.indicator measurable_const (hA0.inter hSS0)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun U => ?_)
    rw [Real.norm_eq_abs]
    by_cases hU : U ∈ A ∩ SS <;> simp [hU]
  have hsplit : (fun U => A.indicator
      (fun U => 1 + (SwarmMarks.rhoOf p true - 1) * SS.indicator (fun _ => (1 : ℝ)) U) U) =
      fun U => A.indicator (fun _ => (1 : ℝ)) U +
        (A ∩ SS).indicator (fun _ => (SwarmMarks.rhoOf p true - 1)) U := by
    funext U
    by_cases hU : U ∈ A <;> by_cases hS : U ∈ SS <;> simp [hU, hS]
  rw [← integral_indicator hA0]
  rw [show (fun U => A.indicator (rhoStep p m n j (g + 1)) U) = fun U => A.indicator
      (fun U => 1 + (SwarmMarks.rhoOf p true - 1) * SS.indicator (fun _ => (1 : ℝ)) U) U from by
    funext U
    by_cases hU : U ∈ A
    · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU, hstep U]
    · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]]
  have hadd : ∫ U, (fun U => A.indicator (fun _ => (1 : ℝ)) U +
        (A ∩ SS).indicator (fun _ => (SwarmMarks.rhoOf p true - 1)) U) U ∂μ
      = ∫ U, A.indicator (fun _ => (1 : ℝ)) U ∂μ +
        ∫ U, (A ∩ SS).indicator (fun _ => (SwarmMarks.rhoOf p true - 1)) U ∂μ :=
    integral_add h1 h2
  rw [hsplit, hadd]
  have h1val : ∫ U, A.indicator (fun _ => (1 : ℝ)) U ∂μ = μ.real A := by
    rw [integral_indicator hA0, setIntegral_const, smul_eq_mul, mul_one]
  rw [h1val]
  have h2val : ∫ U, (A ∩ SS).indicator (fun _ => (SwarmMarks.rhoOf p true - 1)) U ∂μ
      = (SwarmMarks.rhoOf p true - 1) * μ.real (A ∩ SS) := by
    rw [integral_indicator (hA0.inter hSS0), setIntegral_const, smul_eq_mul, mul_comm]
  have hq : aRec p m = 1 + (SwarmMarks.rhoOf p true - 1) * (1 - p) ^ (m - 1) := aRec_eq hp0 m
  rw [h2val, hmass, hq]
  ring

/-- **The conditional mean of the fresh multiplier.** -/
theorem condExp_rhoStep {p : ℝ} (hp0 : p ≠ 0) (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m : ℕ) {n : ℕ} (j : Fin N) (g : ℕ) :
    condExp (infoPiece (N := N) p m n j g) (arrayMeasure N) (rhoStep p m n j (g + 1))
      =ᵐ[arrayMeasure N] fun _ => aRec p m := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hle : infoPiece (N := N) p m n j g ≤ (inferInstance : MeasurableSpace (Array N)) :=
    infoPiece_le p m n j g
  refine (ae_eq_condExp_of_forall_setIntegral_eq hle
    (integrable_rhoStep hp1 hp2 m n j (g + 1)) ?_ ?_
    stronglyMeasurable_const.aestronglyMeasurable).symm
  · intro s _ hs
    exact (integrable_const (aRec p m)).integrableOn
  · intro s hs _
    rw [setIntegral_const, smul_eq_mul, mul_comm]
    exact (setIntegral_rhoStep hp0 hp1 hp2 m j g hs).symm

/-! ### The one-step recursion -/

/-- The coefficient pulling a constant out of a conditional expectation. -/
theorem condExp_affine_gen {m m₀ : MeasurableSpace (Array N)} {μ : Measure (Array N)}
    [IsFiniteMeasure μ] (hm : m ≤ m₀)
    (f : Array N → ℝ) (hf : Integrable f μ) (c : ℝ) :
    condExp m μ (fun U => 1 + c * (1 + f U))
      =ᵐ[μ] fun U => 1 + c * (1 + condExp m μ f U) := by
  set g : Array N → ℝ := fun U => 1 + f U with hg
  have hgint : Integrable g μ := by
    have h : Integrable ((fun _ : Array N => (1 : ℝ)) + f) μ := (integrable_const 1).add hf
    refine h.congr (Filter.Eventually.of_forall fun U => ?_)
    simp [hg, Pi.add_apply]
  have e1 : condExp m μ (fun U => 1 + c * g U)
      =ᵐ[μ] condExp m μ ((fun _ : Array N => (1 : ℝ)) + c • g) :=
    condExp_congr_ae (Filter.Eventually.of_forall fun U => by
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul])
  have e2 : condExp m μ ((fun _ : Array N => (1 : ℝ)) + c • g)
      =ᵐ[μ] condExp m μ (fun _ : Array N => (1 : ℝ)) + condExp m μ (c • g) :=
    condExp_add (integrable_const 1) (hgint.const_mul c) m
  have e3 : condExp m μ (fun _ : Array N => (1 : ℝ)) =ᵐ[μ] fun _ => 1 :=
    Filter.EventuallyEq.of_eq (condExp_const (μ := μ) (m := m) hm (1 : ℝ))
  have e4 : condExp m μ (c • g) =ᵐ[μ] c • condExp m μ g := condExp_smul c g m
  have e5 : condExp m μ g =ᵐ[μ] condExp m μ ((fun _ : Array N => (1 : ℝ)) + f) :=
    condExp_congr_ae (Filter.Eventually.of_forall fun U => by simp [hg, Pi.add_apply])
  have e6 : condExp m μ ((fun _ : Array N => (1 : ℝ)) + f)
      =ᵐ[μ] condExp m μ (fun _ : Array N => (1 : ℝ)) + condExp m μ f :=
    condExp_add (integrable_const 1) hf m
  filter_upwards [e1, e2, e3, e4, e5, e6] with U h1U h2U h3U h4U h5U h6U
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1U h2U h3U h4U h5U h6U ⊢
  rw [h1U, h2U, h3U, h4U, h5U, h6U, h3U]

/-- **The one-step conditional recursion above the record.** -/
theorem condExp_shiftH_succ {p : ℝ} (hp0 : p ≠ 0) (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m : ℕ) {n : ℕ} (j : Fin N) (g : ℕ) :
    condExp (infoPiece (N := N) p m n j g) (arrayMeasure N) (shiftH p m n j (g + 1))
      =ᵐ[arrayMeasure N] fun U => 1 + aRec p m * (1 + shiftH p m n j g U) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  set μ := arrayMeasure N with hμ
  have hle : infoPiece (N := N) p m n j g ≤ (inferInstance : MeasurableSpace (Array N)) :=
    infoPiece_le p m n j g
  have hpt : shiftH p m n j (g + 1)
      = fun U => 1 + rhoStep p m n j (g + 1) U * (1 + shiftH p m n j g U) := by
    funext U
    rw [shiftH_succ hp0]
  have hY : StronglyMeasurable[infoPiece (N := N) p m n j g]
      (fun U => 1 + shiftH p m n j g U) := stronglyMeasurable_shiftH hp0 m n j g
  have hXY : Integrable (fun U => rhoStep p m n j (g + 1) U * (1 + shiftH p m n j g U)) μ :=
    integrable_rhoStep_mul_shiftH hp1 hp2 hp0 m n j g
  have hX : Integrable (rhoStep p m n j (g + 1)) μ := integrable_rhoStep hp1 hp2 m n j (g + 1)
  have e1 : condExp (infoPiece p m n j g) μ (fun U =>
        1 + rhoStep p m n j (g + 1) U * (1 + shiftH p m n j g U))
      =ᵐ[μ] condExp (infoPiece p m n j g) μ (fun _ : Array N => (1 : ℝ)) +
        condExp (infoPiece p m n j g) μ
          (fun U => rhoStep p m n j (g + 1) U * (1 + shiftH p m n j g U)) :=
    condExp_add (integrable_const 1) hXY _
  have e2 : condExp (infoPiece p m n j g) μ
        (fun U => rhoStep p m n j (g + 1) U * (1 + shiftH p m n j g U))
      =ᵐ[μ] condExp (infoPiece p m n j g) μ (rhoStep p m n j (g + 1)) *
        (fun U => 1 + shiftH p m n j g U) :=
    condExp_mul_of_stronglyMeasurable_right hY hXY hX
  have e3 : condExp (infoPiece p m n j g) μ (rhoStep p m n j (g + 1))
      =ᵐ[μ] fun _ : Array N => aRec p m := condExp_rhoStep hp0 hp1 hp2 m j g
  have e4 : condExp (infoPiece p m n j g) μ (fun _ : Array N => (1 : ℝ)) =ᵐ[μ] fun _ => 1 :=
    Filter.EventuallyEq.of_eq (condExp_const (μ := μ) (m := infoPiece p m n j g) hle (1 : ℝ))
  rw [hpt]
  filter_upwards [e1, e2, e3, e4] with U h1U h2U h3U h4U
  simp only [Pi.add_apply, Pi.mul_apply] at h1U h2U h3U h4U ⊢
  rw [h1U, h2U, h3U, h4U]

/-! ### The iteration: `(projh)` -/

/-- The affine iteration `Φ^g` with `Φ(h) = 1 + a (1 + h)`. -/
noncomputable def phiIter (a : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun h => h
  | (g + 1) => fun h => 1 + a * (1 + phiIter a g h)

lemma phiIter_succ (a : ℝ) (g : ℕ) (h : ℝ) :
    phiIter a (g + 1) h = 1 + a * (1 + phiIter a g h) := rfl

lemma phiIter_zero (a : ℝ) (h : ℝ) : phiIter a 0 h = h := rfl

/-- **The projected recursion.**  `E[h_j(M_n^j + g) | enlRecMeas]` is the `g`-fold affine
iteration of `h_j(M_n^j)`, so it satisfies `e_{g+1} = 1 + a (1 + e_g)`. -/
theorem condExp_shiftH {p : ℝ} (hp0 : p ≠ 0) (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m : ℕ) {n : ℕ} (j : Fin N) (g : ℕ) :
    condExp (enlRecMeas (N := N) p m n j) (arrayMeasure N) (shiftH p m n j g)
      =ᵐ[arrayMeasure N] fun U => phiIter (aRec p m) g (shiftH p m n j 0 U) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  set μ := arrayMeasure N with hμ
  induction g with
  | zero =>
      have hs : StronglyMeasurable[enlRecMeas (N := N) p m n j] (shiftH p m n j 0) := by
        have h0 := (measurable_shiftH (p := p) hp0 m n j 0).stronglyMeasurable
        rwa [infoPiece_zero] at h0
      have hce := condExp_of_stronglyMeasurable (μ := μ) (enlRecMeas_le p m n j) hs
        (integrable_shiftH hp1 hp2 hp0 m n j 0)
      exact Filter.EventuallyEq.of_eq hce
  | succ k ih =>
      have hm₀ : enlRecMeas (N := N) p m n j ≤ (inferInstance : MeasurableSpace (Array N)) :=
        enlRecMeas_le p m n j
      have hmk : infoPiece (N := N) p m n j k ≤ (inferInstance : MeasurableSpace (Array N)) :=
        infoPiece_le p m n j k
      have hmono : enlRecMeas (N := N) p m n j ≤ infoPiece (N := N) p m n j k :=
        enlRecMeas_le_infoPiece p m n j k
      have htower : condExp (enlRecMeas p m n j) μ (shiftH p m n j (k + 1))
          =ᵐ[μ] condExp (enlRecMeas p m n j) μ
            (condExp (infoPiece p m n j k) μ (shiftH p m n j (k + 1))) :=
        (condExp_condExp_of_le (μ := μ) hmono hmk).symm
      have hinner : condExp (infoPiece p m n j k) μ (shiftH p m n j (k + 1))
          =ᵐ[μ] fun U => 1 + aRec p m * (1 + shiftH p m n j k U) :=
        condExp_shiftH_succ hp0 hp1 hp2 m j k
      have haff := condExp_affine_gen (m := enlRecMeas p m n j) (μ := μ) hm₀
        (shiftH p m n j k) (integrable_shiftH hp1 hp2 hp0 m n j k) (aRec p m)
      calc condExp (enlRecMeas p m n j) μ (shiftH p m n j (k + 1))
          =ᵐ[μ] condExp (enlRecMeas p m n j) μ
              (condExp (infoPiece p m n j k) μ (shiftH p m n j (k + 1))) := htower
        _ =ᵐ[μ] condExp (enlRecMeas p m n j) μ
              (fun U => 1 + aRec p m * (1 + shiftH p m n j k U)) :=
            condExp_congr_ae hinner
        _ =ᵐ[μ] fun U => 1 + aRec p m * (1 + condExp (enlRecMeas p m n j) μ
              (shiftH p m n j k) U) := haff
        _ =ᵐ[μ] fun U => phiIter (aRec p m) (k + 1) (shiftH p m n j 0 U) := by
            filter_upwards [ih] with U hU
            rw [phiIter_succ, hU]

/-- The event `{0 ≤ M_n^j}` on which the record may be read as a natural number. -/
noncomputable def recNonneg (p : ℝ) (m : ℕ) (n : ℕ) (j : Fin N) : Set (Array N) :=
  {U : Array N | 0 ≤ runMax p m U j n}

/-- `{0 ≤ M_n^j}` is the whole space: the running maximum dominates the initial position `0`. -/
lemma recNonneg_eq_univ (p : ℝ) (m : ℕ) (n : ℕ) (j : Fin N) :
    recNonneg (N := N) p m n j = Set.univ := by
  ext U
  simp only [recNonneg, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact zero_le_runMax p m U j n

/-- **The recursion with the `0 ≤ M_n^j` restriction kept on both sides.** -/
theorem condExp_shiftH_indicator {p : ℝ} (hp0 : p ≠ 0) (hp1 : (1 : ℝ) / 2 < p)
    (hp2 : p < 1) (m : ℕ) {n : ℕ} (j : Fin N) (g : ℕ) :
    condExp (enlRecMeas (N := N) p m n j) (arrayMeasure N)
        ((recNonneg (N := N) p m n j).indicator (shiftH p m n j g))
      =ᵐ[arrayMeasure N] (recNonneg (N := N) p m n j).indicator
        (fun U => phiIter (aRec p m) g (shiftH p m n j 0 U)) := by
  rw [recNonneg_eq_univ, Set.indicator_univ, Set.indicator_univ]
  exact condExp_shiftH hp0 hp1 hp2 m j g

/-- The projected sequence `e_g` of the paper: `e_g = Φ^g (h_j(M_n^j))`. -/
noncomputable def eSeq (p : ℝ) (m : ℕ) (n : ℕ) (j : Fin N) (g : ℕ) (U : Array N) : ℝ :=
  phiIter (aRec p m) g (shiftH p m n j 0 U)

/-- **The recursion `e_{g+1} = 1 + a (1 + e_g)`.** -/
theorem eSeq_succ (p : ℝ) (m n : ℕ) (j : Fin N) (g : ℕ) (U : Array N) :
    eSeq p m n j (g + 1) U = 1 + aRec p m * (1 + eSeq p m n j g U) := by
  simp only [eSeq, phiIter_succ]

/-- **`e_g` is the conditional mean of `h_j(M_n^j + g)` given the record-enlarged information.** -/
theorem eSeq_eq_condExp {p : ℝ} (hp0 : p ≠ 0) (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m : ℕ) {n : ℕ} (j : Fin N) (g : ℕ) :
    eSeq p m n j g
      =ᵐ[arrayMeasure N] condExp (enlRecMeas (N := N) p m n j) (arrayMeasure N)
        (shiftH p m n j g) :=
  (condExp_shiftH hp0 hp1 hp2 m j g).symm

/-- The seed: `e_0 = h_j(M_n^j) = 1 + rho(M_n^j) · 2`, the record mark being part of the
record-enlarged information by `measurableSet_recRow`. -/
theorem eSeq_zero (p : ℝ) (m n : ℕ) (j : Fin N) (U : Array N) :
    eSeq p m n j 0 U = SwarmMarks.hstep p (markB p m j (recVal j (prefOf p m n U) + ((0 : ℕ) : ℤ)) U) 1 :=
  rfl

end Swarming.Enl


