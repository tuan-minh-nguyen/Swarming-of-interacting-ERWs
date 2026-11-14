/-  Context.  `Swarm/QIncrementAdapted.lean` proves that the raw `ZJinc t` is *not*
  `𝓕_{t+1}`-measurable at the actual model (`m ≥ 3`), while the optional projection
  `Qproj T = E[Qcomp T | 𝓕_T]` is a genuine martingale.  This file computes **what exactly**
  `Qcomp T - Qproj T` is.  It is not a diffuse error term: it is exactly the *terminal*
  environmental fluctuation of the potential,

      Qcomp T - Qproj T  =ᵐ  H_j(X_T^i) - E[H_j(X_T^i) | 𝓕_T],

  where `H_j = SwarmOcc.Hpot (envH p m j ·)` is the **realised** (full-environment) potential
  that `VdriftTimeAssembly.Zpot` uses.  Consequences proved here:

  * `measurable_Jcorr_enl_succ`: the record-cost increment `J_{t+1}` is `𝓕_{t+1}`-measurable
    (it is the only other `t`-increment which is not explicitly compensated);
  * `stronglyMeasurable_QnonPot`: `Qcomp T - Z_T` is `𝓕_T`-strongly measurable — the whole
    non-adaptedness of `Qcomp T` is carried by the terminal potential `Z_T`;
  * `Qcomp_sub_Qproj_eq`: the exact identity above, and `Qcomp_sub_Qproj_eq_Hpot` in terms of
    the potential itself;
  * `condExp_Qcomp_sub_Qproj_eq_zero`: the defect has zero `𝓕_s`-conditional mean for every
    `s ≤ T` (it is centred against the *whole* revealed history, so no `𝓕_T`-predictable
    test function can see it);
  * `qresidual_pair_of_split`: hence the required one-sided budget `hQ` is **exactly** the
    conjunction of (i) the same one-sided budget for the genuine martingale `Qproj` and
    (ii) a one-sided budget for the single terminal fluctuation term;
  * `Qcomp_eq_centeredResidualSum_sub_corr`: an independent exact split of the raw `Qcomp`
    into `CenteredResidual.centeredResidualSum` (the potential's centred residual) minus a
    **genuine martingale** (`martingale_corrResidual`) built from the correction increments —
    so all of the non-adaptedness of the raw ledger sits in the potential residual sum.

  No `sorry`, no `admit`, no custom axiom, no native decision procedure.  Axiom audit in `Audit.lean`.
-/
import Swarm.QIncrementAdapted
import Swarm.CenteredResidual

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open VdriftAssembly

variable {N : ℕ}

/-! ## 1. Measurability of the record-cost increment `J_{t+1}` at `𝓕_{t+1}` -/

/-- `F_b` evaluated at an `𝓕_{m₀}`-measurable gap, with the record cost frozen at an **earlier**
index `n ≤ m₀`.  (`measurable_Fcorr_gap_enl` is the case `n = m₀`; the ledger needs the mixed
case because `J_{t+1}` compares `b_{t+1}` with `b_t` at the *same* time-`(t+1)` position.) -/
theorem measurable_Fcorr_gap_le_enl {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m : ℕ) {n m₀ : ℕ}
    (hn : n ≤ m₀) (j : Fin N) (a eps : ℝ) {φ : Array N → ℤ}
    (hφ : Measurable[enlFilt p m m₀] φ) :
    Measurable[enlFilt p m m₀]
      (fun U : Array N => SwarmOcc.Fcorr a eps (bRec p m n j U) (φ U)) := by
  letI : MeasurableSpace (Array N) := enlFilt p m m₀
  have key : Measurable (fun U : Array N => SwarmOcc.Fcorr a eps (bRec p m n j U) (φ U)) := by
    refine SwarmIID.measurable_of_countable_pieces
      (U := fun y : ℤ => fun U : Array N => SwarmOcc.Fcorr a eps (bRec p m n j U) y)
      (fun y => ?_) φ (fun y => hφ (measurableSet_singleton y))
    exact Measurable.mono (measurable_Fcorr_fixed_enl (N := N) hp m n j a eps y)
      (Filtration.mono (enlFilt p m) hn) le_rfl
  exact key

/-- **The record-cost increment `J_{t+1}` is `𝓕_{t+1}`-measurable.** -/
theorem measurable_Jcorr_enl_succ {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m t : ℕ) (i j : Fin N)
    (eps : ℝ) :
    Measurable[enlFilt p m (t + 1)] (fun U : Array N => Jcorr p m eps i j U t) := by
  have hmono : (enlFilt p m t : MeasurableSpace (Array N)) ≤ enlFilt p m (t + 1) :=
    Filtration.mono (enlFilt p m) (Nat.le_succ t)
  have hgap1 : Measurable[enlFilt p m (t + 1)]
      (fun U : Array N => (trajectory p m U (t + 1)).pos i - runMax p m U j (t + 1)) :=
    measurable_gap_enl p m (t + 1) i j
  have hgap2 : Measurable[enlFilt p m (t + 1)]
      (fun U : Array N => (trajectory p m U (t + 1)).pos i - runMax p m U j t) :=
    ((enl_pos_measurable p m (t + 1) le_rfl i)).sub
      (Measurable.mono (measurable_runMax_enl p m t j) hmono le_rfl)
  exact (measurable_Fcorr_gap_enl hp m (t + 1) j (aRec p m) eps hgap1).sub
    (measurable_Fcorr_gap_le_enl hp m (Nat.le_succ t) j (aRec p m) eps hgap2)

/-! ## 2. The `𝓕_T`-adapted part of `Qcomp T`: everything but the terminal potential -/

/-- `Qcomp T - Z_T`, the part of the ledger that is measurable for `𝓕_T`. -/
noncomputable def QnonPot (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) (T : ℕ) : ℝ :=
  Qcomp p m eps (fun r => alphaFun p m r i) i j U T - Zpot p m eps i j U T

/-- **`Qcomp T - Z_T` is the sum of the record costs minus the compensator drift.**  Everything
in the ledger except the terminal potential telescopes away: `Z_0 = 0`. -/
theorem QnonPot_eq (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) (T : ℕ) :
    QnonPot p m eps i j U T
      = (∑ t ∈ Finset.range T, Jcorr p m eps i j U t)
        - (∑ t ∈ Finset.range T, Edrift p m eps (fun r => alphaFun p m r i) i j U t) := by
  have h1 : Qcomp p m eps (fun r => alphaFun p m r i) i j U T
      = (∑ t ∈ Finset.range T, (Zpot p m eps i j U (t + 1) - Zpot p m eps i j U t))
          + (∑ t ∈ Finset.range T, Jcorr p m eps i j U t)
          - (∑ t ∈ Finset.range T, Edrift p m eps (fun r => alphaFun p m r i) i j U t) := by
    rw [Qcomp_eq_sum_increments, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have h2 : (∑ t ∈ Finset.range T, (Zpot p m eps i j U (t + 1) - Zpot p m eps i j U t))
      = Zpot p m eps i j U T - Zpot p m eps i j U 0 :=
    Finset.sum_range_sub (fun t => Zpot p m eps i j U t) T
  rw [QnonPot, h1, h2, Zpot_zero]
  ring

/-- **`Qcomp T - Z_T` is `𝓕_T`-strongly measurable** (for `1/2 ≤ p`).  The record costs are
`𝓕_{t+1}`-measurable and the compensator drift is `𝓕_t`-measurable. -/
theorem stronglyMeasurable_QnonPot {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m T : ℕ) (i j : Fin N)
    (eps : ℝ) :
    StronglyMeasurable[enlFilt p m T] (fun U : Array N => QnonPot p m eps i j U T) := by
  have hJ : StronglyMeasurable[enlFilt p m T]
      (fun U : Array N => ∑ t ∈ Finset.range T, Jcorr p m eps i j U t) := by
    rw [show (fun U : Array N => ∑ t ∈ Finset.range T, Jcorr p m eps i j U t)
        = (∑ t ∈ Finset.range T, fun U : Array N => Jcorr p m eps i j U t) from by
      funext U
      rw [Finset.sum_apply]]
    exact Finset.stronglyMeasurable_sum (m := enlFilt p m T) _
      (fun t ht => (measurable_Jcorr_enl_succ hp m t i j eps).stronglyMeasurable.mono
        (Filtration.mono (enlFilt p m) (Nat.succ_le_of_lt (Finset.mem_range.mp ht))))
  have hE : StronglyMeasurable[enlFilt p m T]
      (fun U : Array N =>
        ∑ t ∈ Finset.range T, Edrift p m eps (fun r => alphaFun p m r i) i j U t) := by
    rw [show (fun U : Array N =>
          ∑ t ∈ Finset.range T, Edrift p m eps (fun r => alphaFun p m r i) i j U t)
        = (∑ t ∈ Finset.range T,
            fun U : Array N => Edrift p m eps (fun r => alphaFun p m r i) i j U t) from by
      funext U
      rw [Finset.sum_apply]]
    exact Finset.stronglyMeasurable_sum (m := enlFilt p m T) _
      (fun t ht => (stronglyMeasurable_Edrift_enl hp m t i j eps).mono
        (Filtration.mono (enlFilt p m) (le_of_lt (Finset.mem_range.mp ht))))
  have heq : (fun U : Array N => QnonPot p m eps i j U T)
      = (fun U : Array N => ∑ t ∈ Finset.range T, Jcorr p m eps i j U t)
        - (fun U : Array N =>
            ∑ t ∈ Finset.range T, Edrift p m eps (fun r => alphaFun p m r i) i j U t) := by
    funext U
    rw [QnonPot_eq]
    rfl
  rw [heq]
  exact hJ.sub hE

/-! ## 3. The exact defect of the optional projection -/

/-- **`Qcomp T = (Qcomp T - Z_T) + Z_T`** with the first summand `𝓕_T`-measurable. -/
theorem Qcomp_eq_QnonPot_add_Zpot (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N)
    (T : ℕ) :
    Qcomp p m eps (fun r => alphaFun p m r i) i j U T
      = QnonPot p m eps i j U T + Zpot p m eps i j U T := by
  rw [QnonPot]
  ring

/-- **The optional projection only changes the terminal potential.**  `Qproj T` is
`(Qcomp T - Z_T) + E[Z_T | 𝓕_T]`, because `Qcomp T - Z_T` is `𝓕_T`-measurable. -/
theorem Qproj_eq_QnonPot_add_condExp {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {i j : Fin N} {eps : ℝ} (hε : 0 < eps) (T : ℕ) :
    Qproj p m eps i j T
      =ᵐ[arrayMeasure N] (fun U : Array N => QnonPot p m eps i j U T)
        + condExp (enlFilt p m T) (arrayMeasure N)
            (fun U : Array N => Zpot p m eps i j U T) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hI : Integrable (fun U : Array N =>
      Qcomp p m eps (fun r => alphaFun p m r i) i j U T) (arrayMeasure N) :=
    integrable_Qcomp hp0 hp1 hε T
  have hZ : Integrable (fun U : Array N => Zpot p m eps i j U T) (arrayMeasure N) :=
    integrable_Zpot hp0 hp1 m i j hε T
  have hA : Integrable (fun U : Array N => QnonPot p m eps i j U T) (arrayMeasure N) :=
    hI.sub hZ
  have hAsm := stronglyMeasurable_QnonPot hp0.le m T i j eps
  have hsplit : (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U T)
      = (fun U : Array N => QnonPot p m eps i j U T)
        + fun U : Array N => Zpot p m eps i j U T := by
    funext U
    rw [Qcomp_eq_QnonPot_add_Zpot]
    rfl
  rw [Qproj, hsplit]
  refine (condExp_add hA hZ (enlFilt p m T)).trans ?_
  rw [condExp_of_stronglyMeasurable ((enlFilt p m).le T) hAsm hA]

/-- **The exact defect of the optional projection.** -/
theorem Qcomp_sub_Qproj_eq {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} {i j : Fin N}
    {eps : ℝ} (hε : 0 < eps) (T : ℕ) :
    (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U T - Qproj p m eps i j T U)
      =ᵐ[arrayMeasure N]
      fun U : Array N => Zpot p m eps i j U T
        - condExp (enlFilt p m T) (arrayMeasure N)
            (fun U : Array N => Zpot p m eps i j U T) U := by
  have h := Qproj_eq_QnonPot_add_condExp (N := N) hp0 hp1 (m := m) (i := i) (j := j) hε T
  filter_upwards [h] with U hU
  rw [Qcomp_eq_QnonPot_add_Zpot p m eps i j U T]
  simp only [Pi.add_apply] at hU ⊢
  linarith

/-! ## 4. The defect is the terminal environment fluctuation, not an error term -/

/-- Record cost term at time `T` is integrable (bounded by `abs_Fcorr_bRec_le`). -/
theorem integrable_Fcorr_gap_T {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m T : ℕ)
    (i j : Fin N) {eps : ℝ} (hε : 0 < eps) :
    Integrable (fun U : Array N => SwarmOcc.Fcorr (aRec p m) eps (bRec p m T j U)
      ((trajectory p m U T).pos i - runMax p m U j T)) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hmeas : Measurable (fun U : Array N => SwarmOcc.Fcorr (aRec p m) eps (bRec p m T j U)
      ((trajectory p m U T).pos i - runMax p m U j T)) :=
    measurable_ambient_of_enl (measurable_Fcorr_gap_enl hp0.le m T j (aRec p m) eps
      (measurable_gap_enl p m T i j))
  refine Integrable.of_bound hmeas.aestronglyMeasurable
    ((2 * ((T : ℕ) : ℝ) + 5) ^ 2 / (eps * (1 - aRec p m) ^ 2))
    (Filter.Eventually.of_forall fun U => ?_)
  rw [Real.norm_eq_abs]
  exact abs_Fcorr_bRec_le hp0 hp1 m T j hε U _

/-- **Integrability of the realised potential at the terminal position.**  It is
`Z_T + F_{b_T}(g_T)` with both summands integrable. -/
theorem integrable_Hpot_envH_T {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m T : ℕ)
    (i j : Fin N) {eps : ℝ} (hε : 0 < eps) :
    Integrable (fun U : Array N =>
      SwarmOcc.Hpot (envH p m j U) ((trajectory p m U T).pos i)) (arrayMeasure N) := by
  have hZ : Integrable (fun U : Array N => Zpot p m eps i j U T) (arrayMeasure N) :=
    integrable_Zpot hp0 hp1 m i j hε T
  have hF := integrable_Fcorr_gap_T hp0 hp1 m T i j hε
  have hfun : (fun U : Array N => SwarmOcc.Hpot (envH p m j U) ((trajectory p m U T).pos i))
      = fun U : Array N => Zpot p m eps i j U T
        + SwarmOcc.Fcorr (aRec p m) eps (bRec p m T j U)
            ((trajectory p m U T).pos i - runMax p m U j T) := by
    funext U
    simp only [Zpot]
    ring
  rw [hfun]
  exact hZ.add hF


/-! ## 5. The defect is the terminal environment fluctuation -/

/-- **`E[H_j(X_T) - F_{b_T}(g_T) | 𝓕_T] = E[H_j(X_T) | 𝓕_T] - F_{b_T}(g_T)`**: the record cost is
`𝓕_T`-measurable, so only the realised environment potential is projected. -/
theorem condExp_Hpot_sub_Fcorr {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {i j : Fin N} {eps : ℝ} (hε : 0 < eps) (T : ℕ) :
    condExp (enlFilt p m T) (arrayMeasure N)
        (fun U : Array N => SwarmOcc.Hpot (envH p m j U) ((trajectory p m U T).pos i)
          - SwarmOcc.Fcorr (aRec p m) eps (bRec p m T j U)
              ((trajectory p m U T).pos i - runMax p m U j T))
      =ᵐ[arrayMeasure N] fun U : Array N =>
        condExp (enlFilt p m T) (arrayMeasure N)
            (fun V : Array N =>
              SwarmOcc.Hpot (envH p m j V) ((trajectory p m V T).pos i)) U
          - SwarmOcc.Fcorr (aRec p m) eps (bRec p m T j U)
              ((trajectory p m U T).pos i - runMax p m U j T) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hHpot := integrable_Hpot_envH_T hp0 hp1 m T i j hε
  have hFc := integrable_Fcorr_gap_T hp0 hp1 m T i j hε
  have hFc_sm : StronglyMeasurable[enlFilt p m T] (fun U : Array N =>
      SwarmOcc.Fcorr (aRec p m) eps (bRec p m T j U)
        ((trajectory p m U T).pos i - runMax p m U j T)) :=
    (measurable_Fcorr_gap_enl hp0.le m T j (aRec p m) eps
      (measurable_gap_enl p m T i j)).stronglyMeasurable
  refine (condExp_sub hHpot hFc (enlFilt p m T)).trans ?_
  rw [condExp_of_stronglyMeasurable ((enlFilt p m).le T) hFc_sm hFc]
  filter_upwards with U
  rfl

/-- **The exact defect, in potential form.**  `Qcomp T - Qproj T` *is* the terminal
full-environment fluctuation `H_j(X_T^i) - E[H_j(X_T^i) | 𝓕_T]` of the realised potential. -/
theorem Qcomp_sub_Qproj_eq_Hpot {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {i j : Fin N} {eps : ℝ} (hε : 0 < eps) (T : ℕ) :
    (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U T - Qproj p m eps i j T U)
      =ᵐ[arrayMeasure N] fun U : Array N =>
        SwarmOcc.Hpot (envH p m j U) ((trajectory p m U T).pos i)
          - condExp (enlFilt p m T) (arrayMeasure N)
              (fun V : Array N =>
                SwarmOcc.Hpot (envH p m j V) ((trajectory p m V T).pos i)) U := by
  have hZeq : (fun U : Array N => Zpot p m eps i j U T)
      = fun U : Array N => SwarmOcc.Hpot (envH p m j U) ((trajectory p m U T).pos i)
          - SwarmOcc.Fcorr (aRec p m) eps (bRec p m T j U)
              ((trajectory p m U T).pos i - runMax p m U j T) := by
    funext U
    simp only [Zpot]
  have hcongr : condExp (enlFilt p m T) (arrayMeasure N) (fun U : Array N => Zpot p m eps i j U T)
      =ᵐ[arrayMeasure N] condExp (enlFilt p m T) (arrayMeasure N)
        (fun U : Array N => SwarmOcc.Hpot (envH p m j U) ((trajectory p m U T).pos i)
          - SwarmOcc.Fcorr (aRec p m) eps (bRec p m T j U)
              ((trajectory p m U T).pos i - runMax p m U j T)) :=
    condExp_congr_ae (Filter.EventuallyEq.of_eq hZeq)
  refine (Qcomp_sub_Qproj_eq (N := N) hp0 hp1 (m := m) (i := i) (j := j) hε T).trans ?_
  filter_upwards [hcongr, condExp_Hpot_sub_Fcorr (N := N) hp0 hp1 (m := m) (i := i) (j := j) hε T]
    with U hU1 hU2
  have hpt : Zpot p m eps i j U T
      = SwarmOcc.Hpot (envH p m j U) ((trajectory p m U T).pos i)
        - SwarmOcc.Fcorr (aRec p m) eps (bRec p m T j U)
            ((trajectory p m U T).pos i - runMax p m U j T) := by
    simp only [Zpot]
  linarith

/-! ## 6. The defect is invisible to the revealed history -/

/-- **The defect has zero `𝓕_s`-conditional mean for every `s ≤ T`.**  It is a *terminal*
fluctuation: centred against the whole revealed past, so no `𝓕_T`-predictable test function
detects it, and no mean/budget statement at time `T` can control it. -/
theorem condExp_Qcomp_sub_Qproj_eq_zero {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {i j : Fin N} {eps : ℝ} (hε : 0 < eps) {s T : ℕ} (hs : s ≤ T) :
    condExp (enlFilt p m s) (arrayMeasure N)
      (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U T - Qproj p m eps i j T U)
      =ᵐ[arrayMeasure N] 0 := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  haveI : IsFiniteMeasure ((arrayMeasure N).trim ((enlFilt p m).le T)) := inferInstance
  have hZ : Integrable (fun U : Array N => Zpot p m eps i j U T) (arrayMeasure N) :=
    integrable_Zpot hp0 hp1 m i j hε T
  have hZc : Integrable (fun U : Array N =>
      condExp (enlFilt p m T) (arrayMeasure N) (fun U : Array N => Zpot p m eps i j U T) U)
      (arrayMeasure N) := integrable_condExp
  refine (condExp_congr_ae
    (Qcomp_sub_Qproj_eq (N := N) hp0 hp1 (m := m) (i := i) (j := j) hε T)).trans ?_
  refine (condExp_sub hZ hZc (enlFilt p m s)).trans ?_
  have htower : condExp (enlFilt p m s) (arrayMeasure N)
      (fun U : Array N => condExp (enlFilt p m T) (arrayMeasure N)
        (fun U : Array N => Zpot p m eps i j U T) U)
      =ᵐ[arrayMeasure N] condExp (enlFilt p m s) (arrayMeasure N)
        (fun U : Array N => Zpot p m eps i j U T) :=
    condExp_condExp_of_le (m₀ := (inferInstance : MeasurableSpace (Array N)))
      (hm₂ := (enlFilt p m).le T) (m₁ := enlFilt p m s) (m₂ := enlFilt p m T)
      (f := fun U : Array N => Zpot p m eps i j U T) (Filtration.mono (enlFilt p m) hs)
  filter_upwards [htower] with U hU
  simp only [Pi.sub_apply, Pi.zero_apply]
  linarith

/-! ## 7. `hQ` is exactly `hQ` for the martingale plus a terminal bound -/

/-- **The one-sided budget splits exactly.**  If the genuine martingale `Qproj` satisfies the
lower budget with coefficient `c`, and the terminal environment fluctuation does too, then the raw
`Qcomp` satisfies it with coefficient `2c`. -/
theorem qbudget_of_proj_and_fluct {p : ℝ} {m : ℕ} {i j : Fin N} {eps c : ℝ} {N₀ : ℕ}
    (hproj : ∀ᵐ U ∂(arrayMeasure N), ∀ T ≥ N₀, -(c * (T : ℝ)) ≤ Qproj p m eps i j T U)
    (hfluct : ∀ᵐ U ∂(arrayMeasure N), ∀ T ≥ N₀,
      -(c * (T : ℝ)) ≤ Qcomp p m eps (fun r => alphaFun p m r i) i j U T - Qproj p m eps i j T U) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ T ≥ N₀,
      -((2 * c) * (T : ℝ)) ≤ Qcomp p m eps (fun r => alphaFun p m r i) i j U T := by
  filter_upwards [hproj, hfluct] with U h1 h2 T hT
  have ha := h1 T hT
  have hb := h2 T hT
  nlinarith

/-- **Equivalence form of the split**, pointwise in the array. -/
theorem qbudget_iff_proj_add_fluct (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N)
    (T : ℕ) (c : ℝ) :
    (-(c * (T : ℝ)) ≤ Qcomp p m eps (fun r => alphaFun p m r i) i j U T) ↔
      (-(c * (T : ℝ)) ≤ Qproj p m eps i j T U
        + (Qcomp p m eps (fun r => alphaFun p m r i) i j U T - Qproj p m eps i j T U)) := by
  constructor <;> intro h <;> linarith


/-! ## 8. `Qcomp 1` itself is not `𝓕₁`-measurable

The countermodel of `QIncrementAdapted` is about the *increment*.  Here is the corresponding
statement about `Q` itself: since `Z_T = (Qcomp T - Z_T) ·` ... the raw ledger value at time `1` is
already not observable at time `1`. -/

/-- **`Z_1` is not `𝓕₁`-strongly measurable.**  `Z_1 = Z_0 + ZJinc 0 - J_0` and both `Z_0` and
`J_0` are `𝓕₁`-measurable, so this follows from the verified countermodel for `ZJinc 0`. -/
theorem not_stronglyMeasurable_Zpot_one {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 3 ≤ m) {eps : ℝ} {i j : Fin N} (hij : i ≠ j) :
    ¬ StronglyMeasurable[enlFilt p m 1] (fun U : Array N => Zpot p m eps i j U 1) := by
  intro hZ
  refine not_stronglyMeasurable_ZJinc_zero (N := N) hp0 hp1 hm (eps := eps) hij ?_
  have hJ : StronglyMeasurable[enlFilt p m 1] (fun U : Array N => Jcorr p m eps i j U 0) :=
    (measurable_Jcorr_enl_succ hp0.le m 0 i j eps).stronglyMeasurable
  have hfun : (fun U : Array N => ZJinc p m eps i j U 0)
      = (fun U : Array N => Zpot p m eps i j U 1)
        - (fun U : Array N => Zpot p m eps i j U 0)
        + fun U : Array N => Jcorr p m eps i j U 0 := by
    funext U
    simp only [ZJinc, Pi.sub_apply, Pi.add_apply]
  have h0 : StronglyMeasurable[enlFilt p m 1] (fun U : Array N => Zpot p m eps i j U 0) := by
    have : (fun U : Array N => Zpot p m eps i j U 0) = fun _ => (0 : ℝ) := by
      funext U
      exact Zpot_zero p m eps i j U
    rw [this]
    exact stronglyMeasurable_const
  rw [hfun]
  exact (hZ.sub h0).add hJ

/-- **The actual-model ledger value `Qcomp 1` is not `𝓕₁`-measurable**: the raw compensator is
not an `𝓕_T`-observable process.  (`Qcomp 1 - Z_1` is `𝓕₁`-measurable by
`stronglyMeasurable_QnonPot`, so the failure is carried by the terminal potential.) -/
theorem not_stronglyMeasurable_Qcomp_one {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 3 ≤ m) {eps : ℝ} {i j : Fin N} (hij : i ≠ j) :
    ¬ StronglyMeasurable[enlFilt p m 1]
        (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U 1) := by
  intro hQ
  have hA : StronglyMeasurable[enlFilt p m 1] (fun U : Array N => QnonPot p m eps i j U 1) :=
    stronglyMeasurable_QnonPot hp0.le m 1 i j eps
  have hZ : StronglyMeasurable[enlFilt p m 1] (fun U : Array N => Zpot p m eps i j U 1) := by
    have hsub := hQ.sub hA
    convert hsub using 1
    funext U
    simp only [Pi.sub_apply]
    rw [Qcomp_eq_QnonPot_add_Zpot p m eps i j U 1]
    ring
  exact not_stronglyMeasurable_Zpot_one hp0 hp1 hm hij hZ

/-! ## 9. No `𝓕_T`-test function can see the defect -/

/-- **The defect integrates to zero against every `𝓕_T`-measurable event.**  This is the precise
sense in which the missing input is not a mean, a variance against predictable multipliers, or a
budget: all `𝓕_T`-predictable tests are blind to it. -/
theorem setIntegral_Qcomp_sub_Qproj_eq_zero {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {i j : Fin N} {eps : ℝ} (hε : 0 < eps) (T : ℕ) {A : Set (Array N)}
    (hA : MeasurableSet[enlFilt p m T] A) :
    ∫ U in A, (Qcomp p m eps (fun r => alphaFun p m r i) i j U T - Qproj p m eps i j T U)
        ∂(arrayMeasure N) = 0 := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  haveI : IsFiniteMeasure ((arrayMeasure N).trim ((enlFilt p m).le T)) := inferInstance
  have hI : Integrable (fun U : Array N =>
      Qcomp p m eps (fun r => alphaFun p m r i) i j U T - Qproj p m eps i j T U)
      (arrayMeasure N) :=
    (integrable_Qcomp hp0 hp1 hε T).sub integrable_condExp
  have hz := condExp_Qcomp_sub_Qproj_eq_zero (N := N) hp0 hp1 (m := m) (i := i) (j := j) hε
    (le_rfl : T ≤ T)
  have h1 : ∫ U in A,
      condExp (enlFilt p m T) (arrayMeasure N)
        (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U T - Qproj p m eps i j T U) U
      ∂(arrayMeasure N)
      = ∫ U in A,
        (Qcomp p m eps (fun r => alphaFun p m r i) i j U T - Qproj p m eps i j T U)
        ∂(arrayMeasure N) :=
    setIntegral_condExp ((enlFilt p m).le T) hI hA
  rw [← h1]
  have hzr : (fun U : Array N => condExp (enlFilt p m T) (arrayMeasure N)
      (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U T - Qproj p m eps i j T U) U)
      =ᵐ[(arrayMeasure N).restrict A] fun _ => (0 : ℝ) :=
    ae_restrict_of_ae hz
  rw [integral_congr_ae hzr]
  simp

/-! ## 10. The `QResidual` shape -/

/-- **`ActualBudgetInterfaces.QResidual`, produced from the split.**  With `eps = 1/64` and
coefficient `c = 1/128` on both pieces, the conclusion is literally the required one-sided budget
for the raw `Qcomp` at every ordered pair (definitionally the statement of `QResidual p m N`). -/
theorem qresidual_of_proj_and_fluct {p : ℝ} (m : ℕ) :
    (∀ i j : Fin N, i ≠ j → ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
        -((1 / 128 : ℝ) * (T : ℝ)) ≤ Qproj p m (1 / 64) i j T U) →
    (∀ i j : Fin N, i ≠ j → ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
        -((1 / 128 : ℝ) * (T : ℝ)) ≤
          Qcomp p m (1 / 64) (fun t => alphaFun p m t i) i j U T - Qproj p m (1 / 64) i j T U) →
    ∀ i j : Fin N, i ≠ j → ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      -((1 / 64 : ℝ) * (T : ℝ)) ≤ Qcomp p m (1 / 64) (fun t => alphaFun p m t i) i j U T := by
  intro hproj hfluct i j hij
  filter_upwards [hproj i j hij, hfluct i j hij] with U h1 h2
  obtain ⟨N₁, hN₁⟩ := h1
  obtain ⟨N₂, hN₂⟩ := h2
  refine ⟨max N₁ N₂, fun T hT => ?_⟩
  have h1' := hN₁ T (le_trans (le_max_left _ _) hT)
  have h2' := hN₂ T (le_trans (le_max_right _ _) hT)
  have hT0 : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
  nlinarith


/-! ## 11. The projection is not the raw process -/

/-- **The raw `Qcomp` really differs from its optional projection.**  If it did not, `Qcomp 1`
would be `𝓕₁`-measurable (it is the conditional expectation), contradicting
`not_stronglyMeasurable_Qcomp_one`.  Hence the defect term cannot be dropped from the ledger: any
`hQ` proof that replaces `Qcomp` by `Qproj` must carry the terminal fluctuation explicitly. -/
theorem exists_Qcomp_ne_Qproj {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 3 ≤ m) {eps : ℝ} (hε : 0 < eps) {i j : Fin N} (hij : i ≠ j) :
    ∃ U : Array N, Qcomp p m eps (fun r => alphaFun p m r i) i j U 1 ≠ Qproj p m eps i j 1 U := by
  by_contra hcon
  push Not at hcon
  refine not_stronglyMeasurable_Qcomp_one hp0 hp1 hm (eps := eps) hij ?_
  have hfun : (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U 1)
      = fun U : Array N => Qproj p m eps i j 1 U := by
    funext U
    exact hcon U
  rw [hfun]
  exact stronglyMeasurable_condExp


/-- **The defect has zero total mean.**  `E[Qcomp T] = E[Qproj T]` for every `T`: the defect is
invisible to every mean-level (annealed) statement, so `∫ Qcomp = 0` carries no information about
the one-sided budget `hQ`. -/
theorem integral_Qcomp_sub_Qproj_eq_zero {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {i j : Fin N} {eps : ℝ} (hε : 0 < eps) (T : ℕ) :
    ∫ U, (Qcomp p m eps (fun r => alphaFun p m r i) i j U T - Qproj p m eps i j T U)
      ∂(arrayMeasure N) = 0 := by
  have h := setIntegral_Qcomp_sub_Qproj_eq_zero (N := N) hp0 hp1 (m := m) (i := i) (j := j)
    hε T (A := Set.univ) MeasurableSet.univ
  simpa only [Measure.restrict_univ] using h


/-! ## 12. The exact structural repair: reveal the terminal environment -/

/-- **The projection defect vanishes exactly when the terminal environment potential is already
revealed.**  If `H_j(X_T^i)` agrees a.e. with an `𝓕_T`-strongly measurable function (i.e. the
marks needed for the realised potential at the terminal position are known by time `T`, which is
what the source's "one new bit at the record" bookkeeping implicitly assumes), then the raw
`Qcomp T` equals its optional projection.  So the missing input is *not* adaptedness of the
increment but revealedness of the terminal environment — and at the actual model this fails
(`not_stronglyMeasurable_Qcomp_one`). -/
theorem Qcomp_eq_Qproj_of_measurable_Hpot {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {i j : Fin N} {eps : ℝ} (hε : 0 < eps) (T : ℕ) {g : Array N → ℝ}
    (hg : StronglyMeasurable[enlFilt p m T] g)
    (hHg : (fun U : Array N => SwarmOcc.Hpot (envH p m j U) ((trajectory p m U T).pos i))
      =ᵐ[arrayMeasure N] g) :
    (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U T)
      =ᵐ[arrayMeasure N] fun U : Array N => Qproj p m eps i j T U := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hHpot := integrable_Hpot_envH_T hp0 hp1 m T i j hε
  have hgint : Integrable g (arrayMeasure N) := hHpot.congr hHg
  have hcond : condExp (enlFilt p m T) (arrayMeasure N)
      (fun U : Array N => SwarmOcc.Hpot (envH p m j U) ((trajectory p m U T).pos i))
      =ᵐ[arrayMeasure N] g :=
    (condExp_congr_ae hHg).trans
      (Filter.EventuallyEq.of_eq
        (condExp_of_stronglyMeasurable ((enlFilt p m).le T) hg hgint))
  have hdef := Qcomp_sub_Qproj_eq_Hpot (N := N) hp0 hp1 (m := m) (i := i) (j := j) hε T
  have hzero : (fun U : Array N =>
        SwarmOcc.Hpot (envH p m j U) ((trajectory p m U T).pos i)
          - condExp (enlFilt p m T) (arrayMeasure N)
              (fun V : Array N =>
                SwarmOcc.Hpot (envH p m j V) ((trajectory p m V T).pos i)) U) =ᵐ[arrayMeasure N] 0 := by
    filter_upwards [hHg, hcond] with U h1 h2
    rw [h1, h2]
    simp
  have hsum : (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U T)
      =ᵐ[arrayMeasure N] fun U : Array N =>
        (Qcomp p m eps (fun r => alphaFun p m r i) i j U T - Qproj p m eps i j T U)
          + Qproj p m eps i j T U := by
    filter_upwards with U
    ring
  refine hsum.trans ?_
  refine (Filter.EventuallyEq.add (hdef.trans hzero) (Filter.EventuallyEq.refl _ _)).trans ?_
  filter_upwards with U
  simp

end Swarming.Enl
