/-
  **Direction D2 (m4) — `ProjLedger.lean`: the paper's *projected* potential `H_{j,n}` and the
  adaptivity of the projected ledger.**

  The paper (`main_1d_revised.tex`, proof of Proposition `ball`) does **not** use the
  quenched potential `H_j(x)` of the revealed environment.  It uses its projection

      H_{j,n}(x) = E[H_j(x) | F_n],          (paper, before `(projh)`)

  where `F_n` is the enlarged filtration (positions *and* revealed coordinates), and it records
  the two structural facts

      H_{j,n}(x+1) - H_{j,n}(x) = E[h_j(x) | F_n]      (for `0 <= x`),
      Z_n = H_{j,n}(X_n^i) - F_{b_n}(X_n^i - M_n^j)

  and then forms the martingale `Q` out of the entries of `Z_{t+1} - Z_t + J_{t+1}`.

  This file builds that object at the actual model.  The content is:

  * `projH p m j n U y` = `condExp (enlFilt p m n) (arrayMeasure N) (fun V => H_j(V)(y)) U`,
    i.e. exactly `H_{j,n}(y)`; `projH_def` is `rfl`.
  * `stronglyMeasurable_projH`, `measurable_Hpot_site`, `integrable_Hpot_site`.
  * `projH_succ_sub` : the paper's derivative identity
    `H_{j,n}(y+1) - H_{j,n}(y) = E[h_j(y) | F_n] = condExp (enlFilt p m n) (hZpot (siteH ..) y)`.
  * `measurable_projH_pos`, `stronglyMeasurable_projH_pos` : the projection evaluated at the
    walker's own position `X_n^i` is `enlFilt p m n`-measurable.
  * `Zproj` : the paper's `Z_n` built from `projH` instead of the quenched `H_j`.
  * `stronglyMeasurable_Zproj`, `stronglyMeasurable_JcorrProj`,
    `stronglyMeasurable_ZJincProj` : **every entry of the projected `(Vdrift)` ledger is adapted
    with no measurability hypothesis**.  This is exactly the point where the quenched ledger
    fails: `CompensatorMeanZero.lean` states `martingale_Qcomp` only under `hadapt`, and
    `QIncrementAdapted.lean` refutes `hadapt` for the quenched `ZJinc` (`m >= 3`).  The projected
    ledger does not have this defect — that is the source-faithful fix.

  Nothing probabilistic is assumed here: no orthogonality of raw `qInc`, no adaptedness of a
  quenched environment, no `hadapt`.
-/
import Swarm.CorrectionDrift
import Swarm.AboveActualDrift
import Swarm.ZBudgetActual
import Swarm.MartingaleLimit

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross

variable {N : ℕ}

/-! ## 1. The paper's projected potential `H_{j,n}` -/

/-- **The paper's `H_{j,n}(y) = E[H_j(y) | F_n]`** at the actual model: the conditional
expectation, against the enlarged filtration `enlFilt p m n`, of the quenched potential
`H_{j}(y) = Hpot (siteH p m j ·) y`. -/
noncomputable def projH (p : ℝ) (m : ℕ) (j : Fin N) (n : ℕ) (U : Array N) (y : ℤ) : ℝ :=
  condExp (enlFilt p m n) (arrayMeasure N) (fun V => SwarmOcc.Hpot (siteH p m j V) y) U

/-- `projH` is *by definition* the conditional expectation defining the paper's `H_{j,n}`. -/
theorem projH_def (p : ℝ) (m : ℕ) (j : Fin N) (n : ℕ) (U : Array N) (y : ℤ) :
    projH p m j n U y
      = condExp (enlFilt p m n) (arrayMeasure N) (fun V => SwarmOcc.Hpot (siteH p m j V) y) U :=
  rfl

/-- `H_{j,n}(y)` is `enlFilt p m n`-strongly measurable (for every fixed site `y`). -/
theorem stronglyMeasurable_projH (p : ℝ) (m : ℕ) (j : Fin N) (n : ℕ) (y : ℤ) :
    StronglyMeasurable[enlFilt (N := N) p m n] (fun U => projH p m j n U y) :=
  MeasureTheory.stronglyMeasurable_condExp

/-- `H_{j,n}(y)` is `enlFilt p m n`-measurable (for every fixed site `y`). -/
theorem measurable_projH_fixed (p : ℝ) (m : ℕ) (j : Fin N) (n : ℕ) (y : ℤ) :
    Measurable[enlFilt (N := N) p m n] (fun U => projH p m j n U y) :=
  (stronglyMeasurable_projH p m j n y).measurable

/-- The quenched potential at a fixed site is ambient measurable. -/
theorem measurable_Hpot_site (p : ℝ) (m : ℕ) (j : Fin N) (y : ℤ) :
    Measurable (fun U : Array N => SwarmOcc.Hpot (siteH p m j U) y) := by
  classical
  by_cases hy : y ≤ 0
  · have hconst : (fun U : Array N => SwarmOcc.Hpot (siteH p m j U) y) = fun _ => (y : ℝ) := by
      funext U
      exact SwarmOcc.Hpot_of_nonpos hy
    rw [hconst]
    exact measurable_const
  · have hsum : (fun U : Array N => SwarmOcc.Hpot (siteH p m j U) y)
        = fun U => ∑ u ∈ Finset.range y.toNat,
            SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u := by
      funext U
      rw [SwarmOcc.Hpot, if_neg hy]
      rfl
    rw [hsum]
    exact Finset.measurable_sum _ fun u _ => measurable_hof_siteMarks_ambient p m j u

/-- The quenched potential at a fixed site is integrable: it is a bounded function of the array. -/
theorem integrable_Hpot_site {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hpne : p ≠ 0)
    (m : ℕ) (j : Fin N) (y : ℤ) :
    Integrable (fun U : Array N => SwarmOcc.Hpot (siteH p m j U) y) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  refine Integrable.of_bound (measurable_Hpot_site p m j y).aestronglyMeasurable
    (|(y : ℝ)| + (y.toNat : ℝ) * (2 * (y.toNat : ℝ) + 3)) ?_
  filter_upwards with U
  rw [Real.norm_eq_abs]
  have hmain : |SwarmOcc.Hpot (siteH p m j U) y|
      ≤ |(y : ℝ)| + (y.toNat : ℝ) * (2 * (y.toNat : ℝ) + 3) := by
    by_cases hy : y ≤ 0
    · rw [SwarmOcc.Hpot_of_nonpos hy, Int.toNat_of_nonpos hy, Nat.cast_zero, zero_mul, add_zero]
      
    · have hy0 : 0 ≤ y := by omega
      have hrew : SwarmOcc.Hpot (siteH p m j U) y
          = ∑ u ∈ Finset.range y.toNat,
              SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u := by
        rw [SwarmOcc.Hpot, if_neg hy]
        rfl
      rw [hrew]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have h1 : ∑ u ∈ Finset.range y.toNat,
            |SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u|
          ≤ ∑ u ∈ Finset.range y.toNat, (2 * (u : ℝ) + 3) :=
        Finset.sum_le_sum fun u _ => SwarmShiftMarks.abs_hof_le' hp0 hp1 hpne _ u
      have h2 : ∑ u ∈ Finset.range y.toNat, (2 * (u : ℝ) + 3)
          ≤ (y.toNat : ℝ) * (2 * (y.toNat : ℝ) + 3) := by
        have hterm : ∀ u ∈ Finset.range y.toNat,
            (2 * (u : ℝ) + 3) ≤ 2 * (y.toNat : ℝ) + 3 := by
          intro u hu
          have hu' : u < y.toNat := Finset.mem_range.mp hu
          have : (u : ℝ) ≤ (y.toNat : ℝ) := by exact_mod_cast Nat.le_of_lt hu'
          linarith
        calc ∑ u ∈ Finset.range y.toNat, (2 * (u : ℝ) + 3)
            ≤ ∑ _u ∈ Finset.range y.toNat, (2 * (y.toNat : ℝ) + 3) :=
              Finset.sum_le_sum hterm
          _ = (y.toNat : ℝ) * (2 * (y.toNat : ℝ) + 3) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      linarith [le_trans h1 h2, abs_nonneg (y : ℝ)]
  exact hmain

/-- **The paper's derivative identity for the projected potential**:
`H_{j,n}(y+1) - H_{j,n}(y) = E[h_j(y) | F_n]`, i.e. the `F_n`-conditional expectation of the
integer-indexed potential step `hZpot h_j y`.

This is the identity that makes the paper's `(Zloss)` a statement about `projH`; it is *not* an
identity about the quenched `Hpot (siteH ..)` at a random site. -/
theorem projH_succ_sub {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hpne : p ≠ 0)
    (m : ℕ) (j : Fin N) (n : ℕ) (y : ℤ) :
    (fun U => projH p m j n U (y + 1) - projH p m j n U y)
      =ᵐ[arrayMeasure N]
      condExp (enlFilt p m n) (arrayMeasure N) (fun V => hZpot (siteH p m j V) y) := by
  have h1 := integrable_Hpot_site hp0 hp1 hpne m j (y + 1)
  have h0 := integrable_Hpot_site hp0 hp1 hpne m j y
  have hsub := MeasureTheory.condExp_sub h1 h0 (enlFilt p m n)
  have hptV : ∀ V : Array N,
      SwarmOcc.Hpot (siteH p m j V) (y + 1) - SwarmOcc.Hpot (siteH p m j V) y
        = hZpot (siteH p m j V) y := by
    intro V
    rw [SwarmOcc.Hpot_succ_sub]
    by_cases hy : 0 ≤ y
    · rw [if_pos hy, hZpot_of_nonneg hy]
    · rw [if_neg hy]
      exact (hZpot_of_nonpos (by omega)).symm
  have hpt : ((fun V : Array N => SwarmOcc.Hpot (siteH p m j V) (y + 1))
        - fun V => SwarmOcc.Hpot (siteH p m j V) y)
      = fun V => hZpot (siteH p m j V) y := by
    funext V
    exact hptV V
  rw [hpt] at hsub
  filter_upwards [hsub] with U hU
  simpa only [projH, Pi.sub_apply] using hU.symm

/-! ## 2. The projection at the walker's own position -/

/-- **`H_{j,n}(X_n^i)` is `enlFilt p m n`-measurable.**  Countable pieces over the (finitely many)
positions reachable at time `n`. -/
theorem measurable_projH_pos (p : ℝ) (m : ℕ) (j : Fin N) (n : ℕ) (i : Fin N) :
    Measurable[enlFilt (N := N) p m n]
      (fun U => projH p m j n U ((trajectory p m U n).pos i)) := by
  letI : MeasurableSpace (Array N) := enlFilt p m n
  exact SwarmIID.measurable_of_countable_pieces
    (U := fun y : ℤ => fun U : Array N => projH p m j n U y)
    (fun y => measurable_projH_fixed p m j n y)
    (fun U => (trajectory p m U n).pos i)
    (fun y => enl_pos_measurable p m n le_rfl i (measurableSet_singleton y))

/-- `H_{j,n}(X_n^i)` is `enlFilt p m n`-strongly measurable. -/
theorem stronglyMeasurable_projH_pos (p : ℝ) (m : ℕ) (j : Fin N) (n : ℕ) (i : Fin N) :
    StronglyMeasurable[enlFilt (N := N) p m n]
      (fun U => projH p m j n U ((trajectory p m U n).pos i)) :=
  (measurable_projH_pos p m j n i).stronglyMeasurable

/-! ## 3. The projected ledger -/

/-- **The paper's `Z_n`, with the projected potential**:
`Z_n = H_{j,n}(X_n^i) - F_{b_n}(X_n^i - M_n^j)`. -/
noncomputable def Zproj (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) (t : ℕ) : ℝ :=
  projH p m j t U ((trajectory p m U t).pos i)
    - SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
        ((trajectory p m U t).pos i - runMax p m U j t)

/-- `Z_t` of the projected ledger is `enlFilt p m t`-strongly measurable. -/
theorem stronglyMeasurable_Zproj {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m : ℕ) (t : ℕ) (i j : Fin N)
    (eps : ℝ) :
    StronglyMeasurable[enlFilt (N := N) p m t] (fun U => Zproj p m eps i j U t) := by
  have hH : StronglyMeasurable[enlFilt p m t]
      (fun U : Array N => projH p m j t U ((trajectory p m U t).pos i)) :=
    stronglyMeasurable_projH_pos p m j t i
  have hF : StronglyMeasurable[enlFilt p m t]
      (fun U : Array N => SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
        ((trajectory p m U t).pos i - runMax p m U j t)) :=
    (VdriftAssembly.measurable_Fcorr_gap_enl hp m t j (aRec p m) eps (VdriftAssembly.measurable_gap_enl p m t i j)).stronglyMeasurable
  exact hH.sub hF

/-- `F_{b_n}(X_{n+1}^i - M_n^j)` is `enlFilt p m (n+1)`-measurable, although the record cost
`b_n` and the record `M_n^j` are only `enlFilt p m n`-measurable. -/
theorem measurable_Fcorr_gap_mono {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) {m n n' : ℕ} (hn : n ≤ n')
    (j : Fin N) (a eps : ℝ) {φ : Array N → ℤ}
    (hφ : Measurable[enlFilt (N := N) p m n'] φ) :
    Measurable[enlFilt (N := N) p m n']
      (fun U : Array N => SwarmOcc.Fcorr a eps (bRec p m n j U) (φ U)) := by
  letI : MeasurableSpace (Array N) := enlFilt p m n'
  have hmono : (enlFilt (N := N) p m n : MeasurableSpace (Array N)) ≤ enlFilt p m n' :=
    Filtration.mono (enlFilt (N := N) p m) hn
  have key : Measurable (fun U : Array N => SwarmOcc.Fcorr a eps (bRec p m n j U) (φ U)) := by
    refine SwarmIID.measurable_of_countable_pieces
      (U := fun y : ℤ => fun U : Array N => SwarmOcc.Fcorr a eps (bRec p m n j U) y)
      (fun y => Measurable.mono (VdriftAssembly.measurable_Fcorr_fixed_enl hp m n j a eps y) hmono le_rfl) φ ?_
    intro y
    exact hφ (measurableSet_singleton y)
  exact key

/-- **The paper's `J_{n+1}` for the projected ledger**:
`F_{b_{n+1}}(X_{n+1}^i - M_{n+1}^j) - F_{b_n}(X_{n+1}^i - M_n^j)`. -/
noncomputable def JcorrProj (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) (t : ℕ) : ℝ :=
  SwarmOcc.Fcorr (aRec p m) eps (bRec p m (t + 1) j U)
      ((trajectory p m U (t + 1)).pos i - runMax p m U j (t + 1))
    - SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
      ((trajectory p m U (t + 1)).pos i - runMax p m U j t)

/-- `J_{t+1}` of the projected ledger is `enlFilt p m (t+1)`-strongly measurable. -/
theorem stronglyMeasurable_JcorrProj {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m : ℕ) (t : ℕ)
    (i j : Fin N) (eps : ℝ) :
    StronglyMeasurable[enlFilt (N := N) p m (t + 1)] (fun U => JcorrProj p m eps i j U t) := by
  have hmono : (enlFilt (N := N) p m t : MeasurableSpace (Array N)) ≤ enlFilt p m (t + 1) :=
    Filtration.mono (enlFilt (N := N) p m) (Nat.le_succ t)
  have hpos : Measurable[enlFilt (N := N) p m (t + 1)]
      (fun U : Array N => (trajectory p m U (t + 1)).pos i) :=
    enl_pos_measurable p m (t + 1) le_rfl i
  have hrun : Measurable[enlFilt (N := N) p m (t + 1)] (fun U : Array N => runMax p m U j t) :=
    Measurable.mono (VdriftAssembly.measurable_runMax_enl p m t j) hmono le_rfl
  have hrun' : Measurable[enlFilt (N := N) p m (t + 1)]
      (fun U : Array N => runMax p m U j (t + 1)) :=
    VdriftAssembly.measurable_runMax_enl p m (t + 1) j
  have h1 : Measurable[enlFilt (N := N) p m (t + 1)]
      (fun U : Array N => SwarmOcc.Fcorr (aRec p m) eps (bRec p m (t + 1) j U)
        ((trajectory p m U (t + 1)).pos i - runMax p m U j (t + 1))) :=
    VdriftAssembly.measurable_Fcorr_gap_enl hp m (t + 1) j (aRec p m) eps (hpos.sub hrun')
  have h0 : Measurable[enlFilt (N := N) p m (t + 1)]
      (fun U : Array N => SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
        ((trajectory p m U (t + 1)).pos i - runMax p m U j t)) :=
    measurable_Fcorr_gap_mono hp (Nat.le_succ t) j (aRec p m) eps (hpos.sub hrun)
  exact (h1.sub h0).stronglyMeasurable

/-- **The paper's `(Vdrift)` increment of the projected ledger**,
`Z_{t+1} - Z_t + J_{t+1}`. -/
noncomputable def ZJincProj (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) (t : ℕ) : ℝ :=
  Zproj p m eps i j U (t + 1) - Zproj p m eps i j U t + JcorrProj p m eps i j U t

/-- **The projected ledger increment is `enlFilt p m (t+1)`-strongly measurable, with no
hypothesis.**  This is the source-faithful replacement for the `hadapt` premise of
`CompensatorMeanZero.martingale_Qcomp`, which `QIncrementAdapted.not_stronglyMeasurable_ZJinc_zero`
refutes for the quenched ledger. -/
theorem stronglyMeasurable_ZJincProj {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m : ℕ) (t : ℕ) (i j : Fin N)
    (eps : ℝ) :
    StronglyMeasurable[enlFilt (N := N) p m (t + 1)] (fun U => ZJincProj p m eps i j U t) := by
  have hmono : (enlFilt (N := N) p m t : MeasurableSpace (Array N)) ≤ enlFilt p m (t + 1) :=
    Filtration.mono (enlFilt (N := N) p m) (Nat.le_succ t)
  have hZ1 : StronglyMeasurable[enlFilt (N := N) p m (t + 1)]
      (fun U : Array N => Zproj p m eps i j U (t + 1)) :=
    stronglyMeasurable_Zproj hp m (t + 1) i j eps
  have hZ0 : StronglyMeasurable[enlFilt (N := N) p m (t + 1)]
      (fun U : Array N => Zproj p m eps i j U t) :=
    (stronglyMeasurable_Zproj hp m t i j eps).mono hmono
  exact (hZ1.sub hZ0).add (stronglyMeasurable_JcorrProj hp m t i j eps)

end Swarming.Enl

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross

variable {N : ℕ}

/-! ## 4. Pointwise (almost sure) bounds: the projected ledger is bounded at every fixed time

`condExp` is only defined up to a null set, so every bound in this section is an almost-sure
statement.  Countably many sites are involved (`L` is `ℤ`-valued), so the sitewise bounds
combine to a bound at the random site by `MeasureTheory.ae_all_iff`. -/

/-- The explicit bound for `H_{j,n}(y)` at site `y`. -/
noncomputable def hbnd (y : ℤ) : ℝ :=
  |(y : ℝ)| + (y.toNat : ℝ) * (2 * (y.toNat : ℝ) + 3)

/-- Pointwise bound for the quenched potential at a fixed site. -/
theorem abs_Hpot_site_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hpne : p ≠ 0)
    (m : ℕ) (j : Fin N) (y : ℤ) (U : Array N) :
    |SwarmOcc.Hpot (siteH p m j U) y| ≤ hbnd y := by
  have hmain : |SwarmOcc.Hpot (siteH p m j U) y|
      ≤ |(y : ℝ)| + (y.toNat : ℝ) * (2 * (y.toNat : ℝ) + 3) := by
    by_cases hy : y ≤ 0
    · rw [SwarmOcc.Hpot_of_nonpos hy, Int.toNat_of_nonpos hy, Nat.cast_zero, zero_mul, add_zero]
    · have hy0 : 0 ≤ y := by omega
      have hrew : SwarmOcc.Hpot (siteH p m j U) y
          = ∑ u ∈ Finset.range y.toNat,
              SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u := by
        rw [SwarmOcc.Hpot, if_neg hy]
        rfl
      rw [hrew]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have h1 : ∑ u ∈ Finset.range y.toNat,
            |SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u|
          ≤ ∑ u ∈ Finset.range y.toNat, (2 * (u : ℝ) + 3) :=
        Finset.sum_le_sum fun u _ => SwarmShiftMarks.abs_hof_le' hp0 hp1 hpne _ u
      have h2 : ∑ u ∈ Finset.range y.toNat, (2 * (u : ℝ) + 3)
          ≤ (y.toNat : ℝ) * (2 * (y.toNat : ℝ) + 3) := by
        have hterm : ∀ u ∈ Finset.range y.toNat,
            (2 * (u : ℝ) + 3) ≤ 2 * (y.toNat : ℝ) + 3 := by
          intro u hu
          have hu' : u < y.toNat := Finset.mem_range.mp hu
          have : (u : ℝ) ≤ (y.toNat : ℝ) := by exact_mod_cast Nat.le_of_lt hu'
          linarith
        calc ∑ u ∈ Finset.range y.toNat, (2 * (u : ℝ) + 3)
            ≤ ∑ _u ∈ Finset.range y.toNat, (2 * (y.toNat : ℝ) + 3) := Finset.sum_le_sum hterm
          _ = (y.toNat : ℝ) * (2 * (y.toNat : ℝ) + 3) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      linarith [le_trans h1 h2, abs_nonneg (y : ℝ)]
  exact hmain

/-- **`|H_{j,n}(y)| <= hbnd y` almost surely**, uniformly in the array. -/
theorem abs_projH_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hpne : p ≠ 0)
    (m : ℕ) (j : Fin N) (n : ℕ) (y : ℤ) :
    ∀ᵐ U ∂(arrayMeasure N), |projH p m j n U y| ≤ hbnd y := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hIntf := integrable_Hpot_site hp0 hp1 hpne m j y
  have hIntC : Integrable (fun _ : Array N => hbnd y) (arrayMeasure N) := integrable_const _
  have hle : (fun V : Array N => SwarmOcc.Hpot (siteH p m j V) y) ≤ᵐ[arrayMeasure N]
      fun _ => hbnd y :=
    Filter.Eventually.of_forall fun V => le_of_abs_le (abs_Hpot_site_le hp0 hp1 hpne m j y V)
  have hge : (fun _ : Array N => -hbnd y) ≤ᵐ[arrayMeasure N]
      fun V => SwarmOcc.Hpot (siteH p m j V) y :=
    Filter.Eventually.of_forall fun V => neg_le_of_abs_le (abs_Hpot_site_le hp0 hp1 hpne m j y V)
  have h1 : condExp (enlFilt p m n) (arrayMeasure N) (fun V => SwarmOcc.Hpot (siteH p m j V) y)
      ≤ᵐ[arrayMeasure N] fun _ => hbnd y := by
    have h := condExp_mono (m := enlFilt p m n) hIntf hIntC hle
    rwa [condExp_const ((enlFilt (N := N) p m).le n) (hbnd y)] at h
  have h2 : condExp (enlFilt p m n) (arrayMeasure N) (fun _ : Array N => -hbnd y)
      ≤ᵐ[arrayMeasure N]
      condExp (enlFilt p m n) (arrayMeasure N) (fun V => SwarmOcc.Hpot (siteH p m j V) y) :=
    condExp_mono (m := enlFilt p m n) (integrable_const (-hbnd y)) hIntf hge
  have h2' : (fun _ : Array N => -hbnd y) ≤ᵐ[arrayMeasure N]
      condExp (enlFilt p m n) (arrayMeasure N) (fun V => SwarmOcc.Hpot (siteH p m j V) y) := by
    have h := h2
    rwa [condExp_const ((enlFilt (N := N) p m).le n) (-hbnd y)] at h
  filter_upwards [h1, h2'] with U hU1 hU2
  exact abs_le.mpr ⟨hU2, hU1⟩

/-- `hbnd` at a reachable site is bounded by its value at the time index. -/
theorem hbnd_le_of_abs_le {y : ℤ} {t : ℕ} (h : |y| ≤ (t : ℤ)) :
    hbnd y ≤ (t : ℝ) + (t : ℝ) * (2 * (t : ℝ) + 3) := by
  have hy : y ≤ (t : ℤ) := le_trans (le_abs_self y) h
  have hyn : y.toNat ≤ t := Int.toNat_le_toNat hy
  have hcast : (y.toNat : ℝ) ≤ (t : ℝ) := by exact_mod_cast hyn
  have habs : |(y : ℝ)| ≤ (t : ℝ) := by
    rw [← Int.cast_abs, ← Int.cast_natCast (n := t)]
    exact_mod_cast h
  have hprod : (y.toNat : ℝ) * (2 * (y.toNat : ℝ) + 3) ≤ (t : ℝ) * (2 * (t : ℝ) + 3) :=
    mul_le_mul hcast (by linarith) (by positivity) (by positivity)
  unfold hbnd
  linarith

/-- The explicit bound for the correction term `F_{b_t}` at time `t`. -/
noncomputable def fbnd (p : ℝ) (m : ℕ) (eps : ℝ) (t : ℕ) : ℝ :=
  (2 * (t : ℝ) + 5) ^ 2 / (eps * (1 - aRec p m) ^ 2)

/-- The explicit bound for the projected potential `Z_t`. -/
noncomputable def zbnd (p : ℝ) (m : ℕ) (eps : ℝ) (t : ℕ) : ℝ :=
  ((t : ℝ) + (t : ℝ) * (2 * (t : ℝ) + 3)) + fbnd p m eps t

/-- **`H_{j,n}(X_n^i)` is almost surely bounded** by the deterministic `hbnd` at time `n`. -/
theorem ae_abs_projH_pos_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hpne : p ≠ 0)
    (m : ℕ) (j : Fin N) (n : ℕ) (i : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N),
      |projH p m j n U ((trajectory p m U n).pos i)|
        ≤ (n : ℝ) + (n : ℝ) * (2 * (n : ℝ) + 3) := by
  have hall : ∀ᵐ U ∂(arrayMeasure N), ∀ y : ℤ, |projH p m j n U y| ≤ hbnd y := by
    rw [MeasureTheory.ae_all_iff]
    intro y
    exact abs_projH_le hp0 hp1 hpne m j n y
  filter_upwards [hall] with U hU
  exact le_trans (hU ((trajectory p m U n).pos i))
    (hbnd_le_of_abs_le (ZBudget.abs_pos_le_time p m U i n))

/-- **`|Z_t|` is almost surely bounded at every fixed time.** -/
theorem abs_Zproj_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hpne : p ≠ 0)
    (m t : ℕ) (i j : Fin N) {eps : ℝ} (hε : 0 < eps) :
    ∀ᵐ U ∂(arrayMeasure N), |Zproj p m eps i j U t| ≤ zbnd p m eps t := by
  filter_upwards [ae_abs_projH_pos_le hp0 hp1 hpne m j t i] with U h1
  have h3 : |SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
      ((trajectory p m U t).pos i - runMax p m U j t)| ≤ fbnd p m eps t :=
    VdriftAssembly.abs_Fcorr_bRec_le hp0 hp1 m t j hε U
      ((trajectory p m U t).pos i - runMax p m U j t)
  have htri : |Zproj p m eps i j U t|
      ≤ |projH p m j t U ((trajectory p m U t).pos i)|
        + |SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
          ((trajectory p m U t).pos i - runMax p m U j t)| :=
    abs_sub _ _
  unfold zbnd
  linarith

/-- **`|J_{t+1}|` is almost surely bounded at every fixed time.** -/
theorem abs_JcorrProj_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m t : ℕ)
    (i j : Fin N) {eps : ℝ} (hε : 0 < eps) :
    ∀ᵐ U ∂(arrayMeasure N), |JcorrProj p m eps i j U t| ≤ 2 * fbnd p m eps (t + 1) := by
  have hmono : fbnd p m eps t ≤ fbnd p m eps (t + 1) := by
    unfold fbnd
    have hden : (0 : ℝ) < eps * (1 - aRec p m) ^ 2 := by
      have h1a : (0 : ℝ) < 1 - aRec p m := by linarith [aRec_lt_one hp0 hp1 m]
      positivity
    have hnum : (2 * (t : ℝ) + 5) ^ 2 ≤ (2 * ((t + 1 : ℕ) : ℝ) + 5) ^ 2 := by
      have h0 : (0 : ℝ) ≤ 2 * (t : ℝ) + 5 := by positivity
      have h1 : (2 * (t : ℝ) + 5) ≤ (2 * ((t + 1 : ℕ) : ℝ) + 5) := by
        push_cast
        linarith
      nlinarith
    exact div_le_div_of_nonneg_right hnum hden.le
  filter_upwards with U
  have h1 : |SwarmOcc.Fcorr (aRec p m) eps (bRec p m (t + 1) j U)
      ((trajectory p m U (t + 1)).pos i - runMax p m U j (t + 1))|
      ≤ fbnd p m eps (t + 1) :=
    VdriftAssembly.abs_Fcorr_bRec_le hp0 hp1 m (t + 1) j hε U
      ((trajectory p m U (t + 1)).pos i - runMax p m U j (t + 1))
  have h2 : |SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
      ((trajectory p m U (t + 1)).pos i - runMax p m U j t)| ≤ fbnd p m eps (t + 1) := by
    have hb := VdriftAssembly.abs_Fcorr_bRec_le hp0 hp1 m t j hε U
      ((trajectory p m U (t + 1)).pos i - runMax p m U j t)
    have hb' : |SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
        ((trajectory p m U (t + 1)).pos i - runMax p m U j t)| ≤ fbnd p m eps t := hb
    linarith
  have htri : |JcorrProj p m eps i j U t|
      ≤ |SwarmOcc.Fcorr (aRec p m) eps (bRec p m (t + 1) j U)
          ((trajectory p m U (t + 1)).pos i - runMax p m U j (t + 1))|
        + |SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
          ((trajectory p m U (t + 1)).pos i - runMax p m U j t)| := by
    unfold JcorrProj
    exact abs_sub _ _
  linarith

/-- The explicit bound for the projected ledger increment at time `t`. -/
noncomputable def zjbnd (p : ℝ) (m : ℕ) (eps : ℝ) (t : ℕ) : ℝ :=
  zbnd p m eps (t + 1) + zbnd p m eps t + 2 * fbnd p m eps (t + 1)

/-- **`|Z_{t+1} - Z_t + J_{t+1}|` is almost surely bounded at every fixed time.** -/
theorem abs_ZJincProj_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hpne : p ≠ 0)
    (m t : ℕ) (i j : Fin N) {eps : ℝ} (hε : 0 < eps) :
    ∀ᵐ U ∂(arrayMeasure N), |ZJincProj p m eps i j U t| ≤ zjbnd p m eps t := by
  filter_upwards [abs_Zproj_le hp0 hp1 hpne m (t + 1) i j hε,
    abs_Zproj_le hp0 hp1 hpne m t i j hε, abs_JcorrProj_le hp0 hp1 m t i j hε]
    with U h1 h0 hJ
  have htri : |ZJincProj p m eps i j U t|
      ≤ |Zproj p m eps i j U (t + 1)| + |Zproj p m eps i j U t|
        + |JcorrProj p m eps i j U t| := by
    have hstep : |ZJincProj p m eps i j U t|
        ≤ |Zproj p m eps i j U (t + 1) - Zproj p m eps i j U t| + |JcorrProj p m eps i j U t| := by
      unfold ZJincProj
      exact abs_add_le _ _
    have h2 : |Zproj p m eps i j U (t + 1) - Zproj p m eps i j U t|
        ≤ |Zproj p m eps i j U (t + 1)| + |Zproj p m eps i j U t| := abs_sub _ _
    linarith
  unfold zjbnd
  linarith

/-! ### Integrability of the projected ledger -/

/-- Everything bounded and adapted is integrable on the probability space `arrayMeasure N`. -/
theorem integrable_of_abs_le {f : Array N → ℝ} {C : ℝ} (hf : StronglyMeasurable f)
    (h : ∀ᵐ U ∂(arrayMeasure N), |f U| ≤ C) :
    Integrable f (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  refine Integrable.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards [h] with U hU
  rwa [Real.norm_eq_abs]

/-- `Z_t` is integrable. -/
theorem integrable_Zproj {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hpne : p ≠ 0)
    (m t : ℕ) (i j : Fin N) {eps : ℝ} (hε : 0 < eps) :
    Integrable (fun U : Array N => Zproj p m eps i j U t) (arrayMeasure N) :=
  integrable_of_abs_le
    ((stronglyMeasurable_Zproj hp0.le m t i j eps).mono (Filtration.le (enlFilt (N := N) p m) t))
    (abs_Zproj_le hp0 hp1 hpne m t i j hε)

/-- `J_{t+1}` is integrable. -/
theorem integrable_JcorrProj {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m t : ℕ)
    (i j : Fin N) {eps : ℝ} (hε : 0 < eps) :
    Integrable (fun U : Array N => JcorrProj p m eps i j U t) (arrayMeasure N) :=
  integrable_of_abs_le
    ((stronglyMeasurable_JcorrProj hp0.le m t i j eps).mono
      (Filtration.le (enlFilt (N := N) p m) (t + 1)))
    (abs_JcorrProj_le hp0 hp1 m t i j hε)

/-- The projected ledger increment `Z_{t+1} - Z_t + J_{t+1}` is integrable. -/
theorem integrable_ZJincProj {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hpne : p ≠ 0)
    (m t : ℕ) (i j : Fin N) {eps : ℝ} (hε : 0 < eps) :
    Integrable (fun U : Array N => ZJincProj p m eps i j U t) (arrayMeasure N) :=
  integrable_of_abs_le
    ((stronglyMeasurable_ZJincProj hp0.le m t i j eps).mono
      (Filtration.le (enlFilt (N := N) p m) (t + 1)))
    (abs_ZJincProj_le hp0 hp1 hpne m t i j hε)


end Swarming.Enl

/-! ## 5. A general lemma: partial sums of centred adapted increments are a martingale -/

namespace ProjMart

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}

/-- **Partial sums of centred adapted increments form a martingale.**  No integrability beyond
the increments themselves, and no independence: zero conditional mean at the increment's own
time is enough. -/
theorem martingale_partialSums_of_centred [IsFiniteMeasure μ] {g : ℕ → Ω → ℝ}
    (hint : ∀ k, Integrable (g k) μ)
    (had : ∀ k, StronglyMeasurable[ℱ (k + 1)] (g k))
    (hmean : ∀ k, μ[g k | ℱ k] =ᵐ[μ] 0) :
    Martingale (fun n => ∑ k ∈ Finset.range n, g k) ℱ μ := by
  refine ⟨fun n => ?_, ?_⟩
  · exact Finset.stronglyMeasurable_sum _ fun k hk =>
      (had k).mono (Filtration.mono ℱ (Finset.mem_range.1 hk))
  · intro i j hij
    have hsum : ∀ k : ℕ, μ[g k | ℱ i] =ᵐ[μ] (if k < i then g k else 0) := by
      intro k
      split_ifs with hk
      · refine Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable (ℱ.le i) ?_ (hint k))
        exact (had k).mono (Filtration.mono ℱ (Nat.succ_le_of_lt hk))
      · have hik : i ≤ k := Nat.le_of_not_lt hk
        have htower : μ[μ[g k | ℱ k] | ℱ i] =ᵐ[μ] μ[g k | ℱ i] :=
          condExp_condExp_of_le (Filtration.mono ℱ hik) (ℱ.le k)
        have hzero : μ[μ[g k | ℱ k] | ℱ i] =ᵐ[μ] 0 := by
          refine (condExp_congr_ae (hmean k)).trans ?_
          simp
        exact htower.symm.trans hzero
    have h1 := condExp_finsetSum (s := Finset.range j) (f := g) (fun k _ => hint k) (ℱ i)
    have h2 : (∑ k ∈ Finset.range j, μ[g k | ℱ i]) =ᵐ[μ]
        ∑ k ∈ Finset.range j, (if k < i then g k else 0) :=
      MartingaleLimit.finset_ae_sum_congr fun k _ => hsum k
    have h3 : (∑ k ∈ Finset.range j, (if k < i then g k else 0)) = ∑ k ∈ Finset.range i, g k :=
      MartingaleLimit.sum_range_ite_lt hij
    show μ[∑ k ∈ Finset.range j, g k | ℱ i] =ᵐ[μ] (∑ k ∈ Finset.range i, g k)
    exact h3 ▸ h1.trans h2

end ProjMart

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross

variable {N : ℕ}

/-! ## 6. Pointwise ledger algebra and the telescoping identity -/

/-- **The exact increment identity of the projected ledger** (the paper's decomposition
`Z_{n+1} - Z_n + J_{n+1} = (H_{n+1} - H_n) - dF_b`, now with the *projected* potential). -/
theorem Zproj_add_J (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) (t : ℕ) :
    Zproj p m eps i j U (t + 1) - Zproj p m eps i j U t + JcorrProj p m eps i j U t
      = projH p m j (t + 1) U ((trajectory p m U (t + 1)).pos i)
        - projH p m j t U ((trajectory p m U t).pos i)
        - (SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
            ((trajectory p m U (t + 1)).pos i - runMax p m U j t)
          - SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
            ((trajectory p m U t).pos i - runMax p m U j t)) := by
  simp only [Zproj, JcorrProj]
  ring

/-- The telescoping identity of the projected ledger: the sum of the increments is the
`Z`-difference plus the summed `J`-corrections. -/
theorem sum_ZJincProj (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) (T : ℕ) :
    ∑ t ∈ Finset.range T, ZJincProj p m eps i j U t
      = Zproj p m eps i j U T - Zproj p m eps i j U 0
        + ∑ t ∈ Finset.range T, JcorrProj p m eps i j U t := by
  have h : ∀ t : ℕ, ZJincProj p m eps i j U t
      = (Zproj p m eps i j U (t + 1) - Zproj p m eps i j U t)
        + JcorrProj p m eps i j U t := fun t => rfl
  simp only [h, Finset.sum_add_distrib, Finset.sum_range_sub]

/-! ## 6. The centred projected increments and the martingale `Q` -/

/-- The **centred projected ledger increment**: `(Z_{t+1} - Z_t + J_{t+1})` minus its
`enlFilt p m t`-conditional mean.  This is the paper's `Q`-increment. -/
noncomputable def qincProj (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) (t : ℕ) : ℝ :=
  ZJincProj p m eps i j U t
    - condExp (enlFilt p m t) (arrayMeasure N) (fun V => ZJincProj p m eps i j V t) U

/-- The **paper's `Q`** for the projected ledger: the partial sums of the centred increments. -/
noncomputable def QProj (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, qincProj p m eps i j U t

/-- The centred projected increment is integrable. -/
theorem integrable_qincProj {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hpne : p ≠ 0)
    (m t : ℕ) (i j : Fin N) {eps : ℝ} (hε : 0 < eps) :
    Integrable (fun U : Array N => qincProj p m eps i j U t) (arrayMeasure N) :=
  (integrable_ZJincProj hp0 hp1 hpne m t i j hε).sub integrable_condExp

/-- The centred projected increment is `enlFilt p m t`-strongly measurable. -/
theorem stronglyMeasurable_qincProj {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m t : ℕ) (i j : Fin N)
    (eps : ℝ) :
    StronglyMeasurable[enlFilt (N := N) p m (t + 1)] (fun U => qincProj p m eps i j U t) := by
  have hmono : (enlFilt (N := N) p m t : MeasurableSpace (Array N)) ≤ enlFilt p m (t + 1) :=
    Filtration.mono (enlFilt (N := N) p m) (Nat.le_succ t)
  have hZ : StronglyMeasurable[enlFilt (N := N) p m (t + 1)]
      (fun U : Array N => ZJincProj p m eps i j U t) :=
    stronglyMeasurable_ZJincProj hp m t i j eps
  have hC : StronglyMeasurable[enlFilt (N := N) p m (t + 1)]
      (fun U : Array N => condExp (enlFilt p m t) (arrayMeasure N)
        (fun V => ZJincProj p m eps i j V t) U) := by
    have h0 : StronglyMeasurable[enlFilt (N := N) p m t]
        (fun U : Array N => condExp (enlFilt p m t) (arrayMeasure N)
          (fun V => ZJincProj p m eps i j V t) U) :=
      MeasureTheory.stronglyMeasurable_condExp
    exact h0.mono hmono
  exact hZ.sub hC

/-- **The centred projected increment has zero conditional mean** — by construction, not by any
model-specific orthogonality. -/
theorem condExp_qincProj_eq_zero {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hpne : p ≠ 0)
    (m t : ℕ) (i j : Fin N) {eps : ℝ} (hε : 0 < eps) :
    condExp (enlFilt p m t) (arrayMeasure N) (fun U => qincProj p m eps i j U t)
      =ᵐ[arrayMeasure N] 0 := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hf : Integrable (fun U : Array N => ZJincProj p m eps i j U t) (arrayMeasure N) :=
    integrable_ZJincProj hp0 hp1 hpne m t i j hε
  have hg : Integrable (fun U : Array N => condExp (enlFilt p m t) (arrayMeasure N)
      (fun V => ZJincProj p m eps i j V t) U) (arrayMeasure N) :=
    integrable_condExp
  have hsub := condExp_sub hf hg (enlFilt p m t)
  have hsub' : condExp (enlFilt p m t) (arrayMeasure N)
      (fun U => ZJincProj p m eps i j U t
        - condExp (enlFilt p m t) (arrayMeasure N) (fun V => ZJincProj p m eps i j V t) U)
      =ᵐ[arrayMeasure N]
      ((fun U => condExp (enlFilt p m t) (arrayMeasure N)
          (fun V => ZJincProj p m eps i j V t) U)
        - (fun U => condExp (enlFilt p m t) (arrayMeasure N)
            (fun V => condExp (enlFilt p m t) (arrayMeasure N)
              (fun W => ZJincProj p m eps i j W t) V) U)) := by
    have hEq : (fun U : Array N => ZJincProj p m eps i j U t
        - condExp (enlFilt p m t) (arrayMeasure N) (fun V => ZJincProj p m eps i j V t) U)
        = (fun U : Array N => ZJincProj p m eps i j U t)
          - (fun U : Array N => condExp (enlFilt p m t) (arrayMeasure N)
              (fun V => ZJincProj p m eps i j V t) U) := rfl
    rw [hEq]
    exact hsub
  have hfix : condExp (enlFilt p m t) (arrayMeasure N)
      (fun U => condExp (enlFilt p m t) (arrayMeasure N)
        (fun V => ZJincProj p m eps i j V t) U)
      =ᵐ[arrayMeasure N] (fun U => condExp (enlFilt p m t) (arrayMeasure N)
        (fun V => ZJincProj p m eps i j V t) U) :=
    Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable ((enlFilt (N := N) p m).le t)
      MeasureTheory.stronglyMeasurable_condExp hg)
  filter_upwards [hsub', hfix] with U hU hF
  simp only [qincProj, Pi.sub_apply, Pi.zero_apply] at hU hF ⊢
  rw [hU, hF]
  ring

/-- **The paper's `Q` is a genuine martingale in the enlarged filtration**, with no adaptedness
hypothesis: the increments are centred by construction and adapted because the potential is the
proper conditional expectation `H_{j,n}`, not the quenched `H_j`. -/
theorem martingale_QProj {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hpne : p ≠ 0)
    (m : ℕ) (i j : Fin N) {eps : ℝ} (hε : 0 < eps) :
    Martingale (fun T (U : Array N) => QProj p m eps i j U T) (enlFilt p m) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have h := ProjMart.martingale_partialSums_of_centred
    (μ := arrayMeasure N) (ℱ := enlFilt (N := N) p m)
    (g := fun t U => qincProj p m eps i j U t)
    (fun t => integrable_qincProj hp0 hp1 hpne m t i j hε)
    (fun t => stronglyMeasurable_qincProj hp0.le m t i j eps)
    (fun t => condExp_qincProj_eq_zero hp0 hp1 hpne m t i j hε)
  rw [show (fun T (U : Array N) => QProj p m eps i j U T)
      = (fun n => ∑ k ∈ Finset.range n, fun U => qincProj p m eps i j U k) from by
        funext T U
        simp only [QProj, Finset.sum_apply]]
  exact h

end Swarming.Enl
