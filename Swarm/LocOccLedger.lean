/-
  # The summed `(Vdrift)` ledger of `(lococc)` on the **actual array**

  This file discharges the `hled` field of `LocOcc.lococc_window` in the concrete model.  The
  paper's first display in the proof of `(lococc)` is

      sum_{u=s}^{t-1} 1{0 <= X_u^i <= M_u^j}
        <= eps (t-s) + (Z_t - Z_s) + sum_{u=s}^{t-1} J_{u+1} - (Q_t - Q_s),

  obtained by summing `(Vdrift)` from `s` to `t-1`.  Here `Z` is the *adapted* projected potential
  `Zproj = E[Zpot | F_t]` of `ProjOptionalLedger` (the raw `Zpot` is not `F_t`-adapted), `Q` is its
  compensator `Qpl`, and `J` is the record cost `Jcorr`.  The one-step input is
  `ProjOptionalLedger.proj_oneStep_Edrift`; no adaptedness or orthogonality of the raw ledger is
  used anywhere.

  Result: for every `1/2 < p < 1`, `2 <= m`, `i != j`, `eps > 0` and `s <= t`, the display holds
  `arrayMeasure N`-almost surely, with no further hypothesis.
-/
import Swarm.LocOccProjected
import Swarm.ProjOptionalLedger

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace LocOcc

/-- **`(Vdrift)` in ledger form, at every time, almost surely, on the actual array.** -/
theorem ae_step_ledger_actual {N : ℕ} {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) {i j : Fin N} (hij : i ≠ j) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), ∀ u : ℕ,
      SwarmOcc.occInd (fun s => (Swarming.Trajectory.trajectory p m U s).pos i)
          (fun s => Swarming.Trajectory.runMax p m U j s) u - ε
        ≤ (Swarming.Enl.ProjLedger.Zproj p m ε i j (u + 1) U
            - Swarming.Enl.ProjLedger.Zproj p m ε i j u U)
          + Swarming.Enl.VdriftAssembly.Jcorr p m ε i j U u
          - (Swarming.Enl.ProjLedger.Qpl p m ε i j (u + 1) U
            - Swarming.Enl.ProjLedger.Qpl p m ε i j u U) := by
  have hstep : ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), ∀ u : ℕ,
      SwarmOcc.occInd (fun s => (Swarming.Trajectory.trajectory p m U s).pos i)
          (fun s => Swarming.Trajectory.runMax p m U j s) u - ε
        ≤ Swarming.Enl.VdriftAssembly.Edrift p m ε (fun r => SwarmCross.alphaFun p m r i) i j U u := by
    rw [MeasureTheory.ae_all_iff]
    intro u
    filter_upwards [Swarming.Enl.ProjLedger.proj_oneStep_Edrift (N := N) hp0 hp1 hm hij hε u]
      with U hU
    linarith
  filter_upwards [hstep] with U hU u
  have hQ : Swarming.Enl.ProjLedger.Qpl p m ε i j (u + 1) U
        - Swarming.Enl.ProjLedger.Qpl p m ε i j u U
      = Swarming.Enl.ProjLedger.projInc p m ε i j u U := by
    simp only [Swarming.Enl.ProjLedger.Qpl, Finset.sum_range_succ]
    ring
  have hinc : Swarming.Enl.ProjLedger.projInc p m ε i j u U
      = (Swarming.Enl.ProjLedger.Zproj p m ε i j (u + 1) U
            - Swarming.Enl.ProjLedger.Zproj p m ε i j u U)
          + Swarming.Enl.VdriftAssembly.Jcorr p m ε i j U u
          - Swarming.Enl.VdriftAssembly.Edrift p m ε (fun r => SwarmCross.alphaFun p m r i) i j U u :=
    rfl
  have huu := hU u
  rw [hQ, hinc]
  linarith

/-- **The paper's window ledger on the actual array.**  Summing `(Vdrift)` from `s` to `t-1`:

    `sum_{u in [s,t)} 1{0 <= X_u^i <= M_u^j} <= eps (t-s) + (Z_t - Z_s) + sum_{u in [s,t)} J_{u+1} - (Q_t - Q_s)`,

almost surely, with the adapted projected potential and its compensator. -/
theorem window_ledger_actual {N : ℕ} {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) {i j : Fin N} (hij : i ≠ j) {ε : ℝ} (hε : 0 < ε) {s t : ℕ} (hst : s ≤ t) :
    ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
      ∑ u ∈ Finset.Ico s t,
          SwarmOcc.occInd (fun r => (Swarming.Trajectory.trajectory p m U r).pos i)
            (fun r => Swarming.Trajectory.runMax p m U j r) u
        ≤ ε * ((t : ℝ) - (s : ℝ))
          + (Swarming.Enl.ProjLedger.Zproj p m ε i j t U
            - Swarming.Enl.ProjLedger.Zproj p m ε i j s U)
          + (∑ u ∈ Finset.Ico s t, Swarming.Enl.VdriftAssembly.Jcorr p m ε i j U u)
          - (Swarming.Enl.ProjLedger.Qpl p m ε i j t U
            - Swarming.Enl.ProjLedger.Qpl p m ε i j s U) := by
  filter_upwards [ae_step_ledger_actual (N := N) hp0 hp1 hm hij hε] with U hU
  exact window_le_of_step (occ := fun u =>
      SwarmOcc.occInd (fun r => (Swarming.Trajectory.trajectory p m U r).pos i)
        (fun r => Swarming.Trajectory.runMax p m U j r) u)
    (J := fun u => Swarming.Enl.VdriftAssembly.Jcorr p m ε i j U u)
    (Z := fun n => Swarming.Enl.ProjLedger.Zproj p m ε i j n U)
    (Q := fun n => Swarming.Enl.ProjLedger.Qpl p m ε i j n U) hst (fun u => hU u)

/-- The paper's `eps = 1/8` instance. -/
theorem window_ledger_actual_eighth {N : ℕ} {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) {i j : Fin N} (hij : i ≠ j) {s t : ℕ} (hst : s ≤ t) :
    ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
      ∑ u ∈ Finset.Ico s t,
          SwarmOcc.occInd (fun r => (Swarming.Trajectory.trajectory p m U r).pos i)
            (fun r => Swarming.Trajectory.runMax p m U j r) u
        ≤ (1 / 8) * ((t : ℝ) - (s : ℝ))
          + (Swarming.Enl.ProjLedger.Zproj p m (1 / 8) i j t U
            - Swarming.Enl.ProjLedger.Zproj p m (1 / 8) i j s U)
          + (∑ u ∈ Finset.Ico s t, Swarming.Enl.VdriftAssembly.Jcorr p m (1 / 8) i j U u)
          - (Swarming.Enl.ProjLedger.Qpl p m (1 / 8) i j t U
            - Swarming.Enl.ProjLedger.Qpl p m (1 / 8) i j s U) :=
  window_ledger_actual hp0 hp1 hm hij (by norm_num) hst


/-- **The `(lococc)` indicator on a positive window.**  Once walker `i` is nonnegative, the paper's
ledger indicator `1{0 <= X_u^i <= M_u^j}` is the position comparison `1{X_u^i <= M_u^j}` used in
the display of `(lococc)`; this is the `hocc` field of `LocOcc.lococc_window` on `{d_r <= L}`. -/
theorem occInd_eq_of_nonneg {X r : ℕ → ℤ} {u : ℕ} (h : 0 ≤ X u) :
    SwarmOcc.occInd X r u = if X u ≤ r u then (1 : ℝ) else 0 := by
  unfold SwarmOcc.occInd
  by_cases hle : X u ≤ r u
  · rw [if_pos ⟨h, hle⟩, if_pos hle]
  · rw [if_neg (fun hc => hle hc.2), if_neg hle]

end LocOcc
