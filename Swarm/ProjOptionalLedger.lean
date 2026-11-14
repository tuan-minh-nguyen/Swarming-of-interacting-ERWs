/-
  **ProjLedger.lean — the paper's adapted `Z_n` *is* the optional projection of the static
  potential ledger, and its compensator is invariant under that projection.**

  Source point.  In the proof of Proposition `ball` of `main_1d_revised.tex` the paper sets

      `Z_n = H_{j,n}(X_n^i) - F_{b_n}(X_n^i - r_n)`,  `H_{j,n}(x) = E[H_j(x) | F_n]`,
      `J_{n+1} = F_{b_{n+1}}(X_{n+1}^i - r_{n+1}) - F_{b_n}(X_{n+1}^i - r_n)`,

  and then uses `(Vdrift)` `E[Z_{n+1} - Z_n + J_{n+1} | F_n] >= 1{0 <= X_n^i <= M_n^j} - eps` and
  the martingale `Q_n = sum_{t<n} (Z_{t+1}-Z_t+J_{t+1} - E[...|F_t])`.

  What is proved here, with no hypotheses beyond `1/2 < p < 1`, `0 < eps` and (for the last
  step) `2 <= m`, `i != j`:

  * `Zproj t` — the optional projection `E[Zpot_t | F_t]` of the campaign's static potential
    ledger `VdriftAssembly.Zpot t`, is `F_t`-strongly measurable (`stronglyMeasurable_Zproj`)
    and integrable (`integrable_Zproj`).  Since `X_t^i`, `M_t^j`, `b_t` are all `F_t`-measurable
    and `H_j(X_t^i)` is the inverse limit of the deterministic-site potentials
    `H_j(y) = Hpot (envH p m j) y`, `Zproj t` *is* the paper's `H_{j,t}(X_t^i) - F_{b_t}(...)`;
    see the discussion in `README.md` for the exact statement that this rests on.

  * `condExp_proj_ledger_eq` — **the compensator of the projected ledger equals the compensator
    of the static ledger**, `E[Zproj_{t+1} - Zproj_t + J_{t+1} | F_t]
    = E[Zpot_{t+1} - Zpot_t + J_{t+1} | F_t]`.  This is the tower property plus `F_t`-strong
    measurability of `Zproj t`; it does *not* use any adaptedness of the static `Zpot`, which is
    genuinely false (`QIncrementAdapted.not_stronglyMeasurable_ZJinc_zero`).

  * `condExp_proj_ledger_eq_Edrift` — that compensator *is* the campaign's `Edrift`, because
    `CorrectionDrift.condExp_Cinc` is unconditional (`compensator_of_correction`).

  * `proj_oneStep_Vdrift` — **`(Vdrift)` for the adapted projected ledger**: the paper's one-step
    drift inequality holds with `Zproj` in place of `Z`.  This is the version of `(Vdrift)` whose
    `Z` is genuinely `F_t`-adapted, so the paper's martingale step is available without any
    adaptedness/orthogonality substitute for the static ledger.

  What is *not* claimed: the summed occupation bound (it needs an upper budget for `Zproj`, i.e.
  the projected `(Vbound)`), the dyadic second moments of the projected increments, `Q_n/n -> 0`,
  `QResidual`, `Ballistic`, regeneration, or the main theorem.  Those stay explicit inputs.
-/
import Swarm.CorrectionDrift
import Swarm.QIncrementAdapted
import Swarm.GlobalPaperCondExp
import Swarm.QDefect

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl
namespace ProjLedger

open Swarming.Uniform Swarming.Trajectory
open Swarming.Enl.VdriftAssembly

variable {N : ℕ}

/-! ### 1. The optional projection of the static potential ledger -/

/-- The paper's adapted `Z_n`, defined as the optional projection `E[Zpot_t | F_t]` of the
campaign's static potential ledger `Zpot`.  By the tower property this is the only candidate for
an `F_t`-adapted process whose `F_t`-conditional increments agree with those of `Zpot`. -/
noncomputable def Zproj (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (t : ℕ) (U : Array N) : ℝ :=
  condExp (enlFilt p m t) (arrayMeasure N) (fun U => Zpot p m eps i j U t) U

theorem Zproj_def (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (t : ℕ) :
    Zproj p m eps i j t
      = condExp (enlFilt p m t) (arrayMeasure N) (fun U => Zpot p m eps i j U t) := rfl

/-- `Zproj t` is `F_t`-strongly measurable — this is exactly what the static `Zpot t` is not. -/
theorem stronglyMeasurable_Zproj (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (t : ℕ) :
    StronglyMeasurable[enlFilt p m t] (Zproj p m eps i j t) :=
  stronglyMeasurable_condExp

/-- The projected potential is integrable at every fixed time. -/
theorem integrable_Zproj {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) (i j : Fin N)
    {eps : ℝ} (hε : 0 < eps) (t : ℕ) :
    Integrable (Zproj p m eps i j t) (arrayMeasure N) :=
  integrable_condExp (μ := arrayMeasure N) (m := enlFilt p m t)
    (f := fun U : Array N => Zpot p m eps i j U t)

/-- At time `0` the paper's `Z` vanishes identically: `X_0^i = 0`, `M_0^j = 0`, and `F_b(g) = 0`
for `g <= 0`.  In particular the projection is the constant zero there. -/
theorem Zproj_zero (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) :
    Zproj p m eps i j 0 = fun _ : Array N => (0 : ℝ) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  funext U
  simp only [Zproj]
  rw [show (fun U : Array N => Zpot p m eps i j U 0) = fun _ => (0 : ℝ) from
    funext fun U => Zpot_zero p m eps i j U]
  simp

/-! ### 2. Linearity of the conditional expectation on the `a - b + c` shape -/

/-- `E[a - b + c | m] = E[a|m] - E[b|m] + E[c|m]`, assembled from `condExp_add`/`condExp_sub`.
Stated separately because every step below has this shape. -/
theorem condExp_sub_add {μ : Measure (Array N)} [IsFiniteMeasure μ]
    {m : MeasurableSpace (Array N)}
    {a b c : Array N → ℝ} (ha : Integrable a μ) (hb : Integrable b μ) (hc : Integrable c μ) :
    μ[((a - b) + c) | m] =ᵐ[μ] μ[a | m] - μ[b | m] + μ[c | m] := by
  have h1 : μ[((a - b) + c) | m] =ᵐ[μ] μ[a - b | m] + μ[c | m] :=
    condExp_add (ha.sub hb) hc m
  have h2 : μ[a - b | m] =ᵐ[μ] μ[a | m] - μ[b | m] := condExp_sub ha hb m
  refine h1.trans ?_
  filter_upwards [h2] with U hU
  simp only [Pi.add_apply, Pi.sub_apply] at hU ⊢
  rw [hU]

/-! ### 3. The compensator is invariant under the optional projection -/

/-- **Compensator invariance.**  Projecting the static potential ledger onto `F_t` does not
change its one-step conditional mean:

    `E[Zproj_{t+1} - Zproj_t + J_{t+1} | F_t] = E[Zpot_{t+1} - Zpot_t + J_{t+1} | F_t]`.

The two `J` terms agree trivially; `E[Zproj_{t+1}|F_t] = E[Zpot_{t+1}|F_t]` is the tower property
along `F_t <= F_{t+1}`, and `E[Zproj_t|F_t] = E[Zpot_t|F_t]` is the tower property at `F_t` with
itself.  No adaptedness of `Zpot` is used (and none holds). -/
theorem condExp_proj_ledger_eq {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m t : ℕ)
    (i j : Fin N) {eps : ℝ} (hε : 0 < eps) :
    condExp (enlFilt p m t) (arrayMeasure N)
        (fun U => Zproj p m eps i j (t + 1) U - Zproj p m eps i j t U + Jcorr p m eps i j U t)
      =ᵐ[arrayMeasure N]
    condExp (enlFilt p m t) (arrayMeasure N)
        (fun U => Zpot p m eps i j U (t + 1) - Zpot p m eps i j U t + Jcorr p m eps i j U t) := by
  show condExp (enlFilt p m t) (arrayMeasure N)
      (((Zproj p m eps i j (t + 1) - Zproj p m eps i j t))
        + fun U => Jcorr p m eps i j U t)
    =ᵐ[arrayMeasure N]
    condExp (enlFilt p m t) (arrayMeasure N)
      (((fun U : Array N => Zpot p m eps i j U (t + 1)) - fun U : Array N => Zpot p m eps i j U t)
        + fun U => Jcorr p m eps i j U t)
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hle : (enlFilt p m t : MeasurableSpace (Array N))
      ≤ (inferInstance : MeasurableSpace (Array N)) := (enlFilt p m).le t
  have hle' : (enlFilt p m (t + 1) : MeasurableSpace (Array N))
      ≤ (inferInstance : MeasurableSpace (Array N)) := (enlFilt p m).le (t + 1)
  have hmono : (enlFilt p m t : MeasurableSpace (Array N)) ≤ enlFilt p m (t + 1) :=
    Filtration.mono (enlFilt p m) (Nat.le_succ t)
  -- integrability of the two `Zpot` terms and of `J`
  have hi1 : Integrable (fun U : Array N => Zpot p m eps i j U (t + 1)) (arrayMeasure N) :=
    integrable_Zpot (eps := eps) hp0 hp1 m i j hε (t + 1)
  have hi0 : Integrable (fun U : Array N => Zpot p m eps i j U t) (arrayMeasure N) :=
    integrable_Zpot (eps := eps) hp0 hp1 m i j hε t
  have hiJ : Integrable (fun U : Array N => Jcorr p m eps i j U t) (arrayMeasure N) :=
    integrable_Jcorr hp0 hp1 m t i j (eps := eps) hε
  have hp1' : Integrable (Zproj p m eps i j (t + 1)) (arrayMeasure N) :=
    integrable_Zproj hp0 hp1 m i j hε (t + 1)
  have hp0' : Integrable (Zproj p m eps i j t) (arrayMeasure N) :=
    integrable_Zproj hp0 hp1 m i j hε t
  -- the two linear expansions
  have hL : condExp (enlFilt p m t) (arrayMeasure N)
      (((Zproj p m eps i j (t + 1) - Zproj p m eps i j t))
        + fun U => Jcorr p m eps i j U t)
      =ᵐ[arrayMeasure N]
      condExp (enlFilt p m t) (arrayMeasure N) (Zproj p m eps i j (t + 1))
        - condExp (enlFilt p m t) (arrayMeasure N) (Zproj p m eps i j t)
        + condExp (enlFilt p m t) (arrayMeasure N) (fun U => Jcorr p m eps i j U t) :=
    condExp_sub_add hp1' hp0' hiJ
  have hR : condExp (enlFilt p m t) (arrayMeasure N)
      (((fun U : Array N => Zpot p m eps i j U (t + 1)) - fun U : Array N => Zpot p m eps i j U t)
        + fun U => Jcorr p m eps i j U t)
      =ᵐ[arrayMeasure N]
      condExp (enlFilt p m t) (arrayMeasure N) (fun U => Zpot p m eps i j U (t + 1))
        - condExp (enlFilt p m t) (arrayMeasure N) (fun U => Zpot p m eps i j U t)
        + condExp (enlFilt p m t) (arrayMeasure N) (fun U => Jcorr p m eps i j U t) :=
    condExp_sub_add hi1 hi0 hiJ
  -- the two tower identities
  have hB : condExp (enlFilt p m t) (arrayMeasure N) (Zproj p m eps i j (t + 1))
      =ᵐ[arrayMeasure N]
      condExp (enlFilt p m t) (arrayMeasure N) (fun U => Zpot p m eps i j U (t + 1)) := by
    have h := condExp_condExp_of_le (μ := arrayMeasure N) (m₁ := enlFilt p m t)
      (m₂ := enlFilt p m (t + 1)) (m₀ := (inferInstance : MeasurableSpace (Array N)))
      (f := fun U : Array N => Zpot p m eps i j U (t + 1)) hmono hle'
    exact h
  have hC : condExp (enlFilt p m t) (arrayMeasure N) (Zproj p m eps i j t)
      =ᵐ[arrayMeasure N]
      condExp (enlFilt p m t) (arrayMeasure N) (fun U => Zpot p m eps i j U t) := by
    have h := condExp_condExp_of_le (μ := arrayMeasure N) (m₁ := enlFilt p m t)
      (m₂ := enlFilt p m t) (m₀ := (inferInstance : MeasurableSpace (Array N)))
      (f := fun U : Array N => Zpot p m eps i j U t) le_rfl hle
    exact h
  have hmid : (condExp (enlFilt p m t) (arrayMeasure N) (Zproj p m eps i j (t + 1))
        - condExp (enlFilt p m t) (arrayMeasure N) (Zproj p m eps i j t)
        + condExp (enlFilt p m t) (arrayMeasure N) (fun U => Jcorr p m eps i j U t))
      =ᵐ[arrayMeasure N]
      (condExp (enlFilt p m t) (arrayMeasure N) (fun U => Zpot p m eps i j U (t + 1))
        - condExp (enlFilt p m t) (arrayMeasure N) (fun U => Zpot p m eps i j U t)
        + condExp (enlFilt p m t) (arrayMeasure N) (fun U => Jcorr p m eps i j U t)) := by
    filter_upwards [hB, hC] with U hU1 hU2
    simp only [Pi.add_apply, Pi.sub_apply, hU1, hU2]
  exact hL.trans (hmid.trans hR.symm)

/-- **The projected ledger's compensator is the campaign's `Edrift`.**  Combining
`condExp_proj_ledger_eq` with the (unconditional) correction-drift identity
`CorrectionDrift.condExp_Cinc` through `compensator_of_correction`.  No further hypothesis: in
particular this does not assert that `Zpot` or `Qcomp` is adapted. -/
theorem condExp_proj_ledger_eq_Edrift {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m t : ℕ)
    (i j : Fin N) {eps : ℝ} (hε : 0 < eps) :
    condExp (enlFilt p m t) (arrayMeasure N)
        (fun U => Zproj p m eps i j (t + 1) U - Zproj p m eps i j t U + Jcorr p m eps i j U t)
      =ᵐ[arrayMeasure N]
      fun U => Edrift p m eps (fun r => SwarmCross.alphaFun p m r i) i j U t :=
  (condExp_proj_ledger_eq hp0 hp1 m t i j hε).trans
    (compensator_of_correction (p := p) (m := m) (i := i) (j := j) (eps := eps)
      (α := fun r => SwarmCross.alphaFun p m r i) hp0 hp1
      (fun t => integrable_Cinc hp0 hp1 m t i j (eps := eps) hε)
      (fun t => condExp_Cinc hp0 hp1 m t i j (eps := eps) hε) t)

/-! ### 4. `(Vdrift)` for the adapted projected ledger -/

/-- **The paper's `(Vdrift)` with a genuinely `F_t`-adapted `Z`.**

    `1{0 <= X_t^i <= M_t^j} - eps <= E[Zproj_{t+1} - Zproj_t + J_{t+1} | F_t]`

for `1/2 < p < 1`, `2 <= m`, `i != j`, `0 < eps`.  The static one-step drift
`Budget.paperWeight_le_condExp_discharged` together with `(Fdrift)`
(`VdriftAssembly.oneStep_drift`) gives the bound for `Edrift`; `condExp_proj_ledger_eq_Edrift`
identifies `Edrift` with the projected ledger's conditional mean.  Nothing about the static `Z`
being adapted is used, and no raw orthogonality of increments is assumed. -/
theorem proj_oneStep_Vdrift {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) {i j : Fin N} (hij : i ≠ j) {eps : ℝ} (hε : 0 < eps) (t : ℕ) :
    (fun U => SwarmOcc.occInd (fun s => (trajectory p m U s).pos i)
        (fun s => runMax p m U j s) t - eps)
      ≤ᵐ[arrayMeasure N]
      condExp (enlFilt p m t) (arrayMeasure N)
        (fun U => Zproj p m eps i j (t + 1) U - Zproj p m eps i j t U + Jcorr p m eps i j U t) := by
  have hAB : Budget.paperWeight p m t i j
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m t) (arrayMeasure N) (HpotInc p m t i j) :=
    Budget.paperWeight_le_condExp_discharged (N := N) (p := p) hp0 hp1 hm hij
  have h := oneStep_drift (p := p) (m := m) (n := t) (i := i) (j := j) (eps := eps)
    (α := fun r => SwarmCross.alphaFun p m r i) hp0 hp1 hε
    (fun U => one_half_le_alphaFun hp0 hp1 m t i U) hAB
  simpa only [Edrift] using
    h.trans_eq (condExp_proj_ledger_eq_Edrift hp0 hp1 m t i j hε).symm

/-! ### 5. The projected ledger's increments are conditionally centred -/

/-- The `t`-th increment of the paper's adapted ledger
`Z_{t+1} - Z_t + J_{t+1} - E[Z_{t+1} - Z_t + J_{t+1} | F_t]`, written in the shape the finite
sums below consume. -/
noncomputable def projInc (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (t : ℕ) (U : Array N) : ℝ :=
  (Zproj p m eps i j (t + 1) U - Zproj p m eps i j t U) + Jcorr p m eps i j U t
    - Edrift p m eps (fun r => SwarmCross.alphaFun p m r i) i j U t

/-- The paper's `Q`-process of the adapted ledger, `Q_T = sum_{t<T} (Z_{t+1}-Z_t+J_{t+1}) - E[...]`,
restricted to the projected `Z`. -/
noncomputable def Qpl (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (T : ℕ) (U : Array N) : ℝ :=
  ∑ t ∈ Finset.range T, projInc p m eps i j t U

/-- **Zero conditional mean.**  Each projected increment has `F_t`-conditional mean zero.  The
static ledger does *not* have this property (`QIncrementAdapted.not_stronglyMeasurable_ZJinc_zero`
refutes the needed strong measurability): the projection onto `F_t` is what repairs it. -/
theorem condExp_projInc_eq_zero {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m t : ℕ)
    (i j : Fin N) {eps : ℝ} (hε : 0 < eps) :
    condExp (enlFilt p m t) (arrayMeasure N) (projInc p m eps i j t)
      =ᵐ[arrayMeasure N] fun _ => (0 : ℝ) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hle : (enlFilt p m t : MeasurableSpace (Array N))
      ≤ (inferInstance : MeasurableSpace (Array N)) := (enlFilt p m).le t
  set A : Array N → ℝ := fun U =>
    (Zproj p m eps i j (t + 1) U - Zproj p m eps i j t U) + Jcorr p m eps i j U t with hA
  set B : Array N → ℝ :=
    fun U => Edrift p m eps (fun r => SwarmCross.alphaFun p m r i) i j U t with hB
  have hiA : Integrable A (arrayMeasure N) :=
    ((integrable_Zproj hp0 hp1 m i j hε (t + 1)).sub (integrable_Zproj hp0 hp1 m i j hε t)).add
      (integrable_Jcorr hp0 hp1 m t i j (eps := eps) hε)
  have hiB : Integrable B (arrayMeasure N) := integrable_Edrift hp0 hp1 m t i j (eps := eps) hε
  have hAeq : condExp (enlFilt p m t) (arrayMeasure N) A
      =ᵐ[arrayMeasure N] B := by
    have h := condExp_proj_ledger_eq_Edrift hp0 hp1 m t i j hε
    simpa only [hA, hB] using h
  have hBed : StronglyMeasurable[enlFilt p m t] B :=
    stronglyMeasurable_Edrift_enl (N := N) (p := p) hp0.le m t i j eps
  have hBeq : condExp (enlFilt p m t) (arrayMeasure N) B =ᵐ[arrayMeasure N] B :=
    Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable hle hBed hiB)
  have hsub : condExp (enlFilt p m t) (arrayMeasure N) (fun U => A U - B U)
      =ᵐ[arrayMeasure N] condExp (enlFilt p m t) (arrayMeasure N) A
        - condExp (enlFilt p m t) (arrayMeasure N) B :=
    condExp_sub hiA hiB (enlFilt p m t)
  have hfun : projInc p m eps i j t = fun U => A U - B U := rfl
  rw [hfun]
  refine hsub.trans ?_
  filter_upwards [hAeq, hBeq] with U h1 h2
  simp only [Pi.sub_apply, h1, h2, sub_self]

/-! ### 6. The paper's ledger decomposition with the adapted `Z` -/

/-- **The exact ledger algebra.**  The projected `Q` telescopes into the paper's display

    `Q_T = Z_T - Z_0 + sum_{t<T} J_{t+1} - sum_{t<T} E[...|F_t]`

with `Z = Zproj`.  This is the decomposition the occupation argument consumes; it is an identity
of real numbers, with no stochastic input. -/
theorem Qpl_eq (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (T : ℕ) (U : Array N) :
    Qpl p m eps i j T U
      = (Zproj p m eps i j T U - Zproj p m eps i j 0 U)
        + (∑ t ∈ Finset.range T, Jcorr p m eps i j U t)
        - (∑ t ∈ Finset.range T,
            Edrift p m eps (fun r => SwarmCross.alphaFun p m r i) i j U t) := by
  have h1 : Qpl p m eps i j T U
      = (∑ t ∈ Finset.range T,
          ((Zproj p m eps i j (t + 1) U - Zproj p m eps i j t U)
            + Jcorr p m eps i j U t))
        - (∑ t ∈ Finset.range T,
            Edrift p m eps (fun r => SwarmCross.alphaFun p m r i) i j U t) := by
    simp only [Qpl, projInc, Finset.sum_sub_distrib]
  rw [h1, Finset.sum_add_distrib, Finset.sum_range_sub (fun x => Zproj p m eps i j x U) T]

/-- **`(Vdrift)` in `Edrift` form for the adapted ledger.** -/
theorem proj_oneStep_Edrift {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) {i j : Fin N} (hij : i ≠ j) {eps : ℝ} (hε : 0 < eps) (t : ℕ) :
    (fun U => SwarmOcc.occInd (fun s => (trajectory p m U s).pos i)
        (fun s => runMax p m U j s) t - eps)
      ≤ᵐ[arrayMeasure N]
      fun U => Edrift p m eps (fun r => SwarmCross.alphaFun p m r i) i j U t := by
  refine (proj_oneStep_Vdrift hp0 hp1 hm hij hε t).trans_eq ?_
  exact condExp_proj_ledger_eq_Edrift hp0 hp1 m t i j hε

/-- **The paper's summed occupation ledger with an `F_T`-adapted `Z`.**

    `sum_{t<T} 1{0 <= X_t^i <= M_t^j} <= eps T + (Z_T - Z_0) + sum_{t<T} J_{t+1} - Q_T`

with `Z = Zproj` and `Q = Qpl`, for every `T`, almost surely, with no adaptation or orthogonality
hypothesis.  The remaining inputs of `(occbnd)` are therefore exactly the *upper* budget for the
adapted `Zproj` and the *lower* tail of the adapted `Qpl`. -/
theorem proj_ledger_pointwise {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) {i j : Fin N} (hij : i ≠ j) {eps : ℝ} (hε : 0 < eps) (T : ℕ) :
    ∀ᵐ U ∂(arrayMeasure N),
      (∑ t ∈ Finset.range T,
          SwarmOcc.occInd (fun s => (trajectory p m U s).pos i)
            (fun s => runMax p m U j s) t)
        ≤ eps * (T : ℝ) + (Zproj p m eps i j T U - Zproj p m eps i j 0 U)
          + (∑ t ∈ Finset.range T, Jcorr p m eps i j U t)
          - Qpl p m eps i j T U := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hstep : ∀ᵐ U ∂(arrayMeasure N), ∀ t : ℕ,
      SwarmOcc.occInd (fun s => (trajectory p m U s).pos i)
          (fun s => runMax p m U j s) t
        ≤ eps + Edrift p m eps (fun r => SwarmCross.alphaFun p m r i) i j U t := by
    rw [MeasureTheory.ae_all_iff]
    intro t
    filter_upwards [proj_oneStep_Edrift hp0 hp1 hm hij hε t] with U hU
    linarith
  filter_upwards [hstep] with U hU
  have hle : (∑ t ∈ Finset.range T,
        SwarmOcc.occInd (fun s => (trajectory p m U s).pos i)
          (fun s => runMax p m U j s) t)
      ≤ ∑ t ∈ Finset.range T,
        (eps + Edrift p m eps (fun r => SwarmCross.alphaFun p m r i) i j U t) :=
    Finset.sum_le_sum (fun t _ => hU t)
  have hsum : (∑ t ∈ Finset.range T,
        (eps + Edrift p m eps (fun r => SwarmCross.alphaFun p m r i) i j U t))
      = eps * (T : ℝ)
        + ∑ t ∈ Finset.range T,
            Edrift p m eps (fun r => SwarmCross.alphaFun p m r i) i j U t := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
  have hQ := Qpl_eq p m eps i j T U
  linarith

/-! ### 7. `Q` is a genuine martingale for the adapted ledger -/

theorem stronglyMeasurable_projInc {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m t : ℕ) (eps : ℝ)
    (i j : Fin N) : StronglyMeasurable[enlFilt p m (t + 1)] (projInc p m eps i j t) := by
  have hmono : (enlFilt p m t : MeasurableSpace (Array N)) ≤ enlFilt p m (t + 1) :=
    Filtration.mono (enlFilt p m) (Nat.le_succ t)
  have h1 : StronglyMeasurable[enlFilt p m (t + 1)] (Zproj p m eps i j (t + 1)) :=
    stronglyMeasurable_Zproj p m eps i j (t + 1)
  have h2 : StronglyMeasurable[enlFilt p m (t + 1)] (Zproj p m eps i j t) :=
    (stronglyMeasurable_Zproj p m eps i j t).mono hmono
  have h3 : StronglyMeasurable[enlFilt p m (t + 1)] (fun U : Array N => Jcorr p m eps i j U t) :=
    (measurable_Jcorr_enl_succ (N := N) (p := p) hp m t i j eps).stronglyMeasurable
  have h4 : StronglyMeasurable[enlFilt p m (t + 1)]
      (fun U : Array N => Edrift p m eps (fun r => SwarmCross.alphaFun p m r i) i j U t) :=
    (stronglyMeasurable_Edrift_enl (N := N) (p := p) hp m t i j eps).mono hmono
  show StronglyMeasurable[enlFilt p m (t + 1)] (fun U : Array N => projInc p m eps i j t U)
  exact ((h1.sub h2).add h3).sub h4

theorem stronglyMeasurable_Qpl {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m : ℕ) (eps : ℝ) (i j : Fin N)
    (T : ℕ) : StronglyMeasurable[enlFilt p m T] (Qpl p m eps i j T) := by
  induction T with
  | zero =>
      have h0 : Qpl p m eps i j 0 = fun _ : Array N => (0 : ℝ) := by
        funext U
        simp only [Qpl, Finset.range_zero, Finset.sum_empty]
      rw [h0]
      exact stronglyMeasurable_const
  | succ T ih =>
      have hsplit : Qpl p m eps i j (T + 1)
          = Qpl p m eps i j T + projInc p m eps i j T := by
        funext U
        simp only [Qpl, Finset.sum_range_succ, Pi.add_apply]
      rw [hsplit]
      exact (ih.mono (Filtration.mono (enlFilt p m) (Nat.le_succ T))).add
        (stronglyMeasurable_projInc hp m T eps i j)

theorem integrable_projInc {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m t : ℕ)
    (i j : Fin N) {eps : ℝ} (hε : 0 < eps) :
    Integrable (projInc p m eps i j t) (arrayMeasure N) :=
  ((integrable_Zproj hp0 hp1 m i j hε (t + 1)).sub (integrable_Zproj hp0 hp1 m i j hε t)).add
    (integrable_Jcorr hp0 hp1 m t i j (eps := eps) hε) |>.sub (integrable_Edrift hp0 hp1 m t i j
      (eps := eps) hε)

theorem integrable_Qpl {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) (eps : ℝ)
    (i j : Fin N) (hε : 0 < eps) (T : ℕ) :
    Integrable (Qpl p m eps i j T) (arrayMeasure N) :=
  integrable_finsetSum (Finset.range T) (fun t _ => integrable_projInc hp0 hp1 m t i j hε)

/-- **`Q` is a martingale.**  For the adapted projected ledger, the paper's `Q` is a genuine
martingale for `enlFilt p m`, with no adaptedness hypothesis, no raw orthogonality, and no
terminal-defect budget.  Its increments are `projInc t`, which are `F_{t+1}`-strongly measurable
and have zero `F_t`-conditional mean. -/
theorem martingale_Qpl {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) {i j : Fin N}
    {eps : ℝ} (hε : 0 < eps) :
    Martingale (fun T (U : Array N) => Qpl p m eps i j T U) (enlFilt p m) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  refine martingale_nat (f := fun T (U : Array N) => Qpl p m eps i j T U) ?_ ?_ ?_
  · intro T
    exact stronglyMeasurable_Qpl hp0.le m eps i j T
  · intro T
    exact integrable_Qpl hp0 hp1 m eps i j hε T
  · intro T
    have hsplit : (fun U : Array N => Qpl p m eps i j (T + 1) U)
        = (fun U : Array N => Qpl p m eps i j T U) + projInc p m eps i j T := by
      funext U
      simp only [Qpl, Finset.sum_range_succ, projInc, Pi.add_apply]
    rw [hsplit]
    have hQT : Integrable (fun U : Array N => Qpl p m eps i j T U) (arrayMeasure N) :=
      integrable_Qpl hp0 hp1 m eps i j hε T
    have hIT : Integrable (projInc p m eps i j T) (arrayMeasure N) :=
      integrable_projInc hp0 hp1 m T i j hε
    have hsm : StronglyMeasurable[enlFilt p m T] (fun U : Array N => Qpl p m eps i j T U) :=
      stronglyMeasurable_Qpl hp0.le m eps i j T
    have hone : condExp (enlFilt p m T) (arrayMeasure N)
        ((fun U : Array N => Qpl p m eps i j T U) + projInc p m eps i j T)
        =ᵐ[arrayMeasure N] fun U : Array N => Qpl p m eps i j T U := by
      refine (condExp_add hQT hIT (enlFilt p m T)).trans ?_
      have hQeq : condExp (enlFilt p m T) (arrayMeasure N)
            (fun U : Array N => Qpl p m eps i j T U)
          =ᵐ[arrayMeasure N] fun U : Array N => Qpl p m eps i j T U :=
        Filter.EventuallyEq.of_eq
          (condExp_of_stronglyMeasurable ((enlFilt p m).le T) hsm hQT)
      filter_upwards [hQeq, condExp_projInc_eq_zero hp0 hp1 m T i j hε] with U h1 h2
      simp only [Pi.add_apply, h1, h2, add_zero]
    exact hone.symm

end ProjLedger
end Swarming.Enl
