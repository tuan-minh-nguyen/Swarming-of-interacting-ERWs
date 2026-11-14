/-
# the predictable small carrier for the actual `Qpl` increments

The integrated `QplOsc` package reduces the paper's `(locmart)` for the actual projected
compensator `Qpl` to two named inputs:

* a family `G : ℕ → Set Ω` of **predictable** truncation events
  (`MeasurableSet[enlFilt p m t] (G t)`) and a level `C` with `|projInc t| ≤ C` a.e. on `G t`;
* the residual probability `μ.real {∃ t < n, U ∉ G t}`.

`QplOsc` supplies neither at the paper's scale: the only envelope it builds is the
deterministic polynomial `Denv ≍ n²/eps`, four orders of magnitude too large.

This file constructs the small carrier from the integrated projected-potential estimates and
proves the level bound.  The content is:

* `nbT` — the only part of the projected increment that is neither controlled by the record
  predecessor `h_j(M_t^j - 1)` nor by the correction potential: the spatial step of the
  projected potential `H_{j,t}` at the *current* position of walker `i`,
  `|H_{j,t}(X_t^i ± 1) - H_{j,t}(X_t^i)|`.  It is `enlFilt p m t`-measurable by construction
  (it is built from `projH`, not from quenched `h_j` values at unrevealed sites) — this is the
  point where the paper's `h_j(x)` at `x ∈ {X_t^i - 1, X_t^i}` becomes predictable.
* `zjinc_eq` — the exact projected analogue of `VdriftAssembly.Zpot_add_J`:
  `Zproj_{t+1} - Zproj_t + J_{t+1} = (H_{j,t+1}(X_{t+1}^i) - H_{j,t}(X_t^i)) - Cinc_t`.
* `ae_abs_zjinc_le_carrier` — on the predictable carrier
  `{h_j(M_t^j - 1) ≤ V} ∩ {nbT t ≤ c}` the whole pre-centring increment is bounded by
  `capB p m V + c + 2(V+2)/(1-a)`, with `capB = incConst (2V+7)` the integrated record envelope
  and the correction-price term `2(V+2)/(1-a)` from `(Fbounds)`.
* `abs_condExp_le_of_carrier` — generic: centring at `F_t` does not inflate a bound that holds
  on an `F_t`-measurable carrier (the conditional mean is pulled out of the carrier by
  `condExp_indicator`, so the off-carrier part cannot leak in).
* `ae_abs_projInc_le_carrier` — the resulting **level bound** `|projInc t| ≤ envB p m V c` on the
  carrier, i.e. a genuine `2(V+1)/(1-a)`-scale envelope instead of the polynomial `Denv`.
* `qpl_measure_max_abs_le_of_small_carrier` — the composition with
  `QplOsc.qpl_measure_max_abs_le_of_predictable_trunc_ae`, with the residual event left exactly
  as `{∃ t < n, U ∉ qplCarrier …}`.
* `qpl_measure_max_abs_le_of_small_carrier_scale` — the paper's scale `V = c = xOf L = L^{1/16}`,
  horizon `T L`, threshold `L^{3/4}`, exponent `-L^{3/8}/(36 T Kep²)`.

Not claimed: any bound on the residual probability itself (that is the `(locmax)` window event
plus the record-window containment, supplied by the integrated `WideLocMax`/`WideTotal` family),
nor `(locgroup)`, `(locmove)`, tightness, regeneration or `MainClaim`.  No `sorry`, no custom
axiom, no `native_decide`.
-/
import Swarm.QplOsc
import Swarm.SiteHMax
import Swarm.ProjHSpatial
import Swarm.WideTotal
import Swarm.QVarBound
import Swarm.ProjLedgerBridge

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

namespace QplPredEnv

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl

variable {N : ℕ}

/-! ### 1. The predictable neighbour term -/

/-- The projected-potential step at the two neighbours of walker `i`'s current position.
Everything in it is `projH p m j t` evaluated at an `enlFilt p m t`-measurable site, hence it is
itself `enlFilt p m t`-measurable: this is the predictable replacement for the paper's
"values `h_j(x)` with `x ∈ {X_n^i - 1, X_n^i}`, `x < M_n^j`". -/
noncomputable def nbT (p : ℝ) (m : ℕ) (i j : Fin N) (t : ℕ) : Array N → ℝ :=
  fun U =>
    |projH p m j t U ((trajectory p m U t).pos i + 1)
        - projH p m j t U ((trajectory p m U t).pos i)|
      + |projH p m j t U ((trajectory p m U t).pos i - 1)
        - projH p m j t U ((trajectory p m U t).pos i)|

/-- `projH` at a shifted current position is measurable at the current time. -/
theorem measurable_projH_pos_add (p : ℝ) (m : ℕ) (j : Fin N) (n : ℕ) (i : Fin N) (c : ℤ) :
    Measurable[enlFilt (N := N) p m n]
      (fun U : Array N => projH p m j n U ((trajectory p m U n).pos i + c)) := by
  letI : MeasurableSpace (Array N) := enlFilt p m n
  refine SwarmIID.measurable_of_countable_pieces
    (U := fun y : ℤ => fun U : Array N => projH p m j n U y)
    (fun y => measurable_projH_fixed p m j n y)
    (fun U => (trajectory p m U n).pos i + c) ?_
  intro y
  have h := enl_pos_measurable p m n (k := n) le_rfl i (measurableSet_singleton (y - c))
  have hset : {U : Array N | (trajectory p m U n).pos i + c = y}
      = {U : Array N | (trajectory p m U n).pos i ∈ ({y - c} : Set ℤ)} := by
    ext U
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    omega
  rw [hset]
  exact h

theorem measurable_nbT (p : ℝ) (m : ℕ) (i j : Fin N) (t : ℕ) :
    Measurable[enlFilt (N := N) p m t] (nbT (N := N) p m i j t) := by
  letI : MeasurableSpace (Array N) := enlFilt (N := N) p m t
  have h0 : Measurable (fun U : Array N => projH p m j t U ((trajectory p m U t).pos i)) := by
    have h := measurable_projH_pos_add (N := N) p m j t i 0
    have hfun : (fun U : Array N => projH p m j t U ((trajectory p m U t).pos i + (0 : ℤ)))
        = fun U : Array N => projH p m j t U ((trajectory p m U t).pos i) := by
      funext U; rw [add_zero]
    rw [hfun] at h
    exact h
  have h1 : Measurable (fun U : Array N => projH p m j t U ((trajectory p m U t).pos i + 1)) :=
    measurable_projH_pos_add (N := N) p m j t i 1
  have h2 : Measurable (fun U : Array N => projH p m j t U ((trajectory p m U t).pos i - 1)) := by
    have h := measurable_projH_pos_add (N := N) p m j t i (-1)
    have hfun : (fun U : Array N => projH p m j t U ((trajectory p m U t).pos i + (-1 : ℤ)))
        = fun U : Array N => projH p m j t U ((trajectory p m U t).pos i - 1) := by
      funext U; rw [sub_eq_add_neg]
    rw [hfun] at h
    exact h
  have hA : Measurable (fun U : Array N => |projH p m j t U ((trajectory p m U t).pos i + 1)
        - projH p m j t U ((trajectory p m U t).pos i)|) := (h1.sub h0).abs
  have hB : Measurable (fun U : Array N => |projH p m j t U ((trajectory p m U t).pos i - 1)
        - projH p m j t U ((trajectory p m U t).pos i)|) := (h2.sub h0).abs
  have hAB : Measurable (fun U : Array N => nbT (N := N) p m i j t U) := hA.add hB
  exact hAB

theorem stronglyMeasurable_nbT (p : ℝ) (m : ℕ) (i j : Fin N) (t : ℕ) :
    StronglyMeasurable[enlFilt (N := N) p m t] (nbT (N := N) p m i j t) :=
  (measurable_nbT (N := N) p m i j t).stronglyMeasurable

/-- `nbT` is nonnegative. -/
theorem nbT_nonneg (p : ℝ) (m : ℕ) (i j : Fin N) (t : ℕ) (U : Array N) :
    0 ≤ nbT (N := N) p m i j t U := by
  simp only [nbT]; positivity

/-! ### 2. The exact projected decomposition and the pre-centring envelope -/

/-- The projected analogue of `VdriftAssembly.Zpot_add_J`, almost surely: the projected `Z`
increment plus the record cost is the sum of the projected-potential step and the (negative)
correction increment at frozen record cost. -/
theorem zjinc_eq_ae {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) (i j : Fin N)
    {eps : ℝ} (hε : 0 < eps) (t : ℕ) :
    (fun U => ProjLedger.Zproj p m eps i j (t + 1) U - ProjLedger.Zproj p m eps i j t U
        + VdriftAssembly.Jcorr p m eps i j U t)
      =ᵐ[arrayMeasure N]
      fun U => (projH p m j (t + 1) U ((trajectory p m U (t + 1)).pos i)
          - projH p m j t U ((trajectory p m U t).pos i))
        - VdriftAssembly.Cinc p m eps i j U t := by
  filter_upwards [ProjLedgerBridge.Zproj_eq_optional_projection (N := N) hp0 hp1
      (m := m) (t := t + 1) (i := i) (j := j) (eps := eps) hε,
    ProjLedgerBridge.Zproj_eq_optional_projection (N := N) hp0 hp1
      (m := m) (t := t) (i := i) (j := j) (eps := eps) hε] with U h1 h2
  have h1' : ProjLedger.Zproj p m eps i j (t + 1) U
      = Swarming.Enl.Zproj p m eps i j U (t + 1) := h1.symm
  have h2' : ProjLedger.Zproj p m eps i j t U = Swarming.Enl.Zproj p m eps i j U t := h2.symm
  rw [h1', h2']
  simp only [Swarming.Enl.Zproj, VdriftAssembly.Jcorr, VdriftAssembly.Cinc]
  ring

/-- `capB` is the integrated record envelope `incConst * (2V+7)`. -/
theorem capB_eq (p : ℝ) (m : ℕ) (V : ℝ) :
    SiteHMax.capB p m V = incConst p m * (2 * V + 7) := rfl

/-- **The pre-centring increment on the predictable carrier.** -/
theorem ae_abs_zjinc_le_carrier {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m : ℕ) (i j : Fin N) {eps : ℝ} (hε : 0 < eps) (t : ℕ) {V c : ℝ} (hV : 0 ≤ V) :
    ∀ᵐ U ∂(arrayMeasure N),
      U ∈ SiteHMax.siteGood p m j V t →
      nbT (N := N) p m i j t U ≤ c →
      |ProjLedger.Zproj p m eps i j (t + 1) U - ProjLedger.Zproj p m eps i j t U
          + VdriftAssembly.Jcorr p m eps i j U t|
        ≤ SiteHMax.capB p m V + c + 2 * (V + 2) * (1 - aRec p m)⁻¹ := by
  filter_upwards [ae_forall_abs_projH_increment_le (N := N) (p := p) hp0 hp1 m (n := t) j,
    zjinc_eq_ae (N := N) hp0 hp1 m i j (eps := eps) hε t] with U htemp hzje hgood hnb
  rw [hzje]
  have hK0 : 0 ≤ (1 - aRec p m)⁻¹ := le_of_lt (inv_pos.mpr (one_sub_aRec_pos hp0 hp1 m))
  have hgood' : HprevAt p m t j U ≤ V := hgood
  have hb1 : bRec p m t j U ≤ V + 2 := by
    have h2 : bRec p m t j U = HprevAt p m t j U + 2 := rfl
    linarith
  have hb2 : bRec p m (t + 1) j U ≤ V + 4 :=
    le_trans (SiteHMax.bRec_succ_le (N := N) hp0 hp1 m t j U) (by linarith)
  -- (i) the temporal step at the site `X_{t+1}^i`
  have hA : |projH p m j (t + 1) U ((trajectory p m U (t + 1)).pos i)
      - projH p m j t U ((trajectory p m U (t + 1)).pos i)| ≤ SiteHMax.capB p m V := by
    have h := htemp ((trajectory p m U (t + 1)).pos i)
    rw [capB_eq]
    have hsum : 1 + bRec p m t j U + bRec p m (t + 1) j U ≤ 2 * V + 7 := by linarith
    have hc0 : 0 ≤ incConst p m := le_of_lt (incConst_pos hp0 hp1 m)
    calc |projH p m j (t + 1) U ((trajectory p m U (t + 1)).pos i)
          - projH p m j t U ((trajectory p m U (t + 1)).pos i)|
        ≤ incConst p m * (1 + bRec p m t j U + bRec p m (t + 1) j U) := h
      _ ≤ incConst p m * (2 * V + 7) := mul_le_mul_of_nonneg_left hsum hc0
  -- (ii) the spatial step at time `t`
  have hS : |projH p m j t U ((trajectory p m U (t + 1)).pos i)
      - projH p m j t U ((trajectory p m U t).pos i)| ≤ nbT (N := N) p m i j t U := by
    rcases SwarmQVariance.X_succ_sub_X (N := N) p m U t i with hstep | hstep
    · have hstep' : (trajectory p m U (t + 1)).pos i = (trajectory p m U t).pos i + 1 := hstep
      rw [hstep']
      simp only [nbT]
      exact le_add_of_nonneg_right (abs_nonneg _)
    · have hstep' : (trajectory p m U (t + 1)).pos i = (trajectory p m U t).pos i - 1 := hstep
      rw [hstep']
      simp only [nbT]
      exact le_add_of_nonneg_left (abs_nonneg _)
  -- (iii) the correction increment at frozen record cost
  have hC : |VdriftAssembly.Cinc p m eps i j U t| ≤ 2 * (V + 2) * (1 - aRec p m)⁻¹ := by
    have hb0 : 0 ≤ bRec p m t j U := by linarith [three_le_bRec hp0 hp1 m t j U]
    have h := SwarmOcc.Fcorr_succ_sub_abs_le (a := aRec p m) (ε := eps) (b := bRec p m t j U)
      (zero_le_aRec hp0 hp1 m) (aRec_lt_one hp0 hp1 m) hb0 hε
      ((trajectory p m U t).pos i - runMax p m U j t)
    have hgap : (trajectory p m U (t + 1)).pos i - runMax p m U j t
        = ((trajectory p m U t).pos i - runMax p m U j t) + 1
        ∨ (trajectory p m U (t + 1)).pos i - runMax p m U j t
          = ((trajectory p m U t).pos i - runMax p m U j t) - 1 := by
      rcases SwarmQVariance.X_succ_sub_X (N := N) p m U t i with hs | hs
      · left
        have hs' : (trajectory p m U (t + 1)).pos i = (trajectory p m U t).pos i + 1 := hs
        rw [hs']; ring
      · right
        have hs' : (trajectory p m U (t + 1)).pos i = (trajectory p m U t).pos i - 1 := hs
        rw [hs']; ring
    have h1 : |SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
        ((trajectory p m U (t + 1)).pos i - runMax p m U j t)
        - SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
          ((trajectory p m U t).pos i - runMax p m U j t)|
        ≤ 2 * bRec p m t j U / (1 - aRec p m) := by
      rcases hgap with hg | hg
      · rw [hg]
        simpa only [add_comm] using h
      · rw [hg]
        have h' := SwarmOcc.Fcorr_succ_sub_abs_le (a := aRec p m) (ε := eps)
          (b := bRec p m t j U) (zero_le_aRec hp0 hp1 m) (aRec_lt_one hp0 hp1 m) hb0 hε
          (((trajectory p m U t).pos i - runMax p m U j t) - 1)
        rw [show ((trajectory p m U t).pos i - runMax p m U j t) - 1 + 1
          = ((trajectory p m U t).pos i - runMax p m U j t) from by ring] at h'
        rw [abs_sub_comm]
        exact h'
    simp only [VdriftAssembly.Cinc]
    refine le_trans h1 ?_
    have h1a : 0 < 1 - aRec p m := one_sub_aRec_pos hp0 hp1 m
    have hmono : 2 * bRec p m t j U / (1 - aRec p m) ≤ 2 * (V + 2) / (1 - aRec p m) := by
      apply div_le_div_of_nonneg_right _ h1a.le
      linarith
    have heq : 2 * (V + 2) / (1 - aRec p m) = 2 * (V + 2) * (1 - aRec p m)⁻¹ := by
      rw [div_eq_mul_inv]
    linarith
  -- assemble
  have htri : |(projH p m j (t + 1) U ((trajectory p m U (t + 1)).pos i)
        - projH p m j t U ((trajectory p m U t).pos i))
      - VdriftAssembly.Cinc p m eps i j U t|
      ≤ |projH p m j (t + 1) U ((trajectory p m U (t + 1)).pos i)
          - projH p m j t U ((trajectory p m U (t + 1)).pos i)|
        + |projH p m j t U ((trajectory p m U (t + 1)).pos i)
          - projH p m j t U ((trajectory p m U t).pos i)|
        + |VdriftAssembly.Cinc p m eps i j U t| := by
    have h1 : |projH p m j (t + 1) U ((trajectory p m U (t + 1)).pos i)
          - projH p m j t U ((trajectory p m U t).pos i)|
        ≤ |projH p m j (t + 1) U ((trajectory p m U (t + 1)).pos i)
            - projH p m j t U ((trajectory p m U (t + 1)).pos i)|
          + |projH p m j t U ((trajectory p m U (t + 1)).pos i)
            - projH p m j t U ((trajectory p m U t).pos i)| := by
      have := abs_add_le (projH p m j (t + 1) U ((trajectory p m U (t + 1)).pos i)
          - projH p m j t U ((trajectory p m U (t + 1)).pos i))
        (projH p m j t U ((trajectory p m U (t + 1)).pos i)
          - projH p m j t U ((trajectory p m U t).pos i))
      have hid : (projH p m j (t + 1) U ((trajectory p m U (t + 1)).pos i)
            - projH p m j t U ((trajectory p m U (t + 1)).pos i))
          + (projH p m j t U ((trajectory p m U (t + 1)).pos i)
            - projH p m j t U ((trajectory p m U t).pos i))
          = projH p m j (t + 1) U ((trajectory p m U (t + 1)).pos i)
            - projH p m j t U ((trajectory p m U t).pos i) := by ring
      rw [hid] at this
      exact this
    calc |(projH p m j (t + 1) U ((trajectory p m U (t + 1)).pos i)
          - projH p m j t U ((trajectory p m U t).pos i))
        - VdriftAssembly.Cinc p m eps i j U t|
        ≤ |projH p m j (t + 1) U ((trajectory p m U (t + 1)).pos i)
            - projH p m j t U ((trajectory p m U t).pos i)|
          + |VdriftAssembly.Cinc p m eps i j U t| := abs_sub _ _
      _ ≤ _ := by linarith
  linarith

/-! ### 3. The carrier, the centring step, and the level bound -/

/-- The **predictable carrier** at time `t`: the record predecessor `h_j(M_t^j - 1)` is at most
`V` and the projected neighbour term is at most `c`.  Both conditions are decided by `F_t`. -/
def qplCarrier (p : ℝ) (m : ℕ) (i j : Fin N) (V c : ℝ) (t : ℕ) : Set (Array N) :=
  SiteHMax.siteGood p m j V t ∩ {U | nbT (N := N) p m i j t U ≤ c}

theorem measurableSet_qplCarrier {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m : ℕ) (i j : Fin N)
    (V c : ℝ) (t : ℕ) :
    MeasurableSet[enlFilt (N := N) p m t] (qplCarrier (N := N) p m i j V c t) := by
  have h1 := SiteHMax.measurableSet_siteGood (N := N) hp m t j V
  have h2 : MeasurableSet[enlFilt (N := N) p m t]
      {U : Array N | nbT (N := N) p m i j t U ≤ c} :=
    measurableSet_le (measurable_nbT (N := N) p m i j t) measurable_const
  exact h1.inter h2

/-- The level of the small envelope: `2 (capB + c + 2(V+2)/(1-a))`. -/
noncomputable def envB (p : ℝ) (m : ℕ) (V c : ℝ) : ℝ :=
  2 * (SiteHMax.capB p m V + c + 2 * (V + 2) * (1 - aRec p m)⁻¹)

theorem envB_pos {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) {V c : ℝ}
    (hV : 0 ≤ V) (hc : 0 ≤ c) : 0 < envB p m V c := by
  have h1 : 0 < SiteHMax.capB p m V := SiteHMax.capB_pos hp0 hp1 m hV
  have h2 : 0 ≤ 2 * (V + 2) * (1 - aRec p m)⁻¹ := by
    have := one_sub_aRec_pos hp0 hp1 m
    have : 0 < (1 - aRec p m)⁻¹ := inv_pos.mpr this
    nlinarith
  simp only [envB]; linarith

/-- **Conditional centring does not inflate a bound that holds on an `F_t`-measurable carrier.**
The carrier indicator is pulled out of the conditional expectation, so the values of `Y` off the
carrier cannot leak back into the conditional mean on the carrier. -/
theorem abs_condExp_le_of_carrier {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {ℱ : Filtration ℕ m0} {t : ℕ} {Y : Ω → ℝ} (hY : Integrable Y μ)
    {G : Set Ω} (hG : MeasurableSet[ℱ t] G) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ᵐ ω ∂μ, ω ∈ G → |Y ω| ≤ B) :
    ∀ᵐ ω ∂μ, ω ∈ G → |μ[Y | ℱ t] ω| ≤ B := by
  have hGm : MeasurableSet G := ℱ.le t G hG
  have hY' : Integrable (G.indicator Y) μ := hY.indicator hGm
  have hbdd : ∀ᵐ ω ∂μ, |(G.indicator Y) ω| ≤ B := by
    filter_upwards [hB] with ω hω
    by_cases h : ω ∈ G
    · rw [Set.indicator_of_mem h]; exact hω h
    · rw [Set.indicator_of_notMem h, abs_zero]; exact hB0
  have h1 : ∀ᵐ ω ∂μ, |μ[G.indicator Y | ℱ t] ω| ≤ B :=
    MeasureTheory.ae_bdd_abs_condExp_of_ae_bdd_abs (m := ℱ t) hbdd
  have h2 : μ[G.indicator Y | ℱ t] =ᵐ[μ] G.indicator (μ[Y | ℱ t]) :=
    MeasureTheory.condExp_indicator hY hG
  filter_upwards [h1, h2] with ω hω1 hω2 hGω
  rw [hω2, Set.indicator_of_mem hGω] at hω1
  exact hω1

/-- **The level bound on the carrier.** -/
theorem ae_abs_projInc_le_carrier {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m : ℕ) (i j : Fin N) {eps : ℝ} (hε : 0 < eps) (t : ℕ) {V c : ℝ}
    (hV : 0 ≤ V) (hc : 0 ≤ c) :
    ∀ᵐ U ∂(arrayMeasure N),
      U ∈ qplCarrier (N := N) p m i j V c t →
      |ProjLedger.projInc p m eps i j t U| ≤ envB p m V c := by
  set B : ℝ := SiteHMax.capB p m V + c + 2 * (V + 2) * (1 - aRec p m)⁻¹ with hBdef
  have hB0 : 0 ≤ B := by
    have h1 : 0 < SiteHMax.capB p m V := SiteHMax.capB_pos hp0 hp1 m hV
    have h2 : 0 ≤ 2 * (V + 2) * (1 - aRec p m)⁻¹ := by
      have h3 := one_sub_aRec_pos hp0 hp1 m
      have : 0 < (1 - aRec p m)⁻¹ := inv_pos.mpr h3
      nlinarith
    rw [hBdef]; linarith
  have hYint : Integrable (fun U : Array N =>
      ProjLedger.Zproj p m eps i j (t + 1) U - ProjLedger.Zproj p m eps i j t U
        + VdriftAssembly.Jcorr p m eps i j U t) (arrayMeasure N) :=
    ((ProjLedger.integrable_Zproj hp0 hp1 m i j hε (t + 1)).sub
      (ProjLedger.integrable_Zproj hp0 hp1 m i j hε t)).add
      (VdriftAssembly.integrable_Jcorr hp0 hp1 m t i j hε)
  have hEd : condExp (enlFilt p m t) (arrayMeasure N)
      (fun U : Array N => ProjLedger.Zproj p m eps i j (t + 1) U
        - ProjLedger.Zproj p m eps i j t U + VdriftAssembly.Jcorr p m eps i j U t)
      =ᵐ[arrayMeasure N]
      fun U => VdriftAssembly.Edrift p m eps (fun r => SwarmCross.alphaFun p m r i) i j U t :=
    ProjLedger.condExp_proj_ledger_eq_Edrift hp0 hp1 m t i j hε
  have hYb : ∀ᵐ U ∂(arrayMeasure N),
      U ∈ qplCarrier (N := N) p m i j V c t →
      |ProjLedger.Zproj p m eps i j (t + 1) U - ProjLedger.Zproj p m eps i j t U
        + VdriftAssembly.Jcorr p m eps i j U t| ≤ B := by
    filter_upwards [ae_abs_zjinc_le_carrier (N := N) hp0 hp1 m i j (eps := eps) hε t hV]
      with U hU hmem
    exact hU hmem.1 hmem.2
  have hcent := abs_condExp_le_of_carrier (μ := arrayMeasure N)
    (ℱ := enlFilt (N := N) p m) (t := t) hYint
    (measurableSet_qplCarrier (N := N) hp0.le m i j V c t) hB0 hYb
  filter_upwards [hcent, hEd, hYb] with U hcentU hEdU hYU hmem
  have hEdb : |VdriftAssembly.Edrift p m eps (fun r => SwarmCross.alphaFun p m r i) i j U t|
      ≤ B := by
    rw [← hEdU]
    exact hcentU hmem
  have hY := hYU hmem
  simp only [ProjLedger.projInc, envB]
  rw [show ProjLedger.Zproj p m eps i j (t + 1) U - ProjLedger.Zproj p m eps i j t U
      + VdriftAssembly.Jcorr p m eps i j U t
      - VdriftAssembly.Edrift p m eps (fun r => SwarmCross.alphaFun p m r i) i j U t
      = (ProjLedger.Zproj p m eps i j (t + 1) U - ProjLedger.Zproj p m eps i j t U
        + VdriftAssembly.Jcorr p m eps i j U t)
        - VdriftAssembly.Edrift p m eps (fun r => SwarmCross.alphaFun p m r i) i j U t from rfl]
  refine (abs_sub _ _).trans ?_
  rw [hBdef] at hY hEdb
  linarith

/-- **The composed maximal bound with the small carrier.** -/
theorem qpl_measure_max_abs_le_of_small_carrier {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {i j : Fin N} (hij : i ≠ j) {eps : ℝ} (hε : 0 < eps) {V c : ℝ}
    (hV : 0 ≤ V) (hc : 0 ≤ c) {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hεpos : 0 < ε) :
    (arrayMeasure N).real
        {U | ∃ k ≤ n, ε ≤ |ProjLedger.Qpl p m eps i j k U|}
      ≤ 2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * (envB p m V c) ^ 2))
        + (arrayMeasure N).real {U | ∃ t < n, U ∉ qplCarrier (N := N) p m i j V c t} :=
  QplOsc.qpl_measure_max_abs_le_of_predictable_trunc_ae (N := N) hp0 hp1 hij hε
    (G := fun t => qplCarrier (N := N) p m i j V c t)
    (fun t => measurableSet_qplCarrier (N := N) hp0.le m i j V c t)
    (envB_pos hp0 hp1 m hV hc)
    (fun t => ae_abs_projInc_le_carrier hp0 hp1 m i j hε t hV hc) hn hεpos

/-! ### 4. The envelope is `O(V+2)` and the paper-scale exponent -/

/-- The explicit constant of the small envelope: `Kep = 2(3 Cproj + 1 + 2/(1-a))`. -/
noncomputable def Kep (p : ℝ) (m : ℕ) : ℝ :=
  2 * (3 * SiteHMax.Cproj p m + 1 + 2 * (1 - aRec p m)⁻¹)

theorem Kep_pos {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) : 0 < Kep p m := by
  have h1 := one_sub_aRec_pos hp0 hp1 m
  have h2 : 0 < (1 - aRec p m)⁻¹ := inv_pos.mpr h1
  have h3 : 0 ≤ SiteHMax.Cproj p m := SiteHMax.Cproj_nonneg hp0 hp1 m
  simp only [Kep]; linarith

theorem Kep_nonneg {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) : 0 ≤ Kep p m :=
  le_of_lt (Kep_pos hp0 hp1 m)

/-- **The envelope is linear in the level.** -/
theorem envB_le_kep {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) {V : ℝ}
    (hV : 1 ≤ V) : envB p m V V ≤ Kep p m * (V + 2) := by
  have hK0 : 0 ≤ (1 - aRec p m)⁻¹ := le_of_lt (inv_pos.mpr (one_sub_aRec_pos hp0 hp1 m))
  have hC0 : 0 ≤ SiteHMax.Cproj p m := SiteHMax.Cproj_nonneg hp0 hp1 m
  have hcap : SiteHMax.capB p m V ≤ SiteHMax.Cproj p m * (3 * (V + 2)) := by
    have h27 : 2 * V + 7 ≤ 3 * (V + 2) := by linarith
    have hdef : SiteHMax.capB p m V = SiteHMax.Cproj p m * (2 * V + 7) := rfl
    rw [hdef]
    exact mul_le_mul_of_nonneg_left h27 hC0
  have hVle : V ≤ V + 2 := by linarith
  have h3 : 2 * (V + 2) * (1 - aRec p m)⁻¹ = (2 * (1 - aRec p m)⁻¹) * (V + 2) := by ring
  have hstep : SiteHMax.capB p m V + V + 2 * (V + 2) * (1 - aRec p m)⁻¹
      ≤ SiteHMax.Cproj p m * (3 * (V + 2)) + (V + 2) + (2 * (1 - aRec p m)⁻¹) * (V + 2) := by
    rw [h3]; linarith
  have hstep2 : SiteHMax.Cproj p m * (3 * (V + 2)) + (V + 2) + (2 * (1 - aRec p m)⁻¹) * (V + 2)
      = 3 * SiteHMax.Cproj p m * (V + 2) + (V + 2) + 2 * (1 - aRec p m)⁻¹ * (V + 2) := by
    ring
  rw [envB]
  calc 2 * (SiteHMax.capB p m V + V + 2 * (V + 2) * (1 - aRec p m)⁻¹)
      ≤ 2 * (SiteHMax.Cproj p m * (3 * (V + 2)) + (V + 2)
          + (2 * (1 - aRec p m)⁻¹) * (V + 2)) := by linarith
    _ = Kep p m * (V + 2) := by
        rw [Kep]; ring

/-- **The composed maximal bound with the level `Kep (V+2)`.** -/
theorem qpl_measure_max_abs_le_of_small_carrier_kep {p : ℝ} (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) {m : ℕ} {i j : Fin N} (hij : i ≠ j) {eps : ℝ} (hε : 0 < eps) {V : ℝ}
    (hV : 1 ≤ V) {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hεpos : 0 < ε) :
    (arrayMeasure N).real
        {U | ∃ k ≤ n, ε ≤ |ProjLedger.Qpl p m eps i j k U|}
      ≤ 2 * ((n : ℝ) + 1)
          * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * (Kep p m * (V + 2)) ^ 2))
        + (arrayMeasure N).real {U | ∃ t < n, U ∉ qplCarrier (N := N) p m i j V V t} := by
  have hV0 : 0 ≤ V := le_trans zero_le_one hV
  have hmain := qpl_measure_max_abs_le_of_small_carrier (N := N) (m := m) hp0 hp1 hij hε hV0 hV0 hn hεpos
  refine le_trans hmain (add_le_add ?_ le_rfl)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Real.exp_le_exp.mpr ?_
  have henv : envB p m V V ≤ Kep p m * (V + 2) := envB_le_kep hp0 hp1 m hV
  have henv0 : 0 < envB p m V V := envB_pos hp0 hp1 m hV0 hV0
  have hKp : 0 < Kep p m := Kep_pos hp0 hp1 m
  have hV2 : (0:ℝ) < V + 2 := by linarith
  have hK0 : 0 < Kep p m * (V + 2) := mul_pos hKp hV2
  have hsq : (envB p m V V) ^ 2 ≤ (Kep p m * (V + 2)) ^ 2 := by
    have h0 : (0:ℝ) ≤ envB p m V V := le_of_lt henv0
    have hle : envB p m V V ≤ Kep p m * (V + 2) := henv
    nlinarith [henv0, hK0, henv, sq_nonneg (envB p m V V - Kep p m * (V + 2))]
  have hden : 4 * (n : ℝ) * (envB p m V V) ^ 2 ≤ 4 * (n : ℝ) * (Kep p m * (V + 2)) ^ 2 := by
    have hn0 : (0:ℝ) ≤ (n : ℝ) := by positivity
    nlinarith
  have hpos1 : 0 < 4 * (n : ℝ) * (envB p m V V) ^ 2 := by
    have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    positivity
  have hpos2 : 0 < 4 * (n : ℝ) * (Kep p m * (V + 2)) ^ 2 := by
    have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    have : (0:ℝ) < (Kep p m * (V + 2)) ^ 2 := by
      have := hK0; positivity
    positivity
  have hfrac : ε ^ 2 / (4 * (n : ℝ) * (Kep p m * (V + 2)) ^ 2)
      ≤ ε ^ 2 / (4 * (n : ℝ) * (envB p m V V) ^ 2) := by
    apply div_le_div_of_nonneg_left (by positivity) hpos1 hden
  have hkey1 : -(ε ^ 2) / (4 * (n : ℝ) * (envB p m V V) ^ 2)
      = -(ε ^ 2 / (4 * (n : ℝ) * (envB p m V V) ^ 2)) := by ring
  have hkey2 : -(ε ^ 2) / (4 * (n : ℝ) * (Kep p m * (V + 2)) ^ 2)
      = -(ε ^ 2 / (4 * (n : ℝ) * (Kep p m * (V + 2)) ^ 2)) := by ring
  rw [hkey1, hkey2]
  exact neg_le_neg hfrac

/-! ### 5. The record-window scale -/

/-- **The `Qpl` maximal bound at the paper's scale** with the small predictable carrier: level
`V = xOf L = L^{1/16}`, horizon `T·L`, deviation `L^{3/4}`, and the explicit exponent
`V^8/(4 T (Kep (V+2))^2)` (which is `≥ V^6/(36 T Kep^2) = L^{3/8}/(36 T Kep^2)` for `L ≥ 1`). -/
theorem qpl_measure_max_abs_le_of_small_carrier_scale {p : ℝ} (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) {m : ℕ} {i j : Fin N} (hij : i ≠ j) {eps : ℝ} (hε : 0 < eps)
    {T L : ℕ} (hT : 1 ≤ T) (hL : 1 ≤ L) :
    (arrayMeasure N).real
        {U | ∃ k ≤ T * L, (L : ℝ) ^ (3 / 4 : ℝ) ≤ |ProjLedger.Qpl p m eps i j k U|}
      ≤ 2 * (((T * L : ℕ) : ℝ) + 1)
          * Real.exp (-((LocSumAct.xOf L) ^ 8 / (4 * (T : ℝ) * (Kep p m * (LocSumAct.xOf L + 2)) ^ 2)))
        + (arrayMeasure N).real
            {U | ∃ t < T * L, U ∉ qplCarrier (N := N) p m i j (LocSumAct.xOf L) (LocSumAct.xOf L) t} := by
  have hLr : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL)
  have hV1 : (1 : ℝ) ≤ LocSumAct.xOf L := LocSumAct.one_le_xOf hL
  have hV0 : (0 : ℝ) < LocSumAct.xOf L := lt_of_lt_of_le zero_lt_one hV1
  have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  have hK0 : 0 < Kep p m := Kep_pos hp0 hp1 m
  have hTL : 1 ≤ T * L :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hmain := qpl_measure_max_abs_le_of_small_carrier_kep (N := N) (m := m) hp0 hp1 hij hε
    (V := LocSumAct.xOf L) hV1 (n := T * L) hTL
    (ε := (L : ℝ) ^ (3 / 4 : ℝ)) (Real.rpow_pos_of_pos hLr _)
  refine le_trans hmain (add_le_add ?_ le_rfl)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Real.exp_le_exp.mpr ?_
  have hLrpow : ((L : ℝ) ^ (3 / 4 : ℝ)) = (LocSumAct.xOf L) ^ 12 :=
    (LocMoveLocal.xOf_pow_twelve L).symm
  have hcast : (((T * L : ℕ)) : ℝ) = (T : ℝ) * (L : ℝ) := by push_cast; ring
  have hVpow : (LocSumAct.xOf L) ^ 16 = (L : ℝ) := LocSumAct.xOf_pow L
  rw [hLrpow, hcast, ← hVpow]
  have hkey : -((LocSumAct.xOf L) ^ 12) ^ 2
        / (4 * ((T : ℝ) * (LocSumAct.xOf L) ^ 16) * (Kep p m * (LocSumAct.xOf L + 2)) ^ 2)
      = -((LocSumAct.xOf L) ^ 8 / (4 * (T : ℝ) * (Kep p m * (LocSumAct.xOf L + 2)) ^ 2)) := by
    have hVne : (LocSumAct.xOf L) ^ 16 ≠ 0 := by positivity
    field_simp
  rw [hkey]

end QplPredEnv
