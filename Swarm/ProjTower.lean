/-  The paper's projected potential is `H_{j,n}(y) = E[H_j(y) | F_n]` (`Swarming.Enl.projH`).
  `ProjHRecord` proves the two record closed forms (above/below the record) and the
  *no-advance* increment identity; the advancing case is recorded there as open because the
  fresh mark at the new record is not revealed at time `n`.  `ProjLedger` sidesteps the
  question for the martingale `Q` by *centring the ledger increment by construction*.

  This file closes the filtration side without any advancing-record analysis at all, by
  conditioning at the site held at time `n`:

  * `condExp_comp_finite_range` — conditioning a site-parametrised family at a measurable
    site of finite range: `E[F_{φ(ω)}(ω) | m] = E[F_y|m]` read at `y = φ(ω)`.  This is the
    only place where a record-case analysis could enter, and it does not: the identity is
    pure σ-algebra.
  * `condExp_projH_succ_fixed` — the sitewise tower `E[H_{j,n+1}(y)|F_n] = H_{j,n}(y)`.
  * `condExp_projH_succ_at_site` / `_at_pos` — the same at any `F_n`-measurable `ℤ`-site of
    finite range, in particular at the walker's own position `X_n^i`.
  * `condExp_projH_pos_increment_eq_slice` — **the drift reduction**: the `F_n`-conditional
    mean of the two-time increment `H_{j,n+1}(X_{n+1}) - H_{j,n}(X_n)` equals the
    `F_n`-conditional mean of the *within-slice* increment at time `n+1`,
    `H_{j,n+1}(X_{n+1}) - H_{j,n+1}(X_n)`.  Hence the record-advance issue drops out of the
    one-step drift: the two-time object is a martingale increment plus a one-slice
    difference.  This is what `ProjHRecord.projH_increment_no_advance` cannot see.

  No proof holes, no custom axiom; only `propext`, `Classical.choice`, `Quot.sound`.
-/
import Swarm.ProjHRecord

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-! ## 0. A general σ-algebra lemma: conditioning at a finite-range site -/

namespace SwarmCondPiece

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Conditioning at a finite-range measurable site.**

For a family `F : ℤ → Ω → ℝ` with `E[F y | m] =ᵐ G y` for every `y` in a finite set `S`, and an
`m`-measurable site `φ` taking values in `S`, the conditional expectation of the picked member
`ω ↦ F (φ ω) ω` is `ω ↦ G (φ ω) ω`.  No countable-summability or domination hypothesis is
needed because `S` is finite. -/
theorem condExp_comp_finite_range {m : MeasurableSpace Ω} (hm : m ≤ m0)
    {φ : Ω → ℤ} (hφ : Measurable[m] φ) {S : Finset ℤ} (hS : ∀ ω, φ ω ∈ S)
    {F : ℤ → Ω → ℝ} (hF : ∀ y ∈ S, Integrable (F y) μ)
    {G : ℤ → Ω → ℝ} (hG : ∀ y ∈ S, μ[F y | m] =ᵐ[μ] G y) :
    μ[(fun ω => F (φ ω) ω) | m] =ᵐ[μ] fun ω => G (φ ω) ω := by
  classical
  have hA : ∀ y : ℤ, MeasurableSet[m] {ω | φ ω = y} := fun y =>
    hφ (measurableSet_singleton y)
  have hpoint : ∀ H : ℤ → Ω → ℝ, (∑ y ∈ S, {ω | φ ω = y}.indicator (H y))
      = fun ω => H (φ ω) ω := by
    intro H
    funext ω
    rw [Finset.sum_apply, Finset.sum_eq_single (φ ω)]
    · exact Set.indicator_of_mem (s := {ω' | φ ω' = φ ω}) (by simp) (H (φ ω))
    · intro y _ hy
      exact Set.indicator_of_notMem (s := {ω' | φ ω' = y}) (fun h => hy h.symm) (H y)
    · intro h
      exact absurd (hS ω) h
  rw [← hpoint F, ← hpoint G]
  refine (condExp_finsetSum (fun y hy => (hF y hy).indicator (hm _ (hA y))) m).trans ?_
  refine MartingaleLimit.finset_ae_sum_congr fun y hy => ?_
  refine (condExp_indicator (hF y hy) (hA y)).trans ?_
  filter_upwards [hG y hy] with ω hω
  by_cases h : φ ω = y
  · simp only [Set.indicator_of_mem, Set.mem_ofPred_eq, h, hω]
  · simp only [Set.indicator_of_notMem, Set.mem_ofPred_eq, h, not_false_eq_true]

end SwarmCondPiece

/-! ## 1. The projected potential is a martingale in the enlarged filtration -/

namespace Swarming.Enl.ProjTower

open Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross

variable {N : ℕ}

/-- **The sitewise tower.**  For a fixed site `y`, `H_{j,·}(y)` is a martingale relative to the
enlarged filtration: `E[H_{j,n+1}(y) | F_n] = H_{j,n}(y)`. -/
theorem condExp_projH_succ_fixed {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hpne : p ≠ 0) (m n : ℕ) (j : Fin N) (y : ℤ) :
    condExp (enlFilt p m n) (arrayMeasure N) (fun U => projH p m j (n + 1) U y)
      =ᵐ[arrayMeasure N] fun U => projH p m j n U y := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hmono : (enlFilt p m n : MeasurableSpace (Array N)) ≤ enlFilt p m (n + 1) :=
    Filtration.mono (enlFilt p m) (Nat.le_succ n)
  have ht := condExp_condExp_of_le (μ := arrayMeasure N) (m₁ := enlFilt p m n)
    (m₂ := enlFilt p m (n + 1)) (m₀ := (inferInstance : MeasurableSpace (Array N)))
    (f := fun V : Array N => SwarmOcc.Hpot (siteH p m j V) y) hmono ((enlFilt p m).le (n + 1))
  simpa only [projH] using ht

/-- **The tower at a finite-range adapted site.**  For any `F_n`-measurable `ℤ`-valued site `φ`
with finite range (e.g. the walker's own position at time `n`), the projection one step ahead
read at `φ` has conditional mean the projection at `φ`:

`E[H_{j,n+1}(φ)|F_n] = H_{j,n}(φ)`.

Nothing is assumed about the record at time `n+1`; in particular this covers the advancing
case `M^j_{n+1} > M^j_n` that `ProjHRecord` leaves open for fixed sites above the record. -/
theorem condExp_projH_succ_at_site {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hpne : p ≠ 0) (m n : ℕ) (j : Fin N) {φ : Array N → ℤ}
    (hφ : Measurable[enlFilt p m n] φ) {S : Finset ℤ} (hS : ∀ U, φ U ∈ S) :
    condExp (enlFilt p m n) (arrayMeasure N) (fun U => projH p m j (n + 1) U (φ U))
      =ᵐ[arrayMeasure N] fun U => projH p m j n U (φ U) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  refine SwarmCondPiece.condExp_comp_finite_range ((enlFilt (N := N) p m).le n) hφ hS
    (F := fun y V => projH p m j (n + 1) V y) ?_ (G := fun y V => projH p m j n V y) ?_
  · intro y _
    exact integrable_condExp
  · intro y _
    exact condExp_projH_succ_fixed hp0 hp1 hpne m n j y

/-- **The tower at the walker's own position.**  This is `condExp_projH_succ_at_site` at
`φ = X_n^i`, whose range is contained in `[-n, n]`. -/
theorem condExp_projH_succ_at_pos {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hpne : p ≠ 0) (m n : ℕ) (i j : Fin N) :
    condExp (enlFilt p m n) (arrayMeasure N)
        (fun U => projH p m j (n + 1) U ((trajectory p m U n).pos i))
      =ᵐ[arrayMeasure N] fun U => projH p m j n U ((trajectory p m U n).pos i) := by
  have hφ : Measurable[enlFilt p m n] (fun U : Array N => (trajectory p m U n).pos i) :=
    enl_pos_measurable p m n le_rfl i
  refine condExp_projH_succ_at_site hp0 hp1 hpne m n j hφ
    (S := Finset.Icc (-(n : ℤ)) n) ?_
  intro U
  rw [Finset.mem_Icc]
  exact abs_le.mp (ZBudget.abs_pos_le_time p m U i n)

/-! ## 2. Integrability of the projection read at the walker's position -/

/-- Ambient measurability of `H_{j,t}` read at the position held at an earlier time `n`. -/
theorem measurable_projH_at_prev_pos (p : ℝ) (m t n : ℕ) (j : Fin N) (i : Fin N) :
    Measurable (fun U : Array N => projH p m j t U ((trajectory p m U n).pos i)) := by
  refine SwarmIID.measurable_of_countable_pieces (ι := ℤ)
    (U := fun y : ℤ => fun U : Array N => projH p m j t U y) (fun y => ?_)
    (fun U => (trajectory p m U n).pos i) (fun y => ?_)
  · exact (stronglyMeasurable_projH p m j t y).mono ((enlFilt p m).le t) |>.measurable
  · exact (enl_pos_measurable p m n le_rfl i).mono ((enlFilt p m).le n) le_rfl
      (measurableSet_singleton y)

/-- `H_{j,t}(X_t^i)` is integrable: it is bounded by a deterministic constant. -/
theorem integrable_projH_pos_at {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hpne : p ≠ 0) (m t : ℕ) (i j : Fin N) :
    Integrable (fun U : Array N => projH p m j t U ((trajectory p m U t).pos i))
      (arrayMeasure N) := by
  have hbdd : ∀ᵐ U ∂(arrayMeasure N),
      |projH p m j t U ((trajectory p m U t).pos i)|
        ≤ (t : ℝ) + (t : ℝ) * (2 * (t : ℝ) + 3) :=
    ae_abs_projH_pos_le hp0 hp1 hpne m j t i
  exact integrable_of_abs_le
    ((stronglyMeasurable_projH_pos p m j t i).mono ((enlFilt p m).le t)) hbdd

/-- **The projection one step ahead read at the position held at time `n` is integrable.** -/
theorem integrable_projH_succ_at_prev_pos {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hpne : p ≠ 0) (m n : ℕ) (i j : Fin N) :
    Integrable (fun U : Array N =>
      projH p m j (n + 1) U ((trajectory p m U n).pos i)) (arrayMeasure N) := by
  have hbdd : ∀ᵐ U ∂(arrayMeasure N),
      |projH p m j (n + 1) U ((trajectory p m U n).pos i)|
        ≤ (n : ℝ) + (n : ℝ) * (2 * (n : ℝ) + 3) := by
    have hall : ∀ᵐ U ∂(arrayMeasure N), ∀ y : ℤ, |projH p m j (n + 1) U y| ≤ hbnd y := by
      rw [MeasureTheory.ae_all_iff]
      intro y
      exact abs_projH_le hp0 hp1 hpne m j (n + 1) y
    filter_upwards [hall] with U hU
    exact le_trans (hU _) (hbnd_le_of_abs_le (ZBudget.abs_pos_le_time p m U i n))
  exact integrable_of_abs_le
    (measurable_projH_at_prev_pos p m (n + 1) n j i).stronglyMeasurable hbdd

/-- **The two-time projected increment is integrable.** -/
theorem integrable_projH_pos_increment {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hpne : p ≠ 0) (m n : ℕ) (i j : Fin N) :
    Integrable (fun U : Array N =>
      projH p m j (n + 1) U ((trajectory p m U (n + 1)).pos i)
        - projH p m j n U ((trajectory p m U n).pos i)) (arrayMeasure N) :=
  (integrable_projH_pos_at hp0 hp1 hpne m (n + 1) i j).sub
    (integrable_projH_pos_at hp0 hp1 hpne m n i j)

/-- **The one-slice projected increment at time `n+1` is integrable.** -/
theorem integrable_projH_prev_pos_increment {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hpne : p ≠ 0) (m n : ℕ) (i j : Fin N) :
    Integrable (fun U : Array N =>
      projH p m j (n + 1) U ((trajectory p m U (n + 1)).pos i)
        - projH p m j (n + 1) U ((trajectory p m U n).pos i)) (arrayMeasure N) :=
  (integrable_projH_pos_at hp0 hp1 hpne m (n + 1) i j).sub
    (integrable_projH_succ_at_prev_pos hp0 hp1 hpne m n i j)

/-! ## 3. The drift reduction: two-time increment vs. one-slice increment -/

/-- **The relative tower, closed: the drift of the projected potential does not see the record
advance.**

The `F_n`-conditional mean of the two-time increment `H_{j,n+1}(X_{n+1}^i) - H_{j,n}(X_n^i)`
equals the `F_n`-conditional mean of the *within-slice* increment at time `n+1`,
`H_{j,n+1}(X_{n+1}^i) - H_{j,n+1}(X_n^i)`.

Reason: by `condExp_projH_succ_at_pos` the projection one step ahead, read at the position
*held* at time `n`, is itself a martingale increment, so subtracting it from the two-time
increment changes nothing in conditional mean.  Consequently the paper's projected drift
`(Zloss)`/`Edrift` can be computed at the single time slice `n+1`, where both sites carry the
*same* record `M^j_{n+1}`: the comparison `M^j_{n+1}` vs `M^j_n` never enters. -/
theorem condExp_projH_pos_increment_eq_slice {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hpne : p ≠ 0) (m n : ℕ) (i j : Fin N) :
    condExp (enlFilt p m n) (arrayMeasure N)
        (fun U : Array N =>
          projH p m j (n + 1) U ((trajectory p m U (n + 1)).pos i)
            - projH p m j n U ((trajectory p m U n).pos i))
      =ᵐ[arrayMeasure N]
    condExp (enlFilt p m n) (arrayMeasure N)
        (fun U : Array N =>
          projH p m j (n + 1) U ((trajectory p m U (n + 1)).pos i)
            - projH p m j (n + 1) U ((trajectory p m U n).pos i)) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hIntA : Integrable (fun U : Array N =>
      projH p m j (n + 1) U ((trajectory p m U (n + 1)).pos i)) (arrayMeasure N) :=
    integrable_projH_pos_at hp0 hp1 hpne m (n + 1) i j
  have hIntB : Integrable (fun U : Array N =>
      projH p m j n U ((trajectory p m U n).pos i)) (arrayMeasure N) :=
    integrable_projH_pos_at hp0 hp1 hpne m n i j
  have hIntC : Integrable (fun U : Array N =>
      projH p m j (n + 1) U ((trajectory p m U n).pos i)) (arrayMeasure N) :=
    integrable_projH_succ_at_prev_pos hp0 hp1 hpne m n i j
  have h1 := condExp_sub hIntA hIntB (enlFilt p m n)
  have h2 := condExp_sub hIntA hIntC (enlFilt p m n)
  have hB : condExp (enlFilt p m n) (arrayMeasure N)
      (fun U : Array N => projH p m j n U ((trajectory p m U n).pos i))
      =ᵐ[arrayMeasure N] fun U : Array N =>
        projH p m j n U ((trajectory p m U n).pos i) :=
    Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable ((enlFilt (N := N) p m).le n)
      (stronglyMeasurable_projH_pos p m j n i) hIntB)
  have hC : condExp (enlFilt p m n) (arrayMeasure N)
      (fun U : Array N => projH p m j (n + 1) U ((trajectory p m U n).pos i))
      =ᵐ[arrayMeasure N] fun U : Array N =>
        projH p m j n U ((trajectory p m U n).pos i) :=
    condExp_projH_succ_at_pos hp0 hp1 hpne m n i j
  have hleft : condExp (enlFilt p m n) (arrayMeasure N)
        (fun U : Array N =>
          projH p m j (n + 1) U ((trajectory p m U (n + 1)).pos i)
            - projH p m j n U ((trajectory p m U n).pos i))
      =ᵐ[arrayMeasure N] fun U : Array N =>
        condExp (enlFilt p m n) (arrayMeasure N)
            (fun V : Array N => projH p m j (n + 1) V ((trajectory p m V (n + 1)).pos i)) U
          - projH p m j n U ((trajectory p m U n).pos i) :=
    h1.trans ((Filter.EventuallyEq.refl _ _).sub hB)
  have hright : condExp (enlFilt p m n) (arrayMeasure N)
        (fun U : Array N =>
          projH p m j (n + 1) U ((trajectory p m U (n + 1)).pos i)
            - projH p m j (n + 1) U ((trajectory p m U n).pos i))
      =ᵐ[arrayMeasure N] fun U : Array N =>
        condExp (enlFilt p m n) (arrayMeasure N)
            (fun V : Array N => projH p m j (n + 1) V ((trajectory p m V (n + 1)).pos i)) U
          - projH p m j n U ((trajectory p m U n).pos i) :=
    h2.trans ((Filter.EventuallyEq.refl _ _).sub hC)
  exact hleft.trans hright.symm


/-! ## 4. The advancing-record case: the exact projected increment when the record catches up

`ProjHRecord.abs_projH_increment_no_advance_le` bounds the increment only when the record does
not move.  Here is the exact formula for the orthogonal case `M^j_{n+1} ≥ y > M^j_n` — the
record advancing past the site.  Then `projH_{n+1}(y)` is the *revealed* quenched value
(`projH_eq_Hpot_of_le_record`) and the increment is the revealed finite block of marks above
the old record, minus the linear and geometric terms of the time-`n` closed form.  Fresh-mark
independence is never used: precisely because the new record has reached `y`, every mark in the
sum is revealed at time `n+1`. -/

/-- **Exact projected increment in the advancing case `M^j_n < y ≤ M^j_{n+1}`.**

For a site `y` placed `g` above the time-`n` record, if the record at time `n+1` has caught up
to `y`, then

`H_{j,n+1}(y) - H_{j,n}(y) = ∑_{k<g} h_j(M^j_n + k) - g L - (e_0 - L)(1-a^g)/(1-a)`,

with `L = (1+a)/(1-a)` and `e_0 = E[h_j(M^j_n)|F_n]`.  The sum is over the marks strictly
below `M^j_{n+1}`, hence revealed.  (When `g ≥ 1` the hypothesis `y ≤ M^j_{n+1}` forces the
advance `M^j_n < M^j_{n+1}`; for `g = 0` it is the trivial `y = M^j_n` case.) -/
theorem projH_increment_advance_of_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m : ℕ) {n : ℕ} (j : Fin N) (y : ℤ) (g : ℕ) :
    ∀ᵐ U ∂(arrayMeasure N),
      y = recVal j (prefOf p m n U) + (g : ℤ) →
      y ≤ recVal j (prefOf p m (n + 1) U) →
      projH p m j (n + 1) U y - projH p m j n U y
        = (∑ k ∈ Finset.range g, SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
              ((recVal j (prefOf p m n U)).toNat + k))
          - (g : ℝ) * ((1 + aRec p m) / (1 - aRec p m))
          - (eRec p m n j 0 U - (1 + aRec p m) / (1 - aRec p m))
              * ((1 - aRec p m ^ g) / (1 - aRec p m)) := by
  have hpne : p ≠ 0 := by linarith
  filter_upwards [ae_forall_projH_closed_form (p := p) hp1 hp2 m (n := n) j,
    projH_eq_Hpot_of_le_record (p := p) hp1 hp2 hpne m (n + 1) j y] with U hcl hbelow
  intro hy hle
  have h1 := hcl y g hy
  have h2 := hbelow hle
  have h3 : SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m n U) + (g : ℤ))
      = SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m n U))
        + ∑ k ∈ Finset.range g, SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
            ((recVal j (prefOf p m n U)).toNat + k) :=
    Hpot_record_add p m n j g U
  rw [h2, h1, hy, h3]
  ring


/-! ## 5. Composition with the projected ledger `Zproj`

`Zproj_{t+1} - Zproj_t + J_{t+1} = (H_{j,t+1}(X^t_{t+1}) - H_{j,t}(X_t)) - dF_t` on the nose
(`ProjLedger.Zproj_add_J`).  Composing with the drift reduction above identifies the potential
part of the ledger's `F_t`-conditional drift with the **one-slice** increment: no record-advance
analysis enters `Edrift`.  The correction part is left as an explicit conditional expectation
(it is not `F_t`-measurable, since `X_{t+1}` enters), which is exactly where the deterministic
`bRec`-bounds (`VdriftAssembly.abs_Fcorr_bRec_le`) apply. -/

/-- The correction-term increment at the *new* position is integrable. -/
theorem integrable_Fcorr_gap_succ {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m n : ℕ) (i j : Fin N) {eps : ℝ} (hε : 0 < eps) :
    Integrable (fun U : Array N => SwarmOcc.Fcorr (aRec p m) eps (bRec p m n j U)
      ((trajectory p m U (n + 1)).pos i - runMax p m U j n)) (arrayMeasure N) := by
  have hbdd : ∀ᵐ U ∂(arrayMeasure N), |SwarmOcc.Fcorr (aRec p m) eps (bRec p m n j U)
      ((trajectory p m U (n + 1)).pos i - runMax p m U j n)|
      ≤ (2 * (n : ℝ) + 5) ^ 2 / (eps * (1 - aRec p m) ^ 2) :=
    Filter.Eventually.of_forall fun U =>
      VdriftAssembly.abs_Fcorr_bRec_le hp0 hp1 m n j hε U _
  have hφ : Measurable[enlFilt p m (n + 1)]
      (fun U : Array N => (trajectory p m U (n + 1)).pos i - runMax p m U j n) :=
    (enl_pos_measurable p m (n + 1) le_rfl i).sub
      ((VdriftAssembly.measurable_runMax_enl p m n j).mono
        (Filtration.mono (enlFilt p m) (Nat.le_succ n)) le_rfl)
  have hmeas := measurable_Fcorr_gap_mono hp0.le (Nat.le_succ n) j (aRec p m) eps hφ
  exact integrable_of_abs_le
    ((hmeas.mono ((enlFilt p m).le (n + 1)) le_rfl).stronglyMeasurable) hbdd

/-- The correction-term increment at the *old* position is integrable. -/
theorem integrable_Fcorr_gap_prev {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m n : ℕ) (i j : Fin N) {eps : ℝ} (hε : 0 < eps) :
    Integrable (fun U : Array N => SwarmOcc.Fcorr (aRec p m) eps (bRec p m n j U)
      ((trajectory p m U n).pos i - runMax p m U j n)) (arrayMeasure N) := by
  have hbdd : ∀ᵐ U ∂(arrayMeasure N), |SwarmOcc.Fcorr (aRec p m) eps (bRec p m n j U)
      ((trajectory p m U n).pos i - runMax p m U j n)|
      ≤ (2 * (n : ℝ) + 5) ^ 2 / (eps * (1 - aRec p m) ^ 2) :=
    Filter.Eventually.of_forall fun U =>
      VdriftAssembly.abs_Fcorr_bRec_le hp0 hp1 m n j hε U _
  have hφ : Measurable[enlFilt p m n]
      (fun U : Array N => (trajectory p m U n).pos i - runMax p m U j n) :=
    (enl_pos_measurable p m n le_rfl i).sub (VdriftAssembly.measurable_runMax_enl p m n j)
  have hmeas := measurable_Fcorr_gap_mono hp0.le (le_refl n) j (aRec p m) eps hφ
  exact integrable_of_abs_le
    ((hmeas.mono ((enlFilt p m).le n) le_rfl).stronglyMeasurable) hbdd

/-- **The `F_n`-conditional drift of the projected ledger has a one-slice potential part.**

`E[Z_{t+1} - Z_t + J_{t+1} | F_t]` is the `F_t`-conditional mean of the *one-slice* potential
increment at time `t+1` minus the `F_t`-conditional mean of the correction increment.  In
particular the potential contribution to `Edrift` is governed by the paper's `(Zloss)` term at
a single time slice, and the two-time object `H_{j,t+1}(X_{t+1}) - H_{j,t}(X_t)` — the only
place where the record could advance — is not needed. -/
theorem condExp_ZJincProj_eq_slice {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hpne : p ≠ 0) (m : ℕ) {eps : ℝ} (hε : 0 < eps) (n : ℕ) (i j : Fin N) :
    condExp (enlFilt p m n) (arrayMeasure N) (fun U => ZJincProj p m eps i j U n)
      =ᵐ[arrayMeasure N]
      (condExp (enlFilt p m n) (arrayMeasure N)
          (fun U : Array N =>
            projH p m j (n + 1) U ((trajectory p m U (n + 1)).pos i)
              - projH p m j (n + 1) U ((trajectory p m U n).pos i))
        - condExp (enlFilt p m n) (arrayMeasure N)
          (fun U : Array N =>
            SwarmOcc.Fcorr (aRec p m) eps (bRec p m n j U)
                ((trajectory p m U (n + 1)).pos i - runMax p m U j n)
              - SwarmOcc.Fcorr (aRec p m) eps (bRec p m n j U)
                ((trajectory p m U n).pos i - runMax p m U j n))) := by
  have hpt : (fun U : Array N => ZJincProj p m eps i j U n)
      = (fun U : Array N =>
          (projH p m j (n + 1) U ((trajectory p m U (n + 1)).pos i)
              - projH p m j n U ((trajectory p m U n).pos i))
            - (SwarmOcc.Fcorr (aRec p m) eps (bRec p m n j U)
                ((trajectory p m U (n + 1)).pos i - runMax p m U j n)
              - SwarmOcc.Fcorr (aRec p m) eps (bRec p m n j U)
                ((trajectory p m U n).pos i - runMax p m U j n))) := by
    funext U
    simp only [ZJincProj, Zproj_add_J]
  rw [hpt]
  have hIntT : Integrable (fun U : Array N =>
      projH p m j (n + 1) U ((trajectory p m U (n + 1)).pos i)
        - projH p m j n U ((trajectory p m U n).pos i)) (arrayMeasure N) :=
    integrable_projH_pos_increment hp0 hp1 hpne m n i j
  have hIntF : Integrable (fun U : Array N =>
      SwarmOcc.Fcorr (aRec p m) eps (bRec p m n j U)
          ((trajectory p m U (n + 1)).pos i - runMax p m U j n)
        - SwarmOcc.Fcorr (aRec p m) eps (bRec p m n j U)
          ((trajectory p m U n).pos i - runMax p m U j n)) (arrayMeasure N) :=
    (integrable_Fcorr_gap_succ hp0 hp1 m n i j hε).sub
      (integrable_Fcorr_gap_prev hp0 hp1 m n i j hε)
  refine (condExp_sub hIntT hIntF (enlFilt p m n)).trans ?_
  exact (condExp_projH_pos_increment_eq_slice hp0 hp1 hpne m n i j).sub
    (Filter.EventuallyEq.refl _ _)


/-- **Exact projected increment in the advancing case, site still above the new record.**

For a site `y` placed `g` above the time-`n` record, when the record advances by exactly `d`
(with `d ≤ g`) so that `y` is still `g - d` above the new record, the two closed forms of
`ProjHRecord` apply at the *same* site with the two records and give

`H_{j,n+1}(y) - H_{j,n}(y)
   = ∑_{k<d} h_j(M^j_n + k) - d L
     + (e_{n+1} - L)(1-a^{g-d})/(1-a) - (e_0 - L)(1-a^g)/(1-a)`,

where `e_{n+1} = E[h_j(M^j_{n+1})|F_{n+1}]` and `e_0 = E[h_j(M^j_n)|F_n]`.  The revealed block
`∑_{k<d} h_j(M^j_n+k)` is `F_{n+1}`-measurable; `e_{n+1}` is the genuine fresh-mark term (the
only place where `FreshBlock`/`RecSeed` is needed).  Together with
`projH_increment_advance_of_le` this covers both `g ≤ d` and `g ≥ d`, i.e. every advancing
configuration, and with the accepted `abs_projH_increment_no_advance_le` every case at a fixed
site. -/
theorem projH_increment_advance_above {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m : ℕ) {n : ℕ} (j : Fin N) (y : ℤ) (g d : ℕ) :
    ∀ᵐ U ∂(arrayMeasure N),
      y = recVal j (prefOf p m n U) + (g : ℤ) →
      recVal j (prefOf p m (n + 1) U) = recVal j (prefOf p m n U) + (d : ℤ) →
      d ≤ g →
      projH p m j (n + 1) U y - projH p m j n U y
        = (∑ k ∈ Finset.range d, SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
              ((recVal j (prefOf p m n U)).toNat + k))
          - (d : ℝ) * ((1 + aRec p m) / (1 - aRec p m))
          + (eRec p m (n + 1) j 0 U - (1 + aRec p m) / (1 - aRec p m))
              * ((1 - aRec p m ^ (g - d)) / (1 - aRec p m))
          - (eRec p m n j 0 U - (1 + aRec p m) / (1 - aRec p m))
              * ((1 - aRec p m ^ g) / (1 - aRec p m)) := by
  filter_upwards [ae_forall_projH_closed_form (p := p) hp1 hp2 m (n := n) j,
    ae_forall_projH_closed_form (p := p) hp1 hp2 m (n := n + 1) j] with U hcln hcln1
  intro hy hd hgd
  have h1 := hcln y g hy
  have hcastZ : ((g - d : ℕ) : ℤ) = (g : ℤ) - (d : ℤ) := by
    have hle : (d : ℤ) ≤ (g : ℤ) := by exact_mod_cast hgd
    omega
  have hy' : y = recVal j (prefOf p m (n + 1) U) + ((g - d : ℕ) : ℤ) := by
    rw [hy, hd, hcastZ]
    ring
  have h2 := hcln1 y (g - d) hy'
  have hadd : SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m (n + 1) U))
      = SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m n U))
        + ∑ k ∈ Finset.range d, SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
            ((recVal j (prefOf p m n U)).toNat + k) := by
    rw [hd]
    exact Hpot_record_add p m n j d U
  rw [h2, h1, hadd, Nat.cast_sub hgd]
  ring

end Swarming.Enl.ProjTower


