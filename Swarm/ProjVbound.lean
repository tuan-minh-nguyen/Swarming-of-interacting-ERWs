/-
  **The projected `(Vbound)` `hZ`, proved.**

  The occupation assembly of `ProjectedBudget` consumes a single remaining hypothesis, the
  paper's projected upper `Z` budget

      hZ :  Z_n <= A * M_n^i + n/64      eventually in n, almost surely,

  for the *adapted* ledger `ProjLedger.Zproj` (`= E[Zpot_n | F_n]`, `ProjOptionalLedger`).

  This file proves it, with `A = targetParam p m + 1 = (1+a)/(1-a) + 1`, by the paper's own
  argument, which is a *pointwise* bound and therefore needs no martingale estimate:

  * `projH_pos_le_linear`: the projected potential at the walker's own position is bounded by
    the linear spatial profile plus the record cost,
        H_{j,n}(X_n^i) <= (L+1) max 0 X_n^i + sum_{x<R} h_j(x) + b_n/(1-a).
    The two cases are `X_n^i <= r_n` (the value is revealed, `projH_eq_Hpot_of_le_record`) and
    `X_n^i > r_n` (the paper's `(projH)` closed form, `projH_pos_above_le`); in the second one
    `r_n < X_n^i`, which makes `(K - L) r_n + L X_n^i <= K X_n^i` with `K = L + 1`.
  * `Zproj_budget_ae`: `Z_n = H_{j,n}(X_n^i) - F_{b_n}(X_n^i - r_n)` and `-F_b <= b^2/(eps(1-a)^2)`
    (`Fcorr_abs_le`), `b_n = O(log n)` (`bRec_eventually_le`, from `(Kmom)`), so
    `log^2 n = o(n)` absorbs everything into `n/64`.

  Consequently `hZ_projected` (the literal premise of `ProjectedBudget`) is unconditional, and
  the N-uniform occupation front `projected_occ_uniform` and the N-uniform positive speed
  `projected_speed_uniform` follow with no hypothesis at all.

  Axioms: only `propext`, `Classical.choice`, `Quot.sound`.
-/
import Swarm.ProjectedBudget
import Swarm.ProjHRecord
import Swarm.ProjHSpatial
import Swarm.ProjLedgerBridge

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology

namespace Swarming.Enl
namespace ProjVbound

open Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross

variable {N : ℕ}

/-! ## 1. The projected potential at the walker's own position -/

/-- The profile constant `K = (1+a)/(1-a) + 1` of the paper's `(Vbound)`. -/
noncomputable def vCoef (p : ℝ) (m : ℕ) : ℝ := SwarmSpatial.targetParam p m + 1

theorem vCoef_eq (p : ℝ) (m : ℕ) :
    vCoef p m = (1 + aRec p m) / (1 - aRec p m) + 1 := rfl

theorem vCoef_nonneg {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) :
    0 ≤ vCoef p m := by
  have h0 : (0 : ℝ) ≤ aRec p m := zero_le_aRec hp1 hp2 m
  have h1 : (0 : ℝ) < 1 - aRec p m := one_sub_aRec_pos hp1 hp2 m
  have : (0 : ℝ) ≤ (1 + aRec p m) / (1 - aRec p m) := by positivity
  rw [vCoef_eq]; linarith

/-- The spatial profile of the `j`-th row of the array, as a site function. -/
noncomputable def rowProfile (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) : ℕ → ℝ :=
  fun x => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x

theorem siteH_eq_rowProfile (p : ℝ) (m : ℕ) (j : Fin N) (U : Array N) :
    siteH p m j U = rowProfile p m U j := rfl

/-- **The paper's `(Vbound)` potential display at the walker's own position.**

Almost surely, with a *spatial onset* `R₀` that does not depend on the time `n`:

    H_{j,n}(X_n^i) <= K max 0 X_n^i + sum_{x<R₀} h_j(x) + b_n/(1-a),   K = (1+a)/(1-a) + 1.

The proof is the paper's: below the record the projection is revealed, above it the paper's
`(projH)` closed form gives the drift slope `(1+a)/(1-a)` and the record cost, and the spatial
average `(spav)` turns the quenched record value `H_j(r_n)` into `K r_n + O(1)`. -/
theorem projH_pos_le_linear {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (i j : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N), ∃ R₀ : ℕ, ∀ n : ℕ,
      projH p m j n U ((trajectory p m U n).pos i)
        ≤ vCoef p m * max 0 ((trajectory p m U n).pos i : ℝ)
          + (∑ x ∈ Finset.range R₀, rowProfile p m U j x)
          + bRec p m n j U / (1 - aRec p m) := by
  have hpne : p ≠ 0 := by linarith
  have hbelow : ∀ᵐ U ∂(arrayMeasure N), ∀ n : ℕ, ∀ y : ℤ,
      y ≤ recVal j (prefOf p m n U) → projH p m j n U y = SwarmOcc.Hpot (siteH p m j U) y :=
    MeasureTheory.ae_all_iff.mpr fun n =>
      ae_forall_projH_eq_Hpot_of_le_record (p := p) hp1 hp2 hpne m n j
  have habove : ∀ᵐ U ∂(arrayMeasure N), ∀ n : ℕ,
      recVal j (prefOf p m n U) < (trajectory p m U n).pos i →
        projH p m j n U ((trajectory p m U n).pos i)
          ≤ SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m n U))
            + (((trajectory p m U n).pos i - recVal j (prefOf p m n U) : ℤ) : ℝ)
                * ((1 + aRec p m) / (1 - aRec p m))
            + bRec p m n j U / (1 - aRec p m) :=
    MeasureTheory.ae_all_iff.mpr fun n => projH_pos_above_le (p := p) hp1 hp2 m (n := n) i j
  filter_upwards [ZBudget.exists_linear_bound_array (N := N) hp1 hp2 hm (j := j),
    hbelow, habove] with U hlin hbl hab
  obtain ⟨R₀, hR₀⟩ := hlin
  have hpos : ∀ x : ℕ, 0 ≤ rowProfile p m U j x :=
    fun x => le_trans zero_le_one (SwarmMarks.one_le_hof hp1.le hp2 _ x)
  have hlin' : ∀ r : ℕ, R₀ ≤ r → ∑ x ∈ Finset.range r, rowProfile p m U j x
      ≤ vCoef p m * (r : ℝ) := hR₀
  have hHlin : ∀ y : ℤ, SwarmOcc.Hpot (siteH p m j U) y
      ≤ vCoef p m * max 0 (y : ℝ) + ∑ x ∈ Finset.range R₀, rowProfile p m U j x := by
    intro y
    rw [siteH_eq_rowProfile]
    exact ZBudget.Hpot_le_linear (vCoef_nonneg hp1 hp2 m) hlin' hpos y
  have hden : (0 : ℝ) < 1 - aRec p m := one_sub_aRec_pos hp1 hp2 m
  refine ⟨R₀, fun n => ?_⟩
  set X : ℤ := (trajectory p m U n).pos i with hX
  set r : ℤ := recVal j (prefOf p m n U) with hr
  set P : ℝ := ∑ x ∈ Finset.range R₀, rowProfile p m U j x with hP
  have hb0 : 0 ≤ bRec p m n j U / (1 - aRec p m) :=
    div_nonneg (by linarith [three_le_bRec hp1 hp2 m n j U]) hden.le
  by_cases hle : X ≤ r
  · rw [hbl n X hle]
    have := hHlin X
    linarith
  · have hlt : r < X := not_le.mp hle
    have h2 := hab n hlt
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := by
      have h : (0 : ℤ) ≤ r := by
        rw [hr, ← runMax_eq_recVal]
        exact zero_le_runMax p m U j n
      exact_mod_cast h
    have hX0 : (0 : ℝ) < (X : ℝ) := lt_of_le_of_lt hr0 (by exact_mod_cast hlt)
    have hrX : (r : ℝ) ≤ (X : ℝ) := by exact_mod_cast hlt.le
    have hHr := hHlin r
    rw [max_eq_right hr0] at hHr
    have hcast : ((X - r : ℤ) : ℝ) = (X : ℝ) - (r : ℝ) := by push_cast; ring
    have hmax : max 0 (X : ℝ) = (X : ℝ) := max_eq_right hX0.le
    have hkey : vCoef p m * (r : ℝ) + ((X - r : ℤ) : ℝ) * ((1 + aRec p m) / (1 - aRec p m))
        ≤ vCoef p m * max 0 (X : ℝ) := by
      rw [hmax, hcast, vCoef_eq]
      have : ((1 + aRec p m) / (1 - aRec p m) + 1) * (r : ℝ)
          + ((X : ℝ) - (r : ℝ)) * ((1 + aRec p m) / (1 - aRec p m))
          = (r : ℝ) + (X : ℝ) * ((1 + aRec p m) / (1 - aRec p m)) := by ring
      rw [this]
      nlinarith [hrX, hX0]
    calc projH p m j n U X
        ≤ SwarmOcc.Hpot (siteH p m j U) r + ((X - r : ℤ) : ℝ)
            * ((1 + aRec p m) / (1 - aRec p m)) + bRec p m n j U / (1 - aRec p m) := h2
      _ ≤ (vCoef p m * (r : ℝ) + P) + ((X - r : ℤ) : ℝ)
            * ((1 + aRec p m) / (1 - aRec p m)) + bRec p m n j U / (1 - aRec p m) := by
          linarith
      _ ≤ vCoef p m * max 0 (X : ℝ) + P + bRec p m n j U / (1 - aRec p m) := by linarith

/-! ## 2. Absorbing the record cost into `n/64` -/

/-- `b/D <= b^2/2 + 1/(2D^2)` for `b >= 0`, `D > 0`: the linear record cost is dominated by the
quadratic `(Fbounds)` cost plus a constant, so a single `log^2 = o(n)` estimate absorbs both. -/
theorem lin_le_sq {b D : ℝ} (hb : 0 ≤ b) (hD : 0 < D) :
    b / D ≤ b ^ 2 / 2 + 1 / (2 * D ^ 2) := by
  have hD2 : (0 : ℝ) < 2 * D ^ 2 := by positivity
  have h : b / D - (b ^ 2 / 2 + 1 / (2 * D ^ 2)) = -((b * D - 1) ^ 2) / (2 * D ^ 2) := by
    field_simp
    ring
  have hnn : -((b * D - 1) ^ 2) / (2 * D ^ 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith [sq_nonneg (b * D - 1)]) hD2.le
  linarith

/-- **The `(Vbound)` absorption step.**  For every constant `C >= 0` and every `B, D > 0`,

    C + (3 + c log(n+2))^2 / B + (3 + c log(n+2)) / D <= n/64      eventually.

This is `log^2 n = o(n)` with the linear record cost first folded into the quadratic one
(`lin_le_sq`). -/
theorem eventually_absorb {C c B D : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c) (hB : 0 < B) (hD : 0 < D) :
    ∀ᶠ T : ℕ in atTop,
      C + (3 + c * Real.log ((T : ℝ) + 2)) ^ 2 / B
        + (3 + c * Real.log ((T : ℝ) + 2)) / D ≤ (1 / 64) * (T : ℝ) := by
  have hB' : (0 : ℝ) < (1 / B + 1 / 2)⁻¹ := by positivity
  have hC' : (0 : ℝ) ≤ C + 1 / (2 * D ^ 2) := by
    have : (0 : ℝ) < 2 * D ^ 2 := by positivity
    have : (0 : ℝ) ≤ 1 / (2 * D ^ 2) := by positivity
    linarith
  have hmain := ZBudget.eventually_const_add_log_sq_div_le (C := C + 1 / (2 * D ^ 2))
    (c := c) (B := (1 / B + 1 / 2)⁻¹) hC' hc hB'
  filter_upwards [hmain] with T hT
  have hlog : (0 : ℝ) ≤ Real.log ((T : ℝ) + 2) := by
    apply Real.log_nonneg
    have h0 : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
    linarith
  have hs : (3 : ℝ) ≤ 3 + c * Real.log ((T : ℝ) + 2) := by
    have : (0 : ℝ) ≤ c * Real.log ((T : ℝ) + 2) := mul_nonneg hc hlog
    linarith
  have hb : (0 : ℝ) ≤ 3 + c * Real.log ((T : ℝ) + 2) := by linarith
  have hlin := lin_le_sq (b := 3 + c * Real.log ((T : ℝ) + 2)) (D := D) hb hD
  have hsq : (0 : ℝ) ≤ (3 + c * Real.log ((T : ℝ) + 2)) ^ 2 := sq_nonneg _
  have hinv : (1 / B + 1 / 2) = ((1 / B + 1 / 2)⁻¹)⁻¹ := (inv_inv _).symm
  have hrew : (3 + c * Real.log ((T : ℝ) + 2)) ^ 2 / ((1 / B + 1 / 2)⁻¹)
      = (3 + c * Real.log ((T : ℝ) + 2)) ^ 2 * (1 / B + 1 / 2) := by
    rw [div_eq_mul_inv, inv_inv]
  rw [hrew] at hT
  have hexp : (3 + c * Real.log ((T : ℝ) + 2)) ^ 2 * (1 / B + 1 / 2)
      = (3 + c * Real.log ((T : ℝ) + 2)) ^ 2 / B
        + (3 + c * Real.log ((T : ℝ) + 2)) ^ 2 / 2 := by
    rw [mul_add, mul_one_div, mul_one_div]
  rw [hexp] at hT
  have hkey : (3 + c * Real.log ((T : ℝ) + 2)) / D
      ≤ (3 + c * Real.log ((T : ℝ) + 2)) ^ 2 / 2 + 1 / (2 * D ^ 2) := hlin
  linarith

/-! ## 3. The projected budget `(Vbound)` -/

/-- **The paper's `(Vbound)` for the adapted ledger.**  Almost surely, eventually in `T`,

    Z_T = H_{j,T}(X_T^i) - F_{b_T}(X_T^i - M_T^j)
        <= ((1+a)/(1-a) + 1) M_T^i + T/64.

Nothing is projected through a conditional expectation here: the bound is proved *for the
projected ledger* from the projected potential display `projH_pos_le_linear`, exactly as in the
paper, so the per-array onset causes no loss. -/
theorem Zproj_budget_ae {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {eps : ℝ} (hε : 0 < eps) (i j : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      Swarming.Enl.Zproj p m eps i j U T
        ≤ vCoef p m * ((runMax p m U i T : ℤ) : ℝ) + (1 / 64) * (T : ℝ) := by
  obtain ⟨c, hcpos, hU2⟩ := ZBudget.exists_log_bound_array (N := N) hp1 hp2 hm (j := j)
  have hD : (0 : ℝ) < 1 - aRec p m := one_sub_aRec_pos hp1 hp2 m
  have hB : 0 < eps * (1 - aRec p m) ^ 2 := by positivity
  filter_upwards [projH_pos_le_linear (p := p) hp1 hp2 hm i j, hU2] with U hproj hlog
  obtain ⟨R₀, hR₀⟩ := hproj
  set C : ℝ := ∑ x ∈ Finset.range R₀, rowProfile p m U j x with hCdef
  have hC : 0 ≤ C :=
    Finset.sum_nonneg fun x _ => le_trans zero_le_one (SwarmMarks.one_le_hof hp1.le hp2 _ x)
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.mp
    (eventually_absorb (C := C) (c := c) (B := eps * (1 - aRec p m) ^ 2) (D := 1 - aRec p m)
      hC hcpos.le hB hD)
  obtain ⟨T₂, hT₂⟩ := Filter.eventually_atTop.mp
    (ZBudget.bRec_eventually_le (m := m) hp1 hp2 hcpos.le j U hlog)
  refine ⟨max T₁ T₂, fun T hT => ?_⟩
  have hTT₁ : T₁ ≤ T := le_trans (le_max_left _ _) hT
  have hTT₂ : T₂ ≤ T := le_trans (le_max_right _ _) hT
  set X : ℤ := (trajectory p m U T).pos i with hX
  set M : ℤ := runMax p m U i T with hM
  set b : ℝ := bRec p m T j U with hbdef
  have hb0 : 0 ≤ b := by
    have h3 := three_le_bRec hp1 hp2 m T j U
    rw [hbdef]; linarith
  -- the correction term
  have hcorr : - SwarmOcc.Fcorr (aRec p m) eps b ((X : ℤ) - runMax p m U j T)
      ≤ b ^ 2 / (eps * (1 - aRec p m) ^ 2) := by
    have h := SwarmOcc.Fcorr_abs_le (zero_le_aRec hp1 hp2 m) (aRec_lt_one hp1 hp2 m) hb0 hε
      ((X : ℤ) - runMax p m U j T)
    linarith [neg_le_of_abs_le h]
  have hZeq : Swarming.Enl.Zproj p m eps i j U T
      = projH p m j T U X - SwarmOcc.Fcorr (aRec p m) eps b ((X : ℤ) - runMax p m U j T) := by
    simp only [Swarming.Enl.Zproj, hX, hbdef]
  have hH := hR₀ T
  rw [← hX, ← hbdef] at hH
  -- logarithmic cap
  have hbcap : b ≤ 3 + c * Real.log ((T : ℝ) + 2) := hT₂ T hTT₂
  have hlog0 : (0 : ℝ) ≤ Real.log ((T : ℝ) + 2) := by
    apply Real.log_nonneg
    have h0 : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
    linarith
  have hs0 : (0 : ℝ) ≤ 3 + c * Real.log ((T : ℝ) + 2) := by
    have : (0 : ℝ) ≤ c * Real.log ((T : ℝ) + 2) := mul_nonneg hcpos.le hlog0
    linarith
  have hbsq : b ^ 2 / (eps * (1 - aRec p m) ^ 2)
      ≤ (3 + c * Real.log ((T : ℝ) + 2)) ^ 2 / (eps * (1 - aRec p m) ^ 2) := by
    apply div_le_div_of_nonneg_right _ hB.le
    nlinarith
  have hlin : b / (1 - aRec p m) ≤ (3 + c * Real.log ((T : ℝ) + 2)) / (1 - aRec p m) := by
    apply div_le_div_of_nonneg_right hbcap hD.le
  have habs := hT₁ T hTT₁
  -- the maximum over the walker's own running maximum
  have hXle : (X : ℝ) ≤ (M : ℝ) := by
    have h := Swarming.Trajectory.le_runMax p m U i T
    rw [hX, hM]
    exact_mod_cast h
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := by
    have h : (0 : ℤ) ≤ M := by rw [hM]; exact zero_le_runMax p m U i T
    exact_mod_cast h
  have hmaxle : max 0 (X : ℝ) ≤ (M : ℝ) := by
    have h0M : max 0 (M : ℝ) = (M : ℝ) := max_eq_right hM0
    rw [← h0M]
    exact max_le_max le_rfl hXle
  have hcoef : vCoef p m * max 0 (X : ℝ) ≤ vCoef p m * (M : ℝ) :=
    mul_le_mul_of_nonneg_left hmaxle (vCoef_nonneg hp1 hp2 m)
  rw [hZeq]
  linarith

/-! ## 4. The literal `hZ` premise of the occupation assembly -/

/-- **The projected `(Vbound)` in the exact shape `ProjectedBudget` consumes**: the adapted
ledger `ProjLedger.Zproj = E[Zpot_n | F_n]` obeys the paper's upper budget with the paper's
coefficient `A = (1+a)/(1-a) + 1` and `delta = 1/64`.

The bridge `Zproj_eq_optional_projection` identifies the optional projection with the paper's
`H_{j,n}(X_n^i) - F_{b_n}(X_n^i - M_n^j)`, so the pointwise budget of §3 applies verbatim. -/
theorem hZ_projected {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (i j : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      Swarming.Enl.ProjLedger.Zproj p m (1 / 64) i j T U
        ≤ vCoef p m * ((runMax p m U i T : ℤ) : ℝ) + (1 / 64) * (T : ℝ) := by
  have heq : ∀ᵐ U ∂(arrayMeasure N), ∀ T : ℕ,
      Swarming.Enl.ProjLedger.Zproj p m (1 / 64) i j T U
        = Swarming.Enl.Zproj p m (1 / 64) i j U T :=
    MeasureTheory.ae_all_iff.mpr fun T =>
      (Swarming.Enl.ProjLedgerBridge.Zproj_eq_optional_projection (p := p) hp0 hp1 (m := m) T i j
        (by norm_num : (0 : ℝ) < 1 / 64)).symm
  filter_upwards [heq, Zproj_budget_ae (p := p) hp0 hp1 hm (eps := 1 / 64)
    (by norm_num : (0 : ℝ) < 1 / 64) i j] with U he hbud
  obtain ⟨N₀, hN₀⟩ := hbud
  exact ⟨N₀, fun T hT => by rw [he T]; exact hN₀ T hT⟩

/-- The same budget at any coefficient `A >= K`, the form needed when the `Z` and `J` budgets
are merged onto a single majorant. -/
theorem hZ_projected_coef {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (i j : Fin N) {A : ℝ} (hA : vCoef p m ≤ A) :
    ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      Swarming.Enl.ProjLedger.Zproj p m (1 / 64) i j T U
        ≤ A * ((runMax p m U i T : ℤ) : ℝ) + (1 / 64) * (T : ℝ) := by
  filter_upwards [hZ_projected (N := N) hp0 hp1 hm i j] with U hU
  obtain ⟨N₀, hN₀⟩ := hU
  refine ⟨N₀, fun T hT => ?_⟩
  have hM0 : (0 : ℝ) ≤ ((runMax p m U i T : ℤ) : ℝ) := by
    have h : (0 : ℤ) ≤ runMax p m U i T := zero_le_runMax p m U i T
    exact_mod_cast h
  have := hN₀ T hT
  have h2 : vCoef p m * ((runMax p m U i T : ℤ) : ℝ) ≤ A * ((runMax p m U i T : ℤ) : ℝ) :=
    mul_le_mul_of_nonneg_right hA hM0
  linarith

/-! ## 5. The unconditional occupation front and positive speed -/

/-- **The N-uniform occupation bound, unconditionally.**  There is a constant `B` (independent of
the number of walkers) such that almost surely, for every ordered pair of distinct walkers and
eventually in `n`,

    #{t < n : 0 <= X_t^i <= M_t^j} <= (K + B) M_n^i + n/8,      K = (1+a)/(1-a) + 1.

The residual hypothesis `hZ` of `ProjectedBudget.ae_occ_uniform_of_projected_Vbound` is
discharged by `hZ_projected`. -/
theorem projected_occ_uniform {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) :
    ∃ B : ℝ, 0 < B ∧ ∀ (N : ℕ), ∀ᵐ U ∂(arrayMeasure N), ∀ i j : Fin N, i ≠ j →
      ∃ N₁ : ℕ, ∀ n ≥ N₁, SwarmOccTwo.OccOfMax p m N i j U n
        ≤ max 1 (vCoef p m + B) * ((runMax p m U i n : ℤ) : ℝ) + (1 / 8) * (n : ℝ) :=
  SwarmProjRes.ae_occ_uniform_of_projected_Vbound (p := p) hp0 hp1 hm (A := vCoef p m)
    (fun N i j _ => hZ_projected (N := N) hp0 hp1 hm i j)

/-- **Positive limiting speed for every walker, with a constant independent of `N`.**  There is
`kappa > 0`, depending only on `m` and `p`, with

    kappa <= liminf_n X_n^i / n     almost surely, for every walker i and every N.

This is the `liminf` front of the paper's Proposition `ball`; the proof here is the paper's
(after `(occbnd)`: the two indicators `1{X_t^i <= M_t^j}` and `1{X_t^j <= M_t^i}` cover up, and
`X_t^i/n <= 1`). -/
theorem projected_speed_uniform {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ), 2 ≤ N → ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
      κ ≤ liminf (fun n : ℕ => ((trajectory p m U n).pos i : ℝ) / n) atTop :=
  SwarmProjRes.ae_speed_uniform_of_projected_Vbound (p := p) hp0 hp1 hm (A := vCoef p m)
    (fun N i j _ => hZ_projected (N := N) hp0 hp1 hm i j)

/-- Non-vacuity witness: an explicit parameter point.  At `m = 2`, `p = 3/4` there is a
positive `kappa` bounding `liminf X_n^i/n` below for every walker in the actual array model. -/
theorem projected_speed_uniform_three_quarters :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ), 2 ≤ N → ∀ᵐ (U : Swarming.Uniform.Array N)
      ∂(Swarming.Uniform.arrayMeasure N), ∀ i : Fin N,
      κ ≤ liminf (fun n : ℕ => ((Swarming.Trajectory.trajectory (3 / 4) 2 U n).pos i : ℝ)
        / n) atTop :=
  projected_speed_uniform (p := 3 / 4) (by norm_num) (by norm_num) (m := 2) (by norm_num)

end ProjVbound
end Swarming.Enl

/-! ## Axiom audit -/


