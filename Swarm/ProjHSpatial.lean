/-  `ProjHAdvance` bounds the *time* increment `H_{j,n+1}(y) - H_{j,n}(y)` at a fixed site.  The
  projected ledger `Z_t = H_{j,t}(X_t^i) - F_{b_t}(X_t^i - M_t)` also moves the site by one unit
  per step, so the paper's `(Vdrift)` increment needs the *spatial* increment of `H_{j,n}` as well.
  This file proves it, in all three positions of the site relative to the record:

  * both sites at or below the record: the increment is the revealed value `h_j(y)`, bounded by
    the mark maximum `1 + qY` (`hZpot_envH_le_qY`);
  * the pair straddling the record (`y = M_n^j`): the increment is exactly `e_0^{(n)}`, bounded by
    `b_n`;
  * both sites strictly above the record: the increment is `L + (e_0 - L) a^g`, bounded by
    `b_n + 4/(1-a)`.

  Combined with `ProjHAdvance.abs_projH_increment_le`, this gives the **potential derivative along
  the walk**, `|H_{j,t+1}(X_{t+1}^i) - H_{j,t}(X_t^i)| ≤ C (1 + b_t + b_{t+1} + qY_{t+1})`, which
  is the potential half of the projected ledger's pathwise `Dinc` bound.  No proof holes, no custom
  axiom, no decision-based proof obligations.
-/
import Swarm.ProjHAdvance

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross

variable {N : ℕ}

/-- The spatial envelope constant `C = 4/(1-a) + 4`. -/
noncomputable def spaceConst (p : ℝ) (m : ℕ) : ℝ := 4 * (1 - aRec p m)⁻¹ + 4

theorem spaceConst_nonneg {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) :
    0 ≤ spaceConst p m := by
  have h : 0 < 1 - aRec p m := one_sub_aRec_pos hp1 hp2 m
  have : (0 : ℝ) < (1 - aRec p m)⁻¹ := inv_pos.mpr h
  simp only [spaceConst]; linarith

/-- **The spatial increment of the projected potential at a fixed time.**  For sites `y`, `y+1`
(with `y` below the horizon `n+1`, so that the revealed value `h_j(y)` is controlled by the mark
maximum `qY`),

    |H_{j,n}(y+1) - H_{j,n}(y)| ≤ (4/(1-a)+4)(1 + b_n) + (1 + qY_n).

The three cases are the position of `y` relative to the record `M_n^j`; the constant is explicit
and `N`-free. -/
theorem abs_projH_spatial_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) {n : ℕ}
    (j : Fin N) (y : ℤ) (hy : y ≤ (n : ℤ) + 1) :
    ∀ᵐ U ∂(arrayMeasure N),
      |projH p m j n U (y + 1) - projH p m j n U y|
        ≤ spaceConst p m * (1 + bRec p m n j U)
            + (1 + SwarmActualBudget.qY (N := N) p m n j U) := by
  filter_upwards [ae_forall_projH_closed_form (p := p) hp1 hp2 m (n := n) j,
    ae_forall_projH_eq_Hpot_of_le_record (p := p) hp1 hp2 (by linarith) m n j,
    eRec_zero_bounds_ae (p := p) hp1 hp2 m (n := n) j] with U hcl hbelow hb
  obtain ⟨he1, he2⟩ := hb
  have hK0 : 0 ≤ (1 - aRec p m)⁻¹ := le_of_lt (inv_pos.mpr (one_sub_aRec_pos hp1 hp2 m))
  have hb0 : 0 ≤ bRec p m n j U := by linarith [three_le_bRec hp1 hp2 m n j U]
  have hC0 : 0 ≤ spaceConst p m := spaceConst_nonneg hp1 hp2 m
  have hq0 : 0 ≤ SwarmActualBudget.qY (N := N) p m n j U := by
    linarith [SwarmActualBudget.one_le_qY hp1.le hp2 m n j U]
  rcases lt_trichotomy y (recVal j (prefOf p m n U)) with hlt | heq | hgt
  · -- both sites at or below the record: the revealed increment
    have hy1 : y + 1 ≤ recVal j (prefOf p m n U) := by omega
    rw [hbelow (y + 1) hy1, hbelow y (by omega)]
    have hstep := Hpot_succ_sub' (h := siteH p m j U) y
    have henv : siteH p m j U = envH p m j U := rfl
    rw [henv] at hstep ⊢
    rw [hstep]
    have hpos : 0 < hZpot (envH p m j U) y :=
      SwarmActualBudget.hZpot_envH_pos hp1.le hp2 m j U y
    rw [abs_of_pos hpos]
    have hle : hZpot (envH p m j U) y ≤ 1 + SwarmActualBudget.qY (N := N) p m n j U :=
      SwarmActualBudget.hZpot_envH_le_qY hp1.le hp2 m n j U hy
    have hprod : 0 ≤ spaceConst p m * (1 + bRec p m n j U) :=
      mul_nonneg hC0 (by linarith)
    linarith [hle, hprod]
  · -- the pair straddles the record: the increment is the projected seed
    have h1 := hcl (y + 1) 1 (by rw [heq]; push_cast; ring)
    have h0 := hcl y 0 (by rw [heq]; push_cast; ring)
    rw [h1, h0]
    have hA1 : (1 - aRec p m ^ 1) / (1 - aRec p m) = 1 := by
      rw [pow_one]
      exact div_self (ne_of_gt (one_sub_aRec_pos hp1 hp2 m))
    have hA0 : (1 - aRec p m ^ 0) / (1 - aRec p m) = 0 := by
      rw [pow_zero, sub_self, zero_div]
    rw [hA1, hA0]
    have hsimp : SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m n U))
          + ((1 : ℕ) : ℝ) * ((1 + aRec p m) / (1 - aRec p m))
          + (eRec p m n j 0 U - (1 + aRec p m) / (1 - aRec p m)) * 1
        - (SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m n U))
          + ((0 : ℕ) : ℝ) * ((1 + aRec p m) / (1 - aRec p m))
          + (eRec p m n j 0 U - (1 + aRec p m) / (1 - aRec p m)) * 0)
        = eRec p m n j 0 U := by
      push_cast; ring
    rw [hsimp, abs_of_nonneg (by linarith : (0 : ℝ) ≤ eRec p m n j 0 U)]
    have hprod : 0 ≤ spaceConst p m * (1 + bRec p m n j U) :=
      mul_nonneg hC0 (by linarith)
    have hble : bRec p m n j U ≤ spaceConst p m * (1 + bRec p m n j U) := by
      simp only [spaceConst]
      nlinarith [hb0, hK0]
    linarith [he2, hprod, hq0, hble]
  · -- both sites strictly above the record
    obtain ⟨k, hk⟩ : ∃ k : ℕ,
        y = recVal j (prefOf p m n U) + ((k + 1 : ℕ) : ℤ) := by
      refine ⟨(y - recVal j (prefOf p m n U)).toNat - 1, ?_⟩
      have hd : (0 : ℤ) < y - recVal j (prefOf p m n U) := by omega
      have hcast : (((y - recVal j (prefOf p m n U)).toNat : ℕ) : ℤ)
          = y - recVal j (prefOf p m n U) := Int.toNat_of_nonneg (le_of_lt hd)
      have hpos : 1 ≤ (y - recVal j (prefOf p m n U)).toNat := by omega
      push_cast
      omega
    have h1 := hcl y (k + 1) hk
    have h2 : y + 1 = recVal j (prefOf p m n U) + ((k + 2 : ℕ) : ℤ) := by
      rw [hk]; push_cast; ring
    have h0 := hcl (y + 1) (k + 2) h2
    rw [h0, h1]
    set L : ℝ := (1 + aRec p m) / (1 - aRec p m) with hL
    set A1 : ℝ := (1 - aRec p m ^ (k + 2)) / (1 - aRec p m) with hA1
    set A0 : ℝ := (1 - aRec p m ^ (k + 1)) / (1 - aRec p m) with hA0
    set e : ℝ := eRec p m n j 0 U with he
    have hLpos : 0 < L := by rw [hL]; exact projL_pos hp1 hp2 m
    have hLK : L ≤ 2 * (1 - aRec p m)⁻¹ := by rw [hL]; exact projL_le hp1 hp2 m
    have hcc0 : 0 ≤ aRec p m ^ (k + 1) := pow_nonneg (zero_le_aRec hp1 hp2 m) _
    have hcc1 : aRec p m ^ (k + 1) ≤ 1 :=
      pow_le_one₀ (zero_le_aRec hp1 hp2 m) (le_of_lt (aRec_lt_one hp1 hp2 m))
    have hsub : A1 - A0 = aRec p m ^ (k + 1) := by
      rw [hA1, hA0]
      exact projA_succ_sub hp1 hp2 m (k + 1)
    have hkey : (SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m n U))
          + ((k + 2 : ℕ) : ℝ) * L + (e - L) * A1)
        - (SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m n U))
          + ((k + 1 : ℕ) : ℝ) * L + (e - L) * A0)
        = L + (e - L) * (A1 - A0) := by
      push_cast; ring
    rw [hkey, hsub]
    -- bound the two pieces
    have hstep1 : |L + (e - L) * aRec p m ^ (k + 1)| ≤ L + |e - L| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos hLpos, abs_of_nonneg hcc0]
      have hmul : |e - L| * aRec p m ^ (k + 1) ≤ |e - L| * 1 :=
        mul_le_mul_of_nonneg_left hcc1 (abs_nonneg _)
      linarith
    have heabs : |e - L| ≤ bRec p m n j U + 2 * (1 - aRec p m)⁻¹ := by
      have h1 : |e| ≤ bRec p m n j U := by
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ e)]
        exact he2
      have h2 : |e - L| ≤ |e| + |L| := abs_sub _ _
      rw [abs_of_pos hLpos] at h2
      linarith
    have hL2K : L ≤ 2 * (1 - aRec p m)⁻¹ := hLK
    have hfinal : L + |e - L| ≤ spaceConst p m * (1 + bRec p m n j U) := by
      simp only [spaceConst]
      nlinarith [heabs, hLK, hb0, hK0]
    linarith [hstep1, hfinal, hq0]

/-- The spatial bound at every site at once. -/
theorem ae_forall_abs_projH_spatial_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ)
    {n : ℕ} (j : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ z : ℤ, z ≤ (n : ℤ) + 1 →
      |projH p m j n U (z + 1) - projH p m j n U z|
        ≤ spaceConst p m * (1 + bRec p m n j U)
            + (1 + SwarmActualBudget.qY (N := N) p m n j U) := by
  refine MeasureTheory.ae_all_iff.mpr fun z : ℤ => ?_
  by_cases hz : z ≤ (n : ℤ) + 1
  · filter_upwards [abs_projH_spatial_le (p := p) hp1 hp2 m (n := n) j z hz] with U hU _
    exact hU
  · filter_upwards with U hz'
    exact absurd hz' hz

/-- **The one-step potential derivative of the projected ledger.**

The projected potential evaluated at the walker's moving position changes by at most

    |H_{j,t+1}(X_{t+1}^i) - H_{j,t}(X_t^i)|
      ≤ (C_inc + C_spa)(1 + b_t + b_{t+1}) + (1 + qY_{t+1}),

i.e. the sum of the temporal envelope at the fixed site `X_t^i` and the spatial increment at time
`t+1`.  Every record case is covered; there is no per-array-event hypothesis. -/
theorem abs_projH_derivative_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ)
    {t : ℕ} (i j : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N),
      |projH p m j (t + 1) U ((trajectory p m U (t + 1)).pos i)
        - projH p m j t U ((trajectory p m U t).pos i)|
        ≤ (incConst p m + spaceConst p m) * (1 + bRec p m t j U + bRec p m (t + 1) j U)
          + (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) := by
  filter_upwards [ae_forall_abs_projH_increment_le (p := p) hp1 hp2 m (n := t) j,
    ae_forall_abs_projH_spatial_le (p := p) hp1 hp2 m (n := t + 1) j] with U htemp hspat
  have hXle : (trajectory p m U t).pos i ≤ (t : ℤ) :=
    le_trans (le_abs_self _) (ZBudget.abs_pos_le_time p m U i t)
  have hT := htemp ((trajectory p m U t).pos i)
  have hsp1 : |projH p m j (t + 1) U ((trajectory p m U t).pos i + 1)
      - projH p m j (t + 1) U ((trajectory p m U t).pos i)|
      ≤ spaceConst p m * (1 + bRec p m (t + 1) j U)
          + (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) :=
    hspat _ (by omega)
  have hsp2 : |projH p m j (t + 1) U ((trajectory p m U t).pos i)
      - projH p m j (t + 1) U ((trajectory p m U t).pos i - 1)|
      ≤ spaceConst p m * (1 + bRec p m (t + 1) j U)
          + (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) := by
    have h := hspat ((trajectory p m U t).pos i - 1) (by omega)
    rwa [show (trajectory p m U t).pos i - 1 + 1 = (trajectory p m U t).pos i from by ring] at h
  have hb0 : 0 ≤ bRec p m t j U := by linarith [three_le_bRec hp1 hp2 m t j U]
  have hb0' : 0 ≤ bRec p m (t + 1) j U := by
    linarith [three_le_bRec hp1 hp2 m (t + 1) j U]
  have hmono1 : spaceConst p m * (1 + bRec p m (t + 1) j U)
      ≤ spaceConst p m * (1 + bRec p m t j U + bRec p m (t + 1) j U) :=
    mul_le_mul_of_nonneg_left (by linarith) (spaceConst_nonneg hp1 hp2 m)
  have hmono2 : incConst p m * (1 + bRec p m t j U + bRec p m (t + 1) j U)
      ≤ (incConst p m + spaceConst p m) * (1 + bRec p m t j U + bRec p m (t + 1) j U) :=
    mul_le_mul_of_nonneg_right (by linarith [spaceConst_nonneg hp1 hp2 m]) (by linarith)
  have htri1 : ∀ z : ℤ,
      |projH p m j (t + 1) U z - projH p m j t U ((trajectory p m U t).pos i)|
        ≤ |projH p m j (t + 1) U z - projH p m j (t + 1) U ((trajectory p m U t).pos i)|
          + |projH p m j (t + 1) U ((trajectory p m U t).pos i)
            - projH p m j t U ((trajectory p m U t).pos i)| := by
    intro z
    have h := abs_add_le (projH p m j (t + 1) U z
        - projH p m j (t + 1) U ((trajectory p m U t).pos i))
      (projH p m j (t + 1) U ((trajectory p m U t).pos i)
        - projH p m j t U ((trajectory p m U t).pos i))
    have hid : (projH p m j (t + 1) U z
          - projH p m j (t + 1) U ((trajectory p m U t).pos i))
        + (projH p m j (t + 1) U ((trajectory p m U t).pos i)
          - projH p m j t U ((trajectory p m U t).pos i))
        = projH p m j (t + 1) U z - projH p m j t U ((trajectory p m U t).pos i) := by ring
    rwa [hid] at h
  rcases StepCross.pos_succ_eq_or p m U t i with hup | hdown
  · rw [hup]
    have h := htri1 ((trajectory p m U t).pos i + 1)
    linarith [h, hsp1, hT, hmono1, hmono2]
  · rw [hdown]
    have h := htri1 ((trajectory p m U t).pos i - 1)
    have habs : |projH p m j (t + 1) U ((trajectory p m U t).pos i - 1)
        - projH p m j (t + 1) U ((trajectory p m U t).pos i)|
        = |projH p m j (t + 1) U ((trajectory p m U t).pos i)
          - projH p m j (t + 1) U ((trajectory p m U t).pos i - 1)| := abs_sub_comm _ _
    rw [habs] at h
    linarith [h, hsp2, hT, hmono1, hmono2]

/-! ### The correction-function step, and the full `Vdrift` increment `Dinc` of the projected ledger -/

/-- One backward step of `F_b`: `|F_b(g-1) - F_b(g)| ≤ 2b/(1-a)`. -/
lemma abs_Fcorr_pred_le {a ε b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b) (hε : 0 < ε)
    (g : ℤ) :
    |SwarmOcc.Fcorr a ε b (g - 1) - SwarmOcc.Fcorr a ε b g| ≤ 2 * b / (1 - a) := by
  have h := SwarmOcc.Fcorr_succ_sub_abs_le ha0 ha1 hb hε (g - 1)
  rwa [show g - 1 + 1 = g from by ring, abs_sub_comm] at h

/-- **The `Vdrift` increment of the projected ledger, decomposed.**  The two `F_{b_{t+1}}` terms
cancel, leaving the projected potential difference plus a *single* step of `F_{b_t}` in the gap
`X_t^i - M_t^j` — the correction never has to be compared across a record advance. -/
theorem ZJincProj_decomp (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) (t : ℕ) :
    ZJincProj p m eps i j U t
      = (projH p m j (t + 1) U ((trajectory p m U (t + 1)).pos i)
          - projH p m j t U ((trajectory p m U t).pos i))
        + (SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
              ((trajectory p m U t).pos i - runMax p m U j t)
            - SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
              ((trajectory p m U (t + 1)).pos i - runMax p m U j t)) := by
  simp only [ZJincProj, Zproj, JcorrProj]
  ring

/-- **The pathwise `Dinc` bound of the projected ledger.**  With
`K = 2/(1-a) + 2/(1-a) + 4/(1-a) + 4` (the potential constant plus the correction step),

    |Z_{t+1} - Z_t + J_{t+1}| ≤ K (1 + b_t + b_{t+1}) + (1 + qY_{t+1}),

for every `t`, every pair `(i,j)`, every `eps > 0`, and **every record case** — no per-array event,
no conditional-independence input and no raw/projected identification.  The mark maximum `qY_{t+1}`
is the only unbounded factor, which is what the paper's `(maxmom)` estimate is for. -/
theorem abs_ZJincProj_le_qY {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) {t : ℕ}
    (i j : Fin N) {eps : ℝ} (hε : 0 < eps) :
    ∀ᵐ U ∂(arrayMeasure N),
      |ZJincProj p m eps i j U t|
        ≤ (incConst p m + spaceConst p m + 2 * (1 - aRec p m)⁻¹)
            * (1 + bRec p m t j U + bRec p m (t + 1) j U)
          + (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) := by
  filter_upwards [abs_projH_derivative_le (p := p) hp1 hp2 m (t := t) i j] with U hU
  have hstep : |SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
        ((trajectory p m U t).pos i - runMax p m U j t)
      - SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
        ((trajectory p m U (t + 1)).pos i - runMax p m U j t)|
      ≤ 2 * bRec p m t j U / (1 - aRec p m) := by
    have ha0 : 0 ≤ aRec p m := zero_le_aRec hp1 hp2 m
    have ha1 : aRec p m < 1 := aRec_lt_one hp1 hp2 m
    have hb0 : 0 ≤ bRec p m t j U := by linarith [three_le_bRec hp1 hp2 m t j U]
    rcases StepCross.pos_succ_eq_or p m U t i with h | h
    · have hg : (trajectory p m U (t + 1)).pos i - runMax p m U j t
          = ((trajectory p m U t).pos i - runMax p m U j t) + 1 := by rw [h]; ring
      rw [hg, abs_sub_comm]
      exact SwarmOcc.Fcorr_succ_sub_abs_le ha0 ha1 hb0 hε
        ((trajectory p m U t).pos i - runMax p m U j t)
    · have hg : (trajectory p m U (t + 1)).pos i - runMax p m U j t
          = ((trajectory p m U t).pos i - runMax p m U j t) - 1 := by rw [h]; ring
      rw [hg, abs_sub_comm]
      exact abs_Fcorr_pred_le ha0 ha1 hb0 hε
        ((trajectory p m U t).pos i - runMax p m U j t)
  have hstep_eq : 2 * bRec p m t j U / (1 - aRec p m)
      = 2 * bRec p m t j U * (1 - aRec p m)⁻¹ := by rw [div_eq_mul_inv]
  rw [ZJincProj_decomp]
  have hK0 : 0 ≤ (1 - aRec p m)⁻¹ := le_of_lt (inv_pos.mpr (one_sub_aRec_pos hp1 hp2 m))
  have hb0 : 0 ≤ bRec p m t j U := by linarith [three_le_bRec hp1 hp2 m t j U]
  have hb0' : 0 ≤ bRec p m (t + 1) j U := by
    linarith [three_le_bRec hp1 hp2 m (t + 1) j U]
  have hmono : 2 * (1 - aRec p m)⁻¹ * bRec p m t j U
      ≤ 2 * (1 - aRec p m)⁻¹ * (1 + bRec p m t j U + bRec p m (t + 1) j U) := by
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    linarith
  have hsum : (incConst p m + spaceConst p m) * (1 + bRec p m t j U + bRec p m (t + 1) j U)
        + 2 * (1 - aRec p m)⁻¹ * (1 + bRec p m t j U + bRec p m (t + 1) j U)
      = (incConst p m + spaceConst p m + 2 * (1 - aRec p m)⁻¹)
          * (1 + bRec p m t j U + bRec p m (t + 1) j U) := by ring
  have htri := abs_add_le
    (projH p m j (t + 1) U ((trajectory p m U (t + 1)).pos i)
      - projH p m j t U ((trajectory p m U t).pos i))
    (SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
        ((trajectory p m U t).pos i - runMax p m U j t)
      - SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
        ((trajectory p m U (t + 1)).pos i - runMax p m U j t))
  have hstep' : 2 * bRec p m t j U * (1 - aRec p m)⁻¹
      ≤ 2 * (1 - aRec p m)⁻¹ * (1 + bRec p m t j U + bRec p m (t + 1) j U) := by
    have heq : 2 * bRec p m t j U * (1 - aRec p m)⁻¹
        = 2 * (1 - aRec p m)⁻¹ * bRec p m t j U := by ring
    rw [heq]; exact hmono
  linarith [htri, hU, hstep, hstep_eq, hstep', hsum]

/-- **The `log^4` second moment of the projected ledger's `Vdrift` increment.**

    ∫ (Z_{t+1} - Z_t + J_{t+1})^2 ≤ C (log (t+2))^4,

`C` depending only on `(m, p)` (not on `N`, on `eps`, on `t`, nor on the pair `(i,j)`).  This is
the `Dinc` second-moment input of the projected ledger, obtained from the pathwise bound
`abs_ZJincProj_le_qY` and the paper's `(maxmom)` estimate for the mark maximum. -/
theorem exists_integral_sq_ZJincProj_le {p : ℝ} (hp0 : 0 < p) (hp1 : (1 : ℝ) / 2 < p)
    (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m) (i j : Fin N) {eps : ℝ} (hε : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ,
      Integrable (fun U : Array N => ZJincProj p m eps i j U t ^ 2) (arrayMeasure N) ∧
      ∫ U, ZJincProj p m eps i j U t ^ 2 ∂(arrayMeasure N)
        ≤ C * (Real.log ((t : ℝ) + 2)) ^ 4 := by
  obtain ⟨C4, hC4pos, hC4⟩ :=
    SwarmActualBudget.integrable_and_integral_qY_pow (N := N) hp0 hp1 hp2 hm 4 (by norm_num) j
  have hK0 : 0 ≤ incConst p m := le_of_lt (incConst_pos hp1 hp2 m)
  have hC0 : 0 ≤ spaceConst p m := spaceConst_nonneg hp1 hp2 m
  have hKinv : 0 ≤ (1 - aRec p m)⁻¹ := le_of_lt (inv_pos.mpr (one_sub_aRec_pos hp1 hp2 m))
  set Ktot : ℝ := 5 * (incConst p m + spaceConst p m + 2 * (1 - aRec p m)⁻¹) + 1 with hKtot
  have hKtot0 : 0 ≤ Ktot := by rw [hKtot]; linarith
  have hKtotpos : 0 < Ktot := by rw [hKtot]; linarith
  refine ⟨Ktot ^ 2 * 16 * C4,
    mul_pos (mul_pos (pow_pos hKtotpos 2) (by norm_num)) hC4pos, fun t => ?_⟩
  obtain ⟨hint4, hb4⟩ := hC4 (t + 1)
  have hb4' : ∫ U, (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) ^ 4
      ∂(arrayMeasure N) ≤ C4 * (Real.log (((t + 1 : ℕ) : ℝ) + 2)) ^ 4 := hb4
  have hpt : ∀ᵐ U ∂(arrayMeasure N),
      ZJincProj p m eps i j U t ^ 2
        ≤ Ktot ^ 2 * (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) ^ 4 := by
    filter_upwards [abs_ZJincProj_le_qY (p := p) hp1 hp2 m (t := t) i j hε] with U hU
    have hq : 1 ≤ 1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U := by
      have := SwarmActualBudget.one_le_qY hp1.le hp2 m (t + 1) j U
      linarith
    have hb1 : bRec p m t j U ≤ SwarmActualBudget.qY (N := N) p m (t + 1) j U + 2 := by
      refine le_trans (SwarmActualBudget.bRec_le_qY_add_two hp1.le hp2 m t j U) ?_
      have := qY_le_succ p m t j U
      linarith
    have hb2 : bRec p m (t + 1) j U ≤ SwarmActualBudget.qY (N := N) p m (t + 1) j U + 2 :=
      SwarmActualBudget.bRec_le_qY_add_two hp1.le hp2 m (t + 1) j U
    have hbound : (incConst p m + spaceConst p m + 2 * (1 - aRec p m)⁻¹)
          * (1 + bRec p m t j U + bRec p m (t + 1) j U)
        + (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U)
        ≤ Ktot * (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) := by
      have hsmall : 1 + bRec p m t j U + bRec p m (t + 1) j U
          ≤ 5 * (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) := by linarith
      have hcoef0 : 0 ≤ incConst p m + spaceConst p m + 2 * (1 - aRec p m)⁻¹ := by linarith
      have hmul := mul_le_mul_of_nonneg_left hsmall hcoef0
      have hfive : (incConst p m + spaceConst p m + 2 * (1 - aRec p m)⁻¹)
            * (5 * (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U))
          = 5 * (incConst p m + spaceConst p m + 2 * (1 - aRec p m)⁻¹)
            * (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) := by ring
      have hq0 : 0 ≤ SwarmActualBudget.qY (N := N) p m (t + 1) j U := by linarith
      rw [hKtot]
      nlinarith [hmul, hfive, hcoef0, hq0]
    have hM : 0 ≤ Ktot * (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) :=
      mul_nonneg hKtot0 (by linarith)
    have hsq : ZJincProj p m eps i j U t ^ 2
        ≤ (Ktot * (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hU.trans hbound) 2
    have hq4 : (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) ^ 2
        ≤ (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) ^ 4 := by
      calc (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) ^ 2
          = (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) ^ 2 * 1 := by ring
        _ ≤ (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) ^ 2
              * (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) ^ 2 := by
            refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
            nlinarith [hq]
        _ = (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) ^ 4 := by ring
    calc ZJincProj p m eps i j U t ^ 2
        ≤ (Ktot * (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U)) ^ 2 := hsq
      _ = Ktot ^ 2 * (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) ^ 2 := by ring
      _ ≤ Ktot ^ 2 * (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) ^ 4 :=
          mul_le_mul_of_nonneg_left hq4 (by positivity)
  have hmeas : AEStronglyMeasurable (fun U : Array N => ZJincProj p m eps i j U t ^ 2)
      (arrayMeasure N) := by
    have hsm : StronglyMeasurable (fun U : Array N => ZJincProj p m eps i j U t) :=
      (stronglyMeasurable_ZJincProj hp1.le m t i j eps).mono
        ((enlFilt (N := N) p m).le (t + 1))
    exact (hsm.measurable.pow_const 2).aestronglyMeasurable
  have hmaj : Integrable (fun U : Array N =>
      Ktot ^ 2 * (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) ^ 4) (arrayMeasure N) :=
    hint4.const_mul _
  have hint : Integrable (fun U : Array N => ZJincProj p m eps i j U t ^ 2) (arrayMeasure N) := by
    refine Integrable.mono' hmaj hmeas ?_
    filter_upwards [hpt] with U hU
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hU
  refine ⟨hint, ?_⟩
  have hmono := integral_mono_ae hint hmaj hpt
  have hfactor : ∫ U, Ktot ^ 2
        * (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) ^ 4 ∂(arrayMeasure N)
      = Ktot ^ 2
        * ∫ U, (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) ^ 4 ∂(arrayMeasure N) :=
    integral_const_mul _ _
  rw [hfactor] at hmono
  have hlog : Real.log (((t + 1 : ℕ) : ℝ) + 2) ≤ 2 * Real.log ((t : ℝ) + 2) := by
    have h := log_three_le_two_mul t
    have hcast : (((t + 1 : ℕ) : ℝ) + 2) = (t : ℝ) + 3 := by push_cast; ring
    rw [hcast]
    exact h
  have hlog4 : (Real.log (((t + 1 : ℕ) : ℝ) + 2)) ^ 4 ≤ 16 * (Real.log ((t : ℝ) + 2)) ^ 4 := by
    have h4 : (Real.log (((t + 1 : ℕ) : ℝ) + 2)) ^ 4
        ≤ (2 * Real.log ((t : ℝ) + 2)) ^ 4 := by
      have h0 : (0 : ℝ) ≤ Real.log (((t + 1 : ℕ) : ℝ) + 2) := by
        refine Real.log_nonneg ?_
        push_cast
        linarith [Nat.cast_nonneg (α := ℝ) t]
      exact pow_le_pow_left₀ h0 hlog 4
    nlinarith [sq_nonneg (Real.log ((t : ℝ) + 2))]
  have hstep : Ktot ^ 2
        * ∫ U, (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) ^ 4 ∂(arrayMeasure N)
      ≤ Ktot ^ 2 * (C4 * (Real.log (((t + 1 : ℕ) : ℝ) + 2)) ^ 4) :=
    mul_le_mul_of_nonneg_left hb4' (by positivity)
  have hbound : Ktot ^ 2 * (C4 * (Real.log (((t + 1 : ℕ) : ℝ) + 2)) ^ 4)
      ≤ Ktot ^ 2 * 16 * C4 * (Real.log ((t : ℝ) + 2)) ^ 4 := by
    have := mul_le_mul_of_nonneg_left hlog4 hC4pos.le
    nlinarith [this, sq_nonneg Ktot, sq_nonneg (Real.log ((t : ℝ) + 2))]
  linarith [hmono, hstep, hbound]

/-- The `Dinc` constant `C = 5(C_inc + C_spa + 2/(1-a)) + 1`, a function of `(m,p)` only. -/
noncomputable def dincConst (p : ℝ) (m : ℕ) : ℝ :=
  5 * (incConst p m + spaceConst p m + 2 * (1 - aRec p m)⁻¹) + 1

/-- **The paper's `(Dinc)` shape, with every factor legitimate.**

    |Z_{t+1}(x) - Z_t(x) + J_{t+1}(x)| ≤ C (1 + Y_{t+1}),      Y = the mark maximum `qY`,

uniformly in `t`, in the pair `(i,j)`, in the walker count `N` and in `eps`.  The record costs are
absorbed with `b_t, b_{t+1} ≤ Y_{t+1} + 2`. -/
theorem abs_ZJincProj_le_Y {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) {t : ℕ}
    (i j : Fin N) {eps : ℝ} (hε : 0 < eps) :
    ∀ᵐ U ∂(arrayMeasure N),
      |ZJincProj p m eps i j U t|
        ≤ dincConst p m * (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) := by
  filter_upwards [abs_ZJincProj_le_qY (p := p) hp1 hp2 m (t := t) i j hε] with U hU
  have hK0 : 0 ≤ incConst p m := le_of_lt (incConst_pos hp1 hp2 m)
  have hC0 : 0 ≤ spaceConst p m := spaceConst_nonneg hp1 hp2 m
  have hKinv : 0 ≤ (1 - aRec p m)⁻¹ := le_of_lt (inv_pos.mpr (one_sub_aRec_pos hp1 hp2 m))
  have hb1 : bRec p m t j U ≤ SwarmActualBudget.qY (N := N) p m (t + 1) j U + 2 := by
    refine le_trans (SwarmActualBudget.bRec_le_qY_add_two hp1.le hp2 m t j U) ?_
    have := qY_le_succ p m t j U
    linarith
  have hb2 : bRec p m (t + 1) j U ≤ SwarmActualBudget.qY (N := N) p m (t + 1) j U + 2 :=
    SwarmActualBudget.bRec_le_qY_add_two hp1.le hp2 m (t + 1) j U
  have hq : 1 ≤ 1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U := by
    have := SwarmActualBudget.one_le_qY hp1.le hp2 m (t + 1) j U
    linarith
  have hq0 : 0 ≤ SwarmActualBudget.qY (N := N) p m (t + 1) j U := by linarith
  have hsmall : 1 + bRec p m t j U + bRec p m (t + 1) j U
      ≤ 5 * (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) := by linarith
  have hcoef0 : 0 ≤ incConst p m + spaceConst p m + 2 * (1 - aRec p m)⁻¹ := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsmall hcoef0
  have hfive : (incConst p m + spaceConst p m + 2 * (1 - aRec p m)⁻¹)
        * (5 * (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U))
      = 5 * (incConst p m + spaceConst p m + 2 * (1 - aRec p m)⁻¹)
        * (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) := by ring
  rw [dincConst]
  nlinarith [hU, hmul, hfive, hcoef0, hq0, hq]

/-! ### Axiom audit -/


