/-
# QplCarrier residual containment: the window event implies the carrier

The accepted `QplPredEnv` reduces the projected-`Qpl` maximal bound to the residual event
`{∃ t < n, U ∉ qplCarrier p m i j V c t}`, where

  `qplCarrier t = SiteHMax.siteGood p m j V t ∩ {nbT ≤ c}`,

`siteGood t = {HprevAt t ≤ V}` (the predecessor potential at the running record) and
`nbT t = |H(X_t^i+1) - H(X_t^i)| + |H(X_t^i-1) - H(X_t^i)|` is the spatial step of the
projected potential at the walker's own position.  This file proves the **containment**:

  an explicit deterministic record-window event `qplWindow` (record of walker `j` inside
  `[A, A+M)`, walker `i` inside the same window with one site of margin, and the quenched
  environment `h_j ≤ V` on the whole window `[A-1, A+M)`)
  implies `qplCarrier` at **every** `t < K`, with the explicit envelope

  `c = 2 * (V + 2 + 2 * (1+a)/(1-a))`.
-/
import Swarm.QplPredEnv
import Swarm.ProjHSpatial
import Swarm.ProjHRecord
import Swarm.WideLocMax
import Swarm.WideTotal

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

namespace QplWindow

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl SwarmMarks SwarmLogRatio LocSumAct QplPredEnv

variable {N : ℕ}

/-! ### 1. The slope and the envelope constants -/

/-- The above-record slope `L = (1+a)/(1-a)` of the projected potential. -/
noncomputable def Lc (p : ℝ) (m : ℕ) : ℝ := (1 + aRec p m) / (1 - aRec p m)

theorem Lc_pos {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) : 0 < Lc p m :=
  projL_pos hp1 hp2 m

theorem Lc_nonneg {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) : 0 ≤ Lc p m :=
  (Lc_pos hp1 hp2 m).le

/-- The carrier level `c = 2 (V + 2 + 2 L)`. -/
noncomputable def envC (p : ℝ) (m : ℕ) (V : ℝ) : ℝ :=
  2 * (V + 2 + 2 * Lc p m)

theorem envC_nonneg {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) {V : ℝ}
    (hV : 0 ≤ V) : 0 ≤ envC p m V := by
  have hL := Lc_nonneg hp1 hp2 m
  simp only [envC]; linarith

/-! ### 2. The predecessor potential is bounded on the window -/

/-- On the record window `[A, A+M)` with `h_j ≤ V` on `[A-1, A+M)`, the predecessor value
`h_j(M_t^j - 1)` is at most `V`: this is `siteGood` at the single time `t`. -/
theorem HprevAt_le_of_window {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (j : Fin N) {A M t : ℕ} (hA : 1 ≤ A) {V : ℝ} (hV1 : 1 ≤ V) {U : Array N}
    (hrec : A ≤ (recVal j (prefOf p m t U)).toNat ∧
      (recVal j (prefOf p m t U)).toNat < A + M)
    (hh : ∀ y ∈ Finset.Ico (A - 1) (A + M), hof p (siteMarks p m U j) y ≤ V) :
    HprevAt p m t j U ≤ V := by
  rcases Nat.eq_zero_or_pos ((recVal j (prefOf p m t U)).toNat) with h0 | hpos
  · rw [HprevAt_of_zero p m t j U h0]; exact hV1
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
      (by omega : (recVal j (prefOf p m t U)).toNat ≠ 0)
    rw [HprevAt_of_succ p m t j U k hk]
    refine hh k ?_
    rw [Finset.mem_Ico]
    obtain ⟨h1, h2⟩ := hrec
    omega

/-! ### 3. The two spatial steps of the projected potential on the window -/

/-- **The `+1` spatial step at or below the record is the revealed value.**  For `y ≥ 0`,
`y ≤ r_t`, `projH` agrees with the quenched potential on both sites, so the step is exactly
`h_j(y)` and is bounded by `V` on the window. -/
theorem abs_step_below_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (j : Fin N) {t : ℕ} {U : Array N} {V : ℝ}
    (hbelow : ∀ y : ℤ, y ≤ recVal j (prefOf p m t U) →
      projH p m j t U y = SwarmOcc.Hpot (siteH p m j U) y)
    {y : ℤ} (hy0 : 0 ≤ y) (hyr : y + 1 ≤ recVal j (prefOf p m t U))
    (hval : hof p (siteMarks p m U j) y.toNat ≤ V) :
    |projH p m j t U (y + 1) - projH p m j t U y| ≤ V := by
  have hmono : 1 ≤ hof p (siteMarks p m U j) y.toNat :=
    one_le_hof hp1.le hp2 (siteMarks p m U j) y.toNat
  rw [hbelow (y + 1) hyr, hbelow y (by omega),
    Hpot_succ_sub' (h := siteH p m j U) y]
  have hz : hZpot (siteH p m j U) y = hof p (siteMarks p m U j) y.toNat := by
    rw [hZpot_of_nonneg hy0]
    rfl
  rw [hz, abs_of_nonneg (le_trans zero_le_one hmono)]
  exact hval

/-- **The `+1` spatial step at or above the record is `L + (e_0 - L) a^g`**, bounded by
`b_t + 2 L`. -/
theorem abs_step_above_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (j : Fin N) {t : ℕ} {U : Array N}
    (hcl : ∀ (y : ℤ) (g : ℕ), y = recVal j (prefOf p m t U) + (g : ℤ) →
      projH p m j t U y
        = SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m t U))
          + (g : ℝ) * ((1 + aRec p m) / (1 - aRec p m))
          + (eRec p m t j 0 U - (1 + aRec p m) / (1 - aRec p m))
              * ((1 - aRec p m ^ g) / (1 - aRec p m)))
    (he1 : 0 ≤ eRec p m t j 0 U)
    (he2 : eRec p m t j 0 U ≤ bRec p m t j U)
    {y : ℤ} (hyr : recVal j (prefOf p m t U) ≤ y) :
    |projH p m j t U (y + 1) - projH p m j t U y|
      ≤ bRec p m t j U + 2 * Lc p m := by
  obtain ⟨g, hg⟩ : ∃ g : ℕ, y = recVal j (prefOf p m t U) + (g : ℤ) :=
    ⟨(y - recVal j (prefOf p m t U)).toNat,
      by rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ y - recVal j (prefOf p m t U))]; omega⟩
  have h1 := hcl y g hg
  have h2 : y + 1 = recVal j (prefOf p m t U) + ((g + 1 : ℕ) : ℤ) := by
    rw [hg]; push_cast; ring
  have h0 := hcl (y + 1) (g + 1) h2
  rw [h0, h1]
  have hLc : Lc p m = (1 + aRec p m) / (1 - aRec p m) := rfl
  rw [hLc]
  have hsub : (1 - aRec p m ^ (g + 1)) / (1 - aRec p m)
      - (1 - aRec p m ^ g) / (1 - aRec p m) = aRec p m ^ g := projA_succ_sub hp1 hp2 m g
  have hkey : (SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m t U))
        + ((g + 1 : ℕ) : ℝ) * ((1 + aRec p m) / (1 - aRec p m))
        + (eRec p m t j 0 U - (1 + aRec p m) / (1 - aRec p m))
            * ((1 - aRec p m ^ (g + 1)) / (1 - aRec p m)))
      - (SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m t U))
        + ((g : ℕ) : ℝ) * ((1 + aRec p m) / (1 - aRec p m))
        + (eRec p m t j 0 U - (1 + aRec p m) / (1 - aRec p m))
            * ((1 - aRec p m ^ g) / (1 - aRec p m)))
      = ((1 + aRec p m) / (1 - aRec p m))
        + (eRec p m t j 0 U - (1 + aRec p m) / (1 - aRec p m))
          * ((1 - aRec p m ^ (g + 1)) / (1 - aRec p m)
              - (1 - aRec p m ^ g) / (1 - aRec p m)) := by
    push_cast; ring
  rw [hkey, hsub]
  have hLpos : 0 < (1 + aRec p m) / (1 - aRec p m) := projL_pos hp1 hp2 m
  have hpow0 : 0 ≤ aRec p m ^ g := pow_nonneg (zero_le_aRec hp1 hp2 m) g
  have hpow1 : aRec p m ^ g ≤ 1 :=
    pow_le_one₀ (zero_le_aRec hp1 hp2 m) (le_of_lt (aRec_lt_one hp1 hp2 m))
  have hstep : |(1 + aRec p m) / (1 - aRec p m)
      + (eRec p m t j 0 U - (1 + aRec p m) / (1 - aRec p m)) * aRec p m ^ g|
      ≤ (1 + aRec p m) / (1 - aRec p m)
        + |eRec p m t j 0 U - (1 + aRec p m) / (1 - aRec p m)| := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos hLpos, abs_of_nonneg hpow0]
    have hmul : |eRec p m t j 0 U - (1 + aRec p m) / (1 - aRec p m)| * aRec p m ^ g
        ≤ |eRec p m t j 0 U - (1 + aRec p m) / (1 - aRec p m)| * 1 :=
      mul_le_mul_of_nonneg_left hpow1 (abs_nonneg _)
    rw [mul_one] at hmul
    linarith
  have heabs : |eRec p m t j 0 U - (1 + aRec p m) / (1 - aRec p m)|
      ≤ bRec p m t j U + (1 + aRec p m) / (1 - aRec p m) := by
    have h1 : |eRec p m t j 0 U - (1 + aRec p m) / (1 - aRec p m)|
        ≤ |eRec p m t j 0 U| + |(1 + aRec p m) / (1 - aRec p m)| := abs_sub _ _
    have h2 : |eRec p m t j 0 U| = eRec p m t j 0 U := abs_of_nonneg he1
    have h3 : |(1 + aRec p m) / (1 - aRec p m)| = (1 + aRec p m) / (1 - aRec p m) :=
      abs_of_pos hLpos
    rw [h2, h3] at h1
    linarith
  have hbr3 : 0 ≤ bRec p m t j U := by linarith [three_le_bRec hp1 hp2 m t j U]
  linarith

/-! ### 4. The `nbT` envelope at a single time, and on the whole horizon -/

/-- **The `nbT` envelope on the record window, at a single time.**  The two spatial steps of the
projected potential at the walker's own position are, on the window, at most `V` (below the
record, where the revealed value is used), `b_t` (at the record, where the step is the projected
seed `e_0`) and `b_t + 2L` (above the record, where the step is the drift slope plus the geometric
correction).  Both are bounded by `V + 2 + 2L` once `b_t ≤ V + 2`, giving `nbT ≤ 2(V+2+2L)`. -/
theorem nbT_le_of_window_at {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} {i j : Fin N} {t : ℕ} {V : ℝ} (hV1 : 1 ≤ V) {A M : ℕ} (hA : 1 ≤ A) :
    ∀ᵐ U ∂(arrayMeasure N),
      (A ≤ (recVal j (prefOf p m t U)).toNat ∧
        (recVal j (prefOf p m t U)).toNat < A + M) →
      (∀ y ∈ Finset.Ico (A - 1) (A + M), hof p (siteMarks p m U j) y ≤ V) →
      (A ≤ ((trajectory p m U t).pos i).toNat ∧
        ((trajectory p m U t).pos i).toNat + 2 ≤ A + M) →
      nbT p m i j t U ≤ envC p m V := by
  have hpne : p ≠ 0 := by linarith
  filter_upwards [ae_forall_projH_eq_Hpot_of_le_record (N := N) (p := p) hp1 hp2 hpne m t j,
    ae_forall_projH_closed_form (N := N) (p := p) hp1 hp2 m (n := t) j,
    eRec_zero_bounds_ae (N := N) (p := p) hp1 hp2 m (n := t) j] with U hbelow hcl hb
  intro hrec hh hX
  have he1 : 0 ≤ eRec p m t j 0 U := le_trans zero_le_one hb.1
  have he2 : eRec p m t j 0 U ≤ bRec p m t j U := hb.2
  have hgood : HprevAt p m t j U ≤ V := HprevAt_le_of_window hp1 hp2 j hA hV1 hrec hh
  have hbr : bRec p m t j U ≤ V + 2 := by
    simp only [bRec]; linarith
  have hLnn : 0 ≤ Lc p m := Lc_nonneg hp1 hp2 m
  set XX : ℤ := (trajectory p m U t).pos i with hXX
  set r : ℤ := recVal j (prefOf p m t U) with hr
  -- the walker's position is a positive integer, inside the window
  have hX0 : (0 : ℤ) ≤ XX := by
    by_contra hcon
    have hz : XX.toNat = 0 := Int.toNat_of_nonpos (by omega)
    omega
  have hXn : (XX.toNat : ℤ) = XX := Int.toNat_of_nonneg hX0
  have hX1 : (1 : ℤ) ≤ XX := by
    have h1 : (A : ℤ) ≤ XX.toNat := by exact_mod_cast hX.1
    have h2 : (1 : ℤ) ≤ (A : ℤ) := by exact_mod_cast hA
    omega
  have hmem : XX.toNat ∈ Finset.Ico (A - 1) (A + M) := by
    rw [Finset.mem_Ico]
    have h1 : (A : ℤ) ≤ XX.toNat := by exact_mod_cast hX.1
    have h2 : (XX.toNat : ℤ) + 2 ≤ (A : ℤ) + (M : ℤ) := by
      exact_mod_cast hX.2
    omega
  have hmem1 : (XX - 1).toNat ∈ Finset.Ico (A - 1) (A + M) := by
    rw [Finset.mem_Ico]
    have hcast : ((XX - 1).toNat : ℤ) = ((XX.toNat : ℕ) : ℤ) - 1 := by
      rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ XX - 1)]
      omega
    have h1 : (A : ℤ) ≤ XX.toNat := by exact_mod_cast hX.1
    have h2 : (XX.toNat : ℤ) + 2 ≤ (A : ℤ) + (M : ℤ) := by
      exact_mod_cast hX.2
    omega
  have hhX : hof p (siteMarks p m U j) XX.toNat ≤ V := hh _ hmem
  have hhX1 : hof p (siteMarks p m U j) (XX - 1).toNat ≤ V := hh _ hmem1
  -- step 1: `X ↦ X + 1`
  have hstepA : |projH p m j t U (XX + 1) - projH p m j t U XX| ≤ V + 2 + 2 * Lc p m := by
    rcases lt_trichotomy XX r with hlt | heq | hgt
    · have h := abs_step_below_le hp1 hp2 (m := m) (j := j) (t := t) (U := U)
        hbelow hX0 (by omega) hhX
      linarith
    · rw [heq]
      rw [hcl (r + 1) 1 (by push_cast; ring), hcl r 0 (by push_cast; ring)]
      have hA1 : (1 - aRec p m ^ (1 : ℕ)) / (1 - aRec p m) = 1 := by
        rw [pow_one]
        exact div_self (ne_of_gt (one_sub_aRec_pos hp1 hp2 m))
      have hA0 : (1 - aRec p m ^ (0 : ℕ)) / (1 - aRec p m) = 0 := by
        rw [pow_zero, sub_self, zero_div]
      rw [hA1, hA0]
      have hsimp : (SwarmOcc.Hpot (siteH p m j U) r
            + ((1 : ℕ) : ℝ) * ((1 + aRec p m) / (1 - aRec p m))
            + (eRec p m t j 0 U - (1 + aRec p m) / (1 - aRec p m)) * 1)
          - (SwarmOcc.Hpot (siteH p m j U) r
            + ((0 : ℕ) : ℝ) * ((1 + aRec p m) / (1 - aRec p m))
            + (eRec p m t j 0 U - (1 + aRec p m) / (1 - aRec p m)) * 0)
          = eRec p m t j 0 U := by
        push_cast; ring
      rw [hsimp, abs_of_nonneg he1]
      linarith
    · have h := abs_step_above_le hp1 hp2 (m := m) (j := j) (t := t) (U := U)
        hcl he1 he2 (le_of_lt hgt)
      linarith
  -- step 2: `X - 1 ↦ X`
  have hstepB : |projH p m j t U (XX - 1) - projH p m j t U XX| ≤ V + 2 + 2 * Lc p m := by
    by_cases hle : XX ≤ r
    · have h := abs_step_below_le hp1 hp2 (m := m) (j := j) (t := t) (U := U)
        hbelow (by omega : (0 : ℤ) ≤ XX - 1) (by omega) hhX1
      rw [show XX - 1 + 1 = XX by ring] at h
      rw [abs_sub_comm]
      linarith
    · have hgt : r < XX := not_le.mp hle
      have h := abs_step_above_le hp1 hp2 (m := m) (j := j) (t := t) (U := U)
        hcl he1 he2 (by omega : r ≤ XX - 1)
      rw [show XX - 1 + 1 = XX by ring] at h
      rw [abs_sub_comm] at h
      linarith
  have hsum : |projH p m j t U (XX + 1) - projH p m j t U XX|
      + |projH p m j t U (XX - 1) - projH p m j t U XX|
      ≤ envC p m V := by
    simp only [envC]
    linarith
  simpa only [nbT, hXX] using hsum

/-! ### 5. The deterministic window event and the carrier containment -/

/-- The **record-window event**: the running record of walker `j` stays in `[A, A+M)`, walker
`i` stays in the same window with one site of margin on each side, and the quenched environment
`h_j` is at most `V` on `[A-1, A+M)`.  All three conditions are deterministic. -/
def qplWindow (p : ℝ) (m : ℕ) (i j : Fin N) (V : ℝ) (A M K : ℕ) : Set (Array N) :=
  {U | (∀ k < K, A ≤ (recVal j (prefOf p m k U)).toNat ∧
      (recVal j (prefOf p m k U)).toNat < A + M) ∧
    (∀ y ∈ Finset.Ico (A - 1) (A + M), hof p (siteMarks p m U j) y ≤ V) ∧
    (∀ k < K, A ≤ ((trajectory p m U k).pos i).toNat ∧
      ((trajectory p m U k).pos i).toNat + 2 ≤ A + M)}

theorem qplWindow_def (p : ℝ) (m : ℕ) (i j : Fin N) (V : ℝ) (A M K : ℕ) :
    qplWindow p m i j V A M K
      = {U | (∀ k < K, A ≤ (recVal j (prefOf p m k U)).toNat ∧
          (recVal j (prefOf p m k U)).toNat < A + M) ∧
        (∀ y ∈ Finset.Ico (A - 1) (A + M), hof p (siteMarks p m U j) y ≤ V) ∧
        (∀ k < K, A ≤ ((trajectory p m U k).pos i).toNat ∧
          ((trajectory p m U k).pos i).toNat + 2 ≤ A + M)} := rfl

/-- **The `nbT` envelope on the whole horizon.** -/
theorem ae_forall_nbT_le_of_window {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} {i j : Fin N} {K : ℕ} {V : ℝ} (hV1 : 1 ≤ V) {A M : ℕ} (hA : 1 ≤ A) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ k : ℕ, k < K →
      (A ≤ (recVal j (prefOf p m k U)).toNat ∧
        (recVal j (prefOf p m k U)).toNat < A + M) →
      (∀ y ∈ Finset.Ico (A - 1) (A + M), hof p (siteMarks p m U j) y ≤ V) →
      (A ≤ ((trajectory p m U k).pos i).toNat ∧
        ((trajectory p m U k).pos i).toNat + 2 ≤ A + M) →
      nbT p m i j k U ≤ envC p m V :=
  MeasureTheory.ae_all_iff.mpr fun k =>
    (nbT_le_of_window_at (N := N) (p := p) hp1 hp2 (m := m) (i := i) (j := j) (t := k) hV1
      (A := A) (M := M) hA).mono
      (fun U hU _hk hrec hh hX => hU hrec hh hX)

/-- **The window event implies the carrier at every time of the horizon.** -/
theorem ae_qplWindow_subset_carrier {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} {i j : Fin N} {K : ℕ} {V : ℝ} (hV1 : 1 ≤ V) {A M : ℕ} (hA : 1 ≤ A) :
    ∀ᵐ U ∂(arrayMeasure N), U ∈ qplWindow p m i j V A M K →
      ∀ k < K, U ∈ qplCarrier (N := N) p m i j V (envC p m V) k := by
  filter_upwards [ae_forall_nbT_le_of_window (N := N) (p := p) hp1 hp2 (m := m) (i := i) (j := j)
    (K := K) (V := V) hV1 (A := A) (M := M) hA] with U hnb hW k hk
  obtain ⟨hrec, hh, hX⟩ := hW
  refine ⟨SiteHMax.siteGood_of_window hp1 hp2 m j hA (K := K) hrec hh hk, ?_⟩
  exact hnb k hk (hrec k hk) hh (hX k hk)

/-! ### 6. The residual probability splits into a harmonic and a geometric part -/

/-- The **geometric containment defect**: either the record of walker `j` or the position of
walker `i` leaves the window `[A, A+M)` (with the one-site margin for walker `i`). -/
def contDefect (p : ℝ) (m : ℕ) (i j : Fin N) (A M K : ℕ) : Set (Array N) :=
  {U | (∃ k < K, ¬ (A ≤ (recVal j (prefOf p m k U)).toNat ∧
        (recVal j (prefOf p m k U)).toNat < A + M)) ∨
      (∃ k < K, ¬ (A ≤ ((trajectory p m U k).pos i).toNat ∧
        ((trajectory p m U k).pos i).toNat + 2 ≤ A + M))}

/-- The **harmonic defect** at level `V`: the quenched environment exceeds `V` somewhere on the
site window `[A-1, A+M)`. -/
def harmDefect (p : ℝ) (m : ℕ) (j : Fin N) (V : ℝ) (A M : ℕ) : Set (Array N) :=
  {U | ¬ ∀ y ∈ Finset.Ico (A - 1) (A + M), hof p (siteMarks p m U j) y ≤ V}

theorem not_mem_qplWindow_subset {p : ℝ} {m : ℕ} {i j : Fin N} {V : ℝ} {A M K : ℕ} :
    {U : Array N | ¬ U ∈ qplWindow p m i j V A M K}
      ⊆ contDefect p m i j A M K ∪ harmDefect p m j V A M := by
  intro U hU
  simp only [qplWindow, Set.mem_ofPred_eq] at hU
  simp only [contDefect, harmDefect, Set.mem_union, Set.mem_ofPred_eq]
  rcases not_and_or.mp hU with hA | hBC
  · left; left
    obtain ⟨k, hk⟩ := not_forall.mp hA
    obtain ⟨hkK, hkP⟩ := Classical.not_imp.mp hk
    exact ⟨k, hkK, hkP⟩
  · rcases not_and_or.mp hBC with hB | hC
    · right; exact hB
    · left; right
      obtain ⟨k, hk⟩ := not_forall.mp hC
      obtain ⟨hkK, hkP⟩ := Classical.not_imp.mp hk
      exact ⟨k, hkK, hkP⟩

/-- **The residual probability is bounded by the geometric defect plus the harmonic defect.**
This is the exact set-theoretic reduction: the harmonic part is *not* renamed, it is isolated as
the single event `harmDefect`. -/
theorem measure_residual_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} {i j : Fin N} {K : ℕ} {V : ℝ} (hV1 : 1 ≤ V) {A M : ℕ} (hA : 1 ≤ A) :
    (arrayMeasure N).real {U | ∃ k < K,
        U ∉ qplCarrier (N := N) p m i j V (envC p m V) k}
      ≤ (arrayMeasure N).real (contDefect p m i j A M K)
        + (arrayMeasure N).real (harmDefect p m j V A M) := by
  have hsub : {U : Array N | ∃ k < K, U ∉ qplCarrier (N := N) p m i j V (envC p m V) k}
      ≤ᵐ[arrayMeasure N] (contDefect p m i j A M K ∪ harmDefect p m j V A M : Set (Array N)) := by
    filter_upwards [ae_qplWindow_subset_carrier (N := N) (p := p) hp1 hp2 (m := m) (i := i)
      (j := j) (K := K) (V := V) hV1 (A := A) (M := M) hA] with U hU hmem
    obtain ⟨k, hk, hkc⟩ := hmem
    exact not_mem_qplWindow_subset (fun hW => absurd (hU hW k hk) hkc)
  have h1 : arrayMeasure N {U : Array N | ∃ k < K,
        U ∉ qplCarrier (N := N) p m i j V (envC p m V) k}
      ≤ arrayMeasure N (contDefect p m i j A M K ∪ harmDefect p m j V A M) :=
    measure_mono_ae hsub
  refine le_trans ?_ (measureReal_union_le (contDefect p m i j A M K) (harmDefect p m j V A M))
  rw [Measure.real_def, Measure.real_def]
  exact ENNReal.toReal_mono (measure_ne_top _ _) h1

/-! ### 7. The harmonic defect is discharged by the accepted wide `(locmax)` bound -/

theorem harmDefect_subset_HMaxBadW (p : ℝ) (m : ℕ) (j : Fin N) {A M L : ℕ} :
    harmDefect p m j (LocSumAct.xOf L) A M
      ⊆ {U : Array N | WideRepair.HMaxBadW p m L 1 M A U} := by
  intro U hU
  simp only [harmDefect, Set.mem_ofPred_eq, WideRepair.HMaxBadW] at hU ⊢
  push Not at hU
  obtain ⟨y, hy, hgt⟩ := hU
  exact ⟨j, y, hy, le_of_lt hgt⟩

/-- **The harmonic defect has the accepted `exp(-c·L^(1/16))` bound.**  The only input is
`WideRepair.array_locmax_bound_paper_window`; the union over the walkers in `HMaxBadW` makes the
single-walker event a subset, so no probability is added. -/
theorem measure_harmDefect_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (j : Fin N) (T : ℕ) (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ (A M : ℕ), 1 ≤ A →
      M + 1 ≤ 2 * (T + 3) * L →
      (arrayMeasure N).real (harmDefect p m j (LocSumAct.xOf L) A M)
        ≤ Real.exp (-c * LocSumAct.xOf L) := by
  obtain ⟨c, hc, L₀, hL0⟩ :=
    WideRepair.array_locmax_bound_paper_window (N := N) (p := p) hp1 hp2 hm T hT
  refine ⟨c, hc, L₀, ?_⟩
  intro L hL A M hA hMUp
  have hmono : arrayMeasure N (harmDefect p m j (LocSumAct.xOf L) A M)
      ≤ arrayMeasure N {U : Array N | WideRepair.HMaxBadW p m L 1 M A U} :=
    measure_mono (harmDefect_subset_HMaxBadW (N := N) p m j (A := A) (M := M) (L := L))
  have hMUp' : 1 + M ≤ 2 * (T + 3) * L := by omega
  have hb := hL0 L hL A 1 M (by simpa using hA) hMUp'
  rw [Measure.real_def]
  calc ((arrayMeasure N) (harmDefect p m j (LocSumAct.xOf L) A M)).toReal
      ≤ ((arrayMeasure N) {U : Array N | WideRepair.HMaxBadW p m L 1 M A U}).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) hmono
    _ ≤ (ENNReal.ofReal (Real.exp (-c * LocSumAct.xOf L))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    _ = Real.exp (-c * LocSumAct.xOf L) := ENNReal.toReal_ofReal (Real.exp_pos _).le

/-! ### 8. The envelope `envB` at the carrier level is `O(V+2)` -/

/-- The explicit constant of the window envelope: `KepW = 2 (3 Cproj + 2 + 10/(1-a))`. -/
noncomputable def KepW (p : ℝ) (m : ℕ) : ℝ :=
  2 * (3 * SiteHMax.Cproj p m + 2 + 10 * (1 - aRec p m)⁻¹)

theorem KepW_pos {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) : 0 < KepW p m := by
  have hC := SiteHMax.Cproj_nonneg hp1 hp2 m
  have hinv : 0 < (1 - aRec p m)⁻¹ := inv_pos.mpr (one_sub_aRec_pos hp1 hp2 m)
  simp only [KepW]
  linarith

/-- **`envB` at the carrier level `c = envC V` is at most `KepW (V+2)`.** -/
theorem envB_envC_le_kepW {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) {V : ℝ}
    (hV : 1 ≤ V) : envB p m V (envC p m V) ≤ KepW p m * (V + 2) := by
  have hV0 : (0 : ℝ) ≤ V := le_trans zero_le_one hV
  have hV2 : (1 : ℝ) ≤ V + 2 := by linarith
  have hC := SiteHMax.Cproj_nonneg hp1 hp2 m
  have hinv : 0 < (1 - aRec p m)⁻¹ := inv_pos.mpr (one_sub_aRec_pos hp1 hp2 m)
  have hLle : Lc p m ≤ 2 * (1 - aRec p m)⁻¹ := projL_le hp1 hp2 m
  have hL0 : 0 ≤ Lc p m := Lc_nonneg hp1 hp2 m
  -- `capB ≤ 3 Cproj (V+2)`
  have hcap : SiteHMax.capB p m V ≤ SiteHMax.Cproj p m * (3 * (V + 2)) := by
    have hdef : SiteHMax.capB p m V = SiteHMax.Cproj p m * (2 * V + 7) := rfl
    rw [hdef]
    refine mul_le_mul_of_nonneg_left ?_ hC
    linarith
  -- `envC ≤ 2 (V+2) + 8/(1-a)`
  have hc : envC p m V ≤ 2 * (V + 2) + 8 * (1 - aRec p m)⁻¹ := by
    simp only [envC]
    nlinarith [hLle, hV0, hinv]
  -- `8/(1-a) ≤ 8 (V+2)/(1-a)`
  have h8 : 8 * (1 - aRec p m)⁻¹ ≤ 8 * (V + 2) * (1 - aRec p m)⁻¹ := by
    have := mul_le_mul_of_nonneg_right hV2 (le_of_lt hinv)
    linarith
  have hkey : SiteHMax.capB p m V + envC p m V + 2 * (V + 2) * (1 - aRec p m)⁻¹
      ≤ (3 * SiteHMax.Cproj p m + 2 + 10 * (1 - aRec p m)⁻¹) * (V + 2) := by
    have h1 : SiteHMax.Cproj p m * (3 * (V + 2)) = 3 * SiteHMax.Cproj p m * (V + 2) := by ring
    nlinarith [hcap, hc, h8, hV2, hinv, hC]
  simp only [envB, KepW]
  linarith

/-! ### 9. The composed `Qpl` maximal bound with the reduced residual -/

/-- **The `Qpl` maximal bound at the paper's scale, with the residual reduced to the geometric
containment defect plus the discharged harmonic defect.**

  `μ.real {∃ k ≤ T*L, L^{3/4} ≤ |Qpl_k|}`
  `  ≤ 2 (T L + 1) exp (-V^8/(4 T (KepW (V+2))^2))`
  `    + μ.real (contDefect …) + μ.real (harmDefect …)`,   `V = xOf L = L^{1/16}`,

and `μ.real (harmDefect …) ≤ exp (-c L^{1/16})` by `measure_harmDefect_le`.  The point is that
the carrier residual is no longer an abstract event: what survives is exactly the geometric
record/position containment defect, with the harmonic part fully charged. -/
theorem qpl_measure_max_abs_le_of_window_scale {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {i j : Fin N} (hij : i ≠ j) {eps : ℝ} (hε : 0 < eps)
    {T L : ℕ} (hT : 1 ≤ T) (hL : 1 ≤ L) {A M : ℕ} (hA : 1 ≤ A)
    (hMUp : M + 1 ≤ 2 * (T + 3) * L) :
    (arrayMeasure N).real
        {U | ∃ k ≤ T * L, (L : ℝ) ^ (3 / 4 : ℝ) ≤ |ProjLedger.Qpl p m eps i j k U|}
      ≤ 2 * (((T * L : ℕ) : ℝ) + 1)
            * Real.exp (-((LocSumAct.xOf L) ^ 8 /
                (4 * (T : ℝ) * (KepW p m * (LocSumAct.xOf L + 2)) ^ 2)))
        + (arrayMeasure N).real (contDefect p m i j A M (T * L))
        + (arrayMeasure N).real (harmDefect p m j (LocSumAct.xOf L) A M) := by
  have hLr : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL)
  have hV1 : (1 : ℝ) ≤ LocSumAct.xOf L := LocSumAct.one_le_xOf hL
  have hV0 : (0 : ℝ) < LocSumAct.xOf L := lt_of_lt_of_le zero_lt_one hV1
  have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  have hTL : 1 ≤ T * L :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hmain := qpl_measure_max_abs_le_of_small_carrier (N := N) (m := m) hp0 hp1 hij hε
    (V := LocSumAct.xOf L) (c := envC p m (LocSumAct.xOf L)) hV0.le
    (envC_nonneg hp0 hp1 m hV0.le) (n := T * L) hTL
    (ε := (L : ℝ) ^ (3 / 4 : ℝ)) (Real.rpow_pos_of_pos hLr _)
  have hres := measure_residual_le (N := N) (p := p) hp0 hp1 (m := m) (i := i) (j := j)
    (K := T * L) (V := LocSumAct.xOf L) hV1 (A := A) (M := M) hA
  refine le_trans hmain ?_
  have hexp : 2 * (((T * L : ℕ) : ℝ) + 1)
        * Real.exp (-((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2
            / (4 * ((T * L : ℕ) : ℝ)
                * (envB p m (LocSumAct.xOf L) (envC p m (LocSumAct.xOf L))) ^ 2))
      ≤ 2 * (((T * L : ℕ) : ℝ) + 1)
        * Real.exp (-((LocSumAct.xOf L) ^ 8 /
            (4 * (T : ℝ) * (KepW p m * (LocSumAct.xOf L + 2)) ^ 2))) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Real.exp_le_exp.mpr ?_
    have hεeq : (L : ℝ) ^ (3 / 4 : ℝ) = (LocSumAct.xOf L) ^ 12 :=
      (LocMoveLocal.xOf_pow_twelve L).symm
    have hVpow : (LocSumAct.xOf L) ^ 16 = (L : ℝ) := LocSumAct.xOf_pow L
    have henv : envB p m (LocSumAct.xOf L) (envC p m (LocSumAct.xOf L))
        ≤ KepW p m * (LocSumAct.xOf L + 2) := envB_envC_le_kepW hp0 hp1 m hV1
    have henv0 : 0 ≤ envB p m (LocSumAct.xOf L) (envC p m (LocSumAct.xOf L)) :=
      (envB_pos hp0 hp1 m hV0.le (envC_nonneg hp0 hp1 m hV0.le)).le
    have henv2 : (envB p m (LocSumAct.xOf L) (envC p m (LocSumAct.xOf L))) ^ 2
        ≤ (KepW p m * (LocSumAct.xOf L + 2)) ^ 2 :=
      pow_le_pow_left₀ henv0 henv 2
    rw [hεeq, Nat.cast_mul, ← hVpow]
    have heB : 0 < envB p m (LocSumAct.xOf L) (envC p m (LocSumAct.xOf L)) :=
      envB_pos hp0 hp1 m hV0.le (envC_nonneg hp0 hp1 m hV0.le)
    -- the two denominators
    have hstep : (LocSumAct.xOf L) ^ 8
          / (4 * (T : ℝ) * (KepW p m * (LocSumAct.xOf L + 2)) ^ 2)
        ≤ ((LocSumAct.xOf L) ^ 12) ^ 2
          / (4 * ((T : ℝ) * (LocSumAct.xOf L) ^ 16)
              * (envB p m (LocSumAct.xOf L) (envC p m (LocSumAct.xOf L))) ^ 2) := by
      -- replace the `V^16`-scaled fraction by the `T*envB^2`-scaled one
      have heq : ((LocSumAct.xOf L) ^ 12) ^ 2
            / (4 * ((T : ℝ) * (LocSumAct.xOf L) ^ 16)
                * (envB p m (LocSumAct.xOf L) (envC p m (LocSumAct.xOf L))) ^ 2)
          = (LocSumAct.xOf L) ^ 8
            / (4 * (T : ℝ)
                * (envB p m (LocSumAct.xOf L) (envC p m (LocSumAct.xOf L))) ^ 2) := by
        have h1 : ((LocSumAct.xOf L) ^ 12) ^ 2
            = (LocSumAct.xOf L) ^ 16 * (LocSumAct.xOf L) ^ 8 := by ring
        have h2 : 4 * ((T : ℝ) * (LocSumAct.xOf L) ^ 16)
              * (envB p m (LocSumAct.xOf L) (envC p m (LocSumAct.xOf L))) ^ 2
            = (LocSumAct.xOf L) ^ 16
              * (4 * (T : ℝ)
                * (envB p m (LocSumAct.xOf L) (envC p m (LocSumAct.xOf L))) ^ 2) := by ring
        rw [h1, h2]
        exact mul_div_mul_left _ _ (by positivity : (LocSumAct.xOf L) ^ 16 ≠ 0)
      rw [heq]
      refine div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ (LocSumAct.xOf L) ^ 8)
        (by positivity) ?_
      exact mul_le_mul_of_nonneg_left henv2 (by positivity)
    have := neg_le_neg hstep
    simpa only [neg_div] using this
  linarith [hexp, hres]

/-! ### 10. The geometric defect is a start-time event -/

/-- The record is monotone in time. -/
theorem recVal_mono_le {p : ℝ} {m : ℕ} {j : Fin N} {U : Array N} {a b : ℕ} (h : a ≤ b) :
    recVal j (prefOf p m a U) ≤ recVal j (prefOf p m b U) := by
  induction b, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact le_trans ih (recVal_le_succ p m U j n)

/-- The record grows by at most one per step. -/
theorem recVal_le_add_run {p : ℝ} {m : ℕ} {j : Fin N} {U : Array N} (a b : ℕ) (h : a ≤ b) :
    recVal j (prefOf p m b U) ≤ recVal j (prefOf p m a U) + ((b - a : ℕ) : ℤ) := by
  induction b, h using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
      have hstep : recVal j (prefOf p m (n + 1) U) ≤ recVal j (prefOf p m n U) + 1 :=
        recVal_succ_le p m U j n
      have hsub : (n + 1 - a : ℕ) = (n - a) + 1 := by omega
      rw [hsub]
      push_cast
      linarith

/-- The walker's position grows by at most one per step. -/
theorem pos_le_add_run (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (s r : ℕ) :
    (trajectory p m U (s + r)).pos i ≤ (trajectory p m U s).pos i + (r : ℤ) := by
  induction r with
  | zero => simp
  | succ k ih =>
      have hstep := SwarmQVariance.X_succ_sub_X (N := N) p m U (s + k) i
      rw [show s + (k + 1) = (s + k) + 1 by ring]
      rcases hstep with h | h
      · have h' : (trajectory p m U (s + k + 1)).pos i
            = (trajectory p m U (s + k)).pos i + 1 := by
          simpa only [SepGroup.Model.X_apply] using h
        rw [h']; push_cast; linarith
      · have h' : (trajectory p m U (s + k + 1)).pos i
            = (trajectory p m U (s + k)).pos i - 1 := by
          simpa only [SepGroup.Model.X_apply] using h
        rw [h']; push_cast; linarith

/-- The walker's position falls by at most one per step. -/
theorem pos_sub_run_le (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (s r : ℕ) :
    (trajectory p m U s).pos i - (r : ℤ) ≤ (trajectory p m U (s + r)).pos i := by
  induction r with
  | zero => simp
  | succ k ih =>
      have hstep := SwarmQVariance.X_succ_sub_X (N := N) p m U (s + k) i
      rw [show s + (k + 1) = (s + k) + 1 by ring]
      rcases hstep with h | h
      · have h' : (trajectory p m U (s + k + 1)).pos i
            = (trajectory p m U (s + k)).pos i + 1 := by
          simpa only [SepGroup.Model.X_apply] using h
        rw [h']; push_cast; linarith
      · have h' : (trajectory p m U (s + k + 1)).pos i
            = (trajectory p m U (s + k)).pos i - 1 := by
          simpa only [SepGroup.Model.X_apply] using h
        rw [h']; push_cast; linarith

/-- **The start condition.**  At time `0` the record of walker `j` and the position of walker `i`
lie in `[A, A+M)` with a `K+1` (resp. `K+2`) margin below the top; this is the paper's
"`d_r ≤ L` at the record time" condition, kept as an explicit event. -/
def startContain (p : ℝ) (m : ℕ) (i j : Fin N) (A M K : ℕ) : Set (Array N) :=
  {U | A ≤ (recVal j (prefOf p m 0 U)).toNat ∧
      (recVal j (prefOf p m 0 U)).toNat + K + 1 ≤ A + M ∧
      A + K ≤ ((trajectory p m U 0).pos i).toNat ∧
      ((trajectory p m U 0).pos i).toNat + K + 2 ≤ A + M}

/-- **The start condition rules out the geometric containment defect.**  Only nearest-neighbour
propagation of the record and of the position is used, with no probability input. -/
theorem contDefect_subset_compl_startContain {p : ℝ} {m : ℕ} {i j : Fin N} {A M K : ℕ}
    (hA : 1 ≤ A) :
    startContain p m i j A M K ⊆ (contDefect p m i j A M K)ᶜ := by
  intro U hU
  obtain ⟨hr0, hrM, hx0, hxM⟩ := hU
  set r0 : ℤ := recVal j (prefOf p m 0 U) with hr0def
  set x0 : ℤ := (trajectory p m U 0).pos i with hx0def
  have hr0nn : 0 ≤ r0 := zero_le_recVal_prefOf p m U j 0
  have hrcast : (r0.toNat : ℤ) = r0 := Int.toNat_of_nonneg hr0nn
  have hx0nn : 0 ≤ x0 := by
    by_contra hcon
    have hz : x0.toNat = 0 := Int.toNat_of_nonpos (by omega)
    omega
  have hxcast : (x0.toNat : ℤ) = x0 := Int.toNat_of_nonneg hx0nn
  have hA1 : (1 : ℤ) ≤ (A : ℤ) := by exact_mod_cast hA
  have hMKr : r0 + (K : ℤ) + 1 ≤ (A : ℤ) + (M : ℤ) := by
    have h : ((r0.toNat + K + 1 : ℕ) : ℤ) ≤ ((A + M : ℕ) : ℤ) := by exact_mod_cast hrM
    push_cast at h
    rw [hrcast] at h
    linarith
  have hMKx : x0 + (K : ℤ) + 2 ≤ (A : ℤ) + (M : ℤ) := by
    have h : ((x0.toNat + K + 2 : ℕ) : ℤ) ≤ ((A + M : ℕ) : ℤ) := by exact_mod_cast hxM
    push_cast at h
    rw [hxcast] at h
    linarith
  have hrec : ∀ k, k < K → A ≤ (recVal j (prefOf p m k U)).toNat ∧
      (recVal j (prefOf p m k U)).toNat < A + M := by
    intro k hk
    have hkK : (k : ℤ) ≤ (K : ℤ) - 1 := by
      have h : ((k : ℕ) : ℤ) + 1 ≤ (K : ℤ) := by exact_mod_cast hk
      linarith
    have hmono : r0 ≤ recVal j (prefOf p m k U) := by
      rw [hr0def]
      exact recVal_mono_le (Nat.zero_le k)
    have hle : recVal j (prefOf p m k U) ≤ r0 + (k : ℤ) := by
      have h := recVal_le_add_run (p := p) (m := m) (j := j) (U := U) 0 k (Nat.zero_le k)
      rw [Nat.sub_zero, ← hr0def] at h
      exact h
    have hzk : (0 : ℤ) ≤ recVal j (prefOf p m k U) := le_trans hr0nn hmono
    have hArec : ((A : ℕ) : ℤ) ≤ r0 := by rw [← hrcast]; exact_mod_cast hr0
    refine ⟨(Int.le_toNat hzk).mpr ?_, (Int.toNat_lt hzk).mpr ?_⟩
    · linarith
    · push_cast
      linarith
  have hpos : ∀ k, k < K → A ≤ ((trajectory p m U k).pos i).toNat ∧
      ((trajectory p m U k).pos i).toNat + 2 ≤ A + M := by
    intro k hk
    have hkK : (k : ℤ) ≤ (K : ℤ) - 1 := by
      have h : ((k : ℕ) : ℤ) + 1 ≤ (K : ℤ) := by exact_mod_cast hk
      linarith
    have hle : (trajectory p m U k).pos i ≤ x0 + (k : ℤ) := by
      have h := pos_le_add_run (p := p) m U i 0 k
      simp only [Nat.zero_add] at h
      rw [hx0def]
      exact h
    have hge : x0 - (k : ℤ) ≤ (trajectory p m U k).pos i := by
      have h := pos_sub_run_le (p := p) m U i 0 k
      simp only [Nat.zero_add] at h
      rw [hx0def]
      exact h
    have hApos : ((A : ℕ) : ℤ) + (K : ℤ) ≤ x0 := by rw [← hxcast]; exact_mod_cast hx0
    have hxk : (0 : ℤ) ≤ (trajectory p m U k).pos i := by linarith
    have hxk2 : (0 : ℤ) ≤ (trajectory p m U k).pos i + 2 := by linarith
    refine ⟨(Int.le_toNat hxk).mpr ?_, ?_⟩
    · linarith
    · have hzeq : ((((trajectory p m U k).pos i).toNat : ℕ) : ℤ) = (trajectory p m U k).pos i :=
        Int.toNat_of_nonneg hxk
      have hZ : (trajectory p m U k).pos i + 2 ≤ (A : ℤ) + (M : ℤ) := by linarith
      omega
  rw [Set.mem_compl_iff, contDefect, Set.mem_ofPred_eq, not_or]
  exact ⟨fun ⟨k, hk, hcon⟩ => hcon (hrec k hk),
    fun ⟨k, hk, hcon⟩ => hcon (hpos k hk)⟩

/-! ### 11. The final composition: harmonic defect discharged, geometric defect exposed -/

/-- **The `Qpl` maximal bound with the harmonic defect fully discharged.**  The only remaining
probability is the geometric containment defect; everything else is explicit. -/
theorem qpl_measure_max_abs_le_of_window_discharged {p : ℝ} (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) {i j : Fin N} (hij : i ≠ j) {eps : ℝ} (hε : 0 < eps)
    {T : ℕ} (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ (A M : ℕ), 1 ≤ A →
      M + 1 ≤ 2 * (T + 3) * L →
      (arrayMeasure N).real
          {U | ∃ k ≤ T * L, (L : ℝ) ^ (3 / 4 : ℝ) ≤ |ProjLedger.Qpl p m eps i j k U|}
        ≤ 2 * (((T * L : ℕ) : ℝ) + 1)
              * Real.exp (-((LocSumAct.xOf L) ^ 8 /
                  (4 * (T : ℝ) * (KepW p m * (LocSumAct.xOf L + 2)) ^ 2)))
          + (arrayMeasure N).real (contDefect p m i j A M (T * L))
          + Real.exp (-c * LocSumAct.xOf L) := by
  obtain ⟨c, hc, L₀, hL0⟩ := measure_harmDefect_le (N := N) (p := p) hp0 hp1 hm j T hT
  refine ⟨c, hc, max L₀ 1, ?_⟩
  intro L hL A M hA hMUp
  have hL0' : L₀ ≤ L := le_trans (le_max_left _ _) hL
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  refine le_trans (qpl_measure_max_abs_le_of_window_scale (N := N) (p := p) hp0 hp1 hij hε
    hT hL1 hA hMUp) ?_
  have hharm := hL0 L hL0' A M hA hMUp
  linarith [hharm]

/-- **The same bound with the geometric defect replaced by its start-time version.**  The residual
is now exactly the complement of `startContain`: the position and record configuration at time `0`
(with the `T*L` margins) is the only remaining probabilistic input. -/
theorem qpl_measure_max_abs_le_of_window_start {p : ℝ} (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) {i j : Fin N} (hij : i ≠ j) {eps : ℝ} (hε : 0 < eps)
    {T : ℕ} (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ (A M : ℕ), 1 ≤ A →
      M + 1 ≤ 2 * (T + 3) * L →
      (arrayMeasure N).real
          {U | ∃ k ≤ T * L, (L : ℝ) ^ (3 / 4 : ℝ) ≤ |ProjLedger.Qpl p m eps i j k U|}
        ≤ 2 * (((T * L : ℕ) : ℝ) + 1)
              * Real.exp (-((LocSumAct.xOf L) ^ 8 /
                  (4 * (T : ℝ) * (KepW p m * (LocSumAct.xOf L + 2)) ^ 2)))
          + (arrayMeasure N).real (startContain p m i j A M (T * L))ᶜ
          + Real.exp (-c * LocSumAct.xOf L) := by
  obtain ⟨c, hc, L₀, hL0⟩ := qpl_measure_max_abs_le_of_window_discharged (N := N) (p := p)
    hp0 hp1 hm hij hε hT
  refine ⟨c, hc, L₀, ?_⟩
  intro L hL A M hA hMUp
  refine le_trans (hL0 L hL A M hA hMUp) ?_
  have hsub := contDefect_subset_compl_startContain (N := N) (p := p) (m := m) (i := i)
    (j := j) (A := A) (M := M) (K := T * L) hA
  have hcomp : contDefect p m i j A M (T * L) ⊆ (startContain p m i j A M (T * L))ᶜ := by
    intro U hU hV
    exact hsub hV hU
  have hmono : (arrayMeasure N).real (contDefect p m i j A M (T * L))
      ≤ (arrayMeasure N).real (startContain p m i j A M (T * L))ᶜ :=
    measureReal_mono hcomp (measure_ne_top _ _)
  linarith [hmono]

/-- **The record-window instantiation at the paper's width.**  Here the window is the *interval*
`[A, A+M)` (so `A` is its lower end, not the anchor of `HMaxBadW`).  Taking `M = L + 2*T*L + 2`
— the total width `M + Up = (L + 2*T*L + 2) + L` of the integrated record window
`[R - L - T*L, R + T*L]` of `WideTotal.exists_measure_sep_window_dev_le_record` — the harmonic
hypothesis `M + 1 ≤ 2 (T+3) L` is automatic for `L ≥ 1`, so the only remaining hypotheses are
`1 ≤ A` and `1 ≤ L`. -/
theorem qpl_measure_max_abs_le_of_record_window {p : ℝ} (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) {i j : Fin N} (hij : i ≠ j) {eps : ℝ} (hε : 0 < eps)
    {T : ℕ} (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ A : ℕ, 1 ≤ A →
      (arrayMeasure N).real
          {U | ∃ k ≤ T * L, (L : ℝ) ^ (3 / 4 : ℝ) ≤ |ProjLedger.Qpl p m eps i j k U|}
        ≤ 2 * (((T * L : ℕ) : ℝ) + 1)
              * Real.exp (-((LocSumAct.xOf L) ^ 8 /
                  (4 * (T : ℝ) * (KepW p m * (LocSumAct.xOf L + 2)) ^ 2)))
          + (arrayMeasure N).real
              (startContain p m i j A (L + 2 * T * L + 2) (T * L))ᶜ
          + Real.exp (-c * LocSumAct.xOf L) := by
  obtain ⟨c, hc, L₀, hL0⟩ := qpl_measure_max_abs_le_of_window_start (N := N) (p := p)
    hp0 hp1 hm hij hε hT
  refine ⟨c, hc, max L₀ 1, ?_⟩
  intro L hL A hA
  refine hL0 L (le_trans (le_max_left _ _) hL) A (L + 2 * T * L + 2) hA ?_
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  have hMUp : L + 2 * T * L + 2 + 1 ≤ 2 * (T + 3) * L := by
    have h2 : 2 * (T + 3) * L = 2 * T * L + 6 * L := by ring
    rw [h2]
    have : 2 * T * L = 2 * (T * L) := by ring
    nlinarith
  exact hMUp

/-! ### 12. The absolute-time start defect is empty: the model starts at the origin

`Trajectory.trajectory_zero` gives `(trajectory p m U 0).pos i = 0` for **every** `i` and every
`U`, hence the running record at time `0` is `0`.  Consequently the lower margin
`A ≤ (M_0^j).toNat` of `startContain` forces `A = 0`, and for the paper window (`1 ≤ A`) the start
event of §10 is empty: `startContain` cannot carry the residual.  This is recorded here as a
theorem, because it is the exact reason the containment has to be anchored with the window's
*lower edge at the origin* (the actual initial configuration), which is what §13 does. -/

theorem pos_zero (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) :
    (trajectory p m U 0).pos i = 0 := by
  simp

theorem recVal_zero (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) :
    recVal j (prefOf p m 0 U) = 0 := by
  have hge : 0 ≤ recVal j (prefOf p m 0 U) := zero_le_recVal_prefOf p m U j 0
  have hle : recVal j (prefOf p m 0 U) ≤ 0 := by
    rw [← runMax_eq_recVal]
    refine le_trans (Finset.sup'_le _ _ (fun t ht => ?_)) (le_of_eq (pos_zero p m U j))
    have ht0 : t = 0 := by simpa using ht
    rw [ht0]
  omega

/-- **The instability of the absolute-time start defect.**  For `1 ≤ A` the start event of §10 is
empty, so `μ.real (startContain …)ᶜ = 1`: the residual of the absolute-time formulation is
absorbed by the initial condition, and the containment has to be anchored at the origin instead. -/
theorem startContain_eq_empty {p : ℝ} {m : ℕ} {i j : Fin N} {A M K : ℕ} (hA : 1 ≤ A) :
    startContain p m i j A M K = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  intro U hU
  obtain ⟨hr0, -, -, -⟩ := hU
  have hz : recVal j (prefOf p m 0 U) = 0 := recVal_zero p m U j
  rw [hz] at hr0
  simp only [Int.toNat_zero] at hr0
  omega

theorem measure_startContain_compl {p : ℝ} {m : ℕ} {i j : Fin N} {A M K : ℕ} (hA : 1 ≤ A) :
    (arrayMeasure N).real (startContain p m i j A M K)ᶜ = 1 := by
  rw [startContain_eq_empty (N := N) hA, Set.compl_empty]
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  rw [Measure.real_def, measure_univ]
  simp

/-! ### 13. The origin-anchored window: containment with no lower margin

Since every walker starts at `0`, the natural window is `[0, 1+M)` in *site* coordinates: its lower
edge is the origin, where the walkers actually are.  No lower margin is then needed, because

* below the record the step at a site `y < 0` is exactly `1` (`Hpot` is linear there), and at
  `y ≥ 0` it is the revealed value `h_j(y)`, controlled by the window;
* the record's own predecessor site `M_t^j - 1` needs the window only when `M_t^j ≥ 1`, and the
  boundary case `M_t^j = 0` gives the value `1`.

So the containment only asks for **upper** bounds on the record and on walker `i`, plus
`h_j ≤ V` on `[0, 1+M)`.  At time `0` the record is `0` and the position is `0`
(`recVal_zero`, `pos_zero`), so those upper bounds hold for *every* `U` as soon as `1 ≤ M`. -/

theorem HprevAt_le_of_top {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (j : Fin N) {M t : ℕ} {V : ℝ} (hV1 : 1 ≤ V) {U : Array N}
    (hr : (recVal j (prefOf p m t U)).toNat < 1 + M)
    (hh : ∀ y ∈ Finset.Ico 0 (1 + M), hof p (siteMarks p m U j) y ≤ V) :
    HprevAt p m t j U ≤ V := by
  rcases Nat.eq_zero_or_pos ((recVal j (prefOf p m t U)).toNat) with h0 | hpos
  · rw [HprevAt_of_zero p m t j U h0]; exact hV1
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
      (by omega : (recVal j (prefOf p m t U)).toNat ≠ 0)
    rw [HprevAt_of_succ p m t j U k hk]
    refine hh k ?_
    rw [Finset.mem_Ico]
    omega

/-- The `+1` step at or below the record, with **no lower margin**: at a negative site the step is
`1`, at a nonnegative site it is the revealed value on the window. -/
theorem abs_step_below_le_top {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {V : ℝ}
    (hV1 : 1 ≤ V) {m : ℕ} (j : Fin N) {t : ℕ} {U : Array N}
    (hbelow : ∀ y : ℤ, y ≤ recVal j (prefOf p m t U) →
      projH p m j t U y = SwarmOcc.Hpot (siteH p m j U) y)
    {y : ℤ} (hyr : y + 1 ≤ recVal j (prefOf p m t U))
    (hval : 0 ≤ y → hof p (siteMarks p m U j) y.toNat ≤ V) :
    |projH p m j t U (y + 1) - projH p m j t U y| ≤ V := by
  rw [hbelow (y + 1) hyr, hbelow y (by omega), Hpot_succ_sub' (h := siteH p m j U) y]
  by_cases hy0 : 0 ≤ y
  · have hz : hZpot (siteH p m j U) y = hof p (siteMarks p m U j) y.toNat := by
      rw [hZpot_of_nonneg hy0]
      rfl
    rw [hz, abs_of_nonneg (le_trans zero_le_one (one_le_hof hp1.le hp2 _ _))]
    exact hval hy0
  · have hz : hZpot (siteH p m j U) y = 1 := hZpot_of_nonpos (by omega)
    rw [hz, abs_one]
    exact hV1

/-- **The `nbT` envelope with no lower margin.** -/
theorem nbT_le_of_top_at {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} {i j : Fin N} {t : ℕ} {V : ℝ} (hV1 : 1 ≤ V) {M : ℕ} :
    ∀ᵐ U ∂(arrayMeasure N),
      (recVal j (prefOf p m t U)).toNat < 1 + M →
      (∀ y ∈ Finset.Ico 0 (1 + M), hof p (siteMarks p m U j) y ≤ V) →
      ((trajectory p m U t).pos i).toNat + 2 ≤ 1 + M →
      nbT p m i j t U ≤ envC p m V := by
  have hpne : p ≠ 0 := by linarith
  filter_upwards [ae_forall_projH_eq_Hpot_of_le_record (N := N) (p := p) hp1 hp2 hpne m t j,
    ae_forall_projH_closed_form (N := N) (p := p) hp1 hp2 m (n := t) j,
    eRec_zero_bounds_ae (N := N) (p := p) hp1 hp2 m (n := t) j] with U hbelow hcl hb
  intro hr hh hX
  have he1 : 0 ≤ eRec p m t j 0 U := le_trans zero_le_one hb.1
  have he2 : eRec p m t j 0 U ≤ bRec p m t j U := hb.2
  have hgood : HprevAt p m t j U ≤ V := HprevAt_le_of_top hp1 hp2 j hV1 hr hh
  have hbr : bRec p m t j U ≤ V + 2 := by
    simp only [bRec]; linarith
  have hLnn : 0 ≤ Lc p m := Lc_nonneg hp1 hp2 m
  set XX : ℤ := (trajectory p m U t).pos i with hXX
  set r : ℤ := recVal j (prefOf p m t U) with hrdef
  have hr0 : 0 ≤ r := hrdef ▸ zero_le_recVal_prefOf p m U j t
  have hrM : r < 1 + (M : ℤ) := by
    have hzn : ((r.toNat : ℕ) : ℤ) = r := Int.toNat_of_nonneg hr0
    have hlt : ((r.toNat : ℕ) : ℤ) < ((1 + M : ℕ) : ℤ) := by exact_mod_cast hr
    push_cast at hlt
    linarith
  by_cases hneg : XX < 0
  · -- the walker is strictly below the origin: both steps are exactly one
    have h1 : |projH p m j t U (XX + 1) - projH p m j t U XX| ≤ V :=
      abs_step_below_le_top hp1 hp2 hV1 (j := j) hbelow (y := XX) (by omega)
        (fun h0 => absurd h0 (by omega))
    have h2 : |projH p m j t U (XX - 1) - projH p m j t U XX| ≤ V := by
      have h := abs_step_below_le_top hp1 hp2 hV1 (j := j) hbelow (y := XX - 1) (by omega)
        (fun h0 => absurd h0 (by omega))
      rw [show XX - 1 + 1 = XX by ring] at h
      rw [abs_sub_comm]
      exact h
    have hsum : |projH p m j t U (XX + 1) - projH p m j t U XX|
        + |projH p m j t U (XX - 1) - projH p m j t U XX| ≤ envC p m V := by
      simp only [envC]; linarith
    simpa only [nbT, hXX] using hsum
  have hX0 : (0 : ℤ) ≤ XX := not_lt.mp hneg

  have hXn : ((XX.toNat : ℕ) : ℤ) = XX := Int.toNat_of_nonneg hX0
  have hX2 : (XX.toNat : ℤ) + 2 ≤ (1 : ℤ) + (M : ℤ) := by
    have : ((XX.toNat + 2 : ℕ) : ℤ) ≤ ((1 + M : ℕ) : ℤ) := by exact_mod_cast hX
    push_cast at this
    linarith
  have hmem : XX.toNat ∈ Finset.Ico 0 (1 + M) := by
    rw [Finset.mem_Ico]; omega
  have hvalX : 0 ≤ XX → hof p (siteMarks p m U j) XX.toNat ≤ V := fun _ => hh _ hmem
  have hvalX1 : 0 ≤ XX - 1 → hof p (siteMarks p m U j) (XX - 1).toNat ≤ V := by
    intro h0
    refine hh _ ?_
    rw [Finset.mem_Ico]
    have hcast : (((XX - 1).toNat : ℕ) : ℤ) = XX - 1 := Int.toNat_of_nonneg h0
    omega
  -- step 1: `X ↦ X + 1`
  have hstepA : |projH p m j t U (XX + 1) - projH p m j t U XX| ≤ V + 2 + 2 * Lc p m := by
    rcases lt_trichotomy XX r with hlt | heq | hgt
    · have h := abs_step_below_le_top hp1 hp2 hV1 (j := j) hbelow (y := XX) (by omega) hvalX
      linarith
    · rw [heq]
      rw [hcl (r + 1) 1 (by push_cast; ring), hcl r 0 (by push_cast; ring)]
      have hA1 : (1 - aRec p m ^ (1 : ℕ)) / (1 - aRec p m) = 1 := by
        rw [pow_one]
        exact div_self (ne_of_gt (one_sub_aRec_pos hp1 hp2 m))
      have hA0 : (1 - aRec p m ^ (0 : ℕ)) / (1 - aRec p m) = 0 := by
        rw [pow_zero, sub_self, zero_div]
      rw [hA1, hA0]
      have hsimp : (SwarmOcc.Hpot (siteH p m j U) r
            + ((1 : ℕ) : ℝ) * ((1 + aRec p m) / (1 - aRec p m))
            + (eRec p m t j 0 U - (1 + aRec p m) / (1 - aRec p m)) * 1)
          - (SwarmOcc.Hpot (siteH p m j U) r
            + ((0 : ℕ) : ℝ) * ((1 + aRec p m) / (1 - aRec p m))
            + (eRec p m t j 0 U - (1 + aRec p m) / (1 - aRec p m)) * 0)
          = eRec p m t j 0 U := by
        push_cast; ring
      rw [hsimp, abs_of_nonneg he1]
      linarith
    · have h := abs_step_above_le hp1 hp2 (m := m) (j := j) (t := t) (U := U)
        hcl he1 he2 (le_of_lt hgt)
      linarith
  -- step 2: `X - 1 ↦ X`
  have hstepB : |projH p m j t U (XX - 1) - projH p m j t U XX| ≤ V + 2 + 2 * Lc p m := by
    by_cases hle : XX ≤ r
    · have h := abs_step_below_le_top hp1 hp2 hV1 (j := j) hbelow (y := XX - 1) (by omega) hvalX1
      rw [show XX - 1 + 1 = XX by ring] at h
      rw [abs_sub_comm]
      linarith
    · have hgt : r < XX := not_le.mp hle
      have h := abs_step_above_le hp1 hp2 (m := m) (j := j) (t := t) (U := U)
        hcl he1 he2 (by omega : r ≤ XX - 1)
      rw [show XX - 1 + 1 = XX by ring] at h
      rw [abs_sub_comm] at h
      linarith
  have hsum : |projH p m j t U (XX + 1) - projH p m j t U XX|
      + |projH p m j t U (XX - 1) - projH p m j t U XX| ≤ envC p m V := by
    simp only [envC]
    linarith
  simpa only [nbT, hXX] using hsum

/-! ### 14. The origin-anchored residual: containment, split, and the crossing event -/

/-- The **origin-anchored window event**: the record of `j` and walker `i` stay below the top
`1+M`, and `h_j ≤ V` on the site window `[0, 1+M)`.  No lower margin appears. -/
def topWindow (p : ℝ) (m : ℕ) (i j : Fin N) (V : ℝ) (M K : ℕ) : Set (Array N) :=
  {U | (∀ k < K, (recVal j (prefOf p m k U)).toNat < 1 + M) ∧
    (∀ y ∈ Finset.Ico 0 (1 + M), hof p (siteMarks p m U j) y ≤ V) ∧
    (∀ k < K, ((trajectory p m U k).pos i).toNat + 2 ≤ 1 + M)}

theorem ae_forall_nbT_le_of_top {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} {i j : Fin N} {K : ℕ} {V : ℝ} (hV1 : 1 ≤ V) {M : ℕ} :
    ∀ᵐ U ∂(arrayMeasure N), ∀ k : ℕ, k < K →
      (recVal j (prefOf p m k U)).toNat < 1 + M →
      (∀ y ∈ Finset.Ico 0 (1 + M), hof p (siteMarks p m U j) y ≤ V) →
      ((trajectory p m U k).pos i).toNat + 2 ≤ 1 + M →
      nbT p m i j k U ≤ envC p m V :=
  MeasureTheory.ae_all_iff.mpr fun k =>
    (nbT_le_of_top_at (N := N) (p := p) hp1 hp2 (m := m) (i := i) (j := j) (t := k) hV1
      (M := M)).mono (fun U hU _hk hr hh hX => hU hr hh hX)

/-- **The origin-anchored window implies the carrier at every time of the horizon.** -/
theorem ae_topWindow_subset_carrier {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} {i j : Fin N} {K : ℕ} {V : ℝ} (hV1 : 1 ≤ V) {M : ℕ} :
    ∀ᵐ U ∂(arrayMeasure N), U ∈ topWindow p m i j V M K →
      ∀ k < K, U ∈ qplCarrier (N := N) p m i j V (envC p m V) k := by
  filter_upwards [ae_forall_nbT_le_of_top (N := N) (p := p) hp1 hp2 (m := m) (i := i) (j := j)
    (K := K) (V := V) hV1 (M := M)] with U hnb hW k hk
  obtain ⟨hrec, hh, hX⟩ := hW
  refine ⟨?_, hnb k hk (hrec k hk) hh (hX k hk)⟩
  -- `siteGood k`, from the record's upper bound and the window
  have hHz : (recVal j (prefOf p m k U)).toNat < 1 + M := hrec k hk
  rcases Nat.eq_zero_or_pos ((recVal j (prefOf p m k U)).toNat) with h0 | hpos
  · show HprevAt p m k j U ≤ V
    rw [HprevAt_of_zero p m k j U h0]
    exact hV1
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
      (by omega : (recVal j (prefOf p m k U)).toNat ≠ 0)
    show HprevAt p m k j U ≤ V
    rw [HprevAt_of_succ p m k j U n hn]
    refine hh n ?_
    rw [Finset.mem_Ico]
    omega

/-- The **top-crossing defect**: the record of `j` or the position of walker `i` reaches the top
`1+M` of the origin-anchored window. -/
def topDefect (p : ℝ) (m : ℕ) (i j : Fin N) (M K : ℕ) : Set (Array N) :=
  {U | (∃ k < K, 1 + M ≤ (recVal j (prefOf p m k U)).toNat) ∨
      (∃ k < K, 1 + M < ((trajectory p m U k).pos i).toNat + 2)}

/-- The **harmonic defect on the origin-anchored window**. -/
def harmDefectTop (p : ℝ) (m : ℕ) (j : Fin N) (V : ℝ) (M : ℕ) : Set (Array N) :=
  {U | ¬ ∀ y ∈ Finset.Ico 0 (1 + M), hof p (siteMarks p m U j) y ≤ V}

theorem not_mem_topWindow_subset {p : ℝ} {m : ℕ} {i j : Fin N} {V : ℝ} {M K : ℕ} :
    {U : Array N | ¬ U ∈ topWindow p m i j V M K}
      ⊆ topDefect p m i j M K ∪ harmDefectTop p m j V M := by
  intro U hU
  simp only [topWindow, Set.mem_ofPred_eq] at hU
  simp only [topDefect, harmDefectTop, Set.mem_union, Set.mem_ofPred_eq]
  rcases not_and_or.mp hU with hA | hBC
  · left; left
    obtain ⟨k, hk⟩ := not_forall.mp hA
    obtain ⟨hkK, hkP⟩ := Classical.not_imp.mp hk
    exact ⟨k, hkK, not_lt.mp hkP⟩
  · rcases not_and_or.mp hBC with hB | hC
    · right; exact hB
    · left; right
      obtain ⟨k, hk⟩ := not_forall.mp hC
      obtain ⟨hkK, hkP⟩ := Classical.not_imp.mp hk
      exact ⟨k, hkK, not_le.mp hkP⟩

/-- **The residual probability splits into the top-crossing event and the harmonic defect.** -/
theorem measure_residual_top_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} {i j : Fin N} {K : ℕ} {V : ℝ} (hV1 : 1 ≤ V) {M : ℕ} :
    (arrayMeasure N).real {U | ∃ k < K,
        U ∉ qplCarrier (N := N) p m i j V (envC p m V) k}
      ≤ (arrayMeasure N).real (topDefect p m i j M K)
        + (arrayMeasure N).real (harmDefectTop p m j V M) := by
  have hsub : {U : Array N | ∃ k < K, U ∉ qplCarrier (N := N) p m i j V (envC p m V) k}
      ≤ᵐ[arrayMeasure N] (topDefect p m i j M K ∪ harmDefectTop p m j V M : Set (Array N)) := by
    filter_upwards [ae_topWindow_subset_carrier (N := N) (p := p) hp1 hp2 (m := m) (i := i)
      (j := j) (K := K) (V := V) hV1 (M := M)] with U hU hmem
    obtain ⟨k, hk, hkc⟩ := hmem
    exact not_mem_topWindow_subset (fun hW => absurd (hU hW k hk) hkc)
  have h1 : arrayMeasure N {U : Array N | ∃ k < K,
        U ∉ qplCarrier (N := N) p m i j V (envC p m V) k}
      ≤ arrayMeasure N (topDefect p m i j M K ∪ harmDefectTop p m j V M) :=
    measure_mono_ae hsub
  refine le_trans ?_ (measureReal_union_le (topDefect p m i j M K) (harmDefectTop p m j V M))
  rw [Measure.real_def, Measure.real_def]
  exact ENNReal.toReal_mono (measure_ne_top _ _) h1

/-- **The top-crossing event cannot come from the initial condition**: at time `0` the record and
every position are `0`, so for `1 ≤ M` the time-`0` instance of `topDefect` is false.  This is the
quantitative form of the repair: with the window anchored at the origin the start event is
*automatic*, not empty-because-vacuous. -/
theorem not_topDefect_zero {p : ℝ} {m : ℕ} {i j : Fin N} {M K : ℕ} (hM : 1 ≤ M) (U : Array N) :
    ¬ (1 + M ≤ (recVal j (prefOf p m 0 U)).toNat ∨
        1 + M < ((trajectory p m U 0).pos i).toNat + 2) := by
  have h1 : recVal j (prefOf p m 0 U) = 0 := recVal_zero p m U j
  have h2 : (trajectory p m U 0).pos i = 0 := pos_zero p m U i
  rintro (h | h)
  · rw [h1] at h
    simp only [Int.toNat_zero] at h
    omega
  · rw [h2] at h
    simp only [Int.toNat_zero] at h
    omega

/-- The time-`0` part of the origin-anchored window holds for **every** `U` as soon as `1 ≤ M`. -/
theorem topWindow_start {p : ℝ} {m : ℕ} {i j : Fin N} {V : ℝ} {M : ℕ} (hM : 1 ≤ M) (U : Array N) :
    (recVal j (prefOf p m 0 U)).toNat < 1 + M ∧
      ((trajectory p m U 0).pos i).toNat + 2 ≤ 1 + M := by
  have h1 : recVal j (prefOf p m 0 U) = 0 := recVal_zero p m U j
  have h2 : (trajectory p m U 0).pos i = 0 := pos_zero p m U i
  rw [h1, h2]
  simp only [Int.toNat_zero]
  omega

theorem harmDefectTop_subset_HMaxBadW (p : ℝ) (m : ℕ) (j : Fin N) {M L : ℕ} :
    harmDefectTop p m j (LocSumAct.xOf L) M
      ⊆ {U : Array N | WideRepair.HMaxBadW p m L 1 M 1 U} := by
  intro U hU
  simp only [harmDefectTop, Set.mem_ofPred_eq, WideRepair.HMaxBadW] at hU ⊢
  push Not at hU
  obtain ⟨y, hy, hgt⟩ := hU
  exact ⟨j, y, hy, le_of_lt hgt⟩

/-- **The harmonic defect on the origin-anchored window is `exp(-c L^{1/16})`**, again by the
accepted `WideRepair.array_locmax_bound_paper_window` (now at the anchor `A = 1`, which is allowed
because `HMaxBadW` needs only `M' = 1 ≤ A`). -/
theorem measure_harmDefectTop_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (j : Fin N) (T : ℕ) (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ M : ℕ, 1 + M ≤ 2 * (T + 3) * L →
      (arrayMeasure N).real (harmDefectTop p m j (LocSumAct.xOf L) M)
        ≤ Real.exp (-c * LocSumAct.xOf L) := by
  obtain ⟨c, hc, L₀, hL0⟩ :=
    WideRepair.array_locmax_bound_paper_window (N := N) (p := p) hp1 hp2 hm T hT
  refine ⟨c, hc, L₀, ?_⟩
  intro L hL M hMUp
  have hmono : arrayMeasure N (harmDefectTop p m j (LocSumAct.xOf L) M)
      ≤ arrayMeasure N {U : Array N | WideRepair.HMaxBadW p m L 1 M 1 U} :=
    measure_mono (harmDefectTop_subset_HMaxBadW (N := N) p m j (M := M) (L := L))
  have hb := hL0 L hL 1 1 M (le_refl 1) hMUp
  rw [Measure.real_def]
  calc ((arrayMeasure N) (harmDefectTop p m j (LocSumAct.xOf L) M)).toReal
      ≤ ((arrayMeasure N) {U : Array N | WideRepair.HMaxBadW p m L 1 M 1 U}).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) hmono
    _ ≤ (ENNReal.ofReal (Real.exp (-c * LocSumAct.xOf L))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    _ = Real.exp (-c * LocSumAct.xOf L) := ENNReal.toReal_ofReal (Real.exp_pos _).le

/-! ### 15. The paper-scale bound with the origin-anchored residual -/

/-- **The `Qpl` maximal bound at the paper's scale with the origin-anchored residual.**

  `μ.real {∃ k ≤ T*L, L^{3/4} ≤ |Qpl_k|}`
  `  ≤ 2 (T L + 1) exp (-V^8/(4 T (KepW (V+2))^2))`
  `    + μ.real (topDefect p m i j M (T*L)) + exp (-c V)`,   `V = xOf L`,

where the only geometric event is the **top crossing** of the record of `j` or of the position of
walker `i`, and the only harmonic event is `h_j > V` somewhere on `[0, 1+M)`.  No lower margin
appears, and the time-`0` configuration satisfies the window's positional conditions for *every*
`U` (`topWindow_start`), so the residual is not polluted by the (deterministic) initial state. -/
theorem qpl_measure_max_abs_le_of_top_scale {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) {i j : Fin N} (hij : i ≠ j) {eps : ℝ} (hε : 0 < eps)
    {T : ℕ} (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ M : ℕ, 1 ≤ M →
      1 + M ≤ 2 * (T + 3) * L →
      (arrayMeasure N).real
          {U | ∃ k ≤ T * L, (L : ℝ) ^ (3 / 4 : ℝ) ≤ |ProjLedger.Qpl p m eps i j k U|}
        ≤ 2 * (((T * L : ℕ) : ℝ) + 1)
              * Real.exp (-((LocSumAct.xOf L) ^ 8 /
                  (4 * (T : ℝ) * (KepW p m * (LocSumAct.xOf L + 2)) ^ 2)))
          + (arrayMeasure N).real (topDefect p m i j M (T * L))
          + Real.exp (-c * LocSumAct.xOf L) := by
  obtain ⟨c, hc, L₀, hL0⟩ := measure_harmDefectTop_le (N := N) (p := p) hp0 hp1 hm j T hT
  refine ⟨c, hc, max L₀ 1, ?_⟩
  intro L hL M hM1 hMUp
  have hL0' : L₀ ≤ L := le_trans (le_max_left _ _) hL
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  have hLr : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL1)
  have hV1 : (1 : ℝ) ≤ LocSumAct.xOf L := LocSumAct.one_le_xOf hL1
  have hV0 : (0 : ℝ) < LocSumAct.xOf L := lt_of_lt_of_le zero_lt_one hV1
  have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  have hTL : 1 ≤ T * L :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hmain := qpl_measure_max_abs_le_of_small_carrier (N := N) (m := m) hp0 hp1 hij hε
    (V := LocSumAct.xOf L) (c := envC p m (LocSumAct.xOf L)) hV0.le
    (envC_nonneg hp0 hp1 m hV0.le) (n := T * L) hTL
    (ε := (L : ℝ) ^ (3 / 4 : ℝ)) (Real.rpow_pos_of_pos hLr _)
  have hres := measure_residual_top_le (N := N) (p := p) hp0 hp1 (m := m) (i := i) (j := j)
    (K := T * L) (V := LocSumAct.xOf L) hV1 (M := M)
  have hharm := hL0 L hL0' M hMUp
  have hexp : 2 * (((T * L : ℕ) : ℝ) + 1)
        * Real.exp (-((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2
            / (4 * ((T * L : ℕ) : ℝ)
                * (envB p m (LocSumAct.xOf L) (envC p m (LocSumAct.xOf L))) ^ 2))
      ≤ 2 * (((T * L : ℕ) : ℝ) + 1)
        * Real.exp (-((LocSumAct.xOf L) ^ 8 /
            (4 * (T : ℝ) * (KepW p m * (LocSumAct.xOf L + 2)) ^ 2))) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Real.exp_le_exp.mpr ?_
    have hεeq : (L : ℝ) ^ (3 / 4 : ℝ) = (LocSumAct.xOf L) ^ 12 :=
      (LocMoveLocal.xOf_pow_twelve L).symm
    have hVpow : (LocSumAct.xOf L) ^ 16 = (L : ℝ) := LocSumAct.xOf_pow L
    have henv : envB p m (LocSumAct.xOf L) (envC p m (LocSumAct.xOf L))
        ≤ KepW p m * (LocSumAct.xOf L + 2) := envB_envC_le_kepW hp0 hp1 m hV1
    have henv0 : 0 ≤ envB p m (LocSumAct.xOf L) (envC p m (LocSumAct.xOf L)) :=
      (envB_pos hp0 hp1 m hV0.le (envC_nonneg hp0 hp1 m hV0.le)).le
    have henv2 : (envB p m (LocSumAct.xOf L) (envC p m (LocSumAct.xOf L))) ^ 2
        ≤ (KepW p m * (LocSumAct.xOf L + 2)) ^ 2 :=
      pow_le_pow_left₀ henv0 henv 2
    rw [hεeq, Nat.cast_mul, ← hVpow]
    have heB : 0 < envB p m (LocSumAct.xOf L) (envC p m (LocSumAct.xOf L)) :=
      envB_pos hp0 hp1 m hV0.le (envC_nonneg hp0 hp1 m hV0.le)
    have hstep : (LocSumAct.xOf L) ^ 8
          / (4 * (T : ℝ) * (KepW p m * (LocSumAct.xOf L + 2)) ^ 2)
        ≤ ((LocSumAct.xOf L) ^ 12) ^ 2
          / (4 * ((T : ℝ) * (LocSumAct.xOf L) ^ 16)
              * (envB p m (LocSumAct.xOf L) (envC p m (LocSumAct.xOf L))) ^ 2) := by
      have heq : ((LocSumAct.xOf L) ^ 12) ^ 2
            / (4 * ((T : ℝ) * (LocSumAct.xOf L) ^ 16)
                * (envB p m (LocSumAct.xOf L) (envC p m (LocSumAct.xOf L))) ^ 2)
          = (LocSumAct.xOf L) ^ 8
            / (4 * (T : ℝ)
                * (envB p m (LocSumAct.xOf L) (envC p m (LocSumAct.xOf L))) ^ 2) := by
        have h1 : ((LocSumAct.xOf L) ^ 12) ^ 2
            = (LocSumAct.xOf L) ^ 16 * (LocSumAct.xOf L) ^ 8 := by ring
        have h2 : 4 * ((T : ℝ) * (LocSumAct.xOf L) ^ 16)
              * (envB p m (LocSumAct.xOf L) (envC p m (LocSumAct.xOf L))) ^ 2
            = (LocSumAct.xOf L) ^ 16
              * (4 * (T : ℝ)
                * (envB p m (LocSumAct.xOf L) (envC p m (LocSumAct.xOf L))) ^ 2) := by ring
        rw [h1, h2]
        exact mul_div_mul_left _ _ (by positivity : (LocSumAct.xOf L) ^ 16 ≠ 0)
      rw [heq]
      refine div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ (LocSumAct.xOf L) ^ 8)
        (by positivity) ?_
      exact mul_le_mul_of_nonneg_left henv2 (by positivity)
    have := neg_le_neg hstep
    simpa only [neg_div] using this
  linarith [hexp, hres, hharm]

end QplWindow
