/-  `ProjHRecord` (accepted, `Swarm/ProjHRecord.lean`) proves the paper's display
  `(projH)` at the actual random record for every fixed time `n`, and the increment bound in the
  case `M_{n+1}^j = M_n^j`.  It leaves open the **advancing** case `M_{n+1}^j = M_n^j + 1`,
  where the two closed forms live at different records.

  The observation driving this file: the advancing increment *identity* needs no conditional
  independence of the fresh mark.  Each closed form is an identity at its own time, and the only
  extra input is the deterministic identity

      H_j(r_n + 1) = H_j(r_n) + h_j(r_n)

  (`Hpot_record_add` at `g = 1`), together with the deterministic fact that the record advances by
  at most one per step (`recVal_succ_le`, proved here from `StepCross.pos_succ_eq_or`).

  Contents:
  * `recVal_le_succ`, `recVal_succ_le`, `recVal_succ_eq_or` — the deterministic record step;
  * `projH_increment_advance` — the paper's increment identity on `{M_{n+1}^j = M_n^j + 1}` for
    `y = M_n^j + (g+1)`, in terms of `e_0^{(n)}`, `e_0^{(n+1)}` and `h_j(M_n^j)`;
  * `abs_projH_increment_advance_le` — its two-sided envelope;
  * `abs_projH_increment_le` / `abs_projH_increment_le_ae_all` — the **complete** pathwise
    envelope `|H_{j,n+1}(y) - H_{j,n}(y)| ≤ C(a)(1 + b_n + b_{n+1})` for every site `y`,
    with no case hypothesis;
  * `abs_projH_spatial_le` — the spatial (one-site) increment of the projected potential, same
    constant shape, which is the other half of the one-step ledger derivative.

  No proof holes, no custom axiom, no decision-based proof obligations.
-/
import Swarm.ProjHRecord
import Swarm.RawSecondMoment

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross

variable {N : ℕ}

/-! ### 1. The deterministic record step: `M_n^j ≤ M_{n+1}^j ≤ M_n^j + 1` -/

/-- The running maximum of walker `j`'s positions, in the `Finset.sup'` normal form used by
`recVal` (with the canonical nonemptiness witness, so that it rewrites cleanly). -/
noncomputable def recMax (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (n : ℕ) : ℤ :=
  (Finset.range (n + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩
    (fun t => (trajectory p m U t).pos j)

/-- `recMax` is the record read off the position prefix. -/
theorem recMax_eq_recVal (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (n : ℕ) :
    recMax p m U j n = recVal j (prefOf p m n U) := by
  unfold recMax recVal
  refine Finset.sup'_congr _ rfl (fun t ht => ?_)
  exact (ext_prefOf U (by simpa using ht) j).symm

/-- The running record never decreases. -/
theorem recVal_le_succ (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (n : ℕ) :
    recVal j (prefOf p m n U) ≤ recVal j (prefOf p m (n + 1) U) := by
  rw [← recMax_eq_recVal, ← recMax_eq_recVal]
  unfold recMax
  refine Finset.sup'_le _ _ (fun t ht => ?_)
  have ht' : t ≤ n := by simpa using ht
  exact Finset.le_sup' (f := fun t => (trajectory p m U t).pos j)
    (Finset.mem_range.mpr (by omega))

/-- The running record advances by at most one per step. -/
theorem recVal_succ_le (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (n : ℕ) :
    recVal j (prefOf p m (n + 1) U) ≤ recVal j (prefOf p m n U) + 1 := by
  rw [← recMax_eq_recVal, ← recMax_eq_recVal]
  unfold recMax
  refine Finset.sup'_le _ _ (fun t ht => ?_)
  have ht2 : t ≤ n + 1 := by simpa using ht
  have hle : (trajectory p m U n).pos j
      ≤ (Finset.range (n + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩
          (fun t => (trajectory p m U t).pos j) :=
    Finset.le_sup' (f := fun t => (trajectory p m U t).pos j)
      (Finset.mem_range.mpr (Nat.lt_succ_self n))
  rcases Nat.lt_or_ge t (n + 1) with hlt | hge
  · have hle' : (trajectory p m U t).pos j
        ≤ (Finset.range (n + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩
            (fun t => (trajectory p m U t).pos j) :=
      Finset.le_sup' (f := fun t => (trajectory p m U t).pos j)
        (Finset.mem_range.mpr hlt)
    linarith
  · have ht' : t = n + 1 := by omega
    subst ht'
    rcases StepCross.pos_succ_eq_or p m U n j with h | h <;> rw [h] <;> linarith

/-- **The record is either unchanged or advances by exactly one.** -/
theorem recVal_succ_eq_or (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (n : ℕ) :
    recVal j (prefOf p m (n + 1) U) = recVal j (prefOf p m n U) ∨
      recVal j (prefOf p m (n + 1) U) = recVal j (prefOf p m n U) + 1 := by
  have h1 := recVal_le_succ p m U j n
  have h2 := recVal_succ_le p m U j n
  omega

/-! ### 2. Elementary facts about the above-record coefficients

`L = (1+a)/(1-a)` is the drift slope, `K = 1/(1-a)` the geometric normaliser, and
`A_k = (1-a^k)/(1-a)` the geometric correction factor.  All that the envelope needs is
`0 < L ≤ 2K`, `0 ≤ A_k ≤ K` and `A_{k+1} - A_k = a^k ≤ 1`. -/

/-- `1 - a > 0`. -/
theorem one_sub_aRec_pos {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) :
    0 < 1 - aRec p m := by
  have := aRec_lt_one hp1 hp2 m
  linarith

/-- The geometric correction factor is nonnegative. -/
theorem projA_nonneg {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) (k : ℕ) :
    0 ≤ (1 - aRec p m ^ k) / (1 - aRec p m) := by
  have ha0 : 0 ≤ aRec p m := zero_le_aRec hp1 hp2 m
  have ha1 : aRec p m < 1 := aRec_lt_one hp1 hp2 m
  have hp : aRec p m ^ k ≤ 1 := pow_le_one₀ ha0 (le_of_lt ha1)
  have hk : (0 : ℝ) ≤ aRec p m ^ k := pow_nonneg ha0 k
  exact div_nonneg (by linarith) (le_of_lt (one_sub_aRec_pos hp1 hp2 m))

/-- The geometric correction factor is at most `K = 1/(1-a)`. -/
theorem projA_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) (k : ℕ) :
    (1 - aRec p m ^ k) / (1 - aRec p m) ≤ (1 - aRec p m)⁻¹ := by
  have ha0 : 0 ≤ aRec p m := zero_le_aRec hp1 hp2 m
  have hp : aRec p m ^ k ≤ 1 := pow_le_one₀ ha0 (le_of_lt (aRec_lt_one hp1 hp2 m))
  have hk : (0 : ℝ) ≤ aRec p m ^ k := pow_nonneg ha0 k
  have hinv : (0 : ℝ) ≤ (1 - aRec p m)⁻¹ :=
    le_of_lt (inv_pos.mpr (one_sub_aRec_pos hp1 hp2 m))
  rw [div_eq_mul_inv]
  calc (1 - aRec p m ^ k) * (1 - aRec p m)⁻¹ ≤ 1 * (1 - aRec p m)⁻¹ :=
        mul_le_mul_of_nonneg_right (by linarith) hinv
    _ = (1 - aRec p m)⁻¹ := one_mul _

/-- The drift slope is positive. -/
theorem projL_pos {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) :
    0 < (1 + aRec p m) / (1 - aRec p m) := by
  have ha0 : 0 ≤ aRec p m := zero_le_aRec hp1 hp2 m
  exact div_pos (by linarith) (one_sub_aRec_pos hp1 hp2 m)

/-- The drift slope is at most `2K`. -/
theorem projL_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) :
    (1 + aRec p m) / (1 - aRec p m) ≤ 2 * (1 - aRec p m)⁻¹ := by
  have ha0 : 0 ≤ aRec p m := zero_le_aRec hp1 hp2 m
  have ha1 : aRec p m < 1 := aRec_lt_one hp1 hp2 m
  have hinv : (0 : ℝ) ≤ (1 - aRec p m)⁻¹ :=
    le_of_lt (inv_pos.mpr (one_sub_aRec_pos hp1 hp2 m))
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (by linarith) hinv

/-- The one-site difference of the geometric factor: `A_{k+1} - A_k = a^k`. -/
theorem projA_succ_sub {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) (k : ℕ) :
    (1 - aRec p m ^ (k + 1)) / (1 - aRec p m) - (1 - aRec p m ^ k) / (1 - aRec p m)
      = aRec p m ^ k := by
  have hden : (1 - aRec p m) ≠ 0 := ne_of_gt (one_sub_aRec_pos hp1 hp2 m)
  rw [div_sub_div_same]
  field_simp
  ring

/-! ### 3. The advancing-record increment identity -/

/-- **The revealing identity at a `+1` advance**: when the record advances by one, the quenched
potential at the new record is the old record value plus the mark `h_j(M_n^j)` at the old record. -/
theorem Hpot_record_succ (p : ℝ) (m n : ℕ) (j : Fin N) (U : Array N)
    (h : recVal j (prefOf p m (n + 1) U) = recVal j (prefOf p m n U) + 1) :
    SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m (n + 1) U))
      = SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m n U)) + H0 p m n j U := by
  have h1z : ((1 : ℕ) : ℤ) = (1 : ℤ) := by norm_num
  rw [h]
  simp only [siteH_def]
  rw [← h1z, Hpot_record_add, Finset.sum_range_one]
  simp [H0]

/-- **The paper's projected-potential increment identity in the advancing case.**

On `{M_{n+1}^j = M_n^j + 1}`, for the site `y = M_n^j + (g+1)`, the two closed forms
`(projH)` at `n` and at `n+1` differ by

    H_{j,n+1}(y) - H_{j,n}(y)
      = h_j(M_n^j) - (1+a)/(1-a)
        + (e_0^{(n+1)} - (1+a)/(1-a)) A_g - (e_0^{(n)} - (1+a)/(1-a)) A_{g+1},

with `A_k = (1-a^k)/(1-a)`.  No conditional independence of the fresh mark is used: the record
increment contributes exactly `H_j(M_n^j + 1) - H_j(M_n^j) = h_j(M_n^j)` (`Hpot_record_succ`), and
each projected value is computed at its own time from `(projH)`. -/
theorem projH_increment_advance {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ)
    {n : ℕ} (j : Fin N) (y : ℤ) (g : ℕ) :
    ∀ᵐ U ∂(arrayMeasure N),
      recVal j (prefOf p m (n + 1) U) = recVal j (prefOf p m n U) + 1 →
      y = recVal j (prefOf p m n U) + ((g + 1 : ℕ) : ℤ) →
      projH p m j (n + 1) U y - projH p m j n U y
        = H0 p m n j U - (1 + aRec p m) / (1 - aRec p m)
          + (eRec p m (n + 1) j 0 U - (1 + aRec p m) / (1 - aRec p m))
              * ((1 - aRec p m ^ g) / (1 - aRec p m))
          - (eRec p m n j 0 U - (1 + aRec p m) / (1 - aRec p m))
              * ((1 - aRec p m ^ (g + 1)) / (1 - aRec p m)) := by
  filter_upwards [ae_forall_projH_closed_form (p := p) hp1 hp2 m (n := n) j,
    ae_forall_projH_closed_form (p := p) hp1 hp2 m (n := n + 1) j] with U hcl hcl1
  intro hadv hy
  have h1 := hcl y (g + 1) hy
  have hy2 : y = recVal j (prefOf p m (n + 1) U) + (g : ℤ) := by
    rw [hadv, hy]
    push_cast
    ring
  have h2 := hcl1 y g hy2
  have hH := Hpot_record_succ p m n j U hadv
  have hpow : aRec p m ^ (g + 1) = aRec p m ^ g * aRec p m := pow_succ _ _
  rw [h2, h1, hH, hpow]
  push_cast
  ring

/-- **The advancing case at the old record itself** (`y = M_n^j`): the site is strictly below the
new record, so both projections are the revealed value and the increment vanishes. -/
theorem projH_increment_advance_zero {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ)
    {n : ℕ} (j : Fin N) (y : ℤ) :
    ∀ᵐ U ∂(arrayMeasure N),
      recVal j (prefOf p m (n + 1) U) = recVal j (prefOf p m n U) + 1 →
      y = recVal j (prefOf p m n U) →
      projH p m j (n + 1) U y - projH p m j n U y = 0 := by
  filter_upwards [ae_forall_projH_closed_form (p := p) hp1 hp2 m (n := n) j,
    ae_forall_projH_eq_Hpot_of_le_record (p := p) hp1 hp2 (by linarith) m (n + 1) j]
    with U hcl hbelow
  intro hadv hy
  have h1 := hcl y 0 (by rw [hy]; push_cast; ring)
  have h2 : y ≤ recVal j (prefOf p m (n + 1) U) := by
    rw [hadv, hy]
    omega
  rw [hbelow y h2, h1, hy]
  norm_num

/-! ### 4. The arithmetic core of the advancing envelope -/

/-- **Arithmetic core.**  With `0 ≤ A_g ≤ K`, `0 ≤ A_{g+1} ≤ K`, `A_{g+1} - A_g = c ∈ [0,1]`,
`0 < L ≤ 2K`, `1 ≤ H_0 ≤ b`, `1 ≤ e ≤ b` and `1 ≤ e' ≤ b'`, the advancing increment

    Δ = H_0 - L + (e' - L) A_g - (e - L) A_{g+1}

satisfies `|Δ| ≤ (2K+2)(1 + b + b')`.  The two-sided bound is what the second-moment estimate
needs; no sharpness is claimed. -/
lemma abs_envelope_core {H0v bb bb' e e' L K Ag Ag1 cc : ℝ}
    (hH01 : 1 ≤ H0v) (hH0b : H0v ≤ bb)
    (he1 : 1 ≤ e) (heb : e ≤ bb) (he1' : 1 ≤ e') (heb' : e' ≤ bb')
    (hAg0 : 0 ≤ Ag) (hAgK : Ag ≤ K) (hAg1_0 : 0 ≤ Ag1) (hAg1K : Ag1 ≤ K)
    (hcc0 : 0 ≤ cc) (hcc1 : cc ≤ 1) (hdiff : Ag1 - Ag = cc)
    (hL0 : 0 < L) (hLK : L ≤ 2 * K)
    (hb0 : 0 ≤ bb) (hb0' : 0 ≤ bb') (hK0 : 0 ≤ K) :
    |H0v - L + (e' - L) * Ag - (e - L) * Ag1| ≤ (2 * K + 2) * (1 + bb + bb') := by
  have hid : H0v - L + (e' - L) * Ag - (e - L) * Ag1
      = H0v + e' * Ag - e * Ag1 + L * cc - L := by
    rw [← hdiff]; ring
  rw [hid]
  have hprod : e' * Ag ≤ bb' * K := by
    have h := mul_le_mul heb' hAgK hAg0 hb0'
    linarith [h]
  have hprod2 : e * Ag1 ≤ bb * K := by
    have h := mul_le_mul heb hAg1K hAg1_0 hb0
    linarith [h]
  have hcross : 0 ≤ e * Ag1 := mul_nonneg (by linarith) hAg1_0
  have hcross2 : 0 ≤ e' * Ag := mul_nonneg (by linarith) hAg0
  have hLc : L * cc ≤ L := by
    have h := mul_le_of_le_one_right (le_of_lt hL0) hcc1
    linarith [h]
  have hLc0 : 0 ≤ L * cc := mul_nonneg (le_of_lt hL0) hcc0
  have hup : H0v + e' * Ag - e * Ag1 + L * cc - L ≤ bb + bb' * K := by
    linarith [hprod, hcross, hLc, hH0b]
  have hlow : (1 : ℝ) - bb * K - 2 * K ≤ H0v + e' * Ag - e * Ag1 + L * cc - L := by
    linarith [hprod2, hcross2, hLc0, hH01, hLK]
  refine abs_le.mpr ⟨?_, ?_⟩
  · nlinarith [hprod2, hprod, mul_nonneg hK0 hb0, mul_nonneg hK0 hb0', mul_nonneg hb0 hb0',
      hcc0, hK0]
  · nlinarith [hprod2, hprod, mul_nonneg hK0 hb0, mul_nonneg hK0 hb0', mul_nonneg hb0 hb0',
      hcc0, hK0]

/-! ### 5. The advancing envelope at the actual model -/

/-- **The projected-potential increment envelope in the advancing case.**  On
`{M_{n+1}^j = M_n^j + 1}`, at the site `y = M_n^j + (g+1)`,

    |H_{j,n+1}(y) - H_{j,n}(y)| ≤ (2/(1-a) + 2) (1 + b_n + b_{n+1}).

The constant is explicit and depends only on the model parameters; both record costs appear
because `b_{n+1}` bounds `e_0^{(n+1)}`. -/
theorem abs_projH_increment_advance_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ)
    {n : ℕ} (j : Fin N) (y : ℤ) (g : ℕ) :
    ∀ᵐ U ∂(arrayMeasure N),
      recVal j (prefOf p m (n + 1) U) = recVal j (prefOf p m n U) + 1 →
      y = recVal j (prefOf p m n U) + ((g + 1 : ℕ) : ℤ) →
      |projH p m j (n + 1) U y - projH p m j n U y|
        ≤ (2 * (1 - aRec p m)⁻¹ + 2)
            * (1 + bRec p m n j U + bRec p m (n + 1) j U) := by
  filter_upwards [projH_increment_advance (p := p) hp1 hp2 m (n := n) j y g,
    eRec_zero_bounds_ae (p := p) hp1 hp2 m (n := n) j,
    eRec_zero_bounds_ae (p := p) hp1 hp2 m (n := n + 1) j] with U hid hb hb'
  intro hadv hy
  obtain ⟨he1, he2⟩ := hb
  obtain ⟨he1', he2'⟩ := hb'
  have ha0 : 0 ≤ aRec p m := zero_le_aRec hp1 hp2 m
  have ha1 : aRec p m < 1 := aRec_lt_one hp1 hp2 m
  have hK0 : 0 ≤ (1 - aRec p m)⁻¹ :=
    le_of_lt (inv_pos.mpr (one_sub_aRec_pos hp1 hp2 m))
  have hH01 : 1 ≤ H0 p m n j U := by
    rw [H0_def]
    exact SwarmMarks.one_le_hof hp1.le hp2 (SwarmLogRatio.siteMarks p m U j) _
  have hH0b : H0 p m n j U ≤ bRec p m n j U := by
    have h := H0_le_HprevAt_add_two hp1 hp2 m n j U
    simpa [bRec] using h
  have hb0 : 0 ≤ bRec p m n j U := by
    linarith [three_le_bRec hp1 hp2 m n j U]
  have hb0' : 0 ≤ bRec p m (n + 1) j U := by
    linarith [three_le_bRec hp1 hp2 m (n + 1) j U]
  have hcc0 : 0 ≤ aRec p m ^ g := pow_nonneg ha0 g
  have hcc1 : aRec p m ^ g ≤ 1 := pow_le_one₀ ha0 (le_of_lt ha1)
  rw [hid hadv hy]
  exact abs_envelope_core hH01 hH0b he1 he2 he1' he2'
    (projA_nonneg hp1 hp2 m g) (projA_le hp1 hp2 m g)
    (projA_nonneg hp1 hp2 m (g + 1)) (projA_le hp1 hp2 m (g + 1))
    hcc0 hcc1 (projA_succ_sub hp1 hp2 m g)
    (projL_pos hp1 hp2 m) (projL_le hp1 hp2 m)
    hb0 hb0' hK0

/-- **All record cases, above the record.**  For the site `y = M_n^j + (g+1)` (strictly above the
record at time `n`), the same envelope holds whichever way the record moves. -/
theorem abs_projH_increment_le_above {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ)
    {n : ℕ} (j : Fin N) (y : ℤ) (g : ℕ) :
    ∀ᵐ U ∂(arrayMeasure N),
      y = recVal j (prefOf p m n U) + ((g + 1 : ℕ) : ℤ) →
      |projH p m j (n + 1) U y - projH p m j n U y|
        ≤ (2 * (1 - aRec p m)⁻¹ + 2)
            * (1 + bRec p m n j U + bRec p m (n + 1) j U) := by
  filter_upwards [abs_projH_increment_advance_le (p := p) hp1 hp2 m (n := n) j y g,
    abs_projH_increment_no_advance_le (p := p) hp1 hp2 m (n := n) j y (g + 1)] with U hadv hno
  intro hy
  have hK0 : 0 ≤ (1 - aRec p m)⁻¹ :=
    le_of_lt (inv_pos.mpr (one_sub_aRec_pos hp1 hp2 m))
  have hb0 : 0 ≤ bRec p m n j U := by linarith [three_le_bRec hp1 hp2 m n j U]
  have hb0' : 0 ≤ bRec p m (n + 1) j U := by
    linarith [three_le_bRec hp1 hp2 m (n + 1) j U]
  rcases recVal_succ_eq_or p m U j n with hsame | hadvance
  · refine (hno hsame hy).trans ?_
    rw [div_eq_mul_inv]
    nlinarith [mul_nonneg hK0 hb0, hb0, hb0', hK0]
  · exact hadv hadvance hy

/-- **The complete pathwise projected-increment envelope at a fixed site.**  For every site `y`
(no hypothesis relating `y` to the record), all record cases give

    |H_{j,n+1}(y) - H_{j,n}(y)| ≤ (2/(1-a) + 2) (1 + b_n + b_{n+1}).

This is the pointwise input for the `log^4` second-moment bound of the projected ledger: the
right-hand side depends on `n` only through the two record costs. -/
theorem abs_projH_increment_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ)
    {n : ℕ} (j : Fin N) (y : ℤ) :
    ∀ᵐ U ∂(arrayMeasure N),
      |projH p m j (n + 1) U y - projH p m j n U y|
        ≤ (2 * (1 - aRec p m)⁻¹ + 2)
            * (1 + bRec p m n j U + bRec p m (n + 1) j U) := by
  have hstep : ∀ᵐ U ∂(arrayMeasure N), ∀ (y : ℤ) (g : ℕ),
      y = recVal j (prefOf p m n U) + ((g + 1 : ℕ) : ℤ) →
      |projH p m j (n + 1) U y - projH p m j n U y|
        ≤ (2 * (1 - aRec p m)⁻¹ + 2)
            * (1 + bRec p m n j U + bRec p m (n + 1) j U) :=
    MeasureTheory.ae_all_iff.mpr fun y : ℤ =>
      MeasureTheory.ae_all_iff.mpr fun g : ℕ =>
        abs_projH_increment_le_above (p := p) hp1 hp2 m (n := n) j y g
  filter_upwards [hstep,
    ae_forall_projH_eq_Hpot_of_le_record (p := p) hp1 hp2 (by linarith) m n j,
    ae_forall_projH_eq_Hpot_of_le_record (p := p) hp1 hp2 (by linarith) m (n + 1) j]
    with U hU hbel hbel1
  have hK0 : 0 ≤ (1 - aRec p m)⁻¹ :=
    le_of_lt (inv_pos.mpr (one_sub_aRec_pos hp1 hp2 m))
  have hb0 : 0 ≤ bRec p m n j U := by linarith [three_le_bRec hp1 hp2 m n j U]
  have hb0' : 0 ≤ bRec p m (n + 1) j U := by
    linarith [three_le_bRec hp1 hp2 m (n + 1) j U]
  by_cases hy : y ≤ recVal j (prefOf p m n U)
  · have hy1 : y ≤ recVal j (prefOf p m (n + 1) U) := le_trans hy (recVal_le_succ p m U j n)
    rw [hbel1 y hy1, hbel y hy, sub_self, abs_zero]
    have : 0 ≤ (2 * (1 - aRec p m)⁻¹ + 2) := by linarith
    exact mul_nonneg this (by linarith)
  · have hgt : recVal j (prefOf p m n U) < y := not_le.mp hy
    obtain ⟨k, hk⟩ : ∃ k : ℕ, y = recVal j (prefOf p m n U) + ((k + 1 : ℕ) : ℤ) := by
      refine ⟨(y - recVal j (prefOf p m n U)).toNat - 1, ?_⟩
      have hd : (0 : ℤ) < y - recVal j (prefOf p m n U) := by omega
      have hcast : (((y - recVal j (prefOf p m n U)).toNat : ℕ) : ℤ)
          = y - recVal j (prefOf p m n U) := Int.toNat_of_nonneg (le_of_lt hd)
      have hpos : 1 ≤ (y - recVal j (prefOf p m n U)).toNat := by omega
      push_cast
      omega
    exact hU y k hk

/-! ### 6. The envelope in terms of the mark maximum `qY`, and the `log^4` second moment -/

/-- **`H_{j,n}(X_{n'}^i)` is `enlFilt p m n`-measurable for any `n' ≤ n`.**  Countable pieces over
the sites, as in `measureable_projH_pos`, with the position read at the *earlier* time. -/
theorem measurable_projH_pos_of_le (p : ℝ) (m : ℕ) (j : Fin N) (n : ℕ) {n' : ℕ} (hn : n' ≤ n)
    (i : Fin N) :
    Measurable[enlFilt (N := N) p m n]
      (fun U => projH p m j n U ((trajectory p m U n').pos i)) := by
  letI : MeasurableSpace (Array N) := enlFilt p m n
  exact SwarmIID.measurable_of_countable_pieces
    (U := fun y : ℤ => fun U : Array N => projH p m j n U y)
    (fun y => measurable_projH_fixed p m j n y)
    (fun U => (trajectory p m U n').pos i)
    (fun y => enl_pos_measurable p m n hn i (measurableSet_singleton y))

/-! `SwarmActualBudget.qY p m t j` is the running maximum of `h_j` over sites `0, …, t+1`
(`RawSecondMoment.lean`), with `bRec_le_qY_add_two` and the paper's `(maxmom)` moment bound
`integrable_and_integral_qY_pow` under the actual array law.  Composing these with the envelope
of §5 gives the pointwise bound `|ΔH| ≤ C (1 + qY)` and the second moment `∫ (ΔH)^2 ≤ C log^4`. -/

/-- The explicit envelope constant `C(a) = 2/(1-a) + 2`. -/
noncomputable def incConst (p : ℝ) (m : ℕ) : ℝ := 2 * (1 - aRec p m)⁻¹ + 2

/-- The envelope constant is positive. -/
theorem incConst_pos {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) :
    0 < incConst p m := by
  have h : 0 < 1 - aRec p m := one_sub_aRec_pos hp1 hp2 m
  have : (0 : ℝ) < (1 - aRec p m)⁻¹ := inv_pos.mpr h
  simp only [incConst]; linarith

/-- The mark maximum is nondecreasing in the horizon. -/
lemma qY_le_succ (p : ℝ) (m t : ℕ) (j : Fin N) (U : Array N) :
    SwarmActualBudget.qY (N := N) p m t j U
      ≤ SwarmActualBudget.qY (N := N) p m (t + 1) j U := by
  unfold SwarmActualBudget.qY SwarmMarks.Yfun
  have hmem : ∀ x ∈ Finset.range (t + 2), x ∈ Finset.range ((t + 1) + 2) := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  exact Finset.sup'_le _ _ (fun x hx =>
    Finset.le_sup' (f := fun x => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x) (hmem x hx))

/-- **The projected increment at a fixed site, dominated by the mark maximum.** -/
theorem abs_projH_increment_le_qY {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ)
    {n : ℕ} (j : Fin N) (y : ℤ) :
    ∀ᵐ U ∂(arrayMeasure N),
      |projH p m j (n + 1) U y - projH p m j n U y|
        ≤ incConst p m * (5 * (1 + SwarmActualBudget.qY (N := N) p m (n + 1) j U)) := by
  filter_upwards [abs_projH_increment_le (p := p) hp1 hp2 m (n := n) j y] with U hU
  have hK0 : 0 ≤ incConst p m := le_of_lt (incConst_pos hp1 hp2 m)
  have hq : 1 ≤ SwarmActualBudget.qY (N := N) p m (n + 1) j U :=
    SwarmActualBudget.one_le_qY hp1.le hp2 m (n + 1) j U
  have hb1 : bRec p m n j U ≤ SwarmActualBudget.qY (N := N) p m (n + 1) j U + 2 := by
    refine le_trans (SwarmActualBudget.bRec_le_qY_add_two hp1.le hp2 m n j U) ?_
    have := qY_le_succ p m n j U
    linarith
  have hb2 : bRec p m (n + 1) j U ≤ SwarmActualBudget.qY (N := N) p m (n + 1) j U + 2 :=
    SwarmActualBudget.bRec_le_qY_add_two hp1.le hp2 m (n + 1) j U
  have hinner : 1 + bRec p m n j U + bRec p m (n + 1) j U
      ≤ 5 * (1 + SwarmActualBudget.qY (N := N) p m (n + 1) j U) := by linarith
  refine hU.trans ?_
  simp only [incConst] at hK0 ⊢
  exact mul_le_mul_of_nonneg_left hinner hK0

/-- The same bound simultaneously at every site (countable intersection of the sitewise ones). -/
theorem ae_forall_abs_projH_increment_le_qY {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m : ℕ) {n : ℕ} (j : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ y : ℤ,
      |projH p m j (n + 1) U y - projH p m j n U y|
        ≤ incConst p m * (5 * (1 + SwarmActualBudget.qY (N := N) p m (n + 1) j U)) :=
  MeasureTheory.ae_all_iff.mpr fun y => abs_projH_increment_le_qY (p := p) hp1 hp2 m (n := n) j y

/-- The planned-increment envelope at every site at once. -/
theorem ae_forall_abs_projH_increment_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m : ℕ) {n : ℕ} (j : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ y : ℤ,
      |projH p m j (n + 1) U y - projH p m j n U y|
        ≤ incConst p m * (1 + bRec p m n j U + bRec p m (n + 1) j U) :=
  MeasureTheory.ae_all_iff.mpr fun y => abs_projH_increment_le (p := p) hp1 hp2 m (n := n) j y

/-- `log (t+3) ≤ 2 log (t+2)`: the horizon shift of `qY`. -/
lemma log_three_le_two_mul (t : ℕ) :
    Real.log ((t : ℝ) + 3) ≤ 2 * Real.log ((t : ℝ) + 2) := by
  have h2 : (0 : ℝ) < (t : ℝ) + 2 := by positivity
  have h : (t : ℝ) + 3 ≤ ((t : ℝ) + 2) ^ 2 := by
    have ht : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
    nlinarith
  calc Real.log ((t : ℝ) + 3) ≤ Real.log (((t : ℝ) + 2) ^ 2) :=
        Real.log_le_log (by positivity) h
    _ = 2 * Real.log ((t : ℝ) + 2) := by
        rw [Real.log_pow]
        push_cast
        ring

/-- **The projected one-step increment at the walker's own position has a `log^4` second moment.**

    ∫ (H_{j,t+1}(X_t^i) - H_{j,t}(X_t^i))^2 ≤ C (log (t+2))^4,

with `C` depending only on `(m, p, N-free)`.  All record cases are covered by §5; the `log^4`
comes from the paper's mark maximum `(maxmom)`.  This is the potential-derivative half of the
projected ledger's second-moment input `hvar`. -/
theorem exists_integral_sq_projH_increment_le {p : ℝ} (hp0 : 0 < p)
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m) (i j : Fin N) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ,
      Integrable (fun U : Array N =>
        (projH p m j (t + 1) U ((trajectory p m U t).pos i)
          - projH p m j t U ((trajectory p m U t).pos i)) ^ 2) (arrayMeasure N) ∧
      ∫ U, (projH p m j (t + 1) U ((trajectory p m U t).pos i)
          - projH p m j t U ((trajectory p m U t).pos i)) ^ 2 ∂(arrayMeasure N)
        ≤ C * (Real.log ((t : ℝ) + 2)) ^ 4 := by
  obtain ⟨C4, hC4pos, hC4⟩ :=
    SwarmActualBudget.integrable_and_integral_qY_pow (N := N) hp0 hp1 hp2 hm 4 (by norm_num) j
  have hK0 : 0 ≤ incConst p m := le_of_lt (incConst_pos hp1 hp2 m)
  have hKpos : 0 < incConst p m := incConst_pos hp1 hp2 m
  refine ⟨(5 * incConst p m) ^ 2 * 16 * C4,
    mul_pos (mul_pos (pow_pos (by linarith) 2) (by norm_num)) hC4pos, fun t => ?_⟩
  obtain ⟨hint4, hb4⟩ := hC4 (t + 1)
  have hb4' : ∫ U, (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) ^ 4
      ∂(arrayMeasure N) ≤ C4 * (Real.log (((t + 1 : ℕ) : ℝ) + 2)) ^ 4 := hb4
  -- pointwise domination
  have hpt : ∀ᵐ U ∂(arrayMeasure N),
      (projH p m j (t + 1) U ((trajectory p m U t).pos i)
          - projH p m j t U ((trajectory p m U t).pos i)) ^ 2
        ≤ (5 * incConst p m) ^ 2 * (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) ^ 4 := by
    filter_upwards [ae_forall_abs_projH_increment_le_qY (p := p) hp1 hp2 m (n := t) j]
      with U hU
    have hU := hU ((trajectory p m U t).pos i)
    have hq : 1 ≤ 1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U := by
      have := SwarmActualBudget.one_le_qY hp1.le hp2 m (t + 1) j U
      linarith
    have hM : 0 ≤ incConst p m * (5 * (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U)) :=
      mul_nonneg hK0 (by linarith)
    have hsq : (projH p m j (t + 1) U ((trajectory p m U t).pos i)
          - projH p m j t U ((trajectory p m U t).pos i)) ^ 2
        ≤ (incConst p m * (5 * (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U))) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hU 2
    have hq2 : (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) ^ 2
        ≤ (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) ^ 4 := by
      have hsq2 : (1 : ℝ) ^ 2 ≤ (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) ^ 2 :=
        pow_le_pow_left₀ (by norm_num) hq 2
      have h1 : (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) ^ 2
          = (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) ^ 2 * 1 := by ring
      calc (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) ^ 2
          = (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) ^ 2 * 1 := by ring
        _ ≤ (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) ^ 2
              * (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) ^ 2 := by
            refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
            nlinarith [hq]
        _ = (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) ^ 4 := by ring
    calc (projH p m j (t + 1) U ((trajectory p m U t).pos i)
          - projH p m j t U ((trajectory p m U t).pos i)) ^ 2
        ≤ (incConst p m * (5 * (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U))) ^ 2 := hsq
      _ = (5 * incConst p m) ^ 2
            * (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) ^ 2 := by ring
      _ ≤ (5 * incConst p m) ^ 2
            * (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) ^ 4 :=
          mul_le_mul_of_nonneg_left hq2 (by positivity)
  -- measurability
  have hmeas : AEStronglyMeasurable (fun U : Array N =>
      (projH p m j (t + 1) U ((trajectory p m U t).pos i)
        - projH p m j t U ((trajectory p m U t).pos i)) ^ 2) (arrayMeasure N) := by
    have h1 : Measurable (fun U : Array N => projH p m j (t + 1) U ((trajectory p m U t).pos i)) :=
      (measurable_projH_pos_of_le p m j (t + 1) (Nat.le_succ t) i).mono
        ((enlFilt (N := N) p m).le (t + 1)) le_rfl
    have h2 : Measurable (fun U : Array N => projH p m j t U ((trajectory p m U t).pos i)) :=
      (measurable_projH_pos p m j t i).mono ((enlFilt (N := N) p m).le t) le_rfl
    exact ((h1.sub h2).pow_const 2).aestronglyMeasurable
  have hmaj : Integrable (fun U : Array N =>
      (5 * incConst p m) ^ 2 * (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) ^ 4)
      (arrayMeasure N) := hint4.const_mul _
  have hint : Integrable (fun U : Array N =>
      (projH p m j (t + 1) U ((trajectory p m U t).pos i)
        - projH p m j t U ((trajectory p m U t).pos i)) ^ 2) (arrayMeasure N) := by
    refine Integrable.mono' hmaj hmeas ?_
    filter_upwards [hpt] with U hU
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hU
  refine ⟨hint, ?_⟩
  have hmono := integral_mono_ae hint hmaj hpt
  have hfactor : ∫ U, (5 * incConst p m) ^ 2
        * (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) ^ 4 ∂(arrayMeasure N)
      = (5 * incConst p m) ^ 2
        * ∫ U, (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) ^ 4 ∂(arrayMeasure N) :=
    integral_const_mul _ _
  rw [hfactor] at hmono
  have hlog : Real.log (((t + 1 : ℕ) : ℝ) + 2) ≤ 2 * Real.log ((t : ℝ) + 2) := by
    have h := log_three_le_two_mul t
    have hcast : (((t + 1 : ℕ) : ℝ) + 2) = (t : ℝ) + 3 := by push_cast; ring
    rw [hcast]
    exact h
  have hlog0 : 0 ≤ Real.log ((t : ℝ) + 2) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) t])
  have hlog4 : (Real.log (((t + 1 : ℕ) : ℝ) + 2)) ^ 4 ≤ 16 * (Real.log ((t : ℝ) + 2)) ^ 4 := by
    have h4 : (Real.log (((t + 1 : ℕ) : ℝ) + 2)) ^ 4
        ≤ (2 * Real.log ((t : ℝ) + 2)) ^ 4 := by
      have h0 : (0 : ℝ) ≤ Real.log (((t + 1 : ℕ) : ℝ) + 2) := by
        refine Real.log_nonneg ?_
        push_cast
        linarith [Nat.cast_nonneg (α := ℝ) t]
      exact pow_le_pow_left₀ h0 hlog 4
    nlinarith
  have hstep : (5 * incConst p m) ^ 2
        * ∫ U, (1 + SwarmActualBudget.qY (N := N) p m (t + 1) j U) ^ 4 ∂(arrayMeasure N)
      ≤ (5 * incConst p m) ^ 2 * (C4 * (Real.log (((t + 1 : ℕ) : ℝ) + 2)) ^ 4) :=
    mul_le_mul_of_nonneg_left hb4' (by positivity)
  have hbound : (5 * incConst p m) ^ 2 * (C4 * (Real.log (((t + 1 : ℕ) : ℝ) + 2)) ^ 4)
      ≤ (5 * incConst p m) ^ 2 * 16 * C4 * (Real.log ((t : ℝ) + 2)) ^ 4 := by
    have := mul_le_mul_of_nonneg_left hlog4 hC4pos.le
    nlinarith [this, sq_nonneg (5 * incConst p m), sq_nonneg (Real.log ((t : ℝ) + 2))]
  linarith [hmono, hstep, hbound]

/-! ### Axiom audit -/


