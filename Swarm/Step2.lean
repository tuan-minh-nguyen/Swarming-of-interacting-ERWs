import Swarm.Imports
import Swarm.StoppedCross
import Swarm.Diag
import Swarm.Step

open MeasureTheory Filter
open scoped Topology BigOperators

namespace SwarmSpeed

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}
variable {wf : Ω → ℕ → ℝ} {b0 b1 : ℕ} {X : ℕ → Ω → ℕ}

/-- The step/absorption disjunction at time `n` of the actual interacting walk. -/
def StepAt (X : ℕ → Ω → ℕ) (b0 b1 n : ℕ) (ω : Ω) : Prop :=
  (b0 < X n ω ∧ X n ω ≤ b1 ∧ (X (n + 1) ω = X n ω + 1 ∨ X (n + 1) ω + 1 = X n ω))
    ∨ (X n ω ≤ b0 ∧ X (n + 1) ω = X n ω) ∨ (X n ω = b1 + 1 ∧ X (n + 1) ω = X n ω)

/-- The interior indicator `1{b0 < X_n <= b1}` is `ℱ n`-measurable. -/
lemma measurable_insideD {Ω : Type*} {m0 : MeasurableSpace Ω} {ℱ : Filtration ℕ m0}
    {b0 b1 : ℕ} {X : ℕ → Ω → ℕ} (hX : ∀ n, Measurable[ℱ n] (X n)) (n : ℕ) :
    Measurable[ℱ n] (inside X b0 b1 n) := by
  change Measurable[ℱ n] (fun ω => if b0 < X n ω ∧ X n ω ≤ b1 then (1 : ℝ) else 0)
  exact Measurable.ite
    ((measurableSet_lt measurable_const (hX n)).inter (measurableSet_le (hX n) measurable_const))
    measurable_const measurable_const

/-- Norm bound for the clamped scale value on the window. -/
lemma norm_scDiag_le_one {wf : Ω → ℕ → ℝ} {b0 b1 : ℕ} {g : Ω → ℕ} {ω : Ω}
    (hlo : ∀ x, (1 : ℝ) / 2 ≤ wf ω x) (hhi : ∀ x, wf ω x < 1) (hb : b0 ≤ b1)
    (hg : g ω ≤ b1 + 1) : ‖scDiag wf b0 b1 g ω‖ ≤ 1 := by
  rw [scDiag_apply hg]
  exact norm_sc_le_one hlo hhi hb hg

/-- Norm bound for the clamped forward increment. -/
lemma norm_deltaD_le_one {wf : Ω → ℕ → ℝ} {b0 b1 : ℕ} {g : Ω → ℕ} {ω : Ω}
    (hlo : ∀ x, (1 : ℝ) / 2 ≤ wf ω x) (hhi : ∀ x, wf ω x < 1) (hb : b0 ≤ b1) :
    ‖deltaD wf b0 b1 g ω‖ ≤ 1 := by
  simp only [deltaD]
  by_cases h : g ω ≤ b1
  · rw [if_pos h]
    have ha : scDiag wf b0 b1 (fun ω' => g ω' + 1) ω = sc (wf ω) b0 b1 (g ω + 1) :=
      scDiag_apply (wf := wf) (g := fun ω' => g ω' + 1) (ω := ω) (by show g ω + 1 ≤ b1 + 1; omega)
    have hb' : scDiag wf b0 b1 (fun ω' => g ω' - 1) ω = sc (wf ω) b0 b1 (g ω - 1) :=
      scDiag_apply (wf := wf) (g := fun ω' => g ω' - 1) (ω := ω) (by show g ω - 1 ≤ b1 + 1; omega)
    rw [ha, hb', Real.norm_eq_abs, abs_le]
    constructor
    · have x1 := sc_nonneg hlo hhi hb (g ω + 1)
      have x2 := sc_le_one hlo hhi hb (show g ω + 1 ≤ b1 + 1 by omega)
      have y1 := sc_nonneg hlo hhi hb (g ω - 1)
      have y2 := sc_le_one hlo hhi hb (show g ω - 1 ≤ b1 + 1 by omega)
      linarith
    · have x1 := sc_nonneg hlo hhi hb (g ω + 1)
      have x2 := sc_le_one hlo hhi hb (show g ω + 1 ≤ b1 + 1 by omega)
      have y1 := sc_nonneg hlo hhi hb (g ω - 1)
      have y2 := sc_le_one hlo hhi hb (show g ω - 1 ≤ b1 + 1 by omega)
      linarith
  · rw [if_neg h]; norm_num

/-- Norm bound for the clamped backward correction on the window. -/
lemma norm_backD_le_two {wf : Ω → ℕ → ℝ} {b0 b1 : ℕ} {g : Ω → ℕ} {ω : Ω}
    (hlo : ∀ x, (1 : ℝ) / 2 ≤ wf ω x) (hhi : ∀ x, wf ω x < 1) (hb : b0 ≤ b1)
    (hg : g ω ≤ b1 + 1) : ‖backD wf b0 b1 g ω‖ ≤ 2 := by
  simp only [backD]
  by_cases h : 1 ≤ g ω
  · rw [if_pos h]
    have ha : scDiag wf b0 b1 (fun ω' => g ω' - 1) ω = sc (wf ω) b0 b1 (g ω - 1) :=
      scDiag_apply (wf := wf) (g := fun ω' => g ω' - 1) (ω := ω) (by show g ω - 1 ≤ b1 + 1; omega)
    have hb' : scDiag wf b0 b1 g ω = sc (wf ω) b0 b1 (g ω) := scDiag_apply hg
    rw [ha, hb', Real.norm_eq_abs, abs_le]
    constructor
    · have x1 := sc_nonneg hlo hhi hb (g ω - 1)
      have x2 := sc_le_one hlo hhi hb (show g ω - 1 ≤ b1 + 1 by omega)
      have y1 := sc_nonneg hlo hhi hb (g ω)
      have y2 := sc_le_one hlo hhi hb hg
      linarith
    · have x1 := sc_nonneg hlo hhi hb (g ω - 1)
      have x2 := sc_le_one hlo hhi hb (show g ω - 1 ≤ b1 + 1 by omega)
      have y1 := sc_nonneg hlo hhi hb (g ω)
      have y2 := sc_le_one hlo hhi hb hg
      linarith
  · rw [if_neg h]; norm_num

section OneStep

variable [IsProbabilityMeasure μ] (hb : b0 ≤ b1) (hX : ∀ n, Measurable[ℱ n] (X n))

include hb hX

/-- **The one-step conditional drift in a revealed random environment.**

On `{b0 < X_n <= b1}` the revealed weight `wf ω (X_n ω)` is below the conditional right-jump
probability `μ[stepRight X n | ℱ_n]`, and every coordinate of `wf ω` is `ℱ_n`-measurable
because `n ≥ s`; hence the site-wise pull-out of the clamped scale function is legitimate and
the deterministic drift computation `sc_drift` applies at each `ω`.  This is the
random-environment replacement of `SwarmSpeed.condExp_sc_step_int`. -/
theorem condExp_scD_step {s n : ℕ} (hw : ∀ x, Measurable[ℱ s] (fun ω => wf ω x)) (hn : s ≤ n)
    (hlo : ∀ᵐ ω ∂μ, ∀ x, (1 : ℝ) / 2 ≤ wf ω x)
    (hhi : ∀ᵐ ω ∂μ, ∀ x, wf ω x < 1)
    (hr : ∀ᵐ ω ∂μ, X n ω ≤ b1 + 1) (hr1 : ∀ᵐ ω ∂μ, X (n + 1) ω ≤ b1 + 1)
    (hstep : ∀ᵐ ω ∂μ, StepAt X b0 b1 n ω)
    (hdom : ∀ᵐ ω ∂μ, b0 < X n ω → X n ω ≤ b1 →
      wf ω (X n ω) ≤ (μ[stepRight X n | ℱ n]) ω) :
    (fun ω => scDiag wf b0 b1 (fun ω' => X n ω') ω)
      ≤ᵐ[μ] (μ[(fun ω => scDiag wf b0 b1 (fun ω' => X (n + 1) ω') ω) | ℱ n]) := by
  classical
  have hbase : ∀ᵐ ω ∂μ, (∀ x, (1 : ℝ) / 2 ≤ wf ω x) ∧ (∀ x, wf ω x < 1) ∧
      X n ω ≤ b1 + 1 ∧ X (n + 1) ω ≤ b1 + 1 ∧ StepAt X b0 b1 n ω ∧
      (b0 < X n ω → X n ω ≤ b1 → wf ω (X n ω) ≤ (μ[stepRight X n | ℱ n]) ω) := by
    filter_upwards [hlo, hhi, hr, hr1, hstep, hdom] with ω h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  set Sc : Ω → ℝ := fun ω => scDiag wf b0 b1 (fun ω' => X n ω') ω with hSc
  set Sc1 : Ω → ℝ := fun ω => scDiag wf b0 b1 (fun ω' => X (n + 1) ω') ω with hSc1
  set Ifn : Ω → ℝ := inside X b0 b1 n with hIfn
  set Rfn : Ω → ℝ := stepRight X n with hRfn
  set Dfn : Ω → ℝ := deltaD wf b0 b1 (fun ω' => X n ω') with hDfn
  set Bfn : Ω → ℝ := backD wf b0 b1 (fun ω' => X n ω') with hBfn
  set Gfn : Ω → ℝ := Rfn * Dfn + Bfn with hGfn
  set Hfn : Ω → ℝ := Ifn * Gfn with hHfn
  have hwn : ∀ x, Measurable[ℱ n] (fun ω => wf ω x) := fun x => (hw x).mono (ℱ.mono hn) le_rfl
  -- measurability
  have hmSc : Measurable[ℱ n] Sc := by rw [hSc]; exact measurable_scDiag hwn (hX n)
  have hmSc1 : Measurable (fun ω => scDiag wf b0 b1 (fun ω' => X (n + 1) ω') ω) :=
    (measurable_scDiag (fun x => (hw x).mono (ℱ.mono (le_trans hn (Nat.le_succ n))) le_rfl)
      (hX (n + 1))).mono (ℱ.le (n + 1)) le_rfl
  have hmSc10 : Measurable Sc1 := by rw [hSc1]; exact hmSc1
  have hmIfn : Measurable[ℱ n] Ifn := by rw [hIfn]; exact measurable_insideD hX n
  have hmIfn0 : Measurable Ifn := hmIfn.mono (ℱ.le n) le_rfl
  have hmDfn : Measurable[ℱ n] Dfn := by
    rw [hDfn]; exact measurable_deltaD hwn (hX n)
  have hmDfn0 : Measurable Dfn := hmDfn.mono (ℱ.le n) le_rfl
  have hmBfn : Measurable[ℱ n] Bfn := by
    rw [hBfn]; exact measurable_backD hwn (hX n)
  have hmBfn0 : Measurable Bfn := hmBfn.mono (ℱ.le n) le_rfl
  have hmRfn : Measurable Rfn := by
    rw [hRfn]
    exact Measurable.ite (measurableSet_eq_fun ((hX (n + 1)).mono (ℱ.le (n + 1)) le_rfl)
      (((hX n).mono (ℱ.le n) le_rfl).add measurable_const)) measurable_const measurable_const
  have hmGfn : Measurable Gfn := by rw [hGfn]; exact (hmRfn.mul hmDfn0).add hmBfn0
  have hmHfn : Measurable Hfn := by rw [hHfn]; exact hmIfn0.mul hmGfn
  -- integrability
  have hmSc0 : Measurable Sc := hmSc.mono (ℱ.le n) le_rfl
  have hintSc : Integrable Sc μ := by
    refine Integrable.of_bound hmSc0.aestronglyMeasurable 1 ?_
    filter_upwards [hbase] with ω ⟨h1, h2, h3, h4, h5, h6⟩
    rw [hSc]
    exact norm_scDiag_le_one h1 h2 hb h3
  have hintSc1 : Integrable Sc1 μ := by
    refine Integrable.of_bound hmSc10.aestronglyMeasurable 1 ?_
    filter_upwards [hbase] with ω ⟨h1, h2, h3, h4, h5, h6⟩
    rw [hSc1]
    exact norm_scDiag_le_one h1 h2 hb h4
  have hintRfn : Integrable Rfn μ := by
    refine Integrable.of_bound hmRfn.aestronglyMeasurable 1 ?_
    filter_upwards with ω
    rw [hRfn]
    exact norm_stepRight_le n ω
  have hintDfn : Integrable Dfn μ := by
    refine Integrable.of_bound hmDfn0.aestronglyMeasurable 1 ?_
    filter_upwards [hbase] with ω ⟨h1, h2, h3, h4, h5, h6⟩
    rw [hDfn]
    exact norm_deltaD_le_one h1 h2 hb
  have hintBfn : Integrable Bfn μ := by
    refine Integrable.of_bound hmBfn0.aestronglyMeasurable 2 ?_
    filter_upwards [hbase] with ω ⟨h1, h2, h3, h4, h5, h6⟩
    rw [hBfn]
    exact norm_backD_le_two h1 h2 hb h3
  have hintIfn : Integrable Ifn μ := by
    refine Integrable.of_bound hmIfn0.aestronglyMeasurable 1 ?_
    filter_upwards with ω
    rw [hIfn]
    exact norm_inside_le n ω
  have hintRD : Integrable (Rfn * Dfn) μ := by
    refine Integrable.of_bound (hmRfn.mul hmDfn0).aestronglyMeasurable 1 ?_
    filter_upwards [hbase] with ω ⟨h1, h2, h3, h4, h5, h6⟩
    rw [Pi.mul_apply, hRfn, hDfn, norm_mul]
    calc ‖stepRight X n ω‖ * ‖deltaD wf b0 b1 (fun ω' => X n ω') ω‖ ≤ 1 * 1 :=
          mul_le_mul (norm_stepRight_le n ω) (norm_deltaD_le_one h1 h2 hb) (norm_nonneg _)
            (by norm_num)
      _ = 1 := by norm_num
  have hintG : Integrable Gfn μ := by
    rw [hGfn]; exact hintRD.add hintBfn
  have hintH : Integrable Hfn μ := by
    rw [hHfn]
    refine Integrable.of_bound (hmIfn0.mul hmGfn).aestronglyMeasurable 3 ?_
    filter_upwards [hbase] with ω ⟨h1, h2, h3, h4, h5, h6⟩
    rw [Pi.mul_apply, norm_mul]
    have hI1 : ‖Ifn ω‖ ≤ 1 := by rw [hIfn]; exact norm_inside_le n ω
    have hR1 : ‖Rfn ω‖ ≤ 1 := by rw [hRfn]; exact norm_stepRight_le n ω
    have hD1 : ‖Dfn ω‖ ≤ 1 := by rw [hDfn]; exact norm_deltaD_le_one h1 h2 hb
    have hB2 : ‖Bfn ω‖ ≤ 2 := by rw [hBfn]; exact norm_backD_le_two h1 h2 hb h3
    have hG3 : ‖Gfn ω‖ ≤ 3 := by
      rw [hGfn, Pi.add_apply]
      refine le_trans (norm_add_le _ _) ?_
      have : ‖(Rfn * Dfn) ω‖ ≤ 1 := by
        rw [Pi.mul_apply, norm_mul]
        calc ‖Rfn ω‖ * ‖Dfn ω‖ ≤ 1 * 1 := mul_le_mul hR1 hD1 (norm_nonneg _) (by norm_num)
          _ = 1 := by norm_num
      linarith
    calc ‖Ifn ω‖ * ‖Gfn ω‖ ≤ 1 * 3 := mul_le_mul hI1 hG3 (norm_nonneg _) (by norm_num)
      _ = 3 := by norm_num
  -- the a.e. step identity
  have hpt : Sc1 =ᵐ[μ] Sc + Hfn := by
    filter_upwards [hbase] with ω hb'
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hb'
    have hd : Dfn ω = scaleDelta (wf ω) b0 b1 X n ω := by rw [hDfn, deltaD_eq_scaleDelta]
    have hbk : Bfn ω = scaleBack (wf ω) b0 b1 X n ω := by rw [hBfn]; exact backD_apply h3
    have hs0 : Sc ω = sc (wf ω) b0 b1 (X n ω) := by rw [hSc]; exact scDiag_apply h3
    have hs1 : Sc1 ω = sc (wf ω) b0 b1 (X (n + 1) ω) := by rw [hSc1]; exact scDiag_apply h4
    rw [Pi.add_apply]
    simp only [hHfn, hGfn, hRfn, hIfn, Pi.mul_apply, Pi.add_apply]
    rw [hs0, hs1, hd, hbk]
    exact sc_step_identity (w := wf ω) (X := X) (b0 := b0) (b1 := b1) n h5
  -- conditional expectation decomposition
  have e0 : ∀ᵐ ω ∂μ, (μ[Sc | ℱ n]) ω = Sc ω :=
    Filter.EventuallyEq.of_eq
      (condExp_of_stronglyMeasurable (m := ℱ n) (ℱ.le n) hmSc.stronglyMeasurable hintSc)
  have e1 : ∀ᵐ ω ∂μ, (μ[Sc1 | ℱ n]) ω = (μ[Sc + Hfn | ℱ n]) ω :=
    condExp_congr_ae hpt
  have e2 : ∀ᵐ ω ∂μ, (μ[Sc + Hfn | ℱ n]) ω = (μ[Sc | ℱ n]) ω + (μ[Hfn | ℱ n]) ω := by
    filter_upwards [condExp_add hintSc hintH (ℱ n)] with ω h
    simpa only [Pi.add_apply] using h
  have e3 : ∀ᵐ ω ∂μ, (μ[Hfn | ℱ n]) ω = Ifn ω * (μ[Gfn | ℱ n]) ω := by
    filter_upwards [condExp_mul_of_stronglyMeasurable_left (m := ℱ n) hmIfn.stronglyMeasurable
      hintH hintG] with ω h
    simpa only [Pi.mul_apply, hHfn] using h
  have e4 : ∀ᵐ ω ∂μ, (μ[Gfn | ℱ n]) ω = (μ[Rfn * Dfn | ℱ n]) ω + (μ[Bfn | ℱ n]) ω := by
    filter_upwards [condExp_add hintRD hintBfn (ℱ n)] with ω h
    simpa only [Pi.add_apply, hGfn] using h
  have e4a : ∀ᵐ ω ∂μ, (μ[Rfn * Dfn | ℱ n]) ω = (μ[Rfn | ℱ n]) ω * Dfn ω := by
    filter_upwards [condExp_mul_of_stronglyMeasurable_right (m := ℱ n) hmDfn.stronglyMeasurable
      hintRD hintRfn] with ω h
    simpa only [Pi.mul_apply] using h
  have e4b : ∀ᵐ ω ∂μ, (μ[Bfn | ℱ n]) ω = Bfn ω :=
    Filter.EventuallyEq.of_eq
      (condExp_of_stronglyMeasurable (m := ℱ n) (ℱ.le n) hmBfn.stronglyMeasurable hintBfn)
  have key : ∀ᵐ ω ∂μ, (μ[Sc1 | ℱ n]) ω
      = Sc ω + Ifn ω * ((μ[Rfn | ℱ n]) ω * Dfn ω + Bfn ω) := by
    filter_upwards [e1, e2, e3, e4, e4a, e4b, e0] with ω h1 h2 h3 h4 h44 h4b h0
    rw [h1, h2, h3, h4, h44, h4b, h0]
  -- nonnegativity of the correction
  have hnn : ∀ᵐ ω ∂μ, 0 ≤ Ifn ω * ((μ[Rfn | ℱ n]) ω * Dfn ω + Bfn ω) := by
    filter_upwards [hbase] with ω hb'
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hb'
    rw [hIfn]
    rcases h5 with ⟨hi1, hi2, hs⟩ | ⟨hle, heq⟩ | ⟨heq, heq2⟩
    · have hin : inside X b0 b1 n ω = 1 := by
        simp only [inside]; rw [if_pos ⟨hi1, hi2⟩]
      have hdel : Dfn ω = sc (wf ω) b0 b1 (X n ω + 1) - sc (wf ω) b0 b1 (X n ω - 1) := by
        rw [hDfn, deltaD_eq_scaleDelta]
        simp only [scaleDelta]; rw [if_pos hi2]
      have hback : Bfn ω = sc (wf ω) b0 b1 (X n ω - 1) - sc (wf ω) b0 b1 (X n ω) := by
        rw [hBfn, backD_apply h3]
        simp only [scaleBack]; rw [if_pos (by omega : 1 ≤ X n ω)]
      have hDnn : 0 ≤ sc (wf ω) b0 b1 (X n ω + 1) - sc (wf ω) b0 b1 (X n ω - 1) :=
        sub_nonneg.mpr (sc_monotone h1 h2 hb (by omega))
      have hkey : wf ω (X n ω) * (sc (wf ω) b0 b1 (X n ω + 1)
            - sc (wf ω) b0 b1 (X n ω - 1))
          + (sc (wf ω) b0 b1 (X n ω - 1) - sc (wf ω) b0 b1 (X n ω)) = 0 := by
        have hdr := sc_drift h1 h2 hb hi1 hi2 (wf ω (X n ω))
        rw [sub_self, zero_mul] at hdr
        linarith
      have hPD : wf ω (X n ω) * (sc (wf ω) b0 b1 (X n ω + 1)
            - sc (wf ω) b0 b1 (X n ω - 1))
          ≤ (μ[stepRight X n | ℱ n]) ω * (sc (wf ω) b0 b1 (X n ω + 1)
            - sc (wf ω) b0 b1 (X n ω - 1)) :=
        mul_le_mul_of_nonneg_right (h6 hi1 hi2) hDnn
      rw [hin, one_mul, hdel, hback, hRfn]
      linarith
    · have hin : inside X b0 b1 n ω = 0 := by
        simp only [inside]; rw [if_neg]; intro hcon; omega
      rw [hin, zero_mul]
    · have hin : inside X b0 b1 n ω = 0 := by
        simp only [inside]; rw [if_neg]; intro hcon; omega
      rw [hin, zero_mul]
  filter_upwards [key, hnn] with ω hk hn
  rw [hk]
  linarith

end OneStep

end SwarmSpeed
