/-
Almost-sure predictable carriers on weighted deterministic-start windows, and
an exact shifted geometric/harmonic residual budget.

The weighted cell theorem conditions the *measure* on its measurable start
cell.  It does not restart the process or assume independence of the future.
The spatial residual uses times `s + k` throughout and keeps the defect events
intersected with the same start cell.  No hitting-time estimate, uniform bound
in `M`, or vanishing-defect assertion is made here.
-/
import Swarm.QplTopDefect
import Swarm.QplWeightedCell
import Swarm.ActualRecordQplCell

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Classical
open scoped BigOperators ENNReal
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory
open Swarming.Enl QplPredEnv QplWindow ShiftedAdvance

namespace ShiftedQplResidual

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- Weighted deterministic-start maximal Azuma bound with an **almost-sure**
predictable envelope.  This is the a.e. counterpart of
`ShiftedAdvance.measureReal_cell_max_abs_shift_le_of_ptrunc`; conditioning on
the start cell converts the a.e. hypothesis without any future-law assumption. -/
theorem measureReal_cell_max_abs_shift_le_of_ptrunc_ae
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0}
    {s : ℕ} {A : Set Ω} (hA : MeasurableSet[ℱ s] A)
    {G : ℕ → Set Ω} (hG : ∀ k, MeasurableSet[ℱ (s + k)] (G k))
    {ξ : ℕ → Ω → ℝ}
    (hξm : ∀ k, StronglyMeasurable[ℱ (s + k + 1)] (ξ (s + k)))
    (hξi : ∀ k, Integrable (ξ (s + k)) μ)
    (hξ0 : ∀ k, μ[ξ (s + k) | ℱ (s + k)] =ᵐ[μ] 0)
    {C : ℝ} (hC : 0 < C)
    (hbdd : ∀ k, ∀ᵐ ω ∂μ, ω ∈ G k → |ξ (s + k) ω| ≤ C)
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    μ.real (A ∩ {ω | ∃ k ≤ n,
        ε ≤ |LocMart.psum ξ (s + k) ω - LocMart.psum ξ s ω|}) ≤
      μ.real A * (2 * ((n : ℝ) + 1) *
        Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2))) +
      μ.real (A ∩ {ω | ∃ k < n, ω ∉ G k}) := by
  let E : Set Ω := {ω | ∃ k ≤ n,
    ε ≤ |LocMart.psum ξ (s + k) ω - LocMart.psum ξ s ω|}
  let R : Set Ω := {ω | ∃ k < n, ω ∉ G k}
  by_cases hA0 : μ A = 0
  · have hz : μ.real (A ∩ E) = 0 := by
      rw [Measure.real_def, measure_mono_null Set.inter_subset_left hA0,
        ENNReal.toReal_zero]
    have hAz : μ.real A = 0 :=
      (measureReal_eq_zero_iff (measure_ne_top μ A)).2 hA0
    change μ.real (A ∩ E) ≤ _
    rw [hz, hAz, zero_mul, zero_add]
    exact measureReal_nonneg
  · let ν : Measure Ω := μ[|A]
    letI : IsProbabilityMeasure ν := cond_isProbabilityMeasure hA0
    let F : Filtration ℕ m0 := cellShiftFilt ℱ s
    let ζ : ℕ → Ω → ℝ := fun k => ξ (s + k)
    have hAm : MeasurableSet A := MeasurableSpace.le_def.1 (ℱ.le s) A hA
    have hG' : ∀ k, MeasurableSet[F k] (G k) := hG
    have hζm : ∀ k, StronglyMeasurable[F (k + 1)] (ζ k) := hξm
    have hζi : ∀ k, Integrable (ζ k) ν := by
      intro k
      change Integrable (ξ (s + k)) ((μ A)⁻¹ • μ.restrict A)
      exact (hξi k).restrict.smul_measure (ENNReal.inv_ne_top.2 hA0)
    have hζ0 : ∀ k, ν[ζ k | F k] =ᵐ[ν] 0 := by
      intro k
      have hAk : MeasurableSet[ℱ (s + k)] A :=
        MeasurableSpace.le_def.1 (ℱ.mono (show s ≤ s + k by omega)) A hA
      exact condExp_eq_zero_cond_of_measurableSet (ℱ.le (s + k))
        hAk (hξi k) (hξ0 k) hA0
    have hbddν : ∀ k, ∀ᵐ ω ∂ν, ω ∈ G k → |ζ k ω| ≤ C := by
      intro k
      change ∀ᵐ ω ∂((μ A)⁻¹ • μ.restrict A), ω ∈ G k → |ξ (s + k) ω| ≤ C
      exact Measure.ae_smul_measure (ae_restrict_of_ae (hbdd k)) _
    have hmain := QplOsc.measure_max_abs_psum_le_of_ptrunc_ae
      (μ := ν) (ℱ := F) (G := G) (ξ := ζ)
      hG' hζm hζi hζ0 hC hbddν hn hε
    let E' : Set Ω := {ω | ∃ k ≤ n, ε ≤ |LocMart.psum ζ k ω|}
    have hE : E' = E := by
      ext ω
      simp only [E, E', Set.mem_ofPred_eq]
      congr! 3 with k hk
      rw [show LocMart.psum ζ k ω =
        LocMart.psum ξ (s + k) ω - LocMart.psum ξ s ω from
        psum_shift_eq_sub s k ω]
    change ν.real E' ≤ _ + ν.real R at hmain
    rw [hE] at hmain
    rw [measureReal_cond_apply hAm, measureReal_cond_apply hAm] at hmain
    have hAreal : μ.real A ≠ 0 :=
      (measureReal_ne_zero_iff (measure_ne_top μ A)).2 hA0
    have hApos : 0 < μ.real A :=
      lt_of_le_of_ne measureReal_nonneg (Ne.symm hAreal)
    have hmul := mul_le_mul_of_nonneg_left hmain hApos.le
    change μ.real (A ∩ E) ≤ _
    calc
      μ.real (A ∩ E) = μ.real A * ((μ.real A)⁻¹ * μ.real (A ∩ E)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hAreal, one_mul]
      _ ≤ μ.real A * (2 * ((n : ℝ) + 1) *
          Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2)) +
            (μ.real A)⁻¹ * μ.real (A ∩ R)) := hmul
      _ = μ.real A * (2 * ((n : ℝ) + 1) *
          Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2))) + μ.real (A ∩ R) := by
        have hr : μ.real A * ((μ.real A)⁻¹ * μ.real (A ∩ R)) = μ.real (A ∩ R) := by
          rw [← mul_assoc, mul_inv_cancel₀ hAreal, one_mul]
        rw [mul_add, hr]

/-- Literal `OscStartCell` form of the weighted a.e.-envelope estimate. -/
theorem measureReal_inter_oscStartCell_le_of_ptrunc_ae
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0}
    {Q : ℕ → Ω → ℝ} {τ : Ω → ℕ} {s : ℕ} {A : Set Ω}
    (hA : MeasurableSet[ℱ s] A)
    (hτ : MeasurableSet[ℱ s] {ω | τ ω = s})
    {G : ℕ → Set Ω} (hG : ∀ k, MeasurableSet[ℱ (s + k)] (G k))
    (hQm : ∀ k, StronglyMeasurable[ℱ (s + k + 1)]
      (fun ω => Q (s + k + 1) ω - Q (s + k) ω))
    (hQi : ∀ k, Integrable (fun ω => Q (s + k + 1) ω - Q (s + k) ω) μ)
    (hQ0 : ∀ k, μ[fun ω => Q (s + k + 1) ω - Q (s + k) ω |
      ℱ (s + k)] =ᵐ[μ] 0)
    {C : ℝ} (hC : 0 < C)
    (hbdd : ∀ k, ∀ᵐ ω ∂μ, ω ∈ G k →
      |Q (s + k + 1) ω - Q (s + k) ω| ≤ C)
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    μ.real (A ∩ OscStartCell Q τ n ε s) ≤
      μ.real (A ∩ {ω | τ ω = s}) * (2 * ((n : ℝ) + 1) *
        Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2))) +
      μ.real ((A ∩ {ω | τ ω = s}) ∩ {ω | ∃ k < n, ω ∉ G k}) := by
  let B : Set Ω := A ∩ {ω | τ ω = s}
  have hB : MeasurableSet[ℱ s] B := hA.inter hτ
  have h := measureReal_cell_max_abs_shift_le_of_ptrunc_ae (μ := μ) (ℱ := ℱ)
    (ξ := fun k ω => Q (k + 1) ω - Q k ω) (A := B)
    hB hG hQm hQi hQ0 hC hbdd hn hε
  have htele : ∀ (k : ℕ) (ω : Ω),
      LocMart.psum (fun k ω => Q (k + 1) ω - Q k ω) (s + k) ω -
        LocMart.psum (fun k ω => Q (k + 1) ω - Q k ω) s ω =
          Q (s + k) ω - Q s ω := by
    intro k ω
    rw [psum_succ_sub, psum_succ_sub]
    ring
  have heq : B ∩ {ω | ∃ k ≤ n,
      ε ≤ |LocMart.psum (fun k ω => Q (k + 1) ω - Q k ω) (s + k) ω -
        LocMart.psum (fun k ω => Q (k + 1) ω - Q k ω) s ω|} =
      A ∩ OscStartCell Q τ n ε s := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, OscStartCell, B]
    constructor
    · rintro ⟨⟨hωA, hωτ⟩, k, hk, hdev⟩
      refine ⟨hωA, hωτ, k, hk, ?_⟩
      rw [htele k ω] at hdev
      exact hdev
    · rintro ⟨hωA, hωτ, k, hk, hdev⟩
      refine ⟨⟨hωA, hωτ⟩, k, hk, ?_⟩
      rw [htele k ω]
      exact hdev
  rw [heq] at h
  exact h

/-- Actual projected-`Qpl` deterministic-start cells with an a.e. predictable
increment envelope. -/
theorem measureReal_qpl_oscStartCell_le_of_ptrunc_ae {N : ℕ} {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) (eps : ℝ) (i j : Fin N)
    (hε : 0 < eps) {τ : Array N → ℕ} {s : ℕ} {A : Set (Array N)}
    (hA : MeasurableSet[enlFilt p m s] A)
    (hτ : MeasurableSet[enlFilt p m s] {U | τ U = s})
    {G : ℕ → Set (Array N)}
    (hG : ∀ k, MeasurableSet[enlFilt p m (s + k)] (G k))
    {C : ℝ} (hC : 0 < C)
    (hbdd : ∀ k, ∀ᵐ U ∂(arrayMeasure N), U ∈ G k →
      |ProjLedger.projInc p m eps i j (s + k) U| ≤ C)
    {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) :
    (arrayMeasure N).real (A ∩ OscStartCell
        (ProjLedger.Qpl p m eps i j) τ n δ s) ≤
      (arrayMeasure N).real (A ∩ {U | τ U = s}) *
        (2 * ((n : ℝ) + 1) * Real.exp (-(δ ^ 2) / (4 * (n : ℝ) * C ^ 2))) +
      (arrayMeasure N).real ((A ∩ {U | τ U = s}) ∩
        {U | ∃ k < n, U ∉ G k}) := by
  have hdiff : ∀ t, (fun U : Array N =>
      ProjLedger.Qpl p m eps i j (t + 1) U - ProjLedger.Qpl p m eps i j t U) =
      ProjLedger.projInc p m eps i j t := by
    intro t
    funext U
    exact QplWeightedCell.Qpl_succ_sub p m eps i j t U
  have hQm : ∀ k, StronglyMeasurable[enlFilt p m (s + k + 1)]
      (fun U : Array N => ProjLedger.Qpl p m eps i j (s + k + 1) U -
        ProjLedger.Qpl p m eps i j (s + k) U) := by
    intro k
    rw [hdiff]
    exact ProjLedger.stronglyMeasurable_projInc hp0.le m (s + k) eps i j
  have hQi : ∀ k, Integrable (fun U : Array N =>
      ProjLedger.Qpl p m eps i j (s + k + 1) U -
        ProjLedger.Qpl p m eps i j (s + k) U) (arrayMeasure N) := by
    intro k
    rw [hdiff]
    exact ProjLedger.integrable_projInc hp0 hp1 m (s + k) i j hε
  have hQ0 : ∀ k, (arrayMeasure N)[fun U : Array N =>
      ProjLedger.Qpl p m eps i j (s + k + 1) U -
        ProjLedger.Qpl p m eps i j (s + k) U |
        enlFilt p m (s + k)] =ᵐ[arrayMeasure N] 0 := by
    intro k
    rw [hdiff]
    exact ProjLedger.condExp_projInc_eq_zero hp0 hp1 m (s + k) i j hε
  have hbdd' : ∀ k, ∀ᵐ U ∂(arrayMeasure N), U ∈ G k →
      |ProjLedger.Qpl p m eps i j (s + k + 1) U -
        ProjLedger.Qpl p m eps i j (s + k) U| ≤ C := by
    intro k
    filter_upwards [hbdd k] with U hU hmem
    rw [QplWeightedCell.Qpl_succ_sub]
    exact hU hmem
  exact measureReal_inter_oscStartCell_le_of_ptrunc_ae
    hA hτ hG hQm hQi hQ0 hC hbdd' hn hδ

variable {N : ℕ}

/-- The record window restricted to the actual future times `s + k`, `k < n`.
The harmonic condition is time-independent and uses the same sites
`[w - 1, w + M)` as `QplWindow.qplWindow`. -/
def shiftedQplWindow (p : ℝ) (m : ℕ) (i j : Fin N) (V : ℝ)
    (s w M n : ℕ) : Set (Array N) :=
  {U | (∀ k < n, w ≤ (recVal j (prefOf p m (s + k) U)).toNat ∧
      (recVal j (prefOf p m (s + k) U)).toNat < w + M) ∧
    (∀ y ∈ Finset.Ico (w - 1) (w + M),
      SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) y ≤ V) ∧
    (∀ k < n, w ≤ ((trajectory p m U (s + k)).pos i).toNat ∧
      ((trajectory p m U (s + k)).pos i).toNat + 2 ≤ w + M)}

/-- Geometric failure of the shifted record/position window. -/
def shiftedContDefect (p : ℝ) (m : ℕ) (i j : Fin N)
    (s w M n : ℕ) : Set (Array N) :=
  {U | (∃ k < n, ¬ (w ≤ (recVal j (prefOf p m (s + k) U)).toNat ∧
        (recVal j (prefOf p m (s + k) U)).toNat < w + M)) ∨
      (∃ k < n, ¬ (w ≤ ((trajectory p m U (s + k)).pos i).toNat ∧
        ((trajectory p m U (s + k)).pos i).toNat + 2 ≤ w + M))}

/-- The exact future carrier residual at times `s + k`, `k < n`. -/
def shiftedCarrierResidual (p : ℝ) (m : ℕ) (i j : Fin N) (V c : ℝ)
    (s n : ℕ) : Set (Array N) :=
  {U | ∃ k < n, U ∉ qplCarrier (N := N) p m i j V c (s + k)}

/-- Logical split of shifted-window failure into geometric and harmonic defects. -/
theorem not_mem_shiftedQplWindow_subset {p : ℝ} {m : ℕ} {i j : Fin N}
    {V : ℝ} {s w M n : ℕ} :
    {U : Array N | ¬ U ∈ shiftedQplWindow p m i j V s w M n} ⊆
      shiftedContDefect p m i j s w M n ∪ harmDefect p m j V w M := by
  intro U hU
  simp only [shiftedQplWindow, Set.mem_ofPred_eq] at hU
  simp only [shiftedContDefect, harmDefect, Set.mem_union, Set.mem_ofPred_eq]
  rcases not_and_or.mp hU with hrec | hrest
  · left
    left
    obtain ⟨k, hk⟩ := not_forall.mp hrec
    obtain ⟨hkn, hkP⟩ := Classical.not_imp.mp hk
    exact ⟨k, hkn, hkP⟩
  · rcases not_and_or.mp hrest with hh | hX
    · exact Or.inr hh
    · left
      right
      obtain ⟨k, hk⟩ := not_forall.mp hX
      obtain ⟨hkn, hkP⟩ := Classical.not_imp.mp hk
      exact ⟨k, hkn, hkP⟩

/-- A.e., the shifted deterministic window implies the actual predictable
carrier at every future time `s + k`. -/
theorem ae_shiftedQplWindow_subset_carrier {p : ℝ} (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) {m : ℕ} {i j : Fin N} {s n : ℕ} {V : ℝ} (hV1 : 1 ≤ V)
    {w M : ℕ} (hw : 1 ≤ w) :
    ∀ᵐ U ∂(arrayMeasure N), U ∈ shiftedQplWindow p m i j V s w M n →
      ∀ k < n, U ∈ qplCarrier (N := N) p m i j V (envC p m V) (s + k) := by
  filter_upwards [ae_forall_nbT_le_of_window (N := N) (p := p) hp0 hp1
    (m := m) (i := i) (j := j) (K := s + n) (V := V) hV1 (A := w) (M := M) hw]
    with U hnb hW k hk
  obtain ⟨hrec, hh, hX⟩ := hW
  refine ⟨?_, ?_⟩
  · show HprevAt p m (s + k) j U ≤ V
    exact HprevAt_le_of_window hp0 hp1 j hw hV1 (hrec k hk) hh
  · exact hnb (s + k) (by omega) (hrec k hk) hh (hX k hk)

/-- Start-weighted shifted residual budget.  Both defects remain intersected
with `B`; no conditional future law or unweighted residual substitution occurs. -/
theorem measureReal_inter_shiftedCarrierResidual_le {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} {i j : Fin N}
    {s n : ℕ} {V : ℝ} (hV1 : 1 ≤ V) {w M : ℕ} (hw : 1 ≤ w)
    (B : Set (Array N)) :
    (arrayMeasure N).real (B ∩ shiftedCarrierResidual p m i j V (envC p m V) s n) ≤
      (arrayMeasure N).real (B ∩ shiftedContDefect p m i j s w M n) +
      (arrayMeasure N).real (B ∩ harmDefect p m j V w M) := by
  have hsub : ∀ᵐ U ∂(arrayMeasure N),
      U ∈ B ∩ shiftedCarrierResidual p m i j V (envC p m V) s n →
        U ∈ (B ∩ shiftedContDefect p m i j s w M n) ∪
          (B ∩ harmDefect p m j V w M) := by
    filter_upwards [ae_shiftedQplWindow_subset_carrier (N := N) hp0 hp1
      (m := m) (i := i) (j := j) (s := s) (n := n) hV1 (w := w) (M := M) hw]
      with U hU hmem
    rcases hmem with ⟨hUB, k, hk, hkc⟩
    have hnot : U ∉ shiftedQplWindow p m i j V s w M n :=
      fun hW => hkc (hU hW k hk)
    rcases not_mem_shiftedQplWindow_subset hnot with hc | hh
    · exact Or.inl ⟨hUB, hc⟩
    · exact Or.inr ⟨hUB, hh⟩
  have hmono := measure_mono_ae hsub
  calc
    (arrayMeasure N).real (B ∩ shiftedCarrierResidual p m i j V (envC p m V) s n)
        ≤ (arrayMeasure N).real ((B ∩ shiftedContDefect p m i j s w M n) ∪
            (B ∩ harmDefect p m j V w M)) :=
      ENNReal.toReal_mono (measure_ne_top _ _) hmono
    _ ≤ _ := measureReal_union_le _ _

/-- Full deterministic-start `Qpl` cell estimate with the actual predictable
carrier and its shifted geometric/harmonic residual budget. -/
theorem measureReal_qpl_oscStartCell_le_shifted_window {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) (eps : ℝ) (i j : Fin N)
    (hε : 0 < eps) {τ : Array N → ℕ} {s : ℕ} {A : Set (Array N)}
    (hA : MeasurableSet[enlFilt p m s] A)
    (hτ : MeasurableSet[enlFilt p m s] {U | τ U = s})
    {V : ℝ} (hV1 : 1 ≤ V) {w M : ℕ} (hw : 1 ≤ w)
    {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) :
    (arrayMeasure N).real (A ∩ OscStartCell
        (ProjLedger.Qpl p m eps i j) τ n δ s) ≤
      (arrayMeasure N).real (A ∩ {U | τ U = s}) *
        (2 * ((n : ℝ) + 1) * Real.exp (-(δ ^ 2) /
          (4 * (n : ℝ) * (envB p m V (envC p m V)) ^ 2))) +
      ((arrayMeasure N).real ((A ∩ {U | τ U = s}) ∩
          shiftedContDefect p m i j s w M n) +
        (arrayMeasure N).real ((A ∩ {U | τ U = s}) ∩
          harmDefect p m j V w M)) := by
  have hG : ∀ k, MeasurableSet[enlFilt p m (s + k)]
      (qplCarrier (N := N) p m i j V (envC p m V) (s + k)) := fun k =>
    measurableSet_qplCarrier hp0.le m i j V (envC p m V) (s + k)
  have hV0 : 0 ≤ V := by linarith
  have hc0 : 0 ≤ envC p m V := envC_nonneg hp0 hp1 m hV0
  have hC : 0 < envB p m V (envC p m V) := envB_pos hp0 hp1 m hV0 hc0
  have hbdd : ∀ k, ∀ᵐ U ∂(arrayMeasure N),
      U ∈ qplCarrier (N := N) p m i j V (envC p m V) (s + k) →
      |ProjLedger.projInc p m eps i j (s + k) U| ≤ envB p m V (envC p m V) :=
    fun k => ae_abs_projInc_le_carrier hp0 hp1 m i j hε (s + k) hV0 hc0
  have hbase := measureReal_qpl_oscStartCell_le_of_ptrunc_ae
    (N := N) hp0 hp1 m eps i j hε hA hτ hG hC hbdd hn hδ
  have hsplit := measureReal_inter_shiftedCarrierResidual_le (N := N)
    hp0 hp1 (m := m) (i := i) (j := j) (s := s) (n := n) hV1
    (w := w) (M := M) hw (A ∩ {U | τ U = s})
  exact hbase.trans (add_le_add le_rfl hsplit)

/-- Conservative literal `recTimeA` cell estimate at a positive candidate time.
The adapted `firstRecordAt` prefix retains the full cell weight in all three
terms.  No measurability of the zero-defaulted record time is asserted. -/
theorem measureReal_qpl_recTimeA_cell_le_shifted_window_prefix {p : ℝ}
    [Nonempty (Fin N)] (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m : ℕ) (eps : ℝ) (i j : Fin N) (hε : 0 < eps)
    {r s : ℕ} (hs : 1 ≤ s) {A : Set (Array N)}
    (hA : MeasurableSet[enlFilt p m s] A)
    {V : ℝ} (hV1 : 1 ≤ V) {w M : ℕ} (hw : 1 ≤ w)
    {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) :
    (arrayMeasure N).real (A ∩ OscStartCell (ProjLedger.Qpl p m eps i j)
        (fun U => SwarmRecordMeas.Actual.recTimeA p m U r) n δ s) ≤
      (arrayMeasure N).real (A ∩ ActualRecordFiltration.firstRecordAt p m r s) *
        (2 * ((n : ℝ) + 1) * Real.exp (-(δ ^ 2) /
          (4 * (n : ℝ) * (envB p m V (envC p m V)) ^ 2))) +
      ((arrayMeasure N).real ((A ∩ ActualRecordFiltration.firstRecordAt p m r s) ∩
          shiftedContDefect p m i j s w M n) +
        (arrayMeasure N).real ((A ∩ ActualRecordFiltration.firstRecordAt p m r s) ∩
          harmDefect p m j V w M)) := by
  let B : Set (Array N) := A ∩ ActualRecordFiltration.firstRecordAt p m r s
  have hB : MeasurableSet[enlFilt p m s] B :=
    hA.inter (ActualRecordFiltration.measurableSet_firstRecordAt p m r s)
  have hconst : MeasurableSet[enlFilt p m s]
      {U : Array N | (fun _ : Array N => s) U = s} := by simp
  have hmain := measureReal_qpl_oscStartCell_le_shifted_window
    (N := N) hp0 hp1 m eps i j hε (τ := fun _ : Array N => s)
    (A := B) hB hconst hV1 (w := w) (M := M) hw (n := n) hn hδ
  have hsub : A ∩ OscStartCell (ProjLedger.Qpl p m eps i j)
      (fun U => SwarmRecordMeas.Actual.recTimeA p m U r) n δ s ⊆
      B ∩ OscStartCell (ProjLedger.Qpl p m eps i j)
        (fun _ : Array N => s) n δ s := by
    rintro U ⟨hUA, hτ, k, hk, hdev⟩
    obtain ⟨-, hhit⟩ :=
      (ActualRecordFiltration.recTimeA_eq_iff_reach_all_firstRecordAt hs U).1 hτ
    exact ⟨⟨hUA, hhit⟩, rfl, k, hk, hdev⟩
  have hmono := measureReal_mono hsub (measure_ne_top (arrayMeasure N) _)
  have hbound := hmono.trans hmain
  dsimp only [B] at hbound
  simpa only [eq_self_iff_true, Set.ofPred_true, Set.inter_univ] using hbound

end ShiftedQplResidual
